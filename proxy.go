package main

import (
	"bufio"
	"crypto/hmac"
	"crypto/md5"
	"crypto/subtle"
	"crypto/tls"
	"encoding/base64"
	"errors"
	"flag"
	"fmt"
	"github.com/jmckaskill/gokerb"
	"github.com/jmckaskill/gokerb/khttp"
	"github.com/jmckaskill/goldap"
	"github.com/jmckaskill/goldap/ad"
	"io"
	"io/ioutil"
	"log"
	"log/syslog"
	"net"
	"net/http"
	"net/http/cgi"
	"net/http/httputil"
	"net/url"
	"os"
	"os/exec"
	osuser "os/user"
	"path"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

func die(args ...interface{}) {
	a := append([]interface{}{"fatal: "}, args...)
	log.Print(a...)
	os.Exit(256)
}

func check(err error) {
	if err != nil {
		die(err)
	}
}

type bitset []uint32

func newBitset(i int) bitset {
	var b bitset
	b.Set(i)
	return b
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func (b1 bitset) HasIntersection(b2 bitset) bool {
	for i := 0; i < min(len(b1), len(b2)); i++ {
		if b1[i]&b2[i] != 0 {
			return true
		}
	}
	return false
}

func (b bitset) Test(i int) bool {
	o := i >> 5
	return o < len(b) && (b[o]&(1<<(uint(i)&31))) != 0
}

func (b bitset) Clone() bitset {
	b2 := make(bitset, len(b))
	copy(b2, b)
	return b2
}

func (b *bitset) Set(i int) {
	o := i >> 5
	if o >= cap(*b) {
		b2 := make(bitset, o+1)
		copy(b2, *b)
		*b = b2
	} else if o >= len(*b) {
		*b = (*b)[:o+1]
	}
	(*b)[o] |= 1 << (uint(i) & 31)
}

func (b *bitset) SetMulti(v bitset) {
	if len(v) >= cap(*b) {
		b2 := make(bitset, len(v))
		copy(b2, *b)
		*b = b2
	} else if len(v) >= len(*b) {
		*b = (*b)[:len(v)]
	}
	for i, v2 := range v {
		(*b)[i] |= v2
	}
}

type ruleGroup struct {
	gid  int
	name string
	dn   ldap.ObjectDN
}

type rule struct {
	url           *url.URL
	gmask         bitset
	groups        []ruleGroup
	hook          string
	cgi           string
	cgicwd        string
	proxy         *url.URL
	stripPrefix   string
	flushInterval time.Duration
	handler       http.Handler
	query url.Values
}

type user struct {
	*ad.User
	gmask bitset
}

var creds []*kerb.Credential
var ldapCred *kerb.Credential
var ldapAlias string
var cookieKey []byte
var sslCert tls.Certificate
var runas string
var groups []ldap.ObjectDN
var groupmap = make(map[ldap.ObjectDN]int)
var configFile string
var logrules bool
var loggroups bool
var logheaders bool

func init() {
	flag.StringVar(&configFile, "config", "/etc/krb-httpd.conf", "config file")
}

func dial(proto, realm string) (io.ReadWriteCloser, error) {
	if realm == "CTCT.NET" {
		return net.Dial(proto, "10.1.46.195:88")
	}

	return kerb.DefaultDial(proto, realm)
}

type writeFlusher interface {
	http.Flusher
	http.ResponseWriter
}

type maxLatencyWriter struct {
	dst     writeFlusher
	latency time.Duration

	lk   sync.Mutex // protects init of done, as well Write + Flush
	done chan bool
}

func (m *maxLatencyWriter) Write(p []byte) (n int, err error) {
	m.lk.Lock()
	defer m.lk.Unlock()
	if m.done == nil {
		m.done = make(chan bool)
		go m.flushLoop()
	}
	n, err = m.dst.Write(p)
	if err != nil {
		m.done <- true
	}
	return
}

func (m *maxLatencyWriter) WriteHeader(status int) {
	m.lk.Lock()
	defer m.lk.Unlock()
	if m.done == nil {
		m.done = make(chan bool)
		go m.flushLoop()
	}
	m.dst.WriteHeader(status)
}

func (m *maxLatencyWriter) Flush()              { m.dst.Flush() }
func (m *maxLatencyWriter) Header() http.Header { return m.dst.Header() }

func (m *maxLatencyWriter) flushLoop() {
	t := time.NewTicker(m.latency)
	defer t.Stop()
	for {
		select {
		case <-t.C:
			m.lk.Lock()
			m.dst.Flush()
			m.lk.Unlock()
		case <-m.done:
			return
		}
	}
	panic("unreached")
}

type maxLatencyHandler struct {
	latency time.Duration
	next    http.Handler
}

func (m maxLatencyHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if wf, ok := w.(writeFlusher); ok {
		w = &maxLatencyWriter{dst: wf, latency: m.latency}
	}

	m.next.ServeHTTP(w, r)

	if lw, ok := w.(*maxLatencyWriter); ok && lw.done != nil {
		close(lw.done)
	}
}

type redirector url.URL

func (u *redirector) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	tgt := new(url.URL)
	*tgt = *(*url.URL)(u)
	tgt.Path = path.Join(tgt.Path, r.URL.Path)
	tgt.RawQuery = r.URL.RawQuery
	http.Redirect(w, r, tgt.String(), http.StatusTemporaryRedirect)
}

var rulelk sync.Mutex
var rules []*rule
var cfgtime time.Time
func getRules(init bool) []*rule {
	rulelk.Lock()
	defer rulelk.Unlock()

	f, err := os.Open(configFile)
	if err != nil {
		return nil
	}
	defer f.Close()
	st, err := f.Stat()
	if err != nil {
		log.Print(err)
		return nil
	}
	if st.ModTime() == cfgtime {
		return rules
	}

	cfgtime = st.ModTime()
	rules, err = parseConfigFile(init)
	if err != nil {
		if init {
			die(err)
		} else {
			log.Print(err)
		}
	}
	log.Print("loaded config file")
	return rules
}

func parseConfigFile(init bool) ([]*rule, error) {
	f, err := os.Open(configFile)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	r := bufio.NewReader(f)
	var p *rule
	var sslCrtFile, sslKeyFile string
	var rules []*rule

	logrules = false
	loggroups = false
	logheaders = false

	for err == nil {
		var s string
		s, err = r.ReadString('\n')
		if s == "" || s[0] == '#' {
			continue
		}

		s = strings.TrimSpace(s)
		cmdi := strings.Index(s, " ")
		if cmdi < 0 {
			cmdi = len(s)
		}
		cmd := strings.TrimSpace(s[:cmdi])
		args := strings.TrimSpace(s[cmdi:])

		switch cmd {
		case "log":
			for _, arg := range strings.Split(args, " ") {
				if arg == "rules" {
					logrules = true
				} else if arg == "headers" {
					logheaders = true
				} else if arg == "groups" {
					loggroups = true
				} else {
					return nil, fmt.Errorf("unknown log %s", arg)
				}
			}
		case "rule":
			if p != nil {
				rules = append(rules, p)
			}
			p = new(rule)
			p.url, err = url.Parse(args)
			if err == nil && p.url.Scheme == "" {
				p.url, err = url.Parse("any://" + args)
			}
			if err != nil {
				return nil, err
			}
			p.query = p.url.Query()

			_, err = path.Match(p.url.Host, "")
			if err != nil {
				return nil, err
			}
			_, err = path.Match(p.url.Path, "")
			if err != nil {
				return nil, err
			}
		case "group":
			a := strings.SplitN(args, " ", 2)
			if len(a) < 2 {
				return nil, fmt.Errorf("invalid group should be 'group <name> <dn>'")
			}
			dn := ldap.ObjectDN(a[1])
			gidx, ok := groupmap[dn]
			if !ok {
				groupmap[dn] = len(groups)
				gidx = len(groups)
				groups = append(groups, dn)
				if loggroups {
					log.Printf("adding group %s %v", dn, gidx)
				}
			}
			p.groups = append(p.groups, ruleGroup{gidx, a[0], dn})
			p.gmask.Set(gidx)
		case "hook":
			p.hook = args
		case "cgi":
			p.cgi = args
		case "cgi-cwd":
			p.cgicwd = args
		case "filesystem":
			p.handler = http.FileServer(http.Dir(args))
		case "strip-prefix":
			p.stripPrefix = args
		case "proxy":
			u, err := url.Parse(args)
			if err != nil {
				return nil, err
			}
			p.handler = httputil.NewSingleHostReverseProxy(u)
		case "flush-interval":
			p.flushInterval, err = time.ParseDuration(args)
			if err != nil {
				return nil, err
			}
		case "redirect":
			u, err := url.Parse(args)
			if err != nil {
				return nil, err
			}
			p.handler = (*redirector)(u)
		}

		// Don't run init commands after bootup as we've probably
		// changed user and can no longer open the files
		if !init {
			continue
		}

		switch cmd {
		case "ldap-key":
			s := strings.SplitN(args, " ", 2)
			if len(s) < 2 {
				return nil, fmt.Errorf("invalid ldap-key expected <alias> <key file>")
			}
			file, err := os.Open(s[1])
			if err != nil {
				return nil, err
			}
			c, err := kerb.ReadKeytab(file, &kerb.CredConfig{Dial: dial})
			file.Close()
			if err != nil || len(c) < 1 {
				return nil, fmt.Errorf("invalid keytab %v %v", s[1], err)
			}
			ldapCred = c[0]
			ldapAlias = s[0]
		case "krb-key":
			file, err := os.Open(args)
			if err != nil {
				return nil, err
			}
			creds, err = kerb.ReadKeytab(file, &kerb.CredConfig{Dial: dial})
			file.Close()
			if err != nil || len(creds) < 1 {
				return nil, fmt.Errorf("invalid keytab %v %v", args, err)
			}
		case "cookie-key":
			cookieKey, err = ioutil.ReadFile(args)
			if err != nil {
				return nil, err
			}
		case "run-as":
			u, err := osuser.Lookup(args)
			if err != nil {
				return nil, err
			}
			runas = u.Uid
		case "ssl-crt":
			sslCrtFile = args
		case "ssl-key":
			sslKeyFile = args
		}
	}

	if err != nil && err != io.EOF {
		return nil, err
	}

	if p != nil {
		rules = append(rules, p)
	}

	for _, p := range rules {
		if len(p.cgi) > 0 {
			p.handler = &cgi.Handler{
				Path: p.cgi,
				Dir:  p.cgicwd,
			}
		}

		if len(p.stripPrefix) > 0 {
			p.handler = http.StripPrefix(p.stripPrefix, p.handler)
		}

		if p.flushInterval > 0 {
			p.handler = &maxLatencyHandler{p.flushInterval, p.handler}
		}
	}

	if init {
		if ldapCred == nil || ldapAlias == "" {
			return nil, fmt.Errorf("need to specify ldap key and alias")
		}

		if len(creds) < 1 {
			return nil, fmt.Errorf("need to specify kerberos key")
		}

		if sslCrtFile == "" || sslKeyFile == "" {
			return nil, fmt.Errorf("need to specify ssl certificate and key")
		}

		sslCert, err = tls.LoadX509KeyPair(sslCrtFile, sslKeyFile)
		if err != nil {
			return nil, err
		}
	}

	return rules, nil
}

func resolveUsers(db *ad.DB, dn ldap.ObjectDN, users map[string]*user, depth int, gmask bitset) error {
	if depth == 0 {
		return errors.New("reached max group depth")
	}

	obj, err := db.LookupDN(dn)
	if err != nil {
		return err
	}

	switch u := obj.(type) {
	case *ad.User:
		pr := fmt.Sprintf("%s@%s", strings.ToLower(u.SAMAccountName), u.Realm)
		if u2, ok := users[pr]; ok {
			u2.gmask.SetMulti(gmask)
		} else {
			users[pr] = &user{u, gmask.Clone()}
		}

	case *ad.Group:
		gidx, ok := groupmap[u.DN]
		if !ok {
			gidx = len(groups)
			groupmap[u.DN] = gidx
			groups = append(groups, u.DN)
			if loggroups {
				log.Printf("adding group %s %v", dn, gidx)
			}
		}

		mask := gmask.Clone()
		mask.Set(gidx)
		for _, dn := range u.Member {
			err := resolveUsers(db, dn, users, depth-1, mask)
			if err == ldap.ErrNotFound {
				continue
			} else if err != nil {
				return err
			}
		}
	}

	return nil
}

func getUsers(db *ad.DB) (map[string]*user, error) {
	users := make(map[string]*user)

	// If we encounter any errors collecting the user list from LDAP, we
	// error out and leave the users map in its current state. This is to
	// avoid temporary glitches from deactivating accounts.
	for i, g := range groups {
		err := resolveUsers(db, g, users, 5, newBitset(i))
		if err != nil {
			return nil, err
		}
	}

	return users, nil
}

func logLines(pfx string, r io.Reader) error {
	b := bufio.NewReaderSize(r, 512)
	for {
		line, isPrefix, err := b.ReadLine()
		if len(line) > 0 {
			log.Print(pfx, string(line))
		}
		if err != nil {
			return err
		}
		// Consume the rest of the overlong line
		for isPrefix {
			_, isPrefix, err = b.ReadLine()
			if err != nil {
				return err
			}
		}
	}
	return nil
}

func runHooks(users map[string]*user) error {
	for _, r := range getRules(false) {
		if r.hook == "" {
			continue
		}

		h := exec.Command(r.hook)
		w, err := h.StdinPipe()
		if err != nil {
			return err
		}
		stderr, err := h.StderrPipe()
		if err != nil {
			return err
		}

		go logLines(fmt.Sprintf("hook %s: ", r.hook), stderr)

		err = h.Start()
		if err != nil {
			return err
		}

		for pr, u := range users {
			if !u.gmask.HasIntersection(r.gmask) {
				continue
			}

			fmt.Fprintf(w, "user %s\n", pr)
			fmt.Fprintf(w, "dn %s\n", u.DN)
			fmt.Fprintf(w, "sid %s\n", u.ObjectSID)
			fmt.Fprintf(w, "name %s\n", u.DisplayName)
			fmt.Fprintf(w, "email %s\n", u.Mail)
			for _, g := range r.groups {
				if u.gmask.Test(g.gid) {
					fmt.Fprintf(w, "group %s %s\n", g.name, g.dn)
				}
			}
			fmt.Fprint(w, "\n")
		}

		fmt.Print(w, "\n")
		w.Close()
		err = h.Wait()
		if err != nil {
			return err
		}
	}

	return nil
}

func authCookie(r *http.Request) (string, error) {
	cookie, err := r.Cookie("kerb")
	if err != nil {
		return "", khttp.ErrNoAuth
	}

	val, err := base64.StdEncoding.DecodeString(cookie.Value)
	if err != nil {
		return "", err
	}

	if len(val) < md5.Size {
		return "", khttp.ErrNoAuth
	}

	sig := hmac.New(md5.New, cookieKey)
	sig.Write(val[:len(val)-md5.Size])

	if subtle.ConstantTimeCompare(sig.Sum(nil), val[len(val)-md5.Size:]) != 1 {
		return "", khttp.ErrNoAuth
	}

	vals := strings.SplitN(string(val[:len(val)-md5.Size]), " ", 2)
	if len(vals) < 2 {
		return "", khttp.ErrNoAuth
	}

	ts, err := time.Parse(time.RFC3339, vals[0])
	if err != nil || time.Now().Sub(ts) > 5*time.Minute || ts.Sub(time.Now()) > 5*time.Minute {
		return "", khttp.ErrNoAuth
	}

	return vals[1], nil
}

func writeCookie(w http.ResponseWriter, user string) {
	var val []byte

	if user != "" {
		val = append(val, time.Now().Format(time.RFC3339)...)
		val = append(val, " "...)
		val = append(val, user...)

		sig := hmac.New(md5.New, cookieKey)
		sig.Write(val)
		val = sig.Sum(val)
	}

	http.SetCookie(w, &http.Cookie{
		Name:     "kerb",
		Secure:   true,
		HttpOnly: true,
		Value:    base64.StdEncoding.EncodeToString(val),
		Path:     "/",
		MaxAge:   600,
	})
}

type loggedResponse struct {
	w    http.ResponseWriter
	r    *http.Request
	url  *url.URL
	user string
}

func (w *loggedResponse) Flush() {
	if wf, ok := w.w.(http.Flusher); ok {
		wf.Flush()
	}
}

func (w *loggedResponse) Header() http.Header         { return w.w.Header() }
func (w *loggedResponse) Write(d []byte) (int, error) { return w.w.Write(d) }

func (w *loggedResponse) WriteHeader(status int) {
	log.Printf("%s %s \"%s %s %s\" %d", w.r.RemoteAddr, w.user, w.r.Method, w.url.String(), w.r.Proto, status)
	w.w.WriteHeader(status)
}

func (r *rule) matches(u *url.URL) bool {
	if r.url.Host != u.Host {
		return false
	}

	rdir := r.url.Path
	if rdir == "/" || rdir == "" {
		// catch all
	} else {
		if strings.HasSuffix(rdir, "/") {
			rdir = rdir[:len(rdir)-1]
		}
		dir := u.Path
		ok := false
		for dir != "/" && !ok {
			ok, _ = path.Match(rdir, dir)
			dir = path.Dir(dir)
		}
		if !ok {
			return false
		}
	}

	if len(r.query) > 0 {
		q2 := u.Query()
		for k,s := range r.query {
			if len(s) > 0 && s[0] != q2.Get(k) {
				return false
			}
		}
	}

	return true
}

func findRule(u *url.URL) (*rule, bitset) {
	var gmask bitset
	for _, r := range getRules(false) {
		if !r.matches(u) {
			continue
		}

		if logrules {
			log.Printf("rule matches %s %s %v", r.url.String(), u.String(), r.gmask)
		}

		if len(r.gmask) > 0 {
			gmask = r.gmask
		}

		if r.handler != nil {
			return r, gmask
		}
	}

	return nil, nil
}

func main() {
	var userlk sync.Mutex
	var users map[string]*user
	var db *ad.DB
	var err error

	slog, err := syslog.New(syslog.LOG_INFO, "krb-httpd")
	check(err)
	log.SetFlags(0)
	log.SetOutput(slog)

	flag.Parse()
	getRules(true)

	httpAuth := khttp.NewAuthenticator(creds, &khttp.AuthConfig{Negotiate: true})

	httpsAuth := khttp.NewAuthenticator(creds, &khttp.AuthConfig{
		BasicLookup: func(u string) (string, string, error) {
			userlk.Lock()
			d := db
			userlk.Unlock()
			if d == nil {
				return "", "", errors.New("no database")
			}
			return d.ResolvePrincipal(u)
		},
		BasicRealm: "Windows Domain Logon (e.g. AM\\User)",
		Negotiate:  true,
	})

	handler := http.HandlerFunc(func(w2 http.ResponseWriter, req *http.Request) {
		var u *user
		var uok bool

		if logheaders {
			log.Print(*req)
		}

		if uid, err := strconv.Atoi(runas); err == nil {
			syscall.Setuid(uid)
		}

		w := &loggedResponse{w2, req, req.URL, ""}

		if req.URL.Host == "" {
			req.URL.Host = req.Host
		}

		auth := httpAuth
		req.URL.Scheme = "http"
		if req.TLS != nil {
			auth = httpsAuth
			req.URL.Scheme = "https"
		}

		rule, gmask := findRule(req.URL)

		if rule == nil || (rule.url.Scheme != "any" && rule.url.Scheme != req.URL.Scheme) {
			goto authFailed
		}

		// See if the rule doesn't require auth
		if len(gmask) == 0 {
			req.Header.Del("Authorization")
			rule.handler.ServeHTTP(w, req)
			return
		}

		w.user, _ = authCookie(req)

		if w.user == "" {
			user, realm, err := auth.Authenticate(w, req)
			if err != nil {
				if err != khttp.ErrNoAuth {
					log.Print("auth failed: ", err)
				}
				goto authFailed
			}

			w.user = fmt.Sprintf("%s@%s", strings.ToLower(user), strings.ToUpper(realm))

			// The cookie is not one-shot so is insecure over
			// unencrypted channels
			if req.TLS != nil {
				writeCookie(w, w.user)
			}
		}

		userlk.Lock()
		if users == nil {
			userlk.Unlock()
			http.Error(w, "The server is still booting up", http.StatusServiceUnavailable)
			return
		}
		u, uok = users[w.user]
		userlk.Unlock()

		if !uok {
			goto authFailed
		}

		if logrules {
			log.Printf("group check have %v need %v", u.gmask, gmask)
		}

		if gmask.HasIntersection(u.gmask) {
			req.Header.Del("Authorization")
			req.Header.Set("Remote-User", w.user)
			req.Header.Set("Remote-Name", u.DisplayName)
			req.Header.Set("Remote-Email", strings.ToLower(u.Mail))
			rule.handler.ServeHTTP(w, req)
			return
		}

	authFailed:
		// See if we need to redirect between http/https. We prefer
		// https if the config file doesn't specify anything, but if
		// the user has already provided auth on http then we go with
		// it.
		if rule != nil && (rule.url.Scheme != "any" || req.Header.Get("Authorization") == "") {
			want := rule.url.Scheme
			if want == "any" {
				want = "https"
			}

			if want != req.URL.Scheme {
				tgt := new(url.URL)
				*tgt = *req.URL
				tgt.Scheme = want
				http.Redirect(w, req, tgt.String(), http.StatusTemporaryRedirect)
				return
			}
		}

		if _, err := req.Cookie("kerb"); err != http.ErrNoCookie {
			writeCookie(w, "")
		}

		auth.SetAuthHeader(w)
		w.WriteHeader(http.StatusUnauthorized)
	})

	httpServer := http.Server{Addr: ":80", Handler: handler}
	httpsServer := http.Server{
		Addr:    ":443",
		Handler: handler,
		TLSConfig: &tls.Config{
			NextProtos:   []string{"http/1.1"},
			Certificates: []tls.Certificate{sslCert},
		},
	}

	httpConn, err := net.Listen("tcp", ":80")
	check(err)

	httpsConn, err := net.Listen("tcp", ":443")
	check(err)

	uid, err := strconv.Atoi(runas)
	check(err)
	err = syscall.Setuid(uid)
	check(err)

	go httpServer.Serve(httpConn)
	go httpsServer.Serve(tls.NewListener(httpsConn, httpsServer.TLSConfig))

	for {
		newdb := ad.New(ldapCred, ldapAlias)
		newusers, err := getUsers(newdb)
		if err != nil {
			log.Print("LDAP failed:", err)
			goto sleep
		}

		err = runHooks(newusers)
		if err != nil {
			log.Print("Hook failed:", err)
			goto sleep
		}

		log.Print("users successfully updated")

		userlk.Lock()
		db = newdb
		users = newusers
		userlk.Unlock()

	sleep:
		time.Sleep(time.Hour)
	}
}
