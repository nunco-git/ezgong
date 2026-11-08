/* 스마트공 공용 구글 로그인 — smartgong.kr 안의 앱들이 같은 Firebase 프로젝트(visitorcount-7a285)·같은 앱 이름('gb')을 써서
   한 번 로그인하면 다른 앱에서도 다시 로그인하지 않아도 된다. (상식 학력 진단·독서 골든벨과 같은 로그인)
   사용: <script src="/sg-auth.js" data-gate></script>  → 로그인 전에는 로그인 화면만 보인다.
         data-gate 없이 넣으면 로그인 도구(SG.auth, SG.db, SG.signIn, SG.onUser)만 제공한다.
         data-nochip 을 더하면 화면 모서리의 '로그아웃' 표시를 숨긴다.
         data-sync="앱이름:키접두어,키접두어" 를 더하면 그 localStorage 키들(학습 진도·설정 등)을 로그인한 계정에 저장하고
         다른 기기·브라우저에서 로그인하면 이어서 쓸 수 있다. (저장 위치: sg_users/{uid}/progress/{앱이름}) */
(function(){
  if (window.SG) return;
  var CFG = {apiKey:"AIzaSyAokDpc5E_KyWXTh5oHMcAClOG0fHDBPtA",authDomain:"visitorcount-7a285.firebaseapp.com",projectId:"visitorcount-7a285",storageBucket:"visitorcount-7a285.firebasestorage.app",messagingSenderId:"120562149638",appId:"1:120562149638:web:c8c4ef310ba72764095687"};
  var B = 'https://www.gstatic.com/firebasejs/10.12.2/firebase-';
  var me = document.currentScript;
  var GATE = !!(me && me.hasAttribute('data-gate')), CHIP = !(me && me.hasAttribute('data-nochip'));
  var SG = window.SG = { user:null, auth:null, db:null, app:null, loaded:false };
  var subs = [], got = false, KEY = 'sg_last_user';
  function ls(k, v){ try{ if (v === undefined) return localStorage.getItem(k); if (v === null) localStorage.removeItem(k); else localStorage.setItem(k, v); }catch(e){ return null; } }
  function load(src){ return new Promise(function(ok, no){ var s = document.createElement('script'); s.src = src; s.onload = ok; s.onerror = function(){ no(new Error('load')); }; document.head.appendChild(s); }); }
  SG.onUser = function(f){ subs.push(f); if (got) { try{ f(SG.user); }catch(e){} } };
  SG.signIn = function(){
    var p = new firebase.auth.GoogleAuthProvider();
    return SG.auth.signInWithPopup(p).catch(function(e){
      var c = e && e.code;
      if ((c === 'auth/popup-blocked' || c === 'auth/operation-not-supported-in-this-environment') && window.top === window) return SG.auth.signInWithRedirect(p);
      throw e;
    });
  };
  SG.signOut = function(){ return SG.auth.signOut(); };
  SG.ready = (async function(){
    if (!(window.firebase && firebase.initializeApp)) await load(B + 'app-compat.js');
    await Promise.all([load(B + 'auth-compat.js'), load(B + 'firestore-compat.js')]);
    SG.app = firebase.apps.find(function(a){ return a.name === 'gb'; }) || firebase.initializeApp(CFG, 'gb');
    SG.auth = firebase.auth(SG.app); SG.db = firebase.firestore(SG.app); SG.loaded = true;
    SG.auth.onAuthStateChanged(function(u){
      SG.user = u || null; got = true;
      if (u) ls(KEY, u.uid); else ls(KEY, null);
      subs.forEach(function(f){ try{ f(SG.user); }catch(e){} });
    });
  })();


  /* ----- 진행 상황 동기화: 같은 앱의 localStorage 키들을 계정에 저장·복원 ----- */
  var SY = null, syMsg = '';
  (function(){
    var a = me && me.getAttribute('data-sync'); if (!a) return;
    var i = a.indexOf(':'); if (i < 1) return;
    SY = { id: a.slice(0, i), pre: a.slice(i + 1).split(',').map(function(x){ return x.trim(); }).filter(Boolean) };
  })();
  var nSet = Storage.prototype.setItem, nRem = Storage.prototype.removeItem, pushTimer = null, pulling = false;
  function match(k){ if (!SY) return false; k = String(k); for (var i = 0; i < SY.pre.length; i++) if (k.indexOf(SY.pre[i]) === 0) return true; return false; }
  function snap(){ var o = {}; try{ for (var i = 0; i < localStorage.length; i++) { var k = localStorage.key(i); if (match(k)) o[k] = localStorage.getItem(k); } }catch(e){} return o; }
  function nget(k){ try{ return localStorage.getItem(k); }catch(e){ return null; } }
  function nput(k, v){ try{ nSet.call(localStorage, k, v); }catch(e){} }
  function ndel(k){ try{ nRem.call(localStorage, k); }catch(e){} }
  function fmt(t){ var d = new Date(t), p = function(n){ return (n < 10 ? '0' : '') + n; }; return p(d.getHours()) + ':' + p(d.getMinutes()); }
  function status(m){ syMsg = m; if (chip) chip.textContent = chipText(); }
  function ref(){ return SG.db.collection('sg_users').doc(SG.user.uid).collection('progress').doc(SY.id); }
  function touch(){
    nput('sg_mod_' + SY.id, String(Date.now()));
    if (!SG.user || pulling) return;
    clearTimeout(pushTimer); pushTimer = setTimeout(push, 2500);
  }
  async function push(){
    if (!SY || !SG.user || !SG.db || pulling) return;
    var d = JSON.stringify(snap());
    if (d.length > 900000) { status('저장 공간 초과'); return; }
    var t = Date.now();
    try{ await ref().set({ d: d, t: t }); nput('sg_sync_t_' + SY.id, String(t)); status('저장됨 ' + fmt(t)); }
    catch(e){ status(e && e.code === 'permission-denied' ? '저장 거부(규칙 확인)' : '저장 실패'); }
  }
  function apply(c){
    var o = {}; try{ o = JSON.parse(c.d || '{}'); }catch(e){}
    var cur = snap(); Object.keys(cur).forEach(function(k){ if (!(k in o)) ndel(k); });
    Object.keys(o).forEach(function(k){ if (match(k)) nput(k, o[k]); });
    nput('sg_sync_t_' + SY.id, String(c.t)); nput('sg_mod_' + SY.id, String(c.t));
    try{ sessionStorage.setItem('sg_reloaded_' + SY.id, String(c.t)); }catch(e){}
    location.reload();
  }
  async function pull(){
    if (!SY || !SG.user) return;
    pulling = true;
    try{
      var s = await ref().get(), mine = snap(), has = Object.keys(mine).length > 0;
      var lt = +nget('sg_sync_t_' + SY.id) || 0, mod = +nget('sg_mod_' + SY.id) || 0;
      if (!s.exists) { pulling = false; if (has) await push(); else status('연결됨'); return; }
      var c = s.data(), ct = +c.t || 0;
      if (JSON.stringify(mine) === (c.d || '{}')) { nput('sg_sync_t_' + SY.id, String(ct)); status('최신 ' + fmt(ct)); pulling = false; return; }
      if (ct === lt) { pulling = false; if (mod > lt) await push(); else status('최신 ' + fmt(ct)); return; }
      var dirty = has && (lt === 0 || mod > lt);
      var useCloud = true;
      if (dirty) useCloud = confirm('이 기기의 기록과 구글 계정에 저장된 기록이 서로 달라요.\n\n[확인] 계정에 저장된 기록을 쓸게요 (이 기기 기록은 바뀌어요)\n[취소] 이 기기 기록을 계정에 저장할게요');
      if (useCloud) { var done = ''; try{ done = sessionStorage.getItem('sg_reloaded_' + SY.id) || ''; }catch(e){} if (done === String(ct)) { pulling = false; return; } apply(c); return; }
      pulling = false; await push();
    }catch(e){ pulling = false; status(e && e.code === 'permission-denied' ? '불러오기 거부(규칙 확인)' : '동기화 실패'); }
    pulling = false;
  }
  if (SY) {
    Storage.prototype.setItem = function(k, v){ nSet.apply(this, arguments); if (this === localStorage && match(k)) touch(); };
    Storage.prototype.removeItem = function(k){ nRem.apply(this, arguments); if (this === localStorage && match(k)) touch(); };
    SG.onUser(function(u){ if (u) pull(); });
    var flush = function(){ if (pushTimer) { clearTimeout(pushTimer); pushTimer = null; push(); } };
    document.addEventListener('visibilitychange', function(){ if (document.visibilityState === 'hidden') flush(); });
    window.addEventListener('pagehide', flush);
  }
  SG.syncNow = function(){ return push(); };

  /* ----- 화면: 로그인 막 + 작은 로그아웃 표시 ----- */
  var ov = null, chip = null;
  function chipText(){ var u = SG.user; return (u && u.email ? u.email : '로그인됨') + ' · 로그아웃' + (syMsg ? ' · ' + syMsg : ''); }
  function css(el, s){ el.style.cssText = s; return el; }
  function mk(tag, s, txt){ var e = document.createElement(tag); css(e, s); if (txt != null) e.textContent = txt; return e; }
  function overlay(state, msg){
    if (!document.body) { document.addEventListener('DOMContentLoaded', function(){ overlay(state, msg); }); return; }
    if (!ov) {
      ov = css(document.createElement('div'), 'position:fixed;inset:0;z-index:2147483000;background:#f6f3ec;color:#1a1a1a;display:flex;align-items:center;justify-content:center;padding:24px;font-family:system-ui,-apple-system,"Malgun Gothic",sans-serif');
      document.body.appendChild(ov);
    }
    ov.innerHTML = '';
    var box = mk('div', 'width:min(360px,100%);text-align:center');
    var name = (document.title || '스마트공').replace(/\s*[-–|·].*$/, '');
    box.appendChild(mk('div', 'font-weight:800;font-size:1.35rem;line-height:1.3;margin-bottom:6px', name));
    box.appendChild(mk('div', 'font-size:.9rem;color:#555;line-height:1.55;margin-bottom:18px', state === 'checking' ? '로그인 정보를 확인하고 있어요…' : '스마트공 앱은 구글 계정으로 한 번 로그인하면 모든 앱을 다시 로그인 없이 쓸 수 있어요.'));
    if (state === 'login' || state === 'error') {
      var b = mk('button', 'width:100%;min-height:48px;border:0;border-radius:12px;background:#1a56db;color:#fff;font-weight:700;font-size:1rem;font-family:inherit;cursor:pointer', '구글로 로그인');
      b.type = 'button';
      b.onclick = function(){
        b.disabled = true; b.textContent = '로그인 창을 여는 중…';
        SG.ready.then(function(){ return SG.signIn(); }).catch(function(e){
          var c = (e && e.code) || '';
          if (c === 'auth/popup-closed-by-user' || c === 'auth/cancelled-popup-request') { overlay('login'); return; }
          overlay('error', c === 'auth/popup-blocked' || c === 'auth/operation-not-supported-in-this-environment' ? '로그인 창이 막혔어요. 아래 "새 탭에서 열기"로 열어 로그인해 주세요.' : c === 'auth/unauthorized-domain' ? '이 주소(' + location.hostname + ')가 Firebase 승인된 도메인에 없어요.' : '로그인에 실패했어요' + (c ? ' (' + c + ')' : '') + '. 인터넷 연결을 확인해 주세요.');
        });
      };
      box.appendChild(b);
      if (window.top !== window) { var a = mk('a', 'display:block;margin-top:12px;font-size:.85rem;color:#1a56db', '새 탭에서 열기'); a.href = location.href; a.target = '_blank'; a.rel = 'noopener'; box.appendChild(a); }
    }
    if (msg) box.appendChild(mk('div', 'margin-top:14px;font-size:.85rem;color:#b42318;line-height:1.5', msg));
    ov.appendChild(box);
  }
  function drawChip(u){
    if (!CHIP || !document.body) return;
    if (chip) { chip.remove(); chip = null; }
    if (!u) return;
    chip = css(document.createElement('button'), 'position:fixed;left:6px;bottom:calc(6px + env(safe-area-inset-bottom,0px));z-index:2147482000;min-height:22px;padding:0 8px;border:0;border-radius:11px;background:rgba(15,23,42,.55);color:#fff;font-weight:600;font-size:11px;font-family:inherit;cursor:pointer;opacity:.55');
    chip.type = 'button'; chip.textContent = chipText(); chip.setAttribute('aria-label', '구글 로그아웃');
    chip.onclick = function(){ if (confirm('로그아웃할까요? 모든 스마트공 앱에서 로그아웃돼요.')) SG.signOut(); };
    document.body.appendChild(chip);
  }
  if (GATE) {
    if (ls(KEY)) { /* 이전에 로그인한 적 있으면 확인되는 동안 화면을 가리지 않는다 */ } else overlay('checking');
    SG.ready.catch(function(){
      if (ls(KEY)) return; /* 오프라인이어도 이전 로그인 기록이 있으면 그대로 사용 */
      overlay('error', '로그인 도구를 불러오지 못했어요. 인터넷 연결을 확인한 뒤 새로 고침해 주세요.');
    });
    SG.onUser(function(u){
      if (u) { if (ov) { ov.remove(); ov = null; } }
      else overlay('login');
      var go = function(){ drawChip(u); };
      if (document.body) go(); else document.addEventListener('DOMContentLoaded', go);
    });
  } else if (CHIP) {
    SG.onUser(function(u){ drawChip(u); });
  }
})();
