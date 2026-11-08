/* 스마트공 공용 구글 로그인 — smartgong.kr 안의 앱들이 같은 Firebase 프로젝트(visitorcount-7a285)·같은 앱 이름('gb')을 써서
   한 번 로그인하면 다른 앱에서도 다시 로그인하지 않아도 된다. (상식 학력 진단·독서 골든벨과 같은 로그인)
   사용: <script src="/sg-auth.js" data-gate></script>  → 화면은 그대로 보이고, 맨 위에 로그인 안내 한 줄이 붙는다.
         data-gate 없이 넣으면 로그인 도구(SG.auth, SG.db, SG.signIn, SG.onUser)만 제공한다.
         data-sync="앱이름:키접두어,키접두어" 를 더하면 그 localStorage 키들(학습 진도·설정 등)을 로그인한 계정에 저장하고
         다른 기기·브라우저에서 로그인하면 이어서 쓸 수 있다. (저장 위치: sg_users/{uid}/progress/{앱이름}) */
(function(){
  if (window.SG) return;
  var CFG = {apiKey:"AIzaSyAokDpc5E_KyWXTh5oHMcAClOG0fHDBPtA",authDomain:"visitorcount-7a285.firebaseapp.com",projectId:"visitorcount-7a285",storageBucket:"visitorcount-7a285.firebasestorage.app",messagingSenderId:"120562149638",appId:"1:120562149638:web:c8c4ef310ba72764095687"};
  var B = 'https://www.gstatic.com/firebasejs/10.12.2/firebase-';
  var me = document.currentScript;
  var GATE = !!(me && me.hasAttribute('data-gate'));
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
  function status(m){ syMsg = m; if (typeof drawBar === 'function') drawBar(); }
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

  /* ----- 화면: 맨 위 한 줄 로그인 안내(화면은 그대로 보이고, 로그인하면 저장·이어하기) ----- */
  var bar = null, errMsg = '';
  function chipText(){ var u = SG.user; return (u && u.email ? u.email : '로그인됨') + ' · ' + (syMsg || '자동 저장돼요'); }
  function status2(){ drawBar(); }
  function mk(tag, s, txt){ var e = document.createElement(tag); e.style.cssText = s; if (txt != null) e.textContent = txt; return e; }
  var BTN = 'min-height:26px;padding:0 12px;border:0;border-radius:13px;font-weight:700;font-size:12px;font-family:inherit;cursor:pointer;white-space:nowrap;';
  function drawBar(){
    if (!got) return;
    if (!document.body) { document.addEventListener('DOMContentLoaded', drawBar); return; }
    if (!bar) { bar = document.createElement('div'); bar.id = 'sg-bar'; document.body.insertBefore(bar, document.body.firstChild); }
    bar.style.cssText = 'display:flex;flex-wrap:wrap;align-items:center;gap:6px 10px;padding:6px 12px;background:#1e293b;color:#e2e8f0;font:12.5px/1.45 system-ui,-apple-system,"Malgun Gothic",sans-serif;box-sizing:border-box;width:100%';
    bar.innerHTML = '';
    var u = SG.user;
    if (!u) {
      bar.appendChild(mk('span', 'flex:1 1 220px;min-width:0', '구글 계정으로 로그인하면 학습 진도와 작업 내용이 저장돼서, 다른 기기에서도 이어서 할 수 있어요.'));
      var b = mk('button', BTN + 'background:#3b82f6;color:#fff', '구글로 로그인'); b.type = 'button';
      b.onclick = function(){
        b.disabled = true; b.textContent = '로그인 창을 여는 중…'; errMsg = '';
        SG.ready.then(function(){ return SG.signIn(); }).catch(function(e){
          var c = (e && e.code) || '';
          if (c !== 'auth/popup-closed-by-user' && c !== 'auth/cancelled-popup-request')
            errMsg = (c === 'auth/popup-blocked' || c === 'auth/operation-not-supported-in-this-environment') ? '로그인 창이 막혔어요. "새 탭에서 열기"로 열어 로그인해 주세요.' : c === 'auth/unauthorized-domain' ? '이 주소(' + location.hostname + ')가 Firebase 승인된 도메인에 없어요.' : '로그인에 실패했어요' + (c ? ' (' + c + ')' : '') + '. 인터넷 연결을 확인해 주세요.';
          drawBar();
        });
      };
      bar.appendChild(b);
      if (errMsg) {
        bar.appendChild(mk('span', 'flex:1 1 100%;color:#fca5a5', errMsg));
        if (window.top !== window) { var a = mk('a', 'color:#93c5fd;font-size:12px', '새 탭에서 열기'); a.href = location.href; a.target = '_blank'; a.rel = 'noopener'; bar.appendChild(a); }
      }
    } else {
      bar.appendChild(mk('span', 'flex:1 1 220px;min-width:0;overflow:hidden;text-overflow:ellipsis', '✓ ' + chipText()));
      var o = mk('button', BTN + 'background:#334155;color:#e2e8f0', '로그아웃'); o.type = 'button';
      o.onclick = function(){ if (confirm('로그아웃할까요? 모든 스마트공 앱에서 로그아웃돼요. (이 기기의 기록은 그대로 남아요)')) SG.signOut(); };
      bar.appendChild(o);
    }
  }
  if (GATE) SG.onUser(function(){ drawBar(); });
})();
