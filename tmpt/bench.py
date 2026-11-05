import os, sys, time, random, tempfile, threading, queue, shutil, importlib, subprocess
sys.path.insert(0, "smart-explorer"); sys.path.insert(0, "tmpt")
import smart_explorer as NEW
import old_se as OLD
random.seed(1)
words = "예산 집행 계획 보고 회의 결과 추진 사업 운영 관리 지원 협조 요청 공문 검토 승인 시행 기관 부서 담당 일정 자료 제출 확인 변경".split()
root = os.path.join(os.environ.get("RUNNER_TEMP", tempfile.gettempdir()), "bench")
N = 6000
for i in range(N):
    d = os.path.join(root, "부서%d" % (i % 30), "폴더%d" % (i % 7))
    os.makedirs(d, exist_ok=True)
    txt = " ".join(random.choice(words) for _ in range(3500))
    if i % 97 == 0: txt += " 특별한단어 "
    with open(os.path.join(d, "문서%05d.txt" % i), "w", encoding="utf-8") as f: f.write(txt)
unc = "\\\\localhost\\" + root[0] + "$" + root[2:]
print("UNC", unc, os.path.isdir(unc), flush=True)
def run(M, cache, r, label):
    pats = [M.make_pattern(t, True) for t in M.parse_query("특별한단어")]
    out = queue.Queue(); stop = threading.Event()
    t = time.time(); M.search_worker(r, pats, {".txt"}, True, True, out, stop, cache); dt = time.time() - t
    hits = sorted(m[1]["path"].lower()[-14:] for m in list(out.queue) if m[0] == "hit")
    print(f"{label}: {dt:.2f}s hits={len(hits)}", flush=True)
    return hits
for r, where in ((root, "로컬"), (unc, "공유폴더(UNC)")):
    if not os.path.isdir(r): continue
    c = NEW.Cache(os.path.join(tempfile.mkdtemp(), "c.db"))
    run(NEW, c, r, where + " 색인 만들기")
    a = run(OLD, c, r, where + " 예전 방식")
    b = run(NEW, c, r, where + " 새 방식")
    a2 = run(OLD, c, r, where + " 예전 방식(2)")
    b2 = run(NEW, c, r, where + " 새 방식(2)")
    print("same results:", a == b, flush=True)
