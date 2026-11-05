import os, sys, time, random, tempfile, threading, queue, cProfile, pstats, io
sys.path.insert(0, "smart-explorer")
import smart_explorer as S
random.seed(1)
words = "예산 집행 계획 보고 회의 결과 추진 사업 운영 관리 지원 협조 요청 공문 검토 승인 시행 기관 부서 담당 일정 자료 제출 확인 변경".split()
root = tempfile.mkdtemp()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
t0 = time.time()
for i in range(N):
    d = os.path.join(root, "부서%d" % (i % 30), "폴더%d" % (i % 7))
    os.makedirs(d, exist_ok=True)
    txt = " ".join(random.choice(words) for _ in range(3500))
    if i % 97 == 0: txt += " 특별한단어 "
    with open(os.path.join(d, "문서%05d.txt" % i), "w", encoding="utf-8") as f: f.write(txt)
print("files made", round(time.time() - t0, 1), "s", flush=True)
cache = S.Cache(os.path.join(tempfile.mkdtemp(), "c.db"))
exts = {".txt"}
def run(q, label):
    pats = [S.make_pattern(t, True) for t in S.parse_query(q)]
    out = queue.Queue(); stop = threading.Event()
    t = time.time(); S.search_worker(root, pats, exts, True, True, out, stop, cache); dt = time.time() - t
    hits = sum(1 for m in list(out.queue) if m[0] == "hit")
    print(f"{label}: {dt:.2f}s hits={hits}", flush=True)
run("특별한단어", "1st (index build)")
run("특별한단어", "2nd (indexed)")
pr = cProfile.Profile(); pr.enable(); run("특별한단어", "3rd profiled"); pr.disable()
s = io.StringIO(); pstats.Stats(pr, stream=s).sort_stats("cumulative").print_stats(18); print(s.getvalue()[:4000])
# 부분 측정
t = time.time(); n = sum(1 for _ in S.iter_files(root, True)); print("walk only", round(time.time() - t, 2), n)
t = time.time()
for p in S.iter_files(root, True): os.stat(p)
print("walk+stat", round(time.time() - t, 2))
