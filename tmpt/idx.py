import os, sys, time, tempfile
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
d = tempfile.mkdtemp()
for i in range(50):
    os.makedirs(os.path.join(d, "f%d" % (i % 5)), exist_ok=True)
    open(os.path.join(d, "f%d" % (i % 5), "doc%d.txt" % i), "w", encoding="utf-8").write("내용 %d 색인시험" % i)
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
ix = app.indexer
ix.stop_flag.set(); time.sleep(0.5); ix.stop_flag.clear()
ix.folders = lambda: [d]
ix._wait_idle = lambda: True
ix._pass()
print("total", ix.total, "read", ix.read, flush=True)
ok1 = ix.total == 50 and ix.read == 50
ix._pass()
print("second read", ix.read, flush=True)
print("OK" if ok1 and ix.read == 0 else "FAIL", "indexer", flush=True)
os._exit(0)
