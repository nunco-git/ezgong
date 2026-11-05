import os, sys, time, tempfile, json
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
H = {"User-Agent": "SmartExplorer/test", "Accept": "application/vnd.github+json"}
r = json.loads(S._wininet_request("https://api.github.com/repos/nunco-git/ezgong/releases?per_page=3", "GET", dict(H), None, 2**21, 10))
print("wininet GET", len(r), r[0]["tag_name"], flush=True)
try:
    S._wininet_request("https://api.github.com/repos/nunco-git/nope-nope", "GET", dict(H), None, 2**20, 10); print("404 FAIL")
except S.NetHTTPError as e:
    print("wininet 404 ok", e.code, flush=True)
b = json.loads(S._wininet_request("https://httpbin.org/anything", "PATCH", {"User-Agent": "t", "Content-Type": "application/json"}, b'{"a": 1}', 2**20, 15))
print("wininet PATCH", b.get("method"), b.get("json"), flush=True)
import urllib.request, urllib.error
def boom(*a, **k): raise urllib.error.URLError("simulated proxy failure")
urllib.request.urlopen = boom
r = json.loads(S.net_request("https://api.github.com/repos/nunco-git/ezgong/releases?per_page=2", headers=dict(H)))
print("fallback ok", len(r), flush=True)
try:
    S.net_request("https://nonexistent.invalid/x")
except Exception as e:
    print("err text:", S.net_error_text(e), flush=True)
# browse sort
d = tempfile.mkdtemp(); d2 = tempfile.mkdtemp()
for i, n in enumerate(["a.txt", "b.txt", "c.txt"]):
    p = os.path.join(d, n); open(p, "w").write("x"); os.utime(p, (1e9 + i * 1000, 1e9 + i * 1000))
os.makedirs(os.path.join(d, "zdir"))
for i in range(200):
    open(os.path.join(d2, "f%03d.txt" % i), "w").write("x")
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
def go():
    p = app.panes[0]
    p.navigate(d2); root.update(); p.tree.yview_moveto(0.8); root.update()
    p.sort_by("name"); root.update()
    p.navigate(d); root.update()
    names = [p.hits[i]["name"] for i in p.tree.get_children()]
    print("order", names, "y", p.tree.yview()[0], flush=True)
    p.navigate(d2); root.update()
    print("d2 top", p.tree.yview()[0], [p.hits[i]["name"] for i in p.tree.get_children()][:2], flush=True)
    os._exit(0)
root.after(2500, go)
root.after(60000, lambda: os._exit(1))
root.mainloop()
