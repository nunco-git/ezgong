import os, sys, time, tempfile, io, base64
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
base = tempfile.mkdtemp()
for i in range(5): open(os.path.join(base, "문서%d.txt" % i), "w", encoding="utf-8").write("미리보기 내용 %d\n" % i * 20)
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
res = []
def check(c, n): res.append(("OK  " if c else "FAIL") + " " + n); print(res[-1], flush=True)
def pump(t):
    e = time.time() + t
    while time.time() < e: root.update(); time.sleep(0.02)
def shot(name):
    from PIL import ImageGrab
    pump(0.8)
    x, y = root.winfo_rootx(), root.winfo_rooty()
    img = ImageGrab.grab(bbox=(x, y - 30, x + root.winfo_width(), y + root.winfo_height()))
    img = img.resize((img.width * 2 // 3, img.height * 2 // 3))
    b = io.BytesIO(); img.save(b, "PNG"); s = base64.b64encode(b.getvalue()).decode()
    for i in range(0, len(s), 4000): print("IMG%s:%s" % (name, s[i:i+4000]), flush=True)
def go():
    try:
        root.state("normal"); root.geometry("1000x680+0+0")
        app.set_layout(1, 1); pump(1.5)
        p = app.panes[0]; p.navigate(base); pump(1)
        p.tree.selection_set(p.tree.get_children()[0]); pump(1)
        check(p.side_preview and str(p.paned.cget("orient")) == "horizontal", "칸 1개 → 미리보기 오른쪽")
        check(p.bf.winfo_rootx() > p.tf.winfo_rootx() + 100, "목록 오른쪽에 미리보기 위치")
        shot("one")
        p.toggle_preview(); pump(0.5)
        check(str(p.bf) not in p.paned.panes(), "숨기기")
        p.toggle_preview(); pump(0.5)
        check(str(p.bf) in p.paned.panes() and p.bf.winfo_ismapped(), "다시 보이기")
        app.set_layout(2, 1); pump(1.5)
        check(all(not q.side_preview for q in app.panes), "칸 2개 → 미리보기 아래")
        check(app.panes[0].bf.winfo_rooty() > app.panes[0].tf.winfo_rooty() + 50, "목록 아래에 미리보기")
        shot("two")
        app.set_layout(1, 1); pump(1)
        check(app.panes[0].side_preview, "다시 1개 → 오른쪽")
        st = app.panes[0].get_state()
        check("sash_side" in st, "경계 위치 저장")
    except Exception:
        import traceback; traceback.print_exc()
    print("\n".join(res), flush=True); os._exit(0)
root.after(1500, go); root.mainloop()
