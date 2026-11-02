import os, sys, time, ctypes, tempfile, io, base64
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
u = ctypes.windll.user32
def mdown(x, y): u.SetCursorPos(int(x), int(y)); time.sleep(0.1); u.mouse_event(2, 0, 0, 0, 0)
def mmove(x, y): u.SetCursorPos(int(x), int(y)); u.mouse_event(1, 0, 0, 0, 0)
def mup(): u.mouse_event(4, 0, 0, 0, 0)
base = tempfile.mkdtemp(); A = os.path.join(base, "A"); B = os.path.join(base, "B"); os.makedirs(A); os.makedirs(B)
for i in range(3): open(os.path.join(A, "f%d.txt" % i), "w").write("x")
os.makedirs(os.path.join(A, "sub"))
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
res = []
def check(c, n): res.append(("OK  " if c else "FAIL") + " " + n); print(res[-1], flush=True)
def pump(t):
    e = time.time() + t
    while time.time() < e: root.update(); time.sleep(0.02)
def shot(name):
    from PIL import ImageGrab
    img = ImageGrab.grab(); b = io.BytesIO(); img.save(b, "PNG"); s = base64.b64encode(b.getvalue()).decode()
    for i in range(0, len(s), 4000): print("IMG%s:%s" % (name, s[i:i+4000]), flush=True)
def go():
    try:
        root.geometry("1000x700+0+0"); app.set_layout(2, 1); pump(2)
        p1, p2 = app.panes[0], app.panes[1]
        p1.navigate(A); p2.navigate(B); pump(2)
        print("panes", len(app.panes), p1.cwd, p2.cwd, flush=True)
        # 1) transfer 직접
        ok = app.transfer([os.path.join(A, "f0.txt")], B, move=True, source=p1); pump(1)
        check(os.path.exists(os.path.join(B, "f0.txt")) and not os.path.exists(os.path.join(A, "f0.txt")), "transfer 이동 (ok=%s)" % ok)
        # 2) 잘라내기 → 붙여넣기
        p1.load_browse(); pump(0.5)
        iid = [i for i in p1.tree.get_children() if p1.hits[i]["name"] == "f1.txt"][0]
        p1.tree.selection_set(iid); p1.clip(cut=True); p2.paste(); pump(1)
        check(os.path.exists(os.path.join(B, "f1.txt")) and not os.path.exists(os.path.join(A, "f1.txt")), "Ctrl+X → Ctrl+V 이동")
        # 3) 실제 마우스로 끌어 놓기
        p1.load_browse(); pump(0.5)
        iid = [i for i in p1.tree.get_children() if p1.hits[i]["name"] == "f2.txt"][0]
        p1.tree.see(iid); pump(0.3)
        bx, by, bw, bh = p1.tree.bbox(iid)
        sx, sy = p1.tree.winfo_rootx() + bx + 30, p1.tree.winfo_rooty() + by + bh // 2
        tx, ty = p2.tree.winfo_rootx() + 80, p2.tree.winfo_rooty() + p2.tree.winfo_height() - 30
        mdown(sx, sy); pump(0.2)
        for k in range(1, 21):
            mmove(sx + (tx - sx) * k / 20, sy + (ty - sy) * k / 20); pump(0.05)
        print("hint:", app.hint_var.get(), flush=True)
        shot("drag")
        mup(); pump(1.5)
        check(os.path.exists(os.path.join(B, "f2.txt")) and not os.path.exists(os.path.join(A, "f2.txt")), "마우스로 끌어 다른 칸에 놓기")
        print("A:", os.listdir(A), "B:", os.listdir(B), flush=True)
    except Exception:
        import traceback; traceback.print_exc()
    os._exit(0)
root.after(1500, go); root.mainloop()
