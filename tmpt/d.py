import os, sys, time, ctypes, tempfile, io, base64, threading, subprocess
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
from ctypes import wintypes
u = ctypes.windll.user32
def mv(x, y): u.SetCursorPos(int(x), int(y)); u.mouse_event(1, 0, 0, 0, 0)
def down(): u.mouse_event(2, 0, 0, 0, 0)
def up(): u.mouse_event(4, 0, 0, 0, 0)
def glide(a, b, n=25, dt=0.04):
    for k in range(1, n + 1):
        mv(a[0] + (b[0] - a[0]) * k / n, a[1] + (b[1] - a[1]) * k / n); time.sleep(dt)
def shot(name):
    from PIL import ImageGrab
    img = ImageGrab.grab(); b = io.BytesIO(); img.save(b, "PNG"); s = base64.b64encode(b.getvalue()).decode()
    for i in range(0, len(s), 4000): print("IMG%s:%s" % (name, s[i:i+4000]), flush=True)
base = tempfile.mkdtemp(); A, B, C, E = (os.path.join(base, n) for n in "ABCE")
for d in (A, B, C, E): os.makedirs(d)
for i in range(3): open(os.path.join(A, "a%d.txt" % i), "w").write("x")
open(os.path.join(E, "external.txt"), "w").write("x")
print("OLE", S.OLE_DND is not None, flush=True)
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
res = []
def check(c, n): res.append(("OK  " if c else "FAIL") + " " + n); print(res[-1], flush=True)
def pump(t):
    e = time.time() + t
    while time.time() < e: root.update(); time.sleep(0.02)
def row_center(p, name):
    iid = [i for i in p.tree.get_children() if p.hits[i]["name"] == name][0]
    p.tree.see(iid); root.update()
    bx, by, bw, bh = p.tree.bbox(iid)
    return p.tree.winfo_rootx() + bx + 40, p.tree.winfo_rooty() + by + bh // 2
def go():
    try:
        root.geometry("640x700+0+0"); app.set_layout(2, 1); pump(2)
        p1, p2 = app.panes[0], app.panes[1]
        p1.navigate(A); p2.navigate(B); pump(2)
        check(app.ole_target is not None, "끌어 놓기 받기 등록")
        # 1) 칸끼리 (OLE)
        sx, sy = row_center(p1, "a0.txt")
        tx, ty = p2.tree.winfo_rootx() + 60, p2.tree.winfo_rooty() + p2.tree.winfo_height() - 40
        def t1():
            time.sleep(0.5); mv(sx, sy); time.sleep(0.2); down(); time.sleep(0.2)
            glide((sx, sy), (tx, ty)); time.sleep(0.6); shot("inner"); up()
        threading.Thread(target=t1, daemon=True).start()
        pump(5)
        check(os.path.exists(os.path.join(B, "a0.txt")) and not os.path.exists(os.path.join(A, "a0.txt")), "칸끼리 끌어 옮기기")
        # 2) 윈도우 탐색기 창으로
        subprocess.Popen(["explorer.exe", C]); time.sleep(4)
        hw = u.FindWindowW("CabinetWClass", None)
        print("explorer hwnd", hw, flush=True)
        u.SetWindowPos(hw, -1, 660, 60, 360, 600, 0x40); time.sleep(1.5)   # HWND_TOPMOST, 보이게
        pump(0.5)
        p1.load_browse(); pump(0.5)
        sx, sy = row_center(p1, "a1.txt")
        def t2():
            time.sleep(0.5); mv(sx, sy); time.sleep(0.2); down(); time.sleep(0.2)
            glide((sx, sy), (840, 450)); time.sleep(0.8); shot("toexplorer"); up()
        threading.Thread(target=t2, daemon=True).start()
        pump(6)
        check(os.path.exists(os.path.join(C, "a1.txt")), "탐색기 창으로 끌어 놓기 (C: %s)" % os.listdir(C))
        u.PostMessageW(hw, 0x10, 0, 0); time.sleep(0.5)
        root.lift(); pump(0.5)
        # 3) 다른 프로그램(별도 창)에서 끌어 오기
        src = subprocess.Popen([sys.executable, "tmpt/src.py", os.path.join(E, "external.txt")])
        time.sleep(4)
        tx, ty = p2.tree.winfo_rootx() + 60, p2.tree.winfo_rooty() + p2.tree.winfo_height() - 40
        def t3():
            mv(900, 650); time.sleep(0.3); down(); time.sleep(0.2)
            glide((900, 650), (tx, ty)); time.sleep(0.8); shot("fromext"); up()
            time.sleep(0.3)
        threading.Thread(target=t3, daemon=True).start()
        pump(7)
        print("hint after:", app.hint_var.get(), flush=True)
        check(os.path.exists(os.path.join(B, "external.txt")), "다른 프로그램에서 끌어 오기 (B: %s)" % os.listdir(B))
        src.kill()
    except Exception:
        import traceback; traceback.print_exc()
    print("\n".join(res), flush=True)
    os._exit(0)
root.after(1500, go); root.mainloop()
