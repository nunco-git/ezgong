import os, sys, time, ctypes, tempfile, io, base64, threading
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
u = ctypes.windll.user32
def key(vk): u.keybd_event(vk, 0, 0, 0); time.sleep(0.05); u.keybd_event(vk, 0, 2, 0)
def shot(name):
    from PIL import ImageGrab
    img = ImageGrab.grab(); b = io.BytesIO(); img.save(b, "PNG"); s = base64.b64encode(b.getvalue()).decode()
    for i in range(0, len(s), 4000): print("IMG%s:%s" % (name, s[i:i+4000]), flush=True)
base = tempfile.mkdtemp()
for i in range(2): open(os.path.join(base, "doc%d.txt" % i), "w").write("hello")
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
res = []
def check(c, n): res.append(("OK  " if c else "FAIL") + " " + n); print(res[-1], flush=True)
def pump(t):
    e = time.time() + t
    while time.time() < e: root.update(); time.sleep(0.02)
titles = []
def enum_titles():
    out = []
    CB = ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_void_p, ctypes.c_void_p)
    def cb(h, l):
        if u.IsWindowVisible(h):
            b = ctypes.create_unicode_buffer(200); u.GetWindowTextW(h, b, 200); out.append(b.value)
        return True
    u.EnumWindows(CB(cb), 0); return out
def go():
    try:
        root.state("normal"); root.geometry("700x600+0+0"); pump(1)
        p = app.panes[0]; p.navigate(base); pump(1.5)
        iid = [i for i in p.tree.get_children() if p.hits[i]["name"] == "doc0.txt"][0]
        p.tree.selection_set(iid); pump(0.3)
        x, y = p.tree.winfo_rootx() + 80, p.tree.winfo_rooty() + 40
        def t1():
            time.sleep(1.5); shot("menu"); key(0x1B)
        threading.Thread(target=t1, daemon=True).start()
        r = p.windows_menu(x, y); pump(0.5)
        check(True, "파일 Windows 메뉴 열고 닫기 (오류 없음)")
        # Properties (r 키) 실행
        def t2():
            time.sleep(1.5); key(ord("R"))
        threading.Thread(target=t2, daemon=True).start()
        p.windows_menu(x, y); pump(3)
        t = [w for w in enum_titles() if "Properties" in w or "속성" in w]
        print("titles", t, flush=True)
        check(bool(t), "Windows 메뉴의 '속성' 실행")
        shot("props")
        # 빈 곳 메뉴
        p.tree.selection_set(())
        def t3():
            time.sleep(1.5); shot("bgmenu"); key(0x1B)
        threading.Thread(target=t3, daemon=True).start()
        p.windows_menu(x, y + 120); pump(0.5)
        check(True, "빈 곳 Windows 메뉴 (오류 없음)")
    except Exception:
        import traceback; traceback.print_exc()
    print("\n".join(res), flush=True)
    os._exit(0)
root.after(1500, go); root.mainloop()
