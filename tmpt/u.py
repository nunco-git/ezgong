import os, sys, io, base64, time, tempfile
which = sys.argv[1]
def grab(name, bbox):
    from PIL import ImageGrab
    img = ImageGrab.grab(bbox=bbox); b = io.BytesIO(); img.save(b, "PNG"); s = base64.b64encode(b.getvalue()).decode()
    for i in range(0, len(s), 4000): print("IMG%s:%s" % (name, s[i:i+4000]), flush=True)
res = []
def check(c, n): res.append(("OK  " if c else "FAIL") + " " + n)
if which == "se":
    sys.path.insert(0, "smart-explorer")
    import smart_explorer as S, tkinter as tk
    S.APP_VERSION = "1.0.0"            # 옛 버전인 척 → 실제 깃허브 확인
    base = tempfile.mkdtemp()
    for i in range(6): os.makedirs(os.path.join(base, "폴더%d" % i))
    for i in range(3): open(os.path.join(base, "파일%d.txt" % i), "w").write("x")
    inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
    app.s["update_checked"] = 0
    def pump(t):
        e = time.time() + t
        while time.time() < e: root.update(); time.sleep(0.03)
    def go():
        app.check_update()
        pane = app.panes[0]; pane.navigate(base); pump(8)
        n0 = len(pane.tree.get_children())
        pane.toggle_dirs(); pump(0.5)
        n1 = len(pane.tree.get_children())
        check(n0 == 9 and n1 == 3, "폴더 숨기기: %d → %d" % (n0, n1))
        check("보이기" in pane.dir_btn.cget("text"), "버튼 글자 바뀜")
        check(pane.get_state()["hide_dirs"], "상태 저장")
        check(app.update_btn.winfo_manager() == "pack", "업데이트 필요 버튼 (info=%s)" % app.update_info)
        root.geometry("1200x500+0+0"); pump(1)
        x, y = root.winfo_rootx(), root.winfo_rooty()
        grab("se", (x, y - 32, x + root.winfo_width(), y + 200))
        pane.toggle_dirs(); pump(0.5)
        check(len(pane.tree.get_children()) == 9, "다시 누르면 폴더 보임")
        print("\n".join(res), flush=True); os._exit(0)
    root.after(1500, go); root.mainloop()
else:
    sys.path.insert(0, "smart-clipboard")
    import smart_clipboard as S
    S.DATA_DIR = tempfile.mkdtemp()
    S.APP_VERSION = "1.0.0"
    app = S.App()
    def go():
        app.show(); app.root.geometry("700x480+100+60")
        app.check_update(force=True)
        e = time.time() + 8
        while time.time() < e and not app.update_info:
            app.root.update(); time.sleep(0.05)
        for _ in range(10): app.root.update(); time.sleep(0.05)
        check(app.upd_lbl.winfo_ismapped(), "업데이트 필요 표시 (info=%s)" % app.update_info)
        r = app.root; x, y = r.winfo_rootx(), r.winfo_rooty()
        grab("clip", (x - 8, y + r.winfo_height() - 60, x + r.winfo_width() + 8, y + r.winfo_height() + 8))
        app.update_check_var.set(False); app._show_update_btn(); app.root.update()
        check(not app.upd_lbl.winfo_ismapped(), "새 버전 확인 끄면 숨김")
        print("\n".join(res), flush=True); os._exit(0)
    app.root.after(1500, go); app.run()
