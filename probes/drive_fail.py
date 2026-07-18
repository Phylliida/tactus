import json, subprocess, sys, time
D="/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/driver_out1"; T="/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/drvtree/p_drv"
def snap(k, mods): return {"op":"snapshot","key":k,"modules":mods}
def chk(k, f, m): return {"op":"check","snapshot":k,"file":f,"module":m,"olean":f"{D}/{m}.olean"}
base="TactusDefs_p_drv_exec__base"; root="TactusDefs_p_drv_exec__root"; umb="TactusDefs_p_drv_exec"
stmts=[f"TactusStmts_p_drv_exec__p_drv__{f}" for f in ["mk_node","size_pos","depth_two"]]
reqs=[snap("D0",["TactusDefs"]), chk("D0",f"{T}/{base}.lean",base),
      snap("D1",["TactusDefs",base]), chk("D1",f"{T}/{root}.lean",root),
      snap("D2",["TactusDefs",base,root]), chk("D2",f"{T}/{umb}.lean",umb),
      snap("D3",["TactusDefs",umb])] + [chk("D3",f"{T}/{s}.lean",s) for s in stmts] + [
      snap("D4",["TactusDefs",umb]+stmts)] + [chk("D4",f"{T}/pkg/p_drv__{f}.lean",f"p_drv__{f}") for f in ["mk_node","size_pos","depth_two"]] + [{"op":"exit"}]
t0=time.time()
p=subprocess.Popen(sys.argv[1:],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
p.stdout.readline()
for r in reqs:
    p.stdin.write(json.dumps(r)+"\n"); p.stdin.flush()
    if r["op"]=="exit": break
    j=json.loads(p.stdout.readline())
    errs=[d for d in j.get("diags",[]) if d["sev"]=="error"]
    print(f"[{time.time()-t0:.1f}s] {r.get('module',r.get('key'))}: ok={j['ok']} ms={j['ms']} errs={len(errs)}" + (f" first_err={errs[0]['msg'][:80]!r}" if errs else ""))
p.wait(timeout=60)
