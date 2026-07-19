import json, subprocess, sys, time
reqs = [
  {"op":"snapshot","key":"S1","modules":["TactusDefs"]},
  {"op":"check","snapshot":"S1","file":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/drvtree2/p_drv2/TactusDefs_p_drv2_exec.lean","module":"TactusDefs_p_drv2_exec","olean":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/driver_out/TactusDefs_p_drv2_exec.olean"},
  {"op":"snapshot","key":"S2","modules":["TactusDefs","TactusDefs_p_drv2_exec"]},
  {"op":"check","snapshot":"S2","file":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/drvtree2/p_drv2/TactusStmts_p_drv2_exec__p_drv2__leaf_of.lean","module":"TactusStmts_p_drv2_exec__p_drv2__leaf_of","olean":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/driver_out/TactusStmts_p_drv2_exec__p_drv2__leaf_of.olean"},
  {"op":"check","snapshot":"S2","file":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/drvtree2/p_drv2/TactusStmts_p_drv2_exec__p_drv2__mk_node.lean","module":"TactusStmts_p_drv2_exec__p_drv2__mk_node","olean":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/driver_out/TactusStmts_p_drv2_exec__p_drv2__mk_node.olean"},
  {"op":"snapshot","key":"S3","modules":["TactusDefs","TactusDefs_p_drv2_exec","TactusStmts_p_drv2_exec__p_drv2__leaf_of","TactusStmts_p_drv2_exec__p_drv2__mk_node"]},
  {"op":"check","snapshot":"S3","file":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/drvtree2/p_drv2/pkg/p_drv2__leaf_of.lean","module":"p_drv2__leaf_of","olean":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/driver_out/p_drv2__leaf_of.olean"},
  {"op":"check","snapshot":"S3","file":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/drvtree2/p_drv2/pkg/p_drv2__mk_node.lean","module":"p_drv2__mk_node","olean":"/tmp/claude-1000/-home-bepis-prog-verus-cad/98c0ee23-9b5e-4975-949c-51f4abcb70be/scratchpad/driver_out/p_drv2__mk_node.olean"},
  {"op":"exit"},
]
t0=time.time()
p = subprocess.Popen(sys.argv[1:], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
ready = p.stdout.readline()
print(f"[{time.time()-t0:.1f}s] ready: {ready.strip()}")
for r in reqs:
    p.stdin.write(json.dumps(r)+"\n"); p.stdin.flush()
    if r["op"]=="exit": break
    resp = p.stdout.readline()
    print(f"[{time.time()-t0:.1f}s] {r['op']}({r.get('module',r.get('key'))}): {resp.strip()[:200]}")
p.wait(timeout=60)
print("stderr:", p.stderr.read()[:500])
