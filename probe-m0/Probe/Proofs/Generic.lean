import Probe.Stmts.M
namespace Probe

-- generic + instance binder flowing through the stmt abbrev
theorem generic_thm : generic_stmt := by
  intro A _ xs
  omega

end Probe
