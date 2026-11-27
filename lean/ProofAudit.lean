import Warmup
import Conjectures
import Lean.Util.CollectAxioms
import Lean.PrivateName

/-! Fail the build if any project declaration uses an axiom beyond Lean's
standard logical axioms `{propext, Classical.choice, Quot.sound}`.
Rejects `sorryAx`, `native_decide` (`Lean.ofReduceBool`), `Lean.trustCompiler`,
and any custom axiom transitively across `Warmup`, `Conjectures`, and all
`Conjectures.*` modules. -/
open Lean Elab Command in
run_cmd do
  let required : Array Name := #[`math_killer_warmup]
  for name in required do
    let _ ← getConstInfo name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut thmCount : Nat := 0
  let mut defCount : Nat := 0
  for (name, info) in env.constants.toList do
    let inProject := match env.getModuleIdxFor? name |>.bind (env.header.modules[·]?) with
      | some mod =>
        let modStr := mod.module.toString
        modStr == "Warmup" ||
          modStr == "Conjectures" ||
          modStr.startsWith "Conjectures."
      | none => false
    if inProject then
      match info with
      | .axiomInfo _ =>
        unless allowed.contains name do
          throwError "Unapproved project axiom: {name}"
      | .thmInfo _ =>
        thmCount := thmCount + 1
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Unapproved axiom {axiomName} in theorem {name}"
      | .defnInfo _ =>
        if !name.isInternal && !isAuxRecursor env name then
          defCount := defCount + 1
          for axiomName in ← collectAxioms name do
            unless allowed.contains axiomName do
              throwError "Unapproved axiom {axiomName} in definition {name}"
      | _ => pure ()
  logInfo m!"PASS: {thmCount} project theorem(s) and {defCount} definition(s) use only propext, Classical.choice, Quot.sound"
