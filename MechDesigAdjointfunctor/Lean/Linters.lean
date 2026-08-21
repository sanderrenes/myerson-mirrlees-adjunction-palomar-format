import Lean
import Batteries.Tactic.Lint

/-!
# Project linters: statements that say nothing

Two checks for the failure mode this project has actually suffered (D14): a declaration that
compiles, looks green, and **states nothing**.  Neither is a hard gate.  See `DECISIONS.md` D17.

* `linter.trueStatement` — a **compiler warning**, fired at elaboration, on any declaration whose
  conclusion is `True`.  Precise and decidable.  This is D14's exact failure:
  `theorem failure_ironing : True := trivial`.
* `witnessless` — a **`#lint` report**, on any theorem tagged `@[needs_witness]` for which no
  `@[witness_for]` exists.  Advisory by construction: `#lint` never runs during `lake build`.

**Neither linter can tell you a statement is *vacuous*.**  Satisfiability of a hypothesis set is
undecidable; nothing here changes that.  `witnessless` is a checklist, not a proof — it records
that you *intended* a witness and have not produced one.  The only real test remains
instantiating the theorem at a mechanism anyone cares about, which is what the `postedPrice_*`
family does for the envelope hypotheses (D7).
-/

open Lean Elab Command

namespace MechDesign.Linter

/-! ### 1. The `True`-statement linter -/

register_option linter.trueStatement : Bool := {
  defValue := true
  descr := "warn on a declaration whose conclusion is `True` — a statement that says nothing"
}

/-- The conclusion of a (possibly dependent) statement: strip every leading `∀`. -/
private partial def conclusionOf : Expr → Expr
  | .forallE _ _ body _ => conclusionOf body
  | e => e

/-- Warn on any declaration whose conclusion is `True`.

`True` is inhabited by `trivial`, so such a declaration always compiles and always looks
finished.  It constrains nothing and proves nothing.  If it is standing in for a claim you
cannot yet state, that is what `TODO.md` is for — a `True` in the corpus is indistinguishable
from a real result to anyone reading the file. -/
def trueStatementLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless linter.trueStatement.get (← getOptions) do return
    let some declIdStx := stx.find? (·.isOfKind ``Parser.Command.declId) | return
    let declName := (← getCurrNamespace) ++ declIdStx[0].getId
    -- Silently ignore anything we cannot resolve: a linter that guesses is worse than none.
    let some ci := (← getEnv).find? declName | return
    if (conclusionOf ci.type).isConstOf ``True then
      Linter.logLint linter.trueStatement declIdStx
        m!"`{declName}` states `True`, which says nothing and is proved by `trivial`.\n\
           If this is standing in for a claim, put the claim in `TODO.md` and delete this. \
           If it is deliberate, silence with `set_option linter.trueStatement false in`."

initialize addLinter trueStatementLinter

/-! ### 2. The witness registry -/

/-- Mark a theorem as one whose hypotheses ought to be shown satisfiable by some concrete
instance.  Opt-in: tagging is how you say the obligation exists. -/
initialize needsWitnessAttr : TagAttribute ←
  registerTagAttribute `needs_witness
    "this theorem's hypotheses should be witnessed by a concrete instance"

/-- Environment extension recording `witness_for` edges: witness ↦ the theorem it witnesses. -/
initialize witnessExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (w, t) => m.insert w t
    addImportedFn := fun nss => nss.foldl (init := {}) fun m ns =>
      ns.foldl (init := m) fun m (w, t) => m.insert w t
  }

/-- `@[witness_for foo]` records that this declaration instantiates `foo`'s hypotheses at a
concrete object — evidence that `foo` is not vacuous. -/
syntax (name := witnessForStx) "witness_for " ident : attr

initialize registerBuiltinAttribute {
  name := `witnessForStx
  descr := "records that this declaration witnesses the hypotheses of the named theorem"
  add := fun decl stx _ => do
    let tgt ← match stx with
      | `(attr| witness_for $id:ident) => Elab.realizeGlobalConstNoOverloadWithInfo id
      | _ => throwError "invalid `witness_for` attribute: expected `@[witness_for thmName]`"
    modifyEnv (witnessExt.addEntry · (decl, tgt))
}

/-- Every theorem that some declaration is a `@[witness_for]`. -/
private def witnessedTheorems (env : Environment) : NameSet :=
  (witnessExt.getState env).foldl (fun s _ tgt => s.insert tgt) {}

/-- **Theorems that asked for a witness and have none.**

Reports any `@[needs_witness]` theorem with no `@[witness_for]` pointing at it.  This does not
prove the theorem is vacuous — nothing can, in general. It records only that you said the
hypotheses deserved an instance and there isn't one. `#lint` never gates `lake build`, so this
is advice, not an obligation. -/
@[env_linter]
meta def witnessless : Batteries.Tactic.Lint.Linter where
  test := fun declName => do
    let env ← getEnv
    unless needsWitnessAttr.hasTag env declName do return none
    if (witnessedTheorems env).contains declName then return none
    return m!"tagged `@[needs_witness]` but nothing is `@[witness_for {declName}]`. \
              Its hypotheses have never been shown satisfiable by a concrete instance."
  noErrorsFound := "All theorems that asked for a witness have one."
  errorsFound := "THEOREMS ASKED FOR A WITNESS AND HAVE NONE. \
    A hypothesis set with no instance has never been shown to be satisfiable — the theorem may \
    be vacuously true. See D7: the two-sided envelope condition was not merely strong, it \
    excluded every reserve-price auction, and only instantiating it at the posted price \
    revealed that."

end MechDesign.Linter
