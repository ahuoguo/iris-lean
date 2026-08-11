/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Bai
-/
module

public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.Invariants
public import Iris.ProgramLogic.WeakestPre

namespace Iris

open ProgramLogic Language.Notation Std BI ProofMode

@[expose] public section

/-!
# Logically atomic Hoare triples

```
<<{ ∀∀ x, atomic_precondition }>>
  code @ E
<<{ ∃∃ y, atomic_postcondition | z, RET return_value; private_postcondition }>>
```

Here `x` is bound in both pre- and postconditions, the return value and the private
postcondition, `y` is bound in the postconditions and the return value, and `z` is bound
in the return value and the private postcondition.  Every binder group may be omitted, and
so may the private postcondition (`; private_postcondition`); as in Rocq, `z` binders are
only supported together with a private postcondition.

-/

/-- Eliminate an atomic update with `imod` when the goal is a `fupd_finally`.  See
`elimModal_aupd_fupd` for why Rocq's single generic instance is split up here. -/
instance elimModal_aupd_fupd_finally {hlc} {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {TA TB : Type _} {Eo Ei E : CoPset} {α : TA → IProp GF} {β Φ : TA → TB → IProp GF}
    {p : Bool} {io : InOut} {Q : IProp GF} :
    ElimModal (Eo ⊆ E) p io false
      (atomicUpdate Eo Ei α β Φ)
      iprop(∃ x, α x ∗ ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀ y, β x y ={Ei,E}=∗ Φ x y)))
      iprop(|={E|}=> Q) iprop(|={Ei|}=> Q) where
  elim_modal h :=
    (sep_mono_left (intuitionisticallyIf_mono (aupd_acc h))).trans (elim_modal trivial)

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

/-- The inner mask is hard-coded to be empty, because we have yet to find an example where
we want it to be anything else.

For the non-atomic postcondition we use an `Option (IProp GF)` combined with `-∗?`.  This
avoids introducing spurious `emp -∗` into proofs that do not need one (which is most of them). -/
@[rocq_alias atomic_wp]
def atomicWp {TA TB TP : Type _}
    (e : Expr)
    (E : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val)
    : IProp GF :=
  iprop(∀ (Φ : Val → IProp GF),
    atomicUpdate (⊤ \ E) ∅ α β (fun x y => iprop(∀ z, POST x y z -∗? Φ (f x y z))) -∗
      WP e {{ Φ }})


section Notation
open Lean

public meta section

syntax auRet := auBinder+ ", "

def unpackRet : Option (TSyntax ``auRet) → MacroM (List (Ident × Term))
  | none => return []
  | some stx => do
    let `(auRet| $bs*, ) := stx | Macro.throwUnsupported
    unpackBinders bs

syntax:max "<<{ " (auForall)? term " }>> " term:max " @ " term:max
  " <<{ " (auExists)? term " | " (auRet)? "RET " term (" ; " term)? " }>>" : term

macro_rules
  | `(<<{ $[$xs]? $α }>> $e @ $E <<{ $[$ys]? $β | $[$zs]? RET $v $[; $POST]? }>>) => do
    let xs ← unpackForall xs
    let ys ← unpackExists ys
    let zs ← unpackRet zs
    let post ← match POST with
      | some POST => `(some iprop($POST))
      | none => `(none)
    `(atomicWp (TA := $(← binderType xs)) (TB := $(← binderType ys))
        (TP := $(← binderType zs)) $e $E
        $(← binderFun xs (← `(iprop($α))))
        $(← binderFun xs (← binderFun ys (← `(iprop($β)))))
        $(← binderFun xs (← binderFun ys (← binderFun zs post)))
        $(← binderFun xs (← binderFun ys (← binderFun zs v))))

end

end Notation

/-! ### Theory -/

section Lemmas

variable {TA TB TP : Type _} {e : Expr} {E : CoPset}
variable {α : TA → IProp GF} {β : TA → TB → IProp GF}
variable {POST : TA → TB → TP → Option (IProp GF)} {f : TA → TB → TP → Val}

/-- Eliminate an atomic update with `imod` when the goal is a weakest precondition for a
physically atomic expression.  See `elimModal_aupd_fupd` for why Rocq's single generic
instance is split up here. -/
instance elimModal_aupd_wp_atomic {TA TB : Type _} {Eo Ei : CoPset}
    {α : TA → IProp GF} {β Φ : TA → TB → IProp GF}
    {p : Bool} {io : InOut} {s : Stuckness} {Φv : Val → IProp GF}
    [hatomic : Language.Atomic ↑s e] :
    ElimModal (Eo ⊆ E) p io false
      (atomicUpdate Eo Ei α β Φ)
      iprop(∃ x, α x ∗ ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀ y, β x y ={Ei,E}=∗ Φ x y)))
      (WP e @ s ; E {{ Φv }}) (WP e @ s ; Ei {{ v, |={Ei,E}=> Φv v }}) where
  elim_modal h :=
    (sep_mono_left (intuitionisticallyIf_mono (aupd_acc h))).trans
      ((elimModalFupdWpAtomic (io := io)).elim_modal hatomic)

/-- Atomic triples imply sequential triples. -/
@[rocq_alias atomic_wp_seq]
theorem atomicWp_seq :
    ⊢ atomicWp e E α β POST f -∗
      ∀ (Φ : Val → IProp GF), ∀ x, α x -∗
        (∀ y, β x y -∗ ∀ z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }} := by
  simp only [atomicWp]
  iintro Hwp %Φ %x Hα HΦ
  iapply wp_frame_wand $$ HΦ
  iapply Hwp
  iauintro
  iaaccintro with Hα
  isplit
  · iintro Hα
    imodintro
    iexact Hα
  · iintro %y Hβ
    imodintro
    iintro %z Hpost HΦ
    iapply HΦ $$ %y Hβ %z Hpost

/-- This version matches the Texan triple, i.e. with a later in front of the continuation. -/
@[rocq_alias atomic_wp_seq_step]
theorem atomicWp_seq_step (he : toVal e = none) :
    ⊢ atomicWp e E α β POST f -∗
      ∀ (Φ : Val → IProp GF), ∀ x, α x -∗
        ▷ (∀ y, β x y -∗ ∀ z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }} := by
  iintro Hwp %Φ %x Hα HΦ
  iapply wp_step_fupd (P := iprop(∀ y, β x y -∗ ∀ z, POST x y z -∗? Φ (f x y z)))
    he LawfulSet.subset_refl $$ [HΦ]
  · imodintro
    inext
    imodintro
    iexact HΦ
  iapply atomicWp_seq $$ Hwp %_ %x Hα
  iintro %y Hβ %z Hpost HΦ
  iapply HΦ $$ %y Hβ %z Hpost

/-- Sequential triples with the empty mask for a physically atomic `e` are atomic. -/
@[rocq_alias atomic_seq_wp_atomic]
theorem atomic_seq_wp_atomic [Language.Atomic .WeaklyAtomic e] :
    ⊢ (∀ (Φ : Val → IProp GF), ∀ x, α x -∗
        (∀ y, β x y -∗ ∀ z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ ∅ {{ Φ }}) -∗
      atomicWp e E α β POST f := by
  simp only [atomicWp]
  iintro Hwp %Φ Hau
  imod aupd_acc LawfulSet.diff_subset_left $$ Hau with ⟨%x, Hα, -, Hclose⟩
  iapply Hwp $$ %_ %x Hα
  iintro %y Hβ %z Hpost
  imod Hclose $$ %y Hβ with HΦ
  iapply HΦ $$ %z Hpost

/-- Sequential triples with a persistent precondition and no initial quantifier are
atomic. -/
@[rocq_alias persistent_seq_wp_atomic]
theorem persistent_seq_wp_atomic {α : PUnit → IProp GF} {β : PUnit → TB → IProp GF}
    {POST : PUnit → TB → TP → Option (IProp GF)} {f : PUnit → TB → TP → Val}
    [Persistent (α .unit)] :
    ⊢ (∀ (Φ : Val → IProp GF), α .unit -∗
        (∀ y, β .unit y -∗ ∀ z, POST .unit y z -∗? Φ (f .unit y z)) -∗
        WP e {{ Φ }}) -∗
      atomicWp e E α β POST f := by
  simp only [atomicWp]
  iintro Hwp %Φ Hau
  iapply fupd_wp
  imod aupd_acc LawfulSet.diff_subset_left $$ Hau with ⟨%_, #Hα, Hclose, -⟩
  imod Hclose $$ Hα with Hau
  imodintro
  iapply wp_fupd
  iapply Hwp $$ Hα
  iintro %y Hβ %z Hpost
  imod aupd_acc LawfulSet.diff_subset_left $$ Hau with ⟨%_, -, -, Hclose⟩
  imod Hclose $$ %y Hβ with HΦ
  iapply HΦ $$ %z Hpost

-- TODO:
private theorem diff_subset_diff_right {E1 E2 : CoPset} (HE : E1 ⊆ E2) :
    ⊤ \ E2 ⊆ ⊤ \ E1 := by
  intro x hx
  rw [LawfulSet.mem_diff] at hx ⊢
  exact ⟨hx.1, fun h => hx.2 (HE x h)⟩

private theorem top_diff_subset_diff_diff {E : CoPset} {N : Namespace}
    (HN : (↑N : CoPset) ⊆ E) : ⊤ \ E ⊆ (⊤ \ (E \ ↑N)) \ ↑N := by
  intro x hx
  simp only [LawfulSet.mem_diff] at hx ⊢
  exact ⟨⟨CoPset.mem_full, fun h => hx.2 h.1⟩, fun h => hx.2 (HN x h)⟩

@[rocq_alias atomic_wp_mask_weaken]
theorem atomicWp_mask_weaken {E1 E2 : CoPset} (HE : E1 ⊆ E2) :
    atomicWp e E1 α β POST f ⊢ atomicWp e E2 α β POST f := by
  simp only [atomicWp]
  iintro Hwp %Φ Hau
  iapply Hwp
  iapply atomicUpdate_mask_weaken (diff_subset_diff_right HE) $$ Hau

/-- We can open invariants around atomic triples.  (Just for demonstration purposes; we
always use `iinv` in proofs.) -/
@[rocq_alias atomic_wp_inv]
theorem atomicWp_inv {N : Namespace} {I : IProp GF} (HN : (↑N : CoPset) ⊆ E) :
    ⊢ atomicWp e (E \ ↑N) (fun x => iprop(▷ I ∗ α x)) (fun x y => iprop(▷ I ∗ β x y))
        POST f -∗
      inv N I -∗ atomicWp e E α β POST f := by
  simp only [atomicWp, BIBase.wandM]
  iintro Hwp #Hinv %Φ Hau
  iapply Hwp
  iauintro
  iinv N with HI
  · refine ⟨fun x hx => ?_, trivial⟩
    rw [LawfulSet.mem_diff, LawfulSet.mem_diff]
    exact ⟨CoPset.mem_full, fun h => h.2 hx⟩
  iapply aacc_aupd (top_diff_subset_diff_diff HN) $$ Hau
  iintro %x Hα
  iaaccintro with [HI Hα]
  · iframe HI Hα
  isplit
  · iintro ⟨HI, Hα⟩
    imodintro
    iframe Hα
    iintro Hau
    imodintro
    iframe HI Hau #
  · iintro %y ⟨HI, Hβ⟩
    imodintro
    iright
    iexists y
    iframe Hβ
    iintro HΦ
    imodintro
    iframe HI HΦ #

end Lemmas

end

end Iris
