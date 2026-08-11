/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Bai
-/
module

public import Iris.BI
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode
public import Iris.Std.CoPset

@[expose] public section

namespace Iris
open Std BI ProofMode

/-- Conveniently split a conjunction on both assumption and conclusion -/
@[rocq_alias iSplitWith]
local macro "isplitwith " H:ident : tactic =>
  `(tactic| (iapply and_parallel $$ $H:ident
             isplit <;> iintro $H:ident))

section Definition

variable [BI PROP] [BIFUpdate PROP] {TA TB : Type _}
variable {Eo Ei : CoPset} {α : TA → PROP} {P P1 P2 : PROP} {β Φ Φ1 Φ2 : TA → TB → PROP}

/-- `atomicAcc` is the "introduction form" of atomic updates: an accessor that can be
aborted back to `P`. -/
@[rocq_alias atomic_acc]
def atomicAcc (Eo Ei : CoPset) (α : TA → PROP) (P : PROP) (β Φ : TA → TB → PROP) : PROP :=
  iprop(|={Eo,Ei}=> ∃ x, α x ∗ ((α x ={Ei,Eo}=∗ P) ∧ (∀ y, β x y ={Ei,Eo}=∗ Φ x y)))

@[rocq_alias atomic_acc_wand]
theorem atomicAcc_wand :
    ⊢ ((P1 -∗ P2) ∧ (∀ x y, Φ1 x y -∗ Φ2 x y)) -∗
      atomicAcc Eo Ei α P1 β Φ1 -∗ atomicAcc Eo Ei α P2 β Φ2 := by
  simp only [atomicAcc]
  iintro HP12 AS
  imod AS with ⟨%x, Hα, Hclose⟩
  imodintro
  iexists x
  iframe Hα
  isplit
  · iintro Hα
    icases Hclose with ⟨Hclose, -⟩
    icases HP12 with ⟨HP12, -⟩
    imod Hclose $$ Hα
    imodintro
    iapply HP12 $$ Hclose
  · iintro %y Hβ
    icases Hclose with ⟨-, Hclose⟩
    icases HP12 with ⟨-, HP12⟩
    imod Hclose $$ %y Hβ
    imodintro
    iapply HP12 $$ %x %y Hclose

@[rocq_alias atomic_acc_mask]
theorem atomicAcc_mask {Ed : CoPset} :
    atomicAcc Eo (Eo \ Ed) α P β Φ ⊣⊢
      ∀ E, ⌜Eo ⊆ E⌝ → atomicAcc E (E \ Ed) α P β Φ := by
  constructor
  · simp only [atomicAcc]
    iintro Hstep %E %HE
    iapply fupd_mask_frame_acc HE $$ Hstep
    iintro ⟨%x, Hα, Hclose⟩ !> Hclose'
    iexists x
    iframe
    isplitwith Hclose
    · iintro Hα
      iapply Hclose' $$ (Hclose $$ Hα)
    · iintro %y Hβ
      iapply Hclose' $$ (Hclose $$ %y Hβ)
  · exact (forall_elim Eo).trans <|
      (and_intro .rfl (pure_intro fun _ h => h)).trans imp_elim_left

@[rocq_alias atomic_acc_mask_weaken]
theorem atomicAcc_mask_weaken {Eo1 Eo2 : CoPset} (HE : Eo1 ⊆ Eo2) :
    atomicAcc Eo1 Ei α P β Φ ⊢ atomicAcc Eo2 Ei α P β Φ := by
  simp only [atomicAcc]
  iintro Hstep
  imod fupd_mask_subseteq HE with Hclose1
  imod Hstep with ⟨%x, Hα, Hclose2⟩
  imodintro
  iexists x
  iframe Hα
  isplitwith Hclose2
  · iintro Hα
    imod Hclose2 $$ Hα
    imod Hclose1
    imodintro
    iexact Hclose2
  · iintro %y Hβ
    imod Hclose2 $$ %y Hβ
    imod Hclose1
    imodintro
    iexact Hclose2

@[rocq_alias atomic_update_pre]
def atomicUpdate.pre (Eo Ei : CoPset) (α : TA → PROP) (β Φ : TA → TB → PROP)
    (Ψ : Unit → PROP) (_ : Unit) : PROP :=
  atomicAcc Eo Ei α (Ψ ()) β Φ

@[rocq_alias atomic_update_pre_mono]
instance atomicUpdate.pre.mono : BIMonoPred (atomicUpdate.pre Eo Ei α β Φ) where
  mono_pred {Ψ1 Ψ2 _ _} := by
    simp only [atomicUpdate.pre]
    iintro #HΨ %_ Hacc
    iapply atomicAcc_wand $$ [HΨ] Hacc
    isplit
    · iapply HΨ
    · iintro %x %y $
  mono_pred_ne.ne _ _ _ _ := .rfl

@[rocq_alias atomic_update]
def atomicUpdate (Eo Ei : CoPset) (α : TA → PROP) (β Φ : TA → TB → PROP) : PROP :=
  bi_greatest_fixpoint (atomicUpdate.pre Eo Ei α β Φ) ()

end Definition

#rocq_ignore atomic_update_def "We do not use Iris' custom seal/unseal visibility control"
#rocq_ignore atomic_update_aux "We do not use Iris' custom seal/unseal visibility control"
#rocq_ignore atomic_update_unseal "We do not use Iris' custom seal/unseal visibility control"

section Notation
open Lean

public meta section

syntax auBinder := binderIdent <|> ("(" binderIdent+ " : " term ")")

def binderName : TSyntax ``binderIdent → MacroM Ident
  | `(binderIdent| $x:ident) => return x
  | _ => withFreshMacroScope do return mkIdent (← MonadQuotation.addMacroScope `x)

def unpackBinders (bs : Array (TSyntax ``auBinder)) : MacroM (List (Ident × Term)) := do
  let mut out := #[]
  for b in bs do
    match b with
    | `(auBinder| $x:binderIdent) => out := out.push (← binderName x, ← `(_))
    | `(auBinder| ($xs:binderIdent* : $t)) =>
      for x in xs do out := out.push (← binderName x, t)
    | _ => Macro.throwUnsupported
  return out.toList

def binderType : List (Ident × Term) → MacroM Term
  | [] => `(Unit)
  | [(_, t)] => return t
  | (x, t) :: bs => do `(PSigma (α := $t) fun $x:ident => $(← binderType bs))

def binderFun : List (Ident × Term) → Term → MacroM Term
  | [], body => `(fun _ => $body)
  | [(x, _)], body => do
    let b : TSyntax ``Lean.Parser.Term.funBinder := ⟨x.raw⟩
    `(fun $b => $body)
  | bs, body => do
    let pat ← `(term| ⟨$(bs.map (·.1) |>.toArray),*⟩)
    let b : TSyntax ``Lean.Parser.Term.funBinder := ⟨pat.raw⟩
    `(fun $b => $body)

syntax auExists := "∃∃ " auBinder+ ", "
syntax auForall := "∀∀ " auBinder+ ", "

def unpackExists : Option (TSyntax ``auExists) → MacroM (List (Ident × Term))
  | none => return []
  | some stx => do
    let `(auExists| ∃∃ $bs*, ) := stx | Macro.throwUnsupported
    unpackBinders bs

def unpackForall : Option (TSyntax ``auForall) → MacroM (List (Ident × Term))
  | none => return []
  | some stx => do
    let `(auForall| ∀∀ $bs*, ) := stx | Macro.throwUnsupported
    unpackBinders bs

syntax:max "AU" " <{ " (auExists)? term " }>" " @ " term ", " term
  " <{ " (auForall)? term ", " "COMM " term " }>" : term

syntax:max "AACC" " <{ " (auExists)? term ", " "ABORT " term " }>" " @ " term ", " term
  " <{ " (auForall)? term ", " "COMM " term " }>" : term

macro_rules
  | `(AU <{ $[$xs]? $α }> @ $Eo, $Ei <{ $[$ys]? $β, COMM $Φ }>) => do
    let xs ← unpackExists xs
    let ys ← unpackForall ys
    `(atomicUpdate (TA := $(← binderType xs)) (TB := $(← binderType ys)) $Eo $Ei
        $(← binderFun xs (← `(iprop($α))))
        $(← binderFun xs (← binderFun ys (← `(iprop($β)))))
        $(← binderFun xs (← binderFun ys (← `(iprop($Φ))))))
  | `(AACC <{ $[$xs]? $α, ABORT $P }> @ $Eo, $Ei <{ $[$ys]? $β, COMM $Φ }>) => do
    let xs ← unpackExists xs
    let ys ← unpackForall ys
    `(atomicAcc (TA := $(← binderType xs)) (TB := $(← binderType ys)) $Eo $Ei
        $(← binderFun xs (← `(iprop($α)))) iprop($P)
        $(← binderFun xs (← binderFun ys (← `(iprop($β)))))
        $(← binderFun xs (← binderFun ys (← `(iprop($Φ))))))
end

end Notation

section Lemmas

variable [BI PROP] [BIFUpdate PROP] {TA TB : Type _}
variable {Eo Ei : CoPset} {α : TA → PROP} {P : PROP} {β Φ : TA → TB → PROP}

@[rocq_alias atomic_acc_ne]
theorem atomicAcc_ne {n} {α1 α2 : TA → PROP} {P1 P2 : PROP}
    {β1 β2 Φ1 Φ2 : TA → TB → PROP} (Hα : ∀ x, α1 x ≡{n}≡ α2 x) (HP : P1 ≡{n}≡ P2)
    (Hβ : ∀ x y, β1 x y ≡{n}≡ β2 x y) (HΦ : ∀ x y, Φ1 x y ≡{n}≡ Φ2 x y) :
    atomicAcc Eo Ei α1 P1 β1 Φ1 ≡{n}≡ atomicAcc Eo Ei α2 P2 β2 Φ2 :=
  BIFUpdate.ne.ne <| exists_ne fun x => sep_ne.ne (Hα x) <| and_ne.ne
    (wand_ne.ne (Hα x) (BIFUpdate.ne.ne HP))
    (forall_ne fun y => wand_ne.ne (Hβ x y) (BIFUpdate.ne.ne (HΦ x y)))

@[rocq_alias atomic_update_ne]
theorem atomicUpdate_ne {n} {α1 α2 : TA → PROP} {β1 β2 Φ1 Φ2 : TA → TB → PROP}
    (Hα : ∀ x, α1 x ≡{n}≡ α2 x) (Hβ : ∀ x y, β1 x y ≡{n}≡ β2 x y)
    (HΦ : ∀ x y, Φ1 x y ≡{n}≡ Φ2 x y) :
    atomicUpdate Eo Ei α1 β1 Φ1 ≡{n}≡ atomicUpdate Eo Ei α2 β2 Φ2 :=
  exists_ne fun _ => sep_ne.ne
    (intuitionistically_ne.ne <| forall_ne fun _ =>
      wand_ne.ne .rfl (atomicAcc_ne Hα .rfl Hβ HΦ))
    .rfl

@[rocq_alias aupd_unfold]
theorem aupd_unfold :
    atomicUpdate Eo Ei α β Φ ⊣⊢ atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ :=
  .of_eq (greatest_fixpoint_unfold _)

@[rocq_alias aupd_aacc]
theorem aupd_aacc :
    atomicUpdate Eo Ei α β Φ ⊢
    atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ :=
  aupd_unfold.mp

@[rocq_alias aupd_intro]
theorem aupd_intro (Ψ : PROP) (H : Ψ ⊢ atomicAcc Eo Ei α Ψ β Φ) :
    Ψ ⊢ atomicUpdate Eo Ei α β Φ := by
  simp only [atomicUpdate]
  iintro HΨ
  iapply greatest_fixpoint_coiter (I := ⟨fun _ _ _ _ => .rfl⟩) (atomicUpdate.pre Eo Ei α β Φ)
    (fun _ => Ψ) $$ [] HΨ
  iintro !> %_ HΨ
  iunfold atomicUpdate.pre
  iapply H $$ HΨ

@[rocq_alias atomic_update_mask_weaken]
theorem atomicUpdate_mask_weaken {Eo1 Eo2 : CoPset} (HE : Eo1 ⊆ Eo2) :
    atomicUpdate Eo1 Ei α β Φ ⊢ atomicUpdate Eo2 Ei α β Φ :=
  aupd_intro _ <| aupd_aacc.trans <| atomicAcc_mask_weaken HE

/-- The elimination form of an atomic update, with the outer mask weakened to `E`.

Stating the conclusion as an *unfolded* fancy update rather than an `atomicAcc` is the point:
the proof-mode `ElimModal` instances match on `|={E,Ei}=> _`, and `atomicAcc` is opaque to
type-class synthesis. -/
theorem aupd_acc {E : CoPset} (hE : Eo ⊆ E) :
    atomicUpdate Eo Ei α β Φ ⊢
      |={E,Ei}=> ∃ x, α x ∗ ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀ y, β x y ={Ei,E}=∗ Φ x y)) :=
  aupd_aacc.trans (atomicAcc_mask_weaken hE)

-- TODO:
/-- This lets you eliminate atomic updates with `imod` when the goal is a fancy update.

Note: Rocq's `elim_mod_aupd` is one instance covering any modality a fancy
update can be eliminated into, via the premise
`∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q'`.  That shape is fine in Iris-Lean as
long as the modality stays abstract — see `elimInv_acc_with_close`, which ports it verbatim
with `M1` a variable.  It breaks once the modality is concrete: `elimModal_timeless` then
becomes a candidate, and its `IntoExcept0 (|={E,Ei}=> R) R` subgoal puts the bound `R` in an
output-parameter slot, which the proof-mode solver rejects.

We therefore mirror the concrete eliminators instead: this one for fancy updates,
`elimModal_aupd_wp_atomic` for weakest preconditions and `elimModal_aupd_fupd_finally` for
`fupd_finally`.  For any other goal, eliminate the update by hand with
`imod (aupd_acc h) $$ Hau`. -/
@[rocq_alias elim_mod_aupd]
instance elimModal_aupd_fupd {p : Bool} {io : InOut} {E E' : CoPset} {Q : PROP} :
    ElimModal (Eo ⊆ E) p io false
      (atomicUpdate Eo Ei α β Φ)
      iprop(∃ x, α x ∗ ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀ y, β x y ={Ei,E}=∗ Φ x y)))
      iprop(|={E,E'}=> Q) iprop(|={Ei,E'}=> Q)
      where
  elim_modal hE :=
    (sep_mono_left (intuitionisticallyIf_mono (aupd_acc hE))).trans (elim_modal trivial)

@[rocq_alias aacc_intro]
theorem aacc_intro (HE : Ei ⊆ Eo) (x : TA) :
    ⊢ α x -∗ ((α x ={Eo}=∗ P) ∧ (∀ y, β x y ={Eo}=∗ Φ x y)) -∗
      atomicAcc Eo Ei α P β Φ := by
  simp only [atomicAcc]
  iintro Hα Hclose
  iapply fupd_mask_intro HE
  iintro Hclose'
  iexists x
  iframe Hα
  isplitwith Hclose
  · iintro Hα
    imod Hclose' with -
    iapply Hclose $$ Hα
  · iintro %y Hβ
    imod Hclose' with -
    iapply Hclose $$ %y Hβ

/-- This lets you open invariants etc. when the goal is an atomic accessor. -/
@[rocq_alias elim_acc_aacc]
instance elimAcc_aacc {X : Type} {E1 E2 : CoPset} {α' β' : X → PROP} {γ' : X → Option PROP}
    {Pas : PROP} :
    ElimAcc (X := X) True (fupd E1 E2) (fupd E2 E1) α' β' γ'
      (atomicAcc E1 Ei α Pas β Φ)
      (fun x' => atomicAcc E2 Ei α iprop(β' x' ∗ (γ' x' -∗? Pas)) β
        (fun x y => iprop(β' x' ∗ (γ' x' -∗? Φ x y)))) where
  elim_acc := by
    simp only [accessor, atomicAcc]
    iintro %_ Hinner >⟨%x', Hα', Hclose⟩
    imod Hinner $$ %x' Hα' with ⟨%x, Hα, Hclose'⟩
    iapply fupd_mask_intro LawfulSet.subset_refl
    iintro Hclose''
    iexists x
    iframe Hα
    isplitwith Hclose'
    · iintro Hα
      imod Hclose'' with -
      imod Hclose' $$ Hα with ⟨Hβ', HPas⟩
      imod Hclose $$ Hβ' with Hγ'
      imodintro
      cases γ' x' with simp_all
      | none => iexact HPas
      | some _ => iapply HPas $$ Hγ'
    · iintro %y Hβ
      imod Hclose'' with -
      imod Hclose' $$ %y Hβ with ⟨Hβ', HΦ⟩
      imod Hclose $$ Hβ' with Hγ'
      imodintro
      cases γ' x' with simp_all
      | none => iexact HΦ
      | some _ => iapply HΦ $$ Hγ'

@[rocq_alias elim_modal_acc]
instance elimModal_acc {p q : Bool} {io : InOut} {φ : Prop} {Pmod Pmod' Q' : PROP}
    [h : ElimModal φ p io q Pmod Pmod'
      iprop(|={Eo,Ei}=> ∃ x, α x ∗ ((α x ={Ei,Eo}=∗ P) ∧ (∀ y, β x y ={Ei,Eo}=∗ Φ x y))) Q'] :
    ElimModal φ p io q Pmod Pmod' (atomicAcc Eo Ei α P β Φ) Q' := h

/-- Lemmas for directly proving one atomic accessor in terms of another (or an atomic
update).  These are only really useful when the atomic accessor you are trying to prove
exactly corresponds to an atomic update/accessor you have as an assumption -- which
is not very common. -/
@[rocq_alias aacc_aacc]
theorem aacc_aacc {TA' TB' : Type _} {E1 E1' E2 E3 : CoPset}
    {α' : TA' → PROP} {P' : PROP} {β' Φ' : TA' → TB' → PROP} (HE : E1' ⊆ E1) :
    ⊢ atomicAcc E1' E2 α P β Φ -∗
      (∀ x, α x -∗ atomicAcc E2 E3 α' iprop(α x ∗ (P ={E1}=∗ P')) β'
        (fun x' y' => iprop((α x ∗ (P ={E1}=∗ Φ' x' y'))
          ∨ ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
      atomicAcc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  ihave Hacc : atomicAcc E1 E2 α P β Φ $$ [Hupd]
  · iapply atomicAcc_mask_weaken HE $$ Hupd
  iunfold atomicAcc at Hacc
  iunfold atomicAcc
  imod Hacc with ⟨%x, Hα, Hclose⟩
  ispecialize Hstep $$ %x Hα
  iunfold atomicAcc at Hstep
  imod Hstep with ⟨%x', Hα', Hclose'⟩
  imodintro
  iexists x'
  iframe Hα'
  isplit
  · iintro Hα'
    icases Hclose' with ⟨Hclose', -⟩
    imod Hclose' $$ Hα' with ⟨Hα, Hupd⟩
    icases Hclose with ⟨Hclose, -⟩
    imod Hclose $$ Hα
    iapply Hupd $$ Hclose
  · iintro %y' Hβ'
    icases Hclose' with ⟨-, Hclose'⟩
    imod Hclose' $$ %y' Hβ' with (⟨Hα, HΦ'⟩ | ⟨%y, Hβ, HΦ'⟩)
    · icases Hclose with ⟨Hclose, -⟩
      imod Hclose $$ Hα
      iapply HΦ' $$ Hclose
    · icases Hclose with ⟨-, Hclose⟩
      imod Hclose $$ %y Hβ
      iapply HΦ' $$ Hclose

@[rocq_alias aacc_aupd]
theorem aacc_aupd {TA' TB' : Type _} {E1 E1' E2 E3 : CoPset}
    {α' : TA' → PROP} {P' : PROP} {β' Φ' : TA' → TB' → PROP} (HE : E1' ⊆ E1) :
    ⊢ atomicUpdate E1' E2 α β Φ -∗
      (∀ x, α x -∗ atomicAcc E2 E3 α'
        iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P')) β'
        (fun x' y' => iprop((α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ Φ' x' y'))
          ∨ ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
      atomicAcc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  ihave Hacc : atomicAcc E1' E2 α (atomicUpdate E1' E2 α β Φ) β Φ $$ [Hupd]
  · iapply aupd_aacc $$ Hupd
  iapply aacc_aacc HE $$ Hacc Hstep

@[rocq_alias aacc_aupd_commit]
theorem aacc_aupd_commit {TA' TB' : Type _} {E1 E1' E2 E3 : CoPset}
    {α' : TA' → PROP} {P' : PROP} {β' Φ' : TA' → TB' → PROP} (HE : E1' ⊆ E1) :
    ⊢ atomicUpdate E1' E2 α β Φ -∗
      (∀ x, α x -∗ atomicAcc E2 E3 α'
        iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P')) β'
        (fun x' y' => iprop(∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
      atomicAcc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  iapply aacc_aupd HE $$ Hupd
  iintro %x Hα
  iapply atomicAcc_wand $$ [] (Hstep $$ %x Hα)
  isplit
  · iintro $
  · iintro %x' %y' H
    iright
    iexact H

@[rocq_alias aacc_aupd_abort]
theorem aacc_aupd_abort {TA' TB' : Type _} {E1 E1' E2 E3 : CoPset}
    {α' : TA' → PROP} {P' : PROP} {β' Φ' : TA' → TB' → PROP} (HE : E1' ⊆ E1) :
    ⊢ atomicUpdate E1' E2 α β Φ -∗
      (∀ x, α x -∗ atomicAcc E2 E3 α'
        iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P')) β'
        (fun x' y' => iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ Φ' x' y')))) -∗
      atomicAcc E1 E3 α' P' β' Φ' := by
  iintro Hupd Hstep
  iapply aacc_aupd HE $$ Hupd
  iintro %x Hα
  iapply atomicAcc_wand $$ [] (Hstep $$ %x Hα)
  isplit
  · iintro $
  · iintro %x' %y' H
    ileft
    iexact H

end Lemmas

public meta section

open Lean Elab Tactic Meta ProofModeM in
elab "iauintro" : tactic =>
  ProofModeM.runTactic `iauintro fun mvar { hyps, goal, .. } => do
    let some #[_, _, _, _, _, Eo, Ei, α, β, Φ] := goal.consumeMData.appM? ``atomicUpdate
      | throwIPMError "goal is not an atomic update"
    let acc ← mkAppM ``atomicAcc #[Eo, Ei, α, hyps.tm, β, Φ]
    let m ← addBIGoal hyps acc
    mvar.assign (← mkAppM ``aupd_intro #[hyps.tm, m])

macro "iaaccintro" " with " sel:specPat : tactic =>
  `(tactic| iapply aacc_intro (by first | assumption | trivial | simp) _ $$ $sel:specPat)

end

#rocq_ignore tac_aupd_intro "Functionality already handled by ProofModeM infrastructure"

end Iris
