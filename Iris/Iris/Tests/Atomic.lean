/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.BI.Lib.Atomic
public import Iris.HeapLang.Instances
public import Iris.HeapLang.Notation
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.ProgramLogic.Atomic

@[expose] public section

namespace Iris.Tests

open Iris BI ProofMode HeapLang ProgramLogic Std

/-! Port of `tests/atomic.v`.

Rocq's version is largely a pretty-printing test driven by `Show.` and a `.ref` file.  The
Iris-Lean notations have no unexpanders yet, so the tests below check what is actually
portable: that every notation variant parses and elaborates, and that `iauintro`,
`iaaccintro`, `aupd_aacc` and `imod` work on atomic updates.

`test_awp_apply` and `test_awp_apply_without` are not ported: they need
`iris_heap_lang/lib/atomic_heap.v` and the `awp_apply` tactic, neither of which exists in
Iris-Lean. -/

section GeneralBITests

variable [BI PROP] [BIFUpdate PROP] {TA TB : Type _} (Eo Ei : CoPset)

-- We can quantify over the index types of an atomic update *inside* Iris and use them with
-- atomic updates.  Rocq needs telescopes for this; Iris-Lean's quantifiers range over an
-- arbitrary `Sort`, so plain types suffice.
example : Prop :=
  ⊢@{PROP} ∀ (TA : Type), ∀ (TB : Type), ∀ (α : TA → PROP), ∀ (β : TA → TB → PROP),
    ∀ (Φ : TA → TB → PROP), atomicUpdate Eo Ei α β Φ

-- `iauintro` turns the goal into an atomic accessor whose abort condition is the current context.
/--
error: unsolved goals
PROP : Type u_1
inst✝¹ : BI PROP
inst✝ : BIFUpdate PROP
TA : Type u_2
TB : Type u_3
Eo Ei : CoPset
P : PROP
α : TA → PROP
β Φ : TA → TB → PROP
⊢ ⏎
  ∗HP : P
  ⊢ atomicAcc Eo Ei α P β Φ
-/
#guard_msgs in
example (P : PROP) (α : TA → PROP) (β Φ : TA → TB → PROP) :
    P ⊢ atomicUpdate Eo Ei α β Φ := by
  iintro HP
  iauintro

-- `iaaccintro` proves an atomic accessor from the atomic precondition, leaving the abort and
-- the commit case.
/--
error: unsolved goals
PROP : Type u_1
inst✝¹ : BI PROP
inst✝ : BIFUpdate PROP
TA : Type u_2
TB : Type u_3
Eo Ei : CoPset
x : TA
α : TA → PROP
β Φ : TA → TB → PROP
⊢ ⏎
  ⊢ α x ={Eo}=∗ α x

PROP : Type u_1
inst✝¹ : BI PROP
inst✝ : BIFUpdate PROP
TA : Type u_2
TB : Type u_3
Eo Ei : CoPset
x : TA
α : TA → PROP
β Φ : TA → TB → PROP
⊢ ⏎
  ⊢ ∀ y, β x y ={Eo}=∗ Φ x y
-/
#guard_msgs in
example (x : TA) (α : TA → PROP) (β Φ : TA → TB → PROP) :
    α x ⊢ atomicAcc Eo Eo α (α x) β Φ := by
  iintro Hα
  iaaccintro with Hα
  isplit

-- Several binders per group are packed into a `PSigma`, but the proof mode still works per
-- binder: `%⟨n, b⟩` introduces them separately and reduces the pattern-matching lambda, and
-- `$$ %⟨i, j⟩` instantiates a packed commit binder.  This is what Rocq needs telescopes for.
example (Ψ : Nat → Bool → PROP) (Θ : Nat → Bool → Nat → Nat → PROP) (R : PROP)
    (h : ∀ n b, Ψ n b ⊢ Θ n b 1 2) :
    AU <{ ∃∃ (n : Nat) (b : Bool), Ψ n b }> @ ⊤, ∅
      <{ ∀∀ (i j : Nat), Θ n b i j, COMM R }> ⊢ |={⊤}=> R := by
  iintro HAU
  imod aupd_acc (E := ⊤) (fun _ h => h) $$ HAU with ⟨%⟨n, b⟩, Hα, -, Hcommit⟩
  ihave HΘ : Θ n b 1 2 $$ [Hα]
  · iapply h n b $$ Hα
  imod Hcommit $$ %⟨1, 2⟩ HΘ
  imodintro
  iexact Hcommit

/-! ### The `AU` and `AACC` notations -/

variable (α : PROP) (β Φ : PROP) (Ψ : Nat → PROP) (Θ : Nat → Bool → PROP)

example : Prop := ⊢ AU <{ α }> @ Eo, Ei <{ β, COMM Φ }>
example : Prop := ⊢ AU <{ ∃∃ (n : Nat), Ψ n }> @ Eo, Ei <{ β, COMM Φ }>
example : Prop := ⊢ AU <{ α }> @ Eo, Ei <{ ∀∀ (_b : Bool), β, COMM Φ }>
example : Prop := ⊢ AU <{ ∃∃ (n : Nat), Ψ n }> @ Eo, Ei <{ ∀∀ (b : Bool), Θ n b, COMM Φ }>
example : Prop :=
  ⊢ AU <{ ∃∃ (n m : Nat), Ψ (n + m) }> @ Eo, Ei <{ ∀∀ (b c : Bool), Θ n (b && c), COMM Φ }>

-- `_` is accepted for an index that is never mentioned; several holes in one group get
-- distinct hygienic names, so the packed `PSigma` pattern stays well formed.
example : Prop := ⊢ AU <{ ∃∃ (_ : Nat), α }> @ Eo, Ei <{ β, COMM Φ }>
example : Prop := ⊢ AU <{ ∃∃ (_ _ : Nat), α }> @ Eo, Ei <{ β, COMM Φ }>

-- Binder groups may be dependent: a later binder's type can mention an earlier one.
example (Ψ : Nat → PROP) : Prop :=
  ⊢ AU <{ ∃∃ (n : Nat) (_h : n = 0), Ψ n }> @ Eo, Ei <{ β, COMM Φ }>

example : Prop := ⊢ AACC <{ α, ABORT Φ }> @ Eo, Ei <{ β, COMM Φ }>
example : Prop := ⊢ AACC <{ ∃∃ (n : Nat), Ψ n, ABORT Φ }> @ Eo, Ei <{ β, COMM Φ }>
example : Prop := ⊢ AACC <{ α, ABORT Φ }> @ Eo, Ei <{ ∀∀ (_b : Bool), β, COMM Φ }>
example : Prop :=
  ⊢ AACC <{ ∃∃ (n : Nat), Ψ n, ABORT Φ }> @ Eo, Ei <{ ∀∀ (b : Bool), Θ n b, COMM Φ }>

end GeneralBITests

/-! ### The logically atomic triple notation

Every combination of `∀∀`, `∃∃`, `RET` binders and private postcondition parses and
type-checks.  As in Rocq, `RET` binders are only supported together with a private
postcondition. -/

section TripleNotation

variable {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]

def code : Exp := hl(#())

/-! Without private postcondition or `RET` binders. -/

example (P : Val → IProp GF) : Prop :=
  ⊢ <<{ ∀∀ (x : Val), P x }>> code @ ∅ <<{ ∃∃ (y : Val), P y | RET hl_val(#()) }>>

example (l : Loc) : Prop :=
  ⊢ <<{ ∀∀ (x : Val), l ↦ some x }>> code @ ∅ <<{ l ↦ some x | RET hl_val(#()) }>>

example (l : Loc) : Prop :=
  ⊢ <<{ l ↦ some hl_val(#()) }>> code @ ∅ <<{ ∃∃ (y : Val), l ↦ some y | RET hl_val(#()) }>>

example (l : Loc) : Prop :=
  ⊢ <<{ l ↦ some hl_val(#()) }>> code @ ∅ <<{ l ↦ some hl_val(#()) | RET hl_val(#()) }>>

/-! Several binders per group. -/

example (P : Val → Loc → IProp GF) : Prop :=
  ⊢ <<{ ∀∀ (x : Val) (l : Loc), P x l }>> code @ ∅
    <<{ ∃∃ (y : Val) (k : Loc), P y k | RET hl_val(#()) }>>

/-! With private postcondition. -/

example (P : Val → IProp GF) : Prop :=
  ⊢ <<{ ∀∀ (x : Val), P x }>> code @ ∅
    <<{ ∃∃ (y : Val), P y | (z : Val), RET z; P z }>>

example (P : Val → IProp GF) : Prop :=
  ⊢ <<{ ∀∀ (x : Val), P x }>> code @ ∅ <<{ ∃∃ (y : Val), P y | RET y; P y }>>

example (P : Val → IProp GF) : Prop :=
  ⊢ <<{ ∀∀ (x : Val), P x }>> code @ ∅ <<{ P x | RET x; P x }>>

example (P : Val → IProp GF) : Prop :=
  ⊢ <<{ P hl_val(#()) }>> code @ ∅ <<{ ∃∃ (y : Val), P y | RET y; P y }>>

example (P : IProp GF) : Prop :=
  ⊢ <<{ P }>> code @ ∅ <<{ P | RET hl_val(#42); P }>>

/-! A non-trivial implementation mask. -/

example (P : Val → IProp GF) (N : Namespace) : Prop :=
  ⊢ <<{ ∀∀ (x : Val), P x }>> code @ (↑N : CoPset) <<{ ∃∃ (y : Val), P y | RET hl_val(#()) }>>

end TripleNotation

/-! ### Working with an atomic update obtained from a logically atomic triple -/

section TripleTactics

variable {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]

-- `aupd_aacc` turns the atomic update into an atomic accessor.
/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
P Φ : Val → IProp GF
⊢ ⏎
  ∗Hacc :
  atomicAcc (⊤ \ ∅) ∅ (fun x => P x)
    (atomicUpdate (⊤ \ ∅) ∅ (fun x => P x) (fun x y => P y) fun x y => iprop(∀ z, none -∗? Φ hl_val(#())))
    (fun x y => P y) fun x y => iprop(∀ z, none -∗? Φ hl_val(#()))
  ⊢ WP code {{ Φ }}
-/
#guard_msgs in
example (P : Val → IProp GF) :
    ⊢ <<{ ∀∀ (x : Val), P x }>> code @ ∅ <<{ ∃∃ (y : Val), P y | RET hl_val(#()) }>> := by
  simp only [atomicWp]
  iintro %Φ Hau
  icases aupd_aacc $$ Hau with Hacc

-- `imod` also eliminates an atomic update into a `fupd_finally` goal.
example {TA TB : Type _} {Eo Ei : CoPset} {α : TA → IProp GF} {β Φ : TA → TB → IProp GF}
    (Q : IProp GF) (h : Eo ⊆ ⊤) :
    atomicUpdate Eo Ei α β Φ ⊢ |={⊤|}=> Q -∗ Q := by
  iintro Hau
  imod Hau with ⟨%x, Hα, -, -⟩
  imodintro
  iintro $

-- `imod` eliminates an atomic update against a physically atomic weakest precondition.
/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
inst✝ : HeapLangGS hlc GF
P Φ : Val → IProp GF
x : Val
⊢ ⏎
  ∗Hα : P x
  ∗Hclose :
  (P x ={∅,⊤}=∗ atomicUpdate (⊤ \ ∅) ∅ (fun x => P x) (fun x y => P y) fun x y => iprop(∀ z, none -∗? Φ hl_val(#()))) ∧
    ∀ y, P y ={∅,⊤}=∗ ∀ z, none -∗? Φ hl_val(#())
  ⊢ WP hl(!#↑0) @ ∅ {{ v, |={∅, ⊤}=> Φ v }}
-/
#guard_msgs in
example (P : Val → IProp GF) :
    ⊢ <<{ ∀∀ (x : Val), P x }>> hl(!#(0 : Nat)) @ ∅
      <<{ ∃∃ (y : Val), P y | RET hl_val(#()) }>> := by
  simp only [atomicWp]
  iintro %Φ Hau
  imod Hau with ⟨%x, Hα, Hclose⟩

end TripleTactics

end Iris.Tests

end
