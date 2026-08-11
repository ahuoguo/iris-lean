/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Bai
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.ProgramLogic.Atomic

namespace Iris.HeapLang

open BI ProgramLogic Std

@[expose] public section

namespace Treiber

def newStack : Val := hl_val% λ _, ref(ref(none()))

def push : Val := hl_val%
  rec push s x :=
    let hd := !s;
    let s' := ref(some((x, hd)));
    if cas(s, hd, s') then #() else push s x

def pop : Val := hl_val%
  rec pop s :=
    let hd := !s;
    match !hd with
    | some(cell) => if cas(s, hd, snd(cell)) then some(fst(cell)) else pop s
    | none() => none()

def iter : Val := hl_val%
  rec iter hd f :=
    match !hd with
    | none() => #()
    | some(cell) => f (fst(cell)); iter (snd(cell)) f

section Proof

variable [HeapLangGS hlc GF]

/-- Agreement between two persistent points-to assertions.  Stating the location and the
fractions explicitly keeps the proof-mode framing goals metavariable-free. -/
private theorem pointsTo_discard_agree (l : Loc) (v₁ v₂ : Option Val) :
    l ↦{.discard} v₁ ∗ l ↦{.discard} v₂ ⊢@{IProp GF} ⌜v₁ = v₂⌝ := pointsTo_agree

/-- `isList hd xs` says that `hd` is the head of an immutable singly-linked list holding
the values `xs`. -/
def isList : Loc → List Val → IProp GF
  | hd, [] => hd ↦{.discard} some hl_val(none())
  | hd, x :: xs =>
    iprop(∃ hd' : Loc, hd ↦{.discard} some hl_val(some((&x, #(.loc hd')))) ∗ isList hd' xs)

instance isList_persistent (hd : Loc) (xs : List Val) :
    Persistent (isList (GF := GF) hd xs) := by
  induction xs generalizing hd with
  | nil =>
    simp only [isList]
    infer_instance
  | cons x xs ih =>
    simp only [isList]
    infer_instance

instance isList_timeless (hd : Loc) (xs : List Val) :
    Timeless (isList (GF := GF) hd xs) := by
  induction xs generalizing hd with
  | nil =>
    simp only [isList]
    infer_instance
  | cons x xs ih =>
    simp only [isList]
    infer_instance

theorem uniq_isList (xs ys : List Val) (hd : Loc) :
    isList (GF := GF) hd xs ∗ isList hd ys ⊢ ⌜xs = ys⌝ := by
  induction xs generalizing ys hd with
  | nil =>
    cases ys with
    | nil =>
      iintro -
      ipureintro
      rfl
    | cons y ys =>
      simp only [isList]
      iintro ⟨Hxs, %hd', Hhd, -⟩
      icases pointsTo_discard_agree hd _ _ $$ [$Hxs $Hhd] with %h
      exact absurd h (by simp)
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [isList]
      iintro ⟨⟨%hd', Hhd, -⟩, Hys⟩
      icases pointsTo_discard_agree hd _ _ $$ [$Hhd $Hys] with %h
      exact absurd h (by simp)
    | cons y ys =>
      simp only [isList]
      iintro ⟨⟨%hd₁, Hhd₁, Hxs⟩, %hd₂, Hhd₂, Hys⟩
      icases pointsTo_discard_agree hd _ _ $$ [$Hhd₁ $Hhd₂] with %h
      obtain ⟨rfl, rfl⟩ : x = y ∧ hd₁ = hd₂ := by simpa using h
      icases ih ys hd₁ $$ [$Hxs $Hys] with %h
      ipureintro
      rw [h]

def isStack (s : Loc) (xs : List Val) : IProp GF :=
  iprop(∃ hd : Loc, s ↦ some hl_val(#(.loc hd)) ∗ isList hd xs)

instance isStack_timeless (s : Loc) (xs : List Val) :
    Timeless (isStack (GF := GF) s xs) := by
  simp only [isStack]
  infer_instance

theorem newStack_spec :
    {{ True }} hl(&newStack #()) {{ s, RET hl_val(#(.loc s)); isStack (GF := GF) s [] }} := by
  iintro %Φ - HΦ
  wp_rec
  wp_bind ref(none())
  wp_alloc l with Hl
  imod pointsTo_persist $$ Hl with #Hl
  wp_alloc l' with Hl'
  imodintro
  iapply HΦ
  simp only [isStack, isList]
  iexists l
  iframe Hl' Hl

theorem push_atomic_spec (s : Loc) (x : Val) :
    ⊢ <<{ ∀∀ (xs : List Val), isStack (GF := GF) s xs }>> hl(&push #(.loc s) &x) @ ∅
      <<{ isStack s (x :: xs) | RET hl_val(#()) }>> := by
  simp only [atomicWp, isStack, BIBase.wandM]
  iintro %Φ HP
  iloeb as IH
  wp_rec
  wp_let
  wp_bind !_
  imod HP with ⟨%xs, ⟨%hd, Hs, Hhd⟩, Hvs', -⟩
  wp_load
  imod Hvs' $$ [Hs Hhd] with HP
  · iexists hd
    iframe Hs Hhd
  imodintro
  wp_let
  wp_alloc l with Hl
  wp_let
  imod pointsTo_persist $$ Hl with #Hl
  wp_bind cmpXchg(_, _, _)
  imod HP with ⟨%xs', ⟨%hd', Hs', Hhd'⟩, Hvs'⟩
  by_cases heq : hd = hd'
  · subst heq
    wp_cmpxchg_suc
    icases Hvs' with ⟨-, Hvs'⟩
    imod Hvs' $$ %() [Hs' Hhd' Hl] with HQ
    · iexists l
      simp only [isList]
      iframe Hs'
      iexists hd
      iframe Hl Hhd'
    imodintro
    wp_pures
    iapply HQ $$ %()
  · wp_cmpxchg_fail
    · intro h
      simp at h
      exact heq h.symm
    icases Hvs' with ⟨Hvs', -⟩
    imod Hvs' $$ [Hs' Hhd'] with HP
    · iexists hd'
      iframe Hs' Hhd'
    imodintro
    wp_pures
    iapply IH $$ HP

theorem pop_atomic_spec (s : Loc) :
    ⊢ <<{ ∀∀ (xs : List Val), isStack (GF := GF) s xs }>> hl(&pop #(.loc s)) @ ∅
      <<{ (match xs with | [] => isStack s [] | _ :: xs' => isStack s xs')
        | RET (match xs with | [] => hl_val(none()) | x :: _ => hl_val(some(&x))) }>> := by
  simp only [atomicWp, isStack, BIBase.wandM]
  iintro %Φ HP
  iloeb as IH
  wp_rec
  wp_bind !_
  imod HP with ⟨%xs, ⟨%hd, Hs, #Hhd⟩, Hvs'⟩
  cases xs with
  | nil =>
    simp only [isList]
    wp_load
    icases Hvs' with ⟨-, Hvs'⟩
    imod Hvs' $$ %() [Hs] with HQ
    · iexists hd
      iframe Hs Hhd
    imodintro
    wp_let
    wp_load
    wp_pures
    iapply HQ $$ %()
  | cons y xs' =>
    simp only [isList]
    icases Hhd with ⟨%hd', #Hhd, #Hxs'⟩
    wp_load
    icases Hvs' with ⟨Hvs', -⟩
    imod Hvs' $$ [Hs] with HP
    · iexists hd
      iframe Hs
      iexists hd'
      iframe Hhd Hxs'
    imodintro
    wp_let
    wp_load
    wp_match
    wp_proj
    wp_bind cmpXchg(_, _, _)
    imod HP with ⟨%xs'', ⟨%hd'', Hs'', Hhd''⟩, Hvs'⟩
    by_cases heq : hd = hd''
    · subst heq
      wp_cmpxchg_suc
      icases Hvs' with ⟨-, Hvs'⟩
      cases xs'' with
      | nil =>
        simp only [isList]
        icases pointsTo_discard_agree hd (some hl_val(some((&y, #(.loc hd')))))
          (some hl_val(none())) $$ [$Hhd $Hhd''] with %h
        exact absurd h (by simp)
      | cons x'' xs'' =>
        simp only [isList]
        icases Hhd'' with ⟨%hd''', Hhd'', Hxs''⟩
        icases pointsTo_discard_agree hd (some hl_val(some((&y, #(.loc hd')))))
          (some hl_val(some((&x'', #(.loc hd'''))))) $$ [$Hhd $Hhd''] with %h
        obtain ⟨rfl, rfl⟩ : y = x'' ∧ hd' = hd''' := by simpa using h
        imod Hvs' $$ %() [Hs'' Hxs''] with HQ
        · iexists hd'
          iframe Hs'' Hxs''
        imodintro
        wp_pures
        iapply HQ $$ %()
    · wp_cmpxchg_fail
      · intro h
        simp at h
        exact heq h.symm
      icases Hvs' with ⟨Hvs', -⟩
      imod Hvs' $$ [Hs'' Hhd''] with HP
      · iexists hd''
        iframe Hs'' Hhd''
      imodintro
      wp_pures
      iapply IH $$ HP

end Proof

end Treiber

end

end Iris.HeapLang
