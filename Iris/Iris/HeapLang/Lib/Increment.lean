/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.ProgramLogic.Atomic

namespace Iris.HeapLang

open BI ProgramLogic Std

@[expose] public section

/-!
# Logically atomic increment

Port of `iris_heap_lang/lib/increment.v`, showing that implementing fetch-and-add on top of
compare-and-swap preserves logical atomicity.

Only the `increment_physical` section is ported: increment directly on top of the physical
heap.  The `increment` and `increment_client` sections build on
`iris_heap_lang/lib/atomic_heap.v` (the `atomic_heap` interface) and on the `awp_apply`
tactic from `iris_heap_lang/proofmode.v`; neither exists in Iris-Lean yet.
-/

namespace Increment

def incrPhy : Val := hl_val%
  rec incr l :=
    let oldv := !l;
    if cas(l, oldv, oldv + #1) then oldv else incr l

section Proof

variable [HeapLangGS hlc GF]

theorem incrPhy_spec (l : Loc) :
    ⊢ <<{ ∀∀ (v : Int), l ↦ some hl_val(#v) }>> hl(&incrPhy #(.loc l)) @ ∅
      <<{ l ↦ some hl_val(#(v + 1 : Int)) | RET hl_val(#v) }>> := by
  simp only [atomicWp, BIBase.wandM]
  iintro %Φ HAU
  iloeb as IH
  wp_rec
  -- `imod` knows how to eliminate atomic updates.  They are mask-changing though, so we
  -- first bind to make sure we have an atomic expression.  Out of the update we get the
  -- atomic precondition together with the two closing updates — one to abort and one to
  -- commit; here we only need to abort.
  wp_bind !_
  imod HAU with ⟨%v, Hl, Hclose, -⟩
  wp_load
  imod Hclose $$ Hl with HAU
  imodintro
  wp_pures
  -- As above, but this time we need both the abort and the commit update.
  wp_bind cmpXchg(_, _, _)
  imod HAU with ⟨%w, Hl, Hclose⟩
  by_cases hvw : v = w
  · subst hvw
    wp_cmpxchg_suc
    icases Hclose with ⟨-, Hclose⟩
    imod Hclose $$ %() Hl with HΦ
    imodintro
    wp_pures
    iapply HΦ $$ %()
  · wp_cmpxchg_fail
    · intro h
      simp at h
      exact hvw h.symm
    icases Hclose with ⟨Hclose, -⟩
    imod Hclose $$ Hl with HAU
    imodintro
    wp_pures
    iapply IH $$ HAU

end Proof

end Increment

end

end Iris.HeapLang
