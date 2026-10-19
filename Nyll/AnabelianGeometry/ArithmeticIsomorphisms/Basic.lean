/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport

/-! # Continuous isomorphisms over a fixed quotient

The quotient maps are retained as actual homomorphisms. Their kernels, rather
than the entire target group, supply the inner equivalence relation.
-/

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u v w z

variable {G : Type u} {H : Type v} {K : Type w} {Γ : Type z}
  [Group G] [Group H] [Group K] [Group Γ]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]

/-- A continuous group isomorphism commuting with the two specified quotient maps. -/
def OverQuotientEquiv (p : G →* Γ) (q : H →* Γ) :=
  { e : G ≃ₜ* H // ∀ g : G, q (e g) = p g }

namespace OverQuotientEquiv

variable {p : G →* Γ} {q : H →* Γ} {r : K →* Γ}

/-- The identity isomorphism over a quotient. -/
def refl (p : G →* Γ) : OverQuotientEquiv p p :=
  ⟨ContinuousMulEquiv.refl G, fun _ => rfl⟩

/-- Composition of isomorphisms over the same quotient. -/
def trans (e : OverQuotientEquiv p q) (f : OverQuotientEquiv q r) :
    OverQuotientEquiv p r :=
  ⟨e.1.trans f.1, fun g => (f.2 (e.1 g)).trans (e.2 g)⟩

/-- Inversion preserves the fixed quotient. -/
def symm (e : OverQuotientEquiv p q) : OverQuotientEquiv q p :=
  ⟨e.1.symm, fun h => by
    calc
      p (e.1.symm h) = q (e.1 (e.1.symm h)) := (e.2 _).symm
      _ = q h := congrArg q (e.1.apply_symm_apply h)⟩

/-- Correct the target by an element of the geometric kernel. -/
def innerTarget [IsTopologicalGroup H] (e : OverQuotientEquiv p q)
    (c : H) (hc : q c = 1) : OverQuotientEquiv p q :=
  ⟨ProCGroups.innerCorrectedGroupEquiv e.1 c, fun g => by
    change q (c * e.1 g * c⁻¹) = p g
    rw [map_mul, map_mul, map_inv, hc, e.2 g]
    simp only [one_mul, inv_one, mul_one]⟩

/-- Associativity is inherited from composition of the actual continuous maps. -/
theorem trans_assoc {L : Type*} [Group L] [TopologicalSpace L] {s : L →* Γ}
    (e : OverQuotientEquiv p q) (f : OverQuotientEquiv q r)
    (h : OverQuotientEquiv r s) : (e.trans f).trans h = e.trans (f.trans h) := by
  apply Subtype.ext
  apply ContinuousMulEquiv.ext
  intro g
  rfl

theorem refl_trans (e : OverQuotientEquiv p q) : (refl p).trans e = e := by
  apply Subtype.ext
  apply ContinuousMulEquiv.ext
  intro g
  rfl

theorem trans_refl (e : OverQuotientEquiv p q) : e.trans (refl q) = e := by
  apply Subtype.ext
  apply ContinuousMulEquiv.ext
  intro g
  rfl

theorem self_trans_symm (e : OverQuotientEquiv p q) : e.trans e.symm = refl p := by
  apply Subtype.ext
  apply ContinuousMulEquiv.ext
  exact e.1.symm_apply_apply

theorem symm_trans_self (e : OverQuotientEquiv p q) : e.symm.trans e = refl q := by
  apply Subtype.ext
  apply ContinuousMulEquiv.ext
  exact e.1.apply_symm_apply

end OverQuotientEquiv

/-- Two isomorphisms differ by target conjugation from the geometric kernel. -/
def GeometricInnerRelated {p : G →* Γ} {q : H →* Γ}
    (e f : OverQuotientEquiv p q) : Prop :=
  ∃ c : H, q c = 1 ∧ ∀ g : G, f.1 g = c * e.1 g * c⁻¹

namespace GeometricInnerRelated

variable {p : G →* Γ} {q : H →* Γ} {r : K →* Γ}

protected theorem refl (e : OverQuotientEquiv p q) : GeometricInnerRelated e e := by
  refine ⟨1, map_one q, ?_⟩
  intro g
  simp only [one_mul, inv_one, mul_one]

protected theorem symm {e f : OverQuotientEquiv p q}
    (h : GeometricInnerRelated e f) : GeometricInnerRelated f e := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨c⁻¹, ?_, ?_⟩
  · rw [map_inv, hc, inv_one]
  · intro g
    rw [he g]
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

protected theorem trans {e f h : OverQuotientEquiv p q}
    (hef : GeometricInnerRelated e f) (hfh : GeometricInnerRelated f h) :
    GeometricInnerRelated e h := by
  obtain ⟨c, hc, he⟩ := hef
  obtain ⟨d, hd, hf⟩ := hfh
  refine ⟨d * c, ?_, ?_⟩
  · rw [map_mul, hd, hc, mul_one]
  · intro g
    rw [hf g, he g, mul_inv_rev]
    simp only [mul_assoc]

/-- Composition descends to geometric inner classes. -/
theorem comp {e e' : OverQuotientEquiv p q} {f f' : OverQuotientEquiv q r}
    (he : GeometricInnerRelated e e') (hf : GeometricInnerRelated f f') :
    GeometricInnerRelated (e.trans f) (e'.trans f') := by
  obtain ⟨c, hc, heq⟩ := he
  obtain ⟨d, hd, hfq⟩ := hf
  refine ⟨d * f.1 c, ?_, ?_⟩
  · rw [map_mul, hd, f.2 c, hc, mul_one]
  · intro g
    change f'.1 (e'.1 g) = (d * f.1 c) * f.1 (e.1 g) * (d * f.1 c)⁻¹
    rw [hfq, heq, map_mul, map_mul, map_inv, mul_inv_rev]
    simp only [mul_assoc]

/-- Inverting the isomorphisms transports geometric conjugation to the source kernel. -/
theorem inv {e f : OverQuotientEquiv p q}
    (h : GeometricInnerRelated e f) : GeometricInnerRelated e.symm f.symm := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨e.1.symm c⁻¹, ?_, ?_⟩
  · rw [← e.2, e.1.apply_symm_apply, map_inv, hc, inv_one]
  · intro y
    have hy := he (f.1.symm y)
    rw [f.1.apply_symm_apply] at hy
    have hmul := congrArg (fun a : H => c⁻¹ * a * c) hy
    apply e.1.injective
    simpa only [OverQuotientEquiv.symm, map_mul, map_inv,
      e.1.apply_symm_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hmul.symm

end GeometricInnerRelated

/-- The equivalence relation uses only the kernel of the target quotient map. -/
def geometricInnerSetoid (p : G →* Γ) (q : H →* Γ) :
    Setoid (OverQuotientEquiv p q) where
  r := GeometricInnerRelated
  iseqv := ⟨GeometricInnerRelated.refl,
    GeometricInnerRelated.symm, GeometricInnerRelated.trans⟩

/-- Isomorphisms over the fixed quotient, modulo geometric inner automorphisms. -/
def OuterEquiv (p : G →* Γ) (q : H →* Γ) :=
  Quotient (geometricInnerSetoid p q)

namespace OuterEquiv

variable {p : G →* Γ} {q : H →* Γ} {r : K →* Γ}

/-- The outer class of a specified isomorphism. -/
def mk (e : OverQuotientEquiv p q) : OuterEquiv p q :=
  Quotient.mk (geometricInnerSetoid p q) e

/-- Equality of classes means conjugation by an actual geometric-kernel element. -/
theorem mk_eq_mk_iff (e f : OverQuotientEquiv p q) :
    mk e = mk f ↔ GeometricInnerRelated e f :=
  Quotient.eq

/-- Composition of geometric outer classes. -/
def trans (e : OuterEquiv p q) (f : OuterEquiv q r) : OuterEquiv p r :=
  Quotient.liftOn₂ e f (fun e f => mk (e.trans f))
    (fun _ _ _ _ he hf => Quotient.sound (GeometricInnerRelated.comp he hf))

/-- The identity geometric outer class. -/
def refl (p : G →* Γ) : OuterEquiv p p := mk (OverQuotientEquiv.refl p)

/-- Inversion is well defined on geometric outer classes. -/
def symm (e : OuterEquiv p q) : OuterEquiv q p :=
  Quotient.liftOn e (fun e => mk e.symm)
    (fun _ _ h => Quotient.sound (GeometricInnerRelated.inv h))

theorem refl_trans (e : OuterEquiv p q) : (refl p).trans e = e := by
  refine Quotient.inductionOn e ?_
  intro e
  exact congrArg mk (OverQuotientEquiv.refl_trans e)

theorem trans_refl (e : OuterEquiv p q) : e.trans (refl q) = e := by
  refine Quotient.inductionOn e ?_
  intro e
  exact congrArg mk (OverQuotientEquiv.trans_refl e)

theorem self_trans_symm (e : OuterEquiv p q) : e.trans e.symm = refl p := by
  refine Quotient.inductionOn e ?_
  intro e
  exact congrArg mk (OverQuotientEquiv.self_trans_symm e)

theorem symm_trans_self (e : OuterEquiv p q) : e.symm.trans e = refl q := by
  refine Quotient.inductionOn e ?_
  intro e
  exact congrArg mk (OverQuotientEquiv.symm_trans_self e)

theorem trans_assoc {L : Type*} [Group L] [TopologicalSpace L] {s : L →* Γ}
    (e : OuterEquiv p q) (f : OuterEquiv q r) (h : OuterEquiv r s) :
    (e.trans f).trans h = e.trans (f.trans h) := by
  refine Quotient.inductionOn e ?_
  intro e
  refine Quotient.inductionOn f ?_
  intro f
  refine Quotient.inductionOn h ?_
  intro h
  exact congrArg mk (OverQuotientEquiv.trans_assoc e f h)

end OuterEquiv

end AnabelianGeometry.ArithmeticIsomorphisms
