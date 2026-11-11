/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.BaseChange.Points
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Nyll.SchemeTheory.Morphisms.FiniteFieldFixedPoints
public import Mathlib.Logic.Equiv.Basic

/-!
# Rational points and fixed points of the original relative Frobenius

The rational-point dictionary is transported through the actual pullback
point equivalence. Its geometric fixed-point condition uses exactly the
relative Frobenius endomorphism whose pullback acts on étale cohomology.
No smoothness, properness, or finiteness of the scheme is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open GoodReductionJacobian.RelativeGroupLaw

namespace AlgebraicGeometry

universe u

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

local notation "b" => Spec.algebraMap k Ω
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "g" => pullback.snd f b
local notation "F" => Scheme.constantBaseChangeFrobenius k Ω X
local notation "σ" => FiniteField.frobeniusAlgEquivOfAlgebraic k Ω

/-- The existing pullback point equivalence, with the identity structure
map simplified to the original extension of constants. -/
def constantBaseChangePointEquiv :
    SchemeHomOver (𝟙 (Spec (.of Ω))) g ≃ SchemeHomOver b f :=
  (baseChangePointEquiv b (𝟙 (Spec (.of Ω)))).trans
    (Equiv.subtypeEquivRight fun _ => by rw [Category.id_comp])

omit [Fintype k] [Algebra.IsAlgebraic k Ω] in
/-- The point comparison is the original first projection. -/
theorem constantBaseChangePointEquiv_apply
    (x : SchemeHomOver (𝟙 (Spec (.of Ω))) g) :
    (constantBaseChangePointEquiv k Ω X x).val = x.val ≫ pullback.fst f b := rfl

/-- Fixed points for the native power of the relative scheme Frobenius
are exactly the original points fixed on their values. -/
theorem constantBaseChangeFrobenius_pow_fixed_iff (m : ℕ)
    (x : SchemeHomOver (𝟙 (Spec (.of Ω))) g) :
    x.val ≫ ((End.of F) ^ m).asHom = x.val ↔
      Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) ≫
        (constantBaseChangePointEquiv k Ω X x).val =
          (constantBaseChangePointEquiv k Ω X x).val := by
  rw [constantBaseChangePointEquiv_apply]
  constructor
  · intro h
    exact (Scheme.constantBaseChangeFrobenius_pow_point_fst k Ω X m x.val).symm.trans
      (congrArg (fun z => z ≫ pullback.fst f b) h)
  · intro h
    apply pullback.hom_ext
    · exact (Scheme.constantBaseChangeFrobenius_pow_point_fst k Ω X m x.val).trans h
    · rw [Category.assoc, Scheme.constantBaseChangeFrobenius_pow_snd]

variable (E : Type u) [Field E] [Finite E] [Algebra k E]
    [Algebra E Ω] [IsScalarTower k E Ω]
    (m : ℕ) (hm : Module.finrank k E = m)

/-- Points over the specified degree extension are exactly geometric fixed
points of the actual relative Frobenius power used on cohomology. -/
def finiteFieldPointsEquivRelativeFrobeniusPowFixed :
    SchemeHomOver (Spec.algebraMap k E) f ≃
      {x : SchemeHomOver (𝟙 (Spec (.of Ω))) g //
        x.val ≫ ((End.of F) ^ m).asHom = x.val} :=
  (finiteFieldPointsEquivFrobeniusPowFixed k E Ω m hm X f).trans
    ((constantBaseChangePointEquiv k Ω X).subtypeEquiv
      (p := fun x : SchemeHomOver (𝟙 (Spec (.of Ω))) g =>
        x.val ≫ ((End.of F) ^ m).asHom = x.val)
      (q := fun x : SchemeHomOver b f =>
        Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) ≫ x.val = x.val)
      (constantBaseChangeFrobenius_pow_fixed_iff k Ω X m)).symm

/-- This dictionary preserves the original point after extension of constants
and projection from the actual geometric base change. -/
theorem finiteFieldPointsEquivRelativeFrobeniusPowFixed_apply_fst
    (p : SchemeHomOver (Spec.algebraMap k E) f) :
    (finiteFieldPointsEquivRelativeFrobeniusPowFixed k Ω X E m hm p).val.val ≫
        pullback.fst f b = Spec.algebraMap E Ω ≫ p.val := by
  let e := (constantBaseChangePointEquiv k Ω X).subtypeEquiv
    (p := fun x : SchemeHomOver (𝟙 (Spec (.of Ω))) g =>
      x.val ≫ ((End.of F) ^ m).asHom = x.val)
    (q := fun x : SchemeHomOver b f =>
      Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) ≫ x.val = x.val)
    (constantBaseChangeFrobenius_pow_fixed_iff k Ω X m)
  let q := finiteFieldPointsEquivFrobeniusPowFixed k E Ω m hm X f p
  exact congrArg (fun z => z.val.val) (e.apply_symm_apply q)

end AlgebraicGeometry
