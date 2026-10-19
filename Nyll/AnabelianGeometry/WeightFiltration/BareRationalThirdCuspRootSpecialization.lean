/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BareRationalCuspDecomposition
import Nyll.JacobianVarieties.Kummer.RationalConfigurationArithmeticPairKummerUnits
import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroRationalRootAction

/-!
# Root specialization at the same chosen third-cusp decomposition prime

Use exactly the rational-place choice, normalization-prime family, and
arithmetic comap used by `rationalConfigurationChosenDecomposition`.
The full geometric divisor of the unchanged pair unit, with an arbitrary
integer multiplicity, proves order zero at this chosen arithmetic place when
the third label differs from the pair. The argument can therefore be the
source unit or the actual target power, without selecting another function.
All ambient algebras, closure instances, and towers are the existing bare
configuration suppliers. The resulting root coordinate retains evaluation,
full constant-root scaling, and the decomposition action at that same prime.

The action is labelled by literal restriction to the fixed constants. The
arithmetic fundamental-group projection's fixed inner correction is not
identified or discarded here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace SchemeTheory EtaleFundamentalGroups.Inertia
open EtaleFundamentalGroups.StrictHenselian AnabelianGeometry.KummerTheory
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower
  normalizationCommAlgGaloisAction

local instance (priority := 2000) thirdCuspSpecializationSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- The unchanged pair unit or its actual power specializes at the original third-cusp
prime. Order zero and all ambient-field suppliers are derived internally;
the same root coordinate retains both full scaling and the actual prime's
original decomposition action. -/
theorem rationalConfiguration_pair_thirdChosenPrime_rootSpecialization
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k))) (a b c : s)
    (hca : c ≠ a) (hcb : c ≠ b)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (m : ℤ) (n : ℕ+)
    (u : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) (u.val : RatFunc k)) =
        m * ((if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
          (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0))) :
    let U := rationalConfigurationGeometricScheme k κ s
    let M := projectiveLineRatFuncModel κ
    let j : U ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
    letI : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
    letI : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
    let ambient := rationalConfigurationAmbient_scalarTowers k κ s Ω
    letI : IsScalarTower κ (RatFunc κ) Ω := ambient.2.1
    letI : IsScalarTower (RatFunc k) (RatFunc κ) Ω := ambient.2.2.2.1
    letI : IsScalarTower k κ Ω := ambient.2.2.2.2.1
    letI : IsScalarTower k (RatFunc k) Ω := ambient.2.2.2.2.2
    letI : IsAlgClosure (RatFunc k) Ω :=
      rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
    letI : IsSepClosure (RatFunc k) Ω := inferInstance
    letI : IsGalois (RatFunc k) Ω := inferInstance
    let p := rationalConfigurationBoundaryPlace k κ s c
    let V := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose
    let hV : V.IsRational :=
      (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.1
    let hord : ∀ x : RatFunc k,
        p.val.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x :=
      (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.2
    let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
    let e := ratFuncRationalPlaceNormalizationEquiv V hV p.val hord (Ω := Ω)
    let Qa : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) :=
      (Q p).comap e.symm.toRingHom
    let rawQa : Ideal (integralClosure V.toValuationSubring Ω) := Qa
    letI : rawQa.IsMaximal := by
      let rawQ : Ideal (integralClosure p.val.toValuationSubring Ω) := Q p
      let : rawQ.IsMaximal := (inferInstance : (Q p).IsMaximal)
      change (rawQ.comap e.symm.toRingHom).IsMaximal
      exact Ideal.comap_isMaximal_of_surjective e.symm.toRingHom e.symm.surjective
    letI : Qa.IsMaximal := (inferInstance : rawQa.IsMaximal)
    let cQa : κ →+* IsLocalRing.ResidueField (Localization.AtPrime rawQa) :=
      (maximalQuotientResidueEquiv rawQa).toRingHom.comp
        (arithmeticConstantResidueMap k V.toValuationSubring κ Ω rawQa)
    ∃ hu0 : V.ord (u.val : RatFunc k) = 0,
    ∃ E : {z : Ω // z ^ (n : ℕ) = algebraMap (RatFunc k) Ω (u.val : RatFunc k)} ≃
        {z : κ // z ^ (n : ℕ) = algebraMap k κ (V.ordZeroValue hV u.val hu0 : k)},
      (∀ z, ∃ r : Localization.AtPrime rawQa,
        integralClosurePrimeToAmbientField V.toValuationSubring (RatFunc k) Ω rawQa r =
            z.val ∧ cQa (E z).val = IsLocalRing.residue (Localization.AtPrime rawQa) r) ∧
      (∀ (ζ : rootsOfUnity (n : ℕ) κ)
        (z : {z : Ω // z ^ (n : ℕ) = algebraMap (RatFunc k) Ω (u.val : RatFunc k)}),
        (E ⟨algebraMap κ Ω (ζ.val : κ) * z.val, by
          have hζ : (ζ.val : κ) ^ (n : ℕ) = 1 :=
            congrArg (fun t : κˣ => (t : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
          rw [mul_pow, ← map_pow, hζ, map_one, one_mul, z.property]⟩).val =
            (ζ.val : κ) * (E z).val) ∧
      ∀ (d : (normalizationDecompositionGroup V.toValuationSubring (RatFunc k) Ω Qa).carrier)
        (z : {z : Ω // z ^ (n : ℕ) = algebraMap (RatFunc k) Ω (u.val : RatFunc k)}),
        (E ⟨d.val z.val, by rw [← map_pow, z.property, d.val.commutes]⟩).val =
          ((d.val.restrictScalars k).restrictNormal κ) (E z).val := by
  intro U M j
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  intro ambient
  let : IsScalarTower κ (RatFunc κ) Ω := ambient.2.1
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := ambient.2.2.2.1
  let : IsScalarTower k κ Ω := ambient.2.2.2.2.1
  let : IsScalarTower k (RatFunc k) Ω := ambient.2.2.2.2.2
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : IsSepClosure (RatFunc k) Ω := inferInstance
  let : IsGalois (RatFunc k) Ω := inferInstance
  intro p V hV hord Q e Qa rawQa
  let : rawQa.IsMaximal := by
    let rawQ : Ideal (integralClosure p.val.toValuationSubring Ω) := Q p
    let : rawQ.IsMaximal := (inferInstance : (Q p).IsMaximal)
    change (rawQ.comap e.symm.toRingHom).IsMaximal
    exact Ideal.comap_isMaximal_of_surjective e.symm.toRingHom e.symm.surjective
  let : Qa.IsMaximal := (inferInstance : rawQa.IsMaximal)
  intro cQa
  have hpa : p.val ≠ (rationalConfigurationBoundaryPlace k κ s a).val := by
    intro h
    apply hca
    apply (rationalConfigurationBoundaryPlaceEquiv k κ s).injective
    exact Subtype.ext h
  have hpb : p.val ≠ (rationalConfigurationBoundaryPlace k κ s b).val := by
    intro h
    apply hcb
    apply (rationalConfigurationBoundaryPlaceEquiv k κ s).injective
    exact Subtype.ext h
  have hu0 : V.ord (u.val : RatFunc k) = 0 := by
    rw [← hord (u.val : RatFunc k), hgeom, ite_eq_right hpa, ite_eq_right hpb, sub_self, mul_zero]
  have hn : IsUnit ((n : ℕ) : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  let : IsSepClosed Ω := IsSepClosed.of_isAlgClosed Ω
  refine ⟨hu0, ?_⟩
  exact Place.exists_ordZero_rationalRootSpecialization_scaling_equivariant
    V hV u.val hu0 (n : ℕ) hn κ Ω rawQa

end AnabelianGeometry.WeightFiltration
