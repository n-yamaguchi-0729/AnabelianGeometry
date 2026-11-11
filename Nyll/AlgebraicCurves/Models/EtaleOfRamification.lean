/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Ramification.Ramification
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictEqMem
public import Nyll.AlgebraicCurves.Geometry.IsClosedSingletonNeGenericPoint
public import Nyll.AlgebraicCurves.Geometry.Schemes.Points.FiniteExtensionPoint
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Finite curve maps with ramification index one

The original generic-point square identifies each actual stalk map with
the inclusion of the corresponding valuation rings. Ramification index one
then identifies their maximal ideals. Over a finite ground field the actual
closed-point residue fields are finite, so the residue extensions are
separable. The local unramified criterion, together with the given finite
flat curve map, gives étaleness in every characteristic.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicCurves.Models.Proofs.Ramification

namespace AlgebraicCurve.Place

/-- A ramification-index-one inclusion of the actual local valuation rings
maps the original maximal ideal onto the original maximal ideal. -/
theorem map_maximalIdeal_eq_of_ramificationIndex_eq_one_of_local_map
    {k F L : Type*} [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
    [Algebra.IsIntegral F L] (v : Place k F) (w : Place k L)
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B]
    (eA : A ≃+* v.toValuationSubring) (eB : B ≃+* w.toValuationSubring)
    (hcompat : ∀ a : A, ((eB (algebraMap A B a) : w.toValuationSubring) : L) =
      algebraMap F L ((eA a : v.toValuationSubring) : F))
    (he : w.ramificationIndex F = 1) :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  have hrestrict : w.restrict F = v := by
    apply v.restrict_eq_of_forall_mem w
    intro a ha
    let b : A := eA.symm ⟨a, ha⟩
    have hb : ((eA b : v.toValuationSubring) : F) = a :=
      congrArg Subtype.val (eA.apply_symm_apply ⟨a, ha⟩)
    rw [← hb, ← hcompat b]
    exact (eB (algebraMap A B b)).property
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  let a : A := eA.symm t
  let b : w.toValuationSubring := eB (algebraMap A B a)
  have hord : w.ord (b : L) = 1 := by
    rw [hcompat a, w.ord_restrict, he, Nat.cast_one, one_mul, hrestrict]
    change v.ord ((eA (eA.symm t) : v.toValuationSubring) : F) = 1
    rw [eA.apply_symm_apply]
    exact v.ord_coe_irreducible ht
  have hb : b ≠ 0 := by
    intro hzero
    rw [hzero, ZeroMemClass.coe_zero, w.ord_zero] at hord
    exact zero_ne_one hord
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, n, hbn, hnord⟩ := HG1b.eq_unit_mul_pow_ord w hs hb
  have hn : n = 1 := by
    have h : (n : ℤ) = 1 := hnord.symm.trans hord
    exact_mod_cast h
  have hbunit : b = (u : w.toValuationSubring) * s := by
    rw [hbn, hn, pow_one]
  have hspan : Ideal.span ({b} : Set w.toValuationSubring) = Ideal.span {s} := by
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      rw [hbunit]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton s))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hmem : (u : w.toValuationSubring) * s ∈
          Ideal.span ({b} : Set w.toValuationSubring) := by
        rw [← hbunit]
        exact Ideal.subset_span (Set.mem_singleton b)
      have h := Ideal.mul_mem_left (Ideal.span ({b} : Set w.toValuationSubring))
        (↑u⁻¹ : w.toValuationSubring) hmem
      rwa [← mul_assoc, Units.inv_mul, one_mul] at h
  have hA : IsLocalRing.maximalIdeal A = Ideal.span {a} := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal eA.symm,
      ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hB : IsLocalRing.maximalIdeal B = Ideal.span {algebraMap A B a} := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal eB.symm,
      hs.maximalIdeal_eq, ← hspan, Ideal.map_span, Set.image_singleton]
    change Ideal.span {eB.symm (eB (algebraMap A B a))} = _
    rw [eB.symm_apply_apply]
  rw [hA, Ideal.map_span, Set.image_singleton, hB]

end AlgebraicCurve.Place

namespace AlgebraicCurve.CurveModel

universe u

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- A finite flat map of the original curve models is étale if the original
finite separable function-field extension has ramification index one at
every place. The finite ground field supplies residue separability. -/
theorem finiteFlat_etale_of_ramificationIndex_eq_one
    {k F L : Type u} [Field k] [Finite k] [Field F] [Field L]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (M : CurveModel k F) (N : CurveModel k L)
    (π : N.C ⟶ M.C) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hgeneric : N.C.fromSpecStalk (genericPoint N.C) ≫ π =
      Spec.map (CommRingCat.ofHom
        (N.ffEquiv.toRingHom.comp
          ((algebraMap F L).comp M.ffEquiv.symm.toRingHom))) ≫
            M.C.fromSpecStalk (genericPoint M.C))
    (hunramified : ∀ w : Place k L, w.ramificationIndex F = 1) : Etale π := by
  have hη : π (genericPoint N.C) = genericPoint M.C := by
    have h := congrArg
      (fun q : Spec (.of N.C.functionField) ⟶ M.C =>
        q (IsLocalRing.closedPoint N.C.functionField)) hgeneric
    change π (N.C.fromSpecStalk (genericPoint N.C)
        (IsLocalRing.closedPoint N.C.functionField)) =
      M.C.fromSpecStalk (genericPoint M.C)
        ((Spec.map (CommRingCat.ofHom
          (N.ffEquiv.toRingHom.comp
            ((algebraMap F L).comp M.ffEquiv.symm.toRingHom))))
          (IsLocalRing.closedPoint N.C.functionField)) at h
    rw [Scheme.fromSpecStalk_closedPoint] at h
    rw [h, Subsingleton.elim
      ((Spec.map (CommRingCat.ofHom
        (N.ffEquiv.toRingHom.comp
          ((algebraMap F L).comp M.ffEquiv.symm.toRingHom))))
        (IsLocalRing.closedPoint N.C.functionField))
      (IsLocalRing.closedPoint M.C.functionField), Scheme.fromSpecStalk_closedPoint]
  have hdense : DenseRange π := by
    rw [DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    apply (genericPoint_specializes z).mem_closed isClosed_closure
    exact subset_closure ⟨genericPoint N.C, hη⟩
  have hfield : π.functionFieldMap hdense = N.ffEquiv.toRingHom.comp
      ((algebraMap F L).comp M.ffEquiv.symm.toRingHom) := by
    have h : CommRingCat.ofHom (π.functionFieldMap hdense) =
        CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
          ((algebraMap F L).comp M.ffEquiv.symm.toRingHom)) := by
      apply Spec.map_injective
      apply (cancel_mono (M.C.fromSpecStalk (genericPoint M.C))).mp
      rw [EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk π hdense]
      exact hgeneric
    exact congrArg CommRingCat.Hom.hom h
  have hformal : FormallyUnramified π := by
    apply HasRingHomProperty.of_stalkMap (P := @FormallyUnramified)
      RingHom.FormallyUnramified.ofLocalizationPrime
    intro y
    by_cases hy : y = genericPoint N.C
    · subst y
      have hsep : Algebra.FormallyUnramified F L :=
        Algebra.FormallyUnramified.of_isSeparable F L
      have hff : (π.functionFieldMap hdense).FormallyUnramified := by
        rw [hfield]
        exact ((RingHom.FormallyUnramified.of_surjective
          M.ffEquiv.symm.surjective).comp
            (RingHom.formallyUnramified_algebraMap.mpr hsep)).comp
              (RingHom.FormallyUnramified.of_surjective N.ffEquiv.surjective)
      unfold Scheme.Hom.functionFieldMap at hff
      rw [CommRingCat.hom_comp] at hff
      exact RingHom.FormallyUnramified.of_comp hff
    · have hyclosed : IsClosed ({y} : Set N.C) :=
        isClosed_singleton_of_ne_genericPoint N.toBase y hy
      have hxclosed : IsClosed ({π y} : Set M.C) := by
        simpa only [Set.image_singleton] using π.isClosedMap {y} hyclosed
      let x : closedPoints M.C := ⟨π y, hxclosed⟩
      let y' : closedPoints N.C := ⟨y, hyclosed⟩
      let A := M.C.presheaf.stalk (π y)
      let B := N.C.presheaf.stalk y
      let eA := HG1b.stalkEquivOfRange M x.1 (M.placeOfPoint x) (M.range_stalk_eq x)
      let eB := HG1b.stalkEquivOfRange N y (N.placeOfPoint y') (N.range_stalk_eq y')
      let : Algebra A B := (π.stalkMap y).hom.toAlgebra
      have : IsLocalHom (algebraMap A B) :=
        inferInstanceAs (IsLocalHom (π.stalkMap y).hom)
      have : Algebra.EssFiniteType A B := LocallyOfFiniteType.stalkMap π y
      have hcompat : ∀ a : A,
          ((eB (algebraMap A B a) : (N.placeOfPoint y').toValuationSubring) : L) =
            algebraMap F L ((eA a : (M.placeOfPoint x).toValuationSubring) : F) := by
        intro a
        change N.ffEquiv.symm
            (algebraMap (N.C.presheaf.stalk y) N.C.functionField (π.stalkMap y a)) =
          algebraMap F L
            (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk (π y)) M.C.functionField a))
        rw [← π.functionFieldMap_algebraMap_stalk hdense y a, hfield]
        exact N.ffEquiv.symm_apply_apply _
      have hmax := Place.map_maximalIdeal_eq_of_ramificationIndex_eq_one_of_local_map
        (M.placeOfPoint x) (N.placeOfPoint y') eA eB hcompat (hunramified _)
      let : Algebra k (M.C.residueField (π y)) :=
        Scheme.pointResidueAlgebra M.toBase (π y)
      have : Module.Finite k (M.C.residueField (π y)) :=
        Scheme.pointResidueAlgebra_finite M.toBase (π y) hxclosed
      have : Finite (M.C.residueField (π y)) := Module.finite_of_finite k
      have : Finite (IsLocalRing.ResidueField A) :=
        inferInstanceAs (Finite (M.C.residueField (π y)))
      let : Algebra k (N.C.residueField y) := Scheme.pointResidueAlgebra N.toBase y
      have : Module.Finite k (N.C.residueField y) :=
        Scheme.pointResidueAlgebra_finite N.toBase y hyclosed
      have : Finite (N.C.residueField y) := Module.finite_of_finite k
      have : Finite (IsLocalRing.ResidueField B) :=
        inferInstanceAs (Finite (N.C.residueField y))
      have : Algebra.IsSeparable (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B) := inferInstance
      exact Algebra.FormallyUnramified.of_map_maximalIdeal hmax
  exact Etale.of_formallyUnramified_of_flat π

end AlgebraicCurve.CurveModel
