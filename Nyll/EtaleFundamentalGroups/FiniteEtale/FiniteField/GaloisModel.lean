/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteTowerModel
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GaloisStage
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GlobalModel
public import Nyll.EtaleFundamentalGroups.GaloisCovers.IsomorphismTransport
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# A finite coefficient model of a geometric Galois cover

A finite étale Galois cover after an algebraic coefficient extension of a
qcqs scheme descends to a finite intermediate field as a Galois cover
with exactly the same automorphism-group order.

First, finite coefficient descent supplies an actual model of the cover.
After rebasing through that field, all deck transformations descend to a
further finite stage by `exists_finiteIntermediateField_galois_stage`.
The two coefficient extensions are then flattened into one intermediate
field of the original extension. The actual tower recovery isomorphisms
preserve both the cover and the cardinality of its automorphism group.

No Galois closure is taken, so prime-to-characteristic orders remain
prime to the characteristic at this finite model.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

open EtaleFundamentalGroups

universe u

/-- Every finite étale Galois cover after an algebraic coefficient
extension has an actual finite coefficient Galois model with the same
automorphism-group order and recovery along the coefficient inclusion. -/
theorem exists_finiteIntermediateField_galois_scheme_model
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k)) :
    let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let XL : Scheme.{u} := Limits.pullback φL f
    ∀ [ConnectedSpace XL] (Z : FiniteEtale XL) [IsGalois Z],
    ∃ H : IntermediateField k L, FiniteDimensional k H ∧
      let φH := Spec.map (CommRingCat.ofHom (algebraMap k H))
      let XH : Scheme.{u} := Limits.pullback φH f
      ∃ hXH : ConnectedSpace XH,
        let : ConnectedSpace XH := hXH
        ∃ N : FiniteEtale XH, IsGalois N ∧ Nat.card (Aut N) = Nat.card (Aut Z) ∧
          Nonempty ((pullback
            (Limits.pullback.map φL f φH f
              (Spec.map (CommRingCat.ofHom H.val.toRingHom)) (𝟙 X) (𝟙 _)
              (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
              (by rw [Category.comp_id, Category.id_comp]))).obj N ≅ Z) := by
  intro φL XL hXL Z hZ
  obtain ⟨F, hF, M, ⟨eM⟩⟩ := exists_finiteIntermediateField_scheme_model k L X f Z
  have : FiniteDimensional k F := hF
  let φF := Spec.map (CommRingCat.ofHom (algebraMap k F))
  let ψF := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let XF : Scheme.{u} := Limits.pullback φF f
  let fF : XF ⟶ Spec (.of F) := Limits.pullback.fst φF f
  let cF : XL ⟶ XF := Limits.pullback.map φL f φF f ψF (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  have : IsAffineHom (Limits.pullback.snd φF f) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback φF f) (inferInstance : IsAffineHom φF)
  have : CompactSpace XF := inferInstanceAs (CompactSpace ↥(Limits.pullback φF f))
  have : QuasiSeparatedSpace XF :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd φF f)
  let U : Scheme.{u} := Limits.pullback ψF fF
  let q : U ⟶ XF := Limits.pullback.snd ψF fF
  let eX : U ≅ XL := constantFieldTowerIso k L F X f
  have hU : ConnectedSpace U := eX.hom.homeomorph.connectedSpace_iff.mpr hXL
  let ZF : FiniteEtale U := (pullback eX.hom).obj Z
  have hZF : IsGalois ZF ∧ Nat.card (Aut ZF) = Nat.card (Aut Z) :=
    isGalois_pullback_and_card_aut_of_isIso eX.hom Z
  have : IsGalois ZF := hZF.1
  let P : FiniteEtale U := (pullback q).obj M
  have hq : eX.hom ≫ cF = q := constantFieldTowerIso_hom_coefficientMap k L F X f
  let eP : P ≅ ZF :=
    (finiteEtalePullbackCompObjIso eX.hom cF q hq M).symm ≪≫
      (pullback eX.hom).mapIso eM
  have : IsGalois P := isGalois_of_iso eP.symm
  obtain ⟨s, hs, hXE, N, hN, hNCard, ⟨eN⟩⟩ :=
    exists_finiteIntermediateField_galois_stage F L XF fF M
  let E := IntermediateField.adjoin F (s : Set L)
  have : FiniteDimensional F E := hs
  let H : IntermediateField k L := E.restrictScalars k
  have hH : FiniteDimensional k H := FiniteDimensional.trans k F E
  let η := Spec.map (CommRingCat.ofHom (algebraMap F E))
  let XE : Scheme.{u} := Limits.pullback η fF
  let φH := Spec.map (CommRingCat.ofHom (algebraMap k H))
  let XH : Scheme.{u} := Limits.pullback φH f
  have : ConnectedSpace XE := hXE
  have : IsGalois N := hN
  let eH : XE ≅ XH := finiteIntermediateTowerIso k L F E X f
  have hXH : ConnectedSpace XH := eH.hom.homeomorph.connectedSpace_iff.mp hXE
  let NH : FiniteEtale XH := (pullback eH.inv).obj N
  have hNH : IsGalois NH ∧ Nat.card (Aut NH) = Nat.card (Aut N) :=
    isGalois_pullback_and_card_aut_of_isIso eH.inv N
  have hPCard : Nat.card (Aut P) = Nat.card (Aut ZF) :=
    Nat.card_congr (Aut.autMulEquivOfIso eP).toEquiv
  have hCard : Nat.card (Aut NH) = Nat.card (Aut Z) :=
    hNH.2.trans (hNCard.trans (hPCard.trans hZF.2))
  have hRecovery : Nonempty ((pullback
      (finiteIntermediateTowerProjection k L F E X f)).obj N ≅ ZF) := by
    rw [finiteIntermediateTowerProjection_eq_cone]
    exact ⟨eN ≪≫ eP⟩
  exact ⟨H, hH, hXH, NH, hNH.1, hCard,
    ⟨finiteIntermediateTowerModelRecoveryIso k L F E X f N Z hRecovery.some⟩⟩

end AlgebraicGeometry.FiniteEtale
