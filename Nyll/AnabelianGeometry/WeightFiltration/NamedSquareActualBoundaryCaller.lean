/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareCoherentBaseChangeCaller
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverBoundaryRestriction

/-! # The same named base-change model has the actual pullback boundary

The retained original model-open isomorphism supplies its actual base change.
The two projective coefficient projections identify its chart with the SAME
Jκ retained by the coherent caller. Boundary pullback and its cardinal bound
are conclusions, not assumptions. The coefficient field here is algebraically
closed κ, as required by the finite-boundary restriction owner.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups CategoryTheory.PreGaloisCategory
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth
namespace AnabelianGeometry.WeightFiltration

local instance actualBoundaryOverCategory (S : Scheme) :
    Category (MorphismProperty.Over (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance actualBoundaryHasPullbacksAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance actualBoundaryStableUnderBaseChangeAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

private theorem actualBoundary_range_comp_of_surjective
    {A B C : Type*} (f : A → B) (g : B → C) (hf : Function.Surjective f) :
    Set.range (g ∘ f) = Set.range g := by
  apply Set.ext
  intro z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨f a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, rfl⟩

/-- Actual omitted-boundary equality and cardinal monotonicity for the named
configuration. All isomorphisms and chart equations are the retained named
construction and the coherent caller's unique Jκ. -/
theorem namedSquareModel_actualBaseChange_boundary_card
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [Infinite E]
    [CharZero κ] [IsAlgClosed κ]
    {X : Scheme} (j : X ⟶ (projectiveLineRatFuncModel E).C) [IsOpenImmersion j]
    (W : FiniteEtale X)
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    [IsFinite p] (hp : p ≫ π E 1 = π E 1)
    (e : W.left ≅ pullback p j) (he : e.hom ≫ pullback.snd p j = W.hom)
    (t : Finset (Projectivization E (E × E)))
    (J : W.left ≅ (rationalConfigurationOpen t : Scheme))
    (hambient : J.hom ≫ (rationalConfigurationOpen t).ι = e.hom ≫ pullback.fst p j)
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsNormalIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsConnected ((FiniteEtale.pullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))).obj W)] :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let f := j ≫ π E 1
    let g := (rationalConfigurationOpen t).ι ≫ π E 1
    let b := pullback.snd φ f
    let Uκ := pullback φ f
    let Wκ := (FiniteEtale.pullback b).obj W
    let jκ : Uκ ⟶ (projectiveLineRatFuncModel κ).C :=
      (isPullback_map E κ 1).flip.lift (pullback.fst φ f)
        (b ≫ j) (by
          exact (pullback.condition (f := φ) (g := f)).trans
            (Category.assoc b j
              (show (projectiveLineRatFuncModel E).C ⟶ Spec (.of E) from π E 1)).symm)
    let pκ : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C :=
      baseChangedModelMap (isPullback_map E κ 1) p hp
    ∀ (Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t),
      Jκ.hom ≫ pullback.snd φ g = pullback.fst W.hom b ≫ J.hom →
      Jκ.hom ≫ pullback.fst φ g = Wκ.hom ≫ pullback.fst φ f →
      (∀ y : (projectiveLineRatFuncModel κ).C,
        y ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
          pκ y ∉ Set.range jκ) ∧
      Nat.card ((projectiveLineRatFuncModel κ).openBoundaryPlaces jκ) ≤ t.card := by
  intro φ f g b Uκ Wκ jκ pκ Jκ hcoeff hbase
  let M : CurveModel κ (RatFunc κ) := projectiveLineRatFuncModel κ
  let lκ : rationalConfigurationGeometricScheme E κ t ⟶ M.C :=
    rationalConfigurationBaseChangeChart E κ t
  have hlκopen : IsOpenImmersion lκ :=
    rationalConfigurationBaseChangeChart_isOpenImmersion E κ t
  let c : M.C ⟶ (projectiveLineRatFuncModel E).C := map E κ 1
  let d : M.C ⟶ Spec (.of κ) := π κ 1
  let l : (rationalConfigurationOpen t : Scheme) ⟶ (projectiveLineRatFuncModel E).C :=
    (rationalConfigurationOpen t).ι
  have hjκcoeff : jκ ≫ c = b ≫ j :=
    (isPullback_map E κ 1).flip.lift_snd _ _ _
  have hjκbase : jκ ≫ d = pullback.fst φ f :=
    (isPullback_map E κ 1).flip.lift_fst _ _ _
  have hjκPB : IsPullback jκ b c j :=
    (IsPullback.of_hasPullback φ f).of_right' (isPullback_map E κ 1).flip
  have hjκopen : IsOpenImmersion jκ := by
    have hi : IsOpenImmersion
        (hjκPB.isoPullback.hom ≫ pullback.fst c j) := inferInstance
    rw [hjκPB.isoPullback_hom_fst] at hi
    exact hi
  let := hjκopen
  let : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
  let : IsFinite pκ := MorphismProperty.of_isPullback (P := @IsFinite)
    (baseChangedModelMap_isPullback (isPullback_map E κ 1) p hp) ‹IsFinite p›
  obtain ⟨eκ, heκproj, heκcoeff⟩ :=
    projectivePairSquare_baseChange_original_cover_iso E κ p hp j W.hom e he
      b jκ hjκcoeff.symm
  let rκ : pullback pκ jκ ⟶ M.C := pullback.fst pκ jκ
  let sκ : pullback pκ jκ ⟶ Uκ := pullback.snd pκ jκ
  have hpκbase : pκ ≫ d = d := baseChangedModelMap_base (isPullback_map E κ 1) p hp
  have hlcoeff : lκ ≫ c = pullback.snd φ g ≫ l :=
    rationalConfigurationBaseChangeChart_comp_map E κ t
  have hlbase : lκ ≫ d = pullback.fst φ g :=
    rationalConfigurationBaseChangeChart_comp_π E κ t
  have hpb : rκ ≫ pκ = sκ ≫ jκ := pullback.condition
  have hchartBase : rκ ≫ d = sκ ≫ jκ ≫ d :=
    (congrArg (fun z : M.C ⟶ Spec (.of κ) => rκ ≫ z) hpκbase.symm).trans
      ((Category.assoc rκ pκ d).symm.trans
      ((congrArg (fun z : pullback pκ jκ ⟶ M.C => z ≫ d) hpb).trans
        (Category.assoc sκ jκ d)))
  have hambientκ : Jκ.hom ≫ lκ = eκ.hom ≫ rκ := by
    apply (isPullback_map E κ 1).hom_ext
    · change (Jκ.hom ≫ lκ) ≫ c = (eκ.hom ≫ rκ) ≫ c
      exact (Category.assoc Jκ.hom lκ c).trans
        ((congrArg (fun z : rationalConfigurationGeometricScheme E κ t ⟶
            (projectiveLineRatFuncModel E).C => Jκ.hom ≫ z) hlcoeff).trans
        ((Category.assoc Jκ.hom (pullback.snd φ g) l).symm.trans
        ((congrArg (fun z : Wκ.left ⟶ (rationalConfigurationOpen t : Scheme) => z ≫ l)
          hcoeff).trans
        ((Category.assoc (pullback.fst W.hom b) J.hom l).trans
        ((congrArg (fun z : W.left ⟶ (projectiveLineRatFuncModel E).C =>
          pullback.fst W.hom b ≫ z) hambient).trans
        (heκcoeff.symm.trans (Category.assoc eκ.hom rκ c).symm))))))
    · change (Jκ.hom ≫ lκ) ≫ d = (eκ.hom ≫ rκ) ≫ d
      exact (Category.assoc Jκ.hom lκ d).trans
        ((congrArg (fun z : rationalConfigurationGeometricScheme E κ t ⟶
          Spec (.of κ) => Jκ.hom ≫ z) hlbase).trans
        (hbase.trans
        ((congrArg (fun z : Wκ.left ⟶ Uκ => z ≫ pullback.fst φ f) heκproj.symm).trans
        ((Category.assoc eκ.hom sκ (pullback.fst φ f)).trans
        ((congrArg (fun z : Uκ ⟶ Spec (.of κ) => eκ.hom ≫ sκ ≫ z) hjκbase.symm).trans
        ((congrArg (fun z : pullback pκ jκ ⟶ Spec (.of κ) => eκ.hom ≫ z)
          hchartBase.symm).trans (Category.assoc eκ.hom rκ d).symm))))))
  have hrJ : Set.range (Jκ.hom ≫ lκ) = Set.range lκ := by
    change Set.range (lκ ∘ Jκ.hom) = Set.range lκ
    exact actualBoundary_range_comp_of_surjective Jκ.hom lκ
      (show Function.Surjective Jκ.hom from Jκ.hom.homeomorph.surjective)
  have hre : Set.range (eκ.hom ≫ pullback.fst pκ jκ) = Set.range (pullback.fst pκ jκ) := by
    change Set.range ((pullback.fst pκ jκ) ∘ eκ.hom) = Set.range (pullback.fst pκ jκ)
    exact actualBoundary_range_comp_of_surjective eκ.hom (pullback.fst pκ jκ)
      (show Function.Surjective eκ.hom from eκ.hom.homeomorph.surjective)
  have hrange : Set.range lκ = Set.range (pullback.fst pκ jκ) :=
    hrJ.symm.trans ((congrArg (fun h : Wκ.left ⟶ M.C => Set.range h) hambientκ).trans hre)
  have hboundary : ∀ y : M.C, y ∉ Set.range lκ ↔ pκ y ∉ Set.range jκ := by
    intro y
    rw [hrange, IsOpenImmersion.range_pullbackFst jκ pκ]
    change pκ y ∉ Set.range jκ ↔ pκ y ∉ Set.range jκ
    exact Iff.rfl
  refine ⟨hboundary, ?_⟩
  let qκ : rationalConfigurationGeometricScheme E κ t ⟶ Uκ := Jκ.inv ≫ Wκ.hom
  have hJκq : Jκ.hom ≫ qκ = Wκ.hom := Jκ.hom_inv_id_assoc Wκ.hom
  have hsquare : lκ ≫ pκ = qκ ≫ jκ := by
    apply (cancel_epi Jκ.hom).mp
    exact (Category.assoc Jκ.hom lκ pκ).symm.trans
      ((congrArg (fun z : Wκ.left ⟶ M.C => z ≫ pκ) hambientκ).trans
      ((Category.assoc eκ.hom rκ pκ).trans
      ((congrArg (fun z : pullback pκ jκ ⟶ M.C => eκ.hom ≫ z) hpb).trans
      ((Category.assoc eκ.hom sκ jκ).symm.trans
      ((congrArg (fun z : Wκ.left ⟶ Uκ => z ≫ jκ) heκproj).trans
      ((congrArg (fun z : Wκ.left ⟶ Uκ => z ≫ jκ) hJκq.symm).trans
        (Category.assoc Jκ.hom qκ jκ)))))))
  have hWsurj : Function.Surjective Wκ.hom := by
    intro x
    have hx := (finiteEtale_hom_denseRange_of_isConnected Wκ) x
    rw [Wκ.hom.isClosedMap.isClosed_range.closure_eq] at hx
    exact hx
  have hqsurj : Function.Surjective qκ := by
    intro x
    obtain ⟨y, hy⟩ := hWsurj x
    refine ⟨Jκ.hom y, ?_⟩
    change (Jκ.hom ≫ qκ) y = x
    exact (congrArg (fun z : Wκ.left ⟶ Uκ => z y) hJκq).trans hy
  have hpsurj : Function.Surjective pκ :=
    surjective_finite_extension_of_open_square jκ qκ hqsurj lκ pκ hsquare
  have hpbase : pκ ≫ M.toBase = M.toBase :=
    baseChangedModelMap_base (isPullback_map E κ 1) p hp
  let : Fintype (M.openBoundaryPlaces jκ) := (M.openBoundaryPlaces_finite jκ).fintype
  let : Fintype (M.openBoundaryPlaces lκ) := (M.openBoundaryPlaces_finite lκ).fintype
  have hc := finiteSquareBoundary_card_le M M pκ hpbase hpsurj jκ lκ hboundary
  have hcNat : Nat.card (M.openBoundaryPlaces jκ) ≤ Nat.card (M.openBoundaryPlaces lκ) := by
    simpa only [Nat.card_eq_fintype_card] using hc
  have htcard : Nat.card (M.openBoundaryPlaces lκ) = t.card :=
    rationalConfigurationBoundaryPlaces_card E κ t
  exact hcNat.trans_eq htcard

end AnabelianGeometry.WeightFiltration
