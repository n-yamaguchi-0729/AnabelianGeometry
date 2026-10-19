/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.ProjectivePairSquareBaseChangeModel
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral

/-! # Named Square Model Base Change Connected -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  projectiveSpace_isIntegral
namespace AnabelianGeometry.WeightFiltration

local instance connectedModelOverCategory (S : Scheme) :
    Category (MorphismProperty.Over (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance connectedModelHasPullbacksAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance connectedModelStableUnderBaseChangeAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

theorem namedSquareModel_actualBaseChange_isConnected
    (E κ : Type) [Field E] [Field κ] [Algebra E κ]
    {X : Scheme} (j : X ⟶ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E))) [IsOpenImmersion j]
    (W : FiniteEtale X)
    (p : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E))
    (hp : p ≫ π E 1 = π E 1)
    (e : W.left ≅ pullback p j) (he : e.hom ≫ pullback.snd p j = W.hom)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (j ≫ π E 1))
    (w : (fiber xi).obj ((FiniteEtale.pullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        (j ≫ π E 1))).obj W)) :
    CategoryTheory.PreGaloisCategory.IsConnected ((FiniteEtale.pullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        (j ≫ π E 1))).obj W) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
  let f := j ≫ π E 1
  let b := pullback.snd φ f
  let Uκ := pullback φ f
  let Wκ := (FiniteEtale.pullback b).obj W
  let jκ : Uκ ⟶ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)) :=
    (isPullback_map E κ 1).flip.lift (pullback.fst φ f) (b ≫ j)
      (by
        exact (pullback.condition (f := φ) (g := f)).trans
          (Category.assoc b j (π E 1)).symm)
  let pκ := baseChangedModelMap (isPullback_map E κ 1) p hp
  have hjcoeff : jκ ≫ map E κ 1 = b ≫ j :=
    (isPullback_map E κ 1).flip.lift_snd _ _ _
  have hjPB : IsPullback jκ b (map E κ 1) j :=
    (IsPullback.of_hasPullback φ f).of_right' (isPullback_map E κ 1).flip
  have hjκ : IsOpenImmersion jκ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hjPB.flip inferInstance
  have : Nonempty Uκ := ⟨xi (IsLocalRing.closedPoint Ω)⟩
  have : IsIntegral Uκ := isIntegral_of_isOpenImmersion jκ
  obtain ⟨eκ, _hproj, _hcoeff⟩ := projectivePairSquare_baseChange_original_cover_iso
    E κ p hp j W.hom e he b jκ hjcoeff.symm
  have : Nonempty Wκ.left :=
    ⟨actualFiberPointLift xi Wκ w (IsLocalRing.closedPoint Ω)⟩
  have : IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)) :=
    projectiveSpace_isIntegral κ 1
  have hopen : IsOpenImmersion (pullback.fst pκ jκ) :=
    MorphismProperty.pullback_fst pκ jκ hjκ
  have hcomp : IsOpenImmersion (eκ.hom ≫ pullback.fst pκ jκ) :=
    @IsOpenImmersion.comp _ _ _ eκ.hom (pullback.fst pκ jκ) inferInstance hopen
  have : IsIntegral Wκ.left :=
    @isIntegral_of_isOpenImmersion Wκ.left _
      (eκ.hom ≫ pullback.fst pκ jκ) hcomp (projectiveSpace_isIntegral κ 1) inferInstance
  exact isConnected_of_connectedSpace_left Wκ

end AnabelianGeometry.WeightFiltration
