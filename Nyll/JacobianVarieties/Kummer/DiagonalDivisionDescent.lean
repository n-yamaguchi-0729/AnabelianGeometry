/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroGroupCut
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalPoincareFamily
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleRootCechDescent
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionIntegralRoot
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRoot
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Root-sensitive descent of the original normalized diagonal class

The actual Picard division construction supplies an integral finite
étale root cover. The native class of this same root supplies the
actual short-extension diagram, and hence a class on the original
covering kernel. Its coefficient inclusion retains that root class;
its transgression is the negative original signed diagonal cycle.

Thus the sign and the original Kummer coefficients are fixed before
any identification with a middle external-cup tensor.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry AlgebraicGeometry.RelPicard CategoryTheory Abelian Limits MonoidalCategory
open NeronModelInfra GoodReductionJacobian

namespace EtaleCohomology

section ProductCover

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (B : FiniteEtale X)

/-- The actual product cover C × B → C × C, with the first factor
unchanged and the second map equal to the specified parameter cover. -/
def diagonalParameterProductCover : FiniteEtale (pullback f f) := by
  let b : SchemeHomOver (B.hom ≫ f) f := ⟨B.hom, rfl⟩
  have : IsFinite (baseChangeSnd f b) := MorphismProperty.of_isPullback
    (P := @IsFinite) (isPullback_baseChangeSnd f b).flip B.prop.toIsFinite
  have : Etale (baseChangeSnd f b) := MorphismProperty.of_isPullback
    (P := @Etale) (isPullback_baseChangeSnd f b).flip B.prop.toEtale
  have : IsFiniteEtale (baseChangeSnd f b) := IsFiniteEtale.mk
  exact FiniteEtale.mk (baseChangeSnd f b)

/-- A surjective parameter cover gives the original surjective
product cover by its actual Cartesian square. -/
theorem diagonalParameterProductCover_surjective [Surjective B.hom] :
    Surjective (diagonalParameterProductCover f B).hom :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (isPullback_baseChangeSnd f (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ f) f)).flip
      (inferInstance : Surjective B.hom)

/-- The actual factorized division cover is the actual étale
base change of its retained parameter cover along the second
projection. This comparison keeps both original cover maps. -/
def diagonalParameterProductCoverBaseChangeIso :
    (finiteEtaleInclusion (pullback f f)).obj (diagonalParameterProductCover f B) ≅
      (etaleBaseChange (pullback.snd f f)).obj ((finiteEtaleInclusion X).obj B) :=
  MorphismProperty.Over.isoMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (isPullback_baseChangeSnd f
      (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ f) f)).flip.isoPullback
    (isPullback_baseChangeSnd f
      (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ f) f)).flip.isoPullback_hom_snd

/-- The comparison preserves the original map to the parameter
component, before passing to covering kernels or cohomology. -/
theorem diagonalParameterProductCoverBaseChangeIso_parameter :
    (diagonalParameterProductCoverBaseChangeIso f B).hom.left ≫
        pullback.fst B.hom (pullback.snd f f) =
      pullback.snd f (B.hom ≫ f) :=
  (isPullback_baseChangeSnd f
    (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ f) f)).flip.isoPullback_hom_fst

end ProductCover

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyIntegral f] (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

/-- The signed diagonal descends through the original Picard division
root on an actual integral parameter component. The same Picard
representation, classifying map and component map are retained in
the coefficient identity, so its overlaps can be compared with the
original division transition families. -/
theorem diagonalSignedCycleClass_exists_picard_division_descent
    (n : ℕ) (hnpos : 0 < n) (hn : IsUnit (n : K)) :
    let _ : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
    let _ : IsIntegral (pullback f f) := isIntegral_pullback_of_smooth_of_isAlgClosed f f
    let Y := pullback f f
    let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
    let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y
    let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
    let E := diagonalEdgeEffectiveCartierDivisor f p hp
    let hnY := etaleKummerExponentUnit_of_base (pullback.snd f f ≫ f) hn
    ∃ (P : RelativePic0Designation K f)
      (h : RelPicard.RepresentsRelSubPic f ⟨p, hp⟩
        (RelPicard.algEquivZeroGroupCut f ⟨p, hp⟩).toSubPicCondition P)
      (_ : Smooth P.toBase) (_ : IsProper P.toBase) (_ : GeometricallyConnected P.toBase),
      let aj := diagonalPicardClassifyingMap f p hp P h
      ∃ (B : Scheme.{u}) (i : B ⟶ h.divisionPullback aj n)
        (hB : IsIntegral B) (_ : IsFiniteEtale i),
        let : IsIntegral B := hB
        let q := i ≫ h.divisionProjection aj n
        ∃ (_ : IsFinite q) (_ : Etale q) (hqsurj : Surjective q),
          let : Surjective q := hqsurj
          let _ : IsFiniteEtale q := IsFiniteEtale.mk
          let B' : FiniteEtale X := FiniteEtale.mk q
          let : Surjective B'.hom := hqsurj
          let : IsIntegral B'.left := hB
          let cB : B'.left ⟶ Spec (.of K) := B'.hom ≫ f
          let U := diagonalParameterProductCover f B'
          let hU : IsIntegral U.left := isIntegral_pullback_of_smooth_of_isAlgClosed f cB
          let _ : Surjective U.hom := diagonalParameterProductCover_surjective f B'
          let z : SchemeHomOver (q ≫ f) (h.divisionStructure aj n) :=
            ⟨i, (Category.assoc i (h.divisionProjection aj n) f).symm⟩
          let L := (Scheme.Modules.pullback (baseChangeSnd f z)).obj (h.divisionRootFamily aj n).L
          let hL := (h.divisionRootFamily aj n).isInvertible.pullback (baseChangeSnd f z)
          ∃ _ : (Scheme.Modules.pullback U.hom).obj (D.1.invModule ⊗ E.1.module) ≅ L.tensorPow n,
            let V := (finiteEtaleInclusion Y).obj U
            let : IsIntegral V.left := hU
            let q₀ := finiteEtaleCoverBaseMap Y U
            let hq := finiteEtaleCoverBaseMap_covering Y U
            let A := abelianCechAugmentationSequence Y.smallEtaleTopology hT q₀
            let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT q₀ hq
            ∃ a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y n) 1,
              a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) =
                (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 V hL) (zero_add 1) ∧
              hA.extClass.comp a (show 1 + 1 = 2 from rfl) +
                (effectiveCartierCycleClass D hnpos hnY -
                  effectiveCartierCycleClass E hnpos hnY) = 0 := by
  intro hX hY Y T hT D E hnY
  obtain ⟨P, h, hs, hproper, hc, B, i, hB, hi, hfinite, hetale, hsurj, ⟨e⟩⟩ :=
    diagonalMiddleBundle_exists_integral_picard_division_root f p hp n hn
  refine ⟨P, h, hs, hproper, hc, ?_⟩
  intro aj
  refine ⟨B, i, hB, hi, ?_⟩
  intro hBintegral q
  refine ⟨hfinite, hetale, hsurj, ?_⟩
  intro hqsurj hqfinite B' hBsurj hB'integral cB U hU hsurjU z L hL
  refine ⟨e, ?_⟩
  intro V hV q₀ hq A hA
  exact signedCartierRoot_exists_cech_descent V hL hT q₀ n D E e hq hnpos hnY

/-- Root-sensitive descent on the actual product with an integral
finite étale parameter curve. The original root, parameter cover,
coefficient image and signed transgression are retained together. -/
theorem diagonalSignedCycleClass_exists_parameter_root_descent
    (n : ℕ) (hnpos : 0 < n) (hn : IsUnit (n : K)) :
    let _ : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
    let _ : IsIntegral (pullback f f) := isIntegral_pullback_of_smooth_of_isAlgClosed f f
    let Y := pullback f f
    let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
    let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y
    let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
    let E := diagonalEdgeEffectiveCartierDivisor f p hp
    let hnY := etaleKummerExponentUnit_of_base (pullback.snd f f ≫ f) hn
    ∃ (B : FiniteEtale X) (hB : IsIntegral B.left) (hBsurj : Surjective B.hom),
      let : IsIntegral B.left := hB
      let : Surjective B.hom := hBsurj
      let cB : B.left ⟶ Spec (.of K) := B.hom ≫ f
      let U := diagonalParameterProductCover f B
      let hU : IsIntegral U.left := isIntegral_pullback_of_smooth_of_isAlgClosed f cB
      let _ : Surjective U.hom := diagonalParameterProductCover_surjective f B
      ∃ (L : U.left.Modules) (hL : Scheme.Modules.IsInvertible L)
        (_ : (Scheme.Modules.pullback U.hom).obj (D.1.invModule ⊗ E.1.module) ≅
          L.tensorPow n),
      let V := (finiteEtaleInclusion Y).obj U
      let : IsIntegral V.left := hU
      let q := finiteEtaleCoverBaseMap Y U
      let hq := finiteEtaleCoverBaseMap_covering Y U
      let A := abelianCechAugmentationSequence Y.smallEtaleTopology hT q
      let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT q hq
      ∃ a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y n) 1,
        a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) =
          (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 V hL) (zero_add 1) ∧
        hA.extClass.comp a (show 1 + 1 = 2 from rfl) +
          (effectiveCartierCycleClass D hnpos hnY -
            effectiveCartierCycleClass E hnpos hnY) = 0 := by
  intro hX hY Y T hT D E hnY
  obtain ⟨P, h, _, _, _, B, i, hB, _, hfinite, hetale, hsurj, e, a, hcoeff, htrans⟩ :=
    diagonalSignedCycleClass_exists_picard_division_descent f p hp n hnpos hn
  let aj := diagonalPicardClassifyingMap f p hp P h
  let q := i ≫ h.divisionProjection aj n
  have : IsIntegral B := hB
  have : IsFinite q := hfinite
  have : Etale q := hetale
  have : IsFiniteEtale q := IsFiniteEtale.mk
  let B' : FiniteEtale X := FiniteEtale.mk q
  let z : SchemeHomOver (q ≫ f) (h.divisionStructure aj n) :=
    ⟨i, (Category.assoc i (h.divisionProjection aj n) f).symm⟩
  let L := (Scheme.Modules.pullback (baseChangeSnd f z)).obj (h.divisionRootFamily aj n).L
  let hL := (h.divisionRootFamily aj n).isInvertible.pullback (baseChangeSnd f z)
  refine ⟨B', hB, hsurj, ?_⟩
  intro hBintegral hBsurjective cB U hU hsurjU
  refine ⟨L, hL, e, ?_⟩
  intro V hV q₀ hq A hA
  exact ⟨a, hcoeff, htrans⟩

/-- The original signed diagonal class is the negative transgression
of a class constructed from its actual division root. The coefficient
image is the restriction of that same root's native H¹(Gm) class. -/
theorem diagonalSignedCycleClass_exists_root_descent
    (n : ℕ) (hnpos : 0 < n) (hn : IsUnit (n : K)) :
    let _ : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
    let _ : IsIntegral (pullback f f) := isIntegral_pullback_of_smooth_of_isAlgClosed f f
    let Y := pullback f f
    let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
    let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y
    let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
    let E := diagonalEdgeEffectiveCartierDivisor f p hp
    let hnY := etaleKummerExponentUnit_of_base (pullback.snd f f ≫ f) hn
    ∃ (U : FiniteEtale Y) (hU : IsIntegral U.left) (_ : Surjective U.hom)
      (L : U.left.Modules) (hL : Scheme.Modules.IsInvertible L)
      (_ : (Scheme.Modules.pullback U.hom).obj (D.1.invModule ⊗ E.1.module) ≅
        L.tensorPow n),
      let V := (finiteEtaleInclusion Y).obj U
      let : IsIntegral V.left := hU
      let q := finiteEtaleCoverBaseMap Y U
      let hq := finiteEtaleCoverBaseMap_covering Y U
      let A := abelianCechAugmentationSequence Y.smallEtaleTopology hT q
      let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT q hq
      ∃ a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y n) 1,
        a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) =
          (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 V hL) (zero_add 1) ∧
        hA.extClass.comp a (show 1 + 1 = 2 from rfl) +
          (effectiveCartierCycleClass D hnpos hnY -
            effectiveCartierCycleClass E hnpos hnY) = 0 := by
  intro hX hY Y T hT D E hnY
  obtain ⟨B, hB, hsurj, L, hL, e, a, hcoeff, htrans⟩ :=
    diagonalSignedCycleClass_exists_parameter_root_descent f p hp n hnpos hn
  have : IsIntegral B.left := hB
  have : Surjective B.hom := hsurj
  let cB : B.left ⟶ Spec (.of K) := B.hom ≫ f
  have hU : IsIntegral (diagonalParameterProductCover f B).left :=
    isIntegral_pullback_of_smooth_of_isAlgClosed f cB
  refine ⟨diagonalParameterProductCover f B, hU,
    diagonalParameterProductCover_surjective f B, L, hL, e, ?_⟩
  intro V hV q₀ hq A hA
  exact ⟨a, hcoeff, htrans⟩

end EtaleCohomology
