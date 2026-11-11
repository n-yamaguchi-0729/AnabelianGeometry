/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.EtaleCohomology.Classical.AbelianCechPullback
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.InvertibleRootCechDescent
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionDescent
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The retained division root on the actual base-changed covering

The product cover and the base change of its parameter cover are
canonically isomorphic over the original surface. Pulling the actual
division root back along this isomorphism retains its tensor-power
isomorphism. Applying root descent on this very base-changed cover
gives the original signed cycle transgression on the kernel used by
the pullback and residual-descent calculations.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Abelian
open AlgebraicGeometry.RelPicard NeronModelInfra

namespace EtaleCohomology

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (B : FiniteEtale X)

/-- A parameter-cover morphism induces the original product morphism,
with its first curve factor unchanged. -/
def diagonalParameterProductCoverMap {B₀ B₁ : FiniteEtale X} (m : B₀ ⟶ B₁) :
    (finiteEtaleInclusion (pullback f f)).obj (diagonalParameterProductCover f B₀) ⟶
      (finiteEtaleInclusion (pullback f f)).obj (diagonalParameterProductCover f B₁) := by
  let b : SchemeHomOver (B₀.hom ≫ f) (B₁.hom ≫ f) :=
    ⟨m.left, (Category.assoc m.left B₁.hom f).symm.trans
      (congrArg (fun t => t ≫ f) m.w)⟩
  refine MorphismProperty.Over.homMk (baseChangeSnd f b) ?_
  exact (baseChangeSnd_comp f
    (⟨B₁.hom, rfl⟩ : SchemeHomOver (B₁.hom ≫ f) f) b).trans
      (congrArg (baseChangeSnd f) (Subtype.ext m.w))

/-- The original product-cover comparison preserves every actual
parameter morphism, including the two maps from an overlap component. -/
theorem diagonalParameterProductCoverBaseChangeIso_naturality
    {B₀ B₁ : FiniteEtale X} (m : B₀ ⟶ B₁) :
    (diagonalParameterProductCoverBaseChangeIso f B₀).hom ≫
        (etaleBaseChange (pullback.snd f f)).map ((finiteEtaleInclusion X).map m) =
      diagonalParameterProductCoverMap f m ≫
        (diagonalParameterProductCoverBaseChangeIso f B₁).hom := by
  let e₀ : pullback f (B₀.hom ≫ f) ⟶ pullback B₀.hom (pullback.snd f f) :=
    (diagonalParameterProductCoverBaseChangeIso f B₀).hom.left
  let e₁ : pullback f (B₁.hom ≫ f) ⟶ pullback B₁.hom (pullback.snd f f) :=
    (diagonalParameterProductCoverBaseChangeIso f B₁).hom.left
  let mB : pullback B₀.hom (pullback.snd f f) ⟶
      pullback B₁.hom (pullback.snd f f) :=
    ((etaleBaseChange (pullback.snd f f)).map ((finiteEtaleInclusion X).map m)).left
  let mP : pullback f (B₀.hom ≫ f) ⟶ pullback f (B₁.hom ≫ f) :=
    (diagonalParameterProductCoverMap f m).left
  have hm : mB ≫ pullback.fst B₁.hom (pullback.snd f f) =
      pullback.fst B₀.hom (pullback.snd f f) ≫ m.left := pullback.lift_fst _ _ _
  have he₀ : e₀ ≫ pullback.fst B₀.hom (pullback.snd f f) =
      pullback.snd f (B₀.hom ≫ f) :=
    diagonalParameterProductCoverBaseChangeIso_parameter f B₀
  have he₁ : e₁ ≫ pullback.fst B₁.hom (pullback.snd f f) =
      pullback.snd f (B₁.hom ≫ f) :=
    diagonalParameterProductCoverBaseChangeIso_parameter f B₁
  have hmP : mP ≫ pullback.snd f (B₁.hom ≫ f) =
      pullback.snd f (B₀.hom ≫ f) ≫ m.left := pullback.lift_snd _ _ _
  apply MorphismProperty.Over.Hom.ext
  change e₀ ≫ mB = mP ≫ e₁
  apply pullback.hom_ext
  · calc
      (e₀ ≫ mB) ≫ pullback.fst B₁.hom (pullback.snd f f) =
          e₀ ≫ (mB ≫ pullback.fst B₁.hom (pullback.snd f f)) := Category.assoc _ _ _
      _ = e₀ ≫ (pullback.fst B₀.hom (pullback.snd f f) ≫ m.left) :=
        congrArg (fun g => e₀ ≫ g) hm
      _ = (e₀ ≫ pullback.fst B₀.hom (pullback.snd f f)) ≫ m.left :=
        (Category.assoc _ _ _).symm
      _ = pullback.snd f (B₀.hom ≫ f) ≫ m.left :=
        congrArg (fun g => g ≫ m.left) he₀
      _ = mP ≫ pullback.snd f (B₁.hom ≫ f) := hmP.symm
      _ = mP ≫ (e₁ ≫ pullback.fst B₁.hom (pullback.snd f f)) :=
        congrArg (fun g => mP ≫ g) he₁.symm
      _ = (mP ≫ e₁) ≫ pullback.fst B₁.hom (pullback.snd f f) :=
        (Category.assoc _ _ _).symm
  · exact ((diagonalParameterProductCoverBaseChangeIso f B₀).hom ≫
      (etaleBaseChange (pullback.snd f f)).map ((finiteEtaleInclusion X).map m)).w.trans
        (diagonalParameterProductCoverMap f m ≫
          (diagonalParameterProductCoverBaseChangeIso f B₁).hom).w.symm

/-- The retained tensor root on the actual product cover transports
to the actual base-changed cover, through its original scheme iso. -/
def diagonalParameterProductBaseChangeRootIso
    (n : ℕ) (M : (pullback f f).Modules)
    {L : (diagonalParameterProductCover f B).left.Modules}
    (e : (Scheme.Modules.pullback (diagonalParameterProductCover f B).hom).obj M ≅
      L.tensorPow n) :
    (Scheme.Modules.pullback
        ((etaleBaseChange (pullback.snd f f)).obj ((finiteEtaleInclusion X).obj B)).hom).obj M ≅
      ((Scheme.Modules.pullback
        (diagonalParameterProductCoverBaseChangeIso f B).inv.left).obj L).tensorPow n := by
  let U := diagonalParameterProductCover f B
  let eB := diagonalParameterProductCoverBaseChangeIso f B
  exact ((Scheme.Modules.pullbackCongr eB.inv.w).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp eB.inv.left U.hom).app M).symm ≪≫
      (Scheme.Modules.pullback eB.inv.left).mapIso e ≪≫
        Scheme.Modules.pullbackTensorPowIso eB.inv.left L n

variable [IsAlgClosed K] [IsIntegral X] [Smooth f]
  [IsIntegral (pullback f f)] [IsIntegral B.left] [Surjective B.hom]

/-- Descent of the same actual root on the canonical base change of
the parameter cover. The coefficient equation still contains that
root, and the transgression still equals the negative original signed
Cartier class. The terminal object and augmentation are precisely the
ones in the original covering-kernel pullback comparison. -/
theorem diagonalParameterProductBaseChange_root_descent
    (n : ℕ) (D E : Scheme.EffectiveCartierDivisor (pullback f f))
    {L : (diagonalParameterProductCover f B).left.Modules}
    (hL : Scheme.Modules.IsInvertible L)
    (e : (Scheme.Modules.pullback (diagonalParameterProductCover f B).hom).obj
        (D.1.invModule ⊗ E.1.module) ≅ L.tensorPow n)
    (hn : 0 < n) (hnY : IsUnit (n : Γ(pullback f f, ⊤))) :
    let Y := pullback f f
    let p₂ := pullback.snd f f
    let T : X.Etale := Scheme.Etale.mk (𝟙 X)
    let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    let V := (etaleBaseChange p₂).obj ((finiteEtaleInclusion X).obj B)
    let hTB := hT.isTerminalObj (etaleBaseChange p₂) T
    let qB := (etaleBaseChange p₂).map (finiteEtaleCoverBaseMap X B)
    let hqB := etaleBaseChange_singleton_covering p₂ (finiteEtaleCoverBaseMap X B)
      (finiteEtaleCoverBaseMap_covering X B)
    let eB := diagonalParameterProductCoverBaseChangeIso f B
    let cB : B.left ⟶ Spec (.of K) := B.hom ≫ f
    let hU : IsIntegral (diagonalParameterProductCover f B).left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed f cB
    let : IsIntegral
        ((finiteEtaleInclusion Y).obj (diagonalParameterProductCover f B)).left := hU
    let _ : IsIntegral V.left := by
      have : IsIso eB.hom.left :=
        inferInstanceAs
          (IsIso ((Scheme.Etale.forget Y ⋙ CategoryTheory.Over.forget Y).map eB.hom))
      exact IsIntegral.of_isIso eB.hom.left
    let hLB := hL.pullback eB.inv.left
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hTB qB
    let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hTB qB hqB
    ∃ a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y n) 1,
      a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) =
        (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 V hLB) (zero_add 1) ∧
      hA.extClass.comp a (show 1 + 1 = 2 from rfl) +
        (effectiveCartierCycleClass D hn hnY - effectiveCartierCycleClass E hn hnY) = 0 := by
  intro Y p₂ T hT V hTB qB hqB eB cB hU hUetale hV hLB A hA
  let eRoot := diagonalParameterProductBaseChangeRootIso f B n
    (D.1.invModule ⊗ E.1.module) e
  exact signedCartierRoot_exists_cech_descent V hLB hTB qB n D E eRoot hqB hn hnY

end EtaleCohomology
