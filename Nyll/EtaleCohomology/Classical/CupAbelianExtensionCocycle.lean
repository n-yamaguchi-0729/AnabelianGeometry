/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupCechH1
public import Nyll.EtaleCohomology.Classical.CupCechKernelComparison
public import Nyll.EtaleCohomology.Classical.CupCechResolution
public import Nyll.EtaleCohomology.Classical.CupTwoStepExtension
public import Nyll.EtaleCohomology.Classical.FreeModuleCechCoefficientComparison
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Native module cocycles of actual abelian extensions

An actual local lift into an abelian extension of the constant integer
sheaf gives an actual edge difference in its coefficient sheaf. The
free-source equivalence turns that same difference into a module
cocycle, without a module structure on the extension's middle object.
Its original classical class is the extension's original Ext class,
proved from the actual covering sequences and their kernel maps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)

variable {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
  {E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (Classical.forgetCoefficients.{u + 1, u, u, u}).obj F ⟶ E)
  (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))
  (hip : i ≫ p = 0)
  (hE : (ShortComplex.mk i p hip).ShortExact)
  (b : (freeAbelianSheafYoneda X.smallEtaleTopology).obj V ⟶ E)
  (hb : b ≫ p = abelianCechUnitAugmentation X.smallEtaleTopology hT f)

/-- The actual coefficient difference of an original abelian local
lift, expressed on the free module edge source. -/
def abelianExtensionModuleCechCocycle :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F :=
  (freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor (yoneda.map f)) F).symm
    (abelianCechFirstRelationMap X.smallEtaleTopology hT f ≫
      CupTwoStepExtension.difference
        (abelianCechAugmentationSequence X.smallEtaleTopology hT f)
        (ShortComplex.mk i p hip) hE (𝟙 ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))) b
        (hb.trans (Category.comp_id _).symm))

/-- The resulting module cocycle has exactly the original abelian
edge difference under the original coefficient inclusion. -/
theorem abelianExtensionModuleCechCocycle_difference :
    freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor (yoneda.map f)) F
        (abelianExtensionModuleCechCocycle X R hT f i p hip hE b hb) ≫ i =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat (yoneda.map f)) ≫ b := by
  let d : kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f) ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}).obj F :=
    CupTwoStepExtension.difference
      (abelianCechAugmentationSequence X.smallEtaleTopology hT f)
      (ShortComplex.mk i p hip) hE
      (𝟙 ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) b
      (hb.trans (Category.comp_id _).symm)
  have hc : freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor (yoneda.map f)) F
      (abelianExtensionModuleCechCocycle X R hT f i p hip hE b hb) =
      abelianCechFirstRelationMap X.smallEtaleTopology hT f ≫ d :=
    Equiv.apply_symm_apply _ _
  have hd : d ≫ i =
      kernel.ι (abelianCechUnitAugmentation X.smallEtaleTopology hT f) ≫ b :=
    CupTwoStepExtension.difference_comp
      (abelianCechAugmentationSequence X.smallEtaleTopology hT f)
      (ShortComplex.mk i p hip) hE
      (𝟙 ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) b
      (hb.trans (Category.comp_id _).symm)
  exact (congrArg (fun z => z ≫ i) hc).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => abelianCechFirstRelationMap X.smallEtaleTopology hT f ≫ z)
        hd).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ b)
            (abelianCechFirstRelationMap_comp X.smallEtaleTopology hT f)))))

/-- The actual difference is a module cocycle because the same
original triangle boundary kills the abelian relation map. -/
theorem abelianExtensionModuleCechCocycle_cocycle :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫
      abelianExtensionModuleCechCocycle X R hT f i p hip hE b hb = 0 := by
  apply (freeModuleSheafUnderlyingHomEquiv_cocycle_iff X (yoneda.map f) R F _).mpr
  let d : kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f) ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}).obj F :=
    CupTwoStepExtension.difference
      (abelianCechAugmentationSequence X.smallEtaleTopology hT f)
      (ShortComplex.mk i p hip) hE
      (𝟙 ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) b
      (hb.trans (Category.comp_id _).symm)
  have hc : freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor (yoneda.map f)) F
      (abelianExtensionModuleCechCocycle X R hT f i p hip hE b hb) =
      abelianCechFirstRelationMap X.smallEtaleTopology hT f ≫ d :=
    Equiv.apply_symm_apply _ _
  let t := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
    (freeCechTriangleBoundaryNat (yoneda.map f))
  exact (congrArg (fun z => t ≫ z) hc).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ d)
        (abelianCechFirstRelationMap_triangle_zero X.smallEtaleTopology hT f)).trans
          (zero_comp)))

include hb in
/-- Any actual module cocycle with the original abelian edge
differences represents the original abelian extension class. -/
theorem etaleCechH1Class_eq_abelianExtClass
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (z : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F)
    (hz : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ z = 0)
    (hzi : freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor (yoneda.map f)) F z ≫ i =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat (yoneda.map f)) ≫ b) :
    etaleCechH1Class X R hT f hf z hz = hE.extClass := by
  let A := abelianCechAugmentationSequence X.smallEtaleTopology hT f
  let k := moduleCechIntegerKernelMap X R hT f hf
  let d := moduleCechCocycleDesc X R hT f z hz
  have : Epi (abelianCechFirstRelationMap X.smallEtaleTopology hT f) :=
    abelianCechFirstRelationMap_epi X.smallEtaleTopology hT f
  have hk : (k ≫ (Classical.forgetCoefficients.{u + 1, u, u, u}).map d) ≫ i = A.f ≫ b := by
    apply (cancel_epi (abelianCechFirstRelationMap X.smallEtaleTopology hT f)).mp
    calc
      _ = ((abelianCechFirstRelationMap X.smallEtaleTopology hT f ≫ k) ≫
          (Classical.forgetCoefficients.{u + 1, u, u, u}).map d) ≫ i := by simp only
            [Category.assoc]
      _ = ((freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) ≫
          (Classical.forgetCoefficients.{u + 1, u, u, u}).map (moduleCechFirstRelationMap
            X.smallEtaleTopology R hT f)) ≫
            (Classical.forgetCoefficients.{u + 1, u, u, u}).map d) ≫ i := by rw
              [moduleCechIntegerKernelMap_relation]
      _ = (freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) ≫
          (Classical.forgetCoefficients.{u + 1, u, u, u}).map (moduleCechFirstRelationMap
            X.smallEtaleTopology R hT f ≫ d)) ≫ i := by
        simp only [Functor.map_comp, Category.assoc]
      _ = (freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) ≫
          (Classical.forgetCoefficients.{u + 1, u, u, u}).map z) ≫ i := by rw
            [moduleCechCocycleDesc_comp]
      _ = freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor (yoneda.map f)) F z ≫ i := by
        rw [freeModuleSheafUnderlyingHomEquiv_eq]
      _ = (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
          (freeCechEdgeBoundaryNat (yoneda.map f)) ≫ b := hzi
      _ = _ := by
        change _ = abelianCechFirstRelationMap X.smallEtaleTopology hT f ≫
          (kernel.ι (abelianCechUnitAugmentation X.smallEtaleTopology hT f) ≫ b)
        rw [← Category.assoc, abelianCechFirstRelationMap_comp]
  let φ : A ⟶ ShortComplex.mk i p hip :=
    { τ₁ := k ≫ (Classical.forgetCoefficients.{u + 1, u, u, u}).map d
      τ₂ := b
      τ₃ := 𝟙 ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))
      comm₁₂ := hk
      comm₂₃ := hb.trans (Category.comp_id _).symm }
  have hn : (abelianCechAugmentationSequence_shortExact
      X.smallEtaleTopology hT f hf).extClass.comp
        (Ext.mk₀ (k ≫ (Classical.forgetCoefficients.{u + 1, u, u, u}).map d)) (add_zero 1) =
      (Ext.mk₀ (𝟙 ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))))).comp hE.extClass (zero_add 1) :=
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass_naturality
      hE φ
  exact (etaleCechH1Class_integerKernel X R hT f hf z hz).trans
    (hn.trans (Ext.mk₀_id_comp hE.extClass))

/-- Every actual abelian local lift supplies the original classical
class through the constructed module cocycle, without an extra
cohomological comparison or a separately supplied edge cocycle. -/
theorem abelianExtensionModuleCechCocycle_class
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T) :
    etaleCechH1Class X R hT f hf
        (abelianExtensionModuleCechCocycle X R hT f i p hip hE b hb)
        (abelianExtensionModuleCechCocycle_cocycle X R hT f i p hip hE b hb) = hE.extClass :=
  etaleCechH1Class_eq_abelianExtClass X R hT f i p hip hE b hb hf _ _
    (abelianExtensionModuleCechCocycle_difference X R hT f i p hip hE b hb)

end EtaleCohomology
