/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CupCechH1
public import Nyll.EtaleCohomology.Classical.CupCechKernelComparison
public import Nyll.EtaleCohomology.Classical.CupCechResolution
public import Nyll.EtaleCohomology.Classical.CupCoefficientSource
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.FreeModuleCechCoefficientComparison
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra

/-!
# The first covering-kernel class of an original cup product

An original edge cocycle and a native degree-one class construct an
actual degree-one class on the first abelian covering kernel. Its
restriction to edges is the same coefficient cocycle acting on that
same native class. Its transgression is the original cup product.

Only the first factor is represented by a cocycle on this cover; the
second factor need not vanish on it. This is the comparison needed
for a tensor assembled from constant degree-one overlap classes.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
  {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}

section KernelHom

variable
  (k : kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f) ⟶
    (Classical.forgetCoefficients.{u + 1, u, u, u}).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)))
  (x : etaleCohomology X R F 1)

/-- An actual scalar map on the first covering kernel acts on the
original module extension. This form also accepts a kernel map
transported from a cover on another scheme. -/
def abelianCechKernelHomCupClass :
    Ext.{u} (kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f))
      ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F) 1 :=
  (Ext.mk₀ k).comp
    (((etaleConstantModuleExtCohomologyEquiv X R F 1).symm x).mapExactFunctor
      (Classical.forgetCoefficients.{u + 1, u, u, u}))
      (zero_add 1)

/-- The transgression of an actual scalar kernel map is its original
native cup action, including the original constant integer source. -/
theorem abelianCechKernelHomCupClass_transgression :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechKernelHomCupClass X R hT f k x) (show 1 + 1 = 2 from rfl) =
      etaleCohomologyCup X R F 1 1 2 rfl
        ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
          (Ext.mk₀ k) (add_zero 1)) x := by
  let y : etaleCohomology X R
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1 :=
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
      (Ext.mk₀ k) (add_zero 1)
  let yM := (etaleConstantModuleExtCohomologyEquiv X R
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1).symm y
  let xM := (etaleConstantModuleExtCohomologyEquiv X R F 1).symm x
  have hy : (Ext.mk₀ (etaleConstantIntegerHom X R)).comp
      (yM.mapExactFunctor (Classical.forgetCoefficients.{u + 1, u, u, u})) (zero_add 1) = y :=
    (etaleConstantModuleExtCohomologyEquiv_forget X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1
      yM).symm.trans
      ((etaleConstantModuleExtCohomologyEquiv X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        1).apply_symm_apply y)
  let U := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let G := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let c := Ext.mk₀ (etaleConstantIntegerHom X R)
  have hcup : etaleCohomologyCup X R F 1 1 2 rfl y x =
      y.comp (xM.mapExactFunctor G) (show 1 + 1 = 2 from rfl) :=
    (etaleCohomologyCup_apply X R F 1 1 2 rfl y x).trans
      ((etaleConstantModuleExtCohomologyEquiv_forget X R F 2
        (yM.comp xM (show 1 + 1 = 2 from rfl))).trans
        ((congrArg (fun z : Ext.{u} (G.obj U) (G.obj F) 2 =>
          c.comp z (zero_add 2))
          (Ext.mapExactFunctor_comp G yM xM (show 1 + 1 = 2 from rfl))).trans
          ((Ext.comp_assoc c (yM.mapExactFunctor G) (xM.mapExactFunctor G)
            (zero_add 1) (show 1 + 1 = 2 from rfl)
            (show 0 + 1 + 1 = 2 from rfl)).symm.trans
            (congrArg (fun z : etaleCohomology X R U 1 =>
              z.comp (xM.mapExactFunctor G) (show 1 + 1 = 2 from rfl)) hy))))
  exact (Ext.comp_assoc_of_second_deg_zero
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass
    (Ext.mk₀ k) (xM.mapExactFunctor G) (show 1 + 1 = 2 from rfl)).symm.trans hcup.symm

end KernelHom

section CupKernel

variable
  (b : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  (hb : ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
    (freeModuleCechTriangleBoundaryNat R (yoneda.map f))) ≫ b = 0)
  (x : etaleCohomology X R F 1)

/-- The original scalar edge cocycle acts on the original module
extension class, through the actual integer covering-kernel map. -/
def abelianCechCupKernelClass :
    Ext.{u} (kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f))
      ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F) 1 :=
  abelianCechKernelHomCupClass X R hT f
    (moduleCechIntegerKernelMap X R hT f hf ≫
      (Classical.forgetCoefficients.{u + 1, u, u, u}).map (moduleCechCocycleDesc X R hT f b hb)) x

/-- The actual first-relation restriction is the unchanged edge
coefficient acting on the unchanged native extension class. -/
theorem abelianCechCupKernelClass_relation :
    (Ext.mk₀ (abelianCechFirstRelationMap X.smallEtaleTopology hT f)).comp
        (abelianCechCupKernelClass X R hT f hf b hb x) (zero_add 1) =
      (Ext.mk₀ (freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map b)).comp
          (((etaleConstantModuleExtCohomologyEquiv X R F 1).symm x).mapExactFunctor
            (Classical.forgetCoefficients.{u + 1, u, u, u}))
            (zero_add 1) := by
  rw [abelianCechCupKernelClass, abelianCechKernelHomCupClass, Ext.mk₀_comp_mk₀_assoc,
    ← Category.assoc, moduleCechIntegerKernelMap_relation,
    Category.assoc, ← Functor.map_comp, moduleCechCocycleDesc_comp]

/-- The transgression of the constructed covering-kernel class is
the original native cup, with its original constant-source comparison. -/
theorem abelianCechCupKernelClass_transgression :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechCupKernelClass X R hT f hf b hb x) (show 1 + 1 = 2 from rfl) =
      etaleCohomologyCup X R F 1 1 2 rfl
        (etaleCechH1Class X R hT f hf b hb) x := by
  exact (abelianCechKernelHomCupClass_transgression X R hT f hf
    (moduleCechIntegerKernelMap X R hT f hf ≫
      (Classical.forgetCoefficients.{u + 1, u, u, u}).map
        (moduleCechCocycleDesc X R hT f b hb)) x).trans
      (congrArg (fun z : etaleCohomology X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1 =>
          etaleCohomologyCup X R F 1 1 2 rfl z x)
        (etaleCechH1Class_integerKernel X R hT f hf b hb).symm)

end CupKernel

/-- Equality on the original edge source gives an actual second-kernel
cochain. Its two-step class retains the difference of the original
transgressions. This applies in particular to finite sums of cups. -/
theorem abelianCechKernelClass_exists_residual
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a b : Ext.{u} (kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f)) G 1)
    (h : (Ext.mk₀ (abelianCechFirstRelationMap X.smallEtaleTopology hT f)).comp
        a (zero_add 1) =
      (Ext.mk₀ (abelianCechFirstRelationMap X.smallEtaleTopology hT f)).comp
        b (zero_add 1)) :
    ∃ w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶ G,
      (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass.comp
          (Ext.mk₀ w) (add_zero 1) = a - b ∧
        (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
            a (show 1 + 1 = 2 from rfl) -
          (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
            b (show 1 + 1 = 2 from rfl) =
        ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
          (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
            (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2) := by
  let hA := abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf
  let hB := abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f
  have hz : (Ext.mk₀ (abelianCechFirstRelationMap X.smallEtaleTopology hT f)).comp
      (a - b) (zero_add 1) = 0 := by
    simp only [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg]
    rw [h, add_neg_cancel]
  obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₃ hB G (a - b) hz
    (show 1 + 0 = 1 from rfl)
  obtain ⟨w, rfl⟩ := (Ext.mk₀_bijective _ G).surjective e
  refine ⟨w, he, ?_⟩
  calc
    _ = hA.extClass.comp (a - b) (show 1 + 1 = 2 from rfl) :=
      ((congrArg (fun z : Ext.{u}
          (kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f)) G 1 =>
        hA.extClass.comp z (show 1 + 1 = 2 from rfl)) (sub_eq_add_neg a b)).trans
        ((Ext.comp_add hA.extClass a (-b) (show 1 + 1 = 2 from rfl)).trans
          ((congrArg (fun z => hA.extClass.comp a (show 1 + 1 = 2 from rfl) + z)
            (Ext.comp_neg hA.extClass b (show 1 + 1 = 2 from rfl))).trans
              (sub_eq_add_neg _ _).symm))).symm
    _ = hA.extClass.comp (hB.extClass.comp (Ext.mk₀ w) (add_zero 1)) rfl :=
      congrArg (fun z : Ext.{u}
        (kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f)) G 1 =>
          hA.extClass.comp z (show 1 + 1 = 2 from rfl)) he.symm
    _ = _ :=
      (Ext.comp_assoc_of_third_deg_zero hA.extClass hB.extClass (Ext.mk₀ w) rfl).symm

/-- Agreement of the actual overlap classes leaves an explicitly
constructed second-kernel residual. Its original two-step class is
exactly the difference from the original cup. Vanishing of this
residual is a further geometric statement, not inferred from overlap
agreement alone. -/
theorem abelianCechCupKernelClass_exists_residual
    (b : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (hb : ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f))) ≫ b = 0)
    (x : etaleCohomology X R F 1)
    (a : Ext.{u} (kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f))
      ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F) 1)
    (h : (Ext.mk₀ (abelianCechFirstRelationMap X.smallEtaleTopology hT f)).comp
        a (zero_add 1) =
      (Ext.mk₀ (freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map b)).comp
          (((etaleConstantModuleExtCohomologyEquiv X R F 1).symm x).mapExactFunctor
            (Classical.forgetCoefficients.{u + 1, u, u, u}))
            (zero_add 1)) :
    ∃ w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}).obj F,
      (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass.comp
          (Ext.mk₀ w) (add_zero 1) = a - abelianCechCupKernelClass X R hT f hf b hb x ∧
        (show etaleCohomology X R F 2 from
          (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
            a (show 1 + 1 = 2 from rfl)) -
          etaleCohomologyCup X R F 1 1 2 rfl (etaleCechH1Class X R hT f hf b hb) x =
        ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
          (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
            (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2) := by
  have h' := h.trans (abelianCechCupKernelClass_relation X R hT f hf b hb x).symm
  obtain ⟨w, hw, htwo⟩ := abelianCechKernelClass_exists_residual X hT f hf
    ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F) a (abelianCechCupKernelClass X R hT f hf
      b hb x) h'
  refine ⟨w, hw, ?_⟩
  exact (congrArg (fun z : etaleCohomology X R F 2 =>
    (show etaleCohomology X R F 2 from
      (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        a (show 1 + 1 = 2 from rfl)) - z)
    (abelianCechCupKernelClass_transgression X R hT f hf b hb x).symm).trans htwo

end EtaleCohomology
