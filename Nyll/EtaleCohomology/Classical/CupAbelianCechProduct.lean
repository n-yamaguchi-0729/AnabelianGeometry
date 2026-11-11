/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CupCechH1
public import Nyll.EtaleCohomology.Classical.CupCechH1Product
public import Nyll.EtaleCohomology.Classical.CupCechTwoStepComparison
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleCechFaces
public import Nyll.EtaleCohomology.Classical.FreeModuleCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# The actual cup triangle as an abelian two-step cocycle

The actual second-kernel comparison gives an abelian representative
of the original module cup. Its triangle values are the same original
product `a₁₂ b₀₁`, through the actual free-source cochain equivalence.
The resulting two-step class is therefore in the original sheaf
cohomology with its integer source. This is the representative used
with the actual multiplicative-group Kummer sequence.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)

variable
  (a : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  (ha : ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
    (freeModuleCechTriangleBoundaryNat R (yoneda.map f))) ≫ a = 0)
  (b : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  (hb : ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
    (freeModuleCechTriangleBoundaryNat R (yoneda.map f))) ≫ b = 0)

/-- The original cup has an actual representative on the second
abelian covering kernel, with the original forgotten coefficient sheaf. -/
def abelianCechCocycleProduct :
    kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :=
  moduleCechSecondIntegerKernelMap X R hT f hf ≫
    (Classical.forgetCoefficients.{u + 1, u, u, u}).map (moduleCechCocycleProduct X R hT f hf a ha b
      hb)

/-- Every original triangle retains the actual product of its two
original edge values under the abelian cochain comparison. -/
theorem abelianCechCocycleProduct_triangles :
    abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
        abelianCechCocycleProduct X R hT f hf a ha b hb =
      freeModuleSheafUnderlyingHomEquiv X R (cechTriangleFunctor (yoneda.map f))
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        (freeModuleSheafAction X R
          ((freeModuleSheafFunctor X R).map (cechTriangleEdge12 (yoneda.map f)) ≫ a)
          ((freeModuleSheafFunctor X R).map (cechTriangleEdge01 (yoneda.map f)) ≫ b)) := by
  rw [abelianCechCocycleProduct, ← Category.assoc,
    moduleCechSecondIntegerKernelMap_triangles, Category.assoc,
    ← Functor.map_comp, moduleCechCocycleProduct_triangles,
    freeModuleSheafUnderlyingHomEquiv_eq]

/-- The original cup of the two original degree-one classes is the
actual abelian two-step connecting class of this same representative. -/
theorem etaleCohomologyCup_cechH1_abelian :
    etaleCohomologyCup X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1 1 2 rfl
        (etaleCechH1Class X R hT f hf a ha) (etaleCechH1Class X R hT f hf b hb) =
      ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp
        (Ext.mk₀ (abelianCechCocycleProduct X R hT f hf a ha b hb)) (add_zero 2) := by
  rw [etaleCohomologyCup_cechH1]
  exact etaleModuleCechTwoStepClass_forget X R hT f hf
    (moduleCechCocycleProduct X R hT f hf a ha b hb)

end EtaleCohomology
