/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianCechConnecting
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorH1
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Actual divisor vertex primitives on the original cover

The proved vanishing of H¹ of the closed-point divisor sheaf supplies a
vertex primitive for every divisor edge cocycle on the original cover.
The covering object need not be affine: the original augmentation exact
sequence and the native cohomology vanishing suffice.

On a smooth integral curve, the divisor of a rational-unit edge lift is
such a cocycle. The primitive below uses the actual comparison between
closed-point divisors and the quotient of generic units by regular units.
It does not assert a regular-unit lift of the divisor vertex section;
that subsequent step requires a refinement and actual local lifts.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} (c : X ⟶ Spec (.of K)) [IsProper c]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)

local notation "P₀" => CategoryTheory.Functor.obj (freeAbelianSheafYoneda X.smallEtaleTopology) V
local notation "P₁" =>
  CategoryTheory.Functor.obj (presheafToSheaf X.smallEtaleTopology AddCommGrpCat)
    (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free)
local notation "d₁" =>
  CategoryTheory.Functor.map (presheafToSheaf X.smallEtaleTopology AddCommGrpCat)
    (freeCechEdgeBoundaryNat (yoneda.map f))
local notation "d₂" =>
  CategoryTheory.Functor.map (presheafToSheaf X.smallEtaleTopology AddCommGrpCat)
    (freeCechTriangleBoundaryNat (yoneda.map f))

include c hT hf in
/-- The actual divisor edge cocycle has a vertex primitive on the
same original cover, supplied by the proved native H¹ vanishing. -/
theorem proper_closedPointDivisor_exists_cech_vertexPrimitive
    (z : P₁ ⟶ closedPointDivisorSheaf X) (hz : d₂ ≫ z = 0) :
    ∃ b : P₀ ⟶ closedPointDivisorSheaf X, d₁ ≫ b = z := by
  let A := abelianCechAugmentationSequence X.smallEtaleTopology hT f
  have hA : A.ShortExact :=
    abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf
  let k := abelianCechCocycleDesc X hT f z hz
  have hk : hA.extClass.comp (Ext.mk₀ k) (add_zero 1) = 0 :=
    closedPointDivisorSheaf_H1_eq_zero_of_proper c _
  obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₁ hA
    (closedPointDivisorSheaf X) (Ext.mk₀ k) (add_zero 1) hk
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective A.X₂ (closedPointDivisorSheaf X)).surjective e
  have hb : A.f ≫ b = k :=
    (Ext.mk₀_bijective A.X₁ (closedPointDivisorSheaf X)).injective
      ((Ext.mk₀_comp_mk₀ A.f b).symm.trans he)
  refine ⟨b, ?_⟩
  rw [← abelianCechFirstRelationMap_comp X.smallEtaleTopology hT f,
    Category.assoc, hb]
  exact abelianCechCocycleDesc_comp X hT f z hz

variable [IsIntegral X] [SmoothOfRelativeDimension 1 c]

local notation "S" => etaleGenericUnitShortComplex X
local notation "D" => smoothCurveClosedPointDivisorGenericUnitIso c
local notation "q" => abelianCechFirstRelationMap X.smallEtaleTopology hT f

include hf in
/-- The divisor of an actual rational-unit edge lift is the boundary
of an actual divisor vertex section on the same original cover. The
prescribed second difference takes values in original regular units. -/
theorem smoothCurve_genericUnitEdge_exists_divisorPrimitive
    (w : kernel q ⟶ (S).X₁) (b : P₁ ⟶ (S).X₂)
    (hb : kernel.ι q ≫ b = w ≫ (S).f) :
    ∃ a : P₀ ⟶ closedPointDivisorSheaf X,
      d₁ ≫ a = b ≫ (S).g ≫ (D).inv := by
  let d : (S).X₃ ⟶ closedPointDivisorSheaf X := (D).inv
  change ∃ a : P₀ ⟶ closedPointDivisorSheaf X, d₁ ≫ a = b ≫ (S).g ≫ d
  have hker : kernel.ι q ≫ (b ≫ (S).g ≫ d) = 0 := by
    calc
      _ = (kernel.ι q ≫ b) ≫ ((S).g ≫ d) :=
        (Category.assoc _ _ _).symm
      _ = (w ≫ (S).f) ≫ ((S).g ≫ d) :=
        congrArg (· ≫ ((S).g ≫ d)) hb
      _ = w ≫ (((S).f ≫ (S).g) ≫ d) := by simp only [Category.assoc]
      _ = 0 := by rw [(S).zero, zero_comp, comp_zero]
  have hz : d₂ ≫ (b ≫ (S).g ≫ d) = 0 := by
    rw [← abelianCechSecondRelationMap_comp X.smallEtaleTopology hT f,
      Category.assoc, hker, comp_zero]
  exact proper_closedPointDivisor_exists_cech_vertexPrimitive c hT f hf
    (b ≫ (S).g ≫ d) hz

end EtaleCohomology
