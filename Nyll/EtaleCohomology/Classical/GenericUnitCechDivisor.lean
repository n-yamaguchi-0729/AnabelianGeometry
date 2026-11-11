/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianCechConnecting
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# The global divisor of an actual transition cocycle

Hilbert 90 supplies a rational vertex primitive of a regular-unit edge
cocycle on its original cover. Its divisor descends to a global section
of the actual quotient of generic units by regular units. The original
divisor boundary is exactly the given transition class, with its sign
fixed by the original covering differential.

The rational primitive and its descended divisor are retained together.
On a smooth curve the existing divisor comparison can therefore read
the native degree from this same divisor, rather than selecting an
unrelated representative of the cohomology class.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) [IsIntegral X]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)

local notation "J" => X.smallEtaleTopology
local notation "S" => etaleGenericUnitShortComplex X
local notation "P₀" => CategoryTheory.Functor.obj (freeAbelianSheafYoneda J) V
local notation "P₁" => CategoryTheory.Functor.obj (presheafToSheaf J AddCommGrpCat)
  (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free)
local notation "d₁" => CategoryTheory.Functor.map (presheafToSheaf J AddCommGrpCat)
  (freeCechEdgeBoundaryNat (yoneda.map f))
local notation "d₂" => CategoryTheory.Functor.map (presheafToSheaf J AddCommGrpCat)
  (freeCechTriangleBoundaryNat (yoneda.map f))

include hT hf in
/-- Hilbert 90 supplies a rational vertex primitive of a specified
generic-unit cocycle on the same original cover. -/
theorem abelianCechGenericUnitCocycle_exists_vertexPrimitive
    (z : P₁ ⟶ (S).X₂) (hz : d₂ ≫ z = 0) :
    ∃ t : P₀ ⟶ (S).X₂, d₁ ≫ t = z := by
  let A := abelianCechAugmentationSequence J hT f
  have hA : A.ShortExact := abelianCechAugmentationSequence_shortExact J hT f hf
  let k := abelianCechCocycleDesc X hT f z hz
  have hk : hA.extClass.comp (Ext.mk₀ k) (add_zero 1) = 0 :=
    genericPoint_units_H1_eq_zero X _
  obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₁ hA (S).X₂
    (Ext.mk₀ k) (add_zero 1) hk
  obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective A.X₂ (S).X₂).surjective e
  have ht : A.f ≫ t = k :=
    (Ext.mk₀_bijective A.X₁ (S).X₂).injective
      ((Ext.mk₀_comp_mk₀ A.f t).symm.trans he)
  refine ⟨t, ?_⟩
  have hrel : abelianCechFirstRelationMap J hT f ≫ A.f = d₁ :=
    abelianCechFirstRelationMap_comp J hT f
  calc
    d₁ ≫ t = (abelianCechFirstRelationMap J hT f ≫ A.f) ≫ t :=
      congrArg (fun r : P₁ ⟶ A.X₂ => r ≫ t) hrel.symm
    _ = abelianCechFirstRelationMap J hT f ≫ (A.f ≫ t) :=
      Category.assoc _ _ _
    _ = abelianCechFirstRelationMap J hT f ≫ k :=
      congrArg (fun r : A.X₁ ⟶ (S).X₂ => abelianCechFirstRelationMap J hT f ≫ r) ht
    _ = z := abelianCechCocycleDesc_comp X hT f z hz

/-- A specified rational lift and its specified descended divisor
compute the original transition class, with the covering differential's sign. -/
theorem abelianCechMultiplicativeCocycle_boundary_of_lift
    (z : P₁ ⟶ (S).X₁) (hz : d₂ ≫ z = 0)
    (t : P₀ ⟶ (S).X₂)
    (a : (constantSheaf J AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ (S).X₃)
    (ht : d₁ ≫ t = z ≫ (S).f)
    (ha : abelianCechUnitAugmentation J hT f ≫ a = t ≫ (S).g) :
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl (Ext.mk₀ a) =
      abelianCechH1Class X hT f hf z hz := by
  let A := abelianCechAugmentationSequence J hT f
  have hA : A.ShortExact := abelianCechAugmentationSequence_shortExact J hT f hf
  have hS : (S).ShortExact := etaleGenericUnitShortComplex_shortExact X
  let k := abelianCechCocycleDesc X hT f z hz
  have hk : A.f ≫ t = k ≫ (S).f := by
    have : Epi (abelianCechFirstRelationMap J hT f) :=
      abelianCechFirstRelationMap_epi J hT f
    apply (cancel_epi (abelianCechFirstRelationMap J hT f)).mp
    have hrel : abelianCechFirstRelationMap J hT f ≫ A.f = d₁ :=
      abelianCechFirstRelationMap_comp J hT f
    have hdesc : abelianCechFirstRelationMap J hT f ≫ k = z :=
      abelianCechCocycleDesc_comp X hT f z hz
    calc
      _ = (abelianCechFirstRelationMap J hT f ≫ A.f) ≫ t :=
        (Category.assoc _ _ _).symm
      _ = d₁ ≫ t := congrArg (fun r : P₁ ⟶ P₀ => r ≫ t) hrel
      _ = z ≫ (S).f := ht
      _ = (abelianCechFirstRelationMap J hT f ≫ k) ≫ (S).f :=
        congrArg (fun r : P₁ ⟶ (S).X₁ => r ≫ (S).f) hdesc.symm
      _ = _ := Category.assoc _ _ _
  let φ : A ⟶ S :=
    { τ₁ := k
      τ₂ := t
      τ₃ := a
      comm₁₂ := hk.symm
      comm₂₃ := ha.symm }
  change (Ext.mk₀ a).comp hS.extClass rfl =
    hA.extClass.comp (Ext.mk₀ k) (add_zero 1)
  exact (hA.extClass_naturality hS φ).symm

/-- An actual regular-unit cocycle has a rational vertex primitive whose
divisor descends on the same cover and represents its original H¹ class. -/
theorem abelianCechMultiplicativeCocycle_exists_genericUnitDivisor
    (z : P₁ ⟶ etaleMultiplicativeGroupSheaf X) (hz : d₂ ≫ z = 0) :
    ∃ (t : P₀ ⟶ (S).X₂)
      (a : (constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ etaleGenericUnitQuotient X),
      d₁ ≫ t = z ≫ (S).f ∧
      abelianCechUnitAugmentation J hT f ≫ a = t ≫ (S).g ∧
      Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl (Ext.mk₀ a) =
        abelianCechH1Class X hT f hf z hz := by
  let A := abelianCechAugmentationSequence J hT f
  have hA : A.ShortExact := abelianCechAugmentationSequence_shortExact J hT f hf
  have : Epi A.g := hA.epi_g
  have hz' : d₂ ≫ (z ≫ (S).f) = 0 :=
    (Category.assoc d₂ z (S).f).symm.trans
      ((congrArg (fun r => r ≫ (S).f) hz).trans zero_comp)
  obtain ⟨t, ht⟩ := abelianCechGenericUnitCocycle_exists_vertexPrimitive
    X hT f hf (z ≫ (S).f) hz'
  have hzero : kernel.ι A.g ≫ (t ≫ (S).g) = 0 := by
    have : Epi (abelianCechFirstRelationMap J hT f) :=
      abelianCechFirstRelationMap_epi J hT f
    apply (cancel_epi (abelianCechFirstRelationMap J hT f)).mp
    have hrel : abelianCechFirstRelationMap J hT f ≫ kernel.ι A.g = d₁ :=
      abelianCechFirstRelationMap_comp J hT f
    calc
      _ = (abelianCechFirstRelationMap J hT f ≫ kernel.ι A.g) ≫ (t ≫ (S).g) :=
        (Category.assoc _ _ _).symm
      _ = d₁ ≫ (t ≫ (S).g) := congrArg (fun r : P₁ ⟶ P₀ => r ≫ (t ≫ (S).g)) hrel
      _ = (d₁ ≫ t) ≫ (S).g := (Category.assoc _ _ _).symm
      _ = (z ≫ (S).f) ≫ (S).g := congrArg (fun r => r ≫ (S).g) ht
      _ = z ≫ ((S).f ≫ (S).g) := Category.assoc _ _ _
      _ = z ≫ 0 := congrArg (fun r => z ≫ r) (S).zero
      _ = 0 := comp_zero
      _ = _ := comp_zero.symm
  let a := Abelian.epiDesc A.g (t ≫ (S).g) hzero
  have ha : A.g ≫ a = t ≫ (S).g := Abelian.comp_epiDesc A.g (t ≫ (S).g) hzero
  exact ⟨t, a, ht, ha,
    abelianCechMultiplicativeCocycle_boundary_of_lift X hT f hf z hz t a ht ha⟩

end EtaleCohomology
