/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveGenericUnitsVanishing
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.FieldHilbert90EtaleObjects
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.PushforwardH1Vanishing
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Small

/-!
# Actual rational-unit primitives on a smooth curve

Tsen vanishing and geometric Hilbert 90 produce an actual rational-unit
edge cochain on the original covering object. Its restriction to the
second covering kernel is the specified cocycle. In particular, one can
apply this to the original finite Kummer cup after mapping its roots of
unity into generic-point units.

The two steps use the actual abelian covering resolution. Tsen kills the
degree-two obstruction; Hilbert 90 on the original covering object then
kills the remaining degree-one obstruction. No refinement or regular
unit lift is asserted here.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian
open EtaleCohomology

namespace AlgebraicCurve

/-- Every actual second covering cocycle with rational-unit coefficients
on a smooth integral curve has a rational-unit edge primitive on the same
cover. The acyclicity inputs are the proved Tsen and Hilbert 90 theorems
for the original generic-point direct image. -/
theorem smoothCurve_genericPoint_units_exists_cech_primitive
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c]
    {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶
      (etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))) :
    ∃ b : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free.{u}) ⟶
          (etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
            (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField))),
      kernel.ι (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ≫ b = w := by
  let j := X.fromSpecStalk (genericPoint X)
  let G := (etaleAbelianPushforward j).obj
    (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))
  let A := abelianCechAugmentationSequence X.smallEtaleTopology hT f
  let B := abelianCechFirstRelationSequence X.smallEtaleTopology hT f
  have hA : A.ShortExact :=
    abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf
  have hB : B.ShortExact :=
    abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f
  let e : Ext A.X₁ G 1 := hB.extClass.comp (Ext.mk₀ w) (add_zero 1)
  have hTsen : hA.extClass.comp e (show 1 + 1 = 2 from rfl) = 0 :=
    smoothCurve_genericPoint_units_H2_eq_zero K c _
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hA G e
    (show 1 + 1 = 2 from rfl) hTsen
  have ha0 : a = 0 :=
    etalePushforward_cohomologyPresheaf_one_eq_zero j
      (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField))) V
      (fun z => etaleMultiplicativeGroup_H1_eq_zero_at_etale_object_of_field
        X.functionField ((etaleBaseChange j).obj V) z) a
  have he : e = 0 := by
    rw [ha0, Ext.comp_zero] at ha
    exact ha.symm
  obtain ⟨a', ha'⟩ := Ext.contravariant_sequence_exact₁ hB G
    (Ext.mk₀ w) (add_zero 1) he
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective B.X₂ G).surjective a'
  refine ⟨b, ?_⟩
  exact (Ext.mk₀_bijective B.X₁ G).injective
    ((Ext.mk₀_comp_mk₀ B.f b).symm.trans ha')

end AlgebraicCurve
