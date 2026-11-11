/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Nyll.EtaleCohomology.Classical.FieldHilbert90EtaleObjects
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.PushforwardGlobalSections
public import Nyll.EtaleCohomology.Classical.PushforwardH1Vanishing
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual generic-unit sequence and first cohomology

Geometric Hilbert 90 annihilates H¹ of the actual direct image of
function-field units. The original long exact sequence therefore identifies
H¹(Gm) with the quotient of H⁰ of the actual generic-unit quotient by the
image of H⁰ of generic-point units. This is the cohomological part of the
Picard comparison; the geometric divisor identification is separate.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits Opposite

namespace EtaleCohomology

/-- The actual direct image of generic-point units has zero first
cohomology on an integral scheme, in arbitrary characteristic. -/
theorem genericPoint_units_H1_eq_zero
    (X : Scheme.{u}) [IsIntegral X]
    (a : Sheaf.H.{u}
      ((etaleAbelianPushforward
        (X.fromSpecStalk (genericPoint X))).obj
          (etaleMultiplicativeGroupSheaf
            (Spec (.of X.functionField)))) 1) : a = 0 := by
  let j := X.fromSpecStalk (genericPoint X)
  let G := (etaleAbelianPushforward j).obj
    (etaleMultiplicativeGroupSheaf
      (Spec (.of X.functionField)))
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let e := sheafCohomologyTerminalEquiv
    X.smallEtaleTopology hT G 1
  apply e.injective
  rw [e.map_zero]
  exact etalePushforward_cohomologyPresheaf_one_eq_zero
    j (etaleMultiplicativeGroupSheaf
      (Spec (.of X.functionField))) T
    (fun b => etaleMultiplicativeGroup_H1_eq_zero_at_etale_object_of_field
      X.functionField ((etaleBaseChange j).obj T) b) (e a)

/-- Degree-zero cohomology of the original direct image consists of
units of the original function field. -/
def genericPointUnitsH0Equiv (X : Scheme.{u}) [IsIntegral X] :
    Sheaf.H.{u}
      ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))) 0 ≃+
      Additive X.functionFieldˣ :=
  (Sheaf.H.equiv₀.{u}
    ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
      (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField))))
    (MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X)).trans
      (AddEquiv.trans (etaleAbelianPushforwardGlobalSectionsIso
        (X.fromSpecStalk (genericPoint X))
        (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))).addCommGroupIsoToAddEquiv
          (etaleMultiplicativeGroupSpecSectionsEquiv
            (Spec (.of X.functionField)) (.of X.functionField) (𝟙 _)))

/-- The actual connecting homomorphism gives H¹(Gm) as the quotient of
H⁰ of generic-unit classes by the image of actual global generic units. -/
def genericUnitQuotientH0CokernelEquivH1
    (X : Scheme.{u}) [IsIntegral X] :
    (Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 ⧸
      (Sheaf.H.map (etaleGenericUnitShortComplex X).g 0).range) ≃+
        Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 := by
  let S := etaleGenericUnitShortComplex X
  let hS := etaleGenericUnitShortComplex_shortExact X
  let δ := Sheaf.H.δ hS 0 1 rfl
  have hsurj : Function.Surjective δ := by
    intro a
    exact Sheaf.H.longSequence_exact₁ hS a
      (genericPoint_units_H1_eq_zero X _) rfl
  have hker : (Sheaf.H.map S.g 0).range = δ.ker := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      change (b.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
      rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
    · intro ha
      exact Sheaf.H.longSequence_exact₃ hS a rfl ha
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective δ hsurj)

/-- On an original degree-zero generic-unit class, the quotient comparison
is the connecting homomorphism of the original short exact sequence. -/
theorem genericUnitQuotientH0CokernelEquivH1_mk
    (X : Scheme.{u}) [IsIntegral X]
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0) :
    genericUnitQuotientH0CokernelEquivH1 X (QuotientAddGroup.mk a) =
      Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl a := rfl

end EtaleCohomology
