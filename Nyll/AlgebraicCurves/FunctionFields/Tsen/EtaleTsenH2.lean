/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Tsen.ActualUnitGaloisH2OfTsen
public import Nyll.EtaleCohomology.Classical.FieldGaloisDescent
public import Nyll.EtaleCohomology.Classical.LiftedFieldSectionRepresentations
public import Nyll.EtaleCohomology.Classical.FieldKummer
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Actual derived etale Tsen vanishing

Finite Galois descent and the proved action comparisons pass from Tsen's
group cohomology theorem to derived sheaf H2, by an actual injective
embedding and the Ext long exact sequence.
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory Limits AlgebraicGeometry
open EtaleCohomology

namespace AlgebraicCurve

/-- Tsen and actual finite-Galois descent give vanishing of derived
etale H1 for the quotient of an injective sheaf by Gm. -/
theorem actualUnitInjectiveQuotient_H1_eq_zero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {I Q : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u}} [Injective I]
    (i : etaleMultiplicativeGroupSheaf (Spec (.of F)) ⟶ I) (p : I ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (a : Sheaf.H.{u} Q 1) : a = 0 := by
  apply etaleH1_eq_zero_of_fieldGalois_cocycle_primitives F Q ?_ a
  intro E _ _ _ _ c hc
  let z : groupCohomology.cocycles₁ (liftedFieldGaloisSheafSectionsRep F E Q) :=
    ⟨c, (groupCohomology.mem_cocycles₁_iff
      (A := liftedFieldGaloisSheafSectionsRep F E Q) c).mpr (by
        intro σ τ
        exact hc σ τ)⟩
  have hz' := liftedActualUnitInjectiveQuotient_sections_H1_eq_zero_of_tsen
    K x hx hfin E i p hz hS (groupCohomology.H1π _ z)
  obtain ⟨s, hs⟩ := (groupCohomology.H1π_eq_zero_iff z).mp hz'
  exact ⟨s, fun σ => congrFun hs σ⟩

/-- The actual derived etale H2 of Gm vanishes over a one-variable function field
over an algebraically closed field. -/
theorem etaleMultiplicativeGroup_H2_eq_zero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf (Spec (.of F))) 2) : a = 0 := by
  let X : Scheme.{u} := Spec (.of F)
  let A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    etaleMultiplicativeGroupSheaf X
  let i : A ⟶ Injective.under A := Injective.ι A
  let p := cokernel.π i
  have hz : i ≫ p = 0 := cokernel.condition i
  have hs : (ShortComplex.mk i p hz).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  let Z : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  obtain ⟨b, hb⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁
    Z hs a (CategoryTheory.Abelian.Ext.eq_zero_of_injective _) (n₀ := 1) rfl
  rw [actualUnitInjectiveQuotient_H1_eq_zero_of_tsen K x hx hfin i p hz hs b,
    CategoryTheory.Abelian.Ext.zero_comp] at hb
  exact hb.symm

/-- Kummer injectivity and the actual derived Tsen theorem give vanishing
of roots-of-unity H2 over the same function field. -/
theorem etaleRootsOfUnity_H2_eq_zero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {n : ℕ} (hn : 0 < n) (hnF : IsUnit (n : Γ(Spec (.of F), ⊤)))
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf (Spec (.of F)) n) 2) : a = 0 := by
  apply etaleRootsOfUnityH2ToMultiplicativeGroup_injective_of_field F hn hnF
  rw [map_zero]
  exact etaleMultiplicativeGroup_H2_eq_zero_of_tsen K x hx hfin _

end AlgebraicCurve
