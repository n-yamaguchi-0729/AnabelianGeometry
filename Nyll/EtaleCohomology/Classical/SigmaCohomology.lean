/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
public import Nyll.EtaleCohomology.Classical.NatInjectiveResolution
public import Nyll.SchemeTheory.Etale.OverField.Decomposition
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Cohomology on disjoint unions

Exactness and cohomology vanishing on an étale disjoint union follow by
gluing componentwise boundary lifts for the actual injective resolution.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
namespace EtaleCohomology

/-- Exactness of sections on a disjoint union follows by gluing
componentwise boundary lifts. -/
theorem etaleSigma_sections_exact {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h : ∀ i, (S.map ((sheafSections X.smallEtaleTopology
      AddCommGrpCat.{u}).obj (op (U i)))).Exact) :
    (S.map ((sheafSections X.smallEtaleTopology
      AddCommGrpCat.{u}).obj (op (etaleSigma U)))).Exact := by
  let E := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
  let T := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  apply (ShortComplex.ab_exact_iff (S.map (E (op (etaleSigma U))))).mpr
  intro q hq
  have hq' : S.g.hom.app (op (etaleSigma U)) q = 0 := hq
  have hi (i : ι) :
      S.g.hom.app (op (U i)) (S.X₂.obj.map (etaleSigmaInj U i).op q) = 0 := by
    rw [S.g.hom.naturality_apply, hq', map_zero]
  choose b hb using fun i =>
    ((ShortComplex.ab_exact_iff (S.map (E (op (U i))))).mp (h i))
      (S.X₂.obj.map (etaleSigmaInj U i).op q) (by
        change S.g.hom.app (op (U i)) _ = 0
        exact hi i)
  let b' : ∀ i, (T.obj S.X₁).obj.obj (op (U i)) := fun i => b i
  let q' : (T.obj S.X₂).obj.obj (op (etaleSigma U)) := q
  let sType := etaleSigmaSection U (T.obj S.X₁) b'
  have hbT (i : ι) : (T.map S.f).hom.app (op (U i)) (b' i) =
      (T.obj S.X₂).obj.map (etaleSigmaInj U i).op q' := hb i
  have hglobal : (T.map S.f).hom.app (op (etaleSigma U)) sType = q' := by
    apply etaleSigmaSection_ext U (T.obj S.X₂)
    intro i
    rw [← (T.map S.f).hom.naturality_apply, etaleSigmaSection_restrict]
    exact hbT i
  let s : ↑((S.map (E (op (etaleSigma U)))).X₁) := sType
  refine ⟨s, ?_⟩
  change (T.map S.f).hom.app (op (etaleSigma U)) sType = q'
  exact hglobal

/-- Actual derived sheaf cohomology vanishes on an arbitrary disjoint
union if it vanishes on every component, in any degree. -/
theorem etaleCohomologyPresheaf_eq_zero_on_sigma
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (h : ∀ i, ∀ a : Sheaf.H'.{u} F n (U i), a = 0)
    (a : Sheaf.H'.{u} F n (etaleSigma U)) : a = 0 := by
  let I := injectiveResolution F
  let E := sheafSections X.smallEtaleTopology AddCommGrpCat.{u}
  have hc (i : ι) : IsZero
      ((((E.obj (op (U i))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology n) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply AddCommGrpCat.ext
    intro b
    change b = 0
    let e := etaleCohomologyPresheafEvaluationResolutionEquiv X (U i) F I n
    calc
      b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = e 0 := congrArg e (h i (e.symm b))
      _ = 0 := e.map_zero
  have hs (i : ι) : ((I.cocomplex.sc n).map (E.obj (op (U i)))).Exact :=
    (ShortComplex.exact_iff_isZero_homology
      ((I.cocomplex.sc n).map (E.obj (op (U i))))).mpr (hc i)
  have hsigma := etaleSigma_sections_exact U (I.cocomplex.sc n) hs
  have hz : IsZero
      ((((E.obj (op (etaleSigma U))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology n) :=
    (ShortComplex.exact_iff_isZero_homology
      ((I.cocomplex.sc n).map (E.obj (op (etaleSigma U))))).mp hsigma
  let e := etaleCohomologyPresheafEvaluationResolutionEquiv X (etaleSigma U) F I n
  apply e.injective
  rw [e.map_zero]
  have hid := (IsZero.iff_id_eq_zero _).mp hz
  exact congrArg (fun m => m (e a)) hid

/-- Vanishing at field-valued étale objects implies vanishing at every
object of the small étale site of a field, including infinite unions. -/
theorem etaleCohomologyPresheaf_eq_zero_of_field_objects
    (K : Type u) [Field K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (h : ∀ (L : Type u) [Field L]
      (a : CommRingCat.of K ⟶ CommRingCat.of L) [IsFiniteEtale (Spec.map a)],
      ∀ b : Sheaf.H'.{u} F n (Scheme.Etale.mk (Spec.map a)), b = 0)
    (V : (Spec (.of K)).Etale) (b : Sheaf.H'.{u} F n V) : b = 0 := by
  obtain ⟨L, a, e, hfield, hsep, he⟩ := Scheme.Etale.exists_iso_sigmaSpec K V
  have hfinite (x : V.left) : IsFiniteEtale (Spec.map (a x)) := by
    let : Field (L x) := (hfield x).toField
    let : Algebra K (L x) := (a x).hom.toAlgebra
    have : Module.Finite K (L x) := (hsep x).1
    have : Algebra.IsSeparable K (L x) := (hsep x).2
    have : Algebra.FormallyEtale K (L x) :=
      Algebra.FormallyEtale.of_isSeparable K (L x)
    have : Algebra.Etale K (L x) :=
      ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    rw [IsFiniteEtale.SpecMap_iff]
    change (algebraMap K (L x)).FiniteEtale
    rw [RingHom.finiteEtale_algebraMap_iff, Algebra.finiteEtale_iff]
    exact ⟨inferInstance, inferInstance⟩
  let U (x : V.left) : (Spec (.of K)).Etale :=
    MorphismProperty.Over.mk ⊤ (Spec.map (a x)) (by
      have := hfinite x
      infer_instance)
  let eV : etaleSigma U ≅ V := MorphismProperty.Over.isoMk e he
  have hU (x : V.left) (c : Sheaf.H'.{u} F n (U x)) : c = 0 := by
    let : Field (L x) := (hfield x).toField
    have : IsFiniteEtale (Spec.map (a x)) := hfinite x
    have : Etale (Spec.map (a x)) := by
      infer_instance
    exact h (L x) (a x) c
  let eH := (F.cohomologyPresheaf n).mapIso eV.op
  let eA := eH.addCommGroupIsoToAddEquiv
  apply eA.injective
  rw [eA.map_zero]
  exact etaleCohomologyPresheaf_eq_zero_on_sigma U F n hU (eA b)

end EtaleCohomology
