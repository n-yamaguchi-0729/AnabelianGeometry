/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.CoverTransportNamedKummer
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryConjugacyAbelianRanges

/-! # Applying named Kummer transport to the same actual inertia conjugacy

This assembly consumes the already reconstructed conjugacy and the computed
named residues. It constructs all range, relation and source-character inputs
of the cover transport theorem; it does not postulate those inputs.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve SchemeTheory
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian
open scoped FintypeCatDiscrete
namespace AnabelianGeometry.WeightFiltration

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {X₁ : Scheme} [IsIntegral X₁] [CompactSpace X₁]
    (j₁ : X₁ ⟶ M.C) [IsOpenImmersion j₁] (hj₁ : DenseRange j₁)
    [Algebra F X₁.functionField]
    (hfield₁ : algebraMap F X₁.functionField =
      (j₁.functionFieldMap hj₁).comp M.ffEquiv.toRingHom)
    {Ω₁ : Type} [Field Ω₁] [Algebra X₁.functionField Ω₁] [Algebra F Ω₁]
    [IsScalarTower F X₁.functionField Ω₁]
    [IsSepClosed Ω₁] [IsSepClosure X₁.functionField Ω₁] [IsSepClosure F Ω₁]
    [∀ p : M.openBoundaryPlaces j₁, Algebra p.val.toValuationSubring Ω₁]
    [∀ p : M.openBoundaryPlaces j₁, IsScalarTower p.val.toValuationSubring F Ω₁]
    [Algebra K Ω₁]
    [∀ p : M.openBoundaryPlaces j₁, IsScalarTower K p.val.toValuationSubring Ω₁]
    (Q₁ : ∀ p : M.openBoundaryPlaces j₁,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω₁))
    [∀ p, (Q₁ p).IsMaximal]
    [Nontrivial (M.openBoundaryPlaces j₁)]
    {X₂ : Scheme} [IsIntegral X₂] [CompactSpace X₂]
    (j₂ : X₂ ⟶ M.C) [IsOpenImmersion j₂] (hj₂ : DenseRange j₂)
    [Algebra F X₂.functionField]
    (hfield₂ : algebraMap F X₂.functionField =
      (j₂.functionFieldMap hj₂).comp M.ffEquiv.toRingHom)
    {Ω₂ : Type} [Field Ω₂] [Algebra X₂.functionField Ω₂] [Algebra F Ω₂]
    [IsScalarTower F X₂.functionField Ω₂]
    [IsSepClosed Ω₂] [IsSepClosure X₂.functionField Ω₂] [IsSepClosure F Ω₂]
    [∀ p : M.openBoundaryPlaces j₂, Algebra p.val.toValuationSubring Ω₂]
    [∀ p : M.openBoundaryPlaces j₂, IsScalarTower p.val.toValuationSubring F Ω₂]
    [Algebra K Ω₂]
    [∀ p : M.openBoundaryPlaces j₂, IsScalarTower K p.val.toValuationSubring Ω₂]
    (Q₂ : ∀ p : M.openBoundaryPlaces j₂,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω₂))
    [∀ p, (Q₂ p).IsMaximal]
    [Nontrivial (M.openBoundaryPlaces j₂)]

include hfield₁ hfield₂ in
/-- All nonnumeric inputs of named transport follow from the same reconstructed
actual inertia conjugacy, with its fixed boundary relabelling. -/
theorem exists_namedCoverTransport_of_actualInertiaConjugacy
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (hg : genusFF K F = 0)
    (ws : Pic0.openKummerUnits K F (M.openBoundaryPlaces j₁) n)
    (wt : Pic0.openKummerUnits K F (M.openBoundaryPlaces j₂) n)
    (e : M.openBoundaryPlaces j₂ ≃ M.openBoundaryPlaces j₁)
    (i₀ : M.openBoundaryPlaces j₂) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    letI : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let ξ₁ := Spec.map (CommRingCat.ofHom (algebraMap X₁.functionField Ω₁)) ≫
      X₁.fromSpecStalk (genericPoint X₁)
    let ξ₂ := Spec.map (CommRingCat.ofHom (algebraMap X₂.functionField Ω₂)) ≫
      X₂.fromSpecStalk (genericPoint X₂)
    let Fs := FiniteEtale.fiber ξ₁
    let Ft := FiniteEtale.fiber ξ₂
    let U := M.openKummerCover (M.openBoundaryPlaces j₁) n hn ws j₁ hj₁
      (M.place_not_mem_openBoundaryPlaces j₁)
    let ys := CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j₁)
      n ws j₁ hj₁ (M.place_not_mem_openBoundaryPlaces j₁) hn ξ₁
    let yt := CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j₂)
      n wt j₂ hj₂ (M.place_not_mem_openBoundaryPlaces j₂) hn ξ₂
    letI := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces j₁)
      n ws j₁ hj₁ (M.place_not_mem_openBoundaryPlaces j₁) hn ξ₁
    letI := CurveModel.OpenKummer.kummerGeometricRootAction_commutes M
      (M.openBoundaryPlaces j₁) n ws j₁ hj₁ (M.place_not_mem_openBoundaryPlaces j₁) hn ξ₁
    ∀ (α : Aut Fs ≃ₜ* Aut Ft),
      (∀ p, ∃ a : Aut Ft,
        (genericPlaceInertia X₁ (e p).val (Q₁ (e p))).map α.toMonoidHom =
          (genericPlaceInertia X₂ p.val (Q₂ p)).map (MulAut.conj a).toMonoidHom) →
      (∀ p, finiteResidue M n j₂ hj₂ hn ξ₂ yt p =
        finiteResidue M n j₁ hj₁ hn ξ₁ ys (e p)) →
      let et := coverTransportFiberEquiv Fs Ft α U
      let het := coverTransportFiberEquiv_smul Fs Ft α U
      letI := transportedFiberTorsor et
      letI := transportedFiberSMulCommClass α.toMulEquiv et het
      ∃ u : (ZMod (n : ℕ))ˣ,
        let W := M.openKummerCover (M.openBoundaryPlaces j₂) n hn
          (wt ^ (u : ZMod (n : ℕ)).val) j₂ hj₂ (M.place_not_mem_openBoundaryPlaces j₂)
        letI := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces j₂)
          n (wt ^ (u : ZMod (n : ℕ)).val) j₂ hj₂
          (M.place_not_mem_openBoundaryPlaces j₂) hn ξ₂
        ∃ f : Ft.obj ((coverTransportOfAutEquiv Fs Ft α).functor.obj U) ≃ Ft.obj W,
          (∀ (z : rootsOfUnity (n : ℕ) K) x, f (z • x) = z • f x) ∧
          ∀ (g : Aut Ft) x, f (g • x) = g • f x := by
  let : Fintype (M.openBoundaryPlaces j₁) := (M.openBoundaryPlaces_finite j₁).fintype
  let : Fintype (M.openBoundaryPlaces j₂) := (M.openBoundaryPlaces_finite j₂).fintype
  intro nn topology ξ₁ ξ₂ Fs Ft U ys yt
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces j₁)
    n ws j₁ hj₁ (M.place_not_mem_openBoundaryPlaces j₁) hn ξ₁
  let := CurveModel.OpenKummer.kummerGeometricRootAction_commutes M
    (M.openBoundaryPlaces j₁) n ws j₁ hj₁ (M.place_not_mem_openBoundaryPlaces j₁) hn ξ₁
  intro α hI hres
  let c := fun p => (boundaryPlaceInertiaHom M j₁ hj₁ hfield₁ Q₁ (e p)).toMonoidHom
  refine exists_coverTransport_equiv_namedKummerPower M j₂ hj₂ hfield₂ Q₂
    n hn hg wt Fs U i₀ α c ?_ ?_ ?_
    (finiteResidue M n j₂ hj₂ hn ξ₂ yt) rfl ?_
  · intro p
    exact boundaryPlaceInertiaHom_injective M j₁ hj₁ hfield₁ Q₁ (e p)
  · intro p
    obtain ⟨a, ha⟩ := hI p
    rw [← boundaryPlaceInertiaLift_range M j₁ hj₁ hfield₁ Q₁ (e p),
      ← boundaryPlaceInertiaLift_range M j₂ hj₂ hfield₂ Q₂ p] at ha
    exact abelianized_ranges_of_conjugate_inertia
      (boundaryPlaceInertiaLift M j₁ hj₁ hfield₁ Q₁ (e p)).toMonoidHom
      (boundaryPlaceInertiaLift M j₂ hj₂ hfield₂ Q₂ p).toMonoidHom α a ha
  · intro v hv
    apply boundary_diagonal_relations_reindex e
      (fun p t => boundaryPlaceInertiaHom M j₁ hj₁ hfield₁ Q₁ p t) ?_ v hv
    intro v hv
    apply (boundaryInertiaMap_eq_one_iff M j₁ hj₁ hfield₁ Q₁ v).mp
    change Finset.univ.noncommProd
      (fun p => boundaryPlaceInertiaHom M j₁ hj₁ hfield₁ Q₁ p (v p))
      (fun _ _ _ _ _ => Commute.all _ _) = 1
    simpa only [Finset.noncommProd_eq_prod] using hv
  · intro z p t
    have hv := namedKummer_torsor_boundary_values M j₁ hj₁ hfield₁ Q₁
      n hn ws z (e p) t
    let r : rootsOfUnity (n : ℕ) K :=
      (primeToRootsSystem K K).projection ⟨n.val, hn⟩ t
    change torsorAbelianCharacter z (c p t) = r ^
        (finiteResidue M n j₂ hj₂ hn ξ₂ yt p).val
    rw [hres p]
    exact hv

end AnabelianGeometry.WeightFiltration
