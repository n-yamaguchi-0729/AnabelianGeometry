/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.NamedKummerFiberRigidity
import Nyll.AnabelianGeometry.CuspidalInertia.CoverTransportBoundaryPower
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaCoordinateSeparation

/-! # Actual cover transport identified with named power Kummer fibers -/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian
open scoped FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (SchemeTheory.normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]

/-- A genuine transported cover torsor is identified with the named power
Kummer cover. Local source values and matching numeric target residues are
inputs; the common power, global character equality and fiber equivalence
are constructed. For a source Kummer cover, its local-value input is supplied
by its actual finite cohomology character and BoundaryInertiaValues. -/
theorem exists_coverTransport_equiv_namedKummerPower
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (hg : genusFF K F = 0)
    (w : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n)
    {C : Type*} [Category C] [GaloisCategory C]
    (Fs : C ⥤ FintypeCat) [FiberFunctor Fs] (U : C)
    [Torsor (rootsOfUnity (n : ℕ) K) (Fs.obj U)]
    [SMulCommClass (Aut Fs) (rootsOfUnity (n : ℕ) K) (Fs.obj U)]
    [Fintype (M.openBoundaryPlaces j)] [Nontrivial (M.openBoundaryPlaces j)]
    (i₀ : M.openBoundaryPlaces j) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    letI : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let Ft := FiniteEtale.fiber ξ
    let y := CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n w j hj
      (M.place_not_mem_openBoundaryPlaces j) hn ξ
    let b := fun p => (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom
    ∀ (α : Aut Fs ≃ₜ* Aut Ft)
      (c : M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit →*
        TopologicalAbelianization (Aut Fs)),
      (∀ p, Function.Injective (c p)) →
      (∀ p, (b p).range.map (TopologicalAbelianization.congr α.symm).toMulEquiv.toMonoidHom =
        (c p).range) →
      (∀ t : M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit,
        (∏ p, c p (t p)) = 1 → ∀ p r, t p = t r) →
      ∀ (a : M.openBoundaryPlaces j → ZMod (n : ℕ)),
      finiteResidue M n j hj hn ξ y = a →
      (∀ (s : Fs.obj U) p t,
        let r : rootsOfUnity (n : ℕ) K :=
          (primeToRootsSystem K K).projection ⟨n.val, hn⟩ t
        torsorAbelianCharacter (G := Aut Fs) s (c p t) = r ^ (a p).val) →
      let e := coverTransportFiberEquiv Fs Ft α U
      let he := coverTransportFiberEquiv_smul Fs Ft α U
      letI := transportedFiberTorsor e
      letI := transportedFiberSMulCommClass α.toMulEquiv e he
      ∃ u : (ZMod (n : ℕ))ˣ,
        let W := M.openKummerCover (M.openBoundaryPlaces j) n hn
          (w ^ (u : ZMod (n : ℕ)).val) j hj (M.place_not_mem_openBoundaryPlaces j)
        letI := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces j)
          n (w ^ (u : ZMod (n : ℕ)).val) j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
        ∃ f : Ft.obj ((coverTransportOfAutEquiv Fs Ft α).functor.obj U) ≃ Ft.obj W,
          (∀ (z : rootsOfUnity (n : ℕ) K) x, f (z • x) = z • f x) ∧
          ∀ (g : Aut Ft) x, f (g • x) = g • f x := by
  intro nn topology η ξ Ft y b α c hc hrange hrelations a hres hsource
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let e := coverTransportFiberEquiv Fs Ft α U
  let he := coverTransportFiberEquiv_smul Fs Ft α U
  let := transportedFiberTorsor e
  let := transportedFiberSMulCommClass α.toMulEquiv e he
  have hb (p : M.openBoundaryPlaces j) : Function.Injective (b p) :=
    boundaryPlaceInertiaHom_injective M j hj hfield Q p
  have hconstant (t : (primeToRootsSystem K K).inverseLimit) : (∏ p, b p t) = 1 := by
    have h := boundaryInertiaMap_constant_eq_one M j hj hfield Q t
    change Finset.univ.noncommProd (fun p => b p t)
      (fun _ _ _ _ _ => Commute.all _ _) = 1 at h
    simpa only [Finset.noncommProd_eq_prod] using h
  obtain ⟨u, hu⟩ := coverTransport_torsor_boundary_power Fs Ft α U K
    (⟨n.val, hn⟩ : InvertibleExponent K) b c hb hc hrange hconstant hrelations i₀
  refine ⟨u, ?_⟩
  let P := Ft.obj ((coverTransportOfAutEquiv Fs Ft α).functor.obj U)
  let q₀ : P := e.symm (Classical.choice (inferInstance : Nonempty (Fs.obj U)))
  apply exists_equivariant_equiv_namedKummerPower_of_boundary_values M j hj hfield Q
    n hn hg w (u : ZMod (n : ℕ)).val P q₀
  intro p t
  have hs := hsource (e q₀) p t
  have ht := boundaryPlaceInertiaHom_h1Value M j hj hfield Q n hn p y t
  let r : rootsOfUnity (n : ℕ) K :=
    (primeToRootsSystem K K).projection ⟨n.val, hn⟩ t
  change h1AbelianCharacter (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))
    ξ y (boundaryPlaceInertiaHom M j hj hfield Q p t) =
      r ^ (finiteResidue M n j hj hn ξ y p).val at ht
  have hp : finiteResidue M n j hj hn ξ y p = a p :=
    congrArg (fun v : M.openBoundaryPlaces j → ZMod (n : ℕ) => v p) hres
  rw [hp] at ht
  exact (hu q₀ p t).trans (congrArg (fun z => z ^ (u : ZMod (n : ℕ)).val)
    (hs.trans ht.symm))

end AnabelianGeometry.WeightFiltration
