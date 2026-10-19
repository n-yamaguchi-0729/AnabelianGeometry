/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.IntrinsicBoundaryWeight
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Common arithmetic lifts for intrinsic cyclotomic spans -/

noncomputable section

open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

private theorem candidate_normalizer_isClosed
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    (J : ClosedSubgroup P) : IsClosed ((Subgroup.normalizer (J : Set P)) : Set P) := by
  have heq : ((Subgroup.normalizer (J : Set P)) : Set P) =
      (⋂ x : J, {g : P | g * (x : P) * g⁻¹ ∈ J}) ∩
      (⋂ x : J, {g : P | g⁻¹ * (x : P) * g ∈ J}) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro hg
      refine ⟨?_, ?_⟩
      · intro x
        exact (Subgroup.mem_set_normalizer_iff.mp hg (x : P)).mp x.property
      · intro x
        have hginv : g⁻¹ ∈ Subgroup.normalizer (J : Set P) :=
          (Subgroup.normalizer (J : Set P)).inv_mem hg
        change g⁻¹ * (x : P) * g ∈ (J : Set P)
        simpa only [inv_inv] using
          (Subgroup.mem_set_normalizer_iff.mp hginv (x : P)).mp x.property
    · rintro ⟨h, hi⟩
      apply Subgroup.mem_set_normalizer_iff.mpr
      intro x
      constructor
      · intro hx
        exact h ⟨x, hx⟩
      · intro hx
        have hx' := hi ⟨g * x * g⁻¹, hx⟩
        simpa [mul_assoc] using hx'
  rw [heq]
  exact (isClosed_iInter fun x => J.isClosed'.preimage
    ((continuous_id.mul continuous_const).mul continuous_inv)).inter
    (isClosed_iInter fun x => J.isClosed'.preimage
      ((continuous_inv.mul continuous_const).mul continuous_id))

/-- The candidate normalizer has open Galois image by the cyclotomic-type
hypothesis. Intersecting with an actual open arithmetic cover image still
has open image, and every element has a lift satisfying BOTH conditions. -/
theorem exists_open_commonLift_in_cover_and_normalizer
    {P Gamma : Type*}
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
    [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
    [CompactSpace Gamma] [T2Space Gamma]
    (p : P →ₜ* Gamma) (J : ClosedSubgroup P) (H : OpenSubgroup P)
    (hN : IsOpen (((Subgroup.normalizer (J : Set P)).map p.toMonoidHom : Subgroup Gamma) :
      Set Gamma)) :
    ∃ K : OpenSubgroup Gamma, ∀ sigma ∈ K,
      ∃ gamma : P, gamma ∈ H ∧ gamma ∈ (Subgroup.normalizer (J : Set P)) ∧ p gamma = sigma := by
  let N : ClosedSubgroup P :=
    ⟨(Subgroup.normalizer (J : Set P)), candidate_normalizer_isClosed J⟩
  let D : OpenSubgroup Gamma :=
    ⟨(Subgroup.normalizer (J : Set P)).map p.toMonoidHom, hN⟩
  let : CompactSpace N := isCompact_iff_compactSpace.mp N.isClosed'.isCompact
  let : CompactSpace D := isCompact_iff_compactSpace.mp D.isClosed.isCompact
  let : IsTopologicalGroup N :=
    inferInstanceAs (IsTopologicalGroup (Subgroup.normalizer (J : Set P)))
  let : IsTopologicalGroup D :=
    inferInstanceAs
      (IsTopologicalGroup ((Subgroup.normalizer (J : Set P)).map p.toMonoidHom))
  let q : N →* D :=
    { toFun := fun n => ⟨p (n : P), ⟨(n : P), n.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one p)
      map_mul' := fun x y => Subtype.ext (map_mul p (x : P) (y : P)) }
  have hq : Function.Surjective q := by
    intro d
    obtain ⟨n, hn, hnd⟩ := d.property
    exact ⟨⟨n, hn⟩, Subtype.ext hnd⟩
  have hqc : Continuous q :=
    (p.continuous.comp continuous_subtype_val).subtype_mk _
  have hqo : IsOpenMap q := q.isOpenMap_of_sigmaCompact hq hqc
  let B : OpenSubgroup N := H.comap (N : Subgroup P).subtype continuous_subtype_val
  have hB : IsOpen (((B : Subgroup N).map q : Subgroup D) : Set D) :=
    hqo _ B.isOpen
  let K : OpenSubgroup Gamma :=
    { toSubgroup := ((B : Subgroup N).map q).map (D : Subgroup Gamma).subtype
      isOpen' := D.isOpen.isOpenMap_subtype_val _ hB }
  refine ⟨K, ?_⟩
  intro sigma hsigma
  obtain ⟨d, hd, hdsigma⟩ := hsigma
  obtain ⟨n, hn, hnd⟩ := hd
  refine ⟨n.val, hn, n.property, ?_⟩
  exact (congrArg Subtype.val hnd).trans hdsigma

/-- The same common lift proves open equivariance of the candidate image
in the actual cover's abelianization. `haction` is the literal conjugation
comparison supplied by recoveredCover_stabilizerEquiv_arithmeticAction,
after transporting its geometric group through its given equivalence.
It is NOT a preservation or htest hypothesis. -/
theorem candidate_image_mem_openCyclotomicSpan_of_actual_conjugation
    {P Gamma V R : Type*}
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
    [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
    [CompactSpace Gamma] [T2Space Gamma]
    [Group V] [TopologicalSpace V] [IsTopologicalGroup V]
    [Group R]
    (p : P →ₜ* Gamma) (J : ClosedSubgroup P) (H : OpenSubgroup P)
    (hN : IsOpen (((Subgroup.normalizer (J : Set P)).map p.toMonoidHom : Subgroup Gamma) :
      Set Gamma))
    (i : V →* P) (hi : Function.Injective i)
    (psi : R →* V)
    (a : Gamma → R → R)
    (rho : Gamma → TopologicalAbelianization V → TopologicalAbelianization V)
    (hcycl : ∀ gamma ∈ (Subgroup.normalizer (J : Set P)), ∀ t,
      i (psi (a (p gamma) t)) = gamma * i (psi t) * gamma⁻¹)
    (haction : ∀ gamma ∈ H, ∀ v : V, ∃ v' : V,
      rho (p gamma) (TopologicalAbelianization.mk V v) =
        TopologicalAbelianization.mk V v' ∧
      i v' = gamma * i v * gamma⁻¹)
    (t : R) :
    TopologicalAbelianization.mk V (psi t) ∈ openCyclotomicSpan a rho := by
  obtain ⟨K, hK⟩ := exists_open_commonLift_in_cover_and_normalizer p J H hN
  let phi : R →* TopologicalAbelianization V :=
    (TopologicalAbelianization.mk V).comp psi
  have heq : ∀ sigma ∈ K, ∀ r, phi (a sigma r) = rho sigma (phi r) := by
    intro sigma hsigma r
    obtain ⟨gamma, hgammaH, hgammaN, hgamma⟩ := hK sigma hsigma
    obtain ⟨v', hv', hiv'⟩ := haction gamma hgammaH (psi r)
    have hpsi : psi (a (p gamma) r) = v' :=
      hi ((hcycl gamma hgammaN r).trans hiv'.symm)
    subst sigma
    change TopologicalAbelianization.mk V (psi (a (p gamma) r)) = _
    rw [hpsi]
    exact hv'.symm
  have hrange : phi.range ≤ openCyclotomicSpan a rho :=
    le_iSup_of_le K (le_iSup_of_le phi (le_iSup_of_le heq le_rfl))
  exact hrange ⟨t, rfl⟩

end AnabelianGeometry.WeightFiltration
