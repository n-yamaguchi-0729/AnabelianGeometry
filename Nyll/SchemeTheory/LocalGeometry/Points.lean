/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Tactic.Push
public import Nyll.SchemeTheory.LocalGeometry.DenseAlgebraicallyClosedSections

/-!
# Closed points, constructible images and geometric surjectivity
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace GeometricPointLifting
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
        [Surjective f]
    (y : Spec (.of K) ⟶ Y) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ f = y := by
  have hne : Nonempty ↑(pullback f y) := by
    obtain ⟨z, -⟩ := (pullback.snd f y).surjective (IsLocalRing.closedPoint K)
    exact ⟨z⟩
  obtain ⟨-, s, hs, -⟩ :=
    (AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed (pullback.snd f y)).nonempty
  exact ⟨s ≫ pullback.fst f y, by rw [Category.assoc, pullback.condition, reassoc_of% hs]⟩

end GeometricPointLifting
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_surjective_of_closedPoints_subset_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace ClosedPointSurjectivity
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Topology

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace SurjClosedPoints
open _root_.AlgebraicGeometry

section TopLemmas

variable {X : Type*} [TopologicalSpace X]

/-- A finite union of locally closed subsets. -/
def FinLC (s : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧ (∀ z ∈ S, IsLocallyClosed z) ∧ s = ⋃₀ S

theorem FinLC.of_isLocallyClosed {s : Set X} (hs : IsLocallyClosed s) : FinLC s :=
  ⟨{s}, Set.finite_singleton s, (by
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact hs), (Set.sUnion_singleton s).symm⟩

theorem FinLC.union {s t : Set X} (hs : FinLC s) (ht : FinLC t) : FinLC (s ∪ t) := by
  obtain ⟨S, hSf, hSl, rfl⟩ := hs
  obtain ⟨T, hTf, hTl, rfl⟩ := ht
  refine ⟨S ∪ T, hSf.union hTf, ?_, (Set.sUnion_union S T).symm⟩
  rintro z (hz | hz)
  exacts [hSl z hz, hTl z hz]

theorem FinLC.inter {s t : Set X} (hs : FinLC s) (ht : FinLC t) : FinLC (s ∩ t) := by
  obtain ⟨S, hSf, hSl, rfl⟩ := hs
  obtain ⟨T, hTf, hTl, rfl⟩ := ht
  refine ⟨Set.image2 (· ∩ ·) S T, hSf.image2 _ hTf, ?_, ?_⟩
  · rintro z ⟨a, ha, b, hb, rfl⟩
    exact (hSl a ha).inter (hTl b hb)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_image2,
        exists_exists_and_exists_and_eq_and]
    constructor
    · rintro ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
      exact ⟨a, ha, b, hb, hxa, hxb⟩
    · rintro ⟨a, ha, b, hb, hxa, hxb⟩
      exact ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩

theorem finLC_and_compl_of_isConstructible {s : Set X} (hs : IsConstructible s) :
    FinLC s ∧ FinLC sᶜ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    exact ⟨.of_isLocallyClosed hU.isLocallyClosed, .of_isLocallyClosed
        hU.isClosed_compl.isLocallyClosed⟩
  | union s _ t _ hs ht =>
    refine ⟨hs.1.union ht.1, ?_⟩
    rw [Set.compl_union]
    exact hs.2.inter ht.2
  | compl s _ hs =>
    rw [compl_compl]
    exact ⟨hs.2, hs.1⟩

theorem nonempty_inter_closedPoints_of_isConstructible [JacobsonSpace X] {s : Set X}
    (hs : IsConstructible s) (hne : s.Nonempty) : (s ∩ closedPoints X).Nonempty := by
  obtain ⟨S, -, hSl, rfl⟩ := (finLC_and_compl_of_isConstructible hs).1
  obtain ⟨x, z, hz, hxz⟩ := hne
  obtain ⟨y, hyz, hyc⟩ := nonempty_inter_closedPoints ⟨x, hxz⟩ (hSl z hz)
  exact ⟨y, ⟨z, hz, hyz⟩, hyc⟩

theorem nonempty_inter_closedPoints_of_isLocallyConstructible [JacobsonSpace X] {s : Set X}
    (hs : IsLocallyConstructible s) (hne : s.Nonempty) : (s ∩ closedPoints X).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hUx, hUo, hUc⟩ := hs x
  have : JacobsonSpace U := .of_isOpenEmbedding hUo.isOpenEmbedding_subtypeVal
  have hxU : x ∈ U := mem_of_mem_nhds hUx
  obtain ⟨y, hys, hyc⟩ :=
    nonempty_inter_closedPoints_of_isConstructible hUc ⟨⟨x, hxU⟩, show (⟨x, hxU⟩ : U).1 ∈ s from hx⟩
  refine ⟨y.1, hys, ?_⟩
  have := hUo.isOpenEmbedding_subtypeVal.preimage_closedPoints (X := U) (Y := X)
  rw [← this] at hyc
  exact hyc

end TopLemmas

theorem isLocallyConstructible_compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsLocallyConstructible s) : IsLocallyConstructible sᶜ := by
  intro x
  obtain ⟨U, hUx, hUo, hUc⟩ := hs x
  refine ⟨U, hUx, hUo, ?_⟩
  have e : (Subtype.val ⁻¹' sᶜ : Set U) = (Subtype.val ⁻¹' s : Set U)ᶜ := rfl
  rw [e]
  exact hUc.compl

theorem surjective_of_closedPoints_subset_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f.base) : Surjective f := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hlc : IsLocallyConstructible (Set.range f.base) := by
    simpa only [Set.image_univ] using
      f.isLocallyConstructible_image (s := Set.univ) IsLocallyConstructible.univ
  have hne : ((Set.range f.base)ᶜ).Nonempty := ⟨y, hy⟩
  obtain ⟨z, hz, hzc⟩ :=
    nonempty_inter_closedPoints_of_isLocallyConstructible (isLocallyConstructible_compl hlc) hne
  exact hz (h hzc)

end AlgebraicGeometry.SurjClosedPoints

open AlgebraicGeometry.SurjClosedPoints in
theorem _root_.AlgebraicGeometry.surjective_of_closedPoints_subset_range {X Y : Scheme.{u}} (f : X
    ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f.base) : Surjective f :=
  AlgebraicGeometry.SurjClosedPoints.surjective_of_closedPoints_subset_range f h

end ClosedPointSurjectivity
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace OpenMaximalSpectrum
open scoped TensorProduct

universe u v w

theorem _root_.PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
    {A : Type u} [CommRing A] [IsJacobsonRing A]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hne : U.Nonempty)
    (htrans : ∀ P Q : PrimeSpectrum A, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal → P ∈ U → Q ∈ U) :
    U = Set.univ := by
  classical
  obtain ⟨P, hP⟩ := hne
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp (isClosed_compl_iff.mpr hU)
  have hPnot : ¬ (s ⊆ (P.asIdeal : Set A)) := by
    intro h
    have : P ∈ Uᶜ := by rw [hs]; exact (PrimeSpectrum.mem_zeroLocus _ _).mpr h
    exact this hP
  rw [Set.not_subset] at hPnot
  obtain ⟨f, hfs, hfP⟩ := hPnot
  have hfrad : f ∉ (⊥ : Ideal A).radical := fun h => hfP (by
    have h' : f ∈ nilradical A := h
    exact nilradical_le_prime P.asIdeal h')
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Submodule.mem_sInf] at hfrad
  push Not at hfrad
  obtain ⟨M, ⟨-, hM⟩, hfM⟩ := hfrad
  have hMU : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ U := by
    by_contra h
    have h' : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ Uᶜ := h
    rw [hs, PrimeSpectrum.mem_zeroLocus] at h'
    exact hfM (h' hfs)
  apply Set.eq_univ_of_forall
  intro Q
  by_contra hQ
  have hQz : s ⊆ (Q.asIdeal : Set A) := by
    have h' : Q ∈ Uᶜ := hQ
    rw [hs, PrimeSpectrum.mem_zeroLocus] at h'
    exact h'
  obtain ⟨M', hM', hQM'⟩ := Q.asIdeal.exists_le_maximal Q.isPrime.ne_top
  have hM'U : (⟨M', hM'.isPrime⟩ : PrimeSpectrum A) ∈ U :=
    htrans ⟨M, hM.isPrime⟩ ⟨M', hM'.isPrime⟩ hM hM' hMU
  have hM'c : (⟨M', hM'.isPrime⟩ : PrimeSpectrum A) ∈ Uᶜ := by
    rw [hs, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    exact hQM' (hQz ha)
  exact hM'c hM'U

end OpenMaximalSpectrum
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace ConstructibleSpecialization
open Topology

universe u

theorem _root_.Topology.IsConstructible.mem_of_mem_closure_of_forall_specializes
    {X : Type u} [TopologicalSpace X] {s : Set X} (hs : Topology.IsConstructible s)
    {x : X} (hx : x ∈ closure s) (hgen : ∀ y ∈ s, x ⤳ y) : x ∈ s := by
  revert hx hgen
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    intro hx hgen
    have hxV : x ∉ V := fun h =>
      (closure_minimal (fun z hz => hz.2) hV.1.isClosed_compl hx) h
    obtain ⟨y, hy⟩ := closure_nonempty_iff.mp ⟨x, hx⟩
    exact ⟨(hgen y hy).mem_open hU.1 hy.1, hxV⟩
  | sup s _ t _ hs' ht' =>
    intro hx hgen
    change x ∈ closure (s ∪ t) at hx
    rw [closure_union] at hx
    rcases hx with hx | hx
    · exact Or.inl (hs' hx fun y hy => hgen y (Or.inl hy))
    · exact Or.inr (ht' hx fun y hy => hgen y (Or.inr hy))

end ConstructibleSpecialization
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace ClosedPointResidueLifting
universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem _root_.AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
    {k₀ : Type u} [Field k₀] {F : Scheme.{u}} (f : F ⟶ Spec (CommRingCat.of k₀))
        [LocallyOfFiniteType f]
    (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]
    (y : F) (hy : IsClosed ({y} : Set F)) :
    ∃ z : Spec (CommRingCat.of k) ⟶ F,
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ∧ z.base (IsLocalRing.closedPoint k) =
          y := by
  set g := F.fromSpecResidueField y ≫ f with hg
  have hfin : IsFinite g := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hy
    exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := g)).mpr inferInstance
  let φ : CommRingCat.of k₀ ⟶ F.residueField y := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hint : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ]
    infer_instance
  let : Algebra k₀ (F.residueField y) := φ.hom.toAlgebra
  have : Algebra.IsIntegral k₀ (F.residueField y) := ⟨hint⟩
  let ψ : F.residueField y →ₐ[k₀] k := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ F.fromSpecResidueField y, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← hφ, ← Spec.map_comp]
    congr 1
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
    exact ψ.commutes a
  · have hmem : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ F.fromSpecResidueField y).base
        (IsLocalRing.closedPoint k) ∈ Set.range (F.fromSpecResidueField y).base :=
      ⟨(Spec.map (CommRingCat.ofHom ψ.toRingHom)).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem

end ClosedPointResidueLifting
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_surjective_of_forall_exists_comp_eq_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace GeometricPointSurjectivity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

theorem _root_.AlgebraicGeometry.surjective_of_forall_exists_comp_eq_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (h : ∀ y : Spec (CommRingCat.of K) ⟶ Y, y ≫ g = 𝟙 _ →
      ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = y) :
    Surjective f := by
  have hJ : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace g
  have hN : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hfp : LocallyOfFinitePresentation f := inferInstance
  refine AlgebraicGeometry.surjective_of_closedPoints_subset_range f fun y hy => ?_
  obtain ⟨x, hx⟩ := h (pointOfClosedPoint g y hy) (pointOfClosedPoint_comp g y hy)
  let p : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  refine ⟨x p, ?_⟩
  calc
    f (x p) = (x ≫ f) p := (Scheme.Hom.comp_apply x f p).symm
    _ = pointOfClosedPoint g y hy p :=
      congrArg (fun φ : Spec (CommRingCat.of K) ⟶ Y => φ p) hx
    _ = y := pointOfClosedPoint_apply g y hy p

end GeometricPointSurjectivity
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace ConstructibleImageSpecialization
open CategoryTheory AlgebraicGeometry Topology

universe u

theorem _root_.AlgebraicGeometry.mem_image_of_mem_closure_image_of_forall_specializes
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {C : Set X} (hC : Topology.IsConstructible C)
    {y : Y} (hy : y ∈ closure (f.base '' C)) (hgen : ∀ c ∈ C, y ⤳ f.base c) :
    y ∈ f.base '' C :=
  (f.isConstructible_image hC).mem_of_mem_closure_of_forall_specializes hy
    (by rintro _ ⟨c, hc, rfl⟩; exact hgen c hc)

end ConstructibleImageSpecialization
end NOSProofs
end AbelianVarieties
end
