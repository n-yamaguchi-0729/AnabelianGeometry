/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.MvPolynomial.Funext
public import Nyll.SchemeTheory.RingTheory.Smooth.Charts

/-! # Finite étale fibers and separable points on smooth schemes -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.EtaleNeighborhoods

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

universe u

namespace FiniteEtale
open _root_.AlgebraicGeometry

theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h₁ : RingHom.FormallyUnramified (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @FormallyUnramified) f inferInstance U V e
  have h₂ : RingHom.FiniteType (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  rw [RingHom.QuasiFinite]
  have : Algebra.EssFiniteType Γ(Y, U) Γ(X, V) :=
    Algebra.EssFiniteType.of_finiteType _ _
  infer_instance

theorem isFinite_of_etale {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Etale f] [QuasiCompact f] : IsFinite f := by
  have hlqf : LocallyQuasiFinite f := locallyQuasiFinite_of_formallyUnramified f
  have hArt : IsLocallyArtinian (Spec (CommRingCat.of k)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr (inferInstanceAs (IsArtinianRing k))
  exact IsFinite.of_locallyQuasiFinite f

end FiniteEtale

end SchemeTheory.EtaleNeighborhoods
namespace AlgebraicGeometry
universe u
open CategoryTheory CategoryTheory.Limits
open SchemeTheory.EtaleNeighborhoods.FiniteEtale in
theorem IsFinite.of_smoothOfRelativeDimension_zero_of_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 0 f] [QuasiCompact f] : IsFinite f := by
  have hEt : Etale f := (Etale.iff_smoothOfRelativeDimension_zero (f := f)).mpr inferInstance
  exact isFinite_of_etale f

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.EtaleNeighborhoods

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace SeparablePoints

open _root_.Algebra

lemma exists_algHom_of_perfectField (K : Type u) [Field K] [PerfectField K]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
    (p : Ideal S) (hp : p ≠ ⊤) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K') (_ : S →ₐ[K] K'), True := by
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal p hp
  let : Field (S ⧸ M) := Ideal.Quotient.field M
  have : Algebra.FiniteType K (S ⧸ M) := inferInstance
  have : Module.Finite K (S ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (S ⧸ M)
  have : Algebra.IsAlgebraic K (S ⧸ M) := Algebra.IsAlgebraic.of_finite K (S ⧸ M)
  have : Algebra.IsSeparable K (S ⧸ M) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨S ⧸ M, inferInstance, inferInstance, inferInstance, inferInstance,
    Ideal.Quotient.mkₐ K M, trivial⟩

lemma exists_eval_ne_zero {K : Type u} [Field K] [Infinite K] {n : ℕ}
    {h : MvPolynomial (Fin n) K} (hh : h ≠ 0) :
    ∃ a : Fin n → K, MvPolynomial.eval a h ≠ 0 := by
  by_contra! H
  exact hh (MvPolynomial.funext fun a => by simpa only [map_zero] using H a)

lemma exists_isMaximal_isSeparable_of_etale (K : Type u) [Field K] [Infinite K] (n : ℕ)
    (Sf : Type u) [CommRing Sf] [Algebra K Sf]
    [Algebra (MvPolynomial (Fin n) K) Sf] [IsScalarTower K (MvPolynomial (Fin n) K) Sf]
    [Algebra.Etale (MvPolynomial (Fin n) K) Sf] (Q₀ : Ideal Sf) [Q₀.IsPrime] :
    ∃ (M : Ideal Sf) (_ : M.IsMaximal),
      FiniteDimensional K (Sf ⧸ M) ∧ Algebra.IsSeparable K (Sf ⧸ M) := by
  classical
  have : Module.Flat (MvPolynomial (Fin n) K) Sf := inferInstance
  have : Algebra.HasGoingDown (MvPolynomial (Fin n) K) Sf := Algebra.HasGoingDown.of_flat
  have hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  have hU : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf))) :=
    hopen.isOpen_range
  let q₀ : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap (algebraMap (MvPolynomial
    (Fin n) K) Sf) ⟨Q₀, ‹_›⟩
  have hq₀ : q₀ ∈ Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf)) := ⟨_,
    rfl⟩
  obtain ⟨_, ⟨h, rfl⟩, hq₀h, hhU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq₀ hU
  have hh0 : h ≠ 0 := by
    intro H
    rw [H] at hq₀h
    change (0 : MvPolynomial (Fin n) K) ∉ q₀.asIdeal at hq₀h
    exact hq₀h (Ideal.zero_mem _)
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hh0
  let ev : (MvPolynomial (Fin n) K) →ₐ[K] K := MvPolynomial.aeval a
  have hev : Function.Surjective ev := fun x =>
    ⟨MvPolynomial.C x, by
      simp only [ev, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]⟩
  let m : Ideal (MvPolynomial (Fin n) K) := RingHom.ker ev
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective ev hev
  have hhm : h ∉ m := by
    change ev h ≠ 0
    exact ha
  have hmD : (⟨m, hm.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin n) K)) ∈ PrimeSpectrum.basicOpen
    h := hhm
  obtain ⟨Q, hQ⟩ := hhU hmD
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q.asIdeal Q.isPrime.ne_top
  have hmM : m ≤ M.comap (algebraMap (MvPolynomial (Fin n) K) Sf) := by
    have : Q.asIdeal.comap (algebraMap (MvPolynomial (Fin n) K) Sf) = m := by
      exact congrArg PrimeSpectrum.asIdeal hQ
    rw [← this]
    exact Ideal.comap_mono hQM
  let : Field (Sf ⧸ M) := Ideal.Quotient.field M
  refine ⟨M, hM, ?_, ?_⟩
  · have : Algebra.FiniteType K (MvPolynomial (Fin n) K) := inferInstance
    have : Algebra.FiniteType (MvPolynomial (Fin n) K) Sf := inferInstance
    have : Algebra.FiniteType K Sf := Algebra.FiniteType.trans (S := (MvPolynomial (Fin n) K))
      inferInstance inferInstance
    have : Algebra.FiniteType K (Sf ⧸ M) := inferInstance
    exact finite_of_finite_type_of_isJacobsonRing K (Sf ⧸ M)
  · let κ := (MvPolynomial (Fin n) K) ⧸ m
    let : Field κ := Ideal.Quotient.field m
    let : Algebra κ (Sf ⧸ M) := (Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf)
      hmM).toAlgebra
    have : IsScalarTower (MvPolynomial (Fin n) K) κ (Sf ⧸ M) := IsScalarTower.of_algebraMap_eq fun
      x => by
      change Ideal.Quotient.mk M (algebraMap (MvPolynomial (Fin n) K) Sf x) =
        Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf) hmM (Ideal.Quotient.mk m x)
      rw [Ideal.quotientMap_mk]
    have : IsScalarTower K κ (Sf ⧸ M) := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap Sf (Sf ⧸ M) (algebraMap K Sf x) =
        Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf) hmM (Ideal.Quotient.mk m
          (algebraMap K (MvPolynomial (Fin n) K) x))
      rw [Ideal.quotientMap_mk, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) Sf]
      rfl
    have : Algebra.FormallyUnramified (MvPolynomial (Fin n) K) (Sf ⧸ M) :=
      Algebra.FormallyUnramified.comp (MvPolynomial (Fin n) K) Sf (Sf ⧸ M)
    have : Algebra.FormallyUnramified κ (Sf ⧸ M) :=
      Algebra.FormallyUnramified.of_restrictScalars (MvPolynomial (Fin n) K) κ (Sf ⧸ M)
    have : Algebra.FiniteType (MvPolynomial (Fin n) K) (Sf ⧸ M) := inferInstance
    have : Algebra.FiniteType κ (Sf ⧸ M) :=
      Algebra.FiniteType.of_restrictScalars_finiteType (MvPolynomial (Fin n) K) κ (Sf ⧸ M)
    have : Algebra.EssFiniteType κ (Sf ⧸ M) := inferInstance
    have : Algebra.IsSeparable κ (Sf ⧸ M) :=
      (Algebra.FormallyUnramified.iff_isSeparable κ (Sf ⧸ M)).mp inferInstance
    let e : κ ≃ₐ[K] K := Ideal.quotientKerAlgEquivOfSurjective hev
    have : Algebra.IsSeparable K κ :=
      Algebra.IsSeparable.of_algHom K K e.toAlgHom
    exact Algebra.IsSeparable.trans K κ (Sf ⧸ M)

lemma exists_algHom_of_smooth (K : Type u) [Field K]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra.Smooth K S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K') (_ : S →ₐ[K] K'), True := by
  classical
  cases finite_or_infinite K with
  | inl hfin =>
    have : PerfectField K := inferInstance
    exact exists_algHom_of_perfectField K S p (Ideal.IsPrime.ne_top ‹_›)
  | inr hinf =>
    obtain ⟨f, hfp, n, _inst, htower, hstd⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (S := S) (p := p)
    have : IsScalarTower K (MvPolynomial (Fin n) K) (Localization.Away f) := htower
    have : Algebra.IsStandardEtale (MvPolynomial (Fin n) K) (Localization.Away f) := hstd
    have hp' : (Ideal.map (algebraMap S (Localization.Away f)) p).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
        ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfp)
    obtain ⟨M, hM, hfinM, hsepM⟩ := exists_isMaximal_isSeparable_of_etale K n
      (Localization.Away f) (Ideal.map (algebraMap S (Localization.Away f)) p)
    let : Field (Localization.Away f ⧸ M) := Ideal.Quotient.field M
    exact ⟨Localization.Away f ⧸ M, inferInstance, inferInstance, hfinM, hsepM,
      (Ideal.Quotient.mkₐ K M).comp (IsScalarTower.toAlgHom K S (Localization.Away f)), trivial⟩

end SeparablePoints

end SchemeTheory.EtaleNeighborhoods
namespace AlgebraicGeometry
universe u
open CategoryTheory CategoryTheory.Limits
open SchemeTheory.EtaleNeighborhoods
theorem exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty
    (K : Type u) [Field K] {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of K)) [Smooth g]
    [Nonempty V] :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K') (P : Spec (CommRingCat.of K') ⟶ V),
      P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K K')) := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hU.fromSpec ≫ g)
  have smoothComp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) [Smooth a] [Smooth b] :
      Smooth (a ≫ b) := inferInstance
  have openSmooth {X Y : Scheme.{u}} (a : X ⟶ Y) [IsOpenImmersion a] :
      Smooth a := inferInstance
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : Smooth hU.fromSpec := openSmooth hU.fromSpec
  have hcomp : Smooth (hU.fromSpec ≫ g) := smoothComp hU.fromSpec g
  have hsm : Smooth (Spec.map ψ) := hψ.symm ▸ hcomp
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hsm
  algebraize [ψ.hom]
  obtain ⟨x, -⟩ : ∃ x : Spec Γ(V, U), hU.fromSpec.base x = v := by
    have : v ∈ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hvU
    exact this
  have : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨K', _, _, _, _, χ, -⟩ :=
    SeparablePoints.exists_algHom_of_smooth K Γ(V, U) x.asIdeal
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec, ?_⟩
  rw [Category.assoc, ← hψ, ← Spec.map_comp]
  congr 1
  ext1
  change χ.toRingHom.comp ψ.hom = algebraMap K K'
  exact χ.comp_algebraMap

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_etale_opensInclusion_comp_of_formallyUnramified_stalkMap_of_smoothOfRelativeDimension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.EtaleNeighborhoods

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace UnramifiedCharts

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma appLE_comp_algebraMap_basicOpen {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (r : Γ(X, V)) :
    (algebraMap Γ(X, V) Γ(X, X.basicOpen r)).comp (f.appLE U V e).hom =
      (f.appLE U (X.basicOpen r) ((X.basicOpen_le r).trans e)).hom := by
  rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

lemma mem_basicOpen_of_not_mem {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hx : x ∈ V)
    (r : Γ(X, V)) (hr : r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ X.basicOpen r := by
  let xV : (V : Scheme.{u}) := ⟨x, hx⟩
  let z : Spec Γ(X, V) := hV.isoSpec.hom xV
  have hz : z ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r := by
    rw [hV.fromSpec_preimage_basicOpen]
    exact hr
  have hzX : hV.fromSpec z = x :=
    congrArg (fun a : (V : Scheme.{u}) ⟶ X => a xV) hV.isoSpec_hom_fromSpec
  have hz' : hV.fromSpec z ∈ X.basicOpen r := hz
  exact hzX ▸ hz'

lemma isUnramifiedAt_of_formallyUnramified_stalkMap {x : X} (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V)
    (H : (f.stalkMap x).hom.FormallyUnramified) :
    let _ : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  intro algUV
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have h1 : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)).mp H
  have h2 : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime p) :=
    .of_isLocalization p.primeCompl
  exact Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p) (Localization.AtPrime q)

lemma exists_basicOpen_formallyUnramified_appLE [LocallyOfFiniteType f] {x : X} (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V)
    (H : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ r : Γ(X, V), x ∈ X.basicOpen r ∧
      (f.appLE U (X.basicOpen r) ((X.basicOpen_le r).trans hVU)).hom.FormallyUnramified := by
  have := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    isUnramifiedAt_of_formallyUnramified_stalkMap f U hU V hV hVU hx H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  refine ⟨r, mem_basicOpen_of_not_mem hV hx r hrx, ?_⟩
  have := hV.isLocalization_basicOpen r
  rw [← RingHom.formallyUnramified_algebraMap] at hr
  rw [← appLE_comp_algebraMap_basicOpen f hVU r]
  convert RingHom.FormallyUnramified.respectsIso.1 _
      (IsLocalization.algEquiv (.powers r) (Localization.Away r) Γ(X, X.basicOpen r)).toRingEquiv hr
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe,
    IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization.Away r), AlgEquiv.commutes,
    RingHom.algebraMap_toAlgebra]

end UnramifiedCharts

end SchemeTheory.EtaleNeighborhoods
namespace AlgebraicGeometry
universe u
open CategoryTheory CategoryTheory.Limits
open SchemeTheory.EtaleNeighborhoods.UnramifiedCharts in
theorem exists_etale_opensInclusion_comp_of_formallyUnramified_stalkMap_of_smoothOfRelativeDimension
    {k : Type u} [Field k] {X Y : Scheme.{u}} (n : ℕ)
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension n fY]
    (φ : X ⟶ Y) (hφ : φ ≫ fY = fX) (x : X) (hx : (φ.stalkMap x).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ φ) := by
  subst hφ
  have hsY : Smooth fY := SmoothOfRelativeDimension.smooth n fY
  have hsX : Smooth (φ ≫ fY) := SmoothOfRelativeDimension.smooth n (φ ≫ fY)
  have : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ fY
  obtain ⟨U', hU', U₂, hU₂, hxU₂, e₂, hS⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := fY) (φ x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) hxU₂ (U₂.2.preimage φ.continuous)
  obtain ⟨r, hxr, hur⟩ := exists_basicOpen_formallyUnramified_appLE φ U₂ hU₂ V hV hVU hxV hx
  have hV₃ : IsAffineOpen (X.basicOpen r) := hV.basicOpen r
  have e₃ : X.basicOpen r ≤ (φ ≫ fY) ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]
    exact ((X.basicOpen_le r).trans hVU).trans (Scheme.Hom.preimage_mono φ e₂)
  have hloc := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) (φ ≫ fY) inferInstance
    ⟨U', hU'⟩ ⟨X.basicOpen r, hV₃⟩ e₃
  obtain ⟨s, hs, hsP⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).mp hloc
  obtain ⟨t, hts, htx⟩ : ∃ t ∈ s, t ∉ (hV₃.primeIdealOf ⟨x, hxr⟩).asIdeal := by
    by_contra! h
    have : Ideal.span (↑s : Set Γ(X, X.basicOpen r)) ≤ (hV₃.primeIdealOf ⟨x, hxr⟩).asIdeal :=
      Ideal.span_le.mpr h
    rw [hs, top_le_iff] at this
    exact (hV₃.primeIdealOf ⟨x, hxr⟩).isPrime.ne_top this
  have hxt : x ∈ X.basicOpen t := mem_basicOpen_of_not_mem hV₃ hxr t htx
  have hV₄ : IsAffineOpen (X.basicOpen t) := hV₃.basicOpen t
  have : IsLocalization.Away t Γ(X, X.basicOpen t) := hV₃.isLocalization_basicOpen t
  have hT : (((φ ≫ fY).appLE U' (X.basicOpen t) ((X.basicOpen_le t).trans e₃)).hom)
      |>.IsStandardSmoothOfRelativeDimension n := by
    rw [← appLE_comp_algebraMap_basicOpen]
    exact hsP t hts _
  have e₄ : X.basicOpen t ≤ φ ⁻¹ᵁ U₂ := (X.basicOpen_le t).trans ((X.basicOpen_le r).trans hVU)
  have hU4 : (φ.appLE U₂ (X.basicOpen t) e₄).hom.FormallyUnramified := by
    rw [← appLE_comp_algebraMap_basicOpen φ ((X.basicOpen_le r).trans hVU) t]
    exact RingHom.FormallyUnramified.stableUnderComposition _ _ hur
      (RingHom.formallyUnramified_algebraMap.mpr (.of_isLocalization (.powers t)))
  have hEt : (φ.appLE U₂ (X.basicOpen t) e₄).hom.Etale := by
    algebraize [(fY.appLE U' U₂ e₂).hom, (φ.appLE U₂ (X.basicOpen t) e₄).hom,
      ((φ ≫ fY).appLE U' (X.basicOpen t) ((X.basicOpen_le t).trans e₃)).hom]
    have : IsScalarTower Γ(Spec (CommRingCat.of k), U') Γ(Y, U₂) Γ(X, X.basicOpen t) :=
      IsScalarTower.of_algebraMap_eq' (by
        simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
          Scheme.Hom.appLE_comp_appLE])
    exact Algebra.Etale.of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
      (R := Γ(Spec (CommRingCat.of k), U')) n
  refine ⟨X.basicOpen t, hxt, ?_⟩
  have : Etale (φ.resLE U₂ (X.basicOpen t) e₄) := by
    have : IsAffine _ := hU₂
    have : IsAffine _ := hV₄
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
    exact (RingHom.Etale.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso φ U₂ (X.basicOpen t) e₄)).mpr hEt
  rw [← Scheme.Hom.resLE_comp_ι φ e₄]
  infer_instance

end AlgebraicGeometry
end
