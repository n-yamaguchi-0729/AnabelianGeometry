/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.EtaleRegularity
public import Nyll.SchemeTheory.LocalGeometry.ConnectedDomainStalks
public import Nyll.SchemeTheory.Affine.ChartStalkLocalization
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Integral affine objects in the small etale site

For a Dedekind base, every small etale object is covered by integral affine
etale objects. The proof uses regularity ascent on stalks, local irreducibility,
and the affine-open basis; the resulting inclusion is cover-dense.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace EtaleCohomology

theorem isRegularAt_dedekindSpec (R : Type u) [CommRing R] [IsDedekindDomain R]
    (x : Spec (CommRingCat.of R)) :
    (Spec (CommRingCat.of R)).IsRegularAt x := by
  let X := Spec (CommRingCat.of R)
  let htop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let p := htop.primeIdealOf ⟨x, trivial⟩
  let e := htop.stalkIsoLocalization p
  let eΓ := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let : IsRegularRing Γ(X, ⊤) := IsRegularRing.of_ringEquiv eΓ.symm
  let : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := inferInstance
  have hreg : IsRegularLocalRing (X.presheaf.stalk (htop.fromSpec p)) :=
    IsRegularLocalRing.of_ringEquiv e.symm.commRingCatIsoToRingEquiv
  change IsRegularLocalRing (X.presheaf.stalk x)
  have heq : htop.fromSpec p = x := htop.fromSpec_primeIdealOf ⟨x, trivial⟩
  rw [← heq]
  exact hreg

theorem etale_isDomain_stalk_of_dedekind (R : Type u) [CommRing R] [IsDedekindDomain R]
    (V : (Spec (CommRingCat.of R)).Etale) (x : V.left) :
    IsDomain (V.left.presheaf.stalk x) := by
  have hreg := Scheme.IsRegularAt.of_etale V.hom x (isRegularAt_dedekindSpec R (V.hom x))
  exact @IsRegularLocalRing.isDomain (V.left.presheaf.stalk x) _ hreg

private theorem isReduced_of_domain (A : Type u) [CommRing A] [IsDomain A] : IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := ha
  have hp (n : ℕ) : a ^ n = 0 → a = 0 := by
    induction n with
    | zero =>
        intro h
        rw [pow_zero] at h
        exact (one_ne_zero h).elim
    | succ n ih =>
      intro h
      have hmul : a ^ n * a = 0 := by simpa [pow_succ] using h
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hmul with hpow | ha
      · exact ih hpow
      · exact ha
  exact hp n hn

theorem exists_integral_affine_etale_neighborhood (R : Type u) [CommRing R] [IsDedekindDomain R]
    (V : (Spec (CommRingCat.of R)).Etale) (x : V.left) :
    ∃ W : V.left.Opens, IsAffineOpen W ∧ x ∈ W ∧ IsIntegral (W : Scheme) := by
  let X := Spec (CommRingCat.of R)
  have hbase : IsLocallyNoetherian X := inferInstance
  have hlocal : IsLocallyNoetherian V.left :=
    @LocallyOfFiniteType.isLocallyNoetherian V.left X V.hom inferInstance hbase
  have hdom := etale_isDomain_stalk_of_dedekind R V x
  obtain ⟨P, hPopen, hxP, hPirred⟩ :=
    @Scheme.exists_isIrreducible_open_of_isDomain_stalk V.left hlocal x hdom
  let P' : V.left.Opens := ⟨P, hPopen⟩
  obtain ⟨W, hWaff, hxW, hWP⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V.left) (U := P') hxP
  have hWirredPre : IsPreirreducible (W : Set V.left) :=
    hPirred.isPreirreducible.open_subset W.isOpen hWP
  have hWirred : IsIrreducible (W : Set V.left) := ⟨⟨x, hxW⟩, hWirredPre⟩
  have hredStalk : ∀ z : V.left, _root_.IsReduced (V.left.presheaf.stalk z) := by
    intro z
    have hd := etale_isDomain_stalk_of_dedekind R V z
    exact @isReduced_of_domain _ _ hd
  have hredV : IsReduced V.left := @isReduced_of_isReduced_stalk V.left hredStalk
  have hredW : IsReduced (W : Scheme) :=
    @isReduced_of_isOpenImmersion (W : Scheme) V.left W.ι inferInstance hredV
  have hIrr : IrreducibleSpace (W : Scheme) :=
    Subtype.irreducibleSpace hWirred
  have hIntegral : IsIntegral (W : Scheme) :=
    @isIntegral_of_irreducibleSpace_of_isReduced (W : Scheme) hredW hIrr
  exact ⟨W, hWaff, hxW, hIntegral⟩


theorem exists_affine_integral_etale_cover
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (V : (Spec (CommRingCat.of R)).Etale) :
    ∃ (A : V.left → (Spec (CommRingCat.of R)).Etale)
      (l : ∀ x, A x ⟶ V),
      (∀ x, IsAffine (A x).left ∧ IsIntegral (A x).left) ∧
        Sieve.ofArrows _ l ∈ (Spec (CommRingCat.of R)).smallEtaleTopology V := by
  classical
  let W (x : V.left) : V.left.Opens :=
    Classical.choose (exists_integral_affine_etale_neighborhood R V x)
  have hW (x : V.left) : IsAffineOpen (W x) ∧ x ∈ W x ∧ IsIntegral (W x : Scheme) :=
    Classical.choose_spec (exists_integral_affine_etale_neighborhood R V x)
  let A (x : V.left) : (Spec (CommRingCat.of R)).Etale :=
    MorphismProperty.Over.mk ⊤ ((W x).ι ≫ V.hom) (by infer_instance)
  let l (x : V.left) : A x ⟶ V :=
    MorphismProperty.Over.homMk ((W x).ι) (by rfl)
  have hA (x : V.left) : IsAffine (A x).left ∧ IsIntegral (A x).left := by
    change IsAffine (W x : Scheme) ∧ IsIntegral (W x : Scheme)
    exact ⟨(hW x).1, (hW x).2.2⟩
  refine ⟨A, l, hA, ?_⟩
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext y
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  refine ⟨y, ⟨y, (hW y).2.1⟩, ?_⟩
  change (W y).ι ⟨y, (hW y).2.1⟩ = y
  rfl

/-- The full subcategory of affine objects that are integral as schemes. -/
def integralAffineEtaleObjectProperty {X : Scheme.{u}} : ObjectProperty X.Etale :=
  fun A => IsAffine A.left ∧ IsIntegral A.left

/-- The inclusion of integral affine objects into the small etale site. -/
def integralAffineEtaleInclusion (X : Scheme.{u}) :
    integralAffineEtaleObjectProperty (X := X).FullSubcategory ⥤ X.Etale :=
  integralAffineEtaleObjectProperty.ι

theorem integralAffineEtaleInclusion_isCoverDense
    (R : Type u) [CommRing R] [IsDedekindDomain R] :
    (integralAffineEtaleInclusion (Spec (CommRingCat.of R))).IsCoverDense
      (Spec (CommRingCat.of R)).smallEtaleTopology := by
  let X := Spec (CommRingCat.of R)
  let P := integralAffineEtaleObjectProperty (X := X)
  change P.ι.IsCoverDense X.smallEtaleTopology
  refine ⟨fun V => ?_⟩
  obtain ⟨A, l, hA, hc⟩ := exists_affine_integral_etale_cover R V
  apply X.smallEtaleTopology.superset_covering (R := _) ?_ hc
  intro W g hg
  obtain ⟨x, k, rfl⟩ :=
    (Sieve.mem_ofArrows_iff (fun i => P.ι.obj ⟨A i, hA i⟩) l g).mp hg
  exact ⟨⟨⟨A x, hA x⟩, k, l x, rfl⟩⟩

end EtaleCohomology
