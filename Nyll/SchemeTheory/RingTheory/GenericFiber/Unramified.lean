/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.GenericFiber.FractionRing
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Generic fibers of unramified domains

The generic fiber of a dominant, essentially finite type formally unramified
map of domains is a field. In particular, this applies to étale algebras.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uS uK uE

/-- The generic fibre of a dominant, essentially finite type unramified map
of domains is a field. No module-finiteness over the original base is required. -/
theorem genericFiber_isField_of_formallyUnramified
    (R : Type uR) (S : Type uS) (K : Type uK)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) :
    IsField (K ⊗[R] S) := by
  let M : Submonoid S :=
    Algebra.algebraMapSubmonoid S (nonZeroDivisors R)
  have hM : M ≤ nonZeroDivisors S := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr)
      (hinj (h.trans (map_zero _).symm))
  let : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization M (K ⊗[R] S) :=
    IsLocalization.tensorRight (R := R) (S := S) (A := K) (nonZeroDivisors R)
  have : IsDomain (K ⊗[R] S) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[R] S) hM
  have : Module.Finite K (K ⊗[R] S) :=
    Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  have : IsArtinianRing (K ⊗[R] S) := IsArtinianRing.of_finite K _
  exact IsArtinianRing.isField_of_isDomain (K ⊗[R] S)

/-- The generic fibre of an étale domain over a domain is a field. -/
theorem genericFiber_isField_of_etale
    (R : Type uR) (S : Type uS) (K : Type uK)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra.Etale R S] :
    IsField (K ⊗[R] S) := by
  have he : (algebraMap R S).Etale := RingHom.etale_algebraMap.mpr inferInstance
  have hflat : (algebraMap R S).Flat :=
    (RingHom.Etale.iff_flat_and_formallyUnramified (f := algebraMap R S)).mp he |>.1
  let _inst : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  apply genericFiber_isField_of_formallyUnramified R S K
  intro x y hxy
  by_contra hne
  have hr : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hreg : IsSMulRegular S (x - y) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
  have hmap : algebraMap R S (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hz : (x - y) • (1 : S) = (x - y) • (0 : S) := by
    simp only [Algebra.smul_def, mul_one, mul_zero, hmap]
  exact one_ne_zero (hreg hz)

/-- A height-one prime of an etale domain has nonzero contraction to the base.
The proof uses only the field property of the generic fiber: a prime disjoint
from the nonzero elements of the base would extend to a prime of that field. -/
theorem heightOne_contraction_ne_bot_of_etale
    {R S K : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra.Etale R S] (w : IsDedekindDomain.HeightOneSpectrum S) :
    w.asIdeal.under R ≠ ⊥ := by
  let T := K ⊗[R] S
  have hinj : Function.Injective (algebraMap R S) := by
    have he : (algebraMap R S).Etale := RingHom.etale_algebraMap.mpr inferInstance
    have hflat : (algebraMap R S).Flat :=
      (RingHom.Etale.iff_flat_and_formallyUnramified
        (f := algebraMap R S)).mp he |>.1
    let _inst : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
    intro x y hxy
    by_contra hne
    have hr : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hreg : IsSMulRegular S (x - y) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
    have hmap : algebraMap R S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz : (x - y) • (1 : S) = (x - y) • (0 : S) := by
      simp only [Algebra.smul_def, mul_one, mul_zero, hmap]
    exact one_ne_zero (hreg hz)
  let M : Submonoid S := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)
  have hM : M ≤ nonZeroDivisors S := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr)
      (hinj (h.trans (map_zero _).symm))
  have : Field T := (genericFiber_isField_of_etale R S K).toField
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) T :=
    IsLocalization.tensorRight (R := R) (S := S) (A := K) (nonZeroDivisors R)
  have : IsLocalization M T := by simpa only [M] using hloc
  have hcontract : w.asIdeal.under R ≠ ⊥ := by
    intro hbot
    have hdisj : Disjoint (M : Set S) w.asIdeal := by
      rw [Set.disjoint_left]
      rintro _ ⟨r, hr, rfl⟩ hrw
      have : r ∈ w.asIdeal.under R := by
        change r ∈ Ideal.comap (algebraMap R S) w.asIdeal
        exact hrw
      have hrbot : r ∈ (⊥ : Ideal R) := by
        rw [← hbot]
        exact this
      exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) (Ideal.mem_bot.mp hrbot)
    let qT := w.asIdeal.map (algebraMap S T)
    have hqT : qT.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
      M T w.asIdeal w.isPrime hdisj
    have hqT_ne_bot : qT ≠ ⊥ := by
      intro h
      have hu := IsLocalization.under_map_of_isPrime_disjoint
        M T w.isPrime hdisj
      have hinjT : Function.Injective (algebraMap S T) :=
        IsLocalization.injective T hM
      have hbotT : (⊥ : Ideal T).under S = ⊥ :=
        Ideal.comap_bot_of_injective (algebraMap S T) hinjT
      change qT.under S = w.asIdeal at hu
      rw [h, hbotT] at hu
      exact w.ne_bot hu.symm
    exact (Ring.not_isField_of_ne_of_ne hqT_ne_bot hqT.ne_top)
      (genericFiber_isField_of_etale R S K)
  exact hcontract

/-- The natural generic-fibre map for a dominant essentially finite type
unramified domain is an equivalence with its fraction field. -/
noncomputable def unramifiedGenericFiberAlgEquiv
    {R : Type uR} {S : Type uS} {K : Type uK} {E : Type uE}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E] :
    (K ⊗[R] S) ≃ₐ[K] E := by
  have hRE : Function.Injective (algebraMap R E) := by
    rw [IsScalarTower.algebraMap_eq R K E]
    exact (algebraMap K E).injective.comp
      (FaithfulSMul.algebraMap_injective R K)
  have hRS : Function.Injective (algebraMap R S) := by
    intro x y hxy
    apply hRE
    rw [IsScalarTower.algebraMap_apply R S E,
      IsScalarTower.algebraMap_apply R S E, hxy]
  let T := K ⊗[R] S
  let : Field T :=
    (genericFiber_isField_of_formallyUnramified R S K hRS).toField
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  have : IsFractionRing S T :=
    isFractionRing_of_genericFiberAlgEquiv (R := R) (C := S)
      (K := K) (E := T) (AlgEquiv.refl : T ≃ₐ[K] T)
  let f : T →ₐ[K] E :=
    (AlgHom.liftEquiv R K S E) (IsScalarTower.toAlgHom R S E)
  have hfS : f.toRingHom.comp (algebraMap S T) = algebraMap S E := by
    ext s
    change f (1 ⊗ₜ[R] s) = algebraMap S E s
    change ((AlgHom.liftEquiv R K S E) (IsScalarTower.toAlgHom R S E))
      (1 ⊗ₜ[R] s) = _
    rw [AlgHom.liftEquiv_tmul]
    change (1 : K) • algebraMap S E s = algebraMap S E s
    exact one_smul _ _
  exact AlgEquiv.ofBijective f
    (IsLocalization.bijective (M := nonZeroDivisors S) f.toRingHom hfS)

/-- The natural generic-fibre equivalence acts on pure tensors by the
product of the two structure maps. -/
@[simp]
theorem unramifiedGenericFiberAlgEquiv_tmul
    {R : Type uR} {S : Type uS} {K : Type uK} {E : Type uE}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E]
    (x : K) (s : S) :
    unramifiedGenericFiberAlgEquiv (R := R) (S := S) (K := K) (E := E)
        (x ⊗ₜ[R] s) = algebraMap K E x * algebraMap S E s := by
  change ((AlgHom.liftEquiv R K S E) (IsScalarTower.toAlgHom R S E))
      (x ⊗ₜ[R] s) = _
  rw [AlgHom.liftEquiv_tmul]
  change x • algebraMap S E s = algebraMap K E x * algebraMap S E s
  exact Algebra.smul_def _ _

/-- The generic-fibre square of compatible fraction fields is an algebraic
pushout, with the specified structure maps. -/
theorem unramifiedGenericFiber_isPushout
    {R : Type uR} {S : Type uS} {K : Type uK} {E : Type uE}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E] :
    Algebra.IsPushout R K S E := by
  let : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  apply Algebra.IsPushout.of_equiv
    (unramifiedGenericFiberAlgEquiv (R := R) (S := S) (K := K) (E := E))
  ext s
  change unramifiedGenericFiberAlgEquiv (R := R) (S := S) (K := K) (E := E)
    (1 ⊗ₜ[R] s) = algebraMap S E s
  rw [unramifiedGenericFiberAlgEquiv_tmul, map_one, one_mul]

end EtaleFundamentalGroups
