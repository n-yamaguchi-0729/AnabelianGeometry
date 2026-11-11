/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.PrimePower
public import Nyll.AbelianVarieties.Tate.Representation
public import Nyll.ProCGroups.Abelian.RestrictedTateModule
public import Nyll.ProCGroups.Abelian.RestrictedTateTransport
public import Nyll.ProCGroups.Abelian.RestrictedTatePadic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Data.Nat.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Comparison with the existing restricted Tate module

Prime-power sequences and the existing restricted module over the powers of a
positive integer have the same actual torsion points and multiplication transitions.
The comparison is additive and preserves every projection. At a prime it also
preserves the canonical p-adic actions and the existing inverse-limit topologies.
No torsion cardinality, divisibility or finiteness assumption on the point group is required.
-/

@[expose] public section

universe u v

namespace TateModule

open ProCGroups

variable (p : ℕ+) (M : Type u) [AddCommGroup M]

/-- Read the restricted family at the powers of `p`. -/
def ofRestricted : RestrictedTateModule M (Submonoid.powers p) →+ TateModule (p : ℕ) M where
  toFun x := ⟨fun n => RestrictedTateModule.evaluation M _ (Submonoid.pow p n) x, by
    intro n
    constructor
    · rw [natCast_zsmul]
      exact (RestrictedTateModule.projection M _ (Submonoid.pow p n) x).property
    · rw [natCast_zsmul]
      have h := RestrictedTateModule.evaluation_compatible x
        (Submonoid.pow p n) (Submonoid.pow p 1)
      have heq : Submonoid.pow p n * Submonoid.pow p 1 = Submonoid.pow p (n + 1) := by
        apply Subtype.ext
        change p ^ n * p ^ 1 = p ^ (n + 1)
        rw [pow_one, pow_succ]
      rw [heq] at h
      change (p : ℕ) ^ 1 • _ = _ at h
      simpa only [pow_one] using h⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact (RestrictedTateModule.evaluation M _ (Submonoid.pow p n)).map_zero
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (RestrictedTateModule.evaluation M _ (Submonoid.pow p n)).map_add x y

@[simp] theorem proj_ofRestricted
    (x : RestrictedTateModule M (Submonoid.powers p)) (n : ℕ) :
    proj (p : ℕ) M n (ofRestricted p M x) =
      RestrictedTateModule.evaluation M _ (Submonoid.pow p n) x := rfl

private theorem pow_injective (hp : 2 ≤ (p : ℕ)) : Function.Injective (fun n : ℕ => p ^ n) := by
  intro i j h
  exact Nat.pow_right_injective hp (congrArg (fun q : ℕ+ => (q : ℕ)) h)

/-- Reindex a compatible prime-power sequence by the corresponding positive integers. -/
def toRestricted (hp : 2 ≤ (p : ℕ)) :
    TateModule (p : ℕ) M →+ RestrictedTateModule M (Submonoid.powers p) where
  toFun x := ⟨fun n => ⟨(x : ℕ → M) (Submonoid.log n), by
      have h := torsion x (Submonoid.log n)
      have hn := congrArg (fun q : Submonoid.powers p => (q.1 : ℕ))
        (Submonoid.pow_log_eq_self n)
      change (p : ℕ) ^ Submonoid.log n = (n.1 : ℕ) at hn
      rw [natCast_zsmul] at h
      change ((p : ℕ) ^ Submonoid.log n) • _ = 0 at h
      rw [hn] at h
      exact h⟩, by
    intro n m
    apply Subtype.ext
    change (m.1 : ℕ) • (x : ℕ → M) (Submonoid.log (n * m)) =
      (x : ℕ → M) (Submonoid.log n)
    rw [Submonoid.log_mul (pow_injective p hp)]
    have hm := congrArg (fun q : Submonoid.powers p => (q.1 : ℕ))
      (Submonoid.pow_log_eq_self m)
    change (p : ℕ) ^ Submonoid.log m = (m.1 : ℕ) at hm
    rw [← hm]
    exact (natCast_zsmul _ _).symm.trans (compat_pow x (Submonoid.log n) (Submonoid.log m))⟩
  map_zero' := by
    apply RestrictedTateModule.ext
    intro n
    rfl
  map_add' x y := by
    apply RestrictedTateModule.ext
    intro n
    rfl

@[simp] theorem evaluation_toRestricted (hp : 2 ≤ (p : ℕ))
    (x : TateModule (p : ℕ) M) (n : Submonoid.powers p) :
    RestrictedTateModule.evaluation M _ n (toRestricted p M hp x) =
      proj (p : ℕ) M (Submonoid.log n) x := rfl

/-- The two Tate constructions are additively equivalent, with their original transitions. -/
def restrictedEquiv (hp : 2 ≤ (p : ℕ)) :
    TateModule (p : ℕ) M ≃+ RestrictedTateModule M (Submonoid.powers p) where
  toFun := toRestricted p M hp
  invFun := ofRestricted p M
  left_inv x := by
    apply Subtype.ext
    funext n
    change (x : ℕ → M) (Submonoid.log (Submonoid.pow p n)) = (x : ℕ → M) n
    rw [Submonoid.log_pow_eq_self (pow_injective p hp)]
  right_inv x := by
    apply RestrictedTateModule.ext
    intro n
    change RestrictedTateModule.evaluation M _ (Submonoid.pow p (Submonoid.log n)) x =
      RestrictedTateModule.evaluation M _ n x
    rw [Submonoid.pow_log_eq_self]
  map_add' := (toRestricted p M hp).map_add

/-- The comparison preserves the original geometric point at every prime-power level. -/
theorem evaluation_restrictedEquiv (hp : 2 ≤ (p : ℕ))
    (x : TateModule (p : ℕ) M) (n : ℕ) :
    RestrictedTateModule.evaluation M _ (Submonoid.pow p n) (restrictedEquiv p M hp x) =
      proj (p : ℕ) M n x := by
  change (x : ℕ → M) (Submonoid.log (Submonoid.pow p n)) = (x : ℕ → M) n
  rw [Submonoid.log_pow_eq_self (pow_injective p hp)]

section Action

variable [Fact (p : ℕ).Prime] {G : Type v} [Monoid G] [DistribMulAction G M]

/-- The comparison intertwines the prime-power representation with the actual
coordinatewise action on the existing restricted Tate module. -/
theorem restrictedEquiv_rep (hp : 2 ≤ (p : ℕ)) (σ : G) (x : TateModule (p : ℕ) M) :
    restrictedEquiv p M hp (rep (p : ℕ) M G σ x) =
      RestrictedTateModule.map (DistribSMul.toAddMonoidHom M σ)
        (restrictedEquiv p M hp x) := by
  apply RestrictedTateModule.ext
  intro n
  rfl

end Action

section LinearComparison

variable [Fact (p : ℕ).Prime]

/-- The original projection-preserving comparison is linear for the actual
p-adic residue actions on both inverse-limit presentations. -/
noncomputable def restrictedLinearEquiv :
    TateModule (p : ℕ) M ≃ₗ[ℤ_[(p : ℕ)]] RestrictedTateModule M (Submonoid.powers p) :=
  { restrictedEquiv p M (Fact.out : (p : ℕ).Prime).two_le with
    map_smul' := by
      intro a x
      apply RestrictedTateModule.ext
      intro n
      rw [RestrictedTateModule.evaluation_padic_smul]
      change ((a • x : TateModule (p : ℕ) M) : ℕ → M) (Submonoid.log n) =
        a.appr (Submonoid.log n) • (x : ℕ → M) (Submonoid.log n)
      rw [smul_apply, natCast_zsmul] }

/-- The linear comparison retains each original torsion-point evaluation. -/
theorem evaluation_restrictedLinearEquiv (x : TateModule (p : ℕ) M) (n : ℕ) :
    RestrictedTateModule.evaluation M _ (Submonoid.pow p n) (restrictedLinearEquiv p M x) =
      proj (p : ℕ) M n x :=
  evaluation_restrictedEquiv p M (Fact.out : (p : ℕ).Prime).two_le x n

variable {M} {N : Type v} [AddCommGroup N]

/-- The same point map gives a commuting square of linear maps in the two presentations. -/
theorem restrictedLinearEquiv_map (f : M →+ N) :
    (restrictedLinearEquiv p N).toLinearMap.comp (map (p : ℕ) f) =
      (RestrictedTateModule.mapLinear p f).comp (restrictedLinearEquiv p M).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply RestrictedTateModule.ext
  intro n
  rfl

/-- The existing coordinate action intertwines with the prime-power representation as
an equality of p-adic linear maps. -/
theorem restrictedLinearEquiv_rep {G : Type v} [Monoid G] [DistribMulAction G M] (σ : G) :
    (restrictedLinearEquiv p M).toLinearMap.comp (rep (p : ℕ) M G σ) =
      (RestrictedTateModule.mapLinear p (DistribSMul.toAddMonoidHom M σ)).comp
        (restrictedLinearEquiv p M).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact restrictedEquiv_rep p M (Fact.out : (p : ℕ).Prime).two_le σ x

end LinearComparison

section Topology

variable (q : ℕ) [Fact q.Prime]

/-- The prime-power topology is the existing inverse-limit topology of discrete torsion levels. -/
instance instTopologicalSpace : TopologicalSpace (TateModule q M) :=
  TopologicalSpace.induced
    (restrictedEquiv ⟨q, (Fact.out : q.Prime).pos⟩ M (Fact.out : q.Prime).two_le)
    inferInstance

/-- The projection-preserving comparison also identifies the inverse-limit topologies. -/
def restrictedHomeomorph :
    TateModule q M ≃ₜ RestrictedTateModule M
      (Submonoid.powers (⟨q, (Fact.out : q.Prime).pos⟩ : ℕ+)) :=
by
  let e : TateModule q M ≃ RestrictedTateModule M
      (Submonoid.powers (⟨q, (Fact.out : q.Prime).pos⟩ : ℕ+)) :=
    (restrictedEquiv ⟨q, (Fact.out : q.Prime).pos⟩ M (Fact.out : q.Prime).two_le).toEquiv
  exact e.toHomeomorphOfIsInducing ⟨rfl⟩

/-- The original homeomorphism and the linear comparison are the same continuous linear map. -/
noncomputable def restrictedContinuousLinearEquiv :
    let positivePrime : ℕ+ := ⟨q, (Fact.out : q.Prime).pos⟩
    let _ : Fact (positivePrime : ℕ).Prime := inferInstanceAs (Fact q.Prime)
    TateModule (positivePrime : ℕ) M ≃L[ℤ_[(positivePrime : ℕ)]]
      RestrictedTateModule M (Submonoid.powers positivePrime) := by
  intro positivePrime primeFact
  exact
    { @restrictedLinearEquiv positivePrime M _ primeFact with
      continuous_toFun := (restrictedHomeomorph M q).continuous_toFun
      continuous_invFun := (restrictedHomeomorph M q).continuous_invFun }

/-- The continuous linear comparison retains the existing homeomorphism pointwise. -/
@[simp] theorem restrictedContinuousLinearEquiv_apply (x : TateModule q M) :
    restrictedContinuousLinearEquiv M q x = restrictedHomeomorph M q x := rfl

/-- The inverse comparison also retains the same original point map. -/
@[simp] theorem restrictedContinuousLinearEquiv_symm_apply
    (x : RestrictedTateModule M (Submonoid.powers (⟨q, (Fact.out : q.Prime).pos⟩ : ℕ+))) :
    (restrictedContinuousLinearEquiv M q).toEquiv.symm x =
      (restrictedHomeomorph M q).symm x := rfl

/-- Each acting element acts continuously on the prime-power Tate module.
Joint continuity in the acting group still requires continuity of its finite-level action. -/
theorem continuous_rep {G : Type v} [Monoid G] [DistribMulAction G M] (σ : G) :
    Continuous (rep q M G σ) := by
  let e := restrictedHomeomorph M q
  have h : (fun x : TateModule q M => rep q M G σ x) =
      fun x => e.symm (RestrictedTateModule.map (DistribSMul.toAddMonoidHom M σ) (e x)) := by
    funext x
    apply e.injective
    have hx : e (rep q M G σ x) =
        RestrictedTateModule.map (DistribSMul.toAddMonoidHom M σ) (e x) :=
      @restrictedEquiv_rep ⟨q, (Fact.out : q.Prime).pos⟩ M _
        (inferInstanceAs (Fact q.Prime)) G _ _ (Fact.out : q.Prime).two_le σ x
    exact hx.trans (e.apply_symm_apply _).symm
  exact (congrArg Continuous h).mpr
    (e.symm.continuous.comp ((RestrictedTateModule.continuous_map _).comp e.continuous))

/-- Finite-level joint continuity passes to the actual prime-power representation. -/
theorem continuous_rep_of_continuous_levels
    {G : Type v} [Monoid G] [DistribMulAction G M] [TopologicalSpace G]
    (h : ∀ n : Submonoid.powers (⟨q, (Fact.out : q.Prime).pos⟩ : ℕ+),
      let _ := FullTateModule.torsionLevelTopology M n.1
      Continuous (fun z : G × torsionLevel M n.1 =>
        RestrictedTateModule.mapTorsion (DistribSMul.toAddMonoidHom M z.1) n.1 z.2)) :
    Continuous (fun z : G × TateModule q M => rep q M G z.1 z.2) := by
  let S : Submonoid ℕ+ := Submonoid.powers ⟨q, (Fact.out : q.Prime).pos⟩
  let e : TateModule q M ≃ₜ RestrictedTateModule M S := restrictedHomeomorph M q
  have hc : Continuous (fun z : G × RestrictedTateModule M S =>
      RestrictedTateModule.map (DistribSMul.toAddMonoidHom M z.1) z.2) :=
    RestrictedTateModule.continuous_map_family
      (fun σ : G => DistribSMul.toAddMonoidHom M σ) h
  have heq : (fun z : G × TateModule q M => rep q M G z.1 z.2) =
      fun z => e.symm (RestrictedTateModule.map
        (DistribSMul.toAddMonoidHom M z.1) (e z.2)) := by
    funext z
    apply e.injective
    have hz := @restrictedEquiv_rep ⟨q, (Fact.out : q.Prime).pos⟩ M _
      (inferInstanceAs (Fact q.Prime)) G _ _ (Fact.out : q.Prime).two_le z.1 z.2
    exact hz.trans (e.apply_symm_apply _).symm
  rw [heq]
  have hp : Continuous (fun z : G × TateModule q M => (z.1, e z.2)) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  exact e.symm.continuous.comp (hc.comp hp)

end Topology

end TateModule
