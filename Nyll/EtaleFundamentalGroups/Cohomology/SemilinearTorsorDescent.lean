/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.Algebra.Torsor.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # Descent of semilinear torsor actions and displacement cocycles -/

noncomputable section
open groupCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {P G T : Type*} [Group P] [Group G] [MulAction P T]
  (q : P →* G) (hq : Function.Surjective q)
  (hker : ∀ p : P, q p = 1 → ∀ t : T, p • t = t)

include hker in
/-- The original action is independent of the chosen quotient lift. -/
theorem torsorAction_eq_of_quotient_eq (p r : P) (h : q p = q r) (t : T) :
    p • t = r • t := by
  have hrel : q (r⁻¹ * p) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  calc
    p • t = (r * (r⁻¹ * p)) • t := by rw [mul_inv_cancel_left]
    _ = r • ((r⁻¹ * p) • t) := mul_smul _ _ _
    _ = r • t := congrArg (r • ·) (hker (r⁻¹ * p) hrel t)

/-- Descend the original action itself, not just its displacement function. -/
@[instance_reducible]
def descendedTorsorAction : MulAction G T where
  smul g t := (hq g).choose • t
  one_smul t := hker _ (hq 1).choose_spec t
  mul_smul g h t := by
    change (hq (g * h)).choose • t = (hq g).choose • ((hq h).choose • t)
    rw [← mul_smul]
    apply torsorAction_eq_of_quotient_eq q hker
    rw [(hq (g * h)).choose_spec, map_mul,
      (hq g).choose_spec, (hq h).choose_spec]

variable {A : Type*} [CommGroup A] [MulDistribMulAction G A] [Torsor A T]
  (hsemi : ∀ (p : P) (a : A) (t : T),
    p • (a • t) = (q p • a) • (p • t))

include hsemi in
/-- The descended action retains the cyclotomic semilinearity. -/
theorem descendedTorsorAction_semilinear (g : G) (a : A) (t : T) :
    letI := descendedTorsorAction q hq hker
    g • (a • t) = (g • a) • (g • t) := by
  change (hq g).choose • (a • t) = (g • a) • ((hq g).choose • t)
  rw [hsemi, (hq g).choose_spec]

/-- Displacement in the actual semilinear torsor before quotient descent. -/
def semilinearDisplacement (t : T) (p : P) : A := (p • t) /ₛ t

include hsemi in
/-- The crossed law is derived from the actual semilinear action. -/
theorem semilinearDisplacement_mul (t : T) (p r : P) :
    semilinearDisplacement t (p * r) =
      (q p • semilinearDisplacement t r) * semilinearDisplacement t p := by
  change ((p * r) • t) /ₛ t = _
  rw [mul_smul]
  conv_lhs => rw [← sdiv_smul (r • t) t]
  rw [hsemi, smul_sdiv_assoc]
  rfl

omit [MulDistribMulAction G A] in
include hker in
/-- Elements of the geometric kernel have zero displacement on the Isom torsor. -/
theorem semilinearDisplacement_kernel (t : T) (p : P) (hp : q p = 1) :
    semilinearDisplacement t p = 1 := by
  change (p • t) /ₛ t = 1
  rw [hker p hp, sdiv_self]

include hsemi hker in
/-- The displacement is constant on the fibres of the arithmetic quotient. -/
theorem semilinearDisplacement_eq_of_quotient_eq (t : T) (p r : P)
    (h : q p = q r) : semilinearDisplacement t p = semilinearDisplacement t r := by
  have hrel : q (r⁻¹ * p) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have hc := semilinearDisplacement_mul q hsemi t r (r⁻¹ * p)
  rw [mul_inv_cancel_left,
    semilinearDisplacement_kernel q hker t (r⁻¹ * p) hrel,
    smul_one, one_mul] at hc
  exact hc

/-- The actual displacement descends to the arithmetic quotient. -/
def descendedTorsorCocycle (t : T) (g : G) : A :=
  semilinearDisplacement t (hq g).choose

include hsemi hker in
/-- The descended function agrees with displacement for every lift. -/
theorem descendedTorsorCocycle_apply_quotient (t : T) (p : P) :
    descendedTorsorCocycle q hq t (q p) = semilinearDisplacement t p := by
  exact semilinearDisplacement_eq_of_quotient_eq (q := q) (hker := hker) (hsemi := hsemi) t _ p
    (hq (q p)).choose_spec

include hsemi hker in
/-- The descended displacement is a genuine crossed cocycle. -/
theorem isMulCocycle_descendedTorsorCocycle (t : T) :
    IsMulCocycle₁ (descendedTorsorCocycle q hq t) := by
  intro g h
  obtain ⟨p, rfl⟩ := hq g
  obtain ⟨r, rfl⟩ := hq h
  rw [← q.map_mul,
    descendedTorsorCocycle_apply_quotient (q := q) (hq := hq)
      (hker := hker) (hsemi := hsemi) t (p * r),
    descendedTorsorCocycle_apply_quotient (q := q) (hq := hq) (hker := hker) (hsemi := hsemi) t r,
    descendedTorsorCocycle_apply_quotient (q := q) (hq := hq) (hker := hker) (hsemi := hsemi) t p]
  exact semilinearDisplacement_mul q hsemi t p r

include hsemi hker in
/-- Quotient descent also preserves locally constant displacement. This
version is used when local constancy has been proved directly by evaluating
an actual Isom in its original discrete source/target fibres. -/
theorem isLocallyConstant_descendedTorsorCocycle_of_displacement
    [TopologicalSpace P] [TopologicalSpace G]
    (hquot : Topology.IsQuotientMap q) (t : T)
    (hlc : IsLocallyConstant (semilinearDisplacement t : P → A)) :
    IsLocallyConstant (descendedTorsorCocycle q hq t) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  apply (IsLocallyConstant.iff_continuous _).mpr
  apply hquot.continuous_iff.mpr
  have heq : (descendedTorsorCocycle q hq t) ∘ q =
      semilinearDisplacement t := by
    funext p
    exact descendedTorsorCocycle_apply_quotient (q := q) (hq := hq)
      (hker := hker) (hsemi := hsemi) t p
  rw [heq]
  exact hlc.continuous

section Topology
variable [TopologicalSpace P] [TopologicalSpace G]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul P T]

include hsemi hker in
/-- Local constancy follows from the existing discrete torsor action and the
quotient topology, not from a separate cocycle-continuity assumption. -/
theorem isLocallyConstant_descendedTorsorCocycle
    (hquot : Topology.IsQuotientMap q) (t : T) :
    IsLocallyConstant (descendedTorsorCocycle q hq t) := by
  apply (IsLocallyConstant.iff_continuous _).mpr
  apply hquot.continuous_iff.mpr
  have heq : (descendedTorsorCocycle q hq t) ∘ q =
      semilinearDisplacement t := by
    funext p
    exact descendedTorsorCocycle_apply_quotient (q := q) (hq := hq)
      (hker := hker) (hsemi := hsemi) t p
  rw [heq]
  exact (continuous_of_discreteTopology : Continuous (fun x : T => (x /ₛ t : A))).comp
    (continuous_id.smul continuous_const)

end Topology
end EtaleFundamentalGroups.Cohomology
