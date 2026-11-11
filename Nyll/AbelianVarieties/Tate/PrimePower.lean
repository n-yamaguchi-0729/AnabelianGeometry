/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.NumberTheory.Padics.RingHoms


/-!
# Prime-power Tate modules as compatible sequences

This is the generic prime-power construction extracted from the upstream
elliptic-curve file. It supplies the actual inverse limit, its p-adic scalar
multiplication, projections, and compatible-sequence lifts used by `Basis`.
The rank-two elliptic-curve arguments and the Galois-representation coefficient
extensions are not included.

`ProCGroups.FullTateModule` and `ProCGroups.RestrictedTateModule` use a different
indexing and bundled torsion-level representation. Their existing declarations
remain the owners of those constructions. `RestrictedTatePadic` supplies the
canonical p-adic action on restricted p-power families, and `RestrictedComparison`
compares this sequence presentation with those families, preserving scalar
multiplication, projections, the topology and the coordinatewise Galois action.
-/

@[expose] public section

universe u

section
/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Anthropic's Fermat's Last Theorem formalization:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_EllipticCurve_TateModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/




/-- Compatible prime-power torsion points with transition multiplication by `p`. -/
def TateModule (p : ℕ) (M : Type u) [AddCommGroup M] : AddSubgroup (ℕ → M) where
  carrier := {x | ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n}
  add_mem' := fun {x y} hx hy n =>
    ⟨by rw [Pi.add_apply, smul_add, (hx n).1, (hy n).1, add_zero],
     by rw [Pi.add_apply, Pi.add_apply, smul_add, (hx n).2, (hy n).2]⟩
  zero_mem' := fun n => ⟨smul_zero _, by rw [Pi.zero_apply, Pi.zero_apply, smul_zero]⟩
  neg_mem' := fun {x} hx n =>
    ⟨by rw [Pi.neg_apply, smul_neg, (hx n).1, neg_zero],
     by rw [Pi.neg_apply, Pi.neg_apply, smul_neg, (hx n).2]⟩

namespace TateModule

variable {p : ℕ} {M : Type u} [AddCommGroup M]

theorem torsion (x : TateModule p M) (n : ℕ) : ((p ^ n : ℕ) : ℤ) • (x : ℕ → M) n = 0 := (x.2 n).1

theorem compat (x : TateModule p M) (n : ℕ) : ((p : ℕ) : ℤ) • (x : ℕ → M) (n + 1) = (x : ℕ → M) n :=
  (x.2 n).2

theorem compat_pow (x : TateModule p M) (n k : ℕ) :
    ((p ^ k : ℕ) : ℤ) • (x : ℕ → M) (n + k) = (x : ℕ → M) n := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_one, one_smul, Nat.add_zero]
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, mul_smul]
    change ((p ^ k : ℕ) : ℤ) • (((p : ℕ) : ℤ) • (x : ℕ → M) ((n + k) + 1)) = _
    rw [compat, ih]

@[simp] theorem coe_add (x y : TateModule p M) : ((x + y : TateModule p M) : ℕ → M) = x + y := rfl
@[simp] theorem coe_zero : ((0 : TateModule p M) : ℕ → M) = 0 := rfl
@[simp] theorem coe_neg (x : TateModule p M) : ((-x : TateModule p M) : ℕ → M) = -x := rfl
@[simp] theorem coe_sub (x y : TateModule p M) : ((x - y : TateModule p M) : ℕ → M) = x - y := rfl

theorem apply_zero (x : TateModule p M) : (x : ℕ → M) 0 = 0 := by
  have h := torsion x 0
  rwa [pow_zero, Nat.cast_one, one_smul] at h

theorem natCast_smul_eq_mod {n c : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0) :
    (c : ℤ) • m = ((c % p ^ n : ℕ) : ℤ) • m := by
  conv_lhs => rw [← Nat.div_add_mod c (p ^ n)]
  rw [Nat.cast_add, add_smul, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero, zero_add]

theorem natCast_smul_eq_of_zmod_eq {n c d : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0)
    (h : (c : ZMod (p ^ n)) = d) : (c : ℤ) • m = (d : ℤ) • m := by
  rw [natCast_smul_eq_mod hm, natCast_smul_eq_mod (c := d) hm,
    (ZMod.natCast_eq_natCast_iff' c d _).1 h]

section Padic

variable [Fact p.Prime]

theorem toZModPow_eq_appr (n : ℕ) (a : ℤ_[p]) :
    PadicInt.toZModPow n a = (a.appr n : ZMod (p ^ n)) := rfl

theorem appr_succ_smul_eq (a : ℤ_[p]) (x : TateModule p M) (n : ℕ) :
    ((a.appr (n + 1) : ℕ) : ℤ) • (x : ℕ → M) n = ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n := by
  refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
  rw [← toZModPow_eq_appr, ← PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ,
    RingHom.comp_apply,
    toZModPow_eq_appr, ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p n.le_succ)]

noncomputable instance instSMul : SMul ℤ_[p] (TateModule p M) :=
  ⟨fun a x => ⟨fun n => ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n, fun n =>
    ⟨by rw [smul_comm, torsion, smul_zero], by rw [smul_comm, compat, appr_succ_smul_eq]⟩⟩⟩

@[simp] theorem smul_apply (a : ℤ_[p]) (x : TateModule p M) (n : ℕ) :
    ((a • x : TateModule p M) : ℕ → M) n = ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n := rfl

noncomputable instance instModule : Module ℤ_[p] (TateModule p M) where
  one_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply]
    have h : (((1 : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) = ((1 : ℕ) : ZMod (p ^ n)) := by
      rw [← toZModPow_eq_appr, map_one, Nat.cast_one]
    rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_one, one_smul]
  mul_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, smul_apply, smul_apply, smul_smul, ← Nat.cast_mul]
    refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
    rw [← toZModPow_eq_appr, map_mul, toZModPow_eq_appr, toZModPow_eq_appr, Nat.cast_mul]
  smul_zero a := Subtype.ext (funext fun n => by
    rw [smul_apply, coe_zero, Pi.zero_apply, smul_zero])
  smul_add a x y := Subtype.ext (funext fun n => by
    rw [smul_apply, coe_add, Pi.add_apply, smul_add, coe_add, Pi.add_apply, smul_apply, smul_apply])
  add_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, coe_add, Pi.add_apply, smul_apply, smul_apply, ← add_smul, ← Nat.cast_add]
    refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
    rw [← toZModPow_eq_appr, map_add, toZModPow_eq_appr, toZModPow_eq_appr, Nat.cast_add]
  zero_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, coe_zero, Pi.zero_apply]
    have h : (((0 : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) = ((0 : ℕ) : ZMod (p ^ n)) := by
      rw [← toZModPow_eq_appr, map_zero, Nat.cast_zero]
    rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_zero, zero_smul]

end Padic

variable (p M) in
/-- Evaluation at the `n`-th prime-power torsion level. -/
def proj (n : ℕ) : TateModule p M →+ M where
  toFun x := (x : ℕ → M) n
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem proj_apply (n : ℕ) (x : TateModule p M) : proj p M n x = (x : ℕ → M) n := rfl

theorem torsionBy_proj (n : ℕ) (x : TateModule p M) : ((p ^ n : ℕ) : ℤ) • proj p M n x = 0 :=
  torsion x n

theorem proj_mem_torsionBy (n : ℕ) (x : TateModule p M) :
    proj p M n x ∈ Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
  (Submodule.mem_torsionBy_iff _ _).2 (torsion x n)

open Submodule

theorem mem_torsionBy_add {n : ℕ} {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) (k : ℕ) :
    m ∈ torsionBy ℤ M ((p ^ (n + k) : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff] at hm ⊢
  rw [pow_add, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero]

theorem smul_mem_torsionBy_of_mem_succ {n : ℕ} {m : M}
    (hm : m ∈ torsionBy ℤ M ((p ^ (n + 1) : ℕ) : ℤ)) :
    ((p : ℕ) : ℤ) • m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff] at hm ⊢
  rw [smul_smul, ← Nat.cast_mul, ← pow_succ, hm]

theorem pow_smul_mem_torsionBy {n k : ℕ} {m : M} (hk : k ≤ n)
    (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    ((p ^ (n - k) : ℕ) : ℤ) • m ∈ torsionBy ℤ M ((p ^ k : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff] at hm ⊢
  rw [smul_smul, ← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hk, hm]

theorem mem_torsionBy_one_of_smul_eq_zero {m : M} (hm : ((p : ℕ) : ℤ) • m = 0) :
    m ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff, pow_one]; exact hm

theorem smul_eq_zero_of_mem_torsionBy_one {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) :
    ((p : ℕ) : ℤ) • m = 0 := by
  rw [mem_torsionBy_iff, pow_one] at hm; exact hm

variable (p M) in
/-- Multiplication by `p` between consecutive actual torsion subgroups. -/
def mulP (n : ℕ) : torsionBy ℤ M ((p ^ (n + 1) : ℕ) : ℤ) →+ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) where
  toFun m := ⟨((p : ℕ) : ℤ) • (m : M), smul_mem_torsionBy_of_mem_succ m.2⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' _ _ := Subtype.ext (smul_add _ _ _)

@[simp] theorem coe_mulP (n : ℕ) (m : torsionBy ℤ M ((p ^ (n + 1) : ℕ) : ℤ)) :
    (mulP p M n m : M) = ((p : ℕ) : ℤ) • (m : M) := rfl

variable (p M) in
/-- The kernel of a transition is the subgroup of points killed by `p`. -/
def kerMulPEquiv (n : ℕ) : (mulP p M n).ker ≃ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ) where
  toFun m := ⟨(m.1 : M), mem_torsionBy_one_of_smul_eq_zero (by
    have h := m.2; rw [AddMonoidHom.mem_ker] at h; exact congrArg Subtype.val h)⟩
  invFun m := ⟨⟨(m : M), by
      rw [mem_torsionBy_iff, pow_succ, Nat.cast_mul, mul_smul,
        smul_eq_zero_of_mem_torsionBy_one m.2, smul_zero]⟩,
    by rw [AddMonoidHom.mem_ker]; exact Subtype.ext (smul_eq_zero_of_mem_torsionBy_one m.2)⟩
  left_inv m := rfl
  right_inv m := rfl

/-- Iterate specified lifts through the multiplication transitions. -/
noncomputable def liftAux
    (next : (k : ℕ) → torsionBy ℤ M ((p ^ k : ℕ) : ℤ) → torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ))
    (n : ℕ) (m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) : (j : ℕ) → torsionBy ℤ M ((p ^ (n + j) : ℕ) : ℤ)
  | 0 => m
  | j + 1 => next (n + j) (liftAux next n m j)

/-- A compatible sequence through a prescribed point, using specified lifts. -/
noncomputable def liftFun
    (next : (k : ℕ) → torsionBy ℤ M ((p ^ k : ℕ) : ℤ) → torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ))
    (n : ℕ) (m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) (k : ℕ) : M :=
  if n ≤ k then (liftAux next n m (k - n) : M) else ((p ^ (n - k) : ℕ) : ℤ) • (m : M)

theorem liftFun_of_le {next} {n : ℕ} {m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)} {k : ℕ} (hk : n ≤ k) :
    liftFun next n m k = (liftAux next n m (k - n) : M) := ite_eq_left hk

theorem liftFun_of_lt {next} {n : ℕ} {m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)} {k : ℕ} (hk : k < n) :
    liftFun next n m k = ((p ^ (n - k) : ℕ) : ℤ) • (m : M) := ite_eq_right (not_le.mpr hk)

theorem coe_liftAux_congr {next} {n : ℕ} {m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)}
    {j j' : ℕ} (h : j = j') :
    (liftAux next n m j : M) = (liftAux next n m j' : M) := by subst h; rfl

theorem pow_smul_coe_liftAux {next} {n : ℕ} {m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)} (j : ℕ) {e : ℕ}
    (he : e = n + j) : ((p ^ e : ℕ) : ℤ) • (liftAux next n m j : M) = 0 := by
  subst he; exact (mem_torsionBy_iff _ _).mp (liftAux next n m j).2


theorem liftFun_mem
    {next : (k : ℕ) → torsionBy ℤ M ((p ^ k : ℕ) : ℤ) → torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ)}
    (hnext : ∀ k (m : torsionBy ℤ M ((p ^ k : ℕ) : ℤ)), ((p : ℕ) : ℤ) • (next k m : M) = m)
    (n : ℕ) (m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) : liftFun next n m ∈ TateModule p M := by
  intro k
  constructor
  · by_cases hk : n ≤ k
    · rw [liftFun_of_le hk]
      exact pow_smul_coe_liftAux (k - n) (by omega)
    · rw [liftFun_of_lt (not_le.mp hk)]
      exact (mem_torsionBy_iff _ _).mp (pow_smul_mem_torsionBy (not_le.mp hk).le m.2)
  · by_cases hk : n ≤ k
    · rw [liftFun_of_le hk, liftFun_of_le (by omega : n ≤ k + 1),
        coe_liftAux_congr (by omega : k + 1 - n = (k - n) + 1)]
      exact hnext _ _
    · by_cases hk' : n ≤ k + 1
      · have hn : n = k + 1 := by omega
        subst hn
        rw [liftFun_of_le le_rfl, liftFun_of_lt (by omega : k < k + 1),
          coe_liftAux_congr (Nat.sub_self _),
          Nat.add_sub_cancel_left, pow_one]
        rfl
      · rw [liftFun_of_lt (not_le.mp hk'), liftFun_of_lt (not_le.mp hk), smul_smul, ← Nat.cast_mul,
          ← pow_succ', show n - (k + 1) + 1 = n - k by omega]

end TateModule

end
