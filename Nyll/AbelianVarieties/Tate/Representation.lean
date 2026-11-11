/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Anthropic's Fermat's Last Theorem formalization.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_EllipticCurve_TateModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

-- Source: Definitions/Def_EllipticCurve_TateModule.lean, lines 174–195 and 651–657.
module

public import Nyll.AbelianVarieties.Tate.PrimePower
public import Nyll.AbelianVarieties.Tate.Basis
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! Algebraic actions and functoriality for prime-power Tate modules. -/

@[expose] public section

universe u v w z

namespace TateModule

variable {p : ℕ} {M : Type u} [AddCommGroup M] [Fact p.Prime]
variable {G : Type v} [Monoid G] [DistribMulAction G M]

variable (p M G) in
/-- The induced algebraic action on compatible prime-power torsion sequences. -/
noncomputable def rep : G →* Module.End ℤ_[p] (TateModule p M) where
  toFun g :=
    { toFun := fun x => ⟨fun n => g • (x : ℕ → M) n, fun n =>
        ⟨by
          change ((p ^ n : ℕ) : ℤ) • DistribSMul.toAddMonoidHom M g ((x : ℕ → M) n) = 0
          rw [← map_zsmul, torsion, map_zero],
         by
          change ((p : ℕ) : ℤ) • DistribSMul.toAddMonoidHom M g ((x : ℕ → M) (n + 1)) = _
          rw [← map_zsmul, compat]; rfl⟩⟩
      map_add' := fun x y => Subtype.ext (funext fun n => by
        change g • ((x + y : TateModule p M) : ℕ → M) n = g • (x : ℕ → M) n + g • (y : ℕ → M) n
        rw [coe_add, Pi.add_apply, smul_add])
      map_smul' := fun a x => Subtype.ext (funext fun n => by
        change g • (((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n) =
          ((a.appr n : ℕ) : ℤ) • (g • (x : ℕ → M) n)
        exact map_zsmul (DistribSMul.toAddMonoidHom M g) _ _) }
  map_one' := LinearMap.ext fun x => Subtype.ext (funext fun n => one_smul G ((x : ℕ → M) n))
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (funext fun n => mul_smul g h ((x : ℕ → M) n))

@[simp] theorem rep_apply (g : G) (x : TateModule p M) (n : ℕ) :
    ((rep p M G g x : TateModule p M) : ℕ → M) n = g • (x : ℕ → M) n := rfl

theorem rep_eq_one_of_forall_torsionBy (g : G)
    (h : ∀ n : ℕ, ∀ m ∈ Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ), g • m = m) :
    rep p M G g = 1 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  rw [rep_apply, Module.End.one_apply]
  exact h n _ (proj_mem_torsionBy n x)

/-- Under the prime-power torsion cardinality condition, an element acts trivially on the
Tate module exactly when it fixes every finite prime-power torsion point.

The implication to finite torsion uses the constructed lifts to compatible sequences.
In particular, this applies to each element of an inertia subgroup. -/
theorem rep_eq_one_iff_forall_torsionBy (r : ℕ)
    (hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) (g : G) :
    rep p M G g = 1 ↔
      ∀ n : ℕ, ∀ m ∈ Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ), g • m = m := by
  constructor
  · intro hrep n m hm
    obtain ⟨x, hx⟩ := exists_proj_eq_of_mem_torsionBy p r hcard n m hm
    have hlevel := congrArg (fun φ : Module.End ℤ_[p] (TateModule p M) =>
      proj p M n (φ x)) hrep
    change g • proj p M n x = proj p M n x at hlevel
    simpa only [hx] using hlevel
  · exact rep_eq_one_of_forall_torsionBy g

section Functoriality

variable (p : ℕ) [Fact p.Prime] {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]

/-- An additive map of point groups induces a linear map on their
actual prime-power Tate modules. -/
def map (f : M →+ N) : TateModule p M →ₗ[ℤ_[p]] TateModule p N where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, torsion, map_zero],
      by rw [← map_zsmul, compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => f.map_add _ _)
  map_smul' a x := Subtype.ext (funext fun n =>
    map_zsmul f (((a.appr n : ℕ) : ℤ)) ((x : ℕ → M) n))

@[simp] theorem map_apply (f : M →+ N) (x : TateModule p M) (n : ℕ) :
    ((map p f x : TateModule p N) : ℕ → N) n = f ((x : ℕ → M) n) := rfl

/-- An additive equivalence of actual point groups induces an integral Tate-module equivalence. -/
def congr (e : M ≃+ N) : TateModule p M ≃ₗ[ℤ_[p]] TateModule p N :=
  { map p e.toAddMonoidHom with
    invFun := map p e.symm.toAddMonoidHom
    left_inv := fun x => Subtype.ext (funext fun n => e.symm_apply_apply ((x : ℕ → M) n))
    right_inv := fun x => Subtype.ext (funext fun n => e.apply_symm_apply ((x : ℕ → N) n)) }


/-- A point map that lifts every prime-power torsion point induces a
surjection of Tate modules when its source torsion levels are finite.
The lift sets form a finite inverse system; their transitions need not be surjective. -/
theorem map_surjective_of_surjective_on_torsion (f : M →+ N)
    (hfinite : ∀ n : ℕ, Finite (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)))
    (hlift : ∀ (n : ℕ) (y : N), ((p ^ n : ℕ) : ℤ) • y = 0 →
      ∃ x : M, ((p ^ n : ℕ) : ℤ) • x = 0 ∧ f x = y) :
    Function.Surjective (map p f) := by
  intro y
  let D (n : ℕ) := {x : M // ((p ^ n : ℕ) : ℤ) • x = 0 ∧ f x = (y : ℕ → N) n}
  have hfin : ∀ n, Finite (D n) := by
    intro n
    have := hfinite n
    apply Finite.of_injective
      (fun x : D n =>
        (⟨x.val, (Submodule.mem_torsionBy_iff _ _).mpr x.property.1⟩ :
          Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)))
    intro x z h
    apply Subtype.ext
    exact congrArg
      (fun t : Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ) => (t : M)) h
  have hne : ∀ n, Nonempty (D n) := by
    intro n
    obtain ⟨x, hx, hfx⟩ := hlift n ((y : ℕ → N) n) (torsion y n)
    exact ⟨⟨x, hx, hfx⟩⟩
  let step (n : ℕ) : D (n + 1) → D n := fun x =>
    ⟨((p : ℕ) : ℤ) • x.val, by
      rw [smul_smul, ← Nat.cast_mul, ← pow_succ]
      exact x.property.1, by
      rw [map_zsmul, x.property.2, compat]⟩
  let F : CategoryTheory.Functor (Opposite ℕ) (Type u) :=
    CategoryTheory.Functor.ofOpSequence (fun n => TypeCat.ofHom (step n))
  have : ∀ j : Opposite ℕ, Finite (F.obj j) := fun j => hfin j.unop
  have : ∀ j : Opposite ℕ, Nonempty (F.obj j) := fun j => hne j.unop
  obtain ⟨s, hs⟩ := _root_.nonempty_sections_of_finite_inverse_system F
  let x : TateModule p M := ⟨fun n => (s (Opposite.op n)).val, fun n => ⟨
    (s (Opposite.op n)).property.1, by
      have hstep := hs (CategoryTheory.homOfLE (Nat.le_add_right n 1)).op
      have hm : F.map (CategoryTheory.homOfLE (Nat.le_add_right n 1)).op =
          TypeCat.ofHom (step n) :=
        CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
      rw [hm] at hstep
      exact congrArg Subtype.val hstep⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext n
  exact (s (Opposite.op n)).property.2

/-- Tate transport preserves equivariance, including a change of the acting group. -/
theorem map_rep {G : Type w} {H : Type z} [Monoid G] [Monoid H]
    [DistribMulAction G M] [DistribMulAction H N]
    (f : M →+ N) (g : G) (h : H) (hf : ∀ m, f (g • m) = h • f m)
    (x : TateModule p M) :
    map p f (rep p M G g x) = rep p N H h (map p f x) :=
  Subtype.ext (funext fun n => hf ((x : ℕ → M) n))

/-- Equivariant comparison of point groups preserves triviality of each Tate operator. -/
theorem rep_eq_one_iff_of_equivariant {G : Type w} {H : Type z} [Monoid G] [Monoid H]
    [DistribMulAction G M] [DistribMulAction H N]
    (e : M ≃+ N) (g : G) (h : H) (he : ∀ m, e (g • m) = h • e m) :
    rep p M G g = 1 ↔ rep p N H h = 1 := by
  constructor
  · intro hg
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := (congr p e).surjective y
    change rep p N H h (map p e.toAddMonoidHom x) = map p e.toAddMonoidHom x
    rw [← map_rep p e.toAddMonoidHom g h he, hg, Module.End.one_apply]
  · intro hh
    apply LinearMap.ext
    intro x
    apply (congr p e).injective
    change map p e.toAddMonoidHom (rep p M G g x) = map p e.toAddMonoidHom x
    rw [map_rep p e.toAddMonoidHom g h he, hh, Module.End.one_apply]

end Functoriality

end TateModule
