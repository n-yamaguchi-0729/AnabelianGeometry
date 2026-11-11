/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Nyll.ProCGroups.Abelian.PrimePowerCharacters
public import Nyll.ProCGroups.Topologies.Conjugation
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# Displacements of decomposition groups in an abelian geometric kernel

Let `A` be a normal abelian subgroup of an arithmetic group `P`, and let `D`
be a decomposition subgroup. Its inertia inside `A` is the actual intersection
`D.subgroupOf A`. Conjugation by `D` acts on the quotient by this intersection.
The geometric normalizer of `D` is exactly the inverse image of the classes
fixed by all these conjugations. In particular, fixed vanishing for one
arithmetic lift separates two points in an `A`-orbit with equal stabilizers.

These are group-theoretic statements. The fixed-vanishing input is explicit;
no geometric fixed-vanishing supplier or reconstruction theorem is asserted.
The inertia intersection is unrestricted, including wild inertia.

The final auxiliary derives fixed vanishing for an abelian pro-p group from
surjectivity of Frobenius minus identity on its finite cyclic characters.
-/

@[expose] public section

namespace AnabelianGeometry.FiniteField

universe u v

variable {P : Type u} [Group P]
variable (A D : Subgroup P) [A.Normal]

/-- Actual decomposition conjugation preserves the actual geometric inertia
intersection. No hypothesis on the structure of inertia is used. -/
theorem decompositionInertia_map_conjNormal (d : D) :
    (D.subgroupOf A).map (MulAut.conjNormal (d : P)).toMonoidHom =
      D.subgroupOf A := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change (d : P) * (y : P) * (d : P)⁻¹ ∈ D
    exact D.mul_mem (D.mul_mem d.property hy) (D.inv_mem d.property)
  · intro x hx
    refine ⟨(MulAut.conjNormal (d : P)).symm x, ?_, ?_⟩
    · change (((MulAut.conjNormal (d : P)).symm x : A) : P) ∈ D
      rw [MulAut.conjNormal_symm_apply]
      exact D.mul_mem (D.mul_mem (D.inv_mem d.property) hx) d.property
    · exact (MulAut.conjNormal (d : P)).apply_symm_apply x

variable [IsMulCommutative A]

/-- Conjugation on the actual geometric quotient by decomposition inertia. -/
def decompositionInertiaQuotientConj (d : D) :
    MulAut (A ⧸ D.subgroupOf A) :=
  QuotientGroup.congr (D.subgroupOf A) (D.subgroupOf A)
    (MulAut.conjNormal (d : P)) (decompositionInertia_map_conjNormal A D d)

/-- The quotient action is induced by the original ambient conjugation. -/
theorem decompositionInertiaQuotientConj_mk (d : D) (a : A) :
    decompositionInertiaQuotientConj A D d (QuotientGroup.mk a) =
      QuotientGroup.mk (MulAut.conjNormal (d : P) a) := rfl

section Topology

variable [TopologicalSpace P] [IsTopologicalGroup P]

/-- The same original quotient conjugation is continuous for the inherited
subgroup and quotient topologies. Its map on representatives is unchanged. -/
noncomputable def decompositionInertiaQuotientContinuousConj (d : D) :
    (A ⧸ D.subgroupOf A) ≃ₜ* (A ⧸ D.subgroupOf A) :=
  ProCGroups.QuotientGroup.congrₜ (D.subgroupOf A) (D.subgroupOf A)
    (ProCGroups.Subgroup.conjNormalContinuousMulEquiv A (d : P))
    (decompositionInertia_map_conjNormal A D d)

/-- The continuous quotient action is the original algebraic action on
every class, so its fixed elements retain the specified decomposition lift. -/
theorem decompositionInertiaQuotientContinuousConj_apply
    (d : D) (q : A ⧸ D.subgroupOf A) :
    decompositionInertiaQuotientContinuousConj A D d q =
      decompositionInertiaQuotientConj A D d q := rfl

end Topology

/-- A geometric displacement class is fixed precisely when its original
inverse conjugate of the decomposition element still belongs to `D`. -/
theorem decompositionInertiaQuotientConj_fixed_iff (d : D) (a : A) :
    decompositionInertiaQuotientConj A D d (QuotientGroup.mk a) =
        QuotientGroup.mk a ↔
      (a : P)⁻¹ * (d : P) * (a : P) ∈ D := by
  rw [decompositionInertiaQuotientConj_mk, eq_comm, QuotientGroup.eq]
  change (a : P)⁻¹ * ((d : P) * (a : P) * (d : P)⁻¹) ∈ D ↔
    (a : P)⁻¹ * (d : P) * (a : P) ∈ D
  constructor
  · intro h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using D.mul_mem h d.property
  · intro h
    simpa only [mul_assoc] using D.mul_mem h (D.inv_mem d.property)

/-- The geometric normalizer is the inverse image of the simultaneous fixed
classes in the actual inertia quotient. The reverse implication also uses
inverses in that quotient, so it proves equality rather than one inclusion. -/
theorem mem_normalizer_iff_decompositionInertiaQuotient_fixed (a : A) :
    (a : P) ∈ Subgroup.normalizer D ↔
      ∀ d : D, decompositionInertiaQuotientConj A D d (QuotientGroup.mk a) =
        QuotientGroup.mk a := by
  constructor
  · intro ha d
    apply (decompositionInertiaQuotientConj_fixed_iff A D d a).mpr
    exact (Subgroup.mem_normalizer_iff''.mp ha (d : P)).mp d.property
  · intro h
    have hinv (d : D) :
        decompositionInertiaQuotientConj A D d (QuotientGroup.mk a⁻¹) =
          QuotientGroup.mk a⁻¹ := by
      change decompositionInertiaQuotientConj A D d
        ((QuotientGroup.mk a : A ⧸ D.subgroupOf A)⁻¹) =
          (QuotientGroup.mk a : A ⧸ D.subgroupOf A)⁻¹
      rw [map_inv, h d]
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      simpa only [Subgroup.coe_inv, inv_inv] using
        (decompositionInertiaQuotientConj_fixed_iff A D ⟨x, hx⟩ a⁻¹).mp
          (hinv ⟨x, hx⟩)
    · intro hx
      have hm := (decompositionInertiaQuotientConj_fixed_iff A D
        ⟨(a : P) * x * (a : P)⁻¹, hx⟩ a).mp
          (h ⟨(a : P) * x * (a : P)⁻¹, hx⟩)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hm

/-- Fixed vanishing for one decomposition element suffices to identify the
entire geometric normalizer with the original inertia intersection. -/
theorem normalizer_subgroupOf_eq_inertia_of_no_fixed (d : D)
    (hfixed : ∀ q : A ⧸ D.subgroupOf A,
      decompositionInertiaQuotientConj A D d q = q → q = 1) :
    (Subgroup.normalizer D).subgroupOf A = D.subgroupOf A := by
  ext a
  constructor
  · intro ha
    apply (QuotientGroup.eq_one_iff a).mp
    exact hfixed (QuotientGroup.mk a)
      ((mem_normalizer_iff_decompositionInertiaQuotient_fixed A D a).mp ha d)
  · intro ha
    exact D.le_normalizer ha

/-- For the original point action, equal stabilizers of two points related
by a geometric displacement force that displacement to fix the point,
provided the actual stabilizer-inertia quotient has no fixed classes. -/
theorem smul_eq_of_stabilizer_eq_of_no_fixed
    {X : Type v} [MulAction P X] (x : X) (a : A)
    (d : MulAction.stabilizer P x)
    (hfixed : ∀ q : A ⧸ (MulAction.stabilizer P x).subgroupOf A,
      decompositionInertiaQuotientConj A (MulAction.stabilizer P x) d q = q → q = 1)
    (hst : MulAction.stabilizer P ((a : P) • x) = MulAction.stabilizer P x) :
    (a : P) • x = x := by
  have ha : (a : P) ∈ Subgroup.normalizer (MulAction.stabilizer P x) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj (a : P) x).symm.trans hst
  have hai : a ∈ (MulAction.stabilizer P x).subgroupOf A := by
    rw [← normalizer_subgroupOf_eq_inertia_of_no_fixed A
      (MulAction.stabilizer P x) d hfixed]
    exact ha
  exact hai

end AnabelianGeometry.FiniteField

namespace ProCGroups.Abelian

universe u

/-- Surjectivity of pullback minus identity on every continuous cyclic
p-power character kills all fixed elements of an abelian pro-p group.
The character detecting a hypothetical nonidentity element is constructed
from its original open normal finite quotients. -/
theorem fixed_eq_one_of_primePower_character_difference_surjective
    {p : ℕ} [Fact p.Prime]
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A]
    (hA : ProC.HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) A)
    (F : A →ₜ* A)
    (hsurj : ∀ n : ℕ, 0 < n → Function.Surjective
      (fun χ : A →ₜ* Multiplicative (ZMod (p ^ n)) => χ.comp F / χ))
    {a : A} (ha : F a = a) : a = 1 := by
  by_contra hne
  obtain ⟨n, hn, χ, hχ⟩ := exists_primePower_character_proP hA hne
  obtain ⟨ψ, hψ⟩ := hsurj n hn χ
  have heval := congrArg (fun η : A →ₜ* Multiplicative (ZMod (p ^ n)) => η a) hψ
  change ψ (F a) / ψ a = χ a at heval
  rw [ha, div_self'] at heval
  exact hχ heval.symm

end ProCGroups.Abelian
