/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.Algebra.Torsor.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.LocallyConstant.Basic

/-! # The arithmetic action on actual geometric torsor isomorphisms -/

noncomputable section
namespace EtaleFundamentalGroups.Cohomology

variable {P G A X Y : Type*} [Group P] [Group G] [CommGroup A]
  [MulDistribMulAction G A] [Torsor A X] [Torsor A Y]
  [MulAction P X] [MulAction P Y]

/-- Actual coefficient-equivariant isomorphisms intertwining the geometric
kernel action. The arithmetic action is not part of the input. -/
def KernelTorsorIso (q : P →* G) (A : Type*) [CommGroup A]
    [Torsor A X] [Torsor A Y] :=
  {e : X ≃ Y //
    (∀ (a : A) (x : X), e (a • x) = a • e x) ∧
    ∀ h : P, q h = 1 → ∀ x : X, e (h • x) = h • e x}

variable (q : P →* G)
  (hX : ∀ (p : P) (a : A) (x : X), p • (a • x) = (q p • a) • (p • x))
  (hY : ∀ (p : P) (a : A) (y : Y), p • (a • y) = (q p • a) • (p • y))

omit [MulDistribMulAction G A] in
/-- One actual fibre point determines a coefficient-equivariant map. -/
theorem KernelTorsorIso.ext_at (e f : KernelTorsorIso (X := X) (Y := Y) q A)
    (x₀ : X) (h : e.val x₀ = f.val x₀) : e = f := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  calc
    e.val x = e.val ((x /ₛ x₀ : A) • x₀) :=
      congrArg e.val (sdiv_smul x x₀).symm
    _ = (x /ₛ x₀ : A) • e.val x₀ := e.property.1 _ _
    _ = (x /ₛ x₀ : A) • f.val x₀ := congrArg ((x /ₛ x₀ : A) • ·) h
    _ = f.val ((x /ₛ x₀ : A) • x₀) := (f.property.1 _ _).symm
    _ = f.val x := congrArg f.val (sdiv_smul x x₀)

/-- Translate an actual kernel-equivariant isomorphism in its target torsor. -/
def kernelTorsorIsoTranslate (a : A) (e : KernelTorsorIso (X := X) (Y := Y) q A) :
    KernelTorsorIso (X := X) (Y := Y) q A :=
  ⟨e.val.trans (Equiv.constSMul Y a), by
    constructor
    · intro b x
      change a • e.val (b • x) = b • (a • e.val x)
      rw [e.property.1, ← mul_smul, ← mul_smul, mul_comm a b]
    · intro h hh x
      change a • e.val (h • x) = h • (a • e.val x)
      rw [e.property.2 h hh, hY, hh, one_smul]⟩

/-- Root translation on the original Isom set. -/
@[instance_reducible]
def kernelTorsorIsoMulAction : MulAction A (KernelTorsorIso (X := X) (Y := Y) q A) where
  smul := kernelTorsorIsoTranslate q hY
  one_smul e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact one_smul A (e.val x)
  mul_smul a b e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact mul_smul a b (e.val x)

/-- The actual Isom set is a root torsor once one geometric isomorphism exists. -/
@[instance_reducible]
def kernelTorsorIsoTorsor
    (e₀ : KernelTorsorIso (X := X) (Y := Y) q A) (x₀ : X) :
    Torsor A (KernelTorsorIso (X := X) (Y := Y) q A) where
  toMulAction := kernelTorsorIsoMulAction q hY
  sdiv e f := (e.val x₀) /ₛ (f.val x₀)
  nonempty := ⟨e₀⟩
  sdiv_smul' e f := by
    apply KernelTorsorIso.ext_at q _ _ x₀
    exact sdiv_smul (e.val x₀) (f.val x₀)
  smul_sdiv' a e := by
    exact smul_sdiv a (e.val x₀)

/-- Arithmetic conjugation of an actual geometric isomorphism. -/
def kernelTorsorIsoConjugate (p : P)
    (e : KernelTorsorIso (X := X) (Y := Y) q A) :
    KernelTorsorIso (X := X) (Y := Y) q A :=
  ⟨{ toFun := fun x => p • e.val (p⁻¹ • x)
     invFun := fun y => p • e.val.symm (p⁻¹ • y)
     left_inv := fun x => by simp only [inv_smul_smul, Equiv.symm_apply_apply, smul_inv_smul]
     right_inv := fun y => by simp only [inv_smul_smul, Equiv.apply_symm_apply, smul_inv_smul] }, by
    constructor
    · intro a x
      change p • e.val (p⁻¹ • (a • x)) = a • (p • e.val (p⁻¹ • x))
      rw [hX, e.property.1, hY, map_inv, smul_inv_smul]
    · intro h hh x
      let r : P := p⁻¹ * h * p
      have hr : q r = 1 := by simp [r, map_mul, map_inv, hh]
      have hs : p⁻¹ • (h • x) = r • (p⁻¹ • x) := by
        simp only [r, mul_smul, smul_inv_smul]
      change p • e.val (p⁻¹ • (h • x)) = h • (p • e.val (p⁻¹ • x))
      rw [hs, e.property.2 r hr]
      simp only [r, mul_smul, smul_inv_smul]⟩

/-- Conjugation is an action on the original Isom set. -/
@[instance_reducible]
def kernelTorsorIsoArithmeticAction :
    MulAction P (KernelTorsorIso (X := X) (Y := Y) q A) where
  smul := kernelTorsorIsoConjugate q hX hY
  one_smul e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (1 : P) • e.val ((1 : P)⁻¹ • x) = e.val x
    simp only [inv_one, one_smul]
  mul_smul p r e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (p * r) • e.val ((p * r)⁻¹ • x) =
      p • (r • e.val (r⁻¹ • (p⁻¹ • x)))
    simp only [mul_inv_rev, mul_smul]

/-- The geometric kernel acts trivially because its equivariance was proved
for the given geometric isomorphism, rather than assumed arithmetically. -/
theorem kernelTorsorIsoConjugate_kernel
    (h : P) (hh : q h = 1) (e : KernelTorsorIso (X := X) (Y := Y) q A) :
    kernelTorsorIsoConjugate q hX hY h e = e := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change h • e.val (h⁻¹ • x) = e.val x
  have hi : q h⁻¹ = 1 := by rw [map_inv, hh, inv_one]
  rw [e.property.2 h⁻¹ hi, smul_inv_smul]

/-- Arithmetic conjugation is semilinear for the prescribed quotient action
on roots of unity. -/
theorem kernelTorsorIsoConjugate_translate (p : P) (a : A)
    (e : KernelTorsorIso (X := X) (Y := Y) q A) :
    kernelTorsorIsoConjugate q hX hY p (kernelTorsorIsoTranslate q hY a e) =
      kernelTorsorIsoTranslate q hY (q p • a) (kernelTorsorIsoConjugate q hX hY p e) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact hY p a (e.val (p⁻¹ • x))

section Topology
variable [TopologicalSpace P] [IsTopologicalGroup P]
  [TopologicalSpace X] [DiscreteTopology X] [ContinuousSMul P X]
  [TopologicalSpace Y] [DiscreteTopology Y] [ContinuousSMul P Y]

/-- The displacement of an actual isomorphism under arithmetic conjugation
is locally constant, using continuity of the original finite fibre actions. -/
theorem isLocallyConstant_kernelTorsorIsoDisplacement
    (e₀ : KernelTorsorIso (X := X) (Y := Y) q A) (x₀ : X) :
    IsLocallyConstant (fun p : P =>
      ((kernelTorsorIsoConjugate q hX hY p e₀).val x₀) /ₛ (e₀.val x₀) : P → A) := by
  have hinner : Continuous (fun p : P => p⁻¹ • x₀) :=
    continuous_inv.smul continuous_const
  have heval : Continuous (fun p : P => p • e₀.val (p⁻¹ • x₀)) :=
    continuous_id.smul ((continuous_of_discreteTopology : Continuous e₀.val).comp hinner)
  have hlc : IsLocallyConstant (fun p : P => p • e₀.val (p⁻¹ • x₀)) :=
    (IsLocallyConstant.iff_continuous _).mpr heval
  exact hlc.comp (fun y : Y => (y /ₛ e₀.val x₀ : A))

end Topology
end EtaleFundamentalGroups.Cohomology
