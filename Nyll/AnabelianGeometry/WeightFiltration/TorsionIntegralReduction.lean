/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TorsionCoefficientMaps

/-!
# Integral lifting and reduction of actual torsion groups

At every invertible index, extension to the fraction field and henselian
reduction are additive equivalences. Both forward maps are the original
coefficient maps on algebra-valued points.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] [IsLocalRing H]
  {A : Scheme} {f : A ⟶ Spec (.of H)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)

section Generic

variable (R L : Type) [CommRing R] [IsIntegrallyClosed R] [Field L]
  [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]

/-- Extension from the normal ring to its fraction field is an additive
bijection on actual torsion at an invertible index. -/
def torsionGenericEquiv (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    ProCGroups.torsionLevel (G.AlgPoints hc R) n ≃+
      ProCGroups.torsionLevel (G.AlgPoints hc L) n := by
  let X := G.unitTorsionCover hc n hn
  have : Module.Finite H Γ(X.left, ⊤) := sections_moduleFinite H X
  let eR := G.torsionLevelEquivKernelSections hc R n hn
  let eL := G.torsionLevelEquivKernelSections hc L n hn
  let e := eR.trans ((SchemeTheory.integralPointEquiv H R L Γ(X.left, ⊤)).trans eL.symm)
  let a := IsScalarTower.toAlgHom H R L
  have he : ∀ x, e x = G.torsionCoefficientMap hc a n x := by
    intro x
    apply eL.injective
    change eL (eL.symm (a.comp (eR x))) = _
    rw [Equiv.apply_symm_apply]
    exact (G.torsionLevelEquivKernelSections_map hc a n hn x).symm
  exact AddEquiv.ofBijective (G.torsionCoefficientMap hc a n)
    ((funext he) ▸ e.bijective)

@[simp] theorem torsionGenericEquiv_apply (n : ℕ+) (hn : IsUnit ((n : ℕ) : H))
    (x : ProCGroups.torsionLevel (G.AlgPoints hc R) n) :
    G.torsionGenericEquiv hc R L n hn x =
      G.torsionCoefficientMap hc (IsScalarTower.toAlgHom H R L) n x := rfl

end Generic

section Reduction

variable (R : Type) [CommRing R] [HenselianLocalRing R] [Algebra H R]

/-- Henselian reduction is an additive bijection on actual torsion at an
invertible index, with the native residue-field algebra structure. -/
def torsionReductionEquiv (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    ProCGroups.torsionLevel (G.AlgPoints hc R) n ≃+
      ProCGroups.torsionLevel (G.AlgPoints hc (IsLocalRing.ResidueField R)) n := by
  let X := G.unitTorsionCover hc n hn
  let eR := G.torsionLevelEquivKernelSections hc R n hn
  let ek := G.torsionLevelEquivKernelSections hc (IsLocalRing.ResidueField R) n hn
  let e := eR.trans
    ((SchemeTheory.henselianPointReductionEquiv H R Γ(X.left, ⊤)).trans ek.symm)
  let a := IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R)
  have he : ∀ x, e x = G.torsionCoefficientMap hc a n x := by
    intro x
    apply ek.injective
    change ek (ek.symm (a.comp (eR x))) = _
    rw [Equiv.apply_symm_apply]
    exact (G.torsionLevelEquivKernelSections_map hc a n hn x).symm
  exact AddEquiv.ofBijective (G.torsionCoefficientMap hc a n)
    ((funext he) ▸ e.bijective)

@[simp] theorem torsionReductionEquiv_apply (n : ℕ+) (hn : IsUnit ((n : ℕ) : H))
    (x : ProCGroups.torsionLevel (G.AlgPoints hc R) n) :
    G.torsionReductionEquiv hc R n hn x =
      G.torsionCoefficientMap hc
        (IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R)) n x := rfl

end Reduction

/-- Actual specialization is an additive equivalence of torsion groups. -/
def torsionSpecializationAddEquiv
    (R L : Type) [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
    [Field L] [Algebra H R] [Algebra R L] [IsFractionRing R L]
    [Algebra H L] [IsScalarTower H R L]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    ProCGroups.torsionLevel (G.AlgPoints hc L) n ≃+
      ProCGroups.torsionLevel (G.AlgPoints hc (IsLocalRing.ResidueField R)) n :=
  (G.torsionGenericEquiv hc R L n hn).symm.trans (G.torsionReductionEquiv hc R n hn)

/-- Actual torsion specialization commutes with the multiplication transitions. -/
theorem torsionSpecializationAddEquiv_transition
    (R L : Type) [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
    [Field L] [Algebra H R] [Algebra R L] [IsFractionRing R L]
    [Algebra H L] [IsScalarTower H R L]
    (n m : ℕ+) (hn : IsUnit ((n : ℕ) : H))
    (hnm : IsUnit (((n * m : ℕ+) : ℕ) : H))
    (x : ProCGroups.torsionLevel (G.AlgPoints hc L) (n * m)) :
    ProCGroups.torsionTransition (G.AlgPoints hc (IsLocalRing.ResidueField R)) n m
        (G.torsionSpecializationAddEquiv hc R L (n * m) hnm x) =
      G.torsionSpecializationAddEquiv hc R L n hn
        (ProCGroups.torsionTransition (G.AlgPoints hc L) n m x) := by
  obtain ⟨y, rfl⟩ := (G.torsionGenericEquiv hc R L (n * m) hnm).surjective x
  have hg := G.torsionCoefficientMap_transition hc (IsScalarTower.toAlgHom H R L) n m y
  change ProCGroups.torsionTransition (G.AlgPoints hc L) n m
      (G.torsionGenericEquiv hc R L (n * m) hnm y) =
    G.torsionGenericEquiv hc R L n hn
      (ProCGroups.torsionTransition (G.AlgPoints hc R) n m y) at hg
  simp only [torsionSpecializationAddEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  rw [hg, AddEquiv.symm_apply_apply]
  exact G.torsionCoefficientMap_transition hc
    (IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R)) n m y

/-- Specialization respects compatible automorphisms of the normal ring and
its fraction field, with the native induced residue action. -/
theorem torsionSpecializationAddEquiv_equivariant
    (R L : Type) [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
    [Field L] [Algebra H R] [Algebra R L] [IsFractionRing R L]
    [Algebra H L] [IsScalarTower H R L]
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H))
    (x : ProCGroups.torsionLevel (G.AlgPoints hc L) n) :
    G.torsionSpecializationAddEquiv hc R L n hn
        (G.torsionCoefficientMap hc σ.toAlgHom n x) =
      G.torsionCoefficientMap hc (SchemeTheory.residueAlgEquiv H R τ).toAlgHom n
        (G.torsionSpecializationAddEquiv hc R L n hn x) := by
  obtain ⟨y, rfl⟩ := (G.torsionGenericEquiv hc R L n hn).surjective x
  have hcomp : σ.toAlgHom.comp (IsScalarTower.toAlgHom H R L) =
      (IsScalarTower.toAlgHom H R L).comp τ.toAlgHom := by
    ext r
    exact hσ r
  have hg : G.torsionCoefficientMap hc σ.toAlgHom n
      (G.torsionGenericEquiv hc R L n hn y) =
    G.torsionGenericEquiv hc R L n hn (G.torsionCoefficientMap hc τ.toAlgHom n y) := by
    apply Subtype.ext
    change AlgPoints.map σ.toAlgHom
        (AlgPoints.map (IsScalarTower.toAlgHom H R L) y.1) =
      AlgPoints.map (IsScalarTower.toAlgHom H R L) (AlgPoints.map τ.toAlgHom y.1)
    have h₁ := congrArg
      (fun b : G.AlgPoints hc R →+ G.AlgPoints hc L => b y.1)
      (AlgPoints.map_comp (L := G) (hc := hc)
        (IsScalarTower.toAlgHom H R L) σ.toAlgHom)
    have h₂ := congrArg
      (fun b : G.AlgPoints hc R →+ G.AlgPoints hc L => b y.1)
      (AlgPoints.map_comp (L := G) (hc := hc)
        τ.toAlgHom (IsScalarTower.toAlgHom H R L))
    rw [hcomp] at h₁
    exact h₁.symm.trans h₂
  rw [hg]
  simp only [torsionSpecializationAddEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  apply Subtype.ext
  change AlgPoints.map (IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R))
      (AlgPoints.map τ.toAlgHom y.1) =
    AlgPoints.map (SchemeTheory.residueAlgEquiv H R τ).toAlgHom
      (AlgPoints.map (IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R)) y.1)
  have hred : (IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R)).comp τ.toAlgHom =
      (SchemeTheory.residueAlgEquiv H R τ).toAlgHom.comp
        (IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R)) := by
    ext r
    exact (SchemeTheory.residueAlgEquiv_residue H R τ r).symm
  have h₁ := congrArg
    (fun b : G.AlgPoints hc R →+ G.AlgPoints hc (IsLocalRing.ResidueField R) => b y.1)
    (AlgPoints.map_comp (L := G) (hc := hc) τ.toAlgHom
      (IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R)))
  have h₂ := congrArg
    (fun b : G.AlgPoints hc R →+ G.AlgPoints hc (IsLocalRing.ResidueField R) => b y.1)
    (AlgPoints.map_comp (L := G) (hc := hc)
      (IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R))
      (SchemeTheory.residueAlgEquiv H R τ).toAlgHom)
  rw [hred] at h₁
  exact h₁.symm.trans h₂

end GoodReductionJacobian.RelativeGroupLaw
