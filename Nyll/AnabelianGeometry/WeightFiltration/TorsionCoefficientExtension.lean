/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TorsionTateSpecialization
import Nyll.ProCGroups.Abelian.FullTateModuleMap
import Mathlib.RingTheory.Adjoin.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual torsion coefficient extension from an algebraically closed field

Integral algebra maps descend uniquely through an algebraically closed
coefficient field. Applying this to actual finite kernel sections makes the
original coefficient maps equivalences, with their original transitions and
actions. Both coefficient fields must be algebras over the same model base.
-/

noncomputable section

namespace AnabelianGeometry.WeightFiltration

/-- Postcomposition through an algebraically closed coefficient field is
bijective on maps from an integral algebra over any commutative base. -/
theorem algHom_postcomp_bijective
    {R B Ω L : Type*} [CommRing R] [CommRing B] [Field Ω] [Field L]
    [Algebra R B] [Algebra R Ω] [Algebra R L]
    [Algebra.IsIntegral R B] [IsAlgClosed Ω] (i : Ω →ₐ[R] L) :
    Function.Bijective (fun a : B →ₐ[R] Ω => i.comp a) := by
  constructor
  · intro a b h
    apply AlgHom.ext
    intro z
    apply i.injective
    exact congrArg (fun q : B →ₐ[R] L => q z) h
  · intro a
    have ha : ∀ b : B, a b ∈ i.range := by
      intro b
      exact ((Algebra.IsIntegral.isIntegral b).map a).mem_range_algHom_of_minpoly_splits
        (IsAlgClosed.splits _) i
    let e : Ω ≃ₐ[R] i.range := AlgEquiv.ofInjective i i.injective
    let a' : B →ₐ[R] i.range := a.codRestrict i.range ha
    refine ⟨e.symm.toAlgHom.comp a', ?_⟩
    apply AlgHom.ext
    intro b
    change i (e.symm (a' b)) = a b
    exact congrArg (fun z : i.range => (z : L)) (e.apply_symm_apply (a' b))

end AnabelianGeometry.WeightFiltration

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale ProCGroups

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] [IsLocalRing H]
  {A : Scheme} {f : A ⟶ Spec (.of H)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)
  {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Field L] [Algebra H Ω] [Algebra H L]

/-- The original coefficient extension is bijective at every unit torsion level. -/
theorem torsionCoefficientMap_bijective (i : Ω →ₐ[H] L)
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    Function.Bijective (G.torsionCoefficientMap hc i n) := by
  let X := G.unitTorsionCover hc n hn
  have : Module.Finite H Γ(X.left, ⊤) := sections_moduleFinite H X
  have hbij := AnabelianGeometry.WeightFiltration.algHom_postcomp_bijective
    (B := Γ(X.left, ⊤)) i
  let eΩ := G.torsionLevelEquivKernelSections hc Ω n hn
  let eL := G.torsionLevelEquivKernelSections hc L n hn
  constructor
  · intro x y h
    apply eΩ.injective
    apply hbij.1
    change i.comp (eΩ x) = i.comp (eΩ y)
    exact (G.torsionLevelEquivKernelSections_map hc i n hn x).symm.trans
      ((congrArg eL h).trans (G.torsionLevelEquivKernelSections_map hc i n hn y))
  · intro y
    obtain ⟨a, ha⟩ := hbij.2 (eL y)
    refine ⟨eΩ.symm a, ?_⟩
    apply eL.injective
    calc
      eL (G.torsionCoefficientMap hc i n (eΩ.symm a)) =
          i.comp (eΩ (eΩ.symm a)) :=
        G.torsionLevelEquivKernelSections_map hc i n hn (eΩ.symm a)
      _ = i.comp a := congrArg (fun b => i.comp b) (eΩ.apply_symm_apply a)
      _ = eL y := ha

/-- The additive equivalence has the original coefficient map as its forward map. -/
def torsionCoefficientEquiv (i : Ω →ₐ[H] L)
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    torsionLevel (G.AlgPoints hc Ω) n ≃+ torsionLevel (G.AlgPoints hc L) n :=
  AddEquiv.ofBijective (G.torsionCoefficientMap hc i n)
    (G.torsionCoefficientMap_bijective hc i n hn)

/-- Actual coefficient extension is a continuous restricted Tate equivalence. -/
def restrictedTateCoefficientEquiv (i : Ω →ₐ[H] L)
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H)) :
    Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω) I) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I) :=
  RestrictedTateModule.equivLevels (fun n => G.torsionCoefficientEquiv hc i n.1 (hI n))
    (fun n m x => G.torsionCoefficientMap_transition hc i n.1 m.1 x)

omit [IsLocalRing H] [IsProper f] [Smooth f] [IsAlgClosed Ω] in
/-- Compatible field automorphisms intertwine the original torsion coefficient maps. -/
theorem torsionCoefficientMap_equivariant (i : Ω →ₐ[H] L)
    (σ : Ω ≃ₐ[H] Ω) (τ : L ≃ₐ[H] L)
    (hi : ∀ z, i (σ z) = τ (i z)) (n : ℕ+)
    (x : torsionLevel (G.AlgPoints hc Ω) n) :
    G.torsionCoefficientMap hc i n (G.torsionCoefficientMap hc σ.toAlgHom n x) =
      G.torsionCoefficientMap hc τ.toAlgHom n (G.torsionCoefficientMap hc i n x) := by
  have hcomp : i.comp σ.toAlgHom = τ.toAlgHom.comp i := AlgHom.ext hi
  apply Subtype.ext
  change ((AlgPoints.map i).comp (AlgPoints.map σ.toAlgHom)) x.val =
    ((AlgPoints.map τ.toAlgHom).comp (AlgPoints.map i)) x.val
  rw [← AlgPoints.map_comp, ← AlgPoints.map_comp, hcomp]

/-- Injectivity on actual finite torsion levels detects the full Tate
family, without identifying all points over the two coefficient fields. -/
theorem fullTateCoefficientMap_injective (i : Ω →ₐ[H] L)
    (hunit : ∀ n : ℕ+, IsUnit ((n : ℕ) : H)) :
    Function.Injective (FullTateModule.map (AlgPoints.map (L := G) (hc := hc) i)) := by
  intro x y hxy
  apply FullTateModule.ext
  intro n
  have h := congrArg (FullTateModule.projection (G.AlgPoints hc L) n) hxy
  have hlevel : G.torsionCoefficientMap hc i n (FullTateModule.projection _ n x) =
      G.torsionCoefficientMap hc i n (FullTateModule.projection _ n y) := h
  exact congrArg Subtype.val ((G.torsionCoefficientMap_bijective hc i n (hunit n)).1 hlevel)

end GoodReductionJacobian.RelativeGroupLaw
