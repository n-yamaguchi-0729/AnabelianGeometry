/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.KernelTorsorIsom
import Nyll.EtaleFundamentalGroups.Cohomology.SemilinearTorsorDescent
import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousKummerScalar
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticExactSequence
import Mathlib.Topology.Separation.Hausdorff

/-! # Scalar radical from an actual arithmetic kernel-torsor isomorphism

The original finite-etale fiber actions give an arithmetic action on the
actual geometric isomorphism torsor. Its displacement descends through the
arithmetic exact sequence, and continuous Hilbert 90 supplies a base scalar.
The pointwise conclusion retains the original conjugation displacement.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale groupCohomology
open scoped FintypeCatDiscrete

namespace EtaleFundamentalGroups.Cohomology

/-- The literal cyclotomic action used by the generic-semilinearity
leaf, packaged only as the class required by the torsor API. -/
@[instance_reducible]
private def rootsGaloisAction
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] (n : ℕ) :
    MulDistribMulAction Gal(κ/k) (rootsOfUnity n κ) where
  smul σ ζ := restrictRootsOfUnity σ.toRingHom n ζ
  one_smul ζ := by
    apply Subtype.ext
    apply Units.ext
    rfl
  mul_smul σ τ ζ := by
    apply Subtype.ext
    apply Units.ext
    rfl
  smul_one σ := (restrictRootsOfUnity σ.toRingHom n).map_one
  smul_mul σ ζ ε := (restrictRootsOfUnity σ.toRingHom n).map_mul ζ ε

section ActualFibers

variable
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X : Scheme) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)

local notation "η" => (xi ≫ Limits.pullback.snd _ f)
local notation "arithQ" => arithmeticFundamentalGroupHom k κ f η
local notation "geomI" => fundamentalGroupHom (Limits.pullback.snd _ f) xi

/-- A coefficient-equivariant geometric isomorphism between the two actual
arithmetic torsors determines a base scalar.  The conclusion keeps the
original arithmetic conjugation displacement pointwise; it does not assume
or claim an identification of the eventual geometric Kummer scalar. -/
theorem exists_scalar_radical_of_actual_kernelTorsorIso
    (n : ℕ) (W₁ W₂ : FiniteEtale X)
    [Torsor (rootsOfUnity n κ) ((fiber η).obj W₁)]
    [Torsor (rootsOfUnity n κ) ((fiber η).obj W₂)]
    (h₁ : ∀ (p : π₁ᵉᵗ(η)) (ζ : rootsOfUnity n κ) (x : (fiber η).obj W₁),
      p • (ζ • x) = (restrictRootsOfUnity (arithQ p).toRingHom n ζ) • (p • x))
    (h₂ : ∀ (p : π₁ᵉᵗ(η)) (ζ : rootsOfUnity n κ) (y : (fiber η).obj W₂),
      p • (ζ • y) = (restrictRootsOfUnity (arithQ p).toRingHom n ζ) • (p • y))
    (e : (fiber η).obj W₁ ≃ (fiber η).obj W₂)
    (heμ : ∀ (ζ : rootsOfUnity n κ) x, e (ζ • x) = ζ • e x)
    (heH : ∀ (δ : π₁ᵉᵗ(xi)) x, e (geomI δ • x) = geomI δ • e x)
    (x₀ : (fiber η).obj W₁) :
    ∃ a : kˣ, ∃ β : κˣ,
      β ^ n = Units.map (algebraMap k κ).toMonoidHom a ∧
      ∀ p : π₁ᵉᵗ(η), KummerTheory.rootQuotient (K := k) β (arithQ p) =
        ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity n κ).val := by
  let A := rootsOfUnity n κ
  let P := π₁ᵉᵗ(η)
  let qm := (arithQ).toMonoidHom
  let := rootsGaloisAction k κ n
  have hX : ∀ (p : P) (ζ : A) (x : (fiber η).obj W₁),
      p • (ζ • x) = (qm p • ζ) • (p • x) := h₁
  have hY : ∀ (p : P) (ζ : A) (y : (fiber η).obj W₂),
      p • (ζ • y) = (qm p • ζ) • (p • y) := h₂
  have hex := arithmetic_exactSequence_of_isSepClosure k κ X f xi
  have hq : Function.Surjective qm := hex.2.1
  have heker : ∀ p : P, qm p = 1 → ∀ x, e (p • x) = p • e x := by
    intro p hp x
    have hpker : p ∈ qm.ker := hp
    have hprange : p ∈ (geomI).toMonoidHom.range := hex.2.2 ▸ hpker
    obtain ⟨δ, rfl⟩ := hprange
    exact heH δ x
  let I := KernelTorsorIso (X := (fiber η).obj W₁)
    (Y := (fiber η).obj W₂) qm A
  let e₀ : I := ⟨e, heμ, heker⟩
  let : Torsor A I := kernelTorsorIsoTorsor qm hY e₀ x₀
  let : MulAction P I := kernelTorsorIsoArithmeticAction qm hX hY
  have hker : ∀ p : P, qm p = 1 → ∀ t : I, p • t = t := by
    intro p hp t
    exact kernelTorsorIsoConjugate_kernel qm hX hY p hp t
  have hsemi : ∀ (p : P) (ζ : A) (t : I),
      p • (ζ • t) = (qm p • ζ) • (p • t) := by
    intro p ζ t
    exact kernelTorsorIsoConjugate_translate qm hX hY p ζ t
  let c : Gal(κ/k) → A := descendedTorsorCocycle qm hq e₀
  have hc : IsMulCocycle₁ c :=
    isMulCocycle_descendedTorsorCocycle (q := qm) (hq := hq)
      (hker := hker) (hsemi := hsemi) e₀
  have hquot : Topology.IsQuotientMap qm :=
    Topology.IsQuotientMap.of_surjective_continuous hq (arithQ).continuous
  have hdisp : IsLocallyConstant (semilinearDisplacement e₀ : P → A) :=
    isLocallyConstant_kernelTorsorIsoDisplacement qm hX hY e₀ x₀
  have hlc : IsLocallyConstant c :=
    isLocallyConstant_descendedTorsorCocycle_of_displacement
      (q := qm) (hq := hq) (hker := hker) (hsemi := hsemi) hquot e₀ hdisp
  let cu : Gal(κ/k) → κˣ := fun σ => (c σ).val
  have hcu : IsMulCocycle₁ cu := by
    intro σ τ
    exact congrArg (fun ζ : A => ζ.val) (hc σ τ)
  have hculc : IsLocallyConstant cu := hlc.comp (fun ζ : A => ζ.val)
  have hcun (σ : Gal(κ/k)) : cu σ ^ n = 1 :=
    (mem_rootsOfUnity n (cu σ)).mp (c σ).property
  obtain ⟨a, β, hβn, hβ⟩ :=
    KummerTheory.exists_scalar_radical_of_isLocallyConstant_mulCocycle
      n cu hcu hculc hcun
  refine ⟨a, β, hβn, ?_⟩
  intro p
  have hcp := descendedTorsorCocycle_apply_quotient
    (q := qm) (hq := hq) (hker := hker) (hsemi := hsemi) e₀ p
  exact (hβ (arithQ p)).trans (congrArg (fun ζ : A => ζ.val) hcp)

end ActualFibers
end EtaleFundamentalGroups.Cohomology
