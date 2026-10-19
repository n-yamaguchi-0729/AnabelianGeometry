/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.CoverTransportFiber
import Nyll.EtaleFundamentalGroups.Cohomology.TransportedFiberTorsor
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticMap

/-!
# Original arithmetic transport from the actual geometric comparison

The arithmetic transported fiber is compared by composing its actual fiber
comparison, the two proved restriction comparisons, and the actual geometric
cover-transport equivalence. Only the coefficient action is transported;
the arithmetic finite-cover actions remain unchanged.
-/

noncomputable section
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale CategoryTheory
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

/-- Assemble the actual arithmetic transported-fiber isomorphism from the
proved restriction comparisons and the actual geometric transported fiber.
The target cover is a parameter: in the named application it is the SAME
power of the arithmetic unit as that of the geometric target unit. -/
theorem exists_arithmeticCoverTransport_geometricEquiv
    {k κ Ω₁ Ω₂ : Type} [Field k] [Field κ] [Field Ω₁] [Field Ω₂]
    [Algebra k κ] [IsSepClosure k κ] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    {Xs Xt Ys Yt : Scheme}
    [ConnectedSpace Xs] [ConnectedSpace Xt] [ConnectedSpace Ys] [ConnectedSpace Yt]
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
    (ps : Ys ⟶ Xs) (pt : Yt ⟶ Xt)
    (ys : Spec (.of Ω₁) ⟶ Ys) (yt : Spec (.of Ω₂) ⟶ Yt)
    (eP : π₁ᵉᵗ(ys ≫ ps) ≃ₜ* π₁ᵉᵗ(yt ≫ pt))
    (eΔ : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (hP : ∀ p, arithmeticFundamentalGroupHom k κ ft (yt ≫ pt) (eP p) =
      arithmeticFundamentalGroupHom k κ fs (ys ≫ ps) p)
    (hΔ : ∀ δ, fundamentalGroupHom pt yt (eΔ δ) =
      eP (fundamentalGroupHom ps ys δ))
    (n : ℕ) (AS : FiniteEtale Xs) (AT : FiniteEtale Xt)
    (GS : FiniteEtale Ys) (GT : FiniteEtale Yt)
    [Torsor (rootsOfUnity n κ) ((fiber (ys ≫ ps)).obj AS)]
    [Torsor (rootsOfUnity n κ) ((fiber (yt ≫ pt)).obj AT)]
    [Torsor (rootsOfUnity n κ) ((fiber ys).obj GS)]
    [Torsor (rootsOfUnity n κ) ((fiber yt).obj GT)]
    (ES : (fiber ys).obj GS ≃ (fiber (ys ≫ ps)).obj AS)
    (ET : (fiber yt).obj GT ≃ (fiber (yt ≫ pt)).obj AT)
    (hSμ : ∀ (ζ : rootsOfUnity n κ) x, ES (ζ • x) = ζ • ES x)
    (hTμ : ∀ (ζ : rootsOfUnity n κ) x, ET (ζ • x) = ζ • ET x)
    (hSH : ∀ (δ : π₁ᵉᵗ(ys)) x, ES (δ • x) = fundamentalGroupHom ps ys δ • ES x)
    (hTH : ∀ (δ : π₁ᵉᵗ(yt)) x, ET (δ • x) = fundamentalGroupHom pt yt δ • ET x)
    (hSsemi : ∀ (p : π₁ᵉᵗ(ys ≫ ps)) (ζ : rootsOfUnity n κ)
      (x : (fiber (ys ≫ ps)).obj AS),
      p • (ζ • x) =
        restrictRootsOfUnity (arithmeticFundamentalGroupHom k κ fs (ys ≫ ps) p).toRingHom
          n ζ • (p • x)) :
    let AG := (coverTransportOfAutEquiv (fiber (ys ≫ ps)) (fiber (yt ≫ pt)) eP).functor.obj AS
    let GG := (coverTransportOfAutEquiv (fiber ys) (fiber yt) eΔ).functor.obj GS
    let ea := coverTransportFiberEquiv (fiber (ys ≫ ps)) (fiber (yt ≫ pt)) eP AS
    let eg := coverTransportFiberEquiv (fiber ys) (fiber yt) eΔ GS
    let ta := transportedFiberTorsor ea
    let tg := transportedFiberTorsor eg
    ∀ (EG : (fiber yt).obj GG ≃ (fiber yt).obj GT),
      (∀ (ζ : rootsOfUnity n κ) x, EG (tg.toMulAction.toSMul.smul ζ x) = ζ • EG x) →
      (∀ (δ : π₁ᵉᵗ(yt)) x, EG (δ • x) = δ • EG x) →
      ∃ E : (fiber (yt ≫ pt)).obj AG ≃ (fiber (yt ≫ pt)).obj AT,
        (∀ (ζ : rootsOfUnity n κ) x,
          E (ta.toMulAction.toSMul.smul ζ x) = ζ • E x) ∧
        (∀ (δ : π₁ᵉᵗ(yt)) x,
          E (fundamentalGroupHom pt yt δ • x) = fundamentalGroupHom pt yt δ • E x) ∧
        ∀ (p : π₁ᵉᵗ(yt ≫ pt)) (ζ : rootsOfUnity n κ) x,
          p • (ta.toMulAction.toSMul.smul ζ x) =
            ta.toMulAction.toSMul.smul
              (restrictRootsOfUnity
                (arithmeticFundamentalGroupHom k κ ft (yt ≫ pt) p).toRingHom n ζ)
              (p • x) := by
  intro AG GG ea eg ta tg EG hGμ hGH
  have haμ (ζ : rootsOfUnity n κ) x : ea (ta.toMulAction.toSMul.smul ζ x) = ζ • ea x :=
    ea.apply_symm_apply _
  have hag (p : π₁ᵉᵗ(yt ≫ pt)) x : ea (p • x) = eP.symm p • ea x :=
    coverTransportFiberEquiv_smul (fiber (ys ≫ ps)) (fiber (yt ≫ pt)) eP AS p x
  have hSμinv (ζ : rootsOfUnity n κ) x : ES.symm (ζ • x) = ζ • ES.symm x := by
    apply ES.injective
    rw [ES.apply_symm_apply, hSμ, ES.apply_symm_apply]
  have hSHinv (δ : π₁ᵉᵗ(ys)) x :
      ES.symm (fundamentalGroupHom ps ys δ • x) = δ • ES.symm x := by
    apply ES.injective
    rw [ES.apply_symm_apply, hSH, ES.apply_symm_apply]
  have hgμinv (ζ : rootsOfUnity n κ) x :
      eg.symm (ζ • x) = tg.toMulAction.toSMul.smul ζ (eg.symm x) := by
    change eg.symm (ζ • x) = eg.symm (ζ • eg (eg.symm x))
    rw [eg.apply_symm_apply]
  have hgHinv (δ : π₁ᵉᵗ(yt)) x : eg.symm (eΔ.symm δ • x) = δ • eg.symm x :=
    coverTransportFiberEquiv_symm_smul (fiber ys) (fiber yt) eΔ GS δ x
  have hΔinv (δ : π₁ᵉᵗ(yt)) : eP.symm (fundamentalGroupHom pt yt δ) =
      fundamentalGroupHom ps ys (eΔ.symm δ) := by
    apply eP.injective
    rw [eP.apply_symm_apply]
    exact (congrArg (fundamentalGroupHom pt yt) (eΔ.apply_symm_apply δ)).symm.trans
      (hΔ (eΔ.symm δ))
  let E := ea.trans (ES.symm.trans (eg.symm.trans (EG.trans ET)))
  refine ⟨E, ?_, ?_, ?_⟩
  · intro ζ x
    change ET (EG (eg.symm (ES.symm (ea (ta.toMulAction.toSMul.smul ζ x))))) =
      ζ • ET (EG (eg.symm (ES.symm (ea x))))
    rw [haμ, hSμinv, hgμinv, hGμ, hTμ]
  · intro δ x
    change ET (EG (eg.symm (ES.symm (ea (fundamentalGroupHom pt yt δ • x))))) =
      fundamentalGroupHom pt yt δ • ET (EG (eg.symm (ES.symm (ea x))))
    rw [hag, hΔinv, hSHinv, hgHinv, hGH, hTH]
  · intro p ζ x
    apply ea.injective
    rw [hag, haμ, hSsemi, haμ, hag]
    have hq : arithmeticFundamentalGroupHom k κ fs (ys ≫ ps) (eP.symm p) =
        arithmeticFundamentalGroupHom k κ ft (yt ≫ pt) p :=
      (hP (eP.symm p)).symm.trans
        (congrArg (arithmeticFundamentalGroupHom k κ ft (yt ≫ pt)) (eP.apply_symm_apply p))
    rw [hq]

end AlgebraicGeometry.FiniteEtale
