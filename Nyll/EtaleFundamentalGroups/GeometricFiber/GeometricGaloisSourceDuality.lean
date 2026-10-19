/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoConjugation
import Nyll.EtaleFundamentalGroups.Cohomology.DeckAbelianH1Duality

/-!
# Source-induced arithmetic conjugation and actual H¹ duality

The original geometric-kernel comparison identifies source-induced scheme
pullback with arithmetic conjugation. The existing H¹ duality then supplies
the cohomological formula, retaining the actual arithmetic Galois label.
-/

noncomputable section

universe u

open CategoryTheory Limits CategoryTheory.PreGaloisCategory
open ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

private theorem autHomOfCompIso_pointed_source
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (θ : S ⟶ S) (xi y : Spec (.of Ω) ⟶ S) (h : xi ≫ θ = y)
    (s : fiber xi ≅ fiber y) (v : Aut (fiber xi)) :
    autHomOfCompIso (pullback θ)
        (pullbackFiberIso θ xi ≪≫ eqToIso (congrArg fiber h) ≪≫ s.symm) v =
      s.symm.conjAut (pointedFundamentalGroupHom θ xi y h v) := by
  subst y
  simp only [eqToIso_refl, Iso.refl_trans]
  change (pullbackFiberIso θ xi ≪≫ s.symm).conjAut _ =
    s.symm.conjAut ((pullbackFiberIso θ xi).conjAut _)
  exact Iso.trans_conjAut _ _ _

variable
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)

private theorem geometricAbelianGaloisAction_eq_map_of_lift
    (g : Aut (fiber (xi ≫ Limits.pullback.snd _ f)))
    (C : Aut (fiber xi) →ₜ* Aut (fiber xi))
    (hc : ∀ v, fundamentalGroupHom (Limits.pullback.snd _ f) xi (C v) =
      g * fundamentalGroupHom (Limits.pullback.snd _ f) xi v * g⁻¹)
    (x : TopologicalAbelianization (Aut (fiber xi))) :
    geometricAbelianGaloisAction k L X f xi
        (arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f) g) x =
      TopologicalAbelianization.map C x := by
  obtain ⟨v, rfl⟩ := TopologicalAbelianization.surjective_mk (Aut (fiber xi)) x
  rw [TopologicalAbelianization.map_apply_mk]
  exact geometricAbelianGaloisAction_mk_of_conjugate k L X f xi g v (C v) (hc v)

open EtaleFundamentalGroups.Cohomology EtaleCohomology.Classical

local instance torsionTopology (S : Scheme.{u}) :
    TopologicalSpace (Multiplicative (finiteTorsionCohomology S 1)) := ⊥

/-- Existing H¹ duality identifies a source-induced arithmetic conjugation with
actual scheme pullback, without a finite-deck assumption. -/
theorem geometricAbelianGaloisAction_source_duality
    (e : Spec (.of Ω) ≅ Spec (.of Ω))
    (θ : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    (hθ : θ ≫ Limits.pullback.snd _ f = Limits.pullback.snd _ f)
    (hpoint : e.hom ≫ xi = xi ≫ θ)
    (x : TopologicalAbelianization (Aut (fiber xi))) :
    let p := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
    let hz : e.hom ≫ (xi ≫ p) = xi ≫ p := by
      rw [← Category.assoc, hpoint, Category.assoc, hθ]
    let g : Aut (fiber (xi ≫ p)) :=
      fiberSourceIso (xi ≫ p) e ≪≫ eqToIso (congrArg fiber hz)
    abelianizationFiniteTorsionH1DualEquiv xi
        (geometricAbelianGaloisAction k L X f xi
          (arithmeticFundamentalGroupHom k L f (xi ≫ p) g⁻¹) x) =
      (abelianizationFiniteTorsionH1DualEquiv xi x).comp
        (finiteTorsionH1PullbackHom θ) := by
  intro p hz g
  let s := fiberSourceIso xi e
  let t := pullbackFiberIso θ xi ≪≫ eqToIso (congrArg fiber hpoint.symm) ≪≫ s.symm
  let C := autHomOfCompIso (pullback θ) t
  have hC (v : Aut (fiber xi)) : C v =
      s.symm.conjAut (pointedFundamentalGroupHom θ xi (e.hom ≫ xi) hpoint.symm v) :=
    autHomOfCompIso_pointed_source θ xi (e.hom ≫ xi) hpoint.symm s v
  have hc (v : Aut (fiber xi)) : fundamentalGroupHom p xi (C v) =
      g⁻¹ * fundamentalGroupHom p xi v * g := by
    rw [hC]
    exact fundamentalGroupHom_sourceDeck_conjugate xi e p θ hθ hpoint v
  have ha := geometricAbelianGaloisAction_eq_map_of_lift k L X f xi g⁻¹ C
    (by intro v; simpa only [inv_inv] using hc v) x
  rw [ha]
  exact abelianizationFiniteTorsionH1DualEquiv_pointedPullback θ xi xi t x

end AlgebraicGeometry.FiniteEtale
