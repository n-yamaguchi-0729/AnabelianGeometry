/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.ProperGlobalSectionsFinite
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Actual global units on a proper integral scheme

Properness makes the original structural map on global sections finite.
The original section ring is a domain, so algebraic closedness makes that
same map an isomorphism. Every positive power map on its actual group of
units is consequently surjective.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c]

/-- The original structural map identifies the actual global section
ring of a proper integral scheme with its algebraically closed base. -/
def properIntegralGlobalSectionsRingEquiv : K ≃+* Γ(X, ⊤) := by
  let g : K →+* Γ(X, ⊤) :=
    c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hg : g.Finite :=
    (finite_appTop_of_isProper_of_isNoetherianRing c).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.finite
  exact RingEquiv.ofBijective g
    (IsAlgClosed.ringHom_bijective_of_isIntegral g hg.to_isIntegral)

/-- The global-section equivalence retains the original pullback of
constants along the structure morphism. -/
theorem properIntegralGlobalSectionsRingEquiv_apply (a : K) :
    properIntegralGlobalSectionsRingEquiv c a =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop) a := rfl

/-- A morphism from a proper integral scheme to an affine scheme
factors uniquely through its algebraically closed field of constants. -/
theorem properIntegralHomToAffine_existsUnique
    {Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    ∃! p : Spec (CommRingCat.of K) ⟶ Y, c ≫ p = f := by
  let e : CommRingCat.of K ≅ Γ(X, ⊤) :=
    (properIntegralGlobalSectionsRingEquiv c).toCommRingCatIso
  have he : e.hom = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop := rfl
  have hc : X.toSpecΓ ≫ Spec.map e.hom = c := by
    rw [he, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality c,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hΓ : c.appTop = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ e.hom := by
    rw [he, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have : IsIso c.appTop := by
    rw [hΓ]
    infer_instance
  let p : Spec (CommRingCat.of K) ⟶ Y :=
    Spec.map (f.appTop ≫ e.inv) ≫ (Scheme.isoSpec Y).inv
  have hp : c ≫ p = f := by
    change c ≫ (Spec.map (f.appTop ≫ e.inv) ≫ (Scheme.isoSpec Y).inv) = f
    rw [← hc, Category.assoc, ← Category.assoc (Spec.map e.hom),
      ← Spec.map_comp, Category.assoc f.appTop e.inv e.hom,
      e.inv_hom_id, Category.comp_id, ← Category.assoc,
      ← Scheme.toSpecΓ_naturality f, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  refine ⟨p, hp, ?_⟩
  intro q hq
  apply ext_of_isAffine
  apply (cancel_mono c.appTop).mp
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hq, hp]

/-- A morphism over the constants into an affine target is the
pullback of a unique rational point of that same target. -/
theorem properIntegralHomOverToAffine_existsUnique
    {Y : Scheme.{u}} [IsAffine Y] (d : Y ⟶ Spec (CommRingCat.of K))
    (f : X ⟶ Y) (hf : f ≫ d = c) :
    ∃! p : Spec (CommRingCat.of K) ⟶ Y,
      p ≫ d = 𝟙 (Spec (CommRingCat.of K)) ∧ c ≫ p = f := by
  obtain ⟨p, hp, hup⟩ := properIntegralHomToAffine_existsUnique c f
  obtain ⟨q, _, huq⟩ := properIntegralHomToAffine_existsUnique c c
  have hd : p ≫ d = 𝟙 (Spec (CommRingCat.of K)) := by
    apply (huq (p ≫ d) ?_).trans
      (huq (𝟙 (Spec (CommRingCat.of K))) (Category.comp_id c)).symm
    rw [← Category.assoc, hp, hf]
  exact ⟨p, ⟨hd, hp⟩, fun r hr => hup r hr.2⟩

include c in
/-- Every actual global unit on a proper integral scheme over an
algebraically closed field has an actual nth root for positive n. -/
theorem properIntegralGlobalUnits_pow_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (fun a : (Γ(X, ⊤) : Type u)ˣ => a ^ n) := by
  let e : Kˣ ≃* (Γ(X, ⊤) : Type u)ˣ :=
    Units.mapEquiv (properIntegralGlobalSectionsRingEquiv c).toMulEquiv
  intro a
  let b : Kˣ := e.symm a
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (b : K) hn
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hn)] at hz
    exact b.ne_zero hz.symm
  let w : Kˣ := Units.mk0 z hz0
  have hw : w ^ n = b := Units.ext hz
  refine ⟨e w, ?_⟩
  calc
    (e w) ^ n = e (w ^ n) := (map_pow e w n).symm
    _ = e b := congrArg e hw
    _ = a := e.apply_symm_apply a

end AlgebraicGeometry
