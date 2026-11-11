/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalFrames
public import Nyll.SchemeTheory.Modules.EqMulPresentations
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The actual rational multiplier of a line-bundle isomorphism

The original uniqueness theorem for injective function-field
presentations applies to the genuine local frame of an invertible
module. It identifies every other such presentation, and in particular
the presentation composed with an actual module isomorphism, by one
original global function-field unit.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] {M N : X.Modules}

/-- Any other actual function-field presentation differs from the
chosen one by one original global rational unit. -/
theorem IsInvertible.exists_unit_functionFieldHom_eq_mul (hM : IsInvertible M)
    (ψ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ s : Γ(M, U), ψ V (M.presheaf.map (homOfLE h).op s) = ψ U s)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (s : Γ(M, U)),
      ψ U (a • s) = algebraMap Γ(X, U) X.functionField a * ψ U s)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (ψ U)) :
    ∃ a : X.functionFieldˣ,
      ∀ (U : X.Opens) [Nonempty U] (s : Γ(M, U)),
        ψ U s = (a : X.functionField) * hM.functionFieldHom U s := by
  have hφnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ s : Γ(M, U), hM.functionFieldHom V (M.presheaf.map (homOfLE h).op s) =
        hM.functionFieldHom U s := by
    intro U V h hV s
    have : Nonempty V := hV
    exact hM.functionFieldHom_restrict h s
  have hφsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (s : Γ(M, U)),
      hM.functionFieldHom U (a • s) =
        algebraMap Γ(X, U) X.functionField a * hM.functionFieldHom U s := by
    intro U hU a s
    exact hM.functionFieldHom_smul U a s
  have hφinj : ∀ U : X.Opens, Nonempty U →
      Function.Injective (hM.functionFieldHom U) := by
    intro U hU
    have : Nonempty U := hU
    exact hM.functionFieldHom_injective U
  obtain ⟨U, s, hxU, hs⟩ := hM.exists_frameSection (genericPoint X)
  have : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  obtain ⟨a, ha, hmul⟩ := exists_forall_eq_mul_of_presentations M
    hM.functionFieldHom ψ hφnat hnat hφsmul hsmul hφinj hinj
      ⟨U, s, frameSection_ne_zero hs⟩
  exact ⟨Units.mk0 a ha, hmul⟩

omit [IsIntegral X] in
private theorem moduleIso_sections_injective (e : M ≅ N) (U : X.Opens) :
    Function.Injective (e.hom.app U) := by
  intro s t h
  have hs : e.inv.app U (e.hom.app U s) = s :=
    ConcreteCategory.congr_hom
      (congrArg (fun f : M ⟶ M => f.app U) e.hom_inv_id) s
  have ht : e.inv.app U (e.hom.app U t) = t :=
    ConcreteCategory.congr_hom
      (congrArg (fun f : M ⟶ M => f.app U) e.hom_inv_id) t
  exact hs.symm.trans ((congrArg (e.inv.app U) h).trans ht)

/-- An actual invertible-module isomorphism is multiplication by the
same original rational unit in every chosen local realization. -/
theorem IsInvertible.exists_unit_functionFieldHom_iso_eq_mul
    (hM : IsInvertible M) (hN : IsInvertible N) (e : M ≅ N) :
    ∃ a : X.functionFieldˣ,
      ∀ (U : X.Opens) [Nonempty U] (s : Γ(M, U)),
        hN.functionFieldHom U (e.hom.app U s) =
          (a : X.functionField) * hM.functionFieldHom U s := by
  let ψ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u) :=
    fun U => (hN.functionFieldHom U).comp (e.hom.app U).hom
  have hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ s : Γ(M, U), ψ V (M.presheaf.map (homOfLE h).op s) = ψ U s := by
    intro U V h hV s
    have : Nonempty V := hV
    have he : e.hom.app V (M.presheaf.map (homOfLE h).op s) =
        N.presheaf.map (homOfLE h).op (e.hom.app U s) :=
      ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality (homOfLE h).op) s
    change hN.functionFieldHom V (e.hom.app V (M.presheaf.map (homOfLE h).op s)) = _
    rw [he]
    exact hN.functionFieldHom_restrict h (e.hom.app U s)
  have hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (s : Γ(M, U)),
      ψ U (a • s) = algebraMap Γ(X, U) X.functionField a * ψ U s := by
    intro U hU a s
    change hN.functionFieldHom U (e.hom.app U (a • s)) = _
    rw [Scheme.Modules.Hom.app_smul]
    exact hN.functionFieldHom_smul U a (e.hom.app U s)
  have hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (ψ U) := by
    intro U hU
    have : Nonempty U := hU
    exact (hN.functionFieldHom_injective U).comp (moduleIso_sections_injective e U)
  exact hM.exists_unit_functionFieldHom_eq_mul ψ hnat hsmul hinj

end AlgebraicGeometry.Scheme.Modules
