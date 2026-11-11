/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.Basic
public import Nyll.SchemeTheory.Modules.EqMulPresentations
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataRangeModuleIotaAppInjective
public import Nyll.SchemeTheory.Sheaves.IdealSheafModule
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Rational multipliers of actual ideal-module isomorphisms

The kernel realization of an ideal module embeds its actual sections in
regular functions. On an integral scheme these embeddings give actual
compatible function-field presentations. An isomorphism of two such
modules is multiplication by one nonzero rational function. The multiplier
is constructed from these presentations, rather than supplied as a
compatibility condition on the isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The original inclusion of the ideal module commutes with restriction
of its actual regular-function values. -/
theorem moduleIota_app_restrict (I : X.IdealSheafData)
    {U V : X.Opens} (h : V ≤ U) (s : Γ(I.module, U)) :
    I.moduleι.app V (I.module.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (I.moduleι.app U s) := by
  exact ConcreteCategory.congr_hom
    (I.moduleι.mapPresheaf.naturality (homOfLE h).op) s

/-- Injectivity of the actual ideal-module inclusion on every open,
deduced from its original affine computation and sheaf separatedness. -/
theorem moduleIota_app_injective (I : X.IdealSheafData) (U : X.Opens) :
    Function.Injective (I.moduleι.app U) := by
  intro s t hst
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    ⟨I.module.presheaf, I.module.isSheaf⟩
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := U) hx
  refine ⟨V, hVU, hxV, ?_⟩
  change I.module.presheaf.map (homOfLE hVU).op s =
    I.module.presheaf.map (homOfLE hVU).op t
  apply (I.range_moduleIota_app_and_injective ⟨V, hV⟩).2
  change I.moduleι.app V (I.module.presheaf.map (homOfLE hVU).op s) =
    I.moduleι.app V (I.module.presheaf.map (homOfLE hVU).op t)
  exact (I.moduleIota_app_restrict hVU s).trans
    ((congrArg (X.presheaf.map (homOfLE hVU).op) hst).trans
      (I.moduleIota_app_restrict hVU t).symm)

/-- The actual kernel inclusion, followed on every nonempty open by
the original generic-point germ map. Empty opens are sent to zero. -/
def moduleFunctionFieldHom (I : X.IdealSheafData) [IsIntegral X]
    (U : X.Opens) : Γ(I.module, U) →+ (X.functionField : Type u) := by
  classical
  exact if h : Nonempty U then
    (X.germToFunctionField U).hom.toAddMonoidHom.comp (I.moduleι.app U).hom
  else 0

theorem moduleFunctionFieldHom_apply (I : X.IdealSheafData) [IsIntegral X]
    (U : X.Opens) [Nonempty U] (s : Γ(I.module, U)) :
    I.moduleFunctionFieldHom U s = X.germToFunctionField U (I.moduleι.app U s) := by
  classical
  have h : I.moduleFunctionFieldHom U =
      (X.germToFunctionField U).hom.toAddMonoidHom.comp (I.moduleι.app U).hom :=
    dite_eq_left (show Nonempty U from inferInstance)
  exact DFunLike.congr_fun h s

/-- These actual rational presentations commute with restriction. -/
theorem moduleFunctionFieldHom_restrict (I : X.IdealSheafData) [IsIntegral X]
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (s : Γ(I.module, U)) :
    I.moduleFunctionFieldHom V (I.module.presheaf.map (homOfLE h).op s) =
      I.moduleFunctionFieldHom U s := by
  rw [moduleFunctionFieldHom_apply, moduleFunctionFieldHom_apply,
    moduleIota_app_restrict]
  obtain ⟨x⟩ := (show Nonempty V from inferInstance)
  have hx : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x.1, trivial, x.2⟩
  exact X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) hx
    (I.moduleι.app U s)

/-- The scalar law uses the existing function-field algebra structure
and the original linearity of the kernel inclusion. -/
theorem moduleFunctionFieldHom_smul (I : X.IdealSheafData) [IsIntegral X]
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (s : Γ(I.module, U)) :
    I.moduleFunctionFieldHom U (a • s) =
      algebraMap Γ(X, U) X.functionField a * I.moduleFunctionFieldHom U s := by
  rw [moduleFunctionFieldHom_apply, moduleFunctionFieldHom_apply,
    Scheme.Modules.Hom.app_smul]
  exact map_mul (X.germToFunctionField U).hom a (I.moduleι.app U s)

theorem moduleFunctionFieldHom_injective (I : X.IdealSheafData) [IsIntegral X]
    (U : X.Opens) [Nonempty U] : Function.Injective (I.moduleFunctionFieldHom U) := by
  intro s t h
  apply I.moduleIota_app_injective U
  apply X.germToFunctionField_injective U
  exact (I.moduleFunctionFieldHom_apply U s).symm.trans
    (h.trans (I.moduleFunctionFieldHom_apply U t))

private theorem moduleIso_app_injective {I J : X.IdealSheafData}
    (e : I.module ≅ J.module) (U : X.Opens) :
    Function.Injective (e.hom.app U) := by
  intro s t h
  have hs : e.inv.app U (e.hom.app U s) = s := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f : I.module ⟶ I.module => f.app U) e.hom_inv_id) s
  have ht : e.inv.app U (e.hom.app U t) = t := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f : I.module ⟶ I.module => f.app U) e.hom_inv_id) t
  exact hs.symm.trans ((congrArg (e.inv.app U) h).trans ht)

/-- An actual ideal-module isomorphism on an integral scheme has a
single original function-field unit as multiplier. The effective Cartier
property supplies a nonzero section of its actual source ideal module. -/
theorem exists_unit_moduleIso_eq_mul [IsIntegral X]
    {I J : X.IdealSheafData} (hI : I.IsEffectiveCartier) (e : I.module ≅ J.module) :
    ∃ a : X.functionFieldˣ,
      ∀ (U : X.Opens) [Nonempty U] (s : Γ(I.module, U)),
        X.germToFunctionField U (J.moduleι.app U (e.hom.app U s)) =
          (a : X.functionField) * X.germToFunctionField U (I.moduleι.app U s) := by
  let φ : ∀ U : X.Opens, Γ(I.module, U) →+ (X.functionField : Type u) :=
    I.moduleFunctionFieldHom
  let ψ : ∀ U : X.Opens, Γ(I.module, U) →+ (X.functionField : Type u) :=
    fun U => (J.moduleFunctionFieldHom U).comp (e.hom.app U).hom
  have hφnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ s : Γ(I.module, U), φ V (I.module.presheaf.map (homOfLE h).op s) = φ U s := by
    intro U V h hV s
    have : Nonempty V := hV
    have : Nonempty U := hV.map (fun x => ⟨x.1, h x.2⟩)
    exact I.moduleFunctionFieldHom_restrict h s
  have hψnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ s : Γ(I.module, U), ψ V (I.module.presheaf.map (homOfLE h).op s) = ψ U s := by
    intro U V h hV s
    have : Nonempty V := hV
    have : Nonempty U := hV.map (fun x => ⟨x.1, h x.2⟩)
    have he : e.hom.app V (I.module.presheaf.map (homOfLE h).op s) =
        J.module.presheaf.map (homOfLE h).op (e.hom.app U s) :=
      ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality (homOfLE h).op) s
    change J.moduleFunctionFieldHom V
      (e.hom.app V (I.module.presheaf.map (homOfLE h).op s)) = _
    rw [he]
    exact J.moduleFunctionFieldHom_restrict h (e.hom.app U s)
  have hφsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (s : Γ(I.module, U)),
      φ U (a • s) = algebraMap Γ(X, U) X.functionField a * φ U s := by
    intro U hU a s
    exact I.moduleFunctionFieldHom_smul U a s
  have hψsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (s : Γ(I.module, U)),
      ψ U (a • s) = algebraMap Γ(X, U) X.functionField a * ψ U s := by
    intro U hU a s
    change J.moduleFunctionFieldHom U (e.hom.app U (a • s)) = _
    rw [Scheme.Modules.Hom.app_smul]
    exact J.moduleFunctionFieldHom_smul U a (e.hom.app U s)
  have hφinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U) := by
    intro U hU
    have : Nonempty U := hU
    exact I.moduleFunctionFieldHom_injective U
  have hψinj : ∀ U : X.Opens, Nonempty U → Function.Injective (ψ U) := by
    intro U hU
    have : Nonempty U := hU
    exact (J.moduleFunctionFieldHom_injective U).comp (moduleIso_app_injective e U)
  obtain ⟨U, hxU, f, hf, hIf⟩ := hI (genericPoint X)
  have : Nonempty U.1 := ⟨⟨genericPoint X, hxU⟩⟩
  have hf0 : f ≠ 0 := by
    intro h
    exact zero_ne_one (hf.left (by
      change f * (0 : Γ(X, U.1)) = f * 1
      rw [h, zero_mul, zero_mul]))
  have hfmem : f ∈ Set.range (I.moduleι.app U) := by
    rw [(I.range_moduleIota_app_and_injective U).1, hIf]
    exact Ideal.mem_span_singleton_self f
  obtain ⟨s, hs⟩ := hfmem
  have hs0 : s ≠ 0 := by
    intro h
    apply hf0
    exact hs.symm.trans ((congrArg (I.moduleι.app U) h).trans (map_zero _))
  obtain ⟨a, ha, hmul⟩ := Scheme.Modules.exists_forall_eq_mul_of_presentations
    I.module φ ψ hφnat hψnat hφsmul hψsmul hφinj hψinj ⟨U.1, s, hs0⟩
  refine ⟨Units.mk0 a ha, ?_⟩
  intro V hV t
  simpa only [φ, ψ, AddMonoidHom.comp_apply, moduleFunctionFieldHom_apply,
    Units.val_mk0] using hmul V t

end AlgebraicGeometry.Scheme.IdealSheafData
