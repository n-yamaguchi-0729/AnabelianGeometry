/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Sheaves.IdealSheafDataRangeModuleIotaAppInjective
public import Nyll.SchemeTheory.Sheaves.IdealSheafModule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Ideal.Span

/-!
# Transport of actual affine ideal generators

The original kernel inclusion identifies the sections of an ideal module
on an affine open with its actual ring ideal. Consequently a generator
of that ideal generates its module sections, and a module isomorphism
sends it to a generator of the target ideal.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The actual regular function underlying an ideal-module section
belongs to the original affine ideal. -/
theorem moduleIota_app_mem (I : X.IdealSheafData) (U : X.affineOpens)
    (s : Γ(I.module, U.1)) :
    (show Γ(X, U.1) from I.moduleι.app U.1 s) ∈ I.ideal U := by
  have hs : (show Γ(X, U.1) from I.moduleι.app U.1 s) ∈
      Set.range (I.moduleι.app U.1) := ⟨s, rfl⟩
  exact Eq.mp (congrArg (fun T : Set Γ(X, U.1) =>
    (show Γ(X, U.1) from I.moduleι.app U.1 s) ∈ T)
      (I.range_moduleIota_app_and_injective U).1) hs

/-- A generator of the actual affine ideal generates all sections
of its original ideal module on that affine open. -/
theorem exists_smul_of_span_moduleIota (I : X.IdealSheafData)
    (U : X.affineOpens) (s : Γ(I.module, U.1))
    (hI : I.ideal U = Ideal.span {show Γ(X, U.1) from I.moduleι.app U.1 s})
    (t : Γ(I.module, U.1)) : ∃ a : Γ(X, U.1), t = a • s := by
  have ht : (show Γ(X, U.1) from I.moduleι.app U.1 t) ∈
      Ideal.span {show Γ(X, U.1) from I.moduleι.app U.1 s} :=
    hI ▸ I.moduleIota_app_mem U t
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp ht
  refine ⟨a, ?_⟩
  apply (I.range_moduleIota_app_and_injective U).2
  change (show Γ(X, U.1) from I.moduleι.app U.1 t) =
    (show Γ(X, U.1) from I.moduleι.app U.1 (a • s))
  exact ha.symm.trans (Scheme.Modules.Hom.app_smul I.moduleι a s).symm

/-- The actual image of an affine ideal generator under a module
isomorphism generates the original target ideal. -/
theorem span_moduleIota_moduleIso_generator
    {I J : X.IdealSheafData} (e : I.module ≅ J.module)
    (U : X.affineOpens) (s : Γ(I.module, U.1))
    (hI : I.ideal U = Ideal.span {show Γ(X, U.1) from I.moduleι.app U.1 s}) :
    J.ideal U =
      Ideal.span {show Γ(X, U.1) from J.moduleι.app U.1 (e.hom.app U.1 s)} := by
  apply le_antisymm
  · intro y hy
    have hy' : y ∈ Set.range (J.moduleι.app U) := by
      rw [(J.range_moduleIota_app_and_injective U).1]
      exact hy
    obtain ⟨t, ht⟩ := hy'
    obtain ⟨a, ha⟩ := I.exists_smul_of_span_moduleIota U s hI (e.inv.app U.1 t)
    have he : e.hom.app U.1 (e.inv.app U.1 t) = t :=
      ConcreteCategory.congr_hom
        (congrArg (fun f : J.module ⟶ J.module => f.app U.1) e.inv_hom_id) t
    refine Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩
    calc
      a * (show Γ(X, U.1) from J.moduleι.app U.1 (e.hom.app U.1 s)) =
          (show Γ(X, U.1) from J.moduleι.app U.1 (e.hom.app U.1 (a • s))) := by
            simp only [Scheme.Modules.Hom.app_smul]
            rfl
      _ = (show Γ(X, U.1) from
          J.moduleι.app U.1 (e.hom.app U.1 (e.inv.app U.1 t))) :=
        congrArg (fun z => J.moduleι.app U.1 (e.hom.app U.1 z)) ha.symm
      _ = (show Γ(X, U.1) from J.moduleι.app U.1 t) :=
        congrArg (J.moduleι.app U.1) he
      _ = y := ht
  · apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact J.moduleIota_app_mem U (e.hom.app U.1 s)

end AlgebraicGeometry.Scheme.IdealSheafData
