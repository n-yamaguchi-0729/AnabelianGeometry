/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleInvModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealModuleTensorInvModuleIso
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalIsomorphism
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierInvertibility
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CartierCycleModuleIsomorphism
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitLocalSections
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitSections
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleCycleTensor
public import Nyll.EtaleCohomology.Classical.InvertibleGenericUnitSections
public import Nyll.EtaleCohomology.Classical.ZariskiH0Ext
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Sheaves.IdealModuleFrames
public import Nyll.SchemeTheory.Sheaves.IdealModuleRationalComparison
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataRangeModuleIotaAppInjective

/-!
# Original line-bundle classes and original Cartier cycle classes

An actual ideal-module frame gives an actual affine Cartier equation.
The chosen rational realization and the original ideal inclusion differ
by one global rational unit, so their original quotient representatives
have the same boundary. The actual tensor inverse identifies the class
of the original divisor line bundle with the existing Cartier class.
Consequently an actual signed divisor-bundle isomorphism computes the
native class of any original invertible module, including Poincaré families.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open Scheme.Modules

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X]

/-- The original Cartier quotient class and the actual ideal-module
frame representative differ by a single original rational image. -/
theorem effectiveCartierGenericUnitH0_eq_moduleRepresentative
    (D : Scheme.EffectiveCartierDivisor X) :
    ∃ a : Additive X.functionFieldˣ,
      let m : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
        Sheaf.H.map (etaleGenericUnitShortComplex X).g 0
          ((genericPointUnitsH0Equiv X).symm a)
      effectiveCartierGenericUnitH0 D =
        m + invertibleModuleGenericUnitH0 D.2.isInvertible.isInvertible_module := by
  let hM := D.2.isInvertible.isInvertible_module
  obtain ⟨a, ha⟩ := hM.exists_unit_functionFieldHom_eq_mul
    D.1.moduleFunctionFieldHom
    (by
      intro U V h hV s
      have : Nonempty V := hV
      have : Nonempty U := hV.map (fun x => ⟨x.1, h x.2⟩)
      exact D.1.moduleFunctionFieldHom_restrict h s)
    (by
      intro U hU a s
      exact D.1.moduleFunctionFieldHom_smul U a s)
    (by
      intro U hU
      have : Nonempty U := hU
      exact D.1.moduleFunctionFieldHom_injective U)
  refine ⟨Additive.ofMul a, ?_⟩
  intro m
  apply etaleAbelianH0_ext_zariski X (etaleGenericUnitQuotient X)
  intro x
  obtain ⟨U, s, hxU, hs⟩ := hM.exists_frameSection x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) hxU
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let t := D.1.module.presheaf.map (homOfLE hVU).op s
  have ht : IsFrameOn t V := (hs.map (homOfLE hVU)).mono hVU
  let f : Γ(X, V) := D.1.moduleι.app V t
  have hf : f ≠ 0 := by
    intro hz
    apply frameSection_ne_zero ht
    apply (D.1.range_moduleIota_app_and_injective ⟨V, hV⟩).2
    exact hz.trans (D.1.moduleι.app V).hom.map_zero.symm
  have hD : D.1.ideal ⟨V, hV⟩ = Ideal.span {f} :=
    D.1.ideal_eq_span_moduleIota_of_frame ⟨V, hV⟩ t ht
  have hu : openSectionRationalUnit X V f hf = a * hM.frameRationalUnit V t ht := by
    apply Units.ext
    exact (D.1.moduleFunctionFieldHom_apply V t).symm.trans (ha V t)
  refine ⟨V, hxV, ?_⟩
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let ev : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      (etaleGenericUnitQuotient X).obj.obj (op ((zariskiToEtale X).obj V)) :=
    ((etaleGenericUnitQuotient X).obj.map
      (hT.from ((zariskiToEtale X).obj V)).op).hom.comp
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT).toAddMonoidHom
  change ev (effectiveCartierGenericUnitH0 D) =
    ev (m + invertibleModuleGenericUnitH0 hM)
  have hsecD : ev (effectiveCartierGenericUnitH0 D) =
      openSectionGenericUnitQuotient X V f hf :=
    effectiveCartierGenericUnitH0_section D ⟨V, hV⟩ f hf hD
  have hsecM : ev (invertibleModuleGenericUnitH0 hM) =
      invertibleFrameGenericUnitQuotient hM V t ht :=
    invertibleModuleGenericUnitH0_section hM V t ht
  have himage : ev m = genericPointRationalUnitQuotientSection X
      ((zariskiToEtale X).obj V) (Additive.ofMul a) :=
    genericPointUnitQuotientH0_section X (Additive.ofMul a) ((zariskiToEtale X).obj V)
  let q := genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj V)
  have hq : openSectionGenericUnitQuotient X V f hf =
      genericPointRationalUnitQuotientSection X ((zariskiToEtale X).obj V)
        (Additive.ofMul a) + invertibleFrameGenericUnitQuotient hM V t ht :=
    (congrArg (fun b : X.functionFieldˣ => q (Additive.ofMul b)) hu).trans
      (map_add q (Additive.ofMul a) (Additive.ofMul (hM.frameRationalUnit V t ht)))
  exact hsecD.trans (hq.trans
    ((congrArg₂
      (fun v w : (etaleGenericUnitQuotient X).obj.obj
        (op ((zariskiToEtale X).obj V)) => v + w) himage.symm hsecM.symm).trans
      (ev.map_add m (invertibleModuleGenericUnitH0 hM)).symm))

/-- The native class of the actual ideal module is the negative of
the original Cartier-divisor class. -/
theorem invertibleModuleMultiplicativeGroupH1_idealModule
    (D : Scheme.EffectiveCartierDivisor X) :
    invertibleModuleMultiplicativeGroupH1 D.2.isInvertible.isInvertible_module =
      -effectiveCartierMultiplicativeGroupH1 D := by
  obtain ⟨a, ha⟩ := effectiveCartierGenericUnitH0_eq_moduleRepresentative D
  let δ : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
  let m : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
    Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 ((genericPointUnitsH0Equiv X).symm a)
  have hz : δ m = 0 := genericPointUnitH0_boundary_zero a
  have h : δ (effectiveCartierGenericUnitH0 D) =
      δ (invertibleModuleGenericUnitH0 D.2.isInvertible.isInvertible_module) :=
    (congrArg δ ha).trans
      ((δ.map_add m (invertibleModuleGenericUnitH0 D.2.isInvertible.isInvertible_module)).trans
        ((congrArg (fun z => z +
          δ (invertibleModuleGenericUnitH0 D.2.isInvertible.isInvertible_module)) hz).trans
            (zero_add _)))
  exact congrArg Neg.neg h.symm

/-- The native class of the actual divisor line bundle is the
original effective Cartier class. -/
theorem invertibleModuleMultiplicativeGroupH1_invModule
    (D : Scheme.EffectiveCartierDivisor X) :
    invertibleModuleMultiplicativeGroupH1 D.2.isInvertible.isInvertible_invModule =
      effectiveCartierMultiplicativeGroupH1 D := by
  let hD := D.2.isInvertible
  obtain ⟨e⟩ := hD.nonempty_module_tensor_invModule_iso.1
  have h := invertibleModuleMultiplicativeGroupH1_iso
    (hD.isInvertible_module.tensor hD.isInvertible_invModule)
    (Scheme.Modules.isInvertible_unit X) e
  rw [invertibleModuleMultiplicativeGroupH1_tensor
      hD.isInvertible_module hD.isInvertible_invModule,
    invertibleModuleMultiplicativeGroupH1_idealModule,
    invertibleModuleMultiplicativeGroupH1_unit] at h
  calc
    invertibleModuleMultiplicativeGroupH1 hD.isInvertible_invModule =
        (effectiveCartierMultiplicativeGroupH1 D +
          -effectiveCartierMultiplicativeGroupH1 D) +
            invertibleModuleMultiplicativeGroupH1 hD.isInvertible_invModule := by
      rw [add_neg_cancel, zero_add]
    _ = effectiveCartierMultiplicativeGroupH1 D +
        (-effectiveCartierMultiplicativeGroupH1 D +
          invertibleModuleMultiplicativeGroupH1 hD.isInvertible_invModule) := add_assoc _ _ _
    _ = effectiveCartierMultiplicativeGroupH1 D := by rw [h, add_zero]

/-- An actual signed divisor-bundle isomorphism computes the original
native H¹(Gm) class of the same original line bundle. -/
theorem invertibleModuleMultiplicativeGroupH1_eq_signedCartier
    {L : X.Modules} (hL : IsInvertible L) (D E : Scheme.EffectiveCartierDivisor X)
    (e : L ≅ D.1.invModule ⊗ E.1.module) :
    invertibleModuleMultiplicativeGroupH1 hL =
      effectiveCartierMultiplicativeGroupH1 D - effectiveCartierMultiplicativeGroupH1 E := by
  have h := invertibleModuleMultiplicativeGroupH1_iso hL
    (D.2.isInvertible.isInvertible_invModule.tensor E.2.isInvertible.isInvertible_module) e
  rw [invertibleModuleMultiplicativeGroupH1_tensor
      D.2.isInvertible.isInvertible_invModule E.2.isInvertible.isInvertible_module,
    invertibleModuleMultiplicativeGroupH1_invModule,
    invertibleModuleMultiplicativeGroupH1_idealModule] at h
  exact h.trans (sub_eq_add_neg _ _).symm

/-- The same actual signed bundle has exactly the existing original
signed Cartier cycle class in native H²(μn). -/
theorem invertibleModuleCycleClass_eq_signedCartier
    {L : X.Modules} (hL : IsInvertible L) (D E : Scheme.EffectiveCartierDivisor X)
    (e : L ≅ D.1.invModule ⊗ E.1.module) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    invertibleModuleCycleClass hL hn hnX =
      effectiveCartierCycleClass D hn hnX - effectiveCartierCycleClass E hn hnX := by
  simpa only [invertibleModuleCycleClass, effectiveCartierCycleClass, map_sub] using
    congrArg (Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl)
      (invertibleModuleMultiplicativeGroupH1_eq_signedCartier hL D E e)

end EtaleCohomology
