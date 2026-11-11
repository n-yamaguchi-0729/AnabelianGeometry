/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalTensor
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Projective.InvertibleTensorPow
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.EtaleCohomology.Classical.CartierCycleModuleIsomorphism
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.GenericUnitRegularOpenSections
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleGenericUnitSections
public import Nyll.EtaleCohomology.Classical.KummerH1Kernel
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.ZariskiH0Ext
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorFrames
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Tensor products and roots of original line-bundle cycle classes

The actual rational tensor-frame comparison proves additivity in the
original H¹(Gm) and Kummer H² groups. An actual tensor-power root thus
makes the original Kummer cycle class vanish, by the original exact
sequence. These statements apply to the genuine Poincaré root bundles
without requiring a presentation as a difference of effective divisors.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Abelian MonoidalCategory Opposite
open Scheme.Modules

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] {L M : X.Modules}

/-- The original tensor-product quotient class differs from the sum
by the image of one actual global rational unit. -/
theorem invertibleModuleGenericUnitH0_tensor
    (hL : IsInvertible L) (hM : IsInvertible M) :
    ∃ a : Additive X.functionFieldˣ,
      let m : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
        Sheaf.H.map (etaleGenericUnitShortComplex X).g 0
          ((genericPointUnitsH0Equiv X).symm a)
      invertibleModuleGenericUnitH0 (hL.tensor hM) =
        m + (invertibleModuleGenericUnitH0 hL + invertibleModuleGenericUnitH0 hM) := by
  obtain ⟨a, ha⟩ := hL.exists_unit_tensorFrameRationalUnit_eq_mul hM
  refine ⟨Additive.ofMul a, ?_⟩
  intro m
  apply etaleAbelianH0_ext_zariski X (etaleGenericUnitQuotient X)
  intro x
  obtain ⟨U, s, t, hxU, hs, ht⟩ := hL.exists_common_frameSections hM x
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨U, hxU, ?_⟩
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let ev : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      (etaleGenericUnitQuotient X).obj.obj (op ((zariskiToEtale X).obj U)) :=
    ((etaleGenericUnitQuotient X).obj.map
      (hT.from ((zariskiToEtale X).obj U)).op).hom.comp
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT).toAddMonoidHom
  change ev (invertibleModuleGenericUnitH0 (hL.tensor hM)) =
    ev (m + (invertibleModuleGenericUnitH0 hL + invertibleModuleGenericUnitH0 hM))
  have hsecT : ev (invertibleModuleGenericUnitH0 (hL.tensor hM)) =
      invertibleFrameGenericUnitQuotient (hL.tensor hM) U
        (tensorSections s t) (hs.tensorSections ht) :=
    invertibleModuleGenericUnitH0_section (hL.tensor hM) U
      (tensorSections s t) (hs.tensorSections ht)
  have hsecL : ev (invertibleModuleGenericUnitH0 hL) =
      invertibleFrameGenericUnitQuotient hL U s hs :=
    invertibleModuleGenericUnitH0_section hL U s hs
  have hsecM : ev (invertibleModuleGenericUnitH0 hM) =
      invertibleFrameGenericUnitQuotient hM U t ht :=
    invertibleModuleGenericUnitH0_section hM U t ht
  have himage : ev m = genericPointRationalUnitQuotientSection X
      ((zariskiToEtale X).obj U) (Additive.ofMul a) :=
    genericPointUnitQuotientH0_section X (Additive.ofMul a) ((zariskiToEtale X).obj U)
  let q := genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U)
  have hq : invertibleFrameGenericUnitQuotient (hL.tensor hM) U
        (tensorSections s t) (hs.tensorSections ht) =
      genericPointRationalUnitQuotientSection X ((zariskiToEtale X).obj U)
        (Additive.ofMul a) +
        (invertibleFrameGenericUnitQuotient hL U s hs +
          invertibleFrameGenericUnitQuotient hM U t ht) :=
    (congrArg (fun b : X.functionFieldˣ => q (Additive.ofMul b)) (ha U s t hs ht)).trans
      ((map_add q (Additive.ofMul a)
        (Additive.ofMul (hL.frameRationalUnit U s hs) +
          Additive.ofMul (hM.frameRationalUnit U t ht))).trans
        (congrArg (fun z => q (Additive.ofMul a) + z)
          (map_add q (Additive.ofMul (hL.frameRationalUnit U s hs))
            (Additive.ofMul (hM.frameRationalUnit U t ht)))))
  have hev : ev (m + (invertibleModuleGenericUnitH0 hL + invertibleModuleGenericUnitH0 hM)) =
      ev m + (ev (invertibleModuleGenericUnitH0 hL) + ev (invertibleModuleGenericUnitH0 hM)) :=
    (ev.map_add m _).trans (congrArg (fun z => ev m + z)
      (ev.map_add (invertibleModuleGenericUnitH0 hL) (invertibleModuleGenericUnitH0 hM)))
  exact hsecT.trans (hq.trans
    ((congrArg₂
      (fun v w : (etaleGenericUnitQuotient X).obj.obj
        (op ((zariskiToEtale X).obj U)) => v + w) himage.symm
      (congrArg₂
        (fun v w : (etaleGenericUnitQuotient X).obj.obj
          (op ((zariskiToEtale X).obj U)) => v + w) hsecL.symm hsecM.symm)).trans hev.symm))

/-- The original native line-bundle class is additive under the
actual tensor product. -/
theorem invertibleModuleMultiplicativeGroupH1_tensor
    (hL : IsInvertible L) (hM : IsInvertible M) :
    invertibleModuleMultiplicativeGroupH1 (hL.tensor hM) =
      invertibleModuleMultiplicativeGroupH1 hL + invertibleModuleMultiplicativeGroupH1 hM := by
  obtain ⟨a, ha⟩ := invertibleModuleGenericUnitH0_tensor hL hM
  let δ : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
  let m : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
    Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 ((genericPointUnitsH0Equiv X).symm a)
  have hz : δ m = 0 := genericPointUnitH0_boundary_zero a
  have he : δ (invertibleModuleGenericUnitH0 (hL.tensor hM)) =
      δ m + (δ (invertibleModuleGenericUnitH0 hL) + δ (invertibleModuleGenericUnitH0 hM)) :=
    (congrArg δ ha).trans ((δ.map_add m _).trans
      (congrArg (fun z => δ m + z)
        (δ.map_add (invertibleModuleGenericUnitH0 hL) (invertibleModuleGenericUnitH0 hM))))
  change -δ (invertibleModuleGenericUnitH0 (hL.tensor hM)) =
    -δ (invertibleModuleGenericUnitH0 hL) + -δ (invertibleModuleGenericUnitH0 hM)
  rw [he, hz, zero_add, neg_add]

/-- The same additivity holds for the original Kummer cycle classes. -/
theorem invertibleModuleCycleClass_tensor
    (hL : IsInvertible L) (hM : IsInvertible M) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    invertibleModuleCycleClass (hL.tensor hM) hn hnX =
      invertibleModuleCycleClass hL hn hnX + invertibleModuleCycleClass hM hn hnX := by
  simpa only [invertibleModuleCycleClass, map_add] using
    congrArg (Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl)
      (invertibleModuleMultiplicativeGroupH1_tensor hL hM)

/-- The actual tensor unit has zero native H¹(Gm) class. -/
theorem invertibleModuleMultiplicativeGroupH1_unit (X : Scheme.{u}) [IsIntegral X] :
    invertibleModuleMultiplicativeGroupH1 (Scheme.Modules.isInvertible_unit X) = 0 :=
  invertibleModuleMultiplicativeGroupH1_of_globalFrame (Scheme.Modules.isInvertible_unit X)
    (unitSection ⊤) (isFrameOn_unitSection ⊤)

/-- Actual tensor powers give the original integer multiple in
native H¹(Gm). -/
theorem invertibleModuleMultiplicativeGroupH1_tensorPow
    (hM : IsInvertible M) (n : ℕ) :
    invertibleModuleMultiplicativeGroupH1 (hM.tensorPow n) =
      n • invertibleModuleMultiplicativeGroupH1 hM := by
  induction n with
  | zero =>
      have hunit := invertibleModuleMultiplicativeGroupH1_iso
        (M := M.tensorPow 0) (N := SheafOfModules.unit X.ringCatSheaf) (hM.tensorPow 0)
        (Scheme.Modules.isInvertible_unit X)
        (eqToIso ((tensorPow_zero M).trans (Scheme.Modules.tensorUnit_eq (X := X))))
      exact (hunit.trans (invertibleModuleMultiplicativeGroupH1_unit X)).trans
        (zero_nsmul (invertibleModuleMultiplicativeGroupH1 hM)).symm
  | succ n ih =>
      have hsucc := invertibleModuleMultiplicativeGroupH1_iso
        (M := M.tensorPow (n + 1)) (N := M.tensorPow n ⊗ M)
        (hM.tensorPow (n + 1)) ((hM.tensorPow n).tensor hM)
        (eqToIso (tensorPow_succ M n))
      have ht := invertibleModuleMultiplicativeGroupH1_tensor
        (L := M.tensorPow n) (M := M) (hM.tensorPow n) hM
      exact hsucc.trans (ht.trans
        ((congrArg (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 =>
          z + invertibleModuleMultiplicativeGroupH1 hM) ih).trans
          (succ_nsmul (invertibleModuleMultiplicativeGroupH1 hM) n).symm))

/-- An actual nth tensor power has zero original μn cycle class,
by the actual power map in the original Kummer sequence. -/
theorem invertibleModuleCycleClass_tensorPow_self
    (hM : IsInvertible M) {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    invertibleModuleCycleClass (hM.tensorPow n) hn hnX = 0 := by
  rw [invertibleModuleCycleClass, invertibleModuleMultiplicativeGroupH1_tensorPow hM,
    ← etaleMultiplicativeGroupPower_cohomology_apply X n 1]
  let hS := etaleKummerComplex_shortExact X hn hnX
  let b := invertibleModuleMultiplicativeGroupH1 hM
  change (b.comp (Ext.mk₀ (etaleMultiplicativeGroupPower X n))
    (add_zero 1)).comp hS.extClass rfl = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- A genuine tensor-power root annihilates the original native
Kummer class of the same original line bundle. -/
theorem invertibleModuleCycleClass_eq_zero_of_tensorPowIso
    (hL : IsInvertible L) (hM : IsInvertible M) {n : ℕ}
    (e : L ≅ M.tensorPow n) (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    invertibleModuleCycleClass hL hn hnX = 0 :=
  (invertibleModuleCycleClass_iso hL (hM.tensorPow n) e hn hnX).trans
    (invertibleModuleCycleClass_tensorPow_self hM hn hnX)

end EtaleCohomology
