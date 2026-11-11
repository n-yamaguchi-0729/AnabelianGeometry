/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalIsomorphism
public import Nyll.EtaleCohomology.Classical.CartierCycleModuleIsomorphism
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitRegularOpenSections
public import Nyll.EtaleCohomology.Classical.InvertibleGenericUnitLocalSections
public import Nyll.EtaleCohomology.Classical.InvertibleGenericUnitSections
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.ZariskiH0Ext
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Native cycle classes of actual invertible modules

The original generic-unit boundary gives an actual H¹(Gm) class for
every invertible module. The sign converts its rational frame values,
which describe the fractional ideal, to the class of the line bundle.
An actual module isomorphism changes the quotient H⁰ representative by
one original global rational unit. The original exact sequence kills
that change. The subsequent original Kummer boundary gives the native
degree-two class, with no supplied Picard/cohomology comparison.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Abelian Limits Opposite
open Scheme.Modules

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] {M N : X.Modules}

/-- The actual module isomorphism changes the original quotient H⁰
class by the image of its original global rational multiplier. -/
theorem invertibleModuleGenericUnitH0_iso
    (hM : IsInvertible M) (hN : IsInvertible N) (e : M ≅ N) :
    ∃ a : Additive X.functionFieldˣ,
      let m : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
        Sheaf.H.map (etaleGenericUnitShortComplex X).g 0
          ((genericPointUnitsH0Equiv X).symm a)
      invertibleModuleGenericUnitH0 hN = m + invertibleModuleGenericUnitH0 hM := by
  obtain ⟨a, ha⟩ := hM.exists_unit_functionFieldHom_iso_eq_mul hN e
  refine ⟨Additive.ofMul a, ?_⟩
  intro m
  apply etaleAbelianH0_ext_zariski X (etaleGenericUnitQuotient X)
  intro x
  obtain ⟨U, s, hxU, hs⟩ := hM.exists_frameSection x
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hunit : hN.frameRationalUnit U (e.hom.app U s) (hs.map_iso e) =
      a * hM.frameRationalUnit U s hs := by
    apply Units.ext
    exact ha U s
  refine ⟨U, hxU, ?_⟩
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let ev : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      (etaleGenericUnitQuotient X).obj.obj (op ((zariskiToEtale X).obj U)) :=
    ((etaleGenericUnitQuotient X).obj.map
      (hT.from ((zariskiToEtale X).obj U)).op).hom.comp
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT).toAddMonoidHom
  change ev (invertibleModuleGenericUnitH0 hN) = ev (m + invertibleModuleGenericUnitH0 hM)
  have hsecN : ev (invertibleModuleGenericUnitH0 hN) =
      invertibleFrameGenericUnitQuotient hN U (e.hom.app U s) (hs.map_iso e) :=
    invertibleModuleGenericUnitH0_section hN U (e.hom.app U s) (hs.map_iso e)
  have hsecM : ev (invertibleModuleGenericUnitH0 hM) =
      invertibleFrameGenericUnitQuotient hM U s hs :=
    invertibleModuleGenericUnitH0_section hM U s hs
  have himage : ev m = genericPointRationalUnitQuotientSection X
      ((zariskiToEtale X).obj U) (Additive.ofMul a) :=
    genericPointUnitQuotientH0_section X (Additive.ofMul a) ((zariskiToEtale X).obj U)
  let q := genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U)
  have hq : invertibleFrameGenericUnitQuotient hN U (e.hom.app U s) (hs.map_iso e) =
      genericPointRationalUnitQuotientSection X ((zariskiToEtale X).obj U)
        (Additive.ofMul a) + invertibleFrameGenericUnitQuotient hM U s hs :=
    (congrArg (fun b : X.functionFieldˣ => q (Additive.ofMul b)) hunit).trans
      (map_add q (Additive.ofMul a) (Additive.ofMul (hM.frameRationalUnit U s hs)))
  exact hsecN.trans
    (hq.trans
      ((congrArg₂
        (fun v w : (etaleGenericUnitQuotient X).obj.obj
          (op ((zariskiToEtale X).obj U)) => v + w) himage.symm hsecM.symm).trans
        (ev.map_add m (invertibleModuleGenericUnitH0 hM)).symm))

/-- The original generic-unit boundary vanishes on the original
image of every global rational unit. -/
theorem genericPointUnitH0_boundary_zero (a : Additive X.functionFieldˣ) :
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
      (Sheaf.H.map (etaleGenericUnitShortComplex X).g 0
        ((genericPointUnitsH0Equiv X).symm a)) = 0 := by
  let S := etaleGenericUnitShortComplex X
  have hS : S.ShortExact := etaleGenericUnitShortComplex_shortExact X
  let b : Sheaf.H.{u} S.X₂ 0 := (genericPointUnitsH0Equiv X).symm a
  change (b.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass (zero_add 1) = 0
  exact (Ext.comp_assoc_of_second_deg_zero b (Ext.mk₀ S.g) hS.extClass
    (zero_add 1)).trans
      ((congrArg
        (fun q : Ext.{u} S.X₂ S.X₁ 1 => b.comp q (zero_add 1))
        hS.comp_extClass).trans (Ext.comp_zero b S.X₁ 1 1 (zero_add 1)))

/-- The actual native H¹(Gm) class of the original line bundle. -/
def invertibleModuleMultiplicativeGroupH1 (hM : IsInvertible M) :
    Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
  -Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
    (invertibleModuleGenericUnitH0 hM)

/-- Actual isomorphic line bundles have the same original native
H¹(Gm) class. -/
theorem invertibleModuleMultiplicativeGroupH1_iso
    (hM : IsInvertible M) (hN : IsInvertible N) (e : M ≅ N) :
    invertibleModuleMultiplicativeGroupH1 hM =
      invertibleModuleMultiplicativeGroupH1 hN := by
  obtain ⟨a, ha⟩ := invertibleModuleGenericUnitH0_iso hM hN e
  let δ : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
  let m : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
    Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 ((genericPointUnitsH0Equiv X).symm a)
  have hz : δ m = 0 := genericPointUnitH0_boundary_zero a
  have he : δ (invertibleModuleGenericUnitH0 hN) = δ (invertibleModuleGenericUnitH0 hM) :=
    (congrArg δ ha).trans
      ((δ.map_add m (invertibleModuleGenericUnitH0 hM)).trans
        ((congrArg
          (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 =>
            z + δ (invertibleModuleGenericUnitH0 hM)) hz).trans
          (zero_add (δ (invertibleModuleGenericUnitH0 hM)))))
  exact congrArg (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 => -z) he.symm

/-- The original Kummer boundary of the actual native line-bundle
class, with the original roots-of-unity coefficient sheaf. -/
def invertibleModuleCycleClass (hM : IsInvertible M) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 2 :=
  Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl
    (invertibleModuleMultiplicativeGroupH1 hM)

/-- Actual line-bundle isomorphisms preserve the original Kummer
degree-two class. -/
theorem invertibleModuleCycleClass_iso
    (hM : IsInvertible M) (hN : IsInvertible N) (e : M ≅ N) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    invertibleModuleCycleClass hM hn hnX = invertibleModuleCycleClass hN hn hnX :=
  congrArg (Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl)
    (invertibleModuleMultiplicativeGroupH1_iso hM hN e)

/-- An actual global frame makes the original quotient representative
the image of its single original rational value. -/
theorem invertibleModuleGenericUnitH0_of_globalFrame
    (hM : IsInvertible M) (s : Γ(M, ⊤)) (hs : IsFrameOn s ⊤) :
    let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    invertibleModuleGenericUnitH0 hM =
      Sheaf.H.map (etaleGenericUnitShortComplex X).g 0
        ((genericPointUnitsH0Equiv X).symm
          (Additive.ofMul (hM.frameRationalUnit ⊤ s hs))) := by
  intro htop
  apply etaleAbelianH0_ext_zariski X (etaleGenericUnitQuotient X)
  intro x
  refine ⟨⊤, trivial, ?_⟩
  exact (invertibleModuleGenericUnitH0_section hM ⊤ s hs).trans
    (genericPointUnitQuotientH0_section X
      (Additive.ofMul (hM.frameRationalUnit ⊤ s hs)) ((zariskiToEtale X).obj ⊤)).symm

/-- The original native class vanishes for an actual globally framed
line bundle. -/
theorem invertibleModuleMultiplicativeGroupH1_of_globalFrame
    (hM : IsInvertible M) (s : Γ(M, ⊤)) (hs : IsFrameOn s ⊤) :
    invertibleModuleMultiplicativeGroupH1 hM = 0 := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let δ : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
  have hz : δ (invertibleModuleGenericUnitH0 hM) = 0 :=
    (congrArg δ (invertibleModuleGenericUnitH0_of_globalFrame hM s hs)).trans
      (genericPointUnitH0_boundary_zero (Additive.ofMul (hM.frameRationalUnit ⊤ s hs)))
  exact (congrArg (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 => -z) hz).trans
    neg_zero

end EtaleCohomology
