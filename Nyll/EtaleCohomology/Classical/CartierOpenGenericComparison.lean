/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitLocalSections
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitSections
public import Nyll.EtaleCohomology.Classical.CartierOpenUnitSections
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitRegularOpenSections
public import Nyll.EtaleCohomology.Classical.OpenUnitEquationSections
public import Nyll.EtaleCohomology.Classical.OpenUnitQuotientEquations
public import Nyll.EtaleCohomology.Classical.UnitDirectImageSquares
public import Nyll.EtaleCohomology.Classical.UnitQuotientFunctoriality
public import Nyll.EtaleCohomology.Classical.ZariskiH0Ext
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Cartier complement classes and original generic-unit classes

The actual generic-point morphism factors through every nonempty open
of an integral scheme. The resulting actual map of unit quotients sends
every original local equation to its original rational representative.
It therefore sends the genuinely glued Cartier class to the original
generic-unit Cartier class. The original boundaries agree, so the open
complement construction computes the original H¹(Gm) class.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The original generic point belongs to every nonempty open. -/
theorem genericPoint_mem_nonemptyOpen
    (X : Scheme.{u}) [IsIntegral X] (O : X.Opens) [Nonempty O] :
    genericPoint X ∈ O := by
  obtain ⟨x⟩ := (show Nonempty O from inferInstance)
  exact ((genericPoint_spec X).mem_open_set_iff O.isOpen).mpr
    ⟨x.1, trivial, x.2⟩

/-- The actual generic-point factor through a nonempty open. -/
def genericPointNonemptyOpenFactor
    (X : Scheme.{u}) [IsIntegral X] (O : X.Opens) [Nonempty O] :
    Spec X.functionField ⟶ O :=
  O.fromSpecStalkOfMem (genericPoint X) (genericPoint_mem_nonemptyOpen X O)

/-- The factor is a morphism over the original scheme. -/
theorem genericPointNonemptyOpenFactor_ι
    (X : Scheme.{u}) [IsIntegral X] (O : X.Opens) [Nonempty O] :
    genericPointNonemptyOpenFactor X O ≫ O.ι = X.fromSpecStalk (genericPoint X) :=
  O.fromSpecStalkOfMem_ι (genericPoint X) (genericPoint_mem_nonemptyOpen X O)

/-- Restriction of actual units on the nonempty open to actual generic
units induces this original cokernel map. -/
def etaleOpenUnitGenericComparison
    (X : Scheme.{u}) [IsIntegral X] (O : X.Opens) [Nonempty O] :
    etaleUnitQuotient O.ι ⟶ etaleGenericUnitQuotient X :=
  etaleUnitQuotientOverMap O.ι (X.fromSpecStalk (genericPoint X))
    (genericPointNonemptyOpenFactor X O) (genericPointNonemptyOpenFactor_ι X O)

/-- Monicity follows from factorization into the original monic
generic-unit map, with no extra compactness hypothesis on the open. -/
theorem etaleMultiplicativeGroupToNonemptyOpen_mono
    (X : Scheme.{u}) [IsIntegral X] (O : X.Opens) [Nonempty O] :
    Mono (etaleMultiplicativeGroupToPushforward O.ι) := by
  have : Mono (etaleMultiplicativeGroupToPushforward
      (X.fromSpecStalk (genericPoint X))) :=
    etaleMultiplicativeGroupToGenericPoint_mono X
  exact mono_of_mono_fac (etaleUnitDirectImageOverMap_unit
    O.ι (X.fromSpecStalk (genericPoint X))
      (genericPointNonemptyOpenFactor X O) (genericPointNonemptyOpenFactor_ι X O))

/-- The original short exact sequence for units on a nonempty open. -/
theorem etaleNonemptyOpenUnitShortComplex_shortExact
    (X : Scheme.{u}) [IsIntegral X] (O : X.Opens) [Nonempty O] :
    (etaleUnitShortComplex O.ι).ShortExact := by
  have : Mono (etaleMultiplicativeGroupToPushforward O.ι) :=
    etaleMultiplicativeGroupToNonemptyOpen_mono X O
  exact etaleUnitShortComplex_shortExact O.ι

/-- The actual open-unit comparison takes every equation to its literal
original function-field representative in the generic quotient. -/
theorem etaleOpenUnitGenericComparison_equation
    (X : Scheme.{u}) [IsIntegral X] (O U : X.Opens)
    [Nonempty O] [Nonempty U] (f : Γ(X, U)) (hf : f ≠ 0)
    (hO : U ⊓ O ≤ X.basicOpen f) :
    (etaleOpenUnitGenericComparison X O).hom.app (op ((zariskiToEtale X).obj U))
        (openEquationUnitQuotientSection X O U f hO) =
      openSectionGenericUnitQuotient X U f hf := by
  let j := X.fromSpecStalk (genericPoint X)
  let p := genericPointNonemptyOpenFactor X O
  let hp := genericPointNonemptyOpenFactor_ι X O
  let V := (zariskiToEtale X).obj U
  let k : pullback U.ι j ⟶ pullback U.ι O.ι :=
    etaleUnitDirectImageOverSchemeMap O.ι j p hp V
  have hk : k ≫ pullback.fst U.ι O.ι = pullback.fst U.ι j :=
    pullback.lift_fst _ _ _
  have hr : openSectionBaseChangeRing O.ι U ≫ k.appTop =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
        (pullback.snd U.ι j).appTop := by
    change (U.topIso.inv ≫ (pullback.fst U.ι O.ι).appTop) ≫ k.appTop = _
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, hk]
    exact genericPointOpenUnit_ring_square X U
  have hu : (etaleUnitDirectImageOverMap O.ι j p hp).hom.app (op V)
      (openEquationDirectImageUnitSection X O U f hO) =
      rationalUnitDirectImageSection j V
        (Additive.ofMul (openSectionRationalUnit X U f hf)) := by
    apply (Additive.toMul (α := (Γ(pullback U.ι j, ⊤) : Type u)ˣ)).injective
    apply Units.ext
    change k.appTop ((openEquationDirectImageUnitSection X O U f hO).toMul.val) =
      (((Scheme.ΓSpecIso X.functionField).inv ≫ (pullback.snd U.ι j).appTop)
        (X.germToFunctionField U f))
    exact (congrArg (fun r : Γ(pullback U.ι O.ι, ⊤) => k.appTop r)
      (openEquationDirectImageUnitSection_val X O U f hO)).trans
        (ConcreteCategory.congr_hom hr f)
  have hπ := ConcreteCategory.congr_hom
    (congrArg (fun a => a.hom.app (op V))
      (etaleUnitQuotientOverMap_π O.ι j p hp))
        (openEquationDirectImageUnitSection X O U f hO)
  change (etaleOpenUnitGenericComparison X O).hom.app (op V)
      (openEquationUnitQuotientSection X O U f hO) =
    (etaleUnitShortComplex j).g.hom.app (op V)
      ((etaleUnitDirectImageOverMap O.ι j p hp).hom.app (op V)
        (openEquationDirectImageUnitSection X O U f hO)) at hπ
  rw [hu] at hπ
  exact hπ

/-- The comparison sends the genuinely glued open-unit H⁰ class to the
original generic-unit H⁰ class of the same actual Cartier divisor. -/
theorem effectiveCartierOpenUnitH0_generic
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) [Nonempty O] (hO : O ≤ D.1.support.compl) :
    Sheaf.H.map (etaleOpenUnitGenericComparison X O) 0
        (effectiveCartierOpenUnitH0 D O hO) =
      effectiveCartierGenericUnitH0 D := by
  apply etaleAbelianH0_ext_zariski X (etaleGenericUnitQuotient X)
  intro x
  obtain ⟨U, hxU, f, hreg, hI⟩ := D.2 x
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have hf : f ≠ 0 := by
    intro hz
    apply (zero_ne_one : (0 : Γ(X, U.1)) ≠ 1)
    exact hreg.left (by simp only [hz, zero_mul])
  refine ⟨U.1, hxU, ?_⟩
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let φ := etaleOpenUnitGenericComparison X O
  let a := effectiveCartierOpenUnitH0 D O hO
  let t := (hT.from ((zariskiToEtale X).obj U.1)).op
  change (etaleGenericUnitQuotient X).obj.map t
      (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT (Sheaf.H.map φ 0 a)) = _
  have he : Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT
        (Sheaf.H.map φ 0 a) =
      φ.hom.app (op (Scheme.Etale.mk (𝟙 X)))
        (Sheaf.H.equiv₀.{u} (etaleUnitQuotient O.ι) hT a) :=
    (Sheaf.H.equiv₀_naturality.{u} (J := X.smallEtaleTopology)
      (F := etaleUnitQuotient O.ι) (G := etaleGenericUnitQuotient X) hT φ a).symm
  have hn : (etaleGenericUnitQuotient X).obj.map t
        (φ.hom.app (op (Scheme.Etale.mk (𝟙 X)))
          (Sheaf.H.equiv₀.{u} (etaleUnitQuotient O.ι) hT a)) =
      φ.hom.app (op ((zariskiToEtale X).obj U.1))
        ((etaleUnitQuotient O.ι).obj.map t
          (Sheaf.H.equiv₀.{u} (etaleUnitQuotient O.ι) hT a)) :=
    (ConcreteCategory.congr_hom (φ.hom.naturality t)
      (Sheaf.H.equiv₀.{u} (etaleUnitQuotient O.ι) hT a)).symm
  have hlocal : (etaleUnitQuotient O.ι).obj.map t
        (Sheaf.H.equiv₀.{u} (etaleUnitQuotient O.ι) hT a) =
      openEquationUnitQuotientSection X O U.1 f
        (idealGenerator_avoidingOpen_le_basicOpen X D.1 O hO U f hI) :=
    effectiveCartierOpenUnitH0_section D O hO U f hI
  have hgeneric : (etaleGenericUnitQuotient X).obj.map t
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT
          (effectiveCartierGenericUnitH0 D)) =
      openSectionGenericUnitQuotient X U.1 f hf :=
    effectiveCartierGenericUnitH0_section D U f hf hI
  exact (congrArg ((etaleGenericUnitQuotient X).obj.map t) he).trans
    (hn.trans ((congrArg (φ.hom.app (op ((zariskiToEtale X).obj U.1))) hlocal).trans
      ((etaleOpenUnitGenericComparison_equation X O U.1 f hf _).trans hgeneric.symm)))

/-- The open-unit boundary is exactly the original Cartier H¹(Gm)
class, proved through the actual comparison of short exact sequences. -/
theorem effectiveCartierOpenUnitH0_boundary
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) [Nonempty O] (hO : O ≤ D.1.support.compl) :
    Sheaf.H.δ (etaleNonemptyOpenUnitShortComplex_shortExact X O) 0 1 rfl
        (effectiveCartierOpenUnitH0 D O hO) =
      effectiveCartierMultiplicativeGroupH1 D := by
  have : Mono (etaleMultiplicativeGroupToPushforward O.ι) :=
    etaleMultiplicativeGroupToNonemptyOpen_mono X O
  have : Mono (etaleMultiplicativeGroupToPushforward
      (X.fromSpecStalk (genericPoint X))) :=
    etaleMultiplicativeGroupToGenericPoint_mono X
  have hδ := etaleUnitBoundary_zero_over O.ι (X.fromSpecStalk (genericPoint X))
    (genericPointNonemptyOpenFactor X O) (genericPointNonemptyOpenFactor_ι X O)
      (effectiveCartierOpenUnitH0 D O hO)
  change Sheaf.H.δ (etaleNonemptyOpenUnitShortComplex_shortExact X O) 0 1 rfl
      (effectiveCartierOpenUnitH0 D O hO) =
    Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
      (Sheaf.H.map (etaleOpenUnitGenericComparison X O) 0
        (effectiveCartierOpenUnitH0 D O hO)) at hδ
  rw [effectiveCartierOpenUnitH0_generic] at hδ
  exact hδ

/-- An actual effective Cartier divisor on an integral scheme misses
the original generic point. -/
theorem effectiveCartier_genericPoint_not_mem_support
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) :
    genericPoint X ∉ D.1.support := by
  obtain ⟨U, hxU, f, hreg, hI⟩ := D.2 (genericPoint X)
  have : Nonempty U.1 := ⟨⟨genericPoint X, hxU⟩⟩
  have hf : f ≠ 0 := by
    intro hz
    apply (zero_ne_one : (0 : Γ(X, U.1)) ≠ 1)
    exact hreg.left (by simp only [hz, zero_mul])
  have hg : IsUnit (X.germToFunctionField U.1 f) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hf
    apply X.germToFunctionField_injective U.1
    exact hz.trans (map_zero (X.germToFunctionField U.1).hom).symm
  have hb : genericPoint X ∈ X.basicOpen f :=
    (X.mem_basicOpen f (genericPoint X) hxU).mpr hg
  intro hs
  have hz := (D.1.mem_support_iff_of_mem hxU).mp hs
  rw [hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton] at hz
  exact hz hb

/-- The actual Cartier complement is nonempty, as required for its
original short exact unit sequence. -/
theorem effectiveCartier_complement_nonempty
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) :
    Nonempty D.1.support.compl :=
  ⟨⟨genericPoint X, effectiveCartier_genericPoint_not_mem_support D⟩⟩

end EtaleCohomology
