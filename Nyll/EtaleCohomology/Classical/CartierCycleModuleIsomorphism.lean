/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitLocalSections
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitSections
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitRegularOpenSections
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.ZariskiH0Ext
public import Nyll.SchemeTheory.Sheaves.IdealModuleLocalGenerators
public import Nyll.SchemeTheory.Sheaves.IdealModuleRationalComparison
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataRangeModuleIotaAppInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Actual Cartier classes are invariant under ideal-module isomorphism

An actual ideal-module isomorphism supplies a single rational multiplier.
Its image carries every affine generator of the source ideal to a generator
of the target ideal. The two original generic-unit H⁰ classes consequently
differ by the image of that actual global rational unit. The original
generic-unit boundary kills this difference, so their native H¹(Gm) and
Kummer H² classes agree. No Picard/cohomology comparison is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Abelian Limits Opposite

namespace EtaleCohomology

/-- The actual H⁰ image of a global rational unit evaluates to its
original quotient section on every object of the small étale site. -/
theorem genericPointUnitQuotientH0_section
    (X : Scheme.{u}) [IsIntegral X] (a : Additive X.functionFieldˣ) (V : X.Etale) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (etaleGenericUnitQuotient X).obj.map (hT.from V).op
      (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT
        (Sheaf.H.map (etaleGenericUnitShortComplex X).g 0
          ((genericPointUnitsH0Equiv X).symm a))) =
      genericPointRationalUnitQuotientSection X V a := by
  intro hT
  let B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
      (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))
  let Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient X
  let π : B ⟶ Q := (etaleGenericUnitShortComplex X).g
  let b : Sheaf.H.{u} B 0 := (genericPointUnitsH0Equiv X).symm a
  have he : Sheaf.H.equiv₀.{u} Q hT (Sheaf.H.map π 0 b) =
      π.hom.app (op (Scheme.Etale.mk (𝟙 X))) (Sheaf.H.equiv₀.{u} B hT b) :=
    (Sheaf.H.equiv₀_naturality.{u} (J := X.smallEtaleTopology)
      (F := B) (G := Q) hT π b).symm
  have hn : Q.obj.map (hT.from V).op
        (π.hom.app (op (Scheme.Etale.mk (𝟙 X))) (Sheaf.H.equiv₀.{u} B hT b)) =
      π.hom.app (op V) (B.obj.map (hT.from V).op (Sheaf.H.equiv₀.{u} B hT b)) :=
    (ConcreteCategory.congr_hom (π.hom.naturality (hT.from V).op)
      (Sheaf.H.equiv₀.{u} B hT b)).symm
  have hr : B.obj.map (hT.from V).op (Sheaf.H.equiv₀.{u} B hT b) =
      rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X)) V a :=
    (genericPointUnitsH0Equiv_section X b V).trans
      (congrArg
        (fun c : Additive X.functionFieldˣ =>
          rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X)) V c)
        ((genericPointUnitsH0Equiv X).apply_symm_apply a))
  exact (congrArg
    (fun z : Q.obj.obj (op (Scheme.Etale.mk (𝟙 X))) =>
      Q.obj.map (hT.from V).op z) he).trans
      (hn.trans (congrArg (fun z : B.obj.obj (op V) => π.hom.app (op V) z) hr))

/-- The difference of the actual Cartier quotient sections is the
original H⁰ image of the rational unit constructed from a module iso. -/
theorem effectiveCartierGenericUnitH0_moduleIso
    {X : Scheme.{u}} [IsIntegral X] (D E : Scheme.EffectiveCartierDivisor X)
    (e : D.1.module ≅ E.1.module) :
    ∃ a : Additive X.functionFieldˣ,
      let m : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
        Sheaf.H.map (etaleGenericUnitShortComplex X).g 0
          ((genericPointUnitsH0Equiv X).symm a)
      effectiveCartierGenericUnitH0 E = m + effectiveCartierGenericUnitH0 D := by
  obtain ⟨a, ha⟩ := Scheme.IdealSheafData.exists_unit_moduleIso_eq_mul D.2 e
  refine ⟨Additive.ofMul a, ?_⟩
  intro m
  apply etaleAbelianH0_ext_zariski X (etaleGenericUnitQuotient X)
  intro x
  obtain ⟨U, hxU, f, hf, hD⟩ := D.2 x
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  have hfmem : f ∈ Set.range (D.1.moduleι.app U) := by
    rw [(D.1.range_moduleIota_app_and_injective U).1, hD]
    exact Ideal.mem_span_singleton_self f
  obtain ⟨s, hs⟩ := hfmem
  let g : Γ(X, U.1) := E.1.moduleι.app U.1 (e.hom.app U.1 s)
  have hE : E.1.ideal U = Ideal.span {g} :=
    Scheme.IdealSheafData.span_moduleIota_moduleIso_generator e U s
      (hD.trans (congrArg (fun z : Γ(X, U.1) => Ideal.span {z}) hs.symm))
  have hvalue : X.germToFunctionField U.1 g =
      (a : X.functionField) * X.germToFunctionField U.1 f :=
    (ha U.1 s).trans
      (congrArg (fun z : Γ(X, U.1) =>
        (a : X.functionField) * X.germToFunctionField U.1 z) hs)
  have hg0 : g ≠ 0 := by
    intro hg
    have hz : (0 : X.functionField) =
        (a : X.functionField) * X.germToFunctionField U.1 f := by
      simpa only [hg, map_zero] using hvalue
    exact (mul_ne_zero a.ne_zero (openSectionRationalUnit X U.1 f hf0).ne_zero) hz.symm
  have hunit : openSectionRationalUnit X U.1 g hg0 =
      a * openSectionRationalUnit X U.1 f hf0 := by
    apply Units.ext
    exact hvalue
  refine ⟨U.1, hxU, ?_⟩
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let ev : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      (etaleGenericUnitQuotient X).obj.obj (op ((zariskiToEtale X).obj U.1)) :=
    ((etaleGenericUnitQuotient X).obj.map
      (hT.from ((zariskiToEtale X).obj U.1)).op).hom.comp
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT).toAddMonoidHom
  change ev (effectiveCartierGenericUnitH0 E) = ev (m + effectiveCartierGenericUnitH0 D)
  have hsecE : ev (effectiveCartierGenericUnitH0 E) =
      openSectionGenericUnitQuotient X U.1 g hg0 :=
    effectiveCartierGenericUnitH0_section E U g hg0 hE
  have hsecD : ev (effectiveCartierGenericUnitH0 D) =
      openSectionGenericUnitQuotient X U.1 f hf0 :=
    effectiveCartierGenericUnitH0_section D U f hf0 hD
  have himage : ev m = genericPointRationalUnitQuotientSection X
      ((zariskiToEtale X).obj U.1) (Additive.ofMul a) :=
    genericPointUnitQuotientH0_section X (Additive.ofMul a) ((zariskiToEtale X).obj U.1)
  let q := genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U.1)
  have hq : openSectionGenericUnitQuotient X U.1 g hg0 =
      genericPointRationalUnitQuotientSection X ((zariskiToEtale X).obj U.1)
        (Additive.ofMul a) + openSectionGenericUnitQuotient X U.1 f hf0 :=
    (congrArg (fun b : X.functionFieldˣ => q (Additive.ofMul b)) hunit).trans
      (map_add q (Additive.ofMul a)
        (Additive.ofMul (openSectionRationalUnit X U.1 f hf0)))
  exact hsecE.trans
    (hq.trans
      ((congrArg₂
        (fun v w : (etaleGenericUnitQuotient X).obj.obj
          (op ((zariskiToEtale X).obj U.1)) => v + w) himage.symm hsecD.symm).trans
        (ev.map_add m (effectiveCartierGenericUnitH0 D)).symm))

/-- Isomorphic actual ideal modules have the same original H¹(Gm)
class. The vanishing rational difference is proved in the original
generic-unit long exact sequence. -/
theorem effectiveCartierMultiplicativeGroupH1_eq_of_moduleIso
    {X : Scheme.{u}} [IsIntegral X] (D E : Scheme.EffectiveCartierDivisor X)
    (e : D.1.module ≅ E.1.module) :
    effectiveCartierMultiplicativeGroupH1 D = effectiveCartierMultiplicativeGroupH1 E := by
  obtain ⟨a, ha⟩ := effectiveCartierGenericUnitH0_moduleIso D E e
  let S := etaleGenericUnitShortComplex X
  have hS : S.ShortExact := etaleGenericUnitShortComplex_shortExact X
  let b : Sheaf.H.{u} S.X₂ 0 := (genericPointUnitsH0Equiv X).symm a
  let m : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 := Sheaf.H.map S.g 0 b
  let δ : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 := Sheaf.H.δ hS 0 1 rfl
  have hz : δ m = 0 := by
    change (b.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass (zero_add 1) = 0
    exact (Ext.comp_assoc_of_second_deg_zero b (Ext.mk₀ S.g) hS.extClass
      (zero_add 1)).trans
        ((congrArg
          (fun q : Ext.{u} S.X₂ S.X₁ 1 => b.comp q (zero_add 1))
          hS.comp_extClass).trans (Ext.comp_zero b S.X₁ 1 1 (zero_add 1)))
  have he : δ (effectiveCartierGenericUnitH0 E) = δ (effectiveCartierGenericUnitH0 D) :=
    (congrArg δ ha).trans
      ((δ.map_add m (effectiveCartierGenericUnitH0 D)).trans
        ((congrArg
          (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 =>
            z + δ (effectiveCartierGenericUnitH0 D)) hz).trans
          (zero_add (δ (effectiveCartierGenericUnitH0 D)))))
  exact he.symm

/-- Isomorphic actual ideal modules have the same original Kummer
cycle class on an integral scheme of any dimension. -/
theorem effectiveCartierCycleClass_eq_of_moduleIso
    {X : Scheme.{u}} [IsIntegral X] (D E : Scheme.EffectiveCartierDivisor X)
    (e : D.1.module ≅ E.1.module) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    effectiveCartierCycleClass D hn hnX = effectiveCartierCycleClass E hn hnX :=
  congrArg (Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl)
    (effectiveCartierMultiplicativeGroupH1_eq_of_moduleIso D E e)

end EtaleCohomology
