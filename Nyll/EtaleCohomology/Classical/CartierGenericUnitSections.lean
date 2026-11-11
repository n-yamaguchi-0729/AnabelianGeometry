/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierGenericUnitLocalSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Nyll.SchemeTheory.Divisors.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Actual Cartier divisors as original generic-unit sections

The local equations furnished by an effective Cartier divisor have compatible
classes in the original generic-unit quotient. The genuine sheaf condition
glues them on the Zariski restriction of that quotient. The resulting native
H⁰ class is characterized by every actual affine local equation, independently
of the charts used in its construction.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- Choose an affine local equation for an effective Cartier divisor at each point. -/
def effectiveCartierEquation
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) (x : X) :
    Σ U : X.affineOpens,
      {f : Γ(X, U.1) // x ∈ U.1 ∧ f ≠ 0 ∧ D.1.ideal U = Ideal.span {f}} := by
  let U := Classical.choose (D.2 x)
  have hU : ∃ (_hx : x ∈ U.1) (f : Γ(X, U.1)),
      IsRegular f ∧ D.1.ideal U = Ideal.span {f} := Classical.choose_spec (D.2 x)
  have hx : x ∈ U.1 := Classical.choose hU
  have hex : ∃ f : Γ(X, U.1), IsRegular f ∧ D.1.ideal U = Ideal.span {f} :=
    Classical.choose_spec hU
  let f := Classical.choose hex
  have hf : IsRegular f ∧ D.1.ideal U = Ideal.span {f} := Classical.choose_spec hex
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  refine ⟨U, f, hx, ?_, hf.2⟩
  intro hzero
  apply (zero_ne_one : (0 : Γ(X, U.1)) ≠ 1)
  exact hf.1.left (by
    change f * (0 : Γ(X, U.1)) = f * (1 : Γ(X, U.1))
    rw [hzero, zero_mul, zero_mul])

/-- A chosen local equation gives a section of the original generic-unit quotient. -/
def effectiveCartierEquationSection
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) (x : X) :
    (etaleGenericUnitQuotient X).obj.obj
      (op ((zariskiToEtale X).obj (effectiveCartierEquation D x).1.1)) := by
  let e := effectiveCartierEquation D x
  have : Nonempty e.1.1 := ⟨⟨x, e.2.property.1⟩⟩
  exact openSectionGenericUnitQuotient X e.1.1 e.2.val e.2.property.2.1

/-- The quotient sections of the chosen local equations agree on overlaps. -/
theorem effectiveCartierEquationSections_compatible
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) :
    TopCat.Presheaf.IsCompatible
      ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X)).obj
      (fun x : X => (effectiveCartierEquation D x).1.1)
      (effectiveCartierEquationSection D) := by
  intro x y
  let e := effectiveCartierEquation D x
  let d := effectiveCartierEquation D y
  have : Nonempty e.1.1 := ⟨⟨x, e.2.property.1⟩⟩
  have : Nonempty d.1.1 := ⟨⟨y, d.2.property.1⟩⟩
  exact idealSheafGenerators_genericUnit_overlap X D.1 e.1 d.1
    e.2.val d.2.val e.2.property.2.1 d.2.property.2.1
    e.2.property.2.2 d.2.property.2.2

/-- Glue the local equation classes, retaining their restriction identities. -/
def effectiveCartierGenericUnitGluing
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) :
    {s : ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X)).obj.obj (op (⊤ : X.Opens)) //
      ∀ x : X, ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X)).obj.map
          (homOfLE (show (effectiveCartierEquation D x).1.1 ≤ ⊤ from le_top)).op s =
            effectiveCartierEquationSection D x} := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X)
  let U : X → X.Opens := fun x => (effectiveCartierEquation D x).1.1
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨x, (effectiveCartierEquation D x).2.property.1⟩
  let h := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover
    (effectiveCartierEquationSection D) (effectiveCartierEquationSections_compatible D)
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/-- The global section obtained by actual sheaf gluing of the divisor's
actual local equations in the original quotient. -/
def effectiveCartierGenericUnitZariskiSection
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) :
    ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleGenericUnitQuotient X)).obj.obj (op (⊤ : X.Opens)) :=
  (effectiveCartierGenericUnitGluing D).val

/-- Every genuine affine local equation computes the glued section.
No compatibility of chart choices is part of this theorem's input. -/
theorem effectiveCartierGenericUnitZariskiSection_restrict
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (U : X.affineOpens) [Nonempty U.1] (f : Γ(X, U.1)) (hf : f ≠ 0)
    (hI : D.1.ideal U = Ideal.span {f}) :
    ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleGenericUnitQuotient X)).obj.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
        (effectiveCartierGenericUnitZariskiSection D) =
      openSectionGenericUnitQuotient X U.1 f hf := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X)
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  let e := effectiveCartierEquation D x
  have : Nonempty e.1.1 := ⟨⟨x, e.2.property.1⟩⟩
  refine ⟨U.1 ⊓ e.1.1, inf_le_left, ⟨hx, e.2.property.1⟩, ?_⟩
  have he : F.obj.map (homOfLE (show e.1.1 ≤ ⊤ from le_top)).op
      (effectiveCartierGenericUnitZariskiSection D) =
        openSectionGenericUnitQuotient X e.1.1 e.2.val e.2.property.2.1 :=
    (effectiveCartierGenericUnitGluing D).property x
  have hover := idealSheafGenerators_genericUnit_overlap X D.1 U e.1
    f e.2.val hf e.2.property.2.1 hI e.2.property.2.2
  calc
    F.obj.map (homOfLE (show U.1 ⊓ e.1.1 ≤ U.1 from inf_le_left)).op
        (F.obj.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
          (effectiveCartierGenericUnitZariskiSection D)) =
      F.obj.map (TopologicalSpace.Opens.infLERight U.1 e.1.1).op
        (F.obj.map (homOfLE (show e.1.1 ≤ ⊤ from le_top)).op
          (effectiveCartierGenericUnitZariskiSection D)) := by
            have hthin :
                (homOfLE (show U.1 ≤ ⊤ from le_top)).op ≫
                    (homOfLE (show U.1 ⊓ e.1.1 ≤ U.1 from inf_le_left)).op =
                  (homOfLE (show e.1.1 ≤ ⊤ from le_top)).op ≫
                    (TopologicalSpace.Opens.infLERight U.1 e.1.1).op :=
              Subsingleton.elim _ _
            simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom (congrArg F.obj.map hthin)
                (effectiveCartierGenericUnitZariskiSection D)
    _ = F.obj.map (TopologicalSpace.Opens.infLERight U.1 e.1.1).op
        (openSectionGenericUnitQuotient X e.1.1 e.2.val e.2.property.2.1) :=
      congrArg (F.obj.map (TopologicalSpace.Opens.infLERight U.1 e.1.1).op) he
    _ = F.obj.map (homOfLE (show U.1 ⊓ e.1.1 ≤ U.1 from inf_le_left)).op
        (openSectionGenericUnitQuotient X U.1 f hf) := hover.symm

/-- The original global étale section represented by an actual effective
Cartier divisor. -/
def effectiveCartierGenericUnitSection
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) :
    (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  (etaleZariskiGlobalSectionsIso X AddCommGrpCat.{u}
    (etaleGenericUnitQuotient X)).hom (effectiveCartierGenericUnitZariskiSection D)

/-- The effective Cartier divisor's native H⁰ class in the original
generic-unit quotient. -/
def effectiveCartierGenericUnitH0
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) :
    Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
  (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X)
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X)).symm
        (effectiveCartierGenericUnitSection D)

/-- On the original small étale site the native H⁰ representative is
exactly the class of any actual affine equation for the divisor. -/
theorem effectiveCartierGenericUnitH0_section
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (U : X.affineOpens) [Nonempty U.1] (f : Γ(X, U.1)) (hf : f ≠ 0)
    (hI : D.1.ideal U = Ideal.span {f}) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (etaleGenericUnitQuotient X).obj.map
      (hT.from ((zariskiToEtale X).obj U.1)).op
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT
          (effectiveCartierGenericUnitH0 D)) =
      openSectionGenericUnitQuotient X U.1 f hf := by
  intro hT
  rw [effectiveCartierGenericUnitH0, AddEquiv.apply_symm_apply]
  let e := etaleZariskiGlobalSectionsIso X AddCommGrpCat.{u}
    (etaleGenericUnitQuotient X)
  let s := effectiveCartierGenericUnitZariskiSection D
  let j : (zariskiToEtale X).obj U.1 ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      U.1.ι (Category.comp_id U.1.ι)
  have ht : hT.from ((zariskiToEtale X).obj U.1) = j := hT.hom_ext _ _
  have hr := ConcreteCategory.congr_hom
    (etaleZariskiGlobalSectionsIso_inv_restrict X AddCommGrpCat.{u}
      (etaleGenericUnitQuotient X) U.1) (e.hom s)
  change ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleGenericUnitQuotient X)).obj.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
      (e.inv (e.hom s)) = (etaleGenericUnitQuotient X).obj.map j.op (e.hom s) at hr
  have hc : e.inv (e.hom s) = s := ConcreteCategory.congr_hom e.hom_inv_id s
  rw [hc] at hr
  rw [ht]
  exact hr.symm.trans (effectiveCartierGenericUnitZariskiSection_restrict D U f hf hI)

/-- The empty divisor's glued section is zero; this follows from its
actual local equation `1` on affine neighborhoods. -/
theorem effectiveCartierGenericUnitZariskiSection_empty
    (X : Scheme.{u}) [IsIntegral X] :
    effectiveCartierGenericUnitZariskiSection (Scheme.EffectiveCartierDivisor.empty X) = 0 := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X)
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  obtain ⟨U, hU, hxU, hUt⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) hx
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hI : (Scheme.EffectiveCartierDivisor.empty X).1.ideal ⟨U, hU⟩ =
      Ideal.span ({1} : Set Γ(X, U)) := Ideal.span_singleton_one.symm
  refine ⟨U, hUt, hxU, ?_⟩
  rw [map_zero]
  exact (effectiveCartierGenericUnitZariskiSection_restrict
    (Scheme.EffectiveCartierDivisor.empty X) ⟨U, hU⟩ 1 one_ne_zero hI).trans
      (openSectionGenericUnitQuotient_unit X U 1)

/-- The native quotient H⁰ class of the empty divisor is zero. -/
theorem effectiveCartierGenericUnitH0_empty
    (X : Scheme.{u}) [IsIntegral X] :
    effectiveCartierGenericUnitH0 (Scheme.EffectiveCartierDivisor.empty X) = 0 := by
  rw [effectiveCartierGenericUnitH0, effectiveCartierGenericUnitSection,
    effectiveCartierGenericUnitZariskiSection_empty, map_zero, map_zero]

end EtaleCohomology
