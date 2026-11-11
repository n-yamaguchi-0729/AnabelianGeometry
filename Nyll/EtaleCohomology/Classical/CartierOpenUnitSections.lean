/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.OpenUnitQuotientEquations
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.UnitQuotientFunctoriality
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Nyll.SchemeTheory.Divisors.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Actual Cartier equations glued on an avoiding open

Local equations give actual units on any specified open avoiding the
Cartier support. Their original quotient classes glue by the genuine
sheaf condition, and every actual affine local equation computes the
resulting native H⁰ class. No function-field pullback enters this
construction.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- A regular affine local equation for the Cartier divisor at a point. -/
def effectiveCartierOpenEquation
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
  exact hf.1.left (by simp only [hzero, zero_mul])

/-- The unit-quotient section represented by a chosen local equation. -/
def effectiveCartierOpenEquationSection
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) (hO : O ≤ D.1.support.compl) (x : X) :
    (etaleUnitQuotient O.ι).obj.obj
      (op ((zariskiToEtale X).obj (effectiveCartierOpenEquation D x).1.1)) := by
  let e := effectiveCartierOpenEquation D x
  have : Nonempty e.1.1 := ⟨⟨x, e.2.property.1⟩⟩
  exact openEquationUnitQuotientSection X O e.1.1 e.2.val
      (idealGenerator_avoidingOpen_le_basicOpen X D.1 O hO e.1 e.2.val e.2.property.2.2)

/-- Local Cartier equations give compatible unit-quotient sections. -/
theorem effectiveCartierOpenEquationSections_compatible
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) (hO : O ≤ D.1.support.compl) :
    TopCat.Presheaf.IsCompatible
      ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleUnitQuotient O.ι)).obj
      (fun x : X => (effectiveCartierOpenEquation D x).1.1)
      (effectiveCartierOpenEquationSection D O hO) := by
  intro x y
  let e := effectiveCartierOpenEquation D x
  let d := effectiveCartierOpenEquation D y
  have : Nonempty e.1.1 := ⟨⟨x, e.2.property.1⟩⟩
  have : Nonempty d.1.1 := ⟨⟨y, d.2.property.1⟩⟩
  exact idealSheafGenerators_openUnit_overlap X D.1 O hO e.1 d.1
    e.2.val d.2.val
    e.2.property.2.2 d.2.property.2.2

/-- Glue the local equation sections on the open complement of the divisor. -/
def effectiveCartierOpenUnitGluing
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) (hO : O ≤ D.1.support.compl) :
    {s : ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleUnitQuotient O.ι)).obj.obj (op (⊤ : X.Opens)) //
      ∀ x : X, ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleUnitQuotient O.ι)).obj.map
          (homOfLE (show (effectiveCartierOpenEquation D x).1.1 ≤ ⊤ from le_top)).op s =
            effectiveCartierOpenEquationSection D O hO x} := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleUnitQuotient O.ι)
  let U : X → X.Opens := fun x => (effectiveCartierOpenEquation D x).1.1
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨x, (effectiveCartierOpenEquation D x).2.property.1⟩
  let h := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover
    (effectiveCartierOpenEquationSection D O hO)
    (effectiveCartierOpenEquationSections_compatible D O hO)
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/-- The global section obtained by actual sheaf gluing of the divisor's
actual local equations in the original quotient. -/
def effectiveCartierOpenUnitZariskiSection
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) (hO : O ≤ D.1.support.compl) :
    ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleUnitQuotient O.ι)).obj.obj (op (⊤ : X.Opens)) :=
  (effectiveCartierOpenUnitGluing D O hO).val

/-- Every genuine affine local equation computes the glued section.
No compatibility of chart choices is part of this theorem's input. -/
theorem effectiveCartierOpenUnitZariskiSection_restrict
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) (hO : O ≤ D.1.support.compl)
    (U : X.affineOpens) [Nonempty U.1] (f : Γ(X, U.1))
    (hI : D.1.ideal U = Ideal.span {f}) :
    ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleUnitQuotient O.ι)).obj.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
        (effectiveCartierOpenUnitZariskiSection D O hO) =
      openEquationUnitQuotientSection X O U.1 f
        (idealGenerator_avoidingOpen_le_basicOpen X D.1 O hO U f hI) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleUnitQuotient O.ι)
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  let e := effectiveCartierOpenEquation D x
  have : Nonempty e.1.1 := ⟨⟨x, e.2.property.1⟩⟩
  refine ⟨U.1 ⊓ e.1.1, inf_le_left, ⟨hx, e.2.property.1⟩, ?_⟩
  have he : F.obj.map (homOfLE (show e.1.1 ≤ ⊤ from le_top)).op
      (effectiveCartierOpenUnitZariskiSection D O hO) =
        openEquationUnitQuotientSection X O e.1.1 e.2.val
      (idealGenerator_avoidingOpen_le_basicOpen X D.1 O hO e.1 e.2.val e.2.property.2.2) :=
    (effectiveCartierOpenUnitGluing D O hO).property x
  have hover := idealSheafGenerators_openUnit_overlap X D.1 O hO U e.1
    f e.2.val hI e.2.property.2.2
  calc
    F.obj.map (homOfLE (show U.1 ⊓ e.1.1 ≤ U.1 from inf_le_left)).op
        (F.obj.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
          (effectiveCartierOpenUnitZariskiSection D O hO)) =
      F.obj.map (TopologicalSpace.Opens.infLERight U.1 e.1.1).op
        (F.obj.map (homOfLE (show e.1.1 ≤ ⊤ from le_top)).op
          (effectiveCartierOpenUnitZariskiSection D O hO)) := by
            have hthin :
                (homOfLE (show U.1 ≤ ⊤ from le_top)).op ≫
                    (homOfLE (show U.1 ⊓ e.1.1 ≤ U.1 from inf_le_left)).op =
                  (homOfLE (show e.1.1 ≤ ⊤ from le_top)).op ≫
                    (TopologicalSpace.Opens.infLERight U.1 e.1.1).op :=
              Subsingleton.elim _ _
            simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom (congrArg F.obj.map hthin)
                (effectiveCartierOpenUnitZariskiSection D O hO)
    _ = F.obj.map (TopologicalSpace.Opens.infLERight U.1 e.1.1).op
        (openEquationUnitQuotientSection X O e.1.1 e.2.val
      (idealGenerator_avoidingOpen_le_basicOpen X D.1 O hO e.1 e.2.val e.2.property.2.2)) :=
      congrArg (F.obj.map (TopologicalSpace.Opens.infLERight U.1 e.1.1).op) he
    _ = F.obj.map (homOfLE (show U.1 ⊓ e.1.1 ≤ U.1 from inf_le_left)).op
        (openEquationUnitQuotientSection X O U.1 f
        (idealGenerator_avoidingOpen_le_basicOpen X D.1 O hO U f hI)) := hover.symm

/-- The original global étale section represented by an actual effective
Cartier divisor. -/
def effectiveCartierOpenUnitSection
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) (hO : O ≤ D.1.support.compl) :
    (etaleUnitQuotient O.ι).obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  (etaleZariskiGlobalSectionsIso X AddCommGrpCat.{u}
    (etaleUnitQuotient O.ι)).hom (effectiveCartierOpenUnitZariskiSection D O hO)

/-- The effective Cartier divisor's native H⁰ class in the original
quotient of units on the specified avoiding open. -/
def effectiveCartierOpenUnitH0
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) (hO : O ≤ D.1.support.compl) :
    Sheaf.H.{u} (etaleUnitQuotient O.ι) 0 :=
  (Sheaf.H.equiv₀.{u} (etaleUnitQuotient O.ι)
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X)).symm
        (effectiveCartierOpenUnitSection D O hO)

/-- On the original small étale site the native H⁰ representative is
exactly the class of any actual affine equation for the divisor. -/
theorem effectiveCartierOpenUnitH0_section
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    (O : X.Opens) (hO : O ≤ D.1.support.compl)
    (U : X.affineOpens) [Nonempty U.1] (f : Γ(X, U.1))
    (hI : D.1.ideal U = Ideal.span {f}) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (etaleUnitQuotient O.ι).obj.map
      (hT.from ((zariskiToEtale X).obj U.1)).op
        (Sheaf.H.equiv₀.{u} (etaleUnitQuotient O.ι) hT
          (effectiveCartierOpenUnitH0 D O hO)) =
      openEquationUnitQuotientSection X O U.1 f
        (idealGenerator_avoidingOpen_le_basicOpen X D.1 O hO U f hI) := by
  intro hT
  rw [effectiveCartierOpenUnitH0, AddEquiv.apply_symm_apply]
  let e := etaleZariskiGlobalSectionsIso X AddCommGrpCat.{u}
    (etaleUnitQuotient O.ι)
  let s := effectiveCartierOpenUnitZariskiSection D O hO
  let j : (zariskiToEtale X).obj U.1 ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      U.1.ι (Category.comp_id U.1.ι)
  have ht : hT.from ((zariskiToEtale X).obj U.1) = j := hT.hom_ext _ _
  have hr := ConcreteCategory.congr_hom
    (etaleZariskiGlobalSectionsIso_inv_restrict X AddCommGrpCat.{u}
      (etaleUnitQuotient O.ι) U.1) (e.hom s)
  change ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleUnitQuotient O.ι)).obj.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
      (e.inv (e.hom s)) = (etaleUnitQuotient O.ι).obj.map j.op (e.hom s) at hr
  have hc : e.inv (e.hom s) = s := ConcreteCategory.congr_hom e.hom_inv_id s
  rw [hc] at hr
  rw [ht]
  exact hr.symm.trans (effectiveCartierOpenUnitZariskiSection_restrict D O hO U f hI)

end EtaleCohomology
