/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Regular units in the original rational-unit quotient

The rational representative of a unit on an actual open subscheme is the
image of that regular unit under the original generic-point unit map.
Consequently its original cokernel class is zero. These formulas apply to
integral schemes in every dimension.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- Rational representatives preserve the additive notation for products
of function-field units. -/
def genericPointRationalUnitQuotientHom
    (X : Scheme.{u}) [IsIntegral X] (V : X.Etale) :
    Additive X.functionFieldˣ →+
      (etaleGenericUnitQuotient X).obj.obj (op V) :=
  ((cokernel.π (etaleMultiplicativeGroupToPushforward
    (X.fromSpecStalk (genericPoint X)))).hom.app (op V)).hom.comp
      (Units.map (((Scheme.ΓSpecIso X.functionField).inv ≫
        (pullback.snd V.hom (X.fromSpecStalk (genericPoint X))).appTop).hom.toMonoidHom)).toAdditive

theorem genericPointRationalUnitQuotientHom_apply
    (X : Scheme.{u}) [IsIntegral X] (V : X.Etale)
    (a : Additive X.functionFieldˣ) :
    genericPointRationalUnitQuotientHom X V a =
      genericPointRationalUnitQuotientSection X V a := rfl

private theorem genericPointOpenUnit_top_appLE
    {A B : Scheme.{u}} (f : A ⟶ B)
    (h : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

private theorem genericPointOpenUnit_topIso_appLE
    (X : Scheme.{u}) (U : X.Opens) :
    U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge := by
  have hm : X.presheaf.map (eqToHom U.ι_image_top).op =
      X.presheaf.map (homOfLE U.ι_image_top.le).op :=
    congrArg (fun k : op U ⟶ op (U.ι ''ᵁ ⊤) => X.presheaf.map k)
      (Subsingleton.elim _ _)
  change X.presheaf.map (eqToHom U.ι_image_top).op =
    U.ι.appLE U ⊤ U.ι_preimage_self.ge
  exact hm.trans (Scheme.Opens.ι_appLE U U ⊤ U.ι_preimage_self.ge).symm

private theorem genericPointOpenUnit_appLE_congr
    {A B : Scheme.{u}} (f g : A ⟶ B) (U : B.Opens) (V : A.Opens)
    (hfg : f = g) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

private theorem genericPointOpenUnit_square_appLE
    (X : Scheme.{u}) (U : X.Opens) {P Z : Scheme.{u}}
    (p : P ⟶ U.toScheme) (q : P ⟶ Z) (j : Z ⟶ X)
    (hcondition : p ≫ U.ι = q ≫ j)
    (hj : (⊤ : Z.Opens) ≤ j ⁻¹ᵁ U) :
    U.topIso.inv ≫ p.appTop = j.appLE U ⊤ hj ≫ q.appTop := by
  have hp : (⊤ : P.Opens) ≤ p ⁻¹ᵁ ⊤ := (Scheme.Hom.preimage_top p).ge
  have hq : (⊤ : P.Opens) ≤ q ⁻¹ᵁ ⊤ := (Scheme.Hom.preimage_top q).ge
  let ep : (⊤ : P.Opens) ≤ (p ≫ U.ι) ⁻¹ᵁ U :=
    hp.trans ((Opens.map p.base).map (homOfLE U.ι_preimage_self.ge)).le
  let eq : (⊤ : P.Opens) ≤ (q ≫ j) ⁻¹ᵁ U :=
    hq.trans ((Opens.map q.base).map (homOfLE hj)).le
  have hleft : U.topIso.inv ≫ p.appTop = (p ≫ U.ι).appLE U ⊤ ep := by
    rw [genericPointOpenUnit_topIso_appLE X U,
      ← genericPointOpenUnit_top_appLE p hp]
    exact Scheme.Hom.appLE_comp_appLE p U.ι U ⊤ ⊤ U.ι_preimage_self.ge hp
  have hmiddle : (p ≫ U.ι).appLE U ⊤ ep = (q ≫ j).appLE U ⊤ eq :=
    genericPointOpenUnit_appLE_congr (p ≫ U.ι) (q ≫ j) U ⊤ hcondition ep eq
  have hright : (q ≫ j).appLE U ⊤ eq = j.appLE U ⊤ hj ≫ q.appTop :=
    (Scheme.Hom.appLE_comp_appLE q j U ⊤ ⊤ hj hq).symm.trans
      (congrArg (fun r : Γ(Z, ⊤) ⟶ Γ(P, ⊤) => j.appLE U ⊤ hj ≫ r)
        (genericPointOpenUnit_top_appLE q hq))
  exact hleft.trans (hmiddle.trans hright)

private theorem genericPointOpenUnit_germ_appLE
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (hx : genericPoint X ∈ U)
    (hj : (⊤ : (Spec X.functionField).Opens) ≤
      (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) :
    (X.fromSpecStalk (genericPoint X)).appLE U ⊤ hj =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv := by
  let j : Spec X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc]
  rw [← (Spec X.functionField).presheaf.map_comp]
  have hthin :
      (homOfLE (show j ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
        (homOfLE hj).op = 𝟙 (op (⊤ : (Spec X.functionField).Opens)) :=
    Subsingleton.elim _ _
  rw [hthin]
  change X.germToFunctionField U ≫
    ((Scheme.ΓSpecIso X.functionField).inv ≫
      (Spec X.functionField).presheaf.map
        (𝟙 (op (⊤ : (Spec X.functionField).Opens)))) = _
  rw [(Spec X.functionField).presheaf.map_id
    (op (⊤ : (Spec X.functionField).Opens)), Category.comp_id]

/-- The actual generic-point square identifies restriction of a regular
open section with the pullback of its germ in the function field. -/
theorem genericPointOpenUnit_ring_square
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    U.topIso.inv ≫
        (pullback.fst U.ι (X.fromSpecStalk (genericPoint X))).appTop =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
        (pullback.snd U.ι (X.fromSpecStalk (genericPoint X))).appTop := by
  let j : Spec X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)
  have hx : genericPoint X ∈ U := by
    obtain ⟨x⟩ := (show Nonempty U from inferInstance)
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      ⟨x.1, trivial, x.2⟩
  let t : Spec X.functionField ⟶ U.toScheme :=
    U.fromSpecStalkOfMem (genericPoint X) hx
  have ht : t ≫ U.ι = j := U.fromSpecStalkOfMem_ι (genericPoint X) hx
  have hj : (⊤ : (Spec X.functionField).Opens) ≤ j ⁻¹ᵁ U := by
    intro y hy
    change j y ∈ U
    rw [← ht, Scheme.Hom.comp_apply]
    exact (t y).property
  let P : Scheme.{u} := pullback U.ι j
  let p : P ⟶ U.toScheme := pullback.fst U.ι j
  let q : P ⟶ Spec X.functionField := pullback.snd U.ι j
  have hsquare : U.topIso.inv ≫ p.appTop = j.appLE U ⊤ hj ≫ q.appTop :=
    genericPointOpenUnit_square_appLE X U p q j pullback.condition hj
  have hjring : j.appLE U ⊤ hj =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv :=
    genericPointOpenUnit_germ_appLE X U hx hj
  exact hsquare.trans ((congrArg
    (fun r : Γ(X, U) ⟶ Γ(Spec X.functionField, ⊤) => r ≫ q.appTop) hjring).trans
      (Category.assoc _ _ _))

/-- A regular open unit gives precisely its original rational germ in the
direct image from the generic point. -/
theorem genericPointRationalUnitDirectImage_of_open_unit
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (a : (Γ(X, U) : Type u)ˣ) :
    rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X))
        ((zariskiToEtale X).obj U)
        (Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a)) =
      (etaleMultiplicativeGroupToPushforward
        (X.fromSpecStalk (genericPoint X))).hom.app
          (op ((zariskiToEtale X).obj U))
        (Additive.ofMul (Units.map U.topIso.inv.hom.toMonoidHom a)) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact (ConcreteCategory.congr_hom (genericPointOpenUnit_ring_square X U)
    a.val).symm

/-- The original rational quotient kills every original regular unit on
an open subscheme. -/
theorem genericPointRationalUnitQuotientHom_open_unit
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (a : (Γ(X, U) : Type u)ˣ) :
    genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U)
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a)) = 0 := by
  let j : Spec X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)
  let V : X.Etale := (zariskiToEtale X).obj U
  let G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    etaleMultiplicativeGroupSheaf X
  let H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf (Spec X.functionField))
  let Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient X
  let i : G ⟶ H := etaleMultiplicativeGroupToPushforward j
  let π : H ⟶ Q := cokernel.π i
  let s : G.obj.obj (op V) :=
    Additive.ofMul (Units.map U.topIso.inv.hom.toMonoidHom a)
  have ha : rationalUnitDirectImageSection j V
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a)) =
      i.hom.app (op V) s :=
    genericPointRationalUnitDirectImage_of_open_unit X U a
  have h := congrArg (fun f : G ⟶ Q => f.hom.app (op V)) (cokernel.condition i)
  have hz : π.hom.app (op V) (i.hom.app (op V) s) = 0 :=
    ConcreteCategory.congr_hom h s
  rw [genericPointRationalUnitQuotientHom_apply]
  change π.hom.app (op V) (rationalUnitDirectImageSection j V
    (Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a))) = 0
  exact (congrArg (fun z : H.obj.obj (op V) => π.hom.app (op V) z) ha).trans hz

end EtaleCohomology
