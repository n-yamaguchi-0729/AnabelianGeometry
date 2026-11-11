/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.PushforwardGlobalSections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Rational representatives of the original generic-unit H⁰

The native degree-zero equivalence is evaluated on the original objects of
the small étale site. Its values are the pullbacks of the original field
unit along the actual second projections of the generic-point squares.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Pull back an original affine-source unit to the actual base-change
object defining the direct image. -/
def rationalUnitDirectImageSection
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of K) ⟶ X) (V : X.Etale) (a : Additive Kˣ) :
    ((etaleAbelianPushforward j).obj
      (etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.obj (op V) :=
  Additive.ofMul (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd V.hom j).appTop).hom.toMonoidHom) a.toMul)

/-- Rational representatives commute with the actual presheaf map on an
arbitrary original base scheme. -/
theorem rationalUnitDirectImageSection_naturality
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of K) ⟶ X) (V W : X.Etale) (m : V ⟶ W)
    (a : Additive Kˣ) :
    ((etaleAbelianPushforward j).obj
      (etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.map m.op
        (rationalUnitDirectImageSection j W a) =
      rationalUnitDirectImageSection j V a := by
  let k := ((etaleBaseChange j).map m).left
  have hsnd : k ≫ pullback.snd W.hom j = pullback.snd V.hom j := by
    dsimp only [k, etaleBaseChange]
    exact pullback.lift_snd _ _ _
  have hrings :
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (pullback.snd V.hom j).appTop =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd W.hom j).appTop) ≫ k.appTop := by
    exact (congrArg
      (fun l : pullback V.hom j ⟶ Spec (CommRingCat.of K) =>
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ l.appTop) hsnd.symm).trans
      ((congrArg (fun l => (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ l)
        (Scheme.Hom.comp_appTop k (pullback.snd W.hom j))).trans
          (Category.assoc _ _ _).symm)
  apply Additive.toMul.injective
  apply Units.ext
  exact (ConcreteCategory.congr_hom hrings a.toMul.val).symm

/-- The original cokernel class of a rational function-field unit on an
original object of the small étale site. -/
def genericPointRationalUnitQuotientSection
    (X : Scheme.{u}) [IsIntegral X] (V : X.Etale)
    (a : Additive X.functionFieldˣ) :
    (etaleGenericUnitQuotient X).obj.obj (op V) :=
  (cokernel.π (etaleMultiplicativeGroupToPushforward
    (X.fromSpecStalk (genericPoint X)))).hom.app (op V)
    (rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X)) V a)

/-- The original rational cokernel class is natural on the original site. -/
theorem genericPointRationalUnitQuotientSection_naturality
    (X : Scheme.{u}) [IsIntegral X] (V W : X.Etale) (m : V ⟶ W)
    (a : Additive X.functionFieldˣ) :
    (etaleGenericUnitQuotient X).obj.map m.op
        (genericPointRationalUnitQuotientSection X W a) =
      genericPointRationalUnitQuotientSection X V a := by
  let j : Spec (CommRingCat.of X.functionField) ⟶ X :=
    X.fromSpecStalk (genericPoint X)
  let G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleAbelianPushforward j).obj
      (etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of X.functionField)))
  let Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient X
  let π : G ⟶ Q := cokernel.π (etaleMultiplicativeGroupToPushforward j)
  let s : G.obj.obj (op W) := rationalUnitDirectImageSection j W a
  have h : π.hom.app (op V) (G.obj.map m.op s) =
      Q.obj.map m.op (π.hom.app (op W) s) :=
    ConcreteCategory.congr_hom (π.hom.naturality m.op) s
  have hn : G.obj.map m.op s = rationalUnitDirectImageSection j V a :=
    rationalUnitDirectImageSection_naturality j V W m a
  change Q.obj.map m.op (π.hom.app (op W) s) =
    π.hom.app (op V) (rationalUnitDirectImageSection j V a)
  exact h.symm.trans (congrArg (fun z : G.obj.obj (op V) => π.hom.app (op V) z) hn)

/-- The original terminal-object representative of a native generic-unit
H⁰ class is the rational representative of its original function-field unit. -/
theorem genericPointUnitsH0Equiv_terminal_section
    (X : Scheme.{u}) [IsIntegral X]
    (a : Sheaf.H.{u}
      ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))) 0) :
    Sheaf.H.equiv₀.{u}
      ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField))))
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X) a =
      rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X))
        (Scheme.Etale.mk (𝟙 X)) (genericPointUnitsH0Equiv X a) := by
  let j := X.fromSpecStalk (genericPoint X)
  let G := (etaleAbelianPushforward j).obj
    (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let s := Sheaf.H.equiv₀.{u} G hT a
  let e := etaleAbelianPushforwardGlobalSectionsIso j
    (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))
  let b := etaleMultiplicativeGroupSpecSectionsEquiv
    (Spec (.of X.functionField)) (.of X.functionField) (𝟙 _)
  have hb : b.symm (genericPointUnitsH0Equiv X a) = e.hom s :=
    b.symm_apply_apply (e.hom s)
  have hr : e.inv (b.symm (genericPointUnitsH0Equiv X a)) =
      rationalUnitDirectImageSection j (Scheme.Etale.mk (𝟙 X))
        (genericPointUnitsH0Equiv X a) := by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  change s = _
  rw [← hr, hb]
  exact (ConcreteCategory.congr_hom e.hom_inv_id s).symm

/-- Evaluate the native H⁰ class on any original étale object, without
replacing its cohomology class or its function-field coordinate. -/
theorem genericPointUnitsH0Equiv_section
    (X : Scheme.{u}) [IsIntegral X]
    (a : Sheaf.H.{u}
      ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))) 0)
    (V : X.Etale) :
    let G := (etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
      (etaleMultiplicativeGroupSheaf (Spec (.of X.functionField)))
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    G.obj.map (hT.from V).op (Sheaf.H.equiv₀.{u} G hT a) =
      rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X)) V
        (genericPointUnitsH0Equiv X a) := by
  intro G hT
  rw [genericPointUnitsH0Equiv_terminal_section X a]
  exact rationalUnitDirectImageSection_naturality
    (X.fromSpecStalk (genericPoint X)) V (Scheme.Etale.mk (𝟙 X))
    (hT.from V) (genericPointUnitsH0Equiv X a)

end EtaleCohomology
