/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Descent.FppfGmRepresentable
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Geometry.RingedSpace.Basic

/-!
# Actual local equations as units on a specified open

A local section whose basic open contains the chosen complement becomes
an actual unit on the original base-changed scheme. The construction and
its restriction law use the literal structure-sheaf ring maps. In
particular they apply to Cartier equations without pulling back a
function field through a nondominant morphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Pull an original section on an open to its actual étale base change. -/
def openSectionBaseChangeRing {X Y : Scheme.{u}} (i : Y ⟶ X) (U : X.Opens) :
    Γ(X, U) ⟶ Γ(pullback U.ι i, ⊤) :=
  U.topIso.inv ≫ (pullback.fst U.ι i).appTop

/-- The section map is the actual structural `appLE` map of the
base-changed scheme, with the original open kept explicit. -/
theorem openSectionBaseChangeRing_eq_appLE
    {X Y : Scheme.{u}} (i : Y ⟶ X) (U : X.Opens)
    (h : (⊤ : (pullback U.ι i).Opens) ≤ (pullback.fst U.ι i ≫ U.ι) ⁻¹ᵁ U) :
    openSectionBaseChangeRing i U = (pullback.fst U.ι i ≫ U.ι).appLE U ⊤ h := by
  have htop : U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge := by
    have hthin : (eqToHom U.ι_image_top).op =
        (homOfLE U.ι_image_top.le).op := Subsingleton.elim _ _
    have ht : U.topIso.inv = X.presheaf.map (eqToHom U.ι_image_top).op := by rfl
    have hi : U.ι.appLE U ⊤ U.ι_preimage_self.ge =
        X.presheaf.map (homOfLE U.ι_image_top.le).op :=
      Scheme.Opens.ι_appLE U U ⊤ U.ι_preimage_self.ge
    exact ht.trans ((congrArg X.presheaf.map hthin).trans hi.symm)
  have hfst : (pullback.fst U.ι i).appTop =
      (pullback.fst U.ι i).appLE ⊤ ⊤ (Scheme.Hom.preimage_top (pullback.fst U.ι i)).ge :=
    (Scheme.Hom.appLE_eq_app (pullback.fst U.ι i)).symm
  change U.topIso.inv ≫ (pullback.fst U.ι i).appTop = _
  calc
    U.topIso.inv ≫ (pullback.fst U.ι i).appTop =
        U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫
          (pullback.fst U.ι i).appLE ⊤ ⊤
            (Scheme.Hom.preimage_top (pullback.fst U.ι i)).ge :=
      congrArg₂
        (fun (a : Γ(X, U) ⟶ Γ(U, ⊤))
          (b : Γ(U, ⊤) ⟶ Γ(pullback U.ι i, ⊤)) => a ≫ b) htop hfst
    _ = (pullback.fst U.ι i ≫ U.ι).appLE U ⊤ h :=
      Scheme.Hom.appLE_comp_appLE (pullback.fst U.ι i) U.ι U ⊤ ⊤ _ _

/-- Restricting the original open section commutes with its actual
base-change ring map. -/
theorem openSectionBaseChangeRing_restrict
    {X Y : Scheme.{u}} (i : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) :
    X.presheaf.map (homOfLE h).op ≫ openSectionBaseChangeRing i W =
      openSectionBaseChangeRing i U ≫
        (((etaleBaseChange i).map ((zariskiToEtale X).map (homOfLE h))).left).appTop := by
  let a : (zariskiToEtale X).obj W ⟶ (zariskiToEtale X).obj U :=
    (zariskiToEtale X).map (homOfLE h)
  let a₀ : (W : Scheme) ⟶ (U : Scheme) := a.left
  let m : pullback W.ι i ⟶ pullback U.ι i := ((etaleBaseChange i).map a).left
  let qU : pullback U.ι i ⟶ X := pullback.fst U.ι i ≫ U.ι
  let qW : pullback W.ι i ⟶ X := pullback.fst W.ι i ≫ W.ι
  have hU : (⊤ : (pullback U.ι i).Opens) ≤ qU ⁻¹ᵁ U := by
    intro z hz
    exact (pullback.fst U.ι i z).property
  have hW : (⊤ : (pullback W.ι i).Opens) ≤ qW ⁻¹ᵁ W := by
    intro z hz
    exact (pullback.fst W.ι i z).property
  have hWU : (⊤ : (pullback W.ι i).Opens) ≤ qW ⁻¹ᵁ U := by
    intro z hz
    exact h (hW hz)
  have hm : m ≫ qU = qW := by
    have hmf : m ≫ pullback.fst U.ι i = pullback.fst W.ι i ≫ a₀ :=
      pullback.lift_fst _ _ _
    have ha : a₀ ≫ U.ι = W.ι :=
      MorphismProperty.Over.w
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) a
    change m ≫ (pullback.fst U.ι i ≫ U.ι) = pullback.fst W.ι i ≫ W.ι
    rw [← Category.assoc, hmf, Category.assoc, ha]
  have hcomp : (⊤ : (pullback W.ι i).Opens) ≤ (m ≫ qU) ⁻¹ᵁ U := by
    intro z _
    exact hU (show m z ∈ (⊤ : (pullback U.ι i).Opens) from trivial)
  have happ : ∀ (q : pullback W.ι i ⟶ X) (hq : q = qW)
      (e : (⊤ : (pullback W.ι i).Opens) ≤ q ⁻¹ᵁ U),
      q.appLE U ⊤ e = qW.appLE U ⊤ hWU := by
    intro q hq e
    cases hq
    rfl
  calc
    X.presheaf.map (homOfLE h).op ≫ openSectionBaseChangeRing i W =
        X.presheaf.map (homOfLE h).op ≫ qW.appLE W ⊤ hW := by
          rw [openSectionBaseChangeRing_eq_appLE i W hW]
    _ = qW.appLE U ⊤ hWU := Scheme.Hom.map_appLE qW hW (homOfLE h).op
    _ = (m ≫ qU).appLE U ⊤ hcomp := (happ (m ≫ qU) hm hcomp).symm
    _ = qU.appLE U ⊤ hU ≫ m.appLE ⊤ ⊤ (Scheme.Hom.preimage_top m).ge :=
      (Scheme.Hom.appLE_comp_appLE m qU U ⊤ ⊤ _ _).symm
    _ = openSectionBaseChangeRing i U ≫ m.appTop :=
      congrArg₂
        (fun (a : Γ(X, U) ⟶ Γ(pullback U.ι i, ⊤))
          (b : Γ(pullback U.ι i, ⊤) ⟶ Γ(pullback W.ι i, ⊤)) => a ≫ b)
        (openSectionBaseChangeRing_eq_appLE i U hU).symm
        (Scheme.Hom.appLE_eq_app m)

/-- If the chosen open lies in the equation's basic open on the chart,
its literal restriction to the base change is an actual unit. -/
theorem openSectionBaseChangeRing_isUnit
    (X : Scheme.{u}) (O U : X.Opens) (f : Γ(X, U))
    (hf : U ⊓ O ≤ X.basicOpen f) :
    IsUnit (openSectionBaseChangeRing O.ι U f) := by
  let P : Scheme.{u} := pullback U.ι O.ι
  let q : P ⟶ X := pullback.fst U.ι O.ι ≫ U.ι
  have hU : (⊤ : P.Opens) ≤ q ⁻¹ᵁ U := by
    intro z hz
    exact (pullback.fst U.ι O.ι z).property
  have hbasic : (⊤ : P.Opens) ≤ q ⁻¹ᵁ (X.basicOpen f) := by
    intro z hz
    apply hf
    refine ⟨hU hz, ?_⟩
    have hq : q z = O.ι (pullback.snd U.ι O.ι z) :=
      congrArg (fun k => k z) (pullback.condition (f := U.ι) (g := O.ι))
    rw [hq]
    exact (pullback.snd U.ι O.ι z).property
  rw [openSectionBaseChangeRing_eq_appLE O.ι U hU]
  apply P.toRingedSpace.isUnit_of_isUnit_germ
  intro z hz
  apply (P.mem_basicOpen (q.appLE U ⊤ hU f) z hz).mp
  rw [Scheme.basicOpen_appLE]
  exact ⟨hz, hbasic hz⟩

/-- The same containment holds after any restriction of the equation. -/
theorem openEquation_restrict_basicOpen
    (X : Scheme.{u}) (O : X.Opens) {U W : X.Opens} (h : W ≤ U)
    (f : Γ(X, U)) (hf : U ⊓ O ≤ X.basicOpen f) :
    W ⊓ O ≤ X.basicOpen (X.presheaf.map (homOfLE h).op f) := by
  rw [Scheme.basicOpen_res]
  intro x hx
  exact ⟨hx.1, hf ⟨h hx.1, hx.2⟩⟩

/-- The actual direct-image unit section of a local equation which is
invertible on the chosen open complement. -/
def openEquationDirectImageUnitSection
    (X : Scheme.{u}) (O U : X.Opens) (f : Γ(X, U))
    (hf : U ⊓ O ≤ X.basicOpen f) :
    ((etaleAbelianPushforward O.ι).obj (etaleMultiplicativeGroupSheaf O)).obj.obj
      (op ((zariskiToEtale X).obj U)) :=
  Additive.ofMul (openSectionBaseChangeRing_isUnit X O U f hf).unit

/-- The constructed unit has exactly the original pulled equation as
its value in the original ring of sections. -/
theorem openEquationDirectImageUnitSection_val
    (X : Scheme.{u}) (O U : X.Opens) (f : Γ(X, U))
    (hf : U ⊓ O ≤ X.basicOpen f) :
    ((Additive.toMul (α := (Γ(pullback U.ι O.ι, ⊤) : Type u)ˣ)
      (openEquationDirectImageUnitSection X O U f hf)) : Γ(pullback U.ι O.ι, ⊤)) =
      openSectionBaseChangeRing O.ι U f :=
  (openSectionBaseChangeRing_isUnit X O U f hf).unit_spec

/-- Restriction of actual unit sections retains the actual restricted
equation, including empty overlaps. -/
theorem openEquationDirectImageUnitSection_restrict
    (X : Scheme.{u}) (O : X.Opens) {U W : X.Opens} (h : W ≤ U)
    (f : Γ(X, U)) (hf : U ⊓ O ≤ X.basicOpen f) :
    ((etaleAbelianPushforward O.ι).obj (etaleMultiplicativeGroupSheaf O)).obj.map
        ((zariskiToEtale X).map (homOfLE h)).op
          (openEquationDirectImageUnitSection X O U f hf) =
      openEquationDirectImageUnitSection X O W (X.presheaf.map (homOfLE h).op f)
        (openEquation_restrict_basicOpen X O h f hf) := by
  apply (Additive.toMul (α := (Γ(pullback W.ι O.ι, ⊤) : Type u)ˣ)).injective
  apply Units.ext
  change (((etaleBaseChange O.ι).map ((zariskiToEtale X).map (homOfLE h))).left).appTop
      ((Additive.toMul (α := (Γ(pullback U.ι O.ι, ⊤) : Type u)ˣ)
        (openEquationDirectImageUnitSection X O U f hf)).val) =
    (Additive.toMul (α := (Γ(pullback W.ι O.ι, ⊤) : Type u)ˣ)
      (openEquationDirectImageUnitSection X O W (X.presheaf.map (homOfLE h).op f)
        (openEquation_restrict_basicOpen X O h f hf))).val
  rw [openEquationDirectImageUnitSection_val, openEquationDirectImageUnitSection_val]
  exact (ConcreteCategory.congr_hom (openSectionBaseChangeRing_restrict O.ι h) f).symm

end EtaleCohomology
