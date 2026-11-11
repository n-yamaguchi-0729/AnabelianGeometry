/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.AbelianCechOverlapPullback
public import Nyll.EtaleCohomology.Classical.AbelianCechPullback
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupCechIntegerSource
public import Nyll.EtaleCohomology.Classical.CupCoefficientSource
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCup
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.FreeAbelianYonedaPullback
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafAugmentation
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Original constant scalar values of finite covering-kernel maps

The original integer-to-module coefficient comparison sends the covering
augmentation to the literal constant section one. Thus a finite scalar
section on an overlap determines the same natural-number multiple of that
map. Actual inverse image preserves these literal constant sections.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The actual integer source of the cup comparison evaluates to the
original constant section one after forgetting the module coefficients. -/
theorem abelianCechFiniteScalarUnit_section
    (X : Scheme.{u}) (R : Type u) [CommRing R]
    {T W : X.Etale} (hT : IsTerminal T) (q : W ⟶ T) :
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of R))
        (abelianCechUnitAugmentation X.smallEtaleTopology hT q ≫
          etaleConstantIntegerHom X R ≫
            ((etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)).hom) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of R))).app (op W) (1 : R) := by
  let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  have hunit : freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W (U.obj F)
      (abelianCechUnitAugmentation X.smallEtaleTopology hT q ≫
        etaleConstantIntegerHom X R) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R))).app (op W) (1 : R) := by
    rw [freeModuleSheafIntegerMap_augmentation,
      ← freeModuleSheafUnderlyingHomEquiv_eq,
      freeModuleSheafUnderlyingHomEquiv_yoneda_sections,
      ← freeModuleSheafCounit_eq_moduleCechUnitAugmentation,
      freeModuleSheafCounit_yoneda_sections]
  rw [← Category.assoc, freeAbelianSheafYonedaHomEquiv_postcomp, hunit]
  exact ConcreteCategory.congr_hom
    (etaleConstantModuleForgetIso_toSheafify X R (ModuleCat.of R R) W) (1 : R)

namespace Classical

/-- A literal finite constant section gives the corresponding integer
multiple of the unchanged augmentation and coefficient-unit maps. -/
theorem finiteCechScalarHom_eq_nsmul
    (X : Scheme.{u}) (ℓ n : ℕ) [NeZero (ℓ ^ (n + 1))]
    {T W : X.Etale} (hT : IsTerminal T) (q : W ⟶ T)
    (k : (freeAbelianSheafYoneda X.smallEtaleTopology).obj W ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n))
    (a : ULift.{u} (ZMod (ℓ ^ (n + 1))))
    (hk : freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W _ k =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ellPowerCoefficients ℓ n))).app (op W) a) :
    k = a.down.val • (abelianCechUnitAugmentation X.smallEtaleTopology hT q ≫
      etaleConstantIntegerHom X (ULift.{u} (ZMod (ℓ ^ (n + 1)))) ≫
        ((etaleConstantModuleForgetIso X (ULift.{u} (ZMod (ℓ ^ (n + 1))))).app
          (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
            (ULift.{u} (ZMod (ℓ ^ (n + 1)))))).hom) := by
  let R := ULift.{u} (ZMod (ℓ ^ (n + 1)))
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n)
  have ha : a.down.val • (1 : R) = a := by
    apply ULift.down_injective
    change a.down.val • (1 : ZMod (ℓ ^ (n + 1))) = a.down
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  apply (freeAbelianSheafYonedaHomAddEquiv X.smallEtaleTopology W F).injective
  rw [map_nsmul]
  change freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W F k =
    a.down.val • freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W F _
  rw [hk, abelianCechFiniteScalarUnit_section]
  let η : R →+ F.obj.obj (op W) :=
    ((toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (ellPowerCoefficients ℓ n))).app (op W)).hom
  exact (congrArg η ha.symm).trans (map_nsmul η a.down.val (1 : R))

end Classical

private theorem abelianSheafIso_hom_app_eq_of_inv_app_eq
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u}} (e : F ≅ G) (U : Cᵒᵖ)
    (x : G.obj.obj U) (y : F.obj.obj U)
    (h : e.inv.hom.app U x = y) : e.hom.hom.app U y = x := by
  have hinv : e.inv.hom.app U ≫ e.hom.hom.app U = 𝟙 (G.obj.obj U) :=
    congrArg (fun φ : G ⟶ G => φ.hom.app U) e.inv_hom_id
  exact (congrArg (fun z : F.obj.obj U => e.hom.hom.app U z) h.symm).trans
    (ConcreteCategory.congr_hom hinv x)

/-- Actual inverse image and the original constant coefficient isomorphism
preserve the literal scalar value of a represented morphism. -/
theorem freeAbelianSheafYonedaPullback_constant_section
    {X Y : Scheme.{u}} (p : X ⟶ Y) (A : AddCommGrpCat.{u}) (W : Y.Etale)
    (k : (freeAbelianSheafYoneda Y.smallEtaleTopology).obj W ⟶
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A)
    (a : A)
    (hk : freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology W _ k =
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op W) a) :
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology ((etaleBaseChange p).obj W)
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A)
        ((freeAbelianSheafYonedaPullbackIso p W).inv ≫
          (etaleAbelianPullback p).map k ≫ ((etaleAbelianPullbackConstantIso p).app A).hom) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op ((etaleBaseChange p).obj W)) a := by
  let F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let L := etaleAbelianPullback p
  let E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := L.obj F
  let e : E ≅ G := (etaleAbelianPullbackConstantIso p).app A
  let W' := (etaleBaseChange p).obj W
  let I := freeAbelianSheafYonedaPullbackIso p W
  let x : G.obj.obj (op W') :=
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op W') a
  let y : E.obj.obj (op W') :=
    ((etaleAbelianPullbackPushforwardAdjunction p).unit.app F).hom.app (op W)
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op W) a)
  have hmaps := etaleAbelianConstantHom_pullback_section p A F (𝟙 F) W W' (𝟙 W')
  rw [L.map_id F, op_id, E.obj.map_id (op W')] at hmaps
  have h := ConcreteCategory.congr_hom hmaps a
  have hy : e.inv.hom.app (op W') x = y := h
  have hconstant : e.hom.hom.app (op W') y = x :=
    abelianSheafIso_hom_app_eq_of_inv_app_eq e (op W') x y hy
  have hsection : freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W' E
      (I.inv ≫ L.map k) = y :=
    (freeAbelianSheafYonedaPullbackIso_section p W F k).trans
      (congrArg (((etaleAbelianPullbackPushforwardAdjunction p).unit.app F).hom.app (op W))
        hk)
  have hpost : freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W' G
      ((I.inv ≫ L.map k) ≫ e.hom) =
        e.hom.hom.app (op W')
          (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W' E (I.inv ≫ L.map k)) :=
    freeAbelianSheafYonedaHomEquiv_postcomp X.smallEtaleTopology W'
      (I.inv ≫ L.map k) e.hom
  have hassoc : freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W' G
      (I.inv ≫ L.map k ≫ e.hom) =
        freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W' G
          ((I.inv ≫ L.map k) ≫ e.hom) :=
    congrArg (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W' G)
      (Category.assoc I.inv (L.map k) e.hom).symm
  exact hassoc.trans
    (hpost.trans ((congrArg (e.hom.hom.app (op W')) hsection).trans hconstant))

namespace Classical

/-- The scalar on an original parameter overlap is the scalar on the
actual base-changed overlap of the original finite kernel map. This is
the exact morphism equality used by the native kernel-cup restriction. -/
theorem finiteCechKernelPullback_overlap_eq_nsmul
    {X Y : Scheme.{u}} (p : X ⟶ Y) (ℓ n : ℕ) [NeZero (ℓ ^ (n + 1))]
    {T V W : Y.Etale} (hT : IsTerminal T) (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ Y.smallEtaleTopology T)
    (x y : W ⟶ V)
    (d : kernel (abelianCechUnitAugmentation Y.smallEtaleTopology hT f) ⟶
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n))
    (a : ULift.{u} (ZMod (ℓ ^ (n + 1)))) :
    let B := etaleBaseChange p
    let hB := hT.isTerminalObj B T
    let l := pullback.lift x y (hT.hom_ext (x ≫ f) (y ≫ f))
    let lB := pullback.lift (B.map x) (B.map y)
      (hB.hom_ext (B.map x ≫ B.map f) (B.map y ≫ B.map f))
    let edge := (freeAbelianSheafYoneda Y.smallEtaleTopology).map l ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology f).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hT f
    let edgeB := (freeAbelianSheafYoneda X.smallEtaleTopology).map lB ≫
      (freeCechEdgeSheafIso X.smallEtaleTopology (B.map f)).inv ≫
        abelianCechFirstRelationMap X.smallEtaleTopology hB (B.map f)
    freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology W _ (edge ≫ d) =
        (toSheafify Y.smallEtaleTopology
          ((Functor.const Y.Etaleᵒᵖ).obj (ellPowerCoefficients ℓ n))).app (op W) a →
      edgeB ≫ finiteCechKernelPullback p ℓ n hT f hf d =
        a.down.val •
          (abelianCechUnitAugmentation X.smallEtaleTopology hB (B.map x ≫ B.map f) ≫
            etaleConstantIntegerHom X (ULift.{u} (ZMod (ℓ ^ (n + 1)))) ≫
              ((etaleConstantModuleForgetIso X (ULift.{u} (ZMod (ℓ ^ (n + 1))))).app
                (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
                  (ULift.{u} (ZMod (ℓ ^ (n + 1)))))).hom) := by
  intro B hB l lB edge edgeB ha
  let L := etaleAbelianPullback p
  let coeff := ((etaleAbelianPullbackConstantIso p).app (ellPowerCoefficients ℓ n)).hom
  have he : edgeB ≫ finiteCechKernelPullback p ℓ n hT f hf d =
      (freeAbelianSheafYonedaPullbackIso p W).inv ≫ L.map (edge ≫ d) ≫ coeff := by
    calc
      edgeB ≫ finiteCechKernelPullback p ℓ n hT f hf d =
          (edgeB ≫ abelianCechAugmentationKernelPullback p hT f hf) ≫ L.map d ≫ coeff := by
        dsimp only [finiteCechKernelPullback, L, coeff]
        simp only [Category.assoc]
      _ = ((freeAbelianSheafYonedaPullbackIso p W).inv ≫ L.map edge) ≫
          L.map d ≫ coeff := by rw [abelianCechOverlapEdge_pullback p hT f hf x y]
      _ = _ := by simp only [L, coeff, edge, Functor.map_comp, Category.assoc]
  apply finiteCechScalarHom_eq_nsmul X ℓ n hB (B.map x ≫ B.map f) _ a
  rw [he]
  exact freeAbelianSheafYonedaPullback_constant_section p (ellPowerCoefficients ℓ n)
    W (edge ≫ d) a ha

end Classical

end EtaleCohomology
