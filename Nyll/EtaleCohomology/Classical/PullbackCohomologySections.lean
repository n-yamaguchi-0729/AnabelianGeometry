/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianPullbackConstants
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCoefficients
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

public import Nyll.EtaleCohomology.Sites.ConstantPullbackSections

/-!
# Degree-zero cohomological pullback is the actual section pullback

The existing constant-sheaf comparison preserves actual constant sections.
Applying this to a map out of the constant integer sheaf identifies the
degree-zero Ext pullback with the original adjunction unit and restriction.
The coefficient-forgetting comparison then gives the same assertion for
module sheaves and the native `etalePullbackGlobalSectionsMap`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem etaleAbelianConstantHom_pullback_section
    (A : AddCommGrpCat.{u}) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (a : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ F)
    (V : Y.Etale) (U : X.Etale) (l : U ⟶ (etaleBaseChange f).obj V) :
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op U) ≫
        (((etaleAbelianPullbackConstantIso f).app A).inv ≫
          (etaleAbelianPullback f).map a).hom.app (op U) =
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op V) ≫
        a.hom.app (op V) ≫
          ((etaleAbelianPullbackPushforwardAdjunction f).unit.app F).hom.app (op V) ≫
            ((etaleAbelianPullback f).obj F).obj.map l.op :=
  Sites.constantSheafHom_pullback_section f (etaleAbelianPullback f)
    (etaleAbelianPullbackPushforwardAdjunction f) A F a V U l

private theorem zeroSections_eval
    {Z : Scheme.{u}} (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})
    {T : Z.Etale} (hT : IsTerminal T) (x : Sheaf.H.{u} F 0) :
    Sheaf.H.equiv₀ F hT x = (Ext.addEquiv₀ x).hom.app (op T)
      ((toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op T)
          (ULift.up (1 : ℤ))) := rfl

/-- The original degree-zero Ext pullback is the actual adjunction-unit
section followed by restriction to a terminal object of the source site. -/
theorem etaleAbelianCohomologyPullbackMap_zero_sections
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (hV : IsTerminal V) {U : X.Etale} (hU : IsTerminal U)
    (l : U ⟶ (etaleBaseChange f).obj V) (x : Sheaf.H.{u} F 0) :
    Sheaf.H.equiv₀ ((etaleAbelianPullback f).obj F) hU
        (etaleAbelianCohomologyPullbackMap f F 0 x) =
      ((etaleAbelianPullback f).obj F).obj.map l.op
        (((etaleAbelianPullbackPushforwardAdjunction f).unit.app F).hom.app (op V)
          (Sheaf.H.equiv₀ F hV x)) := by
  rw [zeroSections_eval, zeroSections_eval, etaleAbelianCohomologyPullbackMap_zero]
  let A : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} ℤ)
  let B : AddCommGrpCat.{u} := ((etaleAbelianPullback f).obj F).obj.obj (op U)
  have h : _ = _ := etaleAbelianConstantHom_pullback_section f A F (Ext.addEquiv₀ x) V U l
  have hpoint := congrArg (fun g : A ⟶ B => g (ULift.up (1 : ℤ))) h
  exact hpoint

variable (R : Type u) [CommRing R]

private theorem forgetCoefficients_pullbackUnit_inv
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    (etaleAbelianPullbackPushforwardAdjunction f).unit.app
        (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) ≫
      (etaleAbelianPushforward f).map
        ((etalePullbackForgetCoefficientsIso f R).inv.app F) =
    Classical.forgetCoefficients.{u + 1, u, u, u}.map
      ((etalePullbackPushforwardAdjunction f R).unit.app F) := by
  let FY := Classical.forgetCoefficients.{u + 1, u, u, u}.obj F
  let FX := (etalePullback f R).obj F
  let AX := (etaleAbelianPullback f).obj FY
  let e : Classical.forgetCoefficients.{u + 1, u, u, u}.obj FX ≅ AX :=
    (etalePullbackForgetCoefficientsIso f R).app F
  let ηA := (etaleAbelianPullbackPushforwardAdjunction f).unit.app FY
  let P := etaleAbelianPushforward f
  let η' : FY ⟶ P.obj (Classical.forgetCoefficients.{u + 1, u, u, u}.obj FX) :=
    Classical.forgetCoefficients.{u + 1, u, u, u}.map
      ((etalePullbackPushforwardAdjunction f R).unit.app F)
  have hu : η' ≫ P.map e.hom = ηA :=
    etalePullbackForgetCoefficientsIso_unit f R F
  have he : P.map e.hom ≫ P.map e.inv = 𝟙 _ :=
    (P.map_comp e.hom e.inv).symm.trans
      ((congrArg P.map e.hom_inv_id).trans (P.map_id _))
  exact (congrArg (fun z : FY ⟶ P.obj AX => z ≫ P.map e.inv) hu.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => η' ≫ z) he).trans (Category.comp_id η')))

private theorem forgetCoefficients_pullbackSection
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (V : Y.Etale) (U : X.Etale) (l : U ⟶ (etaleBaseChange f).obj V) :
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app
      (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F)).hom.app (op V) ≫
        ((etaleAbelianPullback f).obj
          (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F)).obj.map l.op ≫
            ((etalePullbackForgetCoefficientsIso f R).inv.app F).hom.app (op U) =
      (Classical.forgetCoefficients.{u + 1, u, u, u}.map
        ((etalePullbackPushforwardAdjunction f R).unit.app F)).hom.app (op V) ≫
          (Classical.forgetCoefficients.{u + 1, u, u, u}.obj
            ((etalePullback f R).obj F)).obj.map l.op := by
  let FY := Classical.forgetCoefficients.{u + 1, u, u, u}.obj F
  let FX := Classical.forgetCoefficients.{u + 1, u, u, u}.obj
    ((etalePullback f R).obj F)
  let AX := (etaleAbelianPullback f).obj FY
  let e : FX ≅ AX := (etalePullbackForgetCoefficientsIso f R).app F
  let ηA := (etaleAbelianPullbackPushforwardAdjunction f).unit.app FY
  let η' : FY ⟶ (etaleAbelianPushforward f).obj FX :=
    Classical.forgetCoefficients.{u + 1, u, u, u}.map
      ((etalePullbackPushforwardAdjunction f R).unit.app F)
  have hv : ηA.hom.app (op V) ≫ e.inv.hom.app (op ((etaleBaseChange f).obj V)) =
      η'.hom.app (op V) :=
    congrArg (fun z : FY ⟶ (etaleAbelianPushforward f).obj FX => z.hom.app (op V))
      (forgetCoefficients_pullbackUnit_inv f R F)
  exact (congrArg (fun z => ηA.hom.app (op V) ≫ z)
    (e.inv.hom.naturality l.op)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ FX.obj.map l.op) hv))

private theorem evaluate_composite_equality
    {A B C D E : AddCommGrpCat.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : A ⟶ E) (r : E ⟶ D)
    (h : a ≫ b ≫ c = d ≫ r) (t : A) : c (b (a t)) = r (d t) :=
  ConcreteCategory.congr_hom h t

private theorem moduleZeroEquiv_apply
    {Z : Scheme.{u}} {R : Type u} [CommRing R]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R))
    {T : Z.Etale} (hT : IsTerminal T) (x : etaleCohomology Z R F 0) :
    Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F hT x =
      Sheaf.H.equiv₀ (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) hT x := rfl

private theorem modulePullback_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : etaleCohomology Y R F n) :
    etaleCohomologyPullbackMap f R F n x =
      Sheaf.H.map ((etalePullbackForgetCoefficientsIso f R).inv.app F) n
        (etaleAbelianCohomologyPullbackMap f
          (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n x) := rfl

private theorem moduleGlobalSections_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
    etalePullbackGlobalSectionsMap f R F x =
      ((etalePullback f R).obj F).obj.map
        (etaleBaseChangeLift f f ((Category.comp_id f).trans (Category.id_comp f).symm)).op
          (((etalePullbackPushforwardAdjunction f R).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 Y))) x) := rfl

private theorem forgetCoefficients_section_apply
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : F ⟶ (etalePushforward f R).obj G)
    (V : Y.Etale) (U : X.Etale) (l : U ⟶ (etaleBaseChange f).obj V)
    (t : F.obj.obj (op V)) :
    (Classical.forgetCoefficients.{u + 1, u, u, u}.obj G).obj.map l.op
        ((Classical.forgetCoefficients.{u + 1, u, u, u}.map a).hom.app (op V) t) =
      G.obj.map l.op (a.hom.app (op V) t) := rfl

private theorem forgetCoefficients_sectionDiagram
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (b : A ⟶ Classical.forgetCoefficients.{u + 1, u, u, u}.obj G)
    (v : Classical.forgetCoefficients.{u + 1, u, u, u}.obj F ⟶
      (etaleAbelianPushforward f).obj A)
    (a : F ⟶ (etalePushforward f R).obj G)
    (V : Y.Etale) (U : X.Etale) (l : U ⟶ (etaleBaseChange f).obj V)
    (h : v.hom.app (op V) ≫ A.obj.map l.op ≫ b.hom.app (op U) =
      (Classical.forgetCoefficients.{u + 1, u, u, u}.map a).hom.app (op V) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}.obj G).obj.map l.op)
    (t : F.obj.obj (op V)) :
    b.hom.app (op U) (A.obj.map l.op (v.hom.app (op V) t)) =
      G.obj.map l.op (a.hom.app (op V) t) := by
  have he := evaluate_composite_equality (v.hom.app (op V)) (A.obj.map l.op)
    (b.hom.app (op U))
    ((Classical.forgetCoefficients.{u + 1, u, u, u}.map a).hom.app (op V))
    ((Classical.forgetCoefficients.{u + 1, u, u, u}.obj G).obj.map l.op) h t
  exact he.trans (forgetCoefficients_section_apply f R a V U l t)

/-- Under the existing degree-zero equivalence, module cohomological pullback
is the native global-section map defined from the original module adjunction. -/
theorem etaleCohomologyPullbackMap_zero_globalSections
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (x : etaleCohomology Y R F 0) :
    Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u}
        ((etalePullback f R).obj F)
        (MorphismProperty.Over.mkIdTerminal
          (show MorphismProperty Scheme.{u} from @Etale) X)
        (etaleCohomologyPullbackMap f R F 0 x) =
      etalePullbackGlobalSectionsMap f R F
        (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F
          (MorphismProperty.Over.mkIdTerminal
            (show MorphismProperty Scheme.{u} from @Etale) Y) x) := by
  let U : X.Etale := Scheme.Etale.mk (𝟙 X)
  let V : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let hU : IsTerminal U := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let hV : IsTerminal V := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y
  let l : U ⟶ (etaleBaseChange f).obj V :=
    etaleBaseChangeLift f f ((Category.comp_id f).trans (Category.id_comp f).symm)
  let FY := Classical.forgetCoefficients.{u + 1, u, u, u}.obj F
  let FX := (etalePullback f R).obj F
  let AX := (etaleAbelianPullback f).obj FY
  let e : Classical.forgetCoefficients.{u + 1, u, u, u}.obj FX ≅ AX :=
    (etalePullbackForgetCoefficientsIso f R).app F
  have hzero := etaleAbelianCohomologyPullbackMap_zero_sections f FY hV hU l x
  have hcoeff := (Sheaf.H.equiv₀_naturality hU e.inv
    (etaleAbelianCohomologyPullbackMap f FY 0 x)).symm
  let t : FY.obj.obj (op V) := Sheaf.H.equiv₀ FY hV x
  have hsections := forgetCoefficients_sectionDiagram f R (F := F) (G := FX) (A := AX) e.inv
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app FY)
    ((etalePullbackPushforwardAdjunction f R).unit.app F) V U l
    (forgetCoefficients_pullbackSection f R F V U l) t
  have htarget := moduleZeroEquiv_apply FX hU (etaleCohomologyPullbackMap f R F 0 x)
  have hpull := congrArg
    (fun z : etaleCohomology X R FX 0 =>
      Sheaf.H.equiv₀ (Classical.forgetCoefficients.{u + 1, u, u, u}.obj FX) hU z)
    (modulePullback_apply f R F 0 x)
  have hsource := congrArg (fun z : F.obj.obj (op V) =>
    etalePullbackGlobalSectionsMap f R F z) (moduleZeroEquiv_apply F hV x)
  have hglobal := moduleGlobalSections_apply f R F t
  have hpoint := congrArg
    (fun z : AX.obj.obj (op U) => e.inv.hom.app (op U) z) hzero
  exact Eq.trans (α := FX.obj.obj (op U)) htarget
    (Eq.trans (α := FX.obj.obj (op U)) hpull
      (Eq.trans (α := FX.obj.obj (op U)) hcoeff
        (Eq.trans (α := FX.obj.obj (op U)) hpoint
          (Eq.trans (α := FX.obj.obj (op U)) hsections
            (Eq.trans (α := FX.obj.obj (op U)) hglobal.symm hsource.symm)))))

end EtaleCohomology
