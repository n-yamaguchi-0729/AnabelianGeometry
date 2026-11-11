/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Sites.ConnectedModuleConstants
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Degree-zero constant cohomology on a connected scheme

The actual constant-module unit and coefficient-forgetting comparison show
that the original constant abelian sheaf has exactly its constant global
sections. Composing with the original degree-zero Ext equivalence gives H⁰
with its coefficient naturality and its actual scheme-pullback naturality.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology.Classical

private theorem constantUnit_eq_toSheafify
    (X : Scheme.{u}) {T : X.Etale} (hT : IsTerminal T) (A : AddCommGrpCat.{u}) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app A =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op T) := by
  rw [constantSheafAdj, Adjunction.comp_unit_app]
  change 𝟙 A ≫ _ = _
  exact Category.id_comp _

variable (X : Scheme.{u}) [ConnectedSpace X]

/-- On a connected scheme, the constant abelian sheaf unit is an isomorphism. -/
theorem constantAbelianUnit_isIso (A : AddCommGrpCat.{u}) :
    IsIso ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X)).unit.app A) := by
  let R := ULift.{u} ℤ
  let : Module R A := Module.compHom A
    (ULift.ringEquiv : R ≃+* ℤ).toRingHom
  let M : ModuleCat.{u} R := ModuleCat.of R A
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X)
    ((show MorphismProperty Scheme.{u} from @Etale).id_mem X)
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  have : IsIso ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).unit.app M) :=
    etaleConstantModuleSheaf_unit_isIso X R M
  change IsIso ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M))
  rw [← etaleConstantModuleForgetIso_unit X R hT M]
  let eT := ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)).mapIso
    ((etaleConstantModuleForgetIso X R).app M)
  let eM := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapIso
    (asIso ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).unit.app M))
  exact inferInstanceAs (IsIso (eM ≪≫ eT).hom)

/-- Actual constant abelian H⁰ recovers its coefficient group on a connected
scheme, through the original Ext-to-sections equivalence and adjunction unit. -/
def constantH0Equiv (A : AddCommGrpCat.{u}) :
    Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 0 ≃+ A := by
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let η := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app A
  let : IsIso η := constantAbelianUnit_isIso X A
  exact (Sheaf.H.equiv₀.{u}
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) hT).trans
      (asIso η).addCommGroupIsoToAddEquiv.symm

/-- The comparison sends a cohomology class to the constant whose actual
adjunction-unit section is its degree-zero section. -/
theorem constantH0Equiv_unit (A : AddCommGrpCat.{u})
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 0) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app A
      (constantH0Equiv X A a) = Sheaf.H.equiv₀.{u}
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) hT a := by
  intro hT
  let η := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app A
  have : IsIso η := constantAbelianUnit_isIso X A
  exact (asIso η).addCommGroupIsoToAddEquiv.apply_symm_apply _

/-- The actual H⁰ comparison respects every original map of constant
abelian coefficient sheaves. -/
theorem constantH0Equiv_naturality {A B : AddCommGrpCat.{u}} (f : A ⟶ B)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 0) :
    constantH0Equiv X B
      (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map f) 0 a) =
        f (constantH0Equiv X A a) := by
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT
  have : IsIso (adj.unit.app B) := constantAbelianUnit_isIso X B
  apply (asIso (adj.unit.app B)).addCommGroupIsoToAddEquiv.injective
  change adj.unit.app B (constantH0Equiv X B _) = adj.unit.app B (f (constantH0Equiv X A a))
  rw [constantH0Equiv_unit]
  calc
    _ = ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map f).hom.app _
        (Sheaf.H.equiv₀.{u}
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) hT a) :=
      (Sheaf.H.equiv₀_naturality.{u} (J := X.smallEtaleTopology)
        (F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A)
        (G := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj B) hT
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map f) a).symm
    _ = ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map f).hom.app _
        (adj.unit.app A (constantH0Equiv X A a)) :=
      congrArg _ (constantH0Equiv_unit X A a).symm
    _ = adj.unit.app B (f (constantH0Equiv X A a)) :=
      (ConcreteCategory.congr_hom (adj.unit.naturality f) (constantH0Equiv X A a)).symm

variable {X} {Y : Scheme.{u}} [ConnectedSpace Y] (f : X ⟶ Y)

/-- Pullback along the actual inverse-image functor preserves the constant
underlying an H⁰ class. Both schemes may be arbitrary connected schemes. -/
theorem constantH0Equiv_pullback (A : AddCommGrpCat.{u})
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 0) :
    constantH0Equiv X A
      (Sheaf.H.map ((etaleAbelianPullbackConstantIso f).hom.app A) 0
        (etaleAbelianCohomologyPullbackMap f
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 0 a)) =
        constantH0Equiv Y A a := by
  let V : Y.Etale := MorphismProperty.Over.mk ⊤ (𝟙 Y)
    ((show MorphismProperty Scheme.{u} from @Etale).id_mem Y)
  let U : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X)
    ((show MorphismProperty Scheme.{u} from @Etale).id_mem X)
  let hV : IsTerminal V := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y
  let hU : IsTerminal U := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let l : U ⟶ (etaleBaseChange f).obj V :=
    (hV.isTerminalObj (etaleBaseChange f) V).from U
  let FY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let e : (etaleAbelianPullback f).obj FY ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A :=
    (etaleAbelianPullbackConstantIso f).app A
  let ηX := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hU).unit.app A
  let ηY := (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} hV).unit.app A
  have : IsIso ηX := constantAbelianUnit_isIso X A
  let L := etaleAbelianPullback f
  let CX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let tx := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op U)
  let ty := (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op V)
  let up := ((etaleAbelianPullbackPushforwardAdjunction f).unit.app FY).hom.app (op V)
  let res := (L.obj FY).obj.map l.op
  have hcomp : e.inv ≫ L.map (𝟙 FY) = e.inv :=
    (congrArg (fun z : L.obj FY ⟶ L.obj FY => e.inv ≫ z)
      (CategoryTheory.Functor.map_id L FY)).trans (Category.comp_id e.inv)
  have hcompU := congrArg (fun z : CX ⟶ L.obj FY => z.hom.app (op U)) hcomp
  have hs0 : tx ≫ (e.inv ≫ L.map (𝟙 FY)).hom.app (op U) =
      ty ≫ (𝟙 FY : FY ⟶ FY).hom.app (op V) ≫ up ≫ res :=
    etaleAbelianConstantHom_pullback_section f A FY (𝟙 FY) V U l
  have hid : (𝟙 FY : FY ⟶ FY).hom.app (op V) ≫ up ≫ res = up ≫ res :=
    Category.id_comp (up ≫ res)
  have hs1 : tx ≫ e.inv.hom.app (op U) = ty ≫ up ≫ res :=
    (congrArg (fun z : CX.obj.obj (op U) ⟶ (L.obj FY).obj.obj (op U) => tx ≫ z)
      hcompU).symm.trans
        (hs0.trans (congrArg (fun z => ty ≫ z) hid))
  have hs : ηX ≫ e.inv.hom.app (op U) = ηY ≫ up ≫ res :=
    (congrArg (fun z : A ⟶ CX.obj.obj (op U) => z ≫ e.inv.hom.app (op U))
      (constantUnit_eq_toSheafify X hU A)).trans
        (hs1.trans (congrArg (fun z : A ⟶ FY.obj.obj (op V) => z ≫ up ≫ res)
          (constantUnit_eq_toSheafify Y hV A).symm))
  let b : Sheaf.H.{u} (L.obj FY) 0 := etaleAbelianCohomologyPullbackMap f FY 0 a
  let c : Sheaf.H.{u} CX 0 := Sheaf.H.map e.hom 0 b
  have hn : e.hom.hom.app (op U) (Sheaf.H.equiv₀.{u} (L.obj FY) hU b) =
      Sheaf.H.equiv₀.{u} CX hU c :=
    Sheaf.H.equiv₀_naturality.{u} (J := X.smallEtaleTopology)
      (F := L.obj FY) (G := CX) hU e.hom b
  have hb : Sheaf.H.equiv₀.{u} (L.obj FY) hU b =
      res (up (Sheaf.H.equiv₀.{u} FY hV a)) :=
    etaleAbelianCohomologyPullbackMap_zero_sections f FY hV hU l a
  have hy : ηY (constantH0Equiv Y A a) = Sheaf.H.equiv₀.{u} FY hV a :=
    constantH0Equiv_unit Y A a
  have hc := ConcreteCategory.congr_hom hs (constantH0Equiv Y A a)
  let eU := ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op U)).mapIso e
  apply (asIso ηX).addCommGroupIsoToAddEquiv.injective
  change ηX (constantH0Equiv X A c) = ηX (constantH0Equiv Y A a)
  calc
    _ = Sheaf.H.equiv₀.{u} CX hU c := constantH0Equiv_unit X A c
    _ = e.hom.hom.app (op U) (Sheaf.H.equiv₀.{u} (L.obj FY) hU b) := hn.symm
    _ = e.hom.hom.app (op U) (res (up (Sheaf.H.equiv₀.{u} FY hV a))) :=
      congrArg (e.hom.hom.app (op U)) hb
    _ = e.hom.hom.app (op U) (res (up (ηY (constantH0Equiv Y A a)))) :=
      congrArg (fun z : FY.obj.obj (op V) => e.hom.hom.app (op U) (res (up z))) hy.symm
    _ = e.hom.hom.app (op U) (e.inv.hom.app (op U) (ηX (constantH0Equiv Y A a))) :=
      congrArg (e.hom.hom.app (op U)) hc.symm
    _ = ηX (constantH0Equiv Y A a) := eU.addCommGroupIsoToAddEquiv.apply_symm_apply _

end EtaleCohomology.Classical
