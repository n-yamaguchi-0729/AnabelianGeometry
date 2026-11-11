/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.CupCoefficientRestriction
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.SchemeTheory.HomologicalAlgebra.ExtAdjunctionAcyclic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The actual constant Ext source under coefficient restriction

The original coefficient adjunction supplies the integer-source morphism.
Its degree-zero section is the original constant section one. The actual
coefficient map preserves this section, so restriction of scalars commutes
with the native constant-source Ext comparison in every degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The integer-source morphism of the original constant module Ext
comparison, obtained from its actual coefficient adjunction. -/
def etaleConstantIntegerHom :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) (R := R)).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :=
  etaleModuleIntegerHomForgetEquiv X R
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      (etaleFreeIntegerModuleSheafIsoConstant X R).hom

/-- The native constant-source comparison is the actual integer-source
morphism followed by the exact coefficient-forgetting map on Ext. -/
theorem etaleConstantModuleExtCohomologyEquiv_forget
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (a : Ext.{u}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) F n) :
    etaleConstantModuleExtCohomologyEquiv X R F n a =
      (Ext.mk₀ (etaleConstantIntegerHom X R)).comp
        (a.mapExactFunctor (Classical.forgetCoefficients.{u + 1, u, u, u}
          (J := X.smallEtaleTopology) (R := R))) (zero_add n) := by
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let e := etaleFreeIntegerModuleSheafIsoConstant X R
  change etaleModuleExtCohomologyMap X R F n
    ((Ext.mk₀ e.hom).comp a (zero_add n)) = _
  have h : etaleModuleExtCohomologyMap X R F n
      ((Ext.mk₀ e.hom).comp a (zero_add n)) =
        (etaleModuleExtCohomologyMap X R C 0 (Ext.mk₀ e.hom)).comp
          (a.mapExactFunctor U) (zero_add n) := by
    unfold etaleModuleExtCohomologyMap
    exact Adjunction.extMapOfExactRight_comp _ Z (Ext.mk₀ e.hom) a (zero_add n)
  exact h.trans (congrArg (fun z : Ext.{u} Z (U.obj C) 0 =>
    z.comp (a.mapExactFunctor U) (zero_add n))
      (etaleModuleExtCohomologyMap_mk₀ X R e.hom))

private theorem constantIntegerHom_sections :
    Sheaf.H.equiv₀.{u}
        ((Classical.forgetCoefficients.{u + 1, u, u, u}
          (J := X.smallEtaleTopology) (R := R)).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)))
        terminalIsTerminal (Ext.mk₀ (etaleConstantIntegerHom X R)) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).unit.app (ModuleCat.of R R) (1 : R) := by
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let e := etaleFreeIntegerModuleSheafIsoConstant X R
  have hm : etaleModuleExtCohomologyMap X R C 0 (Ext.mk₀ e.hom) =
      Ext.mk₀ (etaleConstantIntegerHom X R) :=
    etaleModuleExtCohomologyMap_mk₀ X R e.hom
  have hs := etaleFreeIntegerModuleSheafIsoConstant_hom_sections X R C (𝟙 C)
  rw [Category.comp_id] at hs
  have hs' : Sheaf.H.equiv₀.{u} (U.obj C) terminalIsTerminal
      (etaleModuleExtCohomologyMap X R C 0 (Ext.mk₀ e.hom)) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).unit.app (ModuleCat.of R R) (1 : R) := by
    let E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
      (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale))
    let η : ModuleCat.of R R ⟶ E.obj C :=
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).unit.app (ModuleCat.of R R)
    rw [Adjunction.homEquiv_unit] at hs
    change Sheaf.H.equiv₀.{u} (U.obj C) terminalIsTerminal
        (etaleModuleExtCohomologyMap X R C 0 (Ext.mk₀ e.hom)) =
      (η ≫ E.map (𝟙 C)) (1 : R) at hs
    have hE : E.map (𝟙 C) = 𝟙 (E.obj C) := E.map_id C
    have hη : η ≫ E.map (𝟙 C) = η :=
      (congrArg (fun k : E.obj C ⟶ E.obj C => η ≫ k) hE).trans (Category.comp_id η)
    exact hs.trans (ConcreteCategory.congr_hom hη (1 : R))
  exact (congrArg (Sheaf.H.equiv₀.{u} (U.obj C) terminalIsTerminal) hm).symm.trans hs'

variable {R} {S : Type u} [CommRing S] (f : R →+* S)

/-- The actual integer-source morphism is compatible with change of
coefficient ring; preservation of its section one proves the square. -/
theorem etaleConstantIntegerHom_coefficient :
    etaleConstantIntegerHom X R ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}
          (J := X.smallEtaleTopology) (R := R)).map (etaleConstantCoefficientHom X f) =
      etaleConstantIntegerHom X S := by
  let CR := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let CS := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)
  let CZ := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let UR := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let US := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := S)
  let a : CR ⟶ (etaleRestrictCoefficients X f).obj CS := etaleConstantCoefficientHom X f
  let b : UR.obj CR ⟶ US.obj CS := UR.map a
  let ηR : ModuleCat.of R R ⟶ CR.obj.obj (op (⊤_ X.Etale)) :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
      terminalIsTerminal).unit.app (ModuleCat.of R R)
  let ηS : ModuleCat.of S S ⟶ CS.obj.obj (op (⊤_ X.Etale)) :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} S)
      terminalIsTerminal).unit.app (ModuleCat.of S S)
  change etaleConstantIntegerHom X R ≫ b = etaleConstantIntegerHom X S
  apply (Ext.mk₀_bijective CZ (US.obj CS)).injective
  apply (Sheaf.H.equiv₀.{u} (US.obj CS) terminalIsTerminal).injective
  have hm : (Ext.mk₀ (etaleConstantIntegerHom X R)).comp (Ext.mk₀ b) (zero_add 0) =
      Ext.mk₀ (etaleConstantIntegerHom X R ≫ b) :=
    Ext.mk₀_comp_mk₀ (etaleConstantIntegerHom X R) b
  have hn : b.hom.app (op (⊤_ X.Etale))
        (Sheaf.H.equiv₀.{u} (UR.obj CR) terminalIsTerminal
          (Ext.mk₀ (etaleConstantIntegerHom X R))) =
      Sheaf.H.equiv₀.{u} (US.obj CS) terminalIsTerminal
        ((Ext.mk₀ (etaleConstantIntegerHom X R)).comp (Ext.mk₀ b) (zero_add 0)) :=
    Sheaf.H.equiv₀_naturality terminalIsTerminal b
      (Ext.mk₀ (etaleConstantIntegerHom X R))
  have hc : b.hom.app (op (⊤_ X.Etale)) (ηR (1 : R)) = ηS (1 : S) := by
    change a.hom.app (op (⊤_ X.Etale)) (ηR (1 : R)) = ηS (1 : S)
    exact (etaleConstantCoefficientHom_unit X f (1 : R)).trans (congrArg ηS f.map_one)
  exact (congrArg (Sheaf.H.equiv₀.{u} (US.obj CS) terminalIsTerminal) hm.symm).trans
    (hn.symm.trans
      ((congrArg (b.hom.app (op (⊤_ X.Etale))) (constantIntegerHom_sections X R)).trans
        (hc.trans (constantIntegerHom_sections X S).symm)))

/-- Restriction of scalars and the actual constant coefficient source map
recover the same original classical cohomology class in every degree. -/
theorem etaleConstantModuleExtCohomologyEquiv_restrictCoefficients
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} S)) (n : ℕ)
    (a : Ext.{u}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)) F n) :
    etaleConstantModuleExtCohomologyEquiv X R
        ((etaleRestrictCoefficients X f).obj F) n
        ((Ext.mk₀ (etaleConstantCoefficientHom X f)).comp
          (a.mapExactFunctor (etaleRestrictCoefficients X f)) (zero_add n)) =
      etaleConstantModuleExtCohomologyEquiv X S F n a := by
  let L := etaleRestrictCoefficients X f
  let UR := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let US := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := S)
  have hm : (a.mapExactFunctor L).mapExactFunctor UR = a.mapExactFunctor US :=
    (Ext.comp_mapExactFunctor a L UR).symm
  rw [etaleConstantModuleExtCohomologyEquiv_forget,
    etaleConstantModuleExtCohomologyEquiv_forget, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    etaleConstantIntegerHom_coefficient]
  exact congrArg (fun z => (Ext.mk₀ (etaleConstantIntegerHom X S)).comp z (zero_add n)) hm

end EtaleCohomology
