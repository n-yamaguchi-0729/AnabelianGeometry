/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantH0Comparison
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.EtaleCohomology.Classical.SheafH0TerminalTransport
public import Nyll.EtaleCohomology.Sites.ConnectedModuleConstants
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The actual cup unit in the original degree-zero comparison

The original Yoneda identity class is the actual constant section one,
at every terminal object of the small étale site. Forgetting coefficients
preserves that section, so the original connected H⁰ comparison sends the
actual finite-level cup unit to one. Terminal comparison is made through
the original restriction maps, rather than identifying chosen terminals.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable (X : Scheme.{u})

private theorem constantUnit_toSheafify
    (D : Type*) [Category* D] [HasWeakSheafify X.smallEtaleTopology D]
    {T : X.Etale} (hT : IsTerminal T) (A : D) :
    (constantSheafAdj X.smallEtaleTopology D hT).unit.app A =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op T) := by
  rw [constantSheafAdj, Adjunction.comp_unit_app]
  change 𝟙 A ≫ _ = _
  exact Category.id_comp _

private theorem constantUnit_restriction
    (D : Type*) [Category* D] [HasWeakSheafify X.smallEtaleTopology D]
    {T S : X.Etale} (hT : IsTerminal T) (hS : IsTerminal S) (j : T ⟶ S) (A : D) :
    (constantSheafAdj X.smallEtaleTopology D hS).unit.app A ≫
        ((constantSheaf X.smallEtaleTopology D).obj A).obj.map j.op =
      (constantSheafAdj X.smallEtaleTopology D hT).unit.app A := by
  rw [constantUnit_toSheafify, constantUnit_toSheafify]
  exact ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).naturality
    j.op).symm.trans
      (Category.id_comp
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op T)))

variable (R : Type u) [CommRing R]

/-- The original Yoneda cup unit has the actual constant section one
at any terminal étale object. -/
theorem etaleCohomologyCupUnit_sections {T : X.Etale} (hT : IsTerminal T) :
    Classical.cohomologyZeroEquiv
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) hT
        (etaleCohomologyCupUnit X R) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).unit.app
        (ModuleCat.of R R) (1 : R) := by
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let e := etaleFreeIntegerModuleSheafIsoConstant X R
  have hs := etaleFreeIntegerModuleSheafIsoConstant_hom_sections X R C (𝟙 C)
  rw [Category.comp_id] at hs
  have h₀ : etaleCohomologyZeroEquiv X R C (etaleCohomologyCupUnit X R) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).unit.app (ModuleCat.of R R) (1 : R) := by
    change etaleCohomologyZeroEquiv X R C
      (etaleModuleExtCohomologyEquiv X R C 0
        ((Ext.mk₀ e.hom).comp (Ext.mk₀ (𝟙 C)) (zero_add 0))) = _
    rw [Ext.comp_mk₀_id]
    let E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
      (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale))
    let η : ModuleCat.of R R ⟶ E.obj C :=
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).unit.app (ModuleCat.of R R)
    rw [Adjunction.homEquiv_unit] at hs
    change etaleCohomologyZeroEquiv X R C
        (etaleModuleExtCohomologyEquiv X R C 0 (Ext.mk₀ e.hom)) =
      (η ≫ E.map (𝟙 C)) (1 : R) at hs
    have hE : E.map (𝟙 C) = 𝟙 (E.obj C) := E.map_id C
    have hη : η ≫ E.map (𝟙 C) = η :=
      (congrArg (fun k : E.obj C ⟶ E.obj C => η ≫ k) hE).trans (Category.comp_id η)
    exact hs.trans (ConcreteCategory.congr_hom hη (1 : R))
  let j : T ⟶ ⊤_ X.Etale := terminal.from T
  change Sheaf.H.equiv₀.{u} (U.obj C) hT (etaleCohomologyCupUnit X R) = _
  have h₀' : Sheaf.H.equiv₀.{u} (U.obj C) terminalIsTerminal
      (etaleCohomologyCupUnit X R) =
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
      terminalIsTerminal).unit.app (ModuleCat.of R R) (1 : R) := h₀
  exact (sheafH0_restriction (U.obj C) hT terminalIsTerminal j
    (etaleCohomologyCupUnit X R)).symm.trans
      ((congrArg ((U.obj C).obj.map j.op) h₀').trans
        (ConcreteCategory.congr_hom
          (constantUnit_restriction X (ModuleCat.{u} R) hT terminalIsTerminal j
            (ModuleCat.of R R)) (1 : R)))

variable [ConnectedSpace X]

/-- The original connected H⁰ comparison sends the forgotten native
cup unit to one in its original regular coefficient group. -/
theorem etaleCohomologyCupUnit_constantH0 :
    Classical.constantH0Equiv X
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (ModuleCat.of R R))
        (etaleConstantCohomologyForgetEquiv R (X := X) (ModuleCat.of R R) 0
          (etaleCohomologyCupUnit X R)) = (1 : R) := by
  let M := ModuleCat.of R R
  let V := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let A := V.obj M
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X)
    ((show MorphismProperty Scheme.{u} from @Etale).id_mem X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let ηM := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).unit.app M
  let ηA := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app A
  let δ := (etaleConstantModuleForgetIso X R).app M
  let δT := ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)).mapIso δ
  have hη : V.map ηM ≫ δT.hom = ηA := etaleConstantModuleForgetIso_unit X R hT M
  have : IsIso ηM := etaleConstantModuleSheaf_unit_isIso X R M
  have : IsIso ηA := by
    rw [← hη]
    let eM := V.mapIso (asIso ηM)
    exact inferInstanceAs (IsIso (eM ≪≫ δT).hom)
  apply (asIso ηA).addCommGroupIsoToAddEquiv.injective
  change ηA (Classical.constantH0Equiv X A
    (Sheaf.H.map δ.hom 0 (etaleCohomologyCupUnit X R))) = ηA (1 : R)
  rw [Classical.constantH0Equiv_unit]
  calc
    _ = δ.hom.hom.app (op T)
        (Sheaf.H.equiv₀.{u} (U.obj C) hT (etaleCohomologyCupUnit X R)) :=
      (Sheaf.H.equiv₀_naturality hT δ.hom (etaleCohomologyCupUnit X R)).symm
    _ = δT.hom (ηM (1 : R)) :=
      congrArg (δ.hom.hom.app (op T)) (etaleCohomologyCupUnit_sections X R hT)
    _ = ηA (1 : R) := ConcreteCategory.congr_hom hη (1 : R)

namespace Classical

/-- The original finite-level cup unit is one under the original
constant-coefficient H⁰ equivalence. -/
theorem finiteLevelCupUnit_constantH0 (ℓ n : ℕ) :
    constantH0Equiv X (ellPowerCoefficients ℓ n) (finiteLevelCupUnit X ℓ n) =
      (1 : ULift.{u} (ZMod (ℓ ^ (n + 1)))) :=
  etaleCohomologyCupUnit_constantH0 X (ULift.{u} (ZMod (ℓ ^ (n + 1))))

end Classical

end EtaleCohomology
