/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.ConstantPullbackCompositionAcrossSites
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Composition of pullbacks needed for external cup

The actual base-change comparison and the constant-sheaf adjunction units
give composition for maps between different schemes. Ext functoriality
then proves composition on the original abelian cohomology. The same
original maps compose at every finite level, on the integral inverse
limits, and on the original rational scalar extensions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual inverse image by a composite agrees with successive
inverse images through the original base-change comparison. -/
def etaleAbelianPullbackCompIso :
    etaleAbelianPullback (f ≫ g) ≅ etaleAbelianPullback g ⋙ etaleAbelianPullback f := by
  have : (etaleBaseChange g ⋙ etaleBaseChange f).IsContinuous
      Z.smallEtaleTopology X.smallEtaleTopology :=
    Functor.isContinuous_comp (etaleBaseChange g) (etaleBaseChange f)
      Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
  let e : etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) (Q := ⊤) f g
  let β : etaleAbelianPushforward (f ≫ g) ≅
      etaleAbelianPushforward f ⋙ etaleAbelianPushforward g :=
    Functor.sheafPushforwardContinuousIso e AddCommGrpCat.{u}
      Z.smallEtaleTopology X.smallEtaleTopology
  exact (etaleAbelianPullbackPushforwardAdjunction (f ≫ g)).leftAdjointUniq
    (((etaleAbelianPullbackPushforwardAdjunction g).comp
      (etaleAbelianPullbackPushforwardAdjunction f)).ofNatIsoRight β.symm)

/-- The actual composition comparison preserves both canonical
constant-sheaf comparisons, even when the three schemes differ. -/
theorem etaleAbelianPullbackCompIso_constant (A : AddCommGrpCat.{u}) :
    (etaleAbelianPullbackCompIso f g).hom.app
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj A) ≫
      (etaleAbelianPullback f).map ((etaleAbelianPullbackConstantIso g).hom.app A) ≫
        (etaleAbelianPullbackConstantIso f).hom.app A =
    (etaleAbelianPullbackConstantIso (f ≫ g)).hom.app A := by
  have : (etaleBaseChange g ⋙ etaleBaseChange f).IsContinuous
      Z.smallEtaleTopology X.smallEtaleTopology :=
    Functor.isContinuous_comp (etaleBaseChange g) (etaleBaseChange f)
      Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
  let e : etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) (Q := ⊤) f g
  let adj := (etaleAbelianPullbackPushforwardAdjunction g).comp
    (etaleAbelianPullbackPushforwardAdjunction f)
  let ec := Sites.constantSheafCompLeftAdjointIso
    (etaleBaseChange g ⋙ etaleBaseChange f) AddCommGrpCat.{u} terminalIsTerminal
    (terminalIsTerminal.isTerminalObj (etaleBaseChange g ⋙ etaleBaseChange f) (⊤_ Z.Etale))
    (etaleAbelianPullback g ⋙ etaleAbelianPullback f) adj
  have h₁ : (etaleAbelianPullbackCompIso f g).hom.app
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj A) ≫ ec.hom.app A =
      (etaleAbelianPullbackConstantIso (f ≫ g)).hom.app A :=
    Sites.constantSheafCompLeftAdjointIso_hom_comp_siteIso_betweenSites
      Z.smallEtaleTopology X.smallEtaleTopology AddCommGrpCat.{u}
      (etaleBaseChange (f ≫ g)) (etaleBaseChange g ⋙ etaleBaseChange f) e terminalIsTerminal
      (terminalIsTerminal.isTerminalObj (etaleBaseChange (f ≫ g)) (⊤_ Z.Etale))
      (terminalIsTerminal.isTerminalObj (etaleBaseChange g ⋙ etaleBaseChange f)
        (⊤_ Z.Etale))
      (etaleAbelianPullback (f ≫ g)) (etaleAbelianPullback g ⋙ etaleAbelianPullback f)
      (etaleAbelianPullbackPushforwardAdjunction (f ≫ g)) adj A
  have h₂ : ec.hom.app A =
      (etaleAbelianPullback f).map ((etaleAbelianPullbackConstantIso g).hom.app A) ≫
        (etaleAbelianPullbackConstantIso f).hom.app A :=
    Sites.constantSheafCompLeftAdjointIso_hom_comp_betweenSites
      Z.smallEtaleTopology Y.smallEtaleTopology AddCommGrpCat.{u} X.smallEtaleTopology
      (etaleBaseChange f) (etaleBaseChange g)
      (terminalIsTerminal : IsTerminal (⊤_ Z.Etale))
      (terminalIsTerminal : IsTerminal (⊤_ Y.Etale))
      (terminalIsTerminal.isTerminalObj (etaleBaseChange g) (⊤_ Z.Etale))
      (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
      (terminalIsTerminal.isTerminalObj (etaleBaseChange g ⋙ etaleBaseChange f)
        (⊤_ Z.Etale))
      (etaleAbelianPullback f) (etaleAbelianPullback g)
      (etaleAbelianPullbackPushforwardAdjunction f)
      (etaleAbelianPullbackPushforwardAdjunction g) A
  rw [h₂] at h₁
  exact h₁

/-- Original abelian cohomological pullback composes under the actual
inverse-image comparison, in every degree and between different schemes. -/
theorem etaleAbelianCohomologyPullbackMap_comp
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) (x : Sheaf.H.{u} F n) :
    Sheaf.H.map ((etaleAbelianPullbackCompIso f g).hom.app F) n
        (etaleAbelianCohomologyPullbackMap (f ≫ g) F n x) =
      etaleAbelianCohomologyPullbackMap f ((etaleAbelianPullback g).obj F) n
        (etaleAbelianCohomologyPullbackMap g F n x) := by
  let ZX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let ZY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let ZZ := (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let ef : (etaleAbelianPullback f).obj ZY ≅ ZX :=
    (etaleAbelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let eg : (etaleAbelianPullback g).obj ZZ ≅ ZY :=
    (etaleAbelianPullbackConstantIso g).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let efg : (etaleAbelianPullback (f ≫ g)).obj ZZ ≅ ZX :=
    (etaleAbelianPullbackConstantIso (f ≫ g)).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let ec : (etaleAbelianPullback g ⋙ etaleAbelianPullback f).obj ZZ ≅ ZX :=
    (etaleAbelianPullback f).mapIso eg ≪≫ ef
  let τ : etaleAbelianPullback (f ≫ g) ⟶
      etaleAbelianPullback g ⋙ etaleAbelianPullback f := (etaleAbelianPullbackCompIso f g).hom
  have hZ : τ.app ZZ ≫ ec.hom = efg.hom :=
    etaleAbelianPullbackCompIso_constant f g (AddCommGrpCat.of (ULift.{u} ℤ))
  have hi : efg.inv ≫ τ.app ZZ = ec.inv := by
    apply (cancel_mono ec.hom).mp
    rw [Category.assoc, hZ, efg.inv_hom_id, ec.inv_hom_id]
  have hx := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
  rw [Sheaf.H.map_apply, etaleAbelianCohomologyPullbackMap_apply,
    etaleAbelianCohomologyPullbackMap_apply, etaleAbelianCohomologyPullbackMap_apply,
    Ext.comp_assoc_of_third_deg_zero]
  change (Ext.mk₀ efg.inv).comp
      ((x.mapExactFunctor (etaleAbelianPullback (f ≫ g))).comp
        (Ext.mk₀ (τ.app F)) (add_zero n)) (zero_add n) =
    (Ext.mk₀ ef.inv).comp
      (((Ext.mk₀ eg.inv).comp
        (x.mapExactFunctor (etaleAbelianPullback g)) (zero_add n)).mapExactFunctor
          (etaleAbelianPullback f)) (zero_add n)
  rw [hx, Ext.mk₀_comp_mk₀_assoc, hi, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, ← Ext.comp_mapExactFunctor]
  rfl

private theorem constantCohomologyPullback_apply_as_map
    {U V : Scheme.{u}} (h : U ⟶ V) (A : AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H.{u} ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    EtaleFundamentalGroups.Cohomology.constantCohomologyPullback h A n a =
      Sheaf.H.map ((etaleAbelianPullbackConstantIso h).app A).hom n
        (etaleAbelianCohomologyPullbackMap h
          ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u}).obj A) n a) := by
  rfl

/-- With the canonical constant-sheaf maps, original constant abelian
pullback composes without an additional coefficient comparison. -/
theorem etaleAbelianConstantCohomologyPullbackMap_comp
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    EtaleFundamentalGroups.Cohomology.constantCohomologyPullback (f ≫ g) A n x =
      EtaleFundamentalGroups.Cohomology.constantCohomologyPullback f A n
        (EtaleFundamentalGroups.Cohomology.constantCohomologyPullback g A n x) := by
  let Lf : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleAbelianPullback f
  let Lg : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} := etaleAbelianPullback g
  let Lfg : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleAbelianPullback (f ≫ g)
  let FX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let FY : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let FZ : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let ef : Lf.obj FY ⟶ FX := (etaleAbelianPullbackConstantIso f).hom.app A
  let eg : Lg.obj FZ ⟶ FY := (etaleAbelianPullbackConstantIso g).hom.app A
  let efg : Lfg.obj FZ ⟶ FX := (etaleAbelianPullbackConstantIso (f ≫ g)).hom.app A
  let τ : Lfg.obj FZ ⟶ Lf.obj (Lg.obj FZ) :=
    (etaleAbelianPullbackCompIso f g).hom.app FZ
  let feg : Lf.obj (Lg.obj FZ) ⟶ Lf.obj FY := Lf.map eg
  let xg : Sheaf.H.{u} (Lg.obj FZ) n := etaleAbelianCohomologyPullbackMap g FZ n x
  let xgf : Sheaf.H.{u} (Lf.obj (Lg.obj FZ)) n :=
    etaleAbelianCohomologyPullbackMap f (Lg.obj FZ) n xg
  let y : Sheaf.H.{u} (Lfg.obj FZ) n :=
    etaleAbelianCohomologyPullbackMap (f ≫ g) FZ n x
  let r : Sheaf.H.{u} (Lf.obj FY) n :=
    etaleAbelianCohomologyPullbackMap f FY n (Sheaf.H.map eg n xg)
  have hA : τ ≫ feg ≫ ef = efg := etaleAbelianPullbackCompIso_constant f g A
  have hP : Sheaf.H.map τ n y = xgf :=
    etaleAbelianCohomologyPullbackMap_comp f g FZ n x
  have hn : r = Sheaf.H.map feg n xgf :=
    etaleAbelianCohomologyPullbackMap_naturality f eg n xg
  have hc : Sheaf.H.map (τ ≫ feg ≫ ef) n y =
      Sheaf.H.map ef n (Sheaf.H.map feg n (Sheaf.H.map τ n y)) :=
    (Sheaf.H.map_comp_apply τ (feg ≫ ef) y).trans
      (Sheaf.H.map_comp_apply feg ef (Sheaf.H.map τ n y))
  have h : Sheaf.H.map efg n y = Sheaf.H.map ef n r :=
    (congrArg (fun φ : Lfg.obj FZ ⟶ FX => Sheaf.H.map φ n y) hA.symm).trans
      (hc.trans
        ((congrArg (fun z : Sheaf.H.{u} (Lf.obj (Lg.obj FZ)) n =>
          Sheaf.H.map ef n (Sheaf.H.map feg n z)) hP).trans
            (congrArg (fun z : Sheaf.H.{u} (Lf.obj FY) n => Sheaf.H.map ef n z) hn.symm)))
  have hfg : EtaleFundamentalGroups.Cohomology.constantCohomologyPullback
      (f ≫ g) A n x = Sheaf.H.map efg n y :=
    constantCohomologyPullback_apply_as_map (f ≫ g) A n x
  have hg : EtaleFundamentalGroups.Cohomology.constantCohomologyPullback
      g A n x = Sheaf.H.map eg n xg :=
    constantCohomologyPullback_apply_as_map g A n x
  have hf : EtaleFundamentalGroups.Cohomology.constantCohomologyPullback
      f A n (Sheaf.H.map eg n xg) = Sheaf.H.map ef n r :=
    constantCohomologyPullback_apply_as_map f A n (Sheaf.H.map eg n xg)
  have hr : EtaleFundamentalGroups.Cohomology.constantCohomologyPullback f A n
      (EtaleFundamentalGroups.Cohomology.constantCohomologyPullback g A n x) =
        Sheaf.H.map ef n r :=
    (congrArg (fun z : Sheaf.H.{u} FY n =>
      EtaleFundamentalGroups.Cohomology.constantCohomologyPullback f A n z) hg).trans hf
  exact hfg.trans (h.trans hr.symm)

namespace Classical

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Original finite-level pullback composes for arbitrary scheme maps. -/
theorem finiteLevelCohomologyPullback_comp (n i : ℕ) :
    finiteLevelCohomologyPullback ℓ (f ≫ g) n i =
      (finiteLevelCohomologyPullback ℓ f n i).comp
        (finiteLevelCohomologyPullback ℓ g n i) := by
  apply LinearMap.ext
  intro x
  exact etaleAbelianConstantCohomologyPullbackMap_comp f g (ellPowerCoefficients ℓ n) i x

/-- Original integral pullback composes on the existing inverse limits
for arbitrary scheme maps. -/
theorem ellAdicCohomologyPullback_comp (i : ℕ) :
    ellAdicCohomologyPullback ℓ (f ≫ g) i =
      (ellAdicCohomologyPullback ℓ f i).comp (ellAdicCohomologyPullback ℓ g i) := by
  apply LinearMap.ext
  intro x
  apply ellAdicCohomology_ext X ℓ i
  intro n
  exact LinearMap.congr_fun (finiteLevelCohomologyPullback_comp f g ℓ n i) (x.val n)

/-- Original rational pullback composes for arbitrary scheme maps on the
existing rational scalar extensions. -/
theorem rationalEllAdicCohomologyPullback_comp (i : ℕ) :
    rationalEllAdicCohomologyPullback ℓ (f ≫ g) i =
      (rationalEllAdicCohomologyPullback ℓ f i).comp
        (rationalEllAdicCohomologyPullback ℓ g i) := by
  change (ellAdicCohomologyPullback ℓ (f ≫ g) i).baseChange ℚ_[ℓ] =
    ((ellAdicCohomologyPullback ℓ f i).baseChange ℚ_[ℓ]).comp
      ((ellAdicCohomologyPullback ℓ g i).baseChange ℚ_[ℓ])
  rw [ellAdicCohomologyPullback_comp]
  exact LinearMap.baseChange_comp (A := ℚ_[ℓ])
    (ellAdicCohomologyPullback ℓ g i) (ellAdicCohomologyPullback ℓ f i)

end Classical

end EtaleCohomology
