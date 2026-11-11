/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.CupCoefficientRestriction
public import Nyll.EtaleCohomology.Classical.CupCoefficientSource
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Cup products preserve actual changes of coefficient ring

The native map on cohomology of constant regular module sheaves agrees
with the original map of constant abelian coefficient sheaves. Exact
restriction of scalars and the proved source square move this coefficient
map across Yoneda composition, proving multiplicativity for every ring
homomorphism, including the nonflat finite coefficient reductions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S)

/-- The native cohomology map induced by a homomorphism of coefficient
rings, retaining the original underlying classical cohomology groups. -/
def etaleCohomologyCoefficientMap (n : ℕ) :
    etaleCohomology X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) n →+
      etaleCohomology X S
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)) n :=
  (Classical.cohomologyMap (etaleConstantCoefficientHom X f) n).toAddMonoidHom

private theorem constantCoefficientHom_forget :
    (Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) (R := R)).map (etaleConstantCoefficientHom X f) ≫
      (etaleConstantModuleForgetIso X S).hom.app (ModuleCat.of S S) =
    (etaleConstantModuleForgetIso X R).hom.app (ModuleCat.of R R) ≫
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom f.toAddMonoidHom) := by
  let UR := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let MR := ModuleCat.of R R
  let MS := ModuleCat.of S S
  let AR := AddCommGrpCat.of R
  let AS := AddCommGrpCat.of S
  let K := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal
  let a := etaleConstantCoefficientHom X f
  let dR := (etaleConstantModuleForgetIso X R).app MR
  let dS := (etaleConstantModuleForgetIso X S).app MS
  let dRT := ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (op (⊤_ X.Etale))).mapIso dR
  let ηR := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
    terminalIsTerminal).unit.app MR
  let ηS := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} S)
    terminalIsTerminal).unit.app MS
  let g : AR ⟶ AS := AddCommGrpCat.ofHom f.toAddMonoidHom
  have hi : dR.inv ≫ UR.map a ≫ dS.hom = K.map g := by
    apply (adj.homEquiv AR (K.obj AS)).injective
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro r
    change dS.hom.hom.app (op (⊤_ X.Etale))
        (a.hom.app (op (⊤_ X.Etale))
          (dRT.inv (adj.unit.app AR r))) =
      (K.map g).hom.app (op (⊤_ X.Etale)) (adj.unit.app AR r)
    have hR : dRT.hom (ηR r) = adj.unit.app AR r :=
      ConcreteCategory.congr_hom
        (etaleConstantModuleForgetIso_unit X R terminalIsTerminal MR) r
    have hS : dS.hom.hom.app (op (⊤_ X.Etale)) (ηS (f r)) =
        adj.unit.app AS (f r) :=
      ConcreteCategory.congr_hom
        (etaleConstantModuleForgetIso_unit X S terminalIsTerminal MS) (f r)
    have hRi : dRT.inv (adj.unit.app AR r) = ηR r :=
      (congrArg dRT.inv hR.symm).trans (dRT.addCommGroupIsoToAddEquiv.symm_apply_apply _)
    calc
      _ = dS.hom.hom.app (op (⊤_ X.Etale))
          (a.hom.app (op (⊤_ X.Etale)) (ηR r)) :=
        congrArg (fun z => dS.hom.hom.app (op (⊤_ X.Etale))
          (a.hom.app (op (⊤_ X.Etale)) z)) hRi
      _ = dS.hom.hom.app (op (⊤_ X.Etale)) (ηS (f r)) :=
        congrArg (dS.hom.hom.app (op (⊤_ X.Etale)))
          (etaleConstantCoefficientHom_unit X f r)
      _ = adj.unit.app AS (f r) := hS
      _ = _ := ConcreteCategory.congr_hom (adj.unit.naturality g) r
  change UR.map a ≫ dS.hom = dR.hom ≫ K.map g
  exact (dR.hom_inv_id_assoc (UR.map a ≫ dS.hom)).symm.trans
    (congrArg (fun z : K.obj AR ⟶ K.obj AS => dR.hom ≫ z) hi)

/-- The coefficient map agrees with the original map of constant abelian
sheaves under the existing coefficient-forgetting comparisons. -/
theorem etaleCohomologyCoefficientMap_forget (n : ℕ)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) n) :
    etaleConstantCohomologyForgetEquiv S (X := X) (ModuleCat.of S S) n
        (etaleCohomologyCoefficientMap X f n x) =
      Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom f.toAddMonoidHom)) n
        (etaleConstantCohomologyForgetEquiv R (X := X) (ModuleCat.of R R) n x) := by
  let CR := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let CS := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)
  let UR := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let US := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := S)
  let a : CR ⟶ (etaleRestrictCoefficients X f).obj CS := etaleConstantCoefficientHom X f
  let b : UR.obj CR ⟶ US.obj CS := UR.map a
  let dR := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
  let dS := (etaleConstantModuleForgetIso X S).app (ModuleCat.of S S)
  let g := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
    (AddCommGrpCat.ofHom f.toAddMonoidHom)
  change Sheaf.H.{u} (UR.obj CR) n at x
  change Sheaf.H.map dS.hom n (Sheaf.H.map b n x) =
    Sheaf.H.map g n (Sheaf.H.map dR.hom n x)
  have h : b ≫ dS.hom = dR.hom ≫ g := constantCoefficientHom_forget X f
  exact (Sheaf.H.map_comp_apply b dS.hom x).symm.trans
    ((congrArg (fun z : UR.obj CR ⟶
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of S)) =>
        Sheaf.H.map z n x) h).trans (Sheaf.H.map_comp_apply dR.hom g x))

private theorem coefficientMap_ext (n : ℕ)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) n) :
    (((etaleConstantModuleExtCohomologyEquiv X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        n).symm x).comp (Ext.mk₀ (etaleConstantCoefficientHom X f)) (add_zero n)) =
      (Ext.mk₀ (etaleConstantCoefficientHom X f)).comp
        (((etaleConstantModuleExtCohomologyEquiv X S
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S))
            n).symm (etaleCohomologyCoefficientMap X f n x)).mapExactFunctor
              (etaleRestrictCoefficients X f)) (zero_add n) := by
  let CR := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let CS := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)
  let eR := etaleConstantModuleExtCohomologyEquiv X R CR n
  let eS := etaleConstantModuleExtCohomologyEquiv X S CS n
  let eRS := etaleConstantModuleExtCohomologyEquiv X R
    ((etaleRestrictCoefficients X f).obj CS) n
  let a := etaleConstantCoefficientHom X f
  let y := etaleCohomologyCoefficientMap X f n x
  have hl : eRS ((eR.symm x).comp (Ext.mk₀ a) (add_zero n)) = y :=
    (etaleConstantModuleExtCohomologyEquiv_naturality X R a n (eR.symm x)).trans
      (congrArg (Classical.cohomologyMap a n) (eR.apply_symm_apply x))
  have hr : eRS ((Ext.mk₀ a).comp
      ((eS.symm y).mapExactFunctor (etaleRestrictCoefficients X f)) (zero_add n)) = y :=
    (etaleConstantModuleExtCohomologyEquiv_restrictCoefficients X f CS n (eS.symm y)).trans
      (eS.apply_symm_apply y)
  exact eRS.injective (hl.trans hr.symm)

/-- Every actual coefficient ring map preserves the native Yoneda cup
product. No flatness of the coefficient ring map is required. -/
theorem etaleCohomologyCup_coefficientMap
    (a b c : ℕ) (h : a + b = c)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) a)
    (y : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) b) :
    etaleCohomologyCoefficientMap X f c
        (etaleCohomologyCup X R
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
            a b c h x y) =
      etaleCohomologyCup X S
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S))
          a b c h (etaleCohomologyCoefficientMap X f a x)
            (etaleCohomologyCoefficientMap X f b y) := by
  let CR := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let CS := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)
  let L := etaleRestrictCoefficients X f
  let v := etaleConstantCoefficientHom X f
  let α := (etaleConstantModuleExtCohomologyEquiv X R CR a).symm x
  let β := (etaleConstantModuleExtCohomologyEquiv X R CR b).symm y
  let α' := (etaleConstantModuleExtCohomologyEquiv X S CS a).symm
    (etaleCohomologyCoefficientMap X f a x)
  let β' := (etaleConstantModuleExtCohomologyEquiv X S CS b).symm
    (etaleCohomologyCoefficientMap X f b y)
  let US := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := S)
  let eRS : Ext.{u} CR (L.obj CS) c → Sheaf.H.{u} (US.obj CS) c :=
    etaleConstantModuleExtCohomologyEquiv X R (L.obj CS) c
  have hα : α.comp (Ext.mk₀ v) (add_zero a) =
      (Ext.mk₀ v).comp (α'.mapExactFunctor L) (zero_add a) := coefficientMap_ext X f a x
  have hβ : β.comp (Ext.mk₀ v) (add_zero b) =
      (Ext.mk₀ v).comp (β'.mapExactFunctor L) (zero_add b) := coefficientMap_ext X f b y
  have hc : (α.comp β h).comp (Ext.mk₀ v) (add_zero c) =
      (Ext.mk₀ v).comp ((α'.comp β' h).mapExactFunctor L) (zero_add c) := by
    calc
      _ = α.comp (β.comp (Ext.mk₀ v) (add_zero b)) h :=
        Ext.comp_assoc_of_third_deg_zero α β (Ext.mk₀ v) h
      _ = α.comp ((Ext.mk₀ v).comp (β'.mapExactFunctor L) (zero_add b)) h :=
        congrArg (fun z : Ext.{u} CR (L.obj CS) b => α.comp z h) hβ
      _ = (α.comp (Ext.mk₀ v) (add_zero a)).comp (β'.mapExactFunctor L) h :=
        (Ext.comp_assoc_of_second_deg_zero α (Ext.mk₀ v) (β'.mapExactFunctor L) h).symm
      _ = ((Ext.mk₀ v).comp (α'.mapExactFunctor L) (zero_add a)).comp
          (β'.mapExactFunctor L) h :=
        congrArg (fun z : Ext.{u} CR (L.obj CS) a => z.comp (β'.mapExactFunctor L) h) hα
      _ = (Ext.mk₀ v).comp
          ((α'.mapExactFunctor L).comp (β'.mapExactFunctor L) h) (zero_add c) :=
        Ext.comp_assoc (Ext.mk₀ v) (α'.mapExactFunctor L) (β'.mapExactFunctor L)
          (zero_add a) h (by simpa only [zero_add] using h)
      _ = _ := congrArg (fun z : Ext.{u} (L.obj CS) (L.obj CS) c =>
        (Ext.mk₀ v).comp z (zero_add c)) (Ext.mapExactFunctor_comp L α' β' h).symm
  have hl : (etaleCohomologyCoefficientMap X f c
      (etaleCohomologyCup X R CR a b c h x y) : Sheaf.H.{u} (US.obj CS) c) =
        eRS ((α.comp β h).comp (Ext.mk₀ v) (add_zero c)) :=
    (etaleConstantModuleExtCohomologyEquiv_naturality X R v c (α.comp β h)).symm
  have hm : eRS ((α.comp β h).comp (Ext.mk₀ v) (add_zero c)) =
      eRS ((Ext.mk₀ v).comp ((α'.comp β' h).mapExactFunctor L) (zero_add c)) :=
    congrArg eRS hc
  have hr : eRS ((Ext.mk₀ v).comp ((α'.comp β' h).mapExactFunctor L) (zero_add c)) =
      (etaleCohomologyCup X S CS a b c h
        (etaleCohomologyCoefficientMap X f a x)
        (etaleCohomologyCoefficientMap X f b y) : Sheaf.H.{u} (US.obj CS) c) :=
    etaleConstantModuleExtCohomologyEquiv_restrictCoefficients X f CS c (α'.comp β' h)
  exact hl.trans (hm.trans hr)

/-- The actual coefficient map preserves the degree-zero cup unit. -/
theorem etaleCohomologyCoefficientMap_unit :
    etaleCohomologyCoefficientMap X f 0 (etaleCohomologyCupUnit X R) =
      etaleCohomologyCupUnit X S := by
  let CR := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let CS := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)
  let L := etaleRestrictCoefficients X f
  let US := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := S)
  let v : CR ⟶ L.obj CS := etaleConstantCoefficientHom X f
  let eRS : Ext.{u} CR (L.obj CS) 0 → Sheaf.H.{u} (US.obj CS) 0 :=
    etaleConstantModuleExtCohomologyEquiv X R (L.obj CS) 0
  have hn : eRS ((Ext.mk₀ (𝟙 CR)).comp (Ext.mk₀ v) (add_zero 0)) =
      (etaleCohomologyCoefficientMap X f 0 (etaleCohomologyCupUnit X R) :
        Sheaf.H.{u} (US.obj CS) 0) :=
    etaleConstantModuleExtCohomologyEquiv_naturality X R v 0 (Ext.mk₀ (𝟙 CR))
  have hs : eRS ((Ext.mk₀ v).comp
      ((Ext.mk₀ (𝟙 CS)).mapExactFunctor L) (zero_add 0)) =
        (etaleCohomologyCupUnit X S : Sheaf.H.{u} (US.obj CS) 0) :=
    etaleConstantModuleExtCohomologyEquiv_restrictCoefficients X f CS 0 (Ext.mk₀ (𝟙 CS))
  have hmapid : (Ext.mk₀ (𝟙 CS) : Ext.{u} CS CS 0).mapExactFunctor L =
      (Ext.mk₀ (𝟙 (L.obj CS)) : Ext.{u} (L.obj CS) (L.obj CS) 0) :=
    (Ext.mapExactFunctor_mk₀ L (𝟙 CS)).trans
      (congrArg (fun k : L.obj CS ⟶ L.obj CS => Ext.mk₀ k) (L.map_id CS))
  have hleft : (Ext.mk₀ (𝟙 CR)).comp (Ext.mk₀ v) (add_zero 0) = Ext.mk₀ v :=
    Ext.mk₀_id_comp (Ext.mk₀ v)
  have hright : (Ext.mk₀ v).comp
      ((Ext.mk₀ (𝟙 CS)).mapExactFunctor L) (zero_add 0) = Ext.mk₀ v :=
    (congrArg (fun z : Ext.{u} (L.obj CS) (L.obj CS) 0 =>
      (Ext.mk₀ v).comp z (zero_add 0)) hmapid).trans (Ext.comp_mk₀_id (Ext.mk₀ v))
  exact ((congrArg eRS hleft).symm.trans hn).symm.trans
    ((congrArg eRS hright).symm.trans hs)

end EtaleCohomology
