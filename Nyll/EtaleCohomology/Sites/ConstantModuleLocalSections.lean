/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ConstantRepresentable
public import Nyll.EtaleCohomology.Sites.ModuleSetComparison
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Actual local scalar representatives on the original étale site

The original constant set sheaf is represented by the actual disjoint
union of copies of the base scheme. Pulling back its actual component
cover proves local surjectivity of the original constant-presheaf unit.
The original module-to-set comparison carries that unit to the same
unit, so the result holds for original constant module sheaves as well.

This argument uses the original coefficient universe on the large
small-étale category. It supplies actual local representatives and does
not impose connectedness on an overlap or enlarge the coefficient type.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable (X : Scheme.{u})

private theorem copies_constant_section (A : Type u) (V : X.Etale) (a : A) :
    (etaleCopiesSheafIso X A).inv.hom.app (op V)
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op V) a) =
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X).from V ≫ etaleCopiesInj X A a := by
  let hT : IsTerminal (etaleBaseObject X) := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let e : X.smallEtaleTopology.yoneda.obj (etaleCopies X A) ≅
      (constantSheaf X.smallEtaleTopology (Type u)).obj A := etaleCopiesSheafIso X A
  let η : (Functor.const X.Etaleᵒᵖ).obj A ⟶
      ((constantSheaf X.smallEtaleTopology (Type u)).obj A).obj :=
    toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)
  let g : V ⟶ etaleBaseObject X := hT.from V
  have hb : e.inv.hom.app (op (etaleBaseObject X))
      (η.app (op (etaleBaseObject X)) a) = etaleCopiesInj X A a := by
    have h := etaleCopiesSheafIso_inv_unit X A a
    have hunit : (constantSheafAdj X.smallEtaleTopology (Type u) hT).unit.app A =
        η.app (op (etaleBaseObject X)) := by
      change ((constantPresheafAdj (Type u) hT).comp
        (sheafificationAdjunction X.smallEtaleTopology (Type u))).unit.app A = _
      rw [Adjunction.comp_unit_app]
      rfl
    exact (congrArg (e.inv.hom.app (op (etaleBaseObject X)))
      (ConcreteCategory.congr_hom hunit a)).symm.trans h
  have hη : η.app (op V) a =
      ((constantSheaf X.smallEtaleTopology (Type u)).obj A).obj.map g.op
        (η.app (op (etaleBaseObject X)) a) :=
    ConcreteCategory.congr_hom (η.naturality g.op) a
  have hn : e.inv.hom.app (op V)
      (((constantSheaf X.smallEtaleTopology (Type u)).obj A).obj.map g.op
        (η.app (op (etaleBaseObject X)) a)) =
      g ≫ e.inv.hom.app (op (etaleBaseObject X))
        (η.app (op (etaleBaseObject X)) a) :=
    ConcreteCategory.congr_hom (e.inv.hom.naturality g.op)
      (η.app (op (etaleBaseObject X)) a)
  exact (congrArg (e.inv.hom.app (op V)) hη).trans
    (hn.trans (congrArg (fun k : etaleBaseObject X ⟶ etaleCopies X A => g ≫ k) hb))

/-- Every original constant set-sheaf section is locally the image
of an actual coefficient, through the original sheafification unit. -/
theorem etaleConstantSet_toSheafify_isLocallySurjective (A : Type u) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)) := by
  constructor
  intro V s
  let C := (constantSheaf X.smallEtaleTopology (Type u)).obj A
  let e : X.smallEtaleTopology.yoneda.obj (etaleCopies X A) ≅
      (constantSheaf X.smallEtaleTopology (Type u)).obj A := etaleCopiesSheafIso X A
  let p : V ⟶ etaleCopies X A := e.inv.hom.app (op V) s
  let hT : IsTerminal (etaleBaseObject X) := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  have hc : Sieve.ofArrows (fun _ : A => etaleBaseObject X) (etaleCopiesInj X A) ∈
      X.smallEtaleTopology (etaleCopies X A) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.ext
    intro x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨a, y, hy⟩ := (sigmaOpenCover (fun _ : A => X)).exists_eq x
      exact Set.mem_iUnion.mpr ⟨a, y, hy⟩
  apply X.smallEtaleTopology.superset_covering ?_
    (X.smallEtaleTopology.pullback_stable p hc)
  intro W k hk
  obtain ⟨a, t, ht⟩ := Sieve.ofArrows.exists hk
  refine ⟨a, ?_⟩
  have he : Function.Injective (e.inv.hom.app (op W)) :=
    ((CategoryTheory.isIso_iff_bijective (e.inv.hom.app (op W))).mp inferInstance).1
  apply he
  have hn : e.inv.hom.app (op W) (C.obj.map k.op s) = k ≫ p :=
    ConcreteCategory.congr_hom (e.inv.hom.naturality k.op) s
  have hconst : e.inv.hom.app (op W)
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op W) a) =
      hT.from W ≫ etaleCopiesInj X A a := copies_constant_section X A W a
  have hfrom : hT.from W = t := hT.hom_ext _ _
  exact hconst.trans
    ((congrArg (fun r : W ⟶ etaleBaseObject X => r ≫ etaleCopiesInj X A a) hfrom).trans
      (ht.symm.trans hn.symm))

variable (R : Type u) [CommRing R]

/-- The original module-to-set comparison retains the literal
constant-presheaf section at every original site object. -/
theorem etaleConstantModuleUnderlyingIso_toSheafify
    (M : ModuleCat.{u} R) (V : X.Etale) (m : M) :
    ((etaleConstantModuleUnderlyingIso X R).hom.app M).hom.app (op V)
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app (op V) m) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj ((forget (ModuleCat.{u} R)).obj M))).app (op V) m := by
  let U := forget (ModuleCat.{u} R)
  have : X.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)
      (Type u) U
  let P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R := (Functor.const X.Etaleᵒᵖ).obj M
  let Q : X.Etaleᵒᵖ ⥤ Type u := (Functor.const X.Etaleᵒᵖ).obj (U.obj M)
  let c : P ⋙ U ≅ Q := Functor.constComp X.Etaleᵒᵖ M U
  let a : sheafify X.smallEtaleTopology (P ⋙ U) ≅
      sheafify X.smallEtaleTopology P ⋙ U :=
    sheafifyComposeIso X.smallEtaleTopology U P
  have hc : ((constantCommuteCompose X.smallEtaleTopology U).hom.app M).hom =
      a.inv ≫ sheafifyMap X.smallEtaleTopology c.hom :=
    constantCommuteCompose_hom_app_hom X.smallEtaleTopology U M
  have hunit : Functor.whiskerRight (toSheafify X.smallEtaleTopology P) U ≫ a.inv =
      toSheafify X.smallEtaleTopology (P ⋙ U) :=
    CategoryTheory.sheafComposeIso_inv_fac X.smallEtaleTopology U P
  have hnat : toSheafify X.smallEtaleTopology (P ⋙ U) ≫
      sheafifyMap X.smallEtaleTopology c.hom =
      c.hom ≫ toSheafify X.smallEtaleTopology Q :=
    (toSheafify_naturality X.smallEtaleTopology c.hom).symm
  have h1 := congrArg
    (fun k : sheafify X.smallEtaleTopology P ⋙ U ⟶ sheafify X.smallEtaleTopology Q =>
      Functor.whiskerRight (toSheafify X.smallEtaleTopology P) U ≫ k) hc
  have h2 : Functor.whiskerRight (toSheafify X.smallEtaleTopology P) U ≫
      (a.inv ≫ sheafifyMap X.smallEtaleTopology c.hom) =
      c.hom ≫ toSheafify X.smallEtaleTopology Q :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg
        (fun k : P ⋙ U ⟶ sheafify X.smallEtaleTopology (P ⋙ U) =>
          k ≫ sheafifyMap X.smallEtaleTopology c.hom) hunit).trans hnat)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h1.trans h2) (op V)) m

/-- The original constant module-presheaf unit is locally surjective
in the original universe, with actual coefficients as local preimages. -/
theorem etaleConstantModule_toSheafify_isLocallySurjective (M : ModuleCat.{u} R) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) := by
  let U := forget (ModuleCat.{u} R)
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M
  let C' := (constantSheaf X.smallEtaleTopology (Type u)).obj (U.obj M)
  let e := (etaleConstantModuleUnderlyingIso X R).app M
  let η := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj (U.obj M))
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology η :=
    etaleConstantSet_toSheafify_isLocallySurjective X (U.obj M)
  constructor
  intro V s
  apply X.smallEtaleTopology.superset_covering ?_
    (Presheaf.imageSieve_mem X.smallEtaleTopology η (e.hom.hom.app (op V) s))
  intro W k hk
  obtain ⟨m, hm⟩ := hk
  refine ⟨m, ?_⟩
  have he : Function.Injective (e.hom.hom.app (op W)) :=
    ((CategoryTheory.isIso_iff_bijective (e.hom.hom.app (op W))).mp inferInstance).1
  apply he
  have hn : e.hom.hom.app (op W) (C.obj.map k.op s) =
      C'.obj.map k.op (e.hom.hom.app (op V) s) :=
    ConcreteCategory.congr_hom (e.hom.hom.naturality k.op) s
  exact (etaleConstantModuleUnderlyingIso_toSheafify X R M W m).trans (hm.trans hn.symm)

end EtaleCohomology
