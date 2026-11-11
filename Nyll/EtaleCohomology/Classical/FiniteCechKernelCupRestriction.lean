/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupCechKernelProduct
public import Nyll.EtaleCohomology.Classical.CupCoefficientSource
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionCohomologyComparison
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionNaturality
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerRestriction
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The actual overlap value of a finite covering-kernel cup

If a finite scalar kernel map has value `r` on an actual overlap,
the cup kernel class restricts to `r` times the original degree-one
class on that overlap. The calculation keeps the original integer
source and both original coefficient comparisons. Passing through
actual étale restriction gives the original finite scheme pullback.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian Opposite

namespace EtaleCohomology.Classical

variable (X : Scheme.{u}) (ℓ n : ℕ)

local notation "R" => ULift (ZMod (ℓ ^ (n + 1)))
local notation "𝓡" =>
  CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R)) (ModuleCat.of R R)
local notation "A" => CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology AddCommGrpCat)
  (ellPowerCoefficients ℓ n)
local notation "δ" => CategoryTheory.Iso.app (etaleConstantModuleForgetIso X R) (ModuleCat.of R R)

/-- The original local-site comparison, followed by the original
constant-coefficient comparison, on finite cohomology presheaves. -/
def finiteLevelCohomologyPresheafRestriction (W : X.Etale) (i : ℕ) :
    Sheaf.H'.{u} A i W →+ finiteLevelCohomology W.left ℓ n i :=
  (Sheaf.H.map
    (((etaleAbelianPullbackRestrictionIso W.hom).app A).inv ≫
      ((etaleAbelianPullbackConstantIso W.hom).app (ellPowerCoefficients ℓ n)).hom) i).comp
    (etaleCohomologyPresheafRestrictionEquiv W A i).toAddMonoidHom

/-- Passing to native finite cohomology on the same étale object
detects the original objectwise class. Both comparisons are isomorphisms. -/
theorem finiteLevelCohomologyPresheafRestriction_injective (W : X.Etale) (i : ℕ) :
    Function.Injective (finiteLevelCohomologyPresheafRestriction X ℓ n W i) := by
  let e := ((etaleAbelianPullbackRestrictionIso W.hom).app A).symm ≪≫
    (etaleAbelianPullbackConstantIso W.hom).app (ellPowerCoefficients ℓ n)
  let eH := ((Sheaf.functorH W.left.smallEtaleTopology i).mapIso e).addCommGroupIsoToAddEquiv
  exact eH.injective.comp
    (etaleCohomologyPresheafRestrictionEquiv W A i).injective

/-- Original terminal restriction of a finite class is the original
finite scheme pullback, with its original constant coefficients. -/
theorem finiteLevelCohomologyPresheafRestriction_terminal [Fact ℓ.Prime]
    {T : X.Etale} (hT : IsTerminal T) (W : X.Etale) (q : W ⟶ T)
    (i : ℕ) (x : finiteLevelCohomology X ℓ n i) :
    finiteLevelCohomologyPresheafRestriction X ℓ n W i
        ((Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT q)).comp
          x (zero_add i)) =
      finiteLevelCohomologyPullback ℓ W.hom n i x := by
  have hres : etaleCohomologyPresheafRestrictionEquiv W A i
      ((Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT q)).comp
        x (zero_add i)) = etaleAbelianRestrictionCohomologyPullback W.hom A i x := by
    have hsource :
        (Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT q)).comp
            x (zero_add i) =
          ((A).cohomologyPresheaf i).map q.op
            (sheafCohomologyTerminalEquiv X.smallEtaleTopology hT A i x) :=
      (Ext.mk₀_comp_mk₀_assoc ((freeAbelianSheafYoneda X.smallEtaleTopology).map q)
        (freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology hT).hom x).symm
    exact (congrArg (etaleCohomologyPresheafRestrictionEquiv W A i) hsource).trans
      (etaleCohomologyPresheafRestrictionEquiv_terminal_restriction W hT q A i x)
  let e := (etaleAbelianPullbackRestrictionIso W.hom).app A
  let c := (etaleAbelianPullbackConstantIso W.hom).app (ellPowerCoefficients ℓ n)
  change Sheaf.H.map (e.inv ≫ c.hom) i
      (etaleCohomologyPresheafRestrictionEquiv W A i
        ((Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT q)).comp x
          (zero_add i))) = _
  rw [hres, finiteLevelCohomologyPullback_apply]
  change Sheaf.H.map (e.inv ≫ c.hom) i
      (Sheaf.H.map e.hom i (etaleAbelianCohomologyPullbackMap W.hom A i x)) =
    Sheaf.H.map c.hom i (etaleAbelianCohomologyPullbackMap W.hom A i x)
  rw [← Sheaf.H.map_comp_apply, ← Category.assoc, e.hom_inv_id, Category.id_comp]

variable {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)

local notation "K₁" => kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f)

/-- An actual scalar value of the covering-kernel map gives the
same multiple of the original class on the original overlap source. -/
theorem finiteCechKernelCupClass_overlap
    (W : X.Etale) (q : W ⟶ T)
    (m : (freeAbelianSheafYoneda X.smallEtaleTopology).obj W ⟶ K₁)
    (k : K₁ ⟶ A) (r : ℕ)
    (hmk : m ≫ k = r • (abelianCechUnitAugmentation X.smallEtaleTopology hT q ≫
      etaleConstantIntegerHom X R ≫ (δ).hom))
    (x : finiteLevelCohomology X ℓ n 1) :
    (Ext.mk₀ m).comp (finiteCechKernelCupClass X ℓ n hT f k x) (zero_add 1) =
      r • (Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT q)).comp
        x (zero_add 1) := by
  let u := abelianCechUnitAugmentation X.smallEtaleTopology hT q
  let xR := (finiteLevelConstantModuleEquiv X ℓ n 1).symm x
  let xM := (etaleConstantModuleExtCohomologyEquiv X R 𝓡 1).symm xR
  let forgetR : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    forgetCoefficients.{u + 1, u, u, u}
  let xF := xM.mapExactFunctor forgetR
  let z := xF.comp (Ext.mk₀ (δ).hom) (add_zero 1)
  let Φ : ((freeAbelianSheafYoneda X.smallEtaleTopology).obj W ⟶ (forgetR).obj 𝓡) →+
      Ext.{u} ((freeAbelianSheafYoneda X.smallEtaleTopology).obj W) A 1 :=
    (z.postcomp _ (zero_add 1)).comp Ext.addEquiv₀.symm.toAddMonoidHom
  have hx : ((Ext.mk₀ (etaleConstantIntegerHom X R)).comp xF (zero_add 1)).comp
      (Ext.mk₀ (δ).hom) (add_zero 1) = x := by
    rw [← etaleConstantModuleExtCohomologyEquiv_forget]
    change finiteLevelConstantModuleEquiv X ℓ n 1
      ((etaleConstantModuleExtCohomologyEquiv X R 𝓡 1)
        ((etaleConstantModuleExtCohomologyEquiv X R 𝓡 1).symm
          ((finiteLevelConstantModuleEquiv X ℓ n 1).symm x))) = x
    rw [LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hΦ : Φ (u ≫ etaleConstantIntegerHom X R) = (Ext.mk₀ u).comp x (zero_add 1) := by
    change (Ext.mk₀ (u ≫ etaleConstantIntegerHom X R)).comp
      (xF.comp (Ext.mk₀ (δ).hom) (add_zero 1)) (zero_add 1) = _
    rw [← Ext.mk₀_comp_mk₀_assoc, ← Ext.comp_assoc_of_third_deg_zero, hx]
  change (Ext.mk₀ m).comp
    (((Ext.mk₀ (k ≫ (δ).inv)).comp xF (zero_add 1)).comp
      (Ext.mk₀ (δ).hom) (add_zero 1)) (zero_add 1) = _
  rw [← Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Ext.comp_assoc_of_third_deg_zero]
  change Φ (m ≫ (k ≫ (δ).inv)) = r • (Ext.mk₀ u).comp x (zero_add 1)
  rw [← Category.assoc, hmk]
  simp only [Preadditive.nsmul_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (map_nsmul Φ r (u ≫ etaleConstantIntegerHom X R)).trans
    (congrArg (fun a => r • a) hΦ)

/-- On the actual étale overlap, the kernel cup is the scalar value
times the original finite scheme pullback of its degree-one factor. -/
theorem finiteCechKernelCupClass_restriction [Fact ℓ.Prime]
    (W : X.Etale) (q : W ⟶ T)
    (m : (freeAbelianSheafYoneda X.smallEtaleTopology).obj W ⟶ K₁)
    (k : K₁ ⟶ A) (r : ℕ)
    (hmk : m ≫ k = r • (abelianCechUnitAugmentation X.smallEtaleTopology hT q ≫
      etaleConstantIntegerHom X R ≫ (δ).hom))
    (x : finiteLevelCohomology X ℓ n 1) :
    finiteLevelCohomologyPresheafRestriction X ℓ n W 1
        ((Ext.mk₀ m).comp (finiteCechKernelCupClass X ℓ n hT f k x) (zero_add 1)) =
      r • finiteLevelCohomologyPullback ℓ W.hom n 1 x := by
  let res := finiteLevelCohomologyPresheafRestriction X ℓ n W 1
  let a := (Ext.mk₀ (abelianCechUnitAugmentation X.smallEtaleTopology hT q)).comp
    x (zero_add 1)
  exact (congrArg res
    (finiteCechKernelCupClass_overlap X ℓ n hT f W q m k r hmk x)).trans
    ((map_nsmul res r a).trans
      (congrArg (fun y : finiteLevelCohomology W.left ℓ n 1 => r • y)
        (finiteLevelCohomologyPresheafRestriction_terminal X ℓ n hT W q 1 x)))

/-- The original coherent finite coordinates commute with actual
local Kummer restriction. Thus the root overlap and the finite cup
overlap can be compared in the same native coefficient group. -/
theorem finiteLevelCohomologyPresheafRestriction_kummer
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : X ⟶ Spec (.of K)) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    (W : X.Etale) (i : ℕ) (a : Sheaf.H'.{u} A i W) :
    finiteLevelKummerCohomologyEquiv (W.hom ≫ c) ℓ hℓ n i
        (finiteLevelCohomologyPresheafRestriction X ℓ n W i a) =
      etaleRootsOfUnityCohomologyPresheafRestriction (ℓ ^ (n + 1)) W i
        (((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology i).map
          (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom).app (op W) a) := by
  let N := ℓ ^ (n + 1)
  let eX := ellPowerConstantKummerKernelIso c ℓ hℓ n
  let eW := ellPowerConstantKummerKernelIso (W.hom ≫ c) ℓ hℓ n
  let L := etaleAbelianPullback W.hom
  let Q := etaleRestriction W.hom AddCommGrpCat.{u}
  let I := etaleAbelianPullbackRestrictionIso W.hom
  let j := (I.app A).inv ≫
    ((etaleAbelianPullbackConstantIso W.hom).app (ellPowerCoefficients ℓ n)).hom
  have hp : L.map eX.hom ≫ etaleRootsOfUnityPullback W.hom N =
      ((etaleAbelianPullbackConstantIso W.hom).app (ellPowerCoefficients ℓ n)).hom ≫
        eW.hom := by
    let α : ellPowerCoefficients.{u} ℓ n ⟶
        AddCommGrpCat.of (Additive (rootsOfUnity N K)) :=
      (EtaleFundamentalGroups.Cohomology.ellPowerRootsCoefficientEquiv
        K ℓ hℓ n).toAddCommGrpIso.hom
    let CX := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
    let CW := constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{u}
    have hn : 0 < N := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
    have hnK : IsUnit (N : K) := by
      simpa only [N, Nat.cast_pow] using hℓ.pow (n + 1)
    change L.map (CX.map α ≫ constantRootsOfUnityToKummerKernel c N) ≫
        etaleRootsOfUnityPullback W.hom N =
      ((etaleAbelianPullbackConstantIso W.hom).app (ellPowerCoefficients ℓ n)).hom ≫
        (CW.map α ≫ constantRootsOfUnityToKummerKernel (W.hom ≫ c) N)
    have hα :
        L.map (CX.map α) ≫
            ((etaleAbelianPullbackConstantIso W.hom).app
              (AddCommGrpCat.of (Additive (rootsOfUnity N K)))).hom =
          ((etaleAbelianPullbackConstantIso W.hom).app (ellPowerCoefficients ℓ n)).hom ≫
            CW.map α :=
      (etaleAbelianPullbackConstantIso W.hom).hom.naturality α
    rw [Functor.map_comp, Category.assoc,
      constantRootsOfUnityToKummerKernel_pullback W.hom c hn hnK,
      ← Category.assoc]
    exact (congrArg
      (fun t => t ≫ constantRootsOfUnityToKummerKernel (W.hom ≫ c) N) hα).trans
        (Category.assoc _ _ _)
  have hrestriction : Q.map eX.hom ≫ etaleRootsOfUnityRestriction W.hom N =
      j ≫ eW.hom := by
    change Q.map eX.hom ≫ (I.inv.app _ ≫ etaleRootsOfUnityPullback W.hom N) = _
    calc
      _ = I.inv.app A ≫ (L.map eX.hom ≫ etaleRootsOfUnityPullback W.hom N) := by
        rw [← Category.assoc, I.inv.naturality eX.hom, Category.assoc]
      _ = I.inv.app A ≫
          (((etaleAbelianPullbackConstantIso W.hom).app (ellPowerCoefficients ℓ n)).hom ≫
            eW.hom) := congrArg (I.inv.app A ≫ ·) hp
      _ = j ≫ eW.hom := (Category.assoc _ _ _).symm
  change Sheaf.H.map eW.hom i
      (Sheaf.H.map j i (etaleCohomologyPresheafRestrictionEquiv W A i a)) =
    Sheaf.H.map (etaleRootsOfUnityRestriction W.hom N) i
      (etaleCohomologyPresheafRestrictionEquiv W (etaleRootsOfUnitySheaf X N) i
        (((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology i).map eX.hom).app
          (op W) a))
  rw [etaleCohomologyPresheafRestrictionEquiv_naturality,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun t => Sheaf.H.map t i
    (etaleCohomologyPresheafRestrictionEquiv W A i a)) hrestriction.symm

/-- Restriction along an actual morphism of étale objects is the
original finite pullback on their schemes. The original coherent
Kummer coordinates retain this identity in every degree. -/
theorem finiteLevelCohomologyPresheafRestriction_object_restriction
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : X ⟶ Spec (.of K)) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    {V W : X.Etale} (g : W ⟶ V) (i : ℕ) (a : Sheaf.H'.{u} A i V) :
    finiteLevelCohomologyPresheafRestriction X ℓ n W i
        (((A).cohomologyPresheaf i).map g.op a) =
      finiteLevelCohomologyPullback ℓ g.left n i
        (finiteLevelCohomologyPresheafRestriction X ℓ n V i a) := by
  have hc : g.left ≫ (V.hom ≫ c) = W.hom ≫ c :=
    (Category.assoc g.left V.hom c).symm.trans
      (congrArg (fun t => t ≫ c) g.w)
  let e := ellPowerConstantKummerKernelIso c ℓ hℓ n
  let η := (Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology i).map e.hom
  have hη : η.app (op W) (((A).cohomologyPresheaf i).map g.op a) =
      ((etaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).cohomologyPresheaf i).map g.op
        (η.app (op V) a) :=
    ConcreteCategory.congr_hom (η.naturality g.op) a
  have hp := finiteLevelKummerCohomologyEquiv_pullback g.left (V.hom ≫ c)
    ℓ hℓ n i (finiteLevelCohomologyPresheafRestriction X ℓ n V i a)
  rw [hc] at hp
  apply (finiteLevelKummerCohomologyEquiv (W.hom ≫ c) ℓ hℓ n i).injective
  rw [finiteLevelCohomologyPresheafRestriction_kummer, hp,
    finiteLevelCohomologyPresheafRestriction_kummer]
  change etaleRootsOfUnityCohomologyPresheafRestriction (ℓ ^ (n + 1)) W i
      (η.app (op W) (((A).cohomologyPresheaf i).map g.op a)) = _
  rw [hη]
  exact etaleRootsOfUnityCohomologyPresheafRestriction_object_restriction
    (ℓ ^ (n + 1)) g i (η.app (op V) a)

end EtaleCohomology.Classical
