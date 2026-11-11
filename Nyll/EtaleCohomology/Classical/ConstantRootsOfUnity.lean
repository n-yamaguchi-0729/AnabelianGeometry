/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
public import Nyll.SchemeTheory.Modules.Functoriality.AffinePullbackSections
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Constant roots of unity and the actual Kummer kernel

Over a field containing a primitive root of the given invertible order,
roots of unity are locally constant on every scheme. The map from the constant sheaf is induced
by the original structural map on units and lands in the kernel of the
original power map. Its local bijectivity follows from simple-root uniqueness
in the ordinary local rings, followed by equality of germs on an open
neighborhood. No reducedness, connectedness or Henselian hypothesis is needed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The structural homomorphism from the ground field to global sections. -/
def rootScalarSections (c : X ⟶ Spec (.of K)) : K →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop).hom

private theorem rootScalarSections_comp {Y : Scheme.{u}}
    (c : X ⟶ Spec (.of K)) (f : Y ⟶ X) :
    rootScalarSections (f ≫ c) = f.appTop.hom.comp (rootScalarSections c) := by
  unfold rootScalarSections
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- The additive coefficient group of roots of unity. -/
abbrev rootCoefficients (K : Type u) [Field K] (n : ℕ) : AddCommGrpCat.{u} :=
  .of (Additive (rootsOfUnity n K))

/-- The structural unit map on the constant roots-of-unity presheaf. -/
def constantRootsToUnitsPresheaf (c : X ⟶ Spec (.of K)) (n : ℕ) :
    (Functor.const X.Etaleᵒᵖ).obj (rootCoefficients K n) ⟶
      (etaleMultiplicativeGroupSheaf X).obj where
  app V := AddCommGrpCat.ofHom
    (((Units.map (rootScalarSections (V.unop.hom ≫ c)).toMonoidHom).comp
      (rootsOfUnity n K).subtype).toAdditive)
  naturality {V W} f := by
    apply ConcreteCategory.hom_ext
    refine fun (ζ : Additive (rootsOfUnity n K)) => ?_
    apply Additive.toMul.injective
    apply Units.ext
    change rootScalarSections (W.unop.hom ≫ c) ((ζ.toMul : Kˣ) : K) =
      f.unop.left.appTop (rootScalarSections (V.unop.hom ≫ c)
        ((ζ.toMul : Kˣ) : K))
    have hc : W.unop.hom ≫ c = f.unop.left ≫ (V.unop.hom ≫ c) :=
      (congrArg (fun a => a ≫ c) f.unop.w).symm.trans (Category.assoc _ _ _)
    rw [hc, rootScalarSections_comp]
    rfl

/-- The structural unit map from the constant roots-of-unity sheaf. -/
def constantRootsToUnits (c : X ⟶ Spec (.of K)) (n : ℕ) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (rootCoefficients K n) ⟶ etaleMultiplicativeGroupSheaf X :=
  ⟨sheafifyLift X.smallEtaleTopology (constantRootsToUnitsPresheaf c n)
    (etaleMultiplicativeGroupSheaf X).property⟩

private theorem constantRootsToUnits_fac (c : X ⟶ Spec (.of K)) (n : ℕ) :
    toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (rootCoefficients K n)) ≫
      (constantRootsToUnits c n).hom = constantRootsToUnitsPresheaf c n :=
  toSheafify_sheafifyLift _ _ _

private theorem constantRootsToUnits_power (c : X ⟶ Spec (.of K)) (n : ℕ) :
    constantRootsToUnits c n ≫ etaleMultiplicativeGroupPower X n = 0 := by
  let P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
    (Functor.const X.Etaleᵒᵖ).obj (rootCoefficients K n)
  let M := etaleMultiplicativeGroupSheaf X
  let p : M.obj ⟶ M.obj := (etaleMultiplicativeGroupPower X n).hom
  have hp : constantRootsToUnitsPresheaf c n ≫ p = 0 := by
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    refine fun (ζ : Additive (rootsOfUnity n K)) => ?_
    apply Additive.toMul.injective
    change Units.map (rootScalarSections (V.unop.hom ≫ c)).toMonoidHom
        (ζ.toMul : Kˣ) ^ n = 1
    rw [← map_pow, (mem_rootsOfUnity n (ζ.toMul : Kˣ)).mp ζ.toMul.property, map_one]
  have hfac : toSheafify X.smallEtaleTopology P ≫
      (constantRootsToUnits c n).hom = constantRootsToUnitsPresheaf c n :=
    constantRootsToUnits_fac c n
  apply Sheaf.hom_ext
  apply sheafify_hom_ext X.smallEtaleTopology _ _ M.property
  change toSheafify X.smallEtaleTopology P ≫
      ((constantRootsToUnits c n).hom ≫ p) = toSheafify X.smallEtaleTopology P ≫ 0
  exact (Category.assoc (toSheafify X.smallEtaleTopology P)
    (constantRootsToUnits c n).hom p).symm.trans
      ((congrArg (fun t : P ⟶ M.obj => t ≫ p) hfac).trans
        (hp.trans (comp_zero (f := toSheafify X.smallEtaleTopology P) (Z := M.obj)).symm))

/-- The original structural map on constant roots of unity, factored through
the kernel of the original n-th power morphism of the unit sheaf. -/
def constantRootsOfUnityToKummerKernel (c : X ⟶ Spec (.of K)) (n : ℕ) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (.of (Additive (rootsOfUnity n K))) ⟶ etaleRootsOfUnitySheaf X n :=
  kernel.lift (etaleMultiplicativeGroupPower X n) (constantRootsToUnits c n)
    (by exact constantRootsToUnits_power c n)

/-- The original constant roots presented in the Kummer kernel. -/
def constantRootsKernelPresentation (c : X ⟶ Spec (.of K)) (n : ℕ) :
    (Functor.const X.Etaleᵒᵖ).obj (rootCoefficients K n) ⟶
      (etaleRootsOfUnitySheaf X n).obj :=
  toSheafify X.smallEtaleTopology _ ≫ (constantRootsOfUnityToKummerKernel c n).hom

private theorem constantRootsKernelPresentation_ι (c : X ⟶ Spec (.of K)) (n : ℕ) :
    constantRootsKernelPresentation c n ≫
      (kernel.ι (etaleMultiplicativeGroupPower X n)).hom =
        constantRootsToUnitsPresheaf c n := by
  let P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
    (Functor.const X.Etaleᵒᵖ).obj (rootCoefficients K n)
  let C := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (rootCoefficients K n)
  let η : P ⟶ C.obj := toSheafify X.smallEtaleTopology P
  let k := kernel.ι (etaleMultiplicativeGroupPower X n)
  have h : (constantRootsOfUnityToKummerKernel c n).hom ≫ k.hom =
      (constantRootsToUnits c n).hom :=
    congrArg (fun t : C ⟶ etaleMultiplicativeGroupSheaf X => t.hom)
      (kernel.lift_ι (etaleMultiplicativeGroupPower X n) (constantRootsToUnits c n)
        (constantRootsToUnits_power c n))
  change (η ≫ (constantRootsOfUnityToKummerKernel c n).hom) ≫ k.hom = _
  exact (Category.assoc η (constantRootsOfUnityToKummerKernel c n).hom k.hom).trans
    ((congrArg (fun t : C.obj ⟶ (etaleMultiplicativeGroupSheaf X).obj => η ≫ t) h).trans
      (constantRootsToUnits_fac c n))

private theorem local_root_is_constant
    (R : Type u) [CommRing R] [IsLocalRing R] (ι : K →+* R)
    {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (hroot : ∃ ζ : K, IsPrimitiveRoot ζ n) (a : Rˣ) (ha : a ^ n = 1) :
    ∃ ζ : rootsOfUnity n K, (a : R) = ι ((ζ : Kˣ) : K) := by
  have : NeZero n := ⟨hn.ne'⟩
  let ρ := (IsLocalRing.residue R).comp ι
  let b : rootsOfUnity n (IsLocalRing.ResidueField R) :=
    ⟨Units.map (IsLocalRing.residue R).toMonoidHom a, by
      apply (mem_rootsOfUnity n _).mpr
      rw [← map_pow, ha, map_one]⟩
  obtain ⟨ζ, hζ⟩ :=
    (RamificationTheory.HilbertRamification.restrictRootsOfUnity_bijective_of_primitiveRoot
      ρ n hroot).surjective b
  refine ⟨ζ, ?_⟩
  have hres : IsLocalRing.residue R (a : R) =
      IsLocalRing.residue R (ι ((ζ : Kˣ) : K)) :=
    (congrArg (fun z : rootsOfUnity n (IsLocalRing.ResidueField R) =>
      ((z : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) hζ).symm
  have hdiff : ¬ IsUnit ((a : R) - ι ((ζ : Kˣ) : K)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hres, sub_self]
    exact not_not_intro rfl
  have haroot : (Polynomial.X ^ n - 1 : Polynomial R).eval (a : R) = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, ← Units.val_pow_eq_pow_val, ha, Units.val_one, sub_self]
  have hζroot : (Polynomial.X ^ n - 1 : Polynomial R).eval
      (ι ((ζ : Kˣ) : K)) = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, ← map_pow,
      (mem_rootsOfUnity' n (ζ : Kˣ)).mp ζ.property, map_one, sub_self]
  have hder : IsUnit (((Polynomial.X ^ n - 1 : Polynomial R).derivative).eval
      (a : R)) := by
    simpa only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_natCast, map_natCast] using
      (hnK.map ι).mul (a.isUnit.pow (n - 1))
  exact IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub haroot hζroot hdiff hder

open AlgebraicCurves.Geometry.Schemes.Proofs.AffineOpenBaseChange in
open AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange in
private theorem unit_root_is_locally_constant
    (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (hroot : ∃ ζ : K, IsPrimitiveRoot ζ n) (a : (Γ(X, ⊤) : Type u)ˣ) (ha : a ^ n = 1) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ ∃ ζ : rootsOfUnity n K,
      Units.map U.ι.appTop.hom.toMonoidHom a =
        Units.map (rootScalarSections (U.ι ≫ c)).toMonoidHom (ζ : Kˣ) := by
  let g : Γ(X, ⊤) →+* X.presheaf.stalk x := (X.presheaf.germ ⊤ x trivial).hom
  let ι : K →+* X.presheaf.stalk x := g.comp (rootScalarSections c)
  obtain ⟨ζ, hζ⟩ := local_root_is_constant (X.presheaf.stalk x) ι hn hnK hroot
    (Units.map g.toMonoidHom a) (by rw [← map_pow, ha, map_one])
  obtain ⟨W, hxW, i, j, heq⟩ :=
    X.presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial
      (a : Γ(X, ⊤)) (rootScalarSections c ((ζ : Kˣ) : K)) hζ
  let U : X.Opens := W
  have hxU : x ∈ U := hxW
  have hij : i = j := Subsingleton.elim _ _
  rw [hij] at heq
  refine ⟨U, hxU, ζ, ?_⟩
  apply Units.ext
  rw [rootScalarSections_comp]
  apply (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective
  change ((U.ι.appTop ≫ U.topIso.hom) (a : Γ(X, ⊤))) =
    (U.ι.appTop ≫ U.topIso.hom) (rootScalarSections c ((ζ : Kˣ) : K))
  rw [opens_ι_appTop_topIso_hom]
  have hj : j = homOfLE (le_top : U ≤ ⊤) := Subsingleton.elim _ _
  rw [hj] at heq
  exact heq

/-- The structural presentation of constant roots in the Kummer kernel is locally injective. -/
theorem constantRootsKernelPresentation_locallyInjective
    (c : X ⟶ Spec (.of K)) (n : ℕ) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (constantRootsKernelPresentation c n) := by
  constructor
  intro V a b hab
  let S := Presheaf.equalizerSieve
    (F := (Functor.const X.Etaleᵒᵖ).obj (rootCoefficients K n)) a b
  change S ∈ X.smallGrothendieckTopology
    (show MorphismProperty Scheme.{u} from @Etale) V.unop
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
    (le_refl _)]
  apply (Scheme.mem_toGrothendieck_smallPretopology
    (P := show MorphismProperty Scheme.{u} from @Etale)
    (Q := show MorphismProperty Scheme.{u} from @Etale) V.unop S).mpr
  intro x
  have hu : (constantRootsToUnitsPresheaf c n).app V a =
      (constantRootsToUnitsPresheaf c n).app V b := by
    have h := congrArg (fun t =>
      (kernel.ι (etaleMultiplicativeGroupPower X n)).hom.app V t) hab
    have hι := congrArg (fun t => t.app V) (constantRootsKernelPresentation_ι c n)
    exact (ConcreteCategory.congr_hom hι a).symm.trans
      (h.trans (ConcreteCategory.congr_hom hι b))
  have heq : a = b := by
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    let g := (V.unop.left.presheaf.germ ⊤ x trivial).hom
    apply (g.comp (rootScalarSections (V.unop.hom ≫ c))).injective
    exact congrArg (fun t : Additive ((Γ(V.unop.left, ⊤) : Type u)ˣ) =>
      g ((t.toMul : (Γ(V.unop.left, ⊤) : Type u)ˣ) : Γ(V.unop.left, ⊤))) hu
  refine ⟨V.unop, 𝟙 V.unop, x, ?_, inferInstance, rfl⟩
  exact heq

/-- A primitive root in the ground field makes every kernel section locally constant
when the positive exponent is invertible. -/
theorem constantRootsKernelPresentation_locallySurjective_of_primitiveRoot
    (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (hroot : ∃ ζ : K, IsPrimitiveRoot ζ n) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (constantRootsKernelPresentation c n) := by
  constructor
  intro V s
  let k := kernel.ι (etaleMultiplicativeGroupPower X n)
  let a : (Γ(V.left, ⊤) : Type u)ˣ := (k.hom.app (op V) s).toMul
  have ha : a ^ n = 1 := by
    have hz := ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op V))
        (kernel.condition (etaleMultiplicativeGroupPower X n))) s
    change (etaleMultiplicativeGroupPower X n).hom.app (op V)
      (k.hom.app (op V) s) = 0 at hz
    exact congrArg Additive.toMul hz
  let S := Presheaf.imageSieve (constantRootsKernelPresentation c n) s
  change S ∈ X.smallGrothendieckTopology
    (show MorphismProperty Scheme.{u} from @Etale) V
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
    (le_refl _)]
  apply (Scheme.mem_toGrothendieck_smallPretopology
    (P := show MorphismProperty Scheme.{u} from @Etale)
    (Q := show MorphismProperty Scheme.{u} from @Etale) V S).mpr
  intro x
  obtain ⟨U, hxU, ζ, hζ⟩ := unit_root_is_locally_constant (V.hom ≫ c) hn hnK hroot a ha x
  let W : X.Etale := Scheme.Etale.mk (U.ι ≫ V.hom)
  let g : W ⟶ V := MorphismProperty.Over.homMk U.ι rfl
  refine ⟨W, g, ⟨x, hxU⟩, ?_, inferInstance, rfl⟩
  refine ⟨Additive.ofMul ζ, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (k.hom.app (op W))).mp inferInstance
  have hι := ConcreteCategory.congr_hom
    (congrArg (fun t => t.app (op W)) (constantRootsKernelPresentation_ι c n))
      (Additive.ofMul ζ)
  have hk := ConcreteCategory.congr_hom (k.hom.naturality g.op) s
  refine hι.trans ?_
  refine Eq.trans ?_ hk.symm
  apply Additive.toMul.injective
  change Units.map (rootScalarSections ((U.ι ≫ V.hom) ≫ c)).toMonoidHom
    (ζ : Kˣ) = Units.map U.ι.appTop.hom.toMonoidHom a
  rw [Category.assoc]
  exact hζ.symm

/-- Over an algebraically closed field, every kernel section is locally a constant root
when its order is invertible. -/
theorem constantRootsKernelPresentation_locallySurjective [IsAlgClosed K]
    (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K)) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (constantRootsKernelPresentation c n) := by
  have : NeZero (n : K) := ⟨hnK.ne_zero⟩
  exact constantRootsKernelPresentation_locallySurjective_of_primitiveRoot c hn hnK
    (HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n)

/-- Over a field containing a primitive root of the positive invertible order,
the original structural map identifies constant roots with the Kummer kernel. -/
def constantRootsOfUnityKummerKernelIsoOfPrimitiveRoot
    (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (hroot : ∃ ζ : K, IsPrimitiveRoot ζ n) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (.of (Additive (rootsOfUnity n K))) ≅ etaleRootsOfUnitySheaf X n := by
  have : Presheaf.IsLocallyInjective X.smallEtaleTopology
      (constantRootsKernelPresentation c n) := by
    exact constantRootsKernelPresentation_locallyInjective c n
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (constantRootsKernelPresentation c n) := by
    exact constantRootsKernelPresentation_locallySurjective_of_primitiveRoot
      c hn hnK hroot
  have hW := X.smallEtaleTopology.W_of_isLocallyBijective
    (constantRootsKernelPresentation c n)
  have hMap : X.smallEtaleTopology.W (constantRootsOfUnityToKummerKernel c n).hom :=
    (X.smallEtaleTopology.W.precomp_iff _ _
      (X.smallEtaleTopology.W_toSheafify
        ((Functor.const X.Etaleᵒᵖ).obj (rootCoefficients K n)))).mp hW
  have : IsIso (constantRootsOfUnityToKummerKernel c n) :=
    (X.smallEtaleTopology.W_sheafToPresheaf_map_iff_isIso _).mp hMap
  exact asIso (constantRootsOfUnityToKummerKernel c n)

/-- On an original constant generator, the comparison followed by the
Kummer inclusion is the actual structural homomorphism on units. -/
theorem constantRootsOfUnityKummerKernelIsoOfPrimitiveRoot_generator
    (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (hroot : ∃ ζ : K, IsPrimitiveRoot ζ n) (V : X.Etale) (ζ : rootsOfUnity n K) :
    (kernel.ι (etaleMultiplicativeGroupPower X n)).hom.app (op V)
      ((constantRootsOfUnityKummerKernelIsoOfPrimitiveRoot c hn hnK hroot).hom.hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (Additive (rootsOfUnity n K))))).app (op V)
              (Additive.ofMul ζ))) =
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (.of K)).inv ≫ (V.hom ≫ c).appTop).hom.toMonoidHom)
          (ζ : Kˣ)) :=
  ConcreteCategory.congr_hom
    (congrArg (fun t => t.app (op V)) (constantRootsKernelPresentation_ι c n))
      (Additive.ofMul ζ)

/-- Over an algebraically closed field, constant roots of invertible order
give exactly the original Kummer kernel, in every characteristic. -/
def constantRootsOfUnityKummerKernelIso [IsAlgClosed K]
    (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K)) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (.of (Additive (rootsOfUnity n K))) ≅ etaleRootsOfUnitySheaf X n := by
  have : NeZero (n : K) := ⟨hnK.ne_zero⟩
  exact constantRootsOfUnityKummerKernelIsoOfPrimitiveRoot c hn hnK
    (HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n)

/-- On an original constant generator, the comparison followed by the
Kummer inclusion is the actual structural homomorphism on units. -/
theorem constantRootsOfUnityKummerKernelIso_generator [IsAlgClosed K]
    (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (V : X.Etale) (ζ : rootsOfUnity n K) :
    (kernel.ι (etaleMultiplicativeGroupPower X n)).hom.app (op V)
      ((constantRootsOfUnityKummerKernelIso c hn hnK).hom.hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (Additive (rootsOfUnity n K))))).app (op V)
              (Additive.ofMul ζ))) =
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (.of K)).inv ≫ (V.hom ≫ c).appTop).hom.toMonoidHom)
          (ζ : Kˣ)) := by
  have : NeZero (n : K) := ⟨hnK.ne_zero⟩
  exact constantRootsOfUnityKummerKernelIsoOfPrimitiveRoot_generator c hn hnK
    (HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n) V ζ

end EtaleCohomology
