/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Actual finite coefficients in a covering function field

The original constant-module comparison and the original Kummer
inclusion give an injective map on sections at a connected finite
étale cover. On a literal constant generator this map is the actual
structural image of the same coherent primitive root. Thus subsequent
deck computations retain the original coefficients and their root
normalization.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory
open EtaleCohomology EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (Y : FiniteEtale X) [IsConnected Y]

local notation "N" => ℓ ^ (n + 1)
local notation "R" => ULift (ZMod N)
local notation "C₀" =>
  CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R)) (ModuleCat.of R R)
local notation "W" => CategoryTheory.Functor.obj (finiteEtaleInclusion X) Y
local notation "η" =>
  NatTrans.app (toSheafify X.smallEtaleTopology
    (CategoryTheory.Functor.obj (CategoryTheory.Functor.const X.Etaleᵒᵖ) (ModuleCat.of R R))) (op W)

/-- The original finite coefficient section, mapped through its
actual Kummer inclusion into the function field of the same cover. -/
def finiteEtaleKummerCoefficientMap :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    (C₀).obj.obj (op W) →+ Additive Y.left.functionFieldˣ := by
  intro hY
  let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
  let κ := (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom ≫
    kernel.ι (etaleMultiplicativeGroupPower X N)
  exact (finiteEtaleGenericUnitSectionsEquiv Y).toAddMonoidHom.comp
    (((etaleGenericUnitShortComplex X).f.hom.app (op W)).hom.comp
      ((κ.hom.app (op W)).hom.comp (δ.hom.hom.app (op W)).hom))

/-- None of the original coefficient information is lost by passing
to the actual covering function field. -/
theorem finiteEtaleKummerCoefficientMap_injective :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    Function.Injective (finiteEtaleKummerCoefficientMap c ℓ hℓ n Y) := by
  intro hY
  let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
  let κ := (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom ≫
    kernel.ι (etaleMultiplicativeGroupPower X N)
  have : Mono (etaleGenericUnitShortComplex X).f :=
    (etaleGenericUnitShortComplex_shortExact X).mono_f
  exact (finiteEtaleGenericUnitSectionsEquiv Y).injective.comp
    (((AddCommGrpCat.mono_iff_injective
      ((etaleGenericUnitShortComplex X).f.hom.app (op W))).mp inferInstance).comp
      (((AddCommGrpCat.mono_iff_injective (κ.hom.app (op W))).mp inferInstance).comp
        ((AddCommGrpCat.mono_iff_injective (δ.hom.hom.app (op W))).mp inferInstance)))

/-- A literal original constant generator maps to the structural
image of its same coherent root of unity. -/
theorem finiteEtaleKummerCoefficientMap_generator (a : R) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    finiteEtaleKummerCoefficientMap c ℓ hℓ n Y (η a) =
      Additive.ofMul (Units.map
        (AlgebraicCurve.baseToFunctionField (C := Y.left) (Y.hom ≫ c)).toMonoidHom
        ((ellPowerRootsCoefficientEquiv K ℓ hℓ n a).toMul : Kˣ)) := by
  intro hY
  let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
  have hδ := ConcreteCategory.congr_hom
    (etaleConstantModuleForgetIso_toSheafify X R (ModuleCat.of R R) W) a
  change δ.hom.hom.app (op W) (η a) =
    (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (ellPowerCoefficients.{u} ℓ n))).app (op W) a at hδ
  change finiteEtaleGenericUnitSectionsEquiv Y
    ((etaleGenericUnitShortComplex X).f.hom.app (op W)
      ((kernel.ι (etaleMultiplicativeGroupPower X N)).hom.app (op W)
        ((ellPowerConstantKummerKernelIso c ℓ hℓ n).hom.hom.app (op W)
          (δ.hom.hom.app (op W) (η a))))) = _
  rw [hδ, ellPowerConstantKummerKernelIso_generator]
  refine (finiteEtaleGenericUnitSectionsEquiv_regularUnit Y _).trans ?_
  rfl

/-- The same generator formula in the supplied primitive-root
coordinates used for explicit cyclic cochains. The root is the one
already fixed by the original finite coefficient comparison. -/
theorem finiteEtaleKummerCoefficientMap_generator_coordinate (a : R) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let hζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
    let ι := AlgebraicCurve.baseToFunctionField (C := Y.left) (Y.hom ≫ c)
    finiteEtaleKummerCoefficientMap c ℓ hℓ n Y (η a) =
      Additive.ofMul (_root_.KummerTheory.primitiveRootCoordinate
        (hζ.map_of_injective (Units.map_injective (f := ι.toMonoidHom) ι.injective))
        a.down) := by
  intro hY hζ ι
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [finiteEtaleKummerCoefficientMap_generator]
  change Additive.ofMul (Units.map ι.toMonoidHom
    (_root_.KummerTheory.primitiveRootCoordinate hζ a.down)) = _
  exact congrArg Additive.ofMul
    (_root_.KummerTheory.primitiveRootCoordinate_map hζ ι a.down)

include c hℓ in
/-- Every original finite coefficient section on the connected
cover is a unique literal constant. Surjectivity follows from the
actual roots in its function field, using the fixed coherent root. -/
theorem finiteEtaleKummerCoefficientGenerator_bijective :
    Function.Bijective η := by
  have : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let ι := AlgebraicCurve.baseToFunctionField (C := Y.left) (Y.hom ≫ c)
  let hζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
  let hζY := hζ.map_of_injective
    (Units.map_injective (f := ι.toMonoidHom) ι.injective)
  let q : (C₀).obj.obj (op W) →+ Additive Y.left.functionFieldˣ :=
    finiteEtaleKummerCoefficientMap c ℓ hℓ n Y
  constructor
  · intro a b hab
    have h := congrArg q hab
    rw [finiteEtaleKummerCoefficientMap_generator_coordinate,
      finiteEtaleKummerCoefficientMap_generator_coordinate] at h
    apply ULift.ext
    exact (_root_.KummerTheory.primitiveRootCoordinate_injective hζY)
      (Additive.ofMul.injective h)
  · intro s
    have hN : ((N : ℕ) : R) = 0 := by
      apply ULift.ext
      exact ZMod.natCast_self N
    have hs : N • s = 0 := by
      rw [← Nat.cast_smul_eq_nsmul R, hN, zero_smul]
    have hq : N • q s = 0 :=
      (map_nsmul q (N : ℕ) s).symm.trans ((congrArg q hs).trans (map_zero q))
    have hp : (q s).toMul ^ N = 1 := congrArg Additive.toMul hq
    obtain ⟨a, ha⟩ := _root_.KummerTheory.primitiveRootCoordinate_surjective_roots
      hζY (q s).toMul hp
    refine ⟨ULift.up a, ?_⟩
    apply finiteEtaleKummerCoefficientMap_injective c ℓ hℓ n Y
    rw [finiteEtaleKummerCoefficientMap_generator_coordinate]
    exact congrArg Additive.ofMul ha

/-- The actual constant generator is an equivalence at the connected
finite cover. Its inverse reads the original section's scalar. -/
def finiteEtaleKummerCoefficientsEquiv : R ≃ₗ[R] (C₀).obj.obj (op W) :=
  LinearEquiv.ofBijective (η).hom
    (finiteEtaleKummerCoefficientGenerator_bijective c ℓ hℓ n Y)

theorem finiteEtaleKummerCoefficientsEquiv_apply (a : R) :
    finiteEtaleKummerCoefficientsEquiv c ℓ hℓ n Y a = η a := rfl

/-- The scalar of any original section has the same actual
function-field root value, with the same coherent normalization. -/
theorem finiteEtaleKummerCoefficientMap_coordinate (s : (C₀).obj.obj (op W)) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let hζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
    let ι := AlgebraicCurve.baseToFunctionField (C := Y.left) (Y.hom ≫ c)
    finiteEtaleKummerCoefficientMap c ℓ hℓ n Y s =
      Additive.ofMul (_root_.KummerTheory.primitiveRootCoordinate
        (hζ.map_of_injective (Units.map_injective (f := ι.toMonoidHom) ι.injective))
        ((finiteEtaleKummerCoefficientsEquiv c ℓ hℓ n Y).symm s).down) := by
  intro hY hζ ι
  let e := finiteEtaleKummerCoefficientsEquiv c ℓ hℓ n Y
  calc
    _ = finiteEtaleKummerCoefficientMap c ℓ hℓ n Y (η (e.symm s)) :=
      congrArg (finiteEtaleKummerCoefficientMap c ℓ hℓ n Y)
        (e.apply_symm_apply s).symm
    _ = _ := finiteEtaleKummerCoefficientMap_generator_coordinate c ℓ hℓ n Y (e.symm s)

end EtaleFundamentalGroups.Cohomology
