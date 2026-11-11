/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRefinement
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.GaloisCechCochains
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCocycle
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCover
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisCoefficients
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisCocycle
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupRootPower
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# A field cochain on the original finite Kummer cover

The actual covering function field identifies a specified deck
cochain with a map from the original free edge sheaf. An explicit
pointwise coboundary equation then becomes equality with the original
finite cup on the entire original free triangle sheaf. The actual
refinement, coefficients and original two-step representative are
retained; no comparison of cohomology classes is assumed.
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
  (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 (b i) =
    ℓ ^ (n + 1) • d i)
  {T : X.Etale} (hT : IsTerminal T)
  (Y : FiniteEtale X) [IsGalois Y]
  (g : (finiteEtaleInclusion X).obj Y ⟶
    finiteKummerCupCommonCover c ℓ hℓ n d b hb hT)

local notation "N" => ℓ ^ (n + 1)
local notation "R" => ULift (ZMod N)
local notation "W" => (CategoryTheory.Functor.obj (finiteEtaleInclusion X)) Y
local notation "f" => hT.from (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT)
local notation "G" => (ShortComplex.X₂ (etaleGenericUnitShortComplex X))
local notation "Q" => presheafToSheaf X.smallEtaleTopology AddCommGrpCat
local notation "A" => sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat
local notation "χ[" i "]" => finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i

/-- A specified field cochain as an actual morphism from the
original free edge sheaf of the same Galois refinement. -/
def finiteKummerCupGaloisFieldCochain :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    (Aut Y → Additive Y.left.functionFieldˣ) →
      ((Q).obj (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶ G) := by
  intro hY a
  exact galoisCechEdgeCochain X G Y (g ≫ f)
    (fun σ => (finiteEtaleGenericUnitSectionsEquiv Y).symm (a σ))

/-- An explicit field coboundary equation gives the exact original
cup triangle morphism on the same cover, with its unchanged native
Kummer coefficient inclusion. -/
theorem finiteKummerCupGaloisFieldCochain_boundary :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let hζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
    let cY : Y.left ⟶ Spec (.of K) := Y.hom ≫ c
    let ι := AlgebraicCurve.baseToFunctionField cY
    let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
    let κ := (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom ≫
      kernel.ι (etaleMultiplicativeGroupPower X N)
    ∀ a : Aut Y → Additive Y.left.functionFieldˣ,
      (∀ σ τ : Aut Y,
        Additive.ofMul (Units.map
            (σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
            (a τ).toMul) - a (τ * σ) + a σ =
          Additive.ofMul (_root_.KummerTheory.primitiveRootCoordinate
            (hζ.map_of_injective (Units.map_injective («f» := ι.toMonoidHom) ι.injective))
            (χ[true] σ * χ[false] τ).down)) →
      (Q).map (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫
          finiteKummerCupGaloisFieldCochain c ℓ hℓ n d b hb hT Y g a =
        abelianCechTriangleRefinement f g X.smallEtaleTopology ≫
          ((abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
            finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT) ≫
              (δ.hom ≫ κ ≫ (etaleGenericUnitShortComplex X).f)) := by
  intro hY hζ cY ι δ κ a ha
  unfold finiteKummerCupGaloisFieldCochain
  let ρ := δ.hom ≫ κ ≫ (etaleGenericUnitShortComplex X).f
  let w := abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
    finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT
  apply abelianCechTriangleHom_ext_galois X G Y hT (g ≫ f)
  intro σ τ
  let t := galoisCechTriangle X Y hT (g ≫ f) σ τ
  let t' := (cechTriangleRefinement f g).app (op W) t
  have hr : (((A).homEquiv _ G
      (abelianCechTriangleRefinement f g X.smallEtaleTopology ≫ (w ≫ ρ))).app (op W))
        (FreeAbelianGroup.of t) =
      ρ.hom.app (op W)
        (finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W t') := by
    change (freeAbelianSheafHomEquiv X (cechTriangleFunctor (yoneda.map (g ≫ f))) G
      ((freeAbelianSheafFunctor X).map (cechTriangleRefinement f g) ≫ (w ≫ ρ))).app
        (op W) t = _
    rw [freeAbelianSheafHomEquiv_precomp, freeAbelianSheafHomEquiv_postcomp]
    rfl
  have hleft := galoisCechEdgeCochain_triangle_coordinate X G Y hT (g ≫ f)
    (fun σ => (finiteEtaleGenericUnitSectionsEquiv Y).symm (a σ)) σ τ
  let e : (G).obj.obj (op W) ≃+ Additive Y.left.functionFieldˣ :=
    finiteEtaleGenericUnitSectionsEquiv Y
  have hdeck : e ((G).obj.map ((finiteEtaleInclusion X).map σ.asIso.hom).op
      (e.symm (a τ))) =
      Additive.ofMul (Units.map
        (σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
        (a τ).toMul) := by
    have h := finiteEtaleGenericUnitSectionsEquiv_deck Y σ (e.symm (a τ))
    change e ((G).obj.map ((finiteEtaleInclusion X).map σ.asIso.hom).op
        (e.symm (a τ))) = Additive.ofMul (Units.map
          (σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
          (e (e.symm (a τ))).toMul) at h
    exact h.trans (congrArg (fun z : Additive Y.left.functionFieldˣ =>
      Additive.ofMul (Units.map
        (σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
        z.toMul)) (e.apply_symm_apply (a τ)))
  let leftSection : (G).obj.obj (op W) :=
    (G).obj.map ((finiteEtaleInclusion X).map σ.asIso.hom).op (e.symm (a τ))
  let middleSection : (G).obj.obj (op W) := e.symm (a (τ * σ))
  let rightSection : (G).obj.obj (op W) := e.symm (a σ)
  have hsections : e (leftSection - middleSection + rightSection) =
      e leftSection - e middleSection + e rightSection :=
    (e.map_add (leftSection - middleSection) rightSection).trans
      (congrArg (fun s : Additive Y.left.functionFieldˣ => s + e rightSection)
        (e.map_sub leftSection middleSection))
  have hvalues : e leftSection - e middleSection + e rightSection =
      Additive.ofMul (Units.map
        (σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
        (a τ).toMul) - a (τ * σ) + a σ :=
    congrArg₂ (fun x y : Additive Y.left.functionFieldˣ => x + y)
      (congrArg₂ (fun x y : Additive Y.left.functionFieldˣ => x - y)
        hdeck (e.apply_symm_apply (a (τ * σ))))
      (e.apply_symm_apply (a σ))
  apply e.injective
  rw [hleft, hr]
  refine hsections.trans (hvalues.trans ?_)
  change _ = finiteEtaleKummerCoefficientMap c ℓ hℓ n Y
    (finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W t')
  rw [finiteKummerCupGaloisTriangleSection,
    finiteEtaleKummerCoefficientMap_generator_coordinate]
  exact ha σ τ

end EtaleFundamentalGroups.Cohomology
