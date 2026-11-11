/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRefinement
public import Nyll.EtaleCohomology.Classical.FreeModuleCechFaces
public import Nyll.EtaleCohomology.Classical.FreeModuleCechRelations
public import Nyll.EtaleCohomology.Classical.FreeModuleCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafActionSections
public import Nyll.EtaleCohomology.Classical.GaloisCechCochains
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisCoefficients
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupRootPower
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# The original finite cup in actual deck coordinates

The actual common-cover edge sections have unique scalars on the
connected Galois refinement. Their scalar root equations use the same
two original rational roots. Evaluating the original cup triangle
then gives the scalar product with its original `a₁₂ b₀₁` order.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory
open EtaleCohomology EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

private theorem freeModuleCechTriangleBoundary_eval_hom
    (R : Type u) [Ring R] {A B : Type u} (f : A → B)
    (M : ModuleCat.{u} R) (q : (ModuleCat.free R).obj (CechEdge f) ⟶ M)
    (t : CechTriangle f) :
    q (freeModuleCechTriangleBoundary R f (ModuleCat.freeMk t)) =
      q (ModuleCat.freeMk (CechEdge.mk t.second t.third t.same₂)) -
        q (ModuleCat.freeMk (CechEdge.mk t.first t.third (t.same₁.trans t.same₂))) +
      q (ModuleCat.freeMk (CechEdge.mk t.first t.second t.same₁)) := by
  have hb := ModuleCat.freeDesc_apply (R := R)
    (M := (ModuleCat.free R).obj (CechEdge f))
    (↾fun s : CechTriangle f =>
      ModuleCat.freeMk (CechEdge.mk s.second s.third s.same₂) -
        ModuleCat.freeMk (CechEdge.mk s.first s.third (s.same₁.trans s.same₂)) +
      ModuleCat.freeMk (CechEdge.mk s.first s.second s.same₁)) t
  exact (congrArg q hb).trans
    ((map_add q.hom _ _).trans
      (congrArg (fun a : M =>
        a + q (ModuleCat.freeMk (CechEdge.mk t.first t.second t.same₁)))
        (map_sub q.hom _ _)))

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

local notation "R" => ULift (ZMod (ℓ ^ (n + 1)))
local notation "C" =>
  (CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R))) (ModuleCat.of R R)
local notation "I" => finiteEtaleInclusion X
local notation "W" => (CategoryTheory.Functor.obj I) Y
local notation "f" => hT.from (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT)
local notation "P₁" => cechEdgeFunctor (yoneda.map f)
local notation "P₂" => cechTriangleFunctor (yoneda.map f)
local notation "η" =>
  (NatTrans.app (toSheafify X.smallEtaleTopology
    ((CategoryTheory.Functor.obj (CategoryTheory.Functor.const X.Etaleᵒᵖ))
      (ModuleCat.of R R)))) (op W)
local notation "z[" i "]" => finiteKummerCupCommonCocycle c ℓ hℓ n d b hb hT i
local notation "s[" i "]" => freeModuleSheafHomEquiv X R P₁ C z[i]
local notation "edge[" σ "]" =>
  (CechEdge.mk g
    ((CategoryTheory.Functor.map I) (CategoryTheory.Iso.hom (CategoryTheory.Aut.asIso σ)) ≫ g)
    (IsTerminal.hom_ext hT _ _) : (CategoryTheory.Functor.obj P₁) (op W))
local notation "triangle[" σ "," τ "]" =>
  (NatTrans.app (cechTriangleRefinement f g)) (op W)
    (galoisCechTriangle X Y hT (g ≫ f) σ τ)

/-- The scalar of an original Kummer edge on the actual Galois
refinement, read through the proved original constant-generator equivalence. -/
def finiteKummerCupGaloisCoefficient (i : Bool) (σ : Aut Y) : R :=
  (finiteEtaleKummerCoefficientsEquiv c ℓ hℓ n Y).symm
    ((s[i]).app (op W) edge[σ])

/-- The original edge section is exactly its actual constant scalar. -/
theorem finiteKummerCupGaloisCoefficient_section (i : Bool) (σ : Aut Y) :
    (s[i]).app (op W) edge[σ] =
      η (finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i σ) :=
  ((finiteEtaleKummerCoefficientsEquiv c ℓ hℓ n Y).apply_symm_apply _).symm

/-- These same scalars are the actual deck ratios of the original
rational roots, with precisely the original coherent primitive root. -/
theorem finiteKummerCupGaloisCoefficient_root (i : Bool) (σ : Aut Y) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let hζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
    let ι := AlgebraicCurve.baseToFunctionField («C» := Y.left) (Y.hom ≫ c)
    Additive.ofMul (Units.map
        ((show Y.left ⟶ Y.left from σ.asIso.hom.left).functionFieldMap
          σ.asIso.hom.left.surjective.denseRange).toMonoidHom
        (finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i).toMul) -
      finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i =
        Additive.ofMul (_root_.KummerTheory.primitiveRootCoordinate
          (hζ.map_of_injective (Units.map_injective («f» := ι.toMonoidHom) ι.injective))
          (finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i σ).down) := by
  intro hY hζ ι
  exact (finiteKummerCupGaloisRoot_deckRatio c ℓ hℓ n d b hb hT Y g i σ).trans
    (finiteEtaleKummerCoefficientMap_coordinate c ℓ hℓ n Y ((s[i]).app (op W) edge[σ]))

omit [IsIntegral X] [IsNormalIntegral X] [Fact ℓ.Prime] [IsGalois Y] in
private theorem original_constant_generator_deck (σ : Aut Y) (a : (R : Type u)) :
    (C).obj.map ((I).map σ.asIso.hom).op (η a) = η a := by
  have h := ConcreteCategory.congr_hom
    ((toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R))).naturality
        ((I).map σ.asIso.hom).op) a
  exact h.symm

/-- The later edge of the original triangle has the scalar of its
second deck transformation. This uses actual coefficient naturality. -/
theorem finiteKummerCupGaloisCoefficient_edge12 (i : Bool) (σ τ : Aut Y) :
    (s[i]).app (op W)
        ((cechTriangleEdge12 (yoneda.map f)).app (op W) triangle[σ, τ]) =
      η (finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i τ) := by
  have he : (cechTriangleEdge12 (yoneda.map f)).app (op W) triangle[σ, τ] =
      (P₁).map ((I).map σ.asIso.hom).op edge[τ] := by
    apply CechEdge.ext
    · rfl
    · change (I).map (σ.asIso.hom ≫ τ.asIso.hom) ≫ g =
        (I).map σ.asIso.hom ≫ ((I).map τ.asIso.hom ≫ g)
      rw [(I).map_comp, Category.assoc]
  rw [he]
  have hn := ConcreteCategory.congr_hom ((s[i]).naturality ((I).map σ.asIso.hom).op) edge[τ]
  exact hn.trans ((congrArg ((C).obj.map ((I).map σ.asIso.hom).op)
    (finiteKummerCupGaloisCoefficient_section c ℓ hℓ n d b hb hT Y g i τ)).trans
      (original_constant_generator_deck ℓ n Y σ _))

omit [IsNormalIntegral X] [IsGalois Y] in
private theorem original_cocycle_triangle (i : Bool) (t : (P₂).obj (op W)) :
    (s[i]).app (op W) ((cechTriangleEdge12 (yoneda.map f)).app (op W) t) -
        (s[i]).app (op W) ((cechTriangleEdge02 (yoneda.map f)).app (op W) t) +
      (s[i]).app (op W) ((cechTriangleEdge01 (yoneda.map f)).app (op W) t) = 0 := by
  let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)
  have hz := congrArg (adj.homEquiv (P₂ ⋙ ModuleCat.free R) C)
    (finiteKummerCupCommonCocycle_cocycle c ℓ hℓ n d b hb hT i)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homAddEquiv_zero] at hz
  have h := ConcreteCategory.congr_hom (congrArg (fun q => q.app (op W)) hz)
    (ModuleCat.freeMk t)
  change (adj.homEquiv (P₁ ⋙ ModuleCat.free R) C z[i]).app (op W)
    (freeModuleCechTriangleBoundary R ((yoneda.map f).app (op W))
      (ModuleCat.freeMk t)) = 0 at h
  have heval := freeModuleCechTriangleBoundary_eval_hom R
    ((yoneda.map f).app (op W)) ((C).obj.obj (op W))
    ((adj.homEquiv (P₁ ⋙ ModuleCat.free R) C z[i]).app (op W)) t
  exact heval.symm.trans h

/-- The original edge scalars satisfy the actual deck composition
law, obtained from the original triangle cocycle. -/
theorem finiteKummerCupGaloisCoefficient_mul (i : Bool) (σ τ : Aut Y) :
    finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i (τ * σ) =
      finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i τ +
        finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i σ := by
  let χ := finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i
  have h01 : (cechTriangleEdge01 (yoneda.map f)).app (op W) triangle[σ, τ] = edge[σ] := by
    apply CechEdge.ext
    · exact Category.id_comp g
    · rfl
  have h02 : (cechTriangleEdge02 (yoneda.map f)).app (op W) triangle[σ, τ] = edge[τ * σ] := by
    apply CechEdge.ext
    · exact Category.id_comp g
    · rfl
  have hz := original_cocycle_triangle c ℓ hℓ n d b hb hT Y i triangle[σ, τ]
  rw [finiteKummerCupGaloisCoefficient_edge12, h01, h02,
    finiteKummerCupGaloisCoefficient_section, finiteKummerCupGaloisCoefficient_section] at hz
  change η (χ τ) - η (χ (τ * σ)) + η (χ σ) = 0 at hz
  apply (finiteEtaleKummerCoefficientsEquiv c ℓ hℓ n Y).injective
  change η (χ (τ * σ)) = η (χ τ + χ σ)
  rw [map_add]
  apply sub_eq_zero.mp
  calc
    η (χ (τ * σ)) - (η (χ τ) + η (χ σ)) =
        -(η (χ τ) - η (χ (τ * σ)) + η (χ σ)) := by abel
    _ = 0 := by rw [hz, neg_zero]

/-- The original finite Kummer edge defines an actual additive
character of the opposite deck group, the group acting on the function field. -/
def finiteKummerCupGaloisCharacter (i : Bool) :
    Additive ((Aut Y)ᵐᵒᵖ) →+ R where
  toFun σ := finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i σ.toMul.unop
  map_zero' := by
    let χ := finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i
    have h := finiteKummerCupGaloisCoefficient_mul c ℓ hℓ n d b hb hT Y g i 1 1
    change χ (1 * 1) = χ 1 + χ 1 at h
    rw [one_mul] at h
    exact (add_left_cancel ((add_zero (χ 1)).trans h)).symm
  map_add' σ τ :=
    (finiteKummerCupGaloisCoefficient_mul c ℓ hℓ n d b hb hT Y g i
      σ.toMul.unop τ.toMul.unop).trans (add_comm _ _)

/-- The original cup on the original refined triangle is the
constant product `χ_true(σ) * χ_false(τ)`. The order is inherited from
the original `a₁₂ b₀₁` cup, before taking any cohomology class. -/
theorem finiteKummerCupGaloisTriangleSection (σ τ : Aut Y) :
    finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W triangle[σ, τ] =
      η (finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g true σ *
        finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g false τ) := by
  let a₁ := finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g false τ
  let b₀ := finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g true σ
  let A := (freeModuleSheafFunctor X R).map (cechTriangleEdge12 (yoneda.map f)) ≫ z[false]
  let B := (freeModuleSheafFunctor X R).map (cechTriangleEdge01 (yoneda.map f)) ≫ z[true]
  have hA : (freeModuleSheafHomEquiv X R P₂ C A).app (op W) triangle[σ, τ] = η a₁ := by
    rw [freeModuleSheafHomEquiv_precomp]
    exact finiteKummerCupGaloisCoefficient_edge12 c ℓ hℓ n d b hb hT Y g false σ τ
  have hB : (freeModuleSheafHomEquiv X R P₂ C B).app (op W) triangle[σ, τ] = η b₀ := by
    rw [freeModuleSheafHomEquiv_precomp]
    have he : (cechTriangleEdge01 (yoneda.map f)).app (op W) triangle[σ, τ] = edge[σ] := by
      apply CechEdge.ext
      · exact Category.id_comp g
      · rfl
    change (s[true]).app (op W)
      ((cechTriangleEdge01 (yoneda.map f)).app (op W) triangle[σ, τ]) = _
    rw [he]
    exact finiteKummerCupGaloisCoefficient_section c ℓ hℓ n d b hb hT Y g true σ
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective a₁.down
  have hma : (m : R) = a₁ := by
    apply ULift.ext
    exact hm
  have hscalar : η a₁ = m • η (1 : R) := by
    rw [← hma]
    simpa only [zsmul_one] using map_zsmul (η).hom m (1 : R)
  have haction : finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W triangle[σ, τ] =
      m • η b₀ :=
    (finiteKummerCupTriangleSection_eq_action c ℓ hℓ n d b hb hT W triangle[σ, τ]).trans
      ((freeModuleSheafAction_generator_of_zsmul X R A B W triangle[σ, τ] m
        (hA.trans hscalar)).trans
        (congrArg (fun x : (C).obj.obj (op W) => m • x) hB))
  have hproduct : m • b₀ = b₀ * a₁ := by
    rw [zsmul_eq_mul, hma, mul_comm]
  exact haction.trans
    ((map_zsmul (η).hom m b₀).symm.trans (congrArg η hproduct))

end EtaleFundamentalGroups.Cohomology
