/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CyclicCochainLocalAction
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleCechFaces
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCocycle
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCover
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorRoots
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Actual local root powers for the original finite cup triangle

The actual abelian two-step representative of the original finite
cup is evaluated on its original triangles. On a proved covering
sieve its first edge coefficient has an actual integer representative.
The original coherent roots map then sends that same cup value to the
corresponding power of the second edge's original rational-root ratio.
All local exponent choices are supplied by actual covers here.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology EtaleCohomology.Classical
open scoped EtaleCohomology.ModuleTensor

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 (b i) =
    ℓ ^ (n + 1) • d i)
  {T : X.Etale} (hT : IsTerminal T)

local notation "N" => ℓ ^ (n + 1)
local notation "R" => ULift (ZMod N)
local notation "C" =>
  (CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R))) (ModuleCat.of R R)
local notation "V" => finiteKummerCupCommonCover c ℓ hℓ n d b hb hT
local notation "f" => hT.from V
local notation "P₂" => cechTriangleFunctor (yoneda.map f)
local notation "z[" i "]" => finiteKummerCupCommonCocycle c ℓ hℓ n d b hb hT i
local notation "A₁₂" =>
  (CategoryTheory.Functor.map (freeModuleSheafFunctor X R))
    (cechTriangleEdge12 (yoneda.map f)) ≫ z[false]
local notation "B₀₁" =>
  (CategoryTheory.Functor.map (freeModuleSheafFunctor X R))
    (cechTriangleEdge01 (yoneda.map f)) ≫ z[true]

/-- Evaluation of the actual abelian cup representative on one
of the original triangles of the actual common cover. -/
def finiteKummerCupTriangleSection (W : X.Etale) (t : (P₂).obj (op W)) :
    (C).obj.obj (op W) :=
  (freeAbelianSheafHomEquiv X P₂
    ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) («R» := R)).obj C)
    (abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
      finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT)).app (op W) t

/-- Its value is the original free-module action, with the actual
two original edge factors in their original order. -/
theorem finiteKummerCupTriangleSection_eq_action (W : X.Etale) (t : (P₂).obj (op W)) :
    finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W t =
      (freeModuleSheafHomEquiv X R P₂ C
        (freeModuleSheafAction X R A₁₂ B₀₁)).app (op W) t := by
  unfold finiteKummerCupTriangleSection
  rw [finiteKummerCupSecondCocycle_triangles]
  exact congrArg (fun q => q.app (op W) t)
    (freeModuleSheafUnderlyingHomEquiv_sections X R P₂ C
      (freeModuleSheafAction X R A₁₂ B₀₁))

/-- Every original cup triangle admits an actual covering sieve
on which its roots-of-unity value is the original root ratio raised
to the supplied local integer representing the first edge value. -/
theorem finiteKummerCupTriangleSection_exists_local_rootPower
    (W₀ : X.Etale) (t₀ : (P₂).obj (op W₀)) :
    let j := X.fromSpecStalk (genericPoint X)
    let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
    let κ := (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom ≫
      kernel.ι (etaleMultiplicativeGroupPower X N)
    let s := finiteKummerCupCommonLift c ℓ hℓ n d b hb hT true
    ∃ S : Sieve W₀, S ∈ X.smallEtaleTopology W₀ ∧
      ∀ (W : X.Etale) (k : W ⟶ W₀), S k →
        ∃ m : ℤ,
          (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) C z[false]).app
              (op W) ((cechTriangleEdge12 (yoneda.map f)).app (op W) ((P₂).map k.op t₀)) =
            m • (toSheafify X.smallEtaleTopology
              ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R))).app (op W) (1 : R) ∧
          Units.map (pullback.fst W.hom j).appTop.hom.toMonoidHom
              (κ.hom.app (op W) (δ.hom.hom.app (op W)
                (finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W ((P₂).map k.op t₀)))).toMul =
            (Units.map
              (((etaleBaseChange j).map ((P₂).map k.op t₀).second).left.appTop.hom.toMonoidHom)
                (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n
                  (d true) (b true) (hb true) V s) /
              Units.map
                (((etaleBaseChange j).map ((P₂).map k.op t₀).first).left.appTop.hom.toMonoidHom)
                (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n
                  (d true) (b true) (hb true) V s)) ^ m := by
  intro j δ κ s
  obtain ⟨S, hS, hrep⟩ :=
    freeModuleSheafAction_exists_local_integer X N A₁₂ B₀₁ W₀ t₀
  refine ⟨S, hS, ?_⟩
  intro W k hk
  obtain ⟨m, hm, hprod⟩ := hrep W k hk
  let t := (P₂).map k.op t₀
  let e₀₁ := (cechTriangleEdge01 (yoneda.map f)).app (op W) t
  have hA : (freeModuleSheafHomEquiv X R P₂ C A₁₂).app (op W) t =
      (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) C z[false]).app
        (op W) ((cechTriangleEdge12 (yoneda.map f)).app (op W) t) :=
    congrArg (fun q => q.app (op W) t)
      (freeModuleSheafHomEquiv_precomp X R (cechTriangleEdge12 (yoneda.map f)) C z[false])
  have hB : (freeModuleSheafHomEquiv X R P₂ C B₀₁).app (op W) t =
      (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) C z[true]).app
        (op W) e₀₁ :=
    congrArg (fun q => q.app (op W) t)
      (freeModuleSheafHomEquiv_precomp X R (cechTriangleEdge01 (yoneda.map f)) C z[true])
  have ht : finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W t =
      m • (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) C z[true]).app
        (op W) e₀₁ :=
    (finiteKummerCupTriangleSection_eq_action c ℓ hℓ n d b hb hT W t).trans
      (hprod.trans (congrArg (fun v => m • v) hB))
  refine ⟨m, hA.symm.trans hm, ?_⟩
  change Units.map (pullback.fst W.hom j).appTop.hom.toMonoidHom
    (κ.hom.app (op W) (δ.hom.hom.app (op W)
      (finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W t))).toMul = _
  let v : (C).obj.obj (op W) :=
    (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) C z[true]).app
      (op W) e₀₁
  let q := Units.map (pullback.fst W.hom j).appTop.hom.toMonoidHom
  have hδ : δ.hom.hom.app (op W) (m • v) =
      m • δ.hom.hom.app (op W) v :=
    map_zsmul (δ.hom.hom.app (op W)).hom m v
  have hκ : κ.hom.app (op W) (m • δ.hom.hom.app (op W) v) =
      m • κ.hom.app (op W) (δ.hom.hom.app (op W) v) :=
    map_zsmul (κ.hom.app (op W)).hom m (δ.hom.hom.app (op W) v)
  have hscale : κ.hom.app (op W) (δ.hom.hom.app (op W)
      (finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W t)) =
        m • κ.hom.app (op W) (δ.hom.hom.app (op W) v) :=
    (congrArg (fun z : (C).obj.obj (op W) =>
      κ.hom.app (op W) (δ.hom.hom.app (op W) z)) ht).trans
        ((congrArg (κ.hom.app (op W)) hδ).trans hκ)
  calc
    q (κ.hom.app (op W) (δ.hom.hom.app (op W)
        (finiteKummerCupTriangleSection c ℓ hℓ n d b hb hT W t))).toMul =
        q (m • κ.hom.app (op W) (δ.hom.hom.app (op W) v)).toMul :=
      congrArg (fun z : (etaleMultiplicativeGroupSheaf X).obj.obj (op W) => q z.toMul) hscale
    _ = (q (κ.hom.app (op W) (δ.hom.hom.app (op W) v)).toMul) ^ m :=
      (congrArg q (_root_.toMul_zsmul
        (α := ((Γ(W.left, ⊤) : Type u)ˣ)) m
        (etaleMultiplicativeGroupSectionsEquiv X W
          (κ.hom.app (op W) (δ.hom.hom.app (op W) v))))).trans
          (map_zpow q _ m)
    _ = _ := congrArg (fun z => z ^ m)
      (finiteKummerCupCommonCocycle_rootRatio c ℓ hℓ n d b hb hT true W e₀₁).symm

end EtaleFundamentalGroups.Cohomology
