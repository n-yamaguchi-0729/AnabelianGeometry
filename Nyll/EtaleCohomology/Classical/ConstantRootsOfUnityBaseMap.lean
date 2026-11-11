/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The structural roots map under a change of base-field coordinates

Changing the original structural morphism by a field homomorphism changes
the actual constant-roots comparison by that same homomorphism on roots
of unity. The proof compares the original generator sections in Gm,
using the actual map on global functions. This is the coefficient twist
needed before the Frobenius action on H² can be evaluated.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}

/-- The original structural Kummer map retains the actual root action
when the structural morphism is composed with a base-field homomorphism. -/
theorem constantRootsOfUnityToKummerKernel_baseMap
    (c : X ⟶ Spec (.of K)) (φ : K →+* K) {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : K)) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom (restrictRootsOfUnity φ n).toAdditive) ≫
      constantRootsOfUnityToKummerKernel c n =
    constantRootsOfUnityToKummerKernel (c ≫ Spec.map (CommRingCat.ofHom φ)) n := by
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let A := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let ρ : A ⟶ A := AddCommGrpCat.ofHom (restrictRootsOfUnity φ n).toAdditive
  let V : X.Etale := ⊤_ X.Etale
  let η := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op V)
  let b := constantRootsOfUnityToKummerKernel c n
  let d := constantRootsOfUnityToKummerKernel
    (c ≫ Spec.map (CommRingCat.ofHom φ)) n
  let k := kernel.ι (etaleMultiplicativeGroupPower X n)
  have hη : η ≫ (C.map ρ).hom.app (op V) = ρ ≫ η := by
    have h := congrArg (fun t => t.app (op V))
      (toSheafify_naturality X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map ρ))
    exact h.symm
  apply (cancel_mono k).mp
  rw [Category.assoc]
  apply ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
    (terminalIsTerminal : IsTerminal V)).homEquiv A
      (etaleMultiplicativeGroupSheaf X)).injective
  apply ConcreteCategory.hom_ext
  intro ζ
  change k.hom.app (op V) (b.hom.app (op V) ((C.map ρ).hom.app (op V) (η ζ))) =
    k.hom.app (op V) (d.hom.app (op V) (η ζ))
  have hleft := constantRootsOfUnityKummerKernelIso_generator c hn hnK V (ρ ζ).toMul
  have hright := constantRootsOfUnityKummerKernelIso_generator
    (c ≫ Spec.map (CommRingCat.ofHom φ)) hn hnK V ζ.toMul
  refine (congrArg (fun z => k.hom.app (op V) (b.hom.app (op V) z))
    (ConcreteCategory.congr_hom hη ζ)).trans ?_
  refine hleft.trans (Eq.trans ?_ hright.symm)
  apply Additive.toMul.injective
  apply Units.ext
  have hΓ : CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of K)).inv =
      (Scheme.ΓSpecIso (.of K)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop :=
    Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have hrings : CommRingCat.ofHom φ ≫
        ((Scheme.ΓSpecIso (.of K)).inv ≫ (V.hom ≫ c).appTop) =
      (Scheme.ΓSpecIso (.of K)).inv ≫
        (V.hom ≫ (c ≫ Spec.map (CommRingCat.ofHom φ))).appTop := by
    calc
      _ = (CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of K)).inv) ≫
          (V.hom ≫ c).appTop := (Category.assoc _ _ _).symm
      _ = ((Scheme.ΓSpecIso (.of K)).inv ≫
          (Spec.map (CommRingCat.ofHom φ)).appTop) ≫ (V.hom ≫ c).appTop :=
        congrArg (fun t => t ≫ (V.hom ≫ c).appTop) hΓ
      _ = (Scheme.ΓSpecIso (.of K)).inv ≫
          ((V.hom ≫ c) ≫ Spec.map (CommRingCat.ofHom φ)).appTop :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => (Scheme.ΓSpecIso (.of K)).inv ≫ t)
            (Scheme.Hom.comp_appTop (V.hom ≫ c)
              (Spec.map (CommRingCat.ofHom φ))).symm)
      _ = _ := congrArg
        (fun t : V.left ⟶ Spec (.of K) => (Scheme.ΓSpecIso (.of K)).inv ≫ t.appTop)
          (Category.assoc _ _ _)
  let μ : rootsOfUnity n K :=
    Additive.toMul (show Additive (rootsOfUnity n K) from ζ)
  exact ConcreteCategory.congr_hom hrings ((μ : Kˣ) : K)

/-- In every cohomological degree, a base-field coordinate change acts
through its original map on the constant roots of unity. -/
theorem constantRootsOfUnityToKummerKernel_cohomologyBaseMap
    (c : X ⟶ Spec (.of K)) (φ : K →+* K) {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : K)) (i : ℕ)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (.of (Additive (rootsOfUnity n K)))) i) :
    Sheaf.H.map
        (constantRootsOfUnityToKummerKernel (c ≫ Spec.map (CommRingCat.ofHom φ)) n) i a =
      Sheaf.H.map (constantRootsOfUnityToKummerKernel c n) i
        (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
          (AddCommGrpCat.ofHom (restrictRootsOfUnity φ n).toAdditive)) i a) := by
  rw [← Sheaf.H.map_comp_apply,
    constantRootsOfUnityToKummerKernel_baseMap c φ hn hnK]

end EtaleCohomology
