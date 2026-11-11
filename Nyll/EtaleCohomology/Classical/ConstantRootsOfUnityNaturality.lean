/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianPullbackConstants
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.KummerPowerTransition
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Naturality of the original constant roots comparison

The original structural map from constant roots to the Kummer kernel commutes
with scheme pullback and with the existing roots power maps. The existing
compatible primitive-root coordinates therefore identify the original finite
cyclic coefficient reductions with the actual Kummer kernel transitions.
No new roots are chosen.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X Y : Scheme.{u}}

private theorem constantSource_pushforward_ext
    (f : X ⟶ Y) (A : AddCommGrpCat.{u})
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ F)
    (b : F ⟶ (etaleAbelianPushforward f).obj G)
    (q : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶
      (etaleAbelianPushforward f).obj H) (r : H ⟶ G)
    (h : ∀ (V : Y.Etale) (x : A),
      b.hom.app (op V) (a.hom.app (op V)
        ((toSheafify Y.smallEtaleTopology
          ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op V) x)) =
      r.hom.app (op ((etaleBaseChange f).obj V))
        (q.hom.app (op V) ((toSheafify Y.smallEtaleTopology
          ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op V) x))) :
    a ≫ b = q ≫ (etaleAbelianPushforward f).map r := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext Y.smallEtaleTopology _ _
    ((etaleAbelianPushforward f).obj G).property
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro x
  exact h V.unop x

/-- The original map from constant roots to units, including its Kummer
inclusion, commutes with the original unit map to direct image. -/
private theorem constantRoots_units_pushforward
    (f : X ⟶ Y) (c : Y ⟶ Spec (.of K)) {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : K)) :
    (constantRootsOfUnityToKummerKernel c n ≫
        kernel.ι (etaleMultiplicativeGroupPower Y n)) ≫
          etaleMultiplicativeGroupToPushforward f =
      (etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
        ((etaleAbelianPullbackConstantIso f).hom.app
          (.of (Additive (rootsOfUnity n K)))) ≫
            (etaleAbelianPushforward f).map
              (constantRootsOfUnityToKummerKernel (f ≫ c) n ≫
                kernel.ι (etaleMultiplicativeGroupPower X n)) := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let CY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let CX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let MY := etaleMultiplicativeGroupSheaf Y
  let MX := etaleMultiplicativeGroupSheaf X
  let bY : CY ⟶ MY := constantRootsOfUnityToKummerKernel c n ≫
    kernel.ι (etaleMultiplicativeGroupPower Y n)
  let bX : CX ⟶ MX := constantRootsOfUnityToKummerKernel (f ≫ c) n ≫
    kernel.ι (etaleMultiplicativeGroupPower X n)
  let T := etaleMultiplicativeGroupToPushforward f
  let q : CY ⟶ (etaleAbelianPushforward f).obj CX :=
    (etaleAbelianPullbackPushforwardAdjunction f).homEquiv CY CX
      ((etaleAbelianPullbackConstantIso f).hom.app A)
  apply constantSource_pushforward_ext f A MY MX CX bY T q bX
  intro V
  refine fun (ζ : Additive (rootsOfUnity n K)) => ?_
  let W : X.Etale := (etaleBaseChange f).obj V
  let ηY : A ⟶ CY.obj.obj (op V) :=
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op V)
  let ηX : A ⟶ CX.obj.obj (op W) :=
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op W)
  have hq : ηY ≫ q.hom.app (op V) = ηX :=
    etaleAbelianPullbackConstantIso_hom_section f A V
  have hY : bY.hom.app (op V) (ηY ζ) =
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (.of K)).inv ≫ (V.hom ≫ c).appTop).hom.toMonoidHom)
          (ζ.toMul : Kˣ)) :=
    constantRootsOfUnityKummerKernelIso_generator c hn hnK V ζ.toMul
  have hX : bX.hom.app (op W) (ηX ζ) =
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (.of K)).inv ≫ (W.hom ≫ (f ≫ c)).appTop).hom.toMonoidHom)
          (ζ.toMul : Kˣ)) :=
    constantRootsOfUnityKummerKernelIso_generator (f ≫ c) hn hnK W ζ.toMul
  refine (congrArg (T.hom.app (op V)) hY).trans ?_
  refine Eq.trans ?_ (hX.symm.trans
    (congrArg (bX.hom.app (op W)) (ConcreteCategory.congr_hom hq ζ).symm))
  apply Additive.toMul.injective
  apply Units.ext
  have hbase : pullback.fst V.hom f ≫ (V.hom ≫ c) =
      pullback.snd V.hom f ≫ (f ≫ c) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t : pullback V.hom f ⟶ Y => t ≫ c)
        (pullback.condition (f := V.hom) (g := f))).trans (Category.assoc _ _ _))
  have hrings :
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (V.hom ≫ c).appTop) ≫
          (pullback.fst V.hom f).appTop =
        (Scheme.ΓSpecIso (.of K)).inv ≫
          (pullback.snd V.hom f ≫ (f ≫ c)).appTop := by
    calc
      _ = (Scheme.ΓSpecIso (.of K)).inv ≫
          ((V.hom ≫ c).appTop ≫ (pullback.fst V.hom f).appTop) :=
        Category.assoc _ _ _
      _ = (Scheme.ΓSpecIso (.of K)).inv ≫
          (pullback.fst V.hom f ≫ (V.hom ≫ c)).appTop :=
        congrArg (fun t : Γ(Spec (.of K), ⊤) ⟶ Γ(pullback V.hom f, ⊤) =>
          (Scheme.ΓSpecIso (.of K)).inv ≫ t)
            (Scheme.Hom.comp_appTop (pullback.fst V.hom f) (V.hom ≫ c)).symm
      _ = _ := congrArg (fun t => (Scheme.ΓSpecIso (.of K)).inv ≫ t.appTop) hbase
  exact ConcreteCategory.congr_hom hrings ((ζ.toMul : Kˣ) : K)

/-- Scheme pullback preserves the actual structural map from constant roots
to the original Kummer kernel. -/
theorem constantRootsOfUnityToKummerKernel_pullback
    (f : X ⟶ Y) (c : Y ⟶ Spec (.of K)) {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : K)) :
    (etaleAbelianPullback f).map (constantRootsOfUnityToKummerKernel c n) ≫
        etaleRootsOfUnityPullback f n =
      (etaleAbelianPullbackConstantIso f).hom.app
        (.of (Additive (rootsOfUnity n K))) ≫
          constantRootsOfUnityToKummerKernel (f ≫ c) n := by
  let L := etaleAbelianPullback f
  let adj := etaleAbelianPullbackPushforwardAdjunction f
  let A := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let e := (etaleAbelianPullbackConstantIso f).app A
  let bY := constantRootsOfUnityToKummerKernel c n ≫
    kernel.ι (etaleMultiplicativeGroupPower Y n)
  let bX := constantRootsOfUnityToKummerKernel (f ≫ c) n ≫
    kernel.ι (etaleMultiplicativeGroupPower X n)
  have h := adj.homEquiv_naturality_right_square bY
    (etaleMultiplicativeGroupToPushforward f) (adj.homEquiv _ _ e.hom) bX
      (constantRoots_units_pushforward f c hn hnK)
  rw [Equiv.symm_apply_apply] at h
  have hu : L.map bY ≫ etaleMultiplicativeGroupPullback f = e.hom ≫ bX := h
  apply (cancel_mono (kernel.ι (etaleMultiplicativeGroupPower X n))).mp
  calc
    _ = L.map (constantRootsOfUnityToKummerKernel c n) ≫
        (L.map (kernel.ι (etaleMultiplicativeGroupPower Y n)) ≫
          etaleMultiplicativeGroupPullback f) := by
      rw [Category.assoc, etaleRootsOfUnityPullback_ι]
    _ = L.map bY ≫ etaleMultiplicativeGroupPullback f := by
      rw [Functor.map_comp, Category.assoc]
    _ = e.hom ≫ bX := hu
    _ = _ := (Category.assoc _ _ _).symm

/-- For roots of invertible order over an algebraically closed field,
the original Kummer inverse-image coefficient map is an isomorphism.
The original structural constant-root square identifies this very map. -/
theorem etaleRootsOfUnityPullback_isIso
    (f : X ⟶ Y) (c : Y ⟶ Spec (.of K)) {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : K)) :
    IsIso (etaleRootsOfUnityPullback f n) := by
  have : IsIso (constantRootsOfUnityToKummerKernel c n) :=
    inferInstanceAs (IsIso (constantRootsOfUnityKummerKernelIso c hn hnK).hom)
  have : IsIso (constantRootsOfUnityToKummerKernel (f ≫ c) n) :=
    inferInstanceAs (IsIso (constantRootsOfUnityKummerKernelIso (f ≫ c) hn hnK).hom)
  have : IsIso ((etaleAbelianPullback f).map (constantRootsOfUnityToKummerKernel c n) ≫
      etaleRootsOfUnityPullback f n) := by
    rw [constantRootsOfUnityToKummerKernel_pullback f c hn hnK]
    exact inferInstance
  exact IsIso.of_isIso_comp_left
    ((etaleAbelianPullback f).map (constantRootsOfUnityToKummerKernel c n))
    (etaleRootsOfUnityPullback f n)

/-- The existing roots power map agrees with the original Kummer kernel
transition under the structural constant-root comparison. -/
theorem constantRootsOfUnityToKummerKernel_powerTransition
    (c : X ⟶ Spec (.of K)) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnK : IsUnit (n : K)) (hmK : IsUnit (m : K)) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom
          (rootsOfUnityPowerTransition K (m := n) (n := n * m) ⟨m, rfl⟩).toAdditive) ≫
      constantRootsOfUnityToKummerKernel c n =
    constantRootsOfUnityToKummerKernel c (n * m) ≫
      etaleKummerPowerTransition X n m := by
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n * m) K))
  let B := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let ρ : A ⟶ B := AddCommGrpCat.ofHom
    (rootsOfUnityPowerTransition K (m := n) (n := n * m) ⟨m, rfl⟩).toAdditive
  let V : X.Etale := ⊤_ X.Etale
  let ηA := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op V)
  let ηB := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj B)).app (op V)
  have hη : ηA ≫ (C.map ρ).hom.app (op V) = ρ ≫ ηB := by
    have h := congrArg (fun t => t.app (op V))
      (toSheafify_naturality X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map ρ))
    exact h.symm
  apply (cancel_mono (kernel.ι (etaleMultiplicativeGroupPower X n))).mp
  rw [Category.assoc, Category.assoc, etaleKummerPowerTransition_ι]
  apply ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
    (terminalIsTerminal : IsTerminal V)).homEquiv A
      (etaleMultiplicativeGroupSheaf X)).injective
  apply ConcreteCategory.hom_ext
  refine fun (ζ : Additive (rootsOfUnity (n * m) K)) => ?_
  let k := kernel.ι (etaleMultiplicativeGroupPower X n)
  let kN := kernel.ι (etaleMultiplicativeGroupPower X (n * m))
  let b := constantRootsOfUnityToKummerKernel c n
  let bN := constantRootsOfUnityToKummerKernel c (n * m)
  change k.hom.app (op V) (b.hom.app (op V) ((C.map ρ).hom.app (op V) (ηA ζ))) =
    (etaleMultiplicativeGroupPower X m).hom.app (op V)
      (kN.hom.app (op V) (bN.hom.app (op V) (ηA ζ)))
  have hleft := constantRootsOfUnityKummerKernelIso_generator c hn hnK V
    (ρ ζ).toMul
  have hnmK : IsUnit ((n * m : ℕ) : K) := by
    simpa only [Nat.cast_mul] using hnK.mul hmK
  have hright := constantRootsOfUnityKummerKernelIso_generator c
    (Nat.mul_pos hn hm) hnmK V ζ.toMul
  have hηζ := ConcreteCategory.congr_hom hη ζ
  refine (congrArg (fun t => k.hom.app (op V) (b.hom.app (op V) t)) hηζ).trans ?_
  refine hleft.trans ?_
  refine Eq.trans ?_ (congrArg ((etaleMultiplicativeGroupPower X m).hom.app (op V))
    hright).symm
  apply Additive.toMul.injective
  change Units.map
      (((Scheme.ΓSpecIso (.of K)).inv ≫ (V.hom ≫ c).appTop).hom.toMonoidHom)
        ((ζ.toMul : Kˣ) ^ (n * m / n)) =
    (Units.map
      (((Scheme.ΓSpecIso (.of K)).inv ≫ (V.hom ≫ c).appTop).hom.toMonoidHom)
        (ζ.toMul : Kˣ)) ^ m
  rw [Nat.mul_div_cancel_left m hn, map_pow]

/-- Equality transport of the exponent uses the original power transition,
retaining the original divisible-exponent roots map. -/
private theorem constantRoots_powerTransition_of_eq
    (c : X ⟶ Spec (.of K)) {n m N : ℕ} (hN : N = n * m)
    (hn : 0 < n) (hm : 0 < m) (hnK : IsUnit (n : K)) (hmK : IsUnit (m : K)) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom
          (rootsOfUnityPowerTransition K (m := n) (n := N) ⟨m, hN⟩).toAdditive) ≫
      constantRootsOfUnityToKummerKernel c n =
    constantRootsOfUnityToKummerKernel c N ≫
      eqToHom (congrArg (etaleRootsOfUnitySheaf X) hN) ≫
        etaleKummerPowerTransition X n m := by
  subst N
  simpa only [eqToHom_refl, Category.id_comp] using
    constantRootsOfUnityToKummerKernel_powerTransition c hn hm hnK hmK

/-- The original structural root map intertwines scheme pullback in every
cohomological degree, using the original constant-coefficient pullback. -/
theorem constantRootsOfUnityToKummerKernel_cohomologyPullback
    (f : X ⟶ Y) (c : Y ⟶ Spec (.of K)) {n : ℕ}
    (hn : 0 < n) (hnK : IsUnit (n : K)) (i : ℕ)
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (.of (Additive (rootsOfUnity n K)))) i) :
    Sheaf.H.map (constantRootsOfUnityToKummerKernel (f ≫ c) n) i
        (constantCohomologyPullback f (.of (Additive (rootsOfUnity n K))) i a) =
      etaleRootsOfUnityCohomologyPullback f n i
        (Sheaf.H.map (constantRootsOfUnityToKummerKernel c n) i a) := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let CY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let e := (etaleAbelianPullbackConstantIso f).app A
  let bY := constantRootsOfUnityToKummerKernel c n
  let bX := constantRootsOfUnityToKummerKernel (f ≫ c) n
  let z := etaleAbelianCohomologyPullbackMap f CY i a
  have hnat := etaleAbelianCohomologyPullbackMap_naturality f bY i a
  change Sheaf.H.map bX i (Sheaf.H.map e.hom i z) =
    Sheaf.H.map (etaleRootsOfUnityPullback f n) i
      (etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf Y n) i
        (Sheaf.H.map bY i a))
  calc
    _ = Sheaf.H.map (e.hom ≫ bX) i z :=
      (Sheaf.H.map_comp_apply e.hom bX z).symm
    _ = Sheaf.H.map
        ((etaleAbelianPullback f).map bY ≫ etaleRootsOfUnityPullback f n) i z :=
      congrArg (fun t => Sheaf.H.map t i z)
        (constantRootsOfUnityToKummerKernel_pullback f c hn hnK).symm
    _ = Sheaf.H.map (etaleRootsOfUnityPullback f n) i
        (Sheaf.H.map ((etaleAbelianPullback f).map bY) i z) :=
      Sheaf.H.map_comp_apply _ _ z
    _ = _ := congrArg (Sheaf.H.map (etaleRootsOfUnityPullback f n) i) hnat.symm

open EtaleCohomology.Classical

/-- The existing coherent primitive-root coordinates, followed by the actual
structural map to the Kummer kernel. -/
def ellPowerConstantKummerKernelIso
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (ellPowerCoefficients ℓ n) ≅ etaleRootsOfUnitySheaf X (ℓ ^ (n + 1)) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).mapIso
      (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddCommGrpIso ≪≫
    constantRootsOfUnityKummerKernelIso c (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))

/-- On every original constant generator, the coherent prime-power
comparison is the structural image of that same coherent root. -/
theorem ellPowerConstantKummerKernelIso_generator
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    (n : ℕ) (V : X.Etale) (a : ellPowerCoefficients.{u} ℓ n) :
    (kernel.ι (etaleMultiplicativeGroupPower X (ℓ ^ (n + 1)))).hom.app (op V)
      ((ellPowerConstantKummerKernelIso c ℓ hℓ n).hom.hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (ellPowerCoefficients.{u} ℓ n))).app (op V) a)) =
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (.of K)).inv ≫ (V.hom ≫ c).appTop).hom.toMonoidHom)
        ((ellPowerRootsCoefficientEquiv K ℓ hℓ n a).toMul : Kˣ)) := by
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let A := ellPowerCoefficients.{u} ℓ n
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K))
  let ρ : A ⟶ B := (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddCommGrpIso.hom
  let ηA := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op V)
  let ηB := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj B)).app (op V)
  have hη : ηA ≫ (C.map ρ).hom.app (op V) = ρ ≫ ηB := by
    have h := congrArg (fun t => t.app (op V))
      (toSheafify_naturality X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map ρ))
    exact h.symm
  have hn := ConcreteCategory.congr_hom hη a
  change (C.map ρ).hom.app (op V) (ηA a) = ηB (ρ a) at hn
  let hp := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  let hN : IsUnit ((ℓ ^ (n + 1) : ℕ) : K) := by
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  change (kernel.ι (etaleMultiplicativeGroupPower X (ℓ ^ (n + 1)))).hom.app (op V)
    ((constantRootsOfUnityKummerKernelIso c hp hN).hom.hom.app (op V)
      ((C.map ρ).hom.app (op V) (ηA a))) = _
  rw [hn]
  exact constantRootsOfUnityKummerKernelIso_generator c hp hN V
    (ellPowerRootsCoefficientEquiv K ℓ hℓ n a).toMul

/-- Consecutive Kummer kernels use the original power transition after the
literal equality of their exponents. -/
def ellPowerKummerKernelTransition (X : Scheme.{u}) (ℓ n : ℕ) :
    etaleRootsOfUnitySheaf X (ℓ ^ ((n + 1) + 1)) ⟶
      etaleRootsOfUnitySheaf X (ℓ ^ (n + 1)) :=
  eqToHom (congrArg (etaleRootsOfUnitySheaf X) (pow_succ ℓ (n + 1))) ≫
    etaleKummerPowerTransition X (ℓ ^ (n + 1)) ℓ

/-- Original cyclic reduction and the original Kummer power transition agree
under the same coherent primitive-root coordinates used for H¹. -/
theorem ellPowerConstantKummerKernelIso_reduction
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom (ellPowerReduction ℓ n)) ≫
          (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom =
      (ellPowerConstantKummerKernelIso c ℓ hℓ (n + 1)).hom ≫
        ellPowerKummerKernelTransition X ℓ n := by
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let en : ellPowerCoefficients.{u} ℓ n ≅
      AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K)) :=
    (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddCommGrpIso
  let eN : ellPowerCoefficients.{u} ℓ (n + 1) ≅
      AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ ((n + 1) + 1)) K)) :=
    (ellPowerRootsCoefficientEquiv K ℓ hℓ (n + 1)).toAddCommGrpIso
  let r := AddCommGrpCat.ofHom (ellPowerReduction.{u} ℓ n)
  let ρ := AddCommGrpCat.ofHom
    (rootsOfUnityPowerTransition K (m := ℓ ^ (n + 1)) (n := ℓ ^ ((n + 1) + 1))
      ⟨ℓ, pow_succ ℓ (n + 1)⟩).toAdditive
  have he : r ≫ en.hom = eN.hom ≫ ρ := by
    apply ConcreteCategory.hom_ext
    refine fun (a : ellPowerCoefficients.{u} ℓ (n + 1)) => ?_
    exact (ellPowerRootsCoefficientEquiv_reduction K ℓ hℓ n a).symm
  let b := constantRootsOfUnityToKummerKernel c (ℓ ^ (n + 1))
  let bN := constantRootsOfUnityToKummerKernel c (ℓ ^ ((n + 1) + 1))
  let t := ellPowerKummerKernelTransition X ℓ n
  have hb : C.map ρ ≫ b = bN ≫ t :=
    constantRoots_powerTransition_of_eq c (pow_succ ℓ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1)) (Fact.out : ℓ.Prime).pos
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)) hℓ
  change C.map r ≫ (C.map en.hom ≫ b) = (C.map eN.hom ≫ bN) ≫ t
  calc
    _ = C.map (r ≫ en.hom) ≫ b := by rw [Functor.map_comp, Category.assoc]
    _ = C.map (eN.hom ≫ ρ) ≫ b := congrArg (fun s => C.map s ≫ b) he
    _ = C.map eN.hom ≫ (C.map ρ ≫ b) := by rw [Functor.map_comp, Category.assoc]
    _ = C.map eN.hom ≫ (bN ≫ t) := congrArg (fun s => C.map eN.hom ≫ s) hb
    _ = _ := (Category.assoc _ _ _).symm

/-- The original finite-level cohomology is the cohomology of the actual
Kummer kernel in the existing coherent roots coordinates. -/
def finiteLevelKummerCohomologyEquiv
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n i : ℕ) :
    finiteLevelCohomology X ℓ n i ≃+
      Sheaf.H.{u} (etaleRootsOfUnitySheaf X (ℓ ^ (n + 1))) i :=
  ((Sheaf.functorH X.smallEtaleTopology i).mapIso
    (ellPowerConstantKummerKernelIso c ℓ hℓ n)).addCommGroupIsoToAddEquiv

/-- The finite-level comparison first uses the original coherent coefficient
map, then the original structural map to the Kummer kernel. -/
theorem finiteLevelKummerCohomologyEquiv_apply
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n i : ℕ)
    (a : finiteLevelCohomology X ℓ n i) :
    finiteLevelKummerCohomologyEquiv c ℓ hℓ n i a =
      Sheaf.H.map (constantRootsOfUnityToKummerKernel c (ℓ ^ (n + 1))) i
        (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
          (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddCommGrpIso.hom) i a) :=
  Sheaf.H.map_comp_apply _ _ a

/-- The comparison retains the original finite-level reduction in every
degree, including the H² transition of the original Kummer boundary. -/
theorem finiteLevelKummerCohomologyEquiv_reduction
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n i : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) i) :
    finiteLevelKummerCohomologyEquiv c ℓ hℓ n i (finiteLevelReduction X ℓ n i a) =
      Sheaf.H.map (ellPowerKummerKernelTransition X ℓ n) i
        (finiteLevelKummerCohomologyEquiv c ℓ hℓ (n + 1) i a) := by
  let H := Sheaf.functorH X.smallEtaleTopology i
  let r := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
    (AddCommGrpCat.ofHom (ellPowerReduction.{u} ℓ n))
  let en := (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom
  let eN := (ellPowerConstantKummerKernelIso c ℓ hℓ (n + 1)).hom
  let t := ellPowerKummerKernelTransition X ℓ n
  have he : r ≫ en = eN ≫ t := ellPowerConstantKummerKernelIso_reduction c ℓ hℓ n
  change (H.map r ≫ H.map en) a = (H.map eN ≫ H.map t) a
  exact ConcreteCategory.congr_hom
    ((H.map_comp r en).symm.trans ((congrArg H.map he).trans (H.map_comp eN t))) a

/-- Scheme pullback on the original finite cyclic cohomology agrees with
pullback on the actual Kummer kernel, in every degree and at every level. -/
theorem finiteLevelKummerCohomologyEquiv_pullback
    (f : X ⟶ Y) (c : Y ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : K)) (n i : ℕ) (a : finiteLevelCohomology Y ℓ n i) :
    finiteLevelKummerCohomologyEquiv (f ≫ c) ℓ hℓ n i
        (finiteLevelCohomologyPullback ℓ f n i a) =
      etaleRootsOfUnityCohomologyPullback f (ℓ ^ (n + 1)) i
        (finiteLevelKummerCohomologyEquiv c ℓ hℓ n i a) := by
  let A := ellPowerCoefficients.{u} ℓ n
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K))
  let α : A ⟶ B := (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddCommGrpIso.hom
  let CY := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  let CX := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let bX := constantRootsOfUnityToKummerKernel (f ≫ c) (ℓ ^ (n + 1))
  let bY := constantRootsOfUnityToKummerKernel c (ℓ ^ (n + 1))
  have hnat := constantCohomologyPullback_naturality f A B α i a
  have hn : 0 < ℓ ^ (n + 1) := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  have hnK : IsUnit ((ℓ ^ (n + 1) : ℕ) : K) := by
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  calc
    _ = Sheaf.H.map bX i
        (Sheaf.H.map (CX.map α) i (constantCohomologyPullback f A i a)) :=
      finiteLevelKummerCohomologyEquiv_apply (f ≫ c) ℓ hℓ n i
        (finiteLevelCohomologyPullback ℓ f n i a)
    _ = Sheaf.H.map bX i
        (constantCohomologyPullback f B i (Sheaf.H.map (CY.map α) i a)) :=
      congrArg (Sheaf.H.map bX i) hnat
    _ = etaleRootsOfUnityCohomologyPullback f (ℓ ^ (n + 1)) i
        (Sheaf.H.map bY i (Sheaf.H.map (CY.map α) i a)) :=
      constantRootsOfUnityToKummerKernel_cohomologyPullback f c hn hnK i
        (Sheaf.H.map (CY.map α) i a)
    _ = _ := congrArg (etaleRootsOfUnityCohomologyPullback f (ℓ ^ (n + 1)) i)
      (finiteLevelKummerCohomologyEquiv_apply c ℓ hℓ n i a).symm

end EtaleCohomology
