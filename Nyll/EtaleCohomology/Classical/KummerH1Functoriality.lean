/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.KummerH1Kernel
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.ProperKummerH1
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Original degree-one Kummer comparison under scheme pullback

Both the original degree-zero Kummer boundary and original degree-one
coefficient inclusion commute with the actual inverse image of sheaves.
The original pullback on H¹(Gm) therefore restricts to its multiplication
kernels. The proved proper-scheme comparison retains these same maps,
including the original finite cyclic coefficient pullback.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem kummerBoundary_zero_exactPullback
    {n : ℕ} (hn : 0 < n) (hnY : IsUnit (n : Γ(Y, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 0) :
    etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf Y n) 1
        (Sheaf.H.δ (etaleKummerComplex_shortExact Y hn hnY) 0 1 rfl a) =
      Sheaf.H.δ ((etaleKummerComplex_shortExact Y hn hnY).map_of_exact
        (etaleAbelianPullback f)) 0 1 rfl
          (etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf Y) 0 a) := by
  let L := etaleAbelianPullback f
  let hS := etaleKummerComplex_shortExact Y hn hnY
  let z := ((etaleAbelianPullbackConstantIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))).inv
  change (Ext.mk₀ z).comp ((a.comp hS.extClass rfl).mapExactFunctor L) (zero_add 1) =
    ((Ext.mk₀ z).comp (a.mapExactFunctor L) (zero_add 0)).comp
      (hS.map_of_exact L).extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc (Ext.mk₀ z) (a.mapExactFunctor L)
    (hS.map_of_exact L).extClass (zero_add 0) rfl rfl).symm

/-- The actual original scheme pullback commutes with the original
Kummer class of every actual global unit. -/
theorem etaleKummerBoundary_zero_pullback
    {n : ℕ} (hn : 0 < n) (hnY : IsUnit (n : Γ(Y, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 0) :
    etaleRootsOfUnityCohomologyPullback f n 1
        (Sheaf.H.δ (etaleKummerComplex_shortExact Y hn hnY) 0 1 rfl a) =
      Sheaf.H.δ (etaleKummerComplex_shortExact X hn
        (by simpa only [map_natCast] using hnY.map f.appTop.hom)) 0 1 rfl
          (etaleMultiplicativeGroupCohomologyPullback f 0 a) := by
  have hnX : IsUnit (n : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hnY.map f.appTop.hom
  let hY := etaleKummerComplex_shortExact Y hn hnY
  let hX := etaleKummerComplex_shortExact X hn hnX
  let b := etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf Y) 0 a
  have hδ := Sheaf.H.δ_naturality 0 1 rfl
    (hY.map_of_exact (etaleAbelianPullback f)) hX
    (etaleKummerPullbackComplex f n) b
  change Sheaf.H.δ hX 0 1 rfl
      (Sheaf.H.map (etaleMultiplicativeGroupPullback f) 0 b) =
    Sheaf.H.map (etaleRootsOfUnityPullback f n) 1
      (Sheaf.H.δ (hY.map_of_exact (etaleAbelianPullback f)) 0 1 rfl b) at hδ
  exact (congrArg (Sheaf.H.map (etaleRootsOfUnityPullback f n) 1)
    (kummerBoundary_zero_exactPullback f hn hnY a)).trans hδ.symm

/-- The original Kummer inclusion on degree-one cohomology commutes
with actual scheme pullback. -/
theorem etaleRootsOfUnityH1ToMultiplicativeGroup_pullback
    (n : ℕ) (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) 1) :
    etaleRootsOfUnityH1ToMultiplicativeGroup X n
        (etaleRootsOfUnityCohomologyPullback f n 1 a) =
      etaleMultiplicativeGroupCohomologyPullback f 1
        (etaleRootsOfUnityH1ToMultiplicativeGroup Y n a) := by
  change Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) 1
      (Sheaf.H.map (etaleRootsOfUnityPullback f n) 1
        (etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf Y n) 1 a)) =
    Sheaf.H.map (etaleMultiplicativeGroupPullback f) 1
      (etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf Y) 1
        (Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower Y n)) 1 a))
  rw [etaleAbelianCohomologyPullbackMap_naturality,
    ← Sheaf.H.map_comp_apply, etaleRootsOfUnityPullback_ι,
    Sheaf.H.map_comp_apply]

/-- The original scheme pullback on H¹(Gm), restricted to its actual
multiplication kernel. -/
def etaleKummerH1PowerKernelPullback (n : ℕ) :
    (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1) n).ker →+
    (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) n).ker where
  toFun a := ⟨etaleMultiplicativeGroupCohomologyPullback f 1 a.val, by
    change n • etaleMultiplicativeGroupCohomologyPullback f 1 a.val = 0
    rw [← map_nsmul]
    exact (congrArg (etaleMultiplicativeGroupCohomologyPullback f 1) a.property).trans
      (map_zero (etaleMultiplicativeGroupCohomologyPullback f 1))⟩
  map_zero' := Subtype.ext (map_zero (etaleMultiplicativeGroupCohomologyPullback f 1))
  map_add' a b := Subtype.ext
    (map_add (etaleMultiplicativeGroupCohomologyPullback f 1) a.val b.val)

/-- The torsion pullback retains the original ambient cohomology map. -/
theorem etaleKummerH1PowerKernelPullback_val (n : ℕ)
    (a : (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1) n).ker) :
    (etaleKummerH1PowerKernelPullback f n a).val =
      etaleMultiplicativeGroupCohomologyPullback f 1 a.val := rfl

/-- The original torsion pullbacks commute with the original
consecutive prime-power torsion transitions. -/
theorem etaleKummerH1PowerKernelPullback_transition (ℓ n : ℕ)
    (a : (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1)
        (ℓ ^ ((n + 1) + 1))).ker) :
    etaleKummerH1PowerKernelPullback f (ℓ ^ (n + 1))
        (ellPowerKummerH1PowerKernelTransition Y ℓ n a) =
      ellPowerKummerH1PowerKernelTransition X ℓ n
        (etaleKummerH1PowerKernelPullback f (ℓ ^ ((n + 1) + 1)) a) := by
  apply Subtype.ext
  exact map_nsmul (etaleMultiplicativeGroupCohomologyPullback f 1) ℓ a.val

variable {K : Type u} [Field K] [IsAlgClosed K]
  [IsIntegral X] [IsIntegral Y]

/-- The native degree-one comparison is natural for every original
scheme morphism between proper integral schemes. The morphism need not
preserve the displayed structure maps. -/
theorem properIntegralKummerH1EquivPowerKernel_pullback
    (cX : X ⟶ Spec (CommRingCat.of K)) [IsProper cX]
    (cY : Y ⟶ Spec (CommRingCat.of K)) [IsProper cY]
    {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) 1) :
    properIntegralKummerH1EquivPowerKernel cX hn hnK
        (etaleRootsOfUnityCohomologyPullback f n 1 a) =
      etaleKummerH1PowerKernelPullback f n
        (properIntegralKummerH1EquivPowerKernel cY hn hnK a) := by
  apply Subtype.ext
  exact etaleRootsOfUnityH1ToMultiplicativeGroup_pullback f n a

/-- With the original common structural coefficient map, the original
finite cyclic pullback becomes the original torsion pullback on H¹(Gm). -/
theorem properIntegralFiniteLevelH1EquivPowerKernel_pullback
    (c : Y ⟶ Spec (CommRingCat.of K)) [IsProper c] [IsProper (f ≫ c)]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    (n : ℕ) (a : finiteLevelCohomology Y ℓ n 1) :
    properIntegralFiniteLevelH1EquivPowerKernel (f ≫ c) ℓ hℓ n
        (finiteLevelCohomologyPullback ℓ f n 1 a) =
      etaleKummerH1PowerKernelPullback f (ℓ ^ (n + 1))
        (properIntegralFiniteLevelH1EquivPowerKernel c ℓ hℓ n a) := by
  apply Subtype.ext
  rw [properIntegralFiniteLevelH1EquivPowerKernel_apply,
    finiteLevelKummerCohomologyEquiv_pullback,
    etaleRootsOfUnityH1ToMultiplicativeGroup_pullback,
    etaleKummerH1PowerKernelPullback_val,
    properIntegralFiniteLevelH1EquivPowerKernel_apply]

end EtaleCohomology
