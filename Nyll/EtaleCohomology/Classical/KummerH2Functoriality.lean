/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.KummerH1AdditiveStructures
public import Nyll.EtaleCohomology.Classical.KummerH2KernelPowerTransition
public import Nyll.EtaleCohomology.Classical.FieldKummer
public import Nyll.EtaleCohomology.Classical.KummerH2Kernel
public import Nyll.EtaleCohomology.Classical.KummerPowerTransition
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerPullbackPowerTransition
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Functoriality of the original degree-two Kummer kernel

The power transition on the original roots-of-unity sheaves restricts to
the original H² kernels. Under the Kummer boundary equivalence, it is the
quotient reduction H¹(Gm)/(n*m) → H¹(Gm)/n. In particular these kernel
transitions are surjective for invertible exponents. Scheme pullback also
restricts to the kernels and corresponds to the actual pullback on H¹(Gm)
modulo n. The comparison retains both original cohomology maps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

attribute [local instance] kummerFunctorialityH1AddZero
  kummerFunctorialityH1IsAddCommutative kummerFunctorialityH1QuotientAddZero

/-- Reduction of the original H¹(Gm) quotient leaves its representing
cohomology class unchanged. -/
def etaleKummerH1QuotientReduction (X : Scheme.{u}) (n m : ℕ) :
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom
        (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) (n * m)).range) →+
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom
        (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) n).range) := by
  let A := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1
  refine QuotientAddGroup.map (nsmulAddMonoidHom (α := A) (n * m)).range
    (nsmulAddMonoidHom (α := A) n).range (AddMonoidHom.id A) ?_
  rintro a ⟨b, hb⟩
  refine ⟨m • b, ?_⟩
  change n • (m • b) = a
  change (n * m) • b = a at hb
  exact (mul_smul n m b).symm.trans hb

/-- Quotient reduction retains the original H¹(Gm) representative. -/
theorem etaleKummerH1QuotientReduction_mk
    (X : Scheme.{u}) (n m : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :
    etaleKummerH1QuotientReduction X n m
        (QuotientAddGroup.mk
          (s := (nsmulAddMonoidHom
            (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) (n * m)).range) a) =
      QuotientAddGroup.mk
        (s := (nsmulAddMonoidHom
          (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) n).range) a := rfl

/-- The original quotient reduction is surjective in every pair of
exponents, with the same H¹(Gm) representative giving a lift. -/
theorem etaleKummerH1QuotientReduction_surjective
    (X : Scheme.{u}) (n m : ℕ) :
    Function.Surjective (etaleKummerH1QuotientReduction X n m) := by
  intro a
  refine Quotient.inductionOn' a ?_
  intro b
  exact ⟨QuotientAddGroup.mk
    (s := (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) (n * m)).range) b,
    etaleKummerH1QuotientReduction_mk X n m b⟩

/-- The original Kummer boundary equivalence identifies quotient
reduction with the actual power transition on the H² kernel. -/
theorem etaleKummerH1QuotientEquivH2Kernel_reduction
    (X : Scheme.{u}) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnX : IsUnit (n : Γ(X, ⊤))) (hmX : IsUnit (m : Γ(X, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom (n * m) :
        Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 →+
          Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1).range) :
    etaleKummerH2KernelPowerTransition X n m
        (etaleKummerH1QuotientEquivH2Kernel X (Nat.mul_pos hn hm)
          (by simpa only [Nat.cast_mul] using hnX.mul hmX) a) =
      etaleKummerH1QuotientEquivH2Kernel X hn hnX
        (etaleKummerH1QuotientReduction X n m a) := by
  refine Quotient.inductionOn' a ?_
  intro b
  rw [etaleKummerH1QuotientReduction_mk X n m b]
  apply Subtype.ext
  rw [etaleKummerH2KernelPowerTransition_val,
    etaleKummerH1QuotientEquivH2Kernel_mk,
    etaleKummerH1QuotientEquivH2Kernel_mk]
  exact etaleKummerPowerTransition_connecting X hn hm hnX hmX 1 b

/-- For invertible exponents, the actual power transition on the original
H² kernels is surjective. -/
theorem etaleKummerH2KernelPowerTransition_surjective
    (X : Scheme.{u}) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnX : IsUnit (n : Γ(X, ⊤))) (hmX : IsUnit (m : Γ(X, ⊤))) :
    Function.Surjective (etaleKummerH2KernelPowerTransition X n m) := by
  intro a
  obtain ⟨b, hb⟩ := (etaleKummerH1QuotientEquivH2Kernel X hn hnX).surjective a
  obtain ⟨c, hc⟩ := etaleKummerH1QuotientReduction_surjective X n m b
  refine ⟨etaleKummerH1QuotientEquivH2Kernel X (Nat.mul_pos hn hm)
    (by simpa only [Nat.cast_mul] using hnX.mul hmX) c, ?_⟩
  rw [etaleKummerH1QuotientEquivH2Kernel_reduction X hn hm hnX hmX, hc, hb]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual H² coefficient map commutes with the original pullback of
units and roots of unity. -/
theorem etaleRootsOfUnityH2ToMultiplicativeGroup_pullback
    (n : ℕ) (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) 2) :
    etaleRootsOfUnityH2ToMultiplicativeGroup X n
        (etaleRootsOfUnityCohomologyPullback f n 2 a) =
      etaleMultiplicativeGroupCohomologyPullback f 2
        (etaleRootsOfUnityH2ToMultiplicativeGroup Y n a) := by
  change Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) 2
      (Sheaf.H.map (etaleRootsOfUnityPullback f n) 2
        (etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf Y n) 2 a)) =
    Sheaf.H.map (etaleMultiplicativeGroupPullback f) 2
      (etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf Y) 2
        (Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower Y n)) 2 a))
  rw [etaleAbelianCohomologyPullbackMap_naturality,
    ← Sheaf.H.map_comp_apply, etaleRootsOfUnityPullback_ι,
    Sheaf.H.map_comp_apply]

/-- Original scheme pullback restricted to the actual H² Kummer kernels. -/
def etaleKummerH2KernelPullback (n : ℕ) :
    (etaleRootsOfUnityH2ToMultiplicativeGroup Y n).ker →+
      (etaleRootsOfUnityH2ToMultiplicativeGroup X n).ker :=
  (((etaleRootsOfUnityCohomologyPullback f n 2).comp
    (etaleRootsOfUnityH2ToMultiplicativeGroup Y n).ker.subtype).codRestrict
      (etaleRootsOfUnityH2ToMultiplicativeGroup X n).ker fun a => by
        change etaleRootsOfUnityH2ToMultiplicativeGroup X n
          (etaleRootsOfUnityCohomologyPullback f n 2 a.val) = 0
        rw [etaleRootsOfUnityH2ToMultiplicativeGroup_pullback, a.property, map_zero])

/-- The restricted pullback retains the actual map on roots-of-unity H². -/
theorem etaleKummerH2KernelPullback_val
    (n : ℕ) (a : (etaleRootsOfUnityH2ToMultiplicativeGroup Y n).ker) :
    (etaleKummerH2KernelPullback f n a).val =
      etaleRootsOfUnityCohomologyPullback f n 2 a.val := rfl

/-- Pullback is a morphism of the original H² Kummer-kernel systems,
with the actual power transitions on both schemes. -/
theorem etaleKummerH2KernelPullback_powerTransition
    (n m : ℕ) (a : (etaleRootsOfUnityH2ToMultiplicativeGroup Y (n * m)).ker) :
    etaleKummerH2KernelPowerTransition X n m
        (etaleKummerH2KernelPullback f (n * m) a) =
      etaleKummerH2KernelPullback f n
        (etaleKummerH2KernelPowerTransition Y n m a) := by
  apply Subtype.ext
  rw [etaleKummerH2KernelPowerTransition_val,
    etaleKummerH2KernelPullback_val, etaleKummerH2KernelPullback_val,
    etaleKummerH2KernelPowerTransition_val]
  exact etaleRootsOfUnityCohomologyPullback_powerTransition f n m 2 a.val

/-- The original pullback on H¹(Gm) descends to its quotient by n. -/
def etaleKummerH1QuotientPullback (n : ℕ) :
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1 ⧸
      (nsmulAddMonoidHom
        (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1) n).range) →+
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom
        (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) n).range) := by
  let A := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1
  let B := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1
  let p : A →+ B := etaleMultiplicativeGroupCohomologyPullback f 1
  refine QuotientAddGroup.map (nsmulAddMonoidHom (α := A) n).range
    (nsmulAddMonoidHom (α := B) n).range p ?_
  rintro a ⟨b, hb⟩
  refine ⟨p b, ?_⟩
  change n • p b = p a
  change n • b = a at hb
  exact (map_nsmul p n b).symm.trans (congrArg p hb)

/-- The induced quotient pullback uses the original H¹(Gm) pullback on
representatives. -/
theorem etaleKummerH1QuotientPullback_mk
    (n : ℕ) (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1) :
    etaleKummerH1QuotientPullback f n
        (QuotientAddGroup.mk
          (s := (nsmulAddMonoidHom
            (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1) n).range) a) =
      QuotientAddGroup.mk
        (s := (nsmulAddMonoidHom
          (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) n).range)
        (etaleMultiplicativeGroupCohomologyPullback f 1 a) := rfl

/-- The Kummer kernel equivalence is natural for actual scheme pullback.
Invertibility on the source is supplied by the scheme map on global sections. -/
theorem etaleKummerH1QuotientEquivH2Kernel_pullback
    {n : ℕ} (hn : 0 < n) (hnY : IsUnit (n : Γ(Y, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1 ⧸
      (nsmulAddMonoidHom n :
        Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1 →+
          Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1).range) :
    etaleKummerH2KernelPullback f n
        (etaleKummerH1QuotientEquivH2Kernel Y hn hnY a) =
      etaleKummerH1QuotientEquivH2Kernel X hn
        (by simpa only [map_natCast] using hnY.map f.appTop.hom)
        (etaleKummerH1QuotientPullback f n a) := by
  refine Quotient.inductionOn' a ?_
  intro b
  rw [etaleKummerH1QuotientPullback_mk f n b]
  apply Subtype.ext
  rw [etaleKummerH2KernelPullback_val,
    etaleKummerH1QuotientEquivH2Kernel_mk,
    etaleKummerH1QuotientEquivH2Kernel_mk]
  exact etaleKummerBoundary_one_pullback f hn hnY b

end EtaleCohomology
