/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Laurent.CyclicCover
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerGeometricFiber

/-! # The actual Laurent square map and its root fibres -/

noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

/-- The ring map doubling Laurent exponents. -/
def laurentSquareMap (K : Type u) [Field K] :
    LaurentPolynomial K →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapDomainRingHom K (nsmulAddMonoidHom 2)

/-- The actual square morphism on the Laurent spectrum. -/
def laurentSquareProjection (K : Type u) [Field K] :
    Spec (.of (LaurentPolynomial K)) ⟶ Spec (.of (LaurentPolynomial K)) :=
  Spec.map (CommRingCat.ofHom (laurentSquareMap K))

/-- The Kummer square algebra in its actual root coordinate. -/
def laurentSquareRootEquiv (K : Type u) [Field K] :
    LaurentKummerAlgebra K 2 ≃+* LaurentPolynomial K :=
  (EtaleFundamentalGroups.Kummer.exists_cyclicLaurentRingEquiv
    (R := K) 2 (by decide)).choose

theorem laurentSquareRootEquiv_root (K : Type u) [Field K] :
    laurentSquareRootEquiv K
      (AdjoinRoot.root (X ^ 2 - C (LaurentPolynomial.T 1 : LaurentPolynomial K))) =
      LaurentPolynomial.T 1 :=
  (EtaleFundamentalGroups.Kummer.exists_cyclicLaurentRingEquiv
    (R := K) 2 (by decide)).choose_spec.1

theorem laurentSquareRootEquiv_comp_of (K : Type u) [Field K] :
    (laurentSquareRootEquiv K).toRingHom.comp
      (AdjoinRoot.of (X ^ 2 - C (LaurentPolynomial.T 1 : LaurentPolynomial K))) =
      laurentSquareMap K :=
  (EtaleFundamentalGroups.Kummer.exists_cyclicLaurentRingEquiv
    (R := K) 2 (by decide)).choose_spec.2

/-- The actual comparison of total spaces commutes with projection. -/
theorem laurentSquareRootSpec_triangle (K : Type u) [Field K] :
    Spec.map (CommRingCat.ofHom (laurentSquareRootEquiv K).toRingHom) ≫
      laurentKummerProjection K 2 = laurentSquareProjection K := by
  change Spec.map (CommRingCat.ofHom (laurentSquareRootEquiv K).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (AdjoinRoot.of (X ^ 2 - C (LaurentPolynomial.T 1 : LaurentPolynomial K)))) =
    Spec.map (CommRingCat.ofHom (laurentSquareMap K))
  rw [← Spec.map_comp]
  exact congrArg (fun f : LaurentPolynomial K →+* LaurentPolynomial K =>
    Spec.map (CommRingCat.ofHom f)) (laurentSquareRootEquiv_comp_of K)

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Algebra points of the actual square-map fibre. -/
def LaurentSquareFiberHom (a : Kˣ) :=
  {f : LaurentPolynomial K →+* L //
    f.comp (laurentSquareMap K) = laurentScalarEvaluation (L := L) a}

/-- Scheme points of the actual square-map fibre. -/
def LaurentSquareSchemeFiber (a : Kˣ) :=
  {f : Spec (.of L) ⟶ Spec (.of (LaurentPolynomial K)) //
    f ≫ laurentSquareProjection K = laurentKummerPoint (L := L) a}

/-- Affine scheme points are precisely the corresponding algebra points. -/
def laurentSquareSchemeFiberEquivHom (a : Kˣ) :
    LaurentSquareSchemeFiber (L := L) a ≃ LaurentSquareFiberHom (L := L) a where
  toFun f := ⟨(Spec.preimage f.val).hom, by
    have h := congrArg (fun g : Spec (.of L) ⟶ Spec (.of (LaurentPolynomial K)) =>
      (Spec.preimage g).hom) f.property
    simpa only [laurentSquareProjection, laurentKummerPoint, Spec.preimage_comp,
      Spec.preimage_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h⟩
  invFun f := ⟨Spec.map (CommRingCat.ofHom f.val), by
    change Spec.map (CommRingCat.ofHom f.val) ≫
      Spec.map (CommRingCat.ofHom (laurentSquareMap K)) =
      Spec.map (CommRingCat.ofHom (laurentScalarEvaluation (L := L) a))
    rw [← Spec.map_comp]
    exact congrArg (fun g : LaurentPolynomial K →+* L =>
      Spec.map (CommRingCat.ofHom g)) f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact Spec.map_preimage f.val
  right_inv f := by
    apply Subtype.ext
    exact congrArg (fun g : CommRingCat.of (LaurentPolynomial K) ⟶ CommRingCat.of L => g.hom)
      (Spec.preimage_map (CommRingCat.ofHom f.val))

/-- The explicit Laurent/Kummer equivalence compares the actual fibres. -/
def laurentSquareFiberHomEquivKummer (a : Kˣ) :
    LaurentSquareFiberHom (L := L) a ≃ LaurentKummerFiberHom (L := L) 2 a where
  toFun f := ⟨f.val.comp (laurentSquareRootEquiv K).toRingHom, by
    apply RingHom.ext
    intro x
    change f.val (laurentSquareRootEquiv K (AdjoinRoot.of _ x)) =
      laurentScalarEvaluation (L := L) a x
    have hx : laurentSquareRootEquiv K (AdjoinRoot.of _ x) = laurentSquareMap K x :=
      congrArg (fun g : LaurentPolynomial K →+* LaurentPolynomial K => g x)
        (laurentSquareRootEquiv_comp_of K)
    rw [hx]
    exact congrArg (fun g : LaurentPolynomial K →+* L => g x) f.property⟩
  invFun f := ⟨f.val.comp (laurentSquareRootEquiv K).symm.toRingHom, by
    apply RingHom.ext
    intro x
    change f.val ((laurentSquareRootEquiv K).symm (laurentSquareMap K x)) =
      laurentScalarEvaluation (L := L) a x
    have hx : laurentSquareRootEquiv K (AdjoinRoot.of _ x) = laurentSquareMap K x :=
      congrArg (fun g : LaurentPolynomial K →+* LaurentPolynomial K => g x)
        (laurentSquareRootEquiv_comp_of K)
    rw [← hx, RingEquiv.symm_apply_apply]
    exact congrArg (fun g : LaurentPolynomial K →+* L => g x) f.property⟩
  left_inv f := by
    apply Subtype.ext
    apply RingHom.ext
    intro x
    change f.val (laurentSquareRootEquiv K ((laurentSquareRootEquiv K).symm x)) = f.val x
    rw [RingEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    apply RingHom.ext
    intro x
    change f.val ((laurentSquareRootEquiv K).symm (laurentSquareRootEquiv K x)) = f.val x
    rw [RingEquiv.symm_apply_apply]

/-- Actual square-map fibre points are exactly the square roots. -/
def laurentSquareSchemeFiberEquivRoots (a : Kˣ) :
    LaurentSquareSchemeFiber (L := L) a ≃ {r : L // r ^ 2 = algebraMap K L (a : K)} :=
  ((laurentSquareSchemeFiberEquivHom a).trans (laurentSquareFiberHomEquivKummer a)).trans
    (laurentKummerFiberEquivRoots 2 a)

/-- The associated root is the actual source Laurent coordinate. -/
theorem laurentSquareSchemeFiberEquivRoots_apply (a : Kˣ)
    (f : LaurentSquareSchemeFiber (L := L) a) :
    (laurentSquareSchemeFiberEquivRoots a f).val =
      (Spec.preimage f.val).hom (LaurentPolynomial.T 1 : LaurentPolynomial K) := by
  change (Spec.preimage f.val).hom (laurentSquareRootEquiv K
    (AdjoinRoot.root (X ^ 2 - C (LaurentPolynomial.T 1 : LaurentPolynomial K)))) =
    (Spec.preimage f.val).hom (LaurentPolynomial.T 1 : LaurentPolynomial K)
  rw [laurentSquareRootEquiv_root]

end AnabelianGeometry.GeometricFundamentalGroup
