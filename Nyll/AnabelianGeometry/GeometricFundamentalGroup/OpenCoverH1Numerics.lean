/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCurveH1Deck
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverDegree
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # The actual H¹ exponent of a finite cover of a punctured curve

Compactifying the given finite étale cover and applying Riemann--Hurwitz
expresses its finite-coefficient H¹ exponent in terms of its actual fibre
degree. In particular, the exponent uses the open curve's Euler
characteristic, rather than that of a hypothetical proper cover.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace NeronModelInfra
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- An open immersion into a smooth proper curve with no omitted closed
points is an isomorphism. The generic point already belongs to every
nonempty open, so it supplies no additional boundary point. -/
theorem isIso_of_openBoundary_card_eq_zero
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme} [Nonempty X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (hzero : Nat.card (M.openBoundaryPlaces j) = 0) : IsIso j := by
  classical
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  have hempty : IsEmpty (M.openBoundaryPlaces j) :=
    Fintype.card_eq_zero_iff.mp (by simpa only [Nat.card_eq_fintype_card] using hzero)
  have hgeneric : genericPoint M.C ∈ Set.range j :=
    ((genericPoint_spec M.C).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
      (by
        obtain ⟨z⟩ := (inferInstance : Nonempty X)
        exact ⟨j z, Set.mem_univ _, Set.mem_range_self z⟩)
  have hsurj : Function.Surjective j := by
    intro x
    by_contra hx
    have hxne : x ≠ genericPoint M.C := by rintro rfl; exact hx hgeneric
    let xc : closedPoints M.C :=
      ⟨x, mem_closedPoints_iff.mpr (isClosed_singleton_of_ne_genericPoint M.toBase x hxne)⟩
    let v : M.openBoundaryPlaces j := ⟨M.placeEquiv xc, by
      change (M.placeEquiv.symm (M.placeEquiv xc)).val ∉ Set.range j
      rw [M.placeEquiv.symm_apply_apply]
      exact hx⟩
    exact hempty.false v
  exact (isIso_iff_isOpenImmersion_and_surjective j).mpr
    ⟨inferInstance, ⟨hsurj⟩⟩

/-- The finite H¹ cardinal of an actual connected Galois cover of a
nonproper smooth curve is n^q, where q - 1 is its fibre degree times
2g + r - 2. The compactification and its boundary are constructed internally. -/
theorem exists_openCover_finiteH1_exponent
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hboundary : (M.openBoundaryPlaces j).Nonempty)
    (W : FiniteEtale X) [IsGalois W]
    (n : ℕ+) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X) (geom : Spec (.of Ω) ⟶ W.left)
    (hgeom : geom ≫ W.hom = xi) :
    ∃ q : ℕ,
      Nat.card (Sheaf.H.{0}
        ((constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) = (n : ℕ) ^ q ∧
      (q : ℤ) - 1 = (Nat.card ((fiber xi).obj W) : ℤ) *
        (2 * (genusFF K F : ℤ) + Nat.card (M.openBoundaryPlaces j) - 2) := by
  classical
  have : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  have : IsIntegral ((Functor.id Scheme).obj W.left) :=
    inferInstanceAs (IsIntegral W.left)
  have : IsIntegral ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (IsIntegral X)
  have : CompactSpace ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (CompactSpace X)
  have : IsFiniteEtale W.hom := W.prop
  have : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace W.hom
  have : Surjective W.hom := IsFiniteEtale.surjective W.hom
  let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
  let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
  obtain ⟨N, d, k, hd, hfinite, hk, hsquare, hb⟩ :=
    exists_open_cover_curveModel_square_boundary M j W
  have : IsFinite d := hfinite
  have : IsOpenImmersion k := hk
  have hsurj : Function.Surjective d :=
    surjective_finite_extension_of_open_square j W.hom W.hom.surjective k d hsquare
  have : Etale (k ≫ d) := by rw [hsquare]; infer_instance
  have hNboundary := openBoundary_nonempty_of_finite_square M N d hd hsurj j k hb hboundary
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  let : Fintype (N.openBoundaryPlaces k) := (N.openBoundaryPlaces_finite k).fintype
  obtain ⟨w, hw⟩ := hNboundary
  have hTpos : 0 < Fintype.card (N.openBoundaryPlaces k) :=
    Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
  have hRH := M.two_mul_genus_add_openBoundary_sub_two_eq N d hd hsurj j k hb
  rw [Set.Finite.card_toFinset, Set.Finite.card_toFinset] at hRH
  have hdegree : finrankAlong K (M.finiteCurveFieldMap N d hd hsurj) =
      Nat.card ((fiber xi).obj W) := by
    rw [finrankAlong_openCover_eq_actual M N j W d hd hsurj k hsquare]
    let : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    rw [← natCard_finiteEtaleAut_eq_finrank_functionField_of_isGalois W inferInstance]
    let a : (fiber xi).obj W := (fiberObjEquivHom xi W).symm (Over.homMk geom hgeom)
    exact Nat.card_congr (evaluationEquivOfIsGalois (fiber xi) W a)
  rw [hdegree] at hRH
  have : IsCurveOver K W.left.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one N.toBase
      N.ffEquiv N.ffEquiv_algebraMap
  obtain ⟨εN⟩ := N.nonempty_rationalPoint
  have hkdense : DenseRange k :=
    k.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace k
  let q := 2 * genusFF K W.left.functionField + Fintype.card (N.openBoundaryPlaces k) - 1
  refine ⟨q, N.natCard_open_finiteH1_eq_pow_genus_boundary εN k hkdense ⟨w, hw⟩ n geom, ?_⟩
  rw [Nat.card_eq_fintype_card (α := M.openBoundaryPlaces j)]
  have hq : (q : ℤ) - 1 =
      2 * (genusFF K W.left.functionField : ℤ) +
        Fintype.card (N.openBoundaryPlaces k) - 2 := by
    dsimp only [q]
    omega
  exact hq.trans hRH

end AnabelianGeometry
