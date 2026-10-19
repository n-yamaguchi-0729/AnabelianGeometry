/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenKummerGenericRootFiber
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticKummerRootsRestriction
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois

/-!
# One generic-root coordinate, its full torsor, and arithmetic semilinearity

The coefficient torsor is constructed using precisely the returned normalized
root coordinate. Its compatibility with the existing root-scaling and with
original arithmetic monodromy is retained in the same existential witness.
No unrelated choice of a local-coordinate torsor is identified with it.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale JacobianVarieties.Kummer TopologicalSpace
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

private theorem exists_rootCoordinate_torsor
    {κ Ω T : Type} [Field κ] [IsSepClosed κ] [Field Ω] [Nonempty T]
    (ι : κ →+* Ω) (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ))
    (a : Ωˣ) (e : T ≃ {β : Ω // β ^ (n : ℕ) = (a : Ω)}) :
    ∃ t : Torsor (rootsOfUnity (n : ℕ) κ) T,
      ∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
        (e (t.toMulAction.toSMul.smul ζ x)).val = ι (ζ.val : κ) * (e x).val := by
  let act (ζ : rootsOfUnity (n : ℕ) κ) (x : T) : T :=
    e.symm ⟨ι (ζ.val : κ) * (e x).val, by
      have hz : (ζ.val : κ) ^ (n : ℕ) = 1 :=
        congrArg (fun u : κˣ => (u : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
      rw [mul_pow, ← map_pow, hz, map_one, one_mul]
      exact (e x).property⟩
  have he (ζ : rootsOfUnity (n : ℕ) κ) (x : T) :
      (e (act ζ x)).val = ι (ζ.val : κ) * (e x).val :=
    congrArg Subtype.val (e.apply_symm_apply _)
  let ma : MulAction (rootsOfUnity (n : ℕ) κ) T := {
    smul := act
    one_smul := fun x => e.injective (Subtype.ext (by
      change (e (act 1 x)).val = (e x).val
      rw [he]
      change ι 1 * (e x).val = (e x).val
      rw [map_one, one_mul]))
    mul_smul := fun ζ η x => e.injective (Subtype.ext (by
      change (e (act (ζ * η) x)).val = (e (act ζ (act η x))).val
      rw [he, he, he]
      change ι ((ζ.val : κ) * (η.val : κ)) * (e x).val = _
      rw [map_mul, mul_assoc])) }
  let := ma
  have hzero (x : T) : (e x).val ≠ 0 := by
    intro hx
    have hp := (e x).property
    rw [hx, zero_pow n.ne_zero] at hp
    exact a.ne_zero hp.symm
  have hu (x y : T) : ∃! ζ : rootsOfUnity (n : ℕ) κ, ζ • x = y := by
    obtain ⟨ζ, hζ, huniq⟩ := EtaleFundamentalGroups.Kummer.existsUnique_rootScale
      ι n hn (e x).val (e y).val (hzero x) ((e x).property.trans (e y).property.symm)
    refine ⟨ζ, e.injective (Subtype.ext ((he ζ x).trans hζ)), ?_⟩
    intro η hη
    apply huniq η
    exact (he η x).symm.trans (congrArg (fun z : T => (e z).val) hη)
  let d (x y : T) : rootsOfUnity (n : ℕ) κ := (hu y x).exists.choose
  have hd (x y : T) : d x y • y = x := (hu y x).exists.choose_spec
  let t : Torsor (rootsOfUnity (n : ℕ) κ) T := {
    toMulAction := ma
    sdiv := d
    nonempty := inferInstance
    sdiv_smul' := hd
    smul_sdiv' := fun ζ x => (hu x (ζ • x)).unique (hd (ζ • x) x) rfl }
  exact ⟨t, he⟩

/-- The original arithmetic monodromy is cyclotomically semilinear for the
full roots-of-unity torsor on the original named arithmetic Kummer fiber. -/
theorem exists_arithmeticKummerFiber_genericSemilinearTorsor_with_genericEvaluation
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (w : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {κ Ω : Type} [Field κ] [Field Ω] [IsAlgClosed κ] [IsSepClosed Ω]
    [Algebra K X.functionField] [Algebra K κ] [Algebra K Ω]
    [Algebra X.functionField Ω] [Algebra κ Ω]
    [IsScalarTower K X.functionField Ω] [IsScalarTower K κ Ω]
    [IsSepClosure K κ] [IsSepClosure X.functionField Ω]
    (hbase : (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)) ≫ (j ≫ M.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let xi := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover S n hn w j hj hi
    let q := arithmeticFundamentalGroupHom K κ (j ≫ M.toBase) xi
    let g := j.functionFieldMap hj (M.ffEquiv (w.val : F))
    ∃ e : (fiber xi).obj W ≃ {β : Ω // β ^ (n : ℕ) = algebraMap X.functionField Ω g},
      ∃ t : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber xi).obj W),
        (∀ (ζ : rootsOfUnity (n : ℕ) K) x,
          (e ((kummerGeometricRootAction M S n w j hj hi hn xi).toSMul.smul ζ x)).val =
            pointScalar (j ≫ M.toBase) xi (ζ.val : K) * (e x).val) ∧
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          (e (t.toMulAction.toSMul.smul ζ x)).val =
            algebraMap κ Ω (ζ.val : κ) * (e x).val) ∧
        (∀ (σ : Gal(Ω/X.functionField)) x,
          (e (fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
            (toAut (fiber η) Gal(Ω/X.functionField) σ) • x)).val = σ (e x).val) ∧
        ∀ (p : π₁ᵉᵗ(xi)) (ζ : rootsOfUnity (n : ℕ) κ) x,
          p • (t.toMulAction.toSMul.smul ζ x) =
            t.toMulAction.toSMul.smul
              (restrictRootsOfUnity (q p).toRingHom (n : ℕ) ζ) (p • x) := by
  intro η xi W q g
  have hnκ : IsUnit ((n : ℕ) : κ) := by
    simpa only [map_natCast] using hn.map (algebraMap K κ)
  obtain ⟨e, hscale, hg⟩ := exists_arithmeticKummerFiber_genericRootEquiv
    M S n w j hj hi hn (Ω := Ω)
  have hg0 : algebraMap X.functionField Ω g ≠ 0 :=
    (map_ne_zero (algebraMap X.functionField Ω)).mpr
      ((map_ne_zero (j.functionFieldMap hj)).mpr
        ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero w.val)))
  let a : Ωˣ := Units.mk0 (algebraMap X.functionField Ω g) hg0
  let : Nonempty ((fiber xi).obj W) :=
    kummerGeometricFiber_nonempty M S n w j hj hi hn xi
  obtain ⟨t, ht⟩ := exists_rootCoordinate_torsor (algebraMap κ Ω) n hnκ a e
  let genericMap := X.fromSpecStalk (genericPoint X)
  let θ := fieldSourceAbsoluteGaloisHom X.functionField Ω genericMap
  let : IsDominant genericMap := genericPoint_isDominant X
  let : QuasiCompact genericMap :=
    { isCompact_preimage := fun V _ _ => (Set.toFinite (genericMap ⁻¹' V)).isCompact }
  have hsurj : Function.Surjective θ :=
    fieldSourceAbsoluteGaloisHom_surjective X.functionField Ω genericMap
  have hθ (σ : Gal(Ω/X.functionField)) :
      θ σ = fundamentalGroupHom genericMap η
        (toAut (fiber η) Gal(Ω/X.functionField) σ) := by
    change fundamentalGroupHom genericMap η
      (toAutHomeo (fib X.functionField Ω) Gal(Ω/X.functionField) σ) = _
    rw [toAutHomeo_apply]
  refine ⟨e, t, hscale, ht, hg, ?_⟩
  intro p ζ x
  obtain ⟨σ, rfl⟩ := hsurj p
  apply e.injective
  apply Subtype.ext
  have hgeneric :
      (e (θ σ • (t.toMulAction.toSMul.smul ζ x))).val =
        σ (algebraMap κ Ω (ζ.val : κ)) * (e (θ σ • x)).val := by
    rw [hθ σ]
    exact (hg σ _).trans ((congrArg σ (ht ζ x)).trans
      ((map_mul σ _ _).trans
        (congrArg (σ (algebraMap κ Ω (ζ.val : κ)) * ·) (hg σ x).symm)))
  have hcoeff := fieldSource_arithmetic_roots_restriction
    K X.functionField κ Ω (j ≫ M.toBase) genericMap hbase (n : ℕ) hnκ σ ζ
  have hroot := ht (restrictRootsOfUnity (q (θ σ)).toRingHom (n : ℕ) ζ) (θ σ • x)
  change (e (t.toMulAction.toSMul.smul
    (restrictRootsOfUnity (q (θ σ)).toRingHom (n : ℕ) ζ) (θ σ • x))).val =
      algebraMap κ Ω (q (θ σ) (ζ.val : κ)) * (e (θ σ • x)).val at hroot
  exact hgeneric.trans
    ((congrArg (fun c : Ω => c * (e (θ σ • x)).val) hcoeff).trans hroot.symm)

/-- The original arithmetic monodromy is cyclotomically semilinear for the
full roots-of-unity torsor on the original named arithmetic Kummer fiber. -/
theorem exists_arithmeticKummerFiber_genericSemilinearTorsor
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (w : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {κ Ω : Type} [Field κ] [Field Ω] [IsAlgClosed κ] [IsSepClosed Ω]
    [Algebra K X.functionField] [Algebra K κ] [Algebra K Ω]
    [Algebra X.functionField Ω] [Algebra κ Ω]
    [IsScalarTower K X.functionField Ω] [IsScalarTower K κ Ω]
    [IsSepClosure K κ] [IsSepClosure X.functionField Ω]
    (hbase : (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)) ≫ (j ≫ M.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let xi := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover S n hn w j hj hi
    let q := arithmeticFundamentalGroupHom K κ (j ≫ M.toBase) xi
    let g := j.functionFieldMap hj (M.ffEquiv (w.val : F))
    ∃ e : (fiber xi).obj W ≃ {β : Ω // β ^ (n : ℕ) = algebraMap X.functionField Ω g},
      ∃ t : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber xi).obj W),
        (∀ (ζ : rootsOfUnity (n : ℕ) K) x,
          (e ((kummerGeometricRootAction M S n w j hj hi hn xi).toSMul.smul ζ x)).val =
            pointScalar (j ≫ M.toBase) xi (ζ.val : K) * (e x).val) ∧
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          (e (t.toMulAction.toSMul.smul ζ x)).val =
            algebraMap κ Ω (ζ.val : κ) * (e x).val) ∧
        ∀ (p : π₁ᵉᵗ(xi)) (ζ : rootsOfUnity (n : ℕ) κ) x,
          p • (t.toMulAction.toSMul.smul ζ x) =
            t.toMulAction.toSMul.smul
              (restrictRootsOfUnity (q p).toRingHom (n : ℕ) ζ) (p • x) := by
  intro η xi W q g
  obtain ⟨e, t, hscale, ht, _hg, hsemi⟩ :=
    exists_arithmeticKummerFiber_genericSemilinearTorsor_with_genericEvaluation
      M S n w j hj hi hn (κ := κ) (Ω := Ω) hbase
  exact ⟨e, t, hscale, ht, hsemi⟩

end AlgebraicCurve.CurveModel.OpenKummer
