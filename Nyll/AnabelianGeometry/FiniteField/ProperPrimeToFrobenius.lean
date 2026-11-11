/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.KummerFrobenius
public import Nyll.AnabelianGeometry.FiniteField.ProperKummerTorsionFree
public import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusFixed
public import Nyll.JacobianVarieties.WeilPairing.FiniteFieldNondegeneracy
public import Nyll.ProCGroups.Abelian.SemilinearFixedCharacters
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicPointsEquivariance
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Existence
public import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearTower
public import Nyll.AnabelianGeometry.WeightFiltration.FiniteTorsionCoefficients
public import Nyll.AnabelianGeometry.WeightFiltration.FrobeniusFixedTate
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1IsomorphismPullback
public import Nyll.JacobianVarieties.Pic0.TorsionBijectiveInjective
public import Nyll.JacobianVarieties.Picard.Torsion.TorsionAlgebraicPoints
public import Nyll.JacobianVarieties.Picard.Unpointed.UnpointedJacobian
public import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPairSemilinearSmul
public import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusTower
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Actual proper prime-to-characteristic Frobenius fixed-point vanishing

The finite Kummer comparison and the original semilinear Weil pairing turn
an invariant functional on actual proper H¹ into a Frobenius-fixed Picard
point. One finite subgroup of actual Picard points gives an annihilator
independent of the coefficient exponent. The original Kummer coefficient
lifts then eliminate this finite annihilator in the native fundamental
group's canonical prime-to-characteristic abelian quotient.

The H¹ assertion retains all invertible finite coefficients. It can also
be applied to the restriction of a functional from an open curve, before
the actual finite residue sequence treats its boundary contribution.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open EtaleFundamentalGroups.Cohomology AnabelianGeometry.WeightFiltration
open NeronModelInfra GoodReductionJacobian ProCGroups.Abelian

namespace AnabelianGeometry.FiniteField

/-- Evaluation of the original finite H¹ character at a native fundamental
group element, with its roots-of-unity value retained in the original field. -/
def finiteKummerH1UnitEvaluation
    (K : Type uGeom) [Field K] (n : ℕ+)
    {X : Scheme.{uGeom}} [ConnectedSpace X]
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (z : Aut (FiniteEtale.fiber ξ)) :
    FiniteKummerH1 K X n →+ Additive Kˣ := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  refine
    { toFun := fun a => Additive.ofMul
        ((finiteH1CharacterEquiv A ξ a).toMul z : rootsOfUnity (n : ℕ) K).val
      map_zero' := ?_
      map_add' := ?_ }
  · rw [map_zero]
    rfl
  · intro a b
    rw [map_add]
    rfl

/-- Equality in the actual prime-to-characteristic quotient makes the
original H¹ evaluation invariant under the corresponding scheme pullback.
Only the genuine change of geometric fiber is used. -/
theorem finiteKummerH1UnitEvaluation_pullback_of_primeTo_fixed
    (K : Type uGeom) [Field K] [IsSepClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    {X : Scheme.{uGeom}} [ConnectedSpace X]
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (θ : X ≅ X) (s : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber (ξ ≫ θ.hom))
    (z : Aut (FiniteEtale.fiber ξ))
    (hz : primeToAbelianMk p (Aut (FiniteEtale.fiber ξ))
        (s.symm.conjAut (FiniteEtale.fundamentalGroupHom θ.hom ξ z)) =
      primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) z)
    (a : FiniteKummerH1 K X n) :
    finiteKummerH1UnitEvaluation K n ξ z
        (constantCohomologyPullback θ.hom
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 a) =
      finiteKummerH1UnitEvaluation K n ξ z a := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let u := s.symm.conjAut (FiniteEtale.fundamentalGroupHom θ.hom ξ z)
  have hs : s.conjAut u = FiniteEtale.fundamentalGroupHom θ.hom ξ z := by
    apply Aut.ext
    apply Iso.ext
    exact congrArg (fun f : End _ => f.asHom)
      (s.self_symm_conj (FiniteEtale.fundamentalGroupHom θ.hom ξ z).toEnd)
  have hp := congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => χ z)
    (h1Character_schemePullback θ.hom A ξ a)
  have hb := congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => χ u)
    (h1Character_basePoint A ξ (ξ ≫ θ.hom) s a)
  change h1Character A (ξ ≫ θ.hom) a
      (FiniteEtale.fundamentalGroupHom θ.hom ξ z) =
    h1Character A ξ (constantCohomologyPullback θ.hom A 1 a) z at hp
  change h1Character A (ξ ≫ θ.hom) a (s.conjAut u) =
    h1Character A ξ a u at hb
  rw [hs] at hb
  let χ : Aut (FiniteEtale.fiber ξ) →ₜ* rootsOfUnity (n : ℕ) K := h1Character A ξ a
  have hc : χ u = χ z :=
    unit_roots_character_eq_of_primeToAbelianMk_eq p K n hn
      χ hz
  exact congrArg (fun w : rootsOfUnity (n : ℕ) K => Additive.ofMul w.val)
    (hp.symm.trans (hb.trans hc))

section Proper

variable (k : Type uGeom) [Field k] [Fintype k]
  {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  {C : Scheme.{uGeom}} (c : C ⟶ Spec (.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
  (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
  (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
  (r : ℕ) (hr : r ≠ 0) (θ : M.C ≅ M.C)
  (hproj : θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k K) =
    eC.hom ≫ pullback.fst c (specMap k K))
  (hbase : θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingHom))

include ε heC hr hproj hbase

/-- The actual proper curve supplies one positive annihilator for every
Frobenius-invariant finite Kummer H¹ functional, uniformly in its invertible
coefficient exponent. No Picard comparison, pairing, or finite bound is an input. -/
theorem exists_properFiniteKummerH1_invariant_annihilator :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℕ+) (_ : IsUnit ((n : ℕ) : K))
        (χ : FiniteKummerH1 K M.C n →+ Additive Kˣ),
      (∀ a, χ (constantCohomologyPullback θ.hom
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 a) = χ a) →
      ∀ a, (χ a).toMul ^ N = 1 := by
  obtain ⟨D, ⟨hD⟩, hsD, hpD, hgD⟩ := exists_representsRelSubPic_of_field k c ε
  have : Smooth D.toBase := hsD
  have : IsProper D.toBase := hpD
  have : GeometricallyConnected D.toBase := hgD
  have : CompactSpace D.P := QuasiCompact.compactSpace_of_compactSpace D.toBase
  obtain ⟨aj, _, hclass⟩ := exists_abelJacobi_of_representsRelSubPic k c ε D hD
  let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
  let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut c ε) hD
  obtain ⟨e, _, he⟩ := JacobianVarieties.Picard.exists_pic0_algPoints_equivariant_of_abelJacobi
    c ε D hD aj hclass M eC heC
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r
  obtain ⟨θ', g, hproj', hbase', hg, hfun, _, hge⟩ := he σ
  have hθ : θ'.hom = θ.hom := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hproj'.trans hproj.symm
    · simp only [Category.assoc, heC]
      exact hbase'.trans hbase.symm
  let T := RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom
  let S := T.eqLocus (AddMonoidHom.id (G.AlgPoints hc K))
  have := FiniteField.finite_fixed_frobenius_pow k K r hr
  have : Finite S := WeightFiltration.finite_fixed_algebraicPoints k K D.P D.toBase G hc σ
  refine ⟨Nat.card S, Nat.card_pos, ?_⟩
  intro n hn χ hχ a
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have hnk : IsUnit ((n : ℕ) : k) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hn.ne_zero
    simpa only [map_natCast, map_zero] using congrArg (algebraMap k K) hz
  let τ := JacobianVarieties.Picard.torsionEquivOfAddEquiv e n
  have : Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
    G.finite_torsionLevel_of_isUnit hc K n hnk
  have : Finite (Pic0.torsion K F (n : ℕ)) := Finite.of_injective τ τ.injective
  obtain ⟨t, ht, hft, _⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hfg : ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := ⟨t, ht, hft⟩
  let w : DivisorialWeilPairingData K F (n : ℕ) := Classical.choice
    (Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed K F hfg (n : ℕ))
  let P : Pic0.torsion K F (n : ℕ) ≃+
      Additive (AddChar (Pic0.torsion K F (n : ℕ)) K) :=
    AddEquiv.ofBijective w.toHom
      (Pic0.torsion.bijective_of_injective w.toHom (w.toHom_injective_finiteField k hfg hn.ne_zero))
  let Tn : Pic0.torsion K F (n : ℕ) ≃+ Pic0.torsion K F (n : ℕ) :=
    { toFun := fun b => g • b
      invFun := fun b => g⁻¹ • b
      left_inv := fun b => inv_smul_smul g b
      right_inv := fun b => smul_inv_smul g b
      map_add' := fun b b' => smul_add g b b' }
  have hP (b b' : Pic0.torsion K F (n : ℕ)) :
      Additive.toMul (P (Tn b)) (Tn b') =
        σ.toRingHom.toMonoidHom (Additive.toMul (P b) b') := by
    change w.pair (g • b) (g • b') = σ (w.pair b b')
    rw [w.pair_semilinearSmul, hg]
    rfl
  let jn : Pic0.torsion K F (n : ℕ) →+ G.AlgPoints hc K :=
    e.toAddMonoidHom.comp (Pic0.torsion K F (n : ℕ)).subtype
  have hjn : Function.Injective jn := e.injective.comp Subtype.val_injective
  have hS (b : Pic0.torsion K F (n : ℕ)) (hb : Tn b = b) : jn b ∈ S := by
    change T (e b.val) = e b.val
    have heq := hge b.val
    change e (g • b.val) = T (e b.val) at heq
    exact heq.symm.trans (congrArg (fun b : Pic0.torsion K F (n : ℕ) => e b.val) hb)
  let Ω := SeparableClosure M.C.functionField
  have : IsSepClosed Ω := IsSepClosure.sep_closed M.C.functionField
  let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
    M.C.fromSpecStalk (genericPoint M.C)
  let κ := M.kummerTorsionCohomology n hn ξ
  let ψ : AddChar (Pic0.torsion K F (n : ℕ)) K :=
    { toFun := fun b => (χ (κ b)).toMul.val
      map_zero_eq_one' := by
        rw [map_zero, map_zero]
        rfl
      map_add_eq_mul' := by
        intro b b'
        rw [map_add, map_add]
        rfl }
  have hψ (b : Pic0.torsion K F (n : ℕ)) : ψ (Tn b) = σ.toRingHom.toMonoidHom (ψ b) := by
    change (χ (κ (g • b))).toMul.val = σ ((χ (κ b)).toMul.val)
    have hκ := properKummerCohomology_frobeniusPower k M n hn r θ' g
      (M.functionFieldRingEquiv_semilinear θ' g hfun) hg (Ω := Ω) b
    rw [hθ] at hκ
    change κ (g • b) = Fintype.card k ^ r • constantCohomologyPullback θ.hom
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 (κ b) at hκ
    rw [hκ, map_nsmul, hχ]
    change (χ (κ b)).toMul.val ^ (Fintype.card k ^ r) =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r) ((χ (κ b)).toMul.val)
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  have hbound := ProCGroups.FiniteFixedCharacters.pow_card_target_eq_one_of_semilinear_pairing
    Tn σ.toRingHom.toMonoidHom P hP jn hjn S hS ψ hψ
  obtain ⟨b, rfl⟩ := M.kummerTorsionCohomology_surjective n hn ξ a
  apply Units.ext
  exact congrArg (fun η : AddChar (Pic0.torsion K F (n : ℕ)) K => η b) hbound

end Proper

section Unpointed

variable (k : Type uGeom) [Field k] [Fintype k]
  {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  {C : Scheme.{uGeom}} (c : C ⟶ Spec (.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
  (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
  (r : ℕ) (hr : r ≠ 0) (θ : M.C ≅ M.C)
  (hproj : θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k K) =
    eC.hom ≫ pullback.fst c (specMap k K))
  (hbase : θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingHom))

include heC hr hproj hbase

/-- A finite constant extension supplies the pointed construction internally.
Invariance under the original Frobenius implies invariance under its relevant
power, so the same actual proper H¹ receives a uniform finite annihilator
without assuming any rational point over the original finite field. -/
theorem exists_unpointedProperFiniteKummerH1_invariant_annihilator :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℕ+) (_ : IsUnit ((n : ℕ) : K))
        (χ : FiniteKummerH1 K M.C n →+ Additive Kˣ),
      (∀ a, χ (constantCohomologyPullback θ.hom
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 a) = χ a) →
      ∀ a, (χ a).toMul ^ N = 1 := by
  let P := JacobianVarieties.Picard.Unpointed.presentation k c
  let E := P.extension
  let : Field E := P.extensionField
  let : Algebra k E := P.extensionAlgebra
  have : Module.Finite k E := P.extensionFinite
  have : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  let ι : E →ₐ[k] K := IsAlgClosed.lift
  let : Algebra E K := ι.toRingHom.toAlgebra
  have : IsScalarTower k E K :=
    IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  have : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := k) E
  let cE := baseChange k c E
  let eE := M.constantTowerModelIso k E K c eC
  have heE := M.constantTowerModelIso_base k E K c eC heC
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r
  let σE := FiniteField.frobeniusAlgEquivOfAlgebraic E K ^ r
  let θE := M.coefficientIso cE eE σE
  have hθ : θ.hom = (M.coefficientIso c eC σ).hom := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hproj.trans (M.coefficientIso_fst c eC σ).symm
    · simp only [Category.assoc, heC]
      exact hbase.trans (M.coefficientIso_base c eC heC σ).symm
  let d := Module.finrank k E
  have hfrob : σE.restrictScalars k = σ ^ d := by
    change (AlgEquiv.restrictScalarsHom k)
      (FiniteField.frobeniusAlgEquivOfAlgebraic E K ^ r) = σ ^ d
    rw [map_pow]
    change ((FiniteField.frobeniusAlgEquivOfAlgebraic E K).restrictScalars k) ^ r = σ ^ d
    rw [FiniteField.frobeniusAlgEquiv_restrictScalars k E K]
    change (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ d) ^ r =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r) ^ d
    rw [← pow_mul, ← pow_mul, Nat.mul_comm d r]
  have hθE : θE = M.coefficientIso c eC (σ ^ d) := by
    exact (M.coefficientIso_tower k E K c eC σE).trans
      (congrArg (M.coefficientIso c eC) hfrob)
  obtain ⟨N, hN, hbound⟩ := exists_properFiniteKummerH1_invariant_annihilator
    E cE P.localSection M eE heE r hr θE
      (M.coefficientIso_fst cE eE σE) (M.coefficientIso_base cE eE heE σE)
  refine ⟨N, hN, ?_⟩
  intro n hn χ hχ a
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let Ωg := SeparableClosure M.C.functionField
  have : IsSepClosed Ωg := IsSepClosure.sep_closed M.C.functionField
  let geom := M.C.genericExtensionMorphism Ωg
  have hχσ (b : FiniteKummerH1 K M.C n) :
      χ (constantCohomologyPullback (M.coefficientIso c eC σ).hom A 1 b) = χ b := by
    rw [← hθ]
    exact hχ b
  have hpower (t : ℕ) : ∀ b : FiniteKummerH1 K M.C n,
      χ (constantCohomologyPullback (M.coefficientIso c eC (σ ^ t)).hom A 1 b) = χ b := by
    induction t with
    | zero =>
        intro b
        rw [pow_zero, M.coefficientIso_one]
        exact congrArg χ (constantFiniteH1Pullback_id geom A b)
    | succ t ih =>
        intro b
        rw [pow_succ, M.coefficientIso_mul]
        change χ (constantCohomologyPullback
          ((M.coefficientIso c eC (σ ^ t)).hom ≫ (M.coefficientIso c eC σ).hom) A 1 b) = χ b
        rw [constantFiniteH1Pullback_comp
          (M.coefficientIso c eC (σ ^ t)).hom (M.coefficientIso c eC σ).hom geom A b]
        exact (ih _).trans (hχσ b)
  apply hbound n hn χ ?_ a
  intro b
  rw [hθE]
  exact hpower d b

/-- On the native fundamental group of the actual smooth proper geometric
curve, every positive coefficient-Frobenius fixed class in its canonical
prime-to-characteristic abelian quotient is trivial. The fiber comparison
is arbitrary, and no Tate or Picard comparison is supplied as an assumption. -/
theorem properPrimeToAbelianMk_eq_one_of_frobenius_fixed
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C)
    (s : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber (ξ ≫ θ.hom))
    (z : Aut (FiniteEtale.fiber ξ))
    (hz : primeToAbelianMk p (Aut (FiniteEtale.fiber ξ))
        (s.symm.conjAut (FiniteEtale.fundamentalGroupHom θ.hom ξ z)) =
      primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) z) :
    primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) z = 1 := by
  obtain ⟨N, hN, hbound⟩ := exists_unpointedProperFiniteKummerH1_invariant_annihilator
    k c M eC heC r hr θ hproj hbase
  apply smoothProperPrimeToAbelianMk_eq_one_of_pow K p M.toBase ξ z N hN
  rw [← map_pow]
  apply (primeToAbelianMk_eq_one_iff_unit_roots_characters p K (z ^ N)).mpr
  intro n hn top disc χ
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  obtain ⟨a, ha⟩ := h1Character_surjective A ξ χ
  have hu := hbound n hn (finiteKummerH1UnitEvaluation K n ξ z)
    (finiteKummerH1UnitEvaluation_pullback_of_primeTo_fixed K p n hn ξ θ s z hz) a
  change (h1Character A ξ a z : rootsOfUnity (n : ℕ) K).val ^ N = 1 at hu
  rw [ha] at hu
  apply Subtype.ext
  change (χ (z ^ N) : rootsOfUnity (n : ℕ) K).val = 1
  rw [map_pow]
  exact hu

end Unpointed

end AnabelianGeometry.FiniteField
