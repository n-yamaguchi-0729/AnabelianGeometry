/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AlgebraicallyClosedCohomology
public import Nyll.EtaleCohomology.Classical.CechH1Vanishing
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.ClosedPushforward
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.FilteredColimitSectionGluing
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.RightHomology
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Whiskering

/-!
# First cohomology of the closed-point divisor sheaf

An actual free Čech cocycle is a section on the self-overlap of its cover.
On a quasi-compact overlap this section has finite support among the
original closed-point summands. Each projected cocycle has a primitive:
the existing closed-pushforward comparison and separably closed field
vanishing kill its obstruction in degree one. Their finite sum is a
primitive of the original cocycle. The native Čech criterion then kills
the original divisor-sheaf cohomology class.

The sheaf throughout is the categorical coproduct. No product comparison
or commutation of higher cohomology with filtered colimits is used.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

private theorem exists_primitive_of_extOne_eq_zero
    {C : Type u} [Category.{v} C] [Abelian C] [hExt : HasExt.{w} C]
    {A B D E Z : C} (d : A ⟶ B) (f : B ⟶ D) (g : D ⟶ E)
    (hd : d ≫ f = 0) (hf : f ≫ g = 0)
    (hR : (ShortComplex.mk d f hd).Exact)
    (hK : (ShortComplex.mk f g hf).Exact) [Epi g]
    (hH : ∀ c : Ext.{w} E Z 1, c = 0) (z : B ⟶ Z) (hz : d ≫ z = 0) :
    ∃ b : D ⟶ Z, f ≫ b = z := by
  let R := ShortComplex.mk d f hd
  have : Mono R.fromOpcycles := hR.mono_fromOpcycles
  have hw : R.fromOpcycles ≫ g = 0 := by
    apply (cancel_epi R.pOpcycles).mp
    rw [← Category.assoc, R.p_fromOpcycles, comp_zero]
    exact hf
  let T := ShortComplex.mk R.fromOpcycles g hw
  let φ : ShortComplex.mk f g hf ⟶ T :=
    ShortComplex.homMk R.pOpcycles (𝟙 D) (𝟙 E)
      (by rw [Category.comp_id]; exact R.p_fromOpcycles)
      (by rw [Category.id_comp, Category.comp_id])
  have : Epi φ.τ₁ := inferInstanceAs (Epi R.pOpcycles)
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 D))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 E))
  have : Mono T.f := inferInstanceAs (Mono R.fromOpcycles)
  have : Epi T.g := inferInstanceAs (Epi g)
  have hT : T.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hK }
  let a : R.opcycles ⟶ Z := R.descOpcycles z hz
  obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₁ hT Z
    (Ext.mk₀ a) (n₁ := 1) rfl (hH _)
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective D Z).surjective e
  have hb : R.fromOpcycles ≫ b = a :=
    (Ext.mk₀_bijective R.opcycles Z).injective
      ((Ext.mk₀_comp_mk₀ R.fromOpcycles b).symm.trans he)
  refine ⟨b, ?_⟩
  calc
    f ≫ b = (R.pOpcycles ≫ R.fromOpcycles) ≫ b := by rw [R.p_fromOpcycles]
    _ = R.pOpcycles ≫ a := by rw [Category.assoc, hb]
    _ = z := R.p_descOpcycles z hz

private theorem freeYoneda_closedPointDivisor_finiteSupport
    (X : Scheme.{u}) (U : X.Etale)
    [QuasiCompact (terminal.from U.left)]
    (z : (freeAbelianSheafYoneda X.smallEtaleTopology).obj U ⟶
      closedPointDivisorSheaf X) :
    ∃ T : Finset (closedPoints X), z = ∑ x ∈ T,
      (z ≫ closedPointDivisorSheafComponentProjection X x) ≫
        closedPointDivisorSheafInjection X x := by
  classical
  let hShape : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  let e := freeAbelianSheafYonedaHomAddEquiv X.smallEtaleTopology U
    (closedPointDivisorSheaf X)
  obtain ⟨T, hT⟩ := closedPointDivisorSheaf_finiteSupport_of_quasiCompact X U (e z)
  refine ⟨T, ?_⟩
  apply e.injective
  rw [map_sum]
  refine hT.trans ?_
  apply Finset.sum_congr rfl
  intro x hx
  change _ = freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology U _
    ((z ≫ closedPointDivisorSheafComponentProjection X x) ≫
      closedPointDivisorSheafInjection X x)
  rw [freeAbelianSheafYonedaHomEquiv_postcomp,
    freeAbelianSheafYonedaHomEquiv_postcomp]
  rfl

private theorem closedPointDivisorSummand_H1_eq_zero
    (X : Scheme.{u}) (x : closedPoints X) [IsSepClosed (X.residueField x.1)]
    (c : Sheaf.H.{u} (closedPointDivisorSummand X x) 1) : c = 0 := by
  have : IsClosedImmersion (closedPointResidueFieldMap X x) :=
    closedPointResidueFieldMap_isClosedImmersion X x
  let F := (constantSheaf (Spec (X.residueField x.1)).smallEtaleTopology
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let e := etaleAbelianCohomologyClosedPushforwardEquiv
    (closedPointResidueFieldMap X x) F 1
  let c' : Sheaf.H.{u}
      ((etaleAbelianPushforward (closedPointResidueFieldMap X x)).obj F) 1 := c
  have hc' : c' = 0 := e.injective
    ((fieldSheafCohomology_eq_zero_of_isSepClosed
      (X.residueField x.1) F 0 (e c')).trans e.map_zero.symm)
  exact hc'

/-- Every actual free Čech cocycle of the closed-point divisor sheaf on
an affine surjective cover has a primitive. Only the actual finitely many
projected closed-point cocycles are used. -/
theorem closedPointDivisorSheaf_exists_freeCech_primitive
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (hres : ∀ x : closedPoints X, IsSepClosed (X.residueField x.1))
    (V : X.Etale) (f : V ⟶ Scheme.Etale.mk (𝟙 X))
    [IsAffine V.left] [Surjective f.left]
    (z : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ closedPointDivisorSheaf X)
    (hz : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
      (freeCechTriangleBoundaryNat (yoneda.map f)) ≫ z = 0) :
    ∃ b : (freeAbelianSheafYoneda X.smallEtaleTopology).obj V ⟶
        closedPointDivisorSheaf X,
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat (yoneda.map f)) ≫ b = z := by
  classical
  have hExt : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := inferInstance
  let Q := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let R := (freeCechRelationComplex (yoneda.map f)).map Q
  let K := (freeCechAugmentationComplex (yoneda.map f)).map Q
  have hzR : R.f ≫ z = 0 := hz
  let U : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hU : IsTerminal U := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) X
  have hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology U := by
    have hc : Sieve.ofArrows (fun _ : PUnit.{u + 1} => V) (fun _ => f) ∈
        X.smallEtaleTopology U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff, Set.iUnion_const]
      exact Set.range_eq_univ.mpr f.left.surjective
    simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hc
  have : Epi K.g := freeAbelianSheafYoneda_map_epi_of_cover X.smallEtaleTopology f hf
  have : QuasiSeparatedSpace (Scheme.Etale.mk (𝟙 X)).left :=
    inferInstanceAs (QuasiSeparatedSpace X)
  have : QuasiCompact (terminal.from (pullback f f).left) :=
    etale_affine_overlap_quasiCompact f f
  let e := freeCechEdgeSheafIso X.smallEtaleTopology f
  obtain ⟨T, hT⟩ := freeYoneda_closedPointDivisor_finiteSupport X
    (pullback f f) (e.inv ≫ z)
  have hdecomp : z = ∑ x ∈ T,
      (z ≫ closedPointDivisorSheafComponentProjection X x) ≫
        closedPointDivisorSheafInjection X x := by
    apply (cancel_epi e.inv).mp
    rw [Preadditive.comp_sum]
    simpa only [Category.assoc] using hT
  have hprimitive (x : closedPoints X) :
      ∃ b : K.X₂ ⟶ closedPointDivisorSummand X x,
        K.f ≫ b = z ≫ closedPointDivisorSheafComponentProjection X x := by
    have : IsSepClosed (X.residueField x.1) := hres x
    have hH (c : Ext.{u} K.X₃ (closedPointDivisorSummand X x) 1) : c = 0 := by
      let eH := sheafCohomologyTerminalEquiv X.smallEtaleTopology hU
        (closedPointDivisorSummand X x) 1
      let c' : Sheaf.H'.{u} (closedPointDivisorSummand X x) 1 U := c
      have hc' : c' = 0 := eH.symm.injective
        ((closedPointDivisorSummand_H1_eq_zero X x (eH.symm c')).trans
          eH.symm.map_zero.symm)
      exact hc'
    refine exists_primitive_of_extOne_eq_zero
      (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (hExt := hExt)
      R.f K.f K.g R.zero K.zero
      (freeCechRelationComplex_sheaf_exact X.smallEtaleTopology (yoneda.map f))
      (freeCechAugmentationComplex_sheaf_exact X.smallEtaleTopology (yoneda.map f))
      hH (z ≫ closedPointDivisorSheafComponentProjection X x) ?_
    let z' : R.X₂ ⟶ closedPointDivisorSheaf X := z
    let p := closedPointDivisorSheafComponentProjection X x
    have h := congrArg (fun t : R.X₁ ⟶ closedPointDivisorSheaf X => t ≫ p) hzR
    exact (Category.assoc R.f z' p).symm.trans (h.trans zero_comp)
  choose b hb using hprimitive
  refine ⟨∑ x ∈ T, b x ≫ closedPointDivisorSheafInjection X x, ?_⟩
  change K.f ≫ (∑ x ∈ T, b x ≫ closedPointDivisorSheafInjection X x) = z
  rw [Preadditive.comp_sum]
  calc
    _ = ∑ x ∈ T, (z ≫ closedPointDivisorSheafComponentProjection X x) ≫
        closedPointDivisorSheafInjection X x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Category.assoc, hb x]
      rfl
    _ = z := hdecomp.symm

/-- The actual coproduct divisor sheaf has vanishing native first
cohomology on a quasi-compact, quasi-separated scheme whose closed
residue fields are separably closed. -/
theorem closedPointDivisorSheaf_H1_eq_zero
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (hres : ∀ x : closedPoints X, IsSepClosed (X.residueField x.1))
    (c : Sheaf.H.{u} (closedPointDivisorSheaf X) 1) : c = 0 := by
  apply etaleSheafH1_eq_zero_of_affine_freeCech_primitives X (closedPointDivisorSheaf X)
    (fun V f hV hsurj z hz => ?_) c
  have : IsAffine V.left := hV
  have : Surjective f.left := hsurj
  exact closedPointDivisorSheaf_exists_freeCech_primitive X hres V f z hz

/-- For an actual proper scheme over an algebraically closed field,
the original closed-point divisor sheaf has vanishing first cohomology,
in every characteristic. In particular this applies to proper curves. -/
theorem closedPointDivisorSheaf_H1_eq_zero_of_proper
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (c : Sheaf.H.{u} (closedPointDivisorSheaf X) 1) : c = 0 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  apply closedPointDivisorSheaf_H1_eq_zero X (fun x => ?_) c
  have : IsAlgClosed (X.residueField x.1) := IsAlgClosed.of_ringEquiv k
    (X.residueField x.1)
    (residueFieldIsoBase f x.1 x.2).symm.commRingCatIsoToRingEquiv
  infer_instance

end EtaleCohomology
