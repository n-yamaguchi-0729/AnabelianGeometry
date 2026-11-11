/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PointedSourceDetection
public import Nyll.EtaleFundamentalGroups.GaloisCovers.GenericLiftFieldEmbedding
public import Nyll.EtaleFundamentalGroups.GaloisCovers.GeometricFiniteGaloisMonodromy
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Native geometric abelian classes detected by pointed constant models

The arithmetic label of the specified original source representative forces
it to fix the original algebraic constants. Its action on the actual
geometric curve is therefore a source automorphism. The native arithmetic
exact sequence transfers nontriviality to the geometric abelianization.

Pointed finite descent then supplies an actual abelian cover. Its generic
lift gives the original embedded function field, on which that same source
representative moves a coefficient. The rational lift, original curve map
and literal constant inclusion are all retained for Hilbert containment.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale EtaleFundamentalGroups
open ProCGroups.Abelian TopologicalSpace

namespace AnabelianGeometry.FiniteField

private theorem genericLift_base
    {E Ω : Type uGeom} [Field E] [Field Ω] {Y : Scheme.{uGeom}} [IsIntegral Y]
    (f : Y ⟶ Spec (.of E)) (p : Spec (.of Ω) ⟶ Y)
    (i : Y.functionField →+* Ω)
    (hi : Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) = p) :
    Spec.map (CommRingCat.ofHom (i.comp (AlgebraicCurve.baseToFunctionField f))) =
      p ≫ f := by
  have hbase := AlgebraicCurve.fromSpecStalk_genericPoint_comp_base f
  exact (Spec.map_comp _ _).trans
    ((congrArg (fun q : Spec (.of Y.functionField) ⟶ Spec (.of E) =>
      Spec.map (CommRingCat.ofHom i) ≫ q) hbase.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q : Spec (.of Ω) ⟶ Y => q ≫ f) hi)))

/-- Every nontrivial class in the abelianization of the original arithmetic
geometric kernel is detected by the actual function field of a pointed
abelian cover over finite constants. The source representative and its
constant embedding are unchanged. -/
theorem exists_pointed_constantFunctionField_detecting_geometricAbelianization
    (k K κ Ω : Type uGeom) [Field k] [Finite k] [Field K] [Field κ] [Field Ω]
    [Algebra k K] [Algebra k κ] [Algebra k Ω]
    [Algebra K Ω] [Algebra κ Ω]
    [IsScalarTower k K Ω] [IsScalarTower k κ Ω]
    [IsSepClosure k κ] [IsSepClosure K Ω] [IsSepClosed Ω]
    {C : Scheme.{uGeom}} [IsIntegral C] [IsNormalIntegral C] [IsLocallyNoetherian C]
    [CompactSpace C] [QuasiSeparatedSpace C]
    (c : C ⟶ Spec (.of k)) [GeometricallyConnected c]
    (ε : Spec (.of k) ⟶ C) (hε : ε ≫ c = 𝟙 _)
    (j : Spec (.of K) ⟶ C) [IsDominant j] [IsPreimmersion j]
    (hj : j ≫ c = ξ k K) :
    let π := arithmeticFundamentalGroupHom k κ c (ξ K Ω ≫ j)
    let q := fieldSourceAbsoluteGaloisHom K Ω j
    ∀ (σ : Gal(Ω/K)) (hσ : π (q σ) = 1),
      TopologicalAbelianization.mk π.toMonoidHom.ker ⟨q σ, hσ⟩ ≠ 1 →
    ∃ E : IntermediateField k κ, FiniteDimensional k E ∧
      let bE := Spec.map (CommRingCat.ofHom (algebraMap k E))
      let CE := pullback c bE
      let εE : Spec (.of E) ⟶ CE := pullback.lift (bE ≫ ε) (𝟙 _)
        (by rw [Category.assoc, hε, Category.comp_id, Category.id_comp])
      ∃ hCE : ConnectedSpace CE,
        let _ : ConnectedSpace CE := hCE
        ∃ (N : FiniteEtale CE) (_ : IsGalois N) (_ : IsMulCommutative (Aut N))
          (s : Spec (.of E) ⟶ N.left),
          s ≫ N.hom = εE ∧
          ∃ hNIntegral : IsIntegral N.left,
            let _ : IsIntegral N.left := hNIntegral
            ∃ i : N.left.functionField →+* Ω,
              (Spec.map (CommRingCat.ofHom i) ≫
                  N.left.fromSpecStalk (genericPoint N.left)) ≫
                    N.hom ≫ pullback.fst c bE = ξ K Ω ≫ j ∧
              i.comp (AlgebraicCurve.baseToFunctionField (N.hom ≫ pullback.snd c bE)) =
                (algebraMap κ Ω).comp E.val.toRingHom ∧
              ∃ a : N.left.functionField, σ (i a) ≠ i a := by
  intro π q σ hσ hnon
  have : IsSepClosed κ := IsSepClosure.sep_closed k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k κ))
  let Cκ := pullback b c
  have : ConnectedSpace Cκ := GeometricallyConnected.geometrically_connectedSpace b
    (pullback.snd b c) (pullback.fst b c) (IsPullback.of_hasPullback b c).flip
  have hbase : (ξ K Ω ≫ j) ≫ c = ξ k Ω := by
    rw [Category.assoc, hj, fieldGeometricPoint_comp k K Ω]
  let x : Spec (.of Ω) ⟶ Cκ := pullback.lift (ξ κ Ω) (ξ K Ω ≫ j)
    ((fieldGeometricPoint_comp k κ Ω).trans hbase.symm)
  have hxC : x ≫ pullback.snd b c = ξ K Ω ≫ j := pullback.lift_snd _ _ _
  have hxκ : x ≫ pullback.fst b c = ξ κ Ω := pullback.lift_fst _ _ _
  let e := Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op
  have hK : e.hom ≫ ξ K Ω = ξ K Ω := by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    exact σ.commutes a
  have hκ : e.hom ≫ ξ κ Ω = ξ κ Ω := by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    exact fieldSource_arithmeticKernel_fixes_constants k K κ Ω c j hbase σ hσ a
  have hx : e.hom ≫ x = x := by
    apply pullback.hom_ext
    · rw [Category.assoc, hxκ, hκ]
    · rw [Category.assoc, hxC, ← Category.assoc, hK]
  have hnative (z : Spec (.of Ω) ⟶ C) (hz : z = ξ K Ω ≫ j)
      (hfix : e.hom ≫ z = z) :
      let πz := arithmeticFundamentalGroupHom k κ c z
      let d := Aut.of (fiberSourceIso z e ≪≫ eqToIso (congrArg fiber hfix))
      ∃ hd : πz d = 1,
        TopologicalAbelianization.mk πz.toMonoidHom.ker ⟨d, hd⟩ ≠ 1 := by
    subst z
    intro πz d
    have hd : d = q σ := by
      apply Aut.ext
      ext W w
      apply (fiberObjEquivHom (ξ K Ω ≫ j) W).injective
      ext1
      exact (fiberSourceIso_aut_point (ξ K Ω ≫ j) e hfix W w).trans
        (fundamentalGroupHom_point_of_point_action j (ξ K Ω)
          (suppliedGaloisEquivFundamentalGroup K Ω σ) σ.toRingHom
          (suppliedGaloisEquivFundamentalGroup_point K Ω σ) W w).symm
    refine ⟨(congrArg πz hd).trans hσ, ?_⟩
    simpa only [hd] using hnon
  have hz : e.hom ≫ (x ≫ pullback.snd b c) = x ≫ pullback.snd b c := by
    rw [← Category.assoc, hx]
  obtain ⟨hd, hnd⟩ := hnative (x ≫ pullback.snd b c) hxC hz
  have hg := geometric_sourceAbelianization_ne_one_of_kernel k κ C c x e hx hd hnd
  obtain ⟨E, hE, hCE, N, hN, hcomm, s, p, hs, hpC, hpE, hmove⟩ :=
    exists_pointed_finiteConstant_cover_moved_by_source k κ C c ε hε x e hx hg
  have : FiniteDimensional k E := hE
  let bE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let CE := pullback c bE
  have : IsFiniteEtale bE := constantField_specMap_isFiniteEtale k E
  have : ConnectedSpace CE := hCE
  let W : FiniteEtale C := ⟨Over.mk (pullback.fst c bE), by
    change IsFiniteEtale (pullback.fst c bE)
    infer_instance⟩
  have : ConnectedSpace W.left := hCE
  have : IsConnected W := isConnected_of_connectedSpace_left W
  have : IsIntegral CE := isIntegral_left_of_isConnected_finiteEtale W
  have : IsNormalIntegral CE := isNormalIntegral_left_of_isConnected_finiteEtale W
  have : IsGalois N := hN
  have : IsMulCommutative (Aut N) := hcomm
  have hNIntegral : IsIntegral N.left := isIntegral_left_of_isConnected_finiteEtale N
  have : IsIntegral ((𝟭 Scheme.{uGeom}).obj N.left) := hNIntegral
  have : IsFiniteEtale N.hom := N.prop
  have hp : p ≫ (N.hom ≫ pullback.fst c bE) = ξ K Ω ≫ j := hpC.trans hxC
  obtain ⟨i, hi, a, ha⟩ :=
    exists_moved_functionField_coefficient_of_finiteEtale_genericLift (C := C) (Y := N.left)
      (N.hom ≫ pullback.fst c bE) K Ω j p hp σ.toRingHom hmove
  refine ⟨E, hE, hCE, N, hN, hcomm, s, hs, hNIntegral, i, ?_, ?_, a, ha⟩
  · rw [hi]
    exact hp
  · have hspec : Spec.map (CommRingCat.ofHom
        (i.comp (AlgebraicCurve.baseToFunctionField (N.hom ≫ pullback.snd c bE)))) =
        Spec.map (CommRingCat.ofHom ((algebraMap κ Ω).comp E.val.toRingHom)) := by
      calc
        _ = p ≫ (N.hom ≫ pullback.snd c bE) :=
          genericLift_base (N.hom ≫ pullback.snd c bE) p i hi
        _ = x ≫ pullback.fst b c ≫ Spec.map (CommRingCat.ofHom E.val.toRingHom) := hpE
        _ = (x ≫ pullback.fst b c) ≫ Spec.map (CommRingCat.ofHom E.val.toRingHom) :=
          (Category.assoc _ _ _).symm
        _ = Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫
            Spec.map (CommRingCat.ofHom E.val.toRingHom) :=
          congrArg (fun q : Spec (.of Ω) ⟶ Spec (.of κ) =>
            q ≫ Spec.map (CommRingCat.ofHom E.val.toRingHom)) hxκ
        _ = _ := (Spec.map_comp _ _).symm
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)

end AnabelianGeometry.FiniteField
