/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.ConnectedCoverCuspKernel
import Nyll.AnabelianGeometry.WeightFiltration.CommonOpenCompactificationKernel

/-! # The relative kernel at the actual recovered point

The cover below is its actual finite étale scheme morphism, at its actual
point. Packaging that morphism as a finite étale object allows the original
connected-cover theorem to apply; its generic embedding reconstructs the
prescribed point exactly. The given proper compactification is compared by
the common-open theorem, using its actual structural square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve IsDedekindDomain SchemeTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open AnabelianGeometry.WeightFiltration AnabelianGeometry.CuspidalInertia
open ProCGroups.Abelian TopologicalSpace

namespace EtaleFundamentalGroups.Inertia

private theorem recoveredRelativeKernel_overMk_inv_eq_id
    {D : Type*} [Category D] {A B : D} (xi : A ⟶ B) :
    (eqToIso (Over.mk_left xi)).inv = 𝟙 A := by
  change eqToHom (show A = A from (Over.mk_left xi).symm) = 𝟙 A
  exact eqToHom_refl A _

attribute [local instance]
  placeBaseAmbientAlgebra placeBaseAmbientTower
  extendingPlaceAmbientAlgebra extendingPlaceAmbientTower
  connectedCoverPlaceConstantAmbientTower
  CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The original base cusp relation on the actual finite étale cover is the
kernel of its given proper compactification at the same prescribed point.
The only comparison input is the scheme's structural square. -/
theorem finiteEtale_relativeRelation_eq_compactificationKernel_at_point
    {κ : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [IsCurveOver κ U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ U.functionField)
    (jU : U ⟶ M.C) [IsOpenImmersion jU]
    [QuasiCompact jU] [QuasiSeparated jU]
    (hjU : DenseRange jU)
    (hbase : algebraMap U.functionField U.functionField =
      (jU.functionFieldMap hjU).comp M.ffEquiv.toRingHom)
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]
    {Y C : Scheme} [IsIntegral Y] [IsIntegral C] [ConnectedSpace Y]
    (a : Y ⟶ U) [IsFiniteEtale a]
    (c : C ⟶ Spec (.of κ)) [IsProper c] [Smooth c]
    (jY : Y ⟶ C) [IsOpenImmersion jY]
    (hstruct : jY ≫ c = a ≫ jU ≫ M.toBase)
    (x : Spec (.of Ω) ⟶ Y)
    (hx : x ≫ a = U.genericExtensionMorphism Ω) :
    (Subgroup.closure
      {v : π₁ᵉᵗ(x) |
        pointedFundamentalGroupHom a x (U.genericExtensionMorphism Ω) hx v ∈
          conjugacySaturation
            (⋃ p : M.openBoundaryPlaces jU,
              (show Subgroup π₁ᵉᵗ(U.genericExtensionMorphism Ω) from
                genericPlaceInertia U p.val (Qfamily p)).carrier)} ⊔
      commutator π₁ᵉᵗ(x)).topologicalClosure =
        ((compactificationAbelianizationMap jY x).toMonoidHom.ker).comap
          (TopologicalAbelianization.mk π₁ᵉᵗ(x)) := by
  classical
  let W : FiniteEtale U := FiniteEtale.mk a
  let : ConnectedSpace W.left := inferInstanceAs (ConnectedSpace Y)
  let : IsConnected W := isConnected_of_connectedSpace_left W
  let w : (fiber (U.genericExtensionMorphism Ω)).obj W :=
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) W).symm (Over.homMk x hx)
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    isSeparable_functionField_of_finiteEtale_isConnected W
  let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
  let β := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra L Ω := β.toRingHom.toAlgebra
  let : IsScalarTower K L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    exact (β.commutes b).symm
  let : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K,
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let jL := W.left.fromSpecStalk (genericPoint W.left)
  let x₀ : Spec (.of Ω) ⟶ W.left := ξ L Ω ≫ jL
  let : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
  let : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    change algebraMap κ Ω b = β (algebraMap K L (algebraMap κ K b))
    exact (IsScalarTower.algebraMap_apply κ K Ω b).trans
      (β.commutes (algebraMap κ K b)).symm
  let : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
  let : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
  have hx₀ : x₀ = x := by
    have hg : g = Over.homMk x hx :=
      (fiberObjEquivHom (U.genericExtensionMorphism Ω) W).apply_symm_apply _
    have hgleft : (show Spec (.of Ω) ⟶ Y from g.left) = x :=
      congrArg
        (fun q : Over.mk (U.genericExtensionMorphism Ω) ⟶ W.toComma =>
          (show Spec (.of Ω) ⟶ Y from q.left)) hg
    have hspec : (show Spec (.of Ω) ⟶ Y from x₀) =
        (show Spec (.of Ω) ⟶ Y from g.left) := by
      change Spec.map (CommRingCat.ofHom β.toRingHom) ≫
        W.left.fromSpecStalk (genericPoint W.left) = g.left
      have hβ := finiteEtaleGenericHomFunctionFieldAlgHom_spec W g
      rw [recoveredRelativeKernel_overMk_inv_eq_id, Category.id_comp] at hβ
      exact hβ
    exact hspec.trans hgleft
  obtain ⟨Mc, jW, hopen, hjW, _hfield, hWbase, hkernel⟩ :=
    connectedCover_relativeRelation_eq_compactificationKernel_with_base
      M jU hjU hbase Qfamily W w
  let : IsOpenImmersion jW := hopen
  let hx₀a : x₀ ≫ a = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
  change (Subgroup.closure
    {v : π₁ᵉᵗ(x₀) |
      pointedFundamentalGroupHom a x₀ (U.genericExtensionMorphism Ω) hx₀a v ∈
        conjugacySaturation
          (⋃ p : M.openBoundaryPlaces jU,
            (show Subgroup π₁ᵉᵗ(U.genericExtensionMorphism Ω) from
              genericPlaceInertia U p.val (Qfamily p)).carrier)} ⊔
    commutator π₁ᵉᵗ(x₀)).topologicalClosure =
      ((compactificationAbelianizationMap jW x₀).toMonoidHom.ker).comap
        (TopologicalAbelianization.mk π₁ᵉᵗ(x₀)) at hkernel
  have hcommon : jW ≫ Mc.toBase = jY ≫ c := hWbase.trans hstruct.symm
  let : IsOpenImmersion (show W.left ⟶ C from jY) :=
    (inferInstance : IsOpenImmersion jY)
  have hcompare := compactificationAbelianizationMap_ker_eq_of_common_open
    Mc.toBase c jW jY hcommon x₀
  rw [hcompare] at hkernel
  -- Generalize the endpoint before eliminating the point equality: x₀ itself
  -- depends on the original x through its specified fiber lift.
  let P (y : Spec (.of Ω) ⟶ Y)
      (hy : y ≫ a = U.genericExtensionMorphism Ω) : Prop :=
    (Subgroup.closure
      {v : π₁ᵉᵗ(y) |
        pointedFundamentalGroupHom a y (U.genericExtensionMorphism Ω) hy v ∈
          conjugacySaturation
            (⋃ p : M.openBoundaryPlaces jU,
              (show Subgroup π₁ᵉᵗ(U.genericExtensionMorphism Ω) from
                genericPlaceInertia U p.val (Qfamily p)).carrier)} ⊔
      commutator π₁ᵉᵗ(y)).topologicalClosure =
        ((compactificationAbelianizationMap jY y).toMonoidHom.ker).comap
          (TopologicalAbelianization.mk π₁ᵉᵗ(y))
  change P x hx
  have hkernel' : P x₀ hx₀a := hkernel
  have htransport : ∀ (y : Spec (.of Ω) ⟶ Y)
      (hy : y ≫ a = U.genericExtensionMorphism Ω), x₀ = y → P y hy := by
    intro y hy hxy
    subst y
    exact hkernel'
  exact htransport x hx hx₀

end EtaleFundamentalGroups.Inertia
