/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PointedGaloisModel
public import Nyll.EtaleFundamentalGroups.GaloisCovers.AbelianCoverDetection
public import Nyll.EtaleFundamentalGroups.GeometricFiber.NontrivialActionTransport

/-!
# Rationally pointed finite constant models detect the original abelianization

The native geometric element is first detected by an actual abelian cover.
Finite coefficient descent and adjoining a lift of the chosen rational
point give a rationally pointed arithmetic model. Its original pullback
and fiber comparison preserve the same nontrivial action. Thus the finite
models used for Hilbert class fields form a detecting family for the
original geometric abelianization.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry ProCGroups.Abelian

namespace EtaleFundamentalGroups

universe u

/-- Every nontrivial geometric abelianization class acts nontrivially on
an actual abelian finite étale cover over a finite constant field which
has a rational lift of the specified base point. The action is the one
induced by the literal coefficient inclusion. -/
theorem exists_pointed_finiteConstant_cover_detecting_abelianization
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] [IsSepClosed L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (c : X ⟶ Spec (.of k))
    (ε : Spec (.of k) ⟶ X) (hε : ε ≫ c = 𝟙 _)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] :
    let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let XL := Limits.pullback φL c
    ∀ [ConnectedSpace XL] (x : Spec (.of Ω) ⟶ XL) (g : π₁ᵉᵗ(x)),
      TopologicalAbelianization.mk π₁ᵉᵗ(x) g ≠ 1 →
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
      let XE := Limits.pullback φE c
      let εE : Spec (.of E) ⟶ XE := Limits.pullback.lift (𝟙 _) (φE ≫ ε)
        (by rw [Category.id_comp, Category.assoc, hε, Category.comp_id])
      let bE : XL ⟶ XE := Limits.pullback.map φL c φE c
        (Spec.map (CommRingCat.ofHom E.val.toRingHom)) (𝟙 X) (𝟙 _)
        (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
        (by rw [Category.comp_id, Category.id_comp])
      ∃ hXE : ConnectedSpace XE,
        let _ : ConnectedSpace XE := hXE
        ∃ (N : FiniteEtale XE) (_ : IsGalois N) (_ : IsMulCommutative (Aut N))
          (s : Spec (.of E) ⟶ N.left),
          s ≫ N.hom = εE ∧
          ∃ y : (FiniteEtale.fiber (x ≫ bE)).obj N,
            FiniteEtale.fundamentalGroupHom bE x g • y ≠ y := by
  intro φL XL hXL x g hg
  obtain ⟨Z, hZ, hcommZ, z, hz⟩ :=
    exists_abelian_galoisCover_quotient_ne_one x g hg
  have hGaloisZ : IsGalois Z := hZ
  have habelianZ : IsMulCommutative (Aut Z) := hcommZ
  have hzmove : g • z ≠ z := by
    intro hfix
    apply hz
    change g ∈ (finiteEtaleGaloisCoverQuotientMonoidHom x Z hZ z).ker
    rw [finiteEtaleGaloisCoverQuotientMonoidHom_ker]
    exact hfix
  obtain ⟨E, hE, hXE, N, hN, hcommN, ⟨eN⟩, s, hs⟩ :=
    exists_finiteIntermediateField_pointed_abelian_galois_model k L X c ε hε Z
  let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let XE := Limits.pullback φE c
  have hconnectedE : ConnectedSpace XE := hXE
  have hGaloisN : IsGalois N := hN
  let bE : XL ⟶ XE := Limits.pullback.map φL c φE c
    (Spec.map (CommRingCat.ofHom E.val.toRingHom)) (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  exact ⟨E, hE, hXE, N, hN, hcommN, s, hs,
    FiniteEtale.exists_moved_fiberPoint_of_recovery bE x g N Z eN z hzmove⟩

end EtaleFundamentalGroups
