/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Kernels
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Finite affine coverings carrying local section lifts

On a quasi-compact étale object, a section in the local image of a map of
abelian presheaves lifts over a finite affine étale covering. The lifts are
obtained by restricting actual local preimages to affine open neighborhoods.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

universe u

/-- Local preimages of a section can be chosen on a finite affine étale
covering of a quasi-compact object. -/
theorem exists_finite_affine_cover_section_lifts
    {X : Scheme.{u}} {P Q : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q)
    {U : X.Etale} [QuasiCompact (terminal.from U.left)]
    (a : Q.obj (op U))
    (ha : Presheaf.imageSieve φ a ∈ X.smallEtaleTopology U) :
    ∃ (K : Finset U.left) (V : K → X.Etale) (f : ∀ i, V i ⟶ U),
      (∀ i, IsAffine (V i).left) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
      ∀ i, ∃ t : P.obj (op (V i)), φ.app (op (V i)) t = Q.map (f i).op a := by
  classical
  let S := Presheaf.imageSieve φ a
  let A := Σ V : X.Etale, {g : V ⟶ U // S.arrows g}
  let arrow (b : A) : b.1 ⟶ U := b.2.val
  have hSieve : Sieve.ofArrows (fun b : A => b.1) arrow = S := by
    ext V g
    rw [Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨b, k, rfl⟩
      exact S.downward_closed b.2.property k
    · intro hg
      exact ⟨⟨V, ⟨g, hg⟩⟩, 𝟙 V, Category.id_comp g⟩
  have hCover : Sieve.ofArrows (fun b : A => b.1) arrow ∈
      X.smallEtaleTopology U := by
    rw [hSieve]
    exact ha
  have hRanges := (Scheme.ofArrows_mem_smallEtaleTopology_iff arrow).mp hCover
  have hLift (x : U.left) : ∃ (V : X.Etale) (f : V ⟶ U)
      (t : P.obj (op V)), IsAffine V.left ∧
        φ.app (op V) t = Q.map f.op a ∧ x ∈ Set.range f.left := by
    have hx : x ∈ ⋃ b : A, Set.range (arrow b).left := by
      rw [hRanges]
      exact Set.mem_univ x
    obtain ⟨b, y, hy⟩ := Set.mem_iUnion.mp hx
    let V := b.1
    let g : V ⟶ U := arrow b
    let t₀ := Presheaf.localPreimage φ a g b.2.property
    have ht₀ : φ.app (op V) t₀ = Q.map g.op a :=
      Presheaf.app_localPreimage φ a g b.2.property
    obtain ⟨W, hW, hyW, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := V.left) (U := ⊤) (show y ∈ ⊤ from trivial)
    let B : X.Etale := MorphismProperty.Over.mk ⊤ (W.ι ≫ V.hom) (by infer_instance)
    let l : B ⟶ V := MorphismProperty.Over.homMk W.ι (by rfl)
    refine ⟨B, l ≫ g, P.map l.op t₀, hW, ?_, ?_⟩
    · rw [NatTrans.naturality_apply, ht₀, op_comp, Q.map_comp,
        ConcreteCategory.comp_apply]
    · refine ⟨⟨y, hyW⟩, ?_⟩
      exact hy
  choose V f t hV ht hx using hLift
  have : CompactSpace U.left :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact U.left).2 inferInstance
  obtain ⟨K, hK⟩ := (isCompact_univ : IsCompact (Set.univ : Set U.left)).elim_finite_subcover
    (fun x : U.left => Set.range (f x).left)
    (fun x => (f x).left.isOpenMap.isOpen_range)
    (by intro x hxU; exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨K, (fun i => V i.1), (fun i => f i.1),
    (fun i => hV i.1), ?_, (fun i => ⟨t i.1, ht i.1⟩)⟩
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun i : K => f i.1)).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hK (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩

/-- A closed section of an exact sequence of abelian étale sheaves has
actual primitives on a finite affine étale covering of a quasi-compact
object. The covering members need not be finite over the base. -/
theorem exists_finite_affine_cover_primitive_of_exact
    {X : Scheme.{u}}
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.Exact) (U : X.Etale) [QuasiCompact (terminal.from U.left)]
    (t : S.X₂.obj.obj (op U)) (ht : S.g.hom.app (op U) t = 0) :
    ∃ (K : Finset U.left) (V : K → X.Etale) (f : ∀ i, V i ⟶ U),
      (∀ i, IsAffine (V i).left) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
      ∀ i, ∃ s : S.X₁.obj.obj (op (V i)),
        S.f.hom.app (op (V i)) s = S.X₂.obj.map (f i).op t := by
  let Γ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)
  let e : Γ.obj (kernel S.g) ≅ AddCommGrpCat.of (Γ.map S.g).hom.ker :=
    IsLimit.conePointUniqueUpToIso
      (isLimitOfHasKernelOfPreservesLimit Γ S.g)
      (AddCommGrpCat.kernelIsLimit (Γ.map S.g))
  let z : Γ.obj (kernel S.g) := e.inv ⟨t, ht⟩
  have hz : Γ.map (kernel.ι S.g) z = t := by
    have he : e.inv ≫ Γ.map (kernel.ι S.g) =
        AddCommGrpCat.ofHom (Γ.map S.g).hom.ker.subtype :=
      IsLimit.conePointUniqueUpToIso_inv_comp
        (isLimitOfHasKernelOfPreservesLimit Γ S.g)
        (AddCommGrpCat.kernelIsLimit (Γ.map S.g)) WalkingParallelPair.zero
    exact ConcreteCategory.congr_hom he ⟨t, ht⟩
  let q : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  have : Epi q := S.exact_iff_epi_kernel_lift.mp hS
  have : Sheaf.IsLocallySurjective q :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} q).mpr inferInstance
  obtain ⟨K, V, f, hV, hcover, hs⟩ :=
    exists_finite_affine_cover_section_lifts q.hom z
      (Presheaf.imageSieve_mem X.smallEtaleTopology q.hom z)
  refine ⟨K, V, f, hV, hcover, ?_⟩
  intro i
  obtain ⟨s, h⟩ := hs i
  refine ⟨s, ?_⟩
  have hq : q ≫ kernel.ι S.g = S.f := kernel.lift_ι _ _ _
  have hq' := ConcreteCategory.congr_hom
    (congrArg (fun a => a.hom.app (op (V i))) hq) s
  change (kernel.ι S.g).hom.app (op (V i)) (q.hom.app (op (V i)) s) =
    S.f.hom.app (op (V i)) s at hq'
  rw [← hq', h]
  have hn := ConcreteCategory.congr_hom
    ((kernel.ι S.g).hom.naturality (f i).op) z
  change (kernel.ι S.g).hom.app (op (V i)) ((kernel S.g).obj.map (f i).op z) =
    S.X₂.obj.map (f i).op ((Γ.map (kernel.ι S.g)) z) at hn
  rw [hn, hz]

end EtaleCohomology
