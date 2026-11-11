/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldGaloisAction
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.FieldFiniteCover
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionSplitting
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFibers
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Extensions
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient

/-!
# Descent from actual finite-Galois cocycle primitives

This factors the geometric descent argument out of Hilbert 90. Coefficient
specific acyclicity is supplied separately; no comparison of derived
sheaf cohomology with Galois cohomology is assumed.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

/-- A proved cocycle primitive corrects a local lift to an invariant one. -/
theorem exists_fieldGalois_invariant_lift_of_cocycle_primitives
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {A B Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (i : A ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (hprimitive : ∀ (c : Gal(L/K) → A.obj.obj
        (op ((finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K L))))),
      (∀ σ τ, c (σ * τ) = (fieldGaloisSheafAction K L A σ).asIso.hom (c τ) + c σ) →
      ∃ a, ∀ σ : Gal(L/K), (fieldGaloisSheafAction K L A σ).asIso.hom a - a = c σ)
    (e : B.obj.obj (op ((finiteEtaleInclusion (Spec (.of K))).obj
      (FiniteEtale.mk (ξ K L)))))
    (he : ∀ σ : Gal(L/K),
      (fieldGaloisSheafAction K L Q σ).asIso.hom
        (p.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
          (FiniteEtale.mk (ξ K L)))) e) =
        p.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
          (FiniteEtale.mk (ξ K L)))) e) :
    ∃ e' : B.obj.obj (op ((finiteEtaleInclusion (Spec (.of K))).obj
        (FiniteEtale.mk (ξ K L)))),
      p.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
        (FiniteEtale.mk (ξ K L)))) e' =
          p.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
            (FiniteEtale.mk (ξ K L)))) e ∧
      ∀ σ : Gal(L/K), (fieldGaloisSheafAction K L B σ).asIso.hom e' = e' := by
  let X : Scheme.{u} := Spec (.of K)
  let V : X.Etale := (finiteEtaleInclusion X).obj (FiniteEtale.mk (ξ K L))
  let ρA : Gal(L/K) →* Aut (A.obj.obj (op V)) := fieldGaloisSheafAction K L A
  let ρB : Gal(L/K) →* Aut (B.obj.obj (op V)) := fieldGaloisSheafAction K L B
  let ρQ : Gal(L/K) →* Aut (Q.obj.obj (op V)) := fieldGaloisSheafAction K L Q
  let Γ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have hseq : ((ShortComplex.mk i p hz).map Γ).Exact :=
    hS.exact.map_of_mono_of_preservesKernel Γ hS.mono_f inferInstance
  have : Mono i := hS.mono_f
  have hi : Function.Injective (i.hom.app (op V)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  have ni (σ : Gal(L/K)) (a : A.obj.obj (op V)) :
      i.hom.app (op V) ((ρA σ).asIso.hom a) =
        (ρB σ).asIso.hom (i.hom.app (op V) a) :=
    ConcreteCategory.congr_hom (fieldGaloisSheafAction_naturality K L i σ) a
  have np (σ : Gal(L/K)) (b : B.obj.obj (op V)) :
      p.hom.app (op V) ((ρB σ).asIso.hom b) =
        (ρQ σ).asIso.hom (p.hom.app (op V) b) :=
    ConcreteCategory.congr_hom (fieldGaloisSheafAction_naturality K L p σ) b
  have hex (σ : Gal(L/K)) : ∃ a : A.obj.obj (op V),
      i.hom.app (op V) a = (ρB σ).asIso.hom e - e := by
    apply (ShortComplex.ab_exact_iff _).mp hseq
    change p.hom.app (op V) ((ρB σ).asIso.hom e - e) = 0
    rw [map_sub, np, he, sub_self]
  choose c hc using hex
  have hcoc (σ τ : Gal(L/K)) : c (σ * τ) = (ρA σ).asIso.hom (c τ) + c σ := by
    apply hi
    rw [map_add, hc, ni, hc, hc]
    have hm : (ρB (σ * τ)).asIso.hom e = (ρB σ).asIso.hom ((ρB τ).asIso.hom e) :=
      congrArg (fun a : Aut (B.obj.obj (op V)) => a.asIso.hom e) (map_mul ρB σ τ)
    rw [hm, map_sub, sub_add_sub_cancel]
  obtain ⟨a, ha'⟩ := hprimitive c hcoc
  have ha (σ : Gal(L/K)) : (ρA σ).asIso.hom a = c σ + a :=
    (sub_eq_iff_eq_add).mp (ha' σ)
  refine ⟨e - i.hom.app (op V) a, ?_, ?_⟩
  · have hz' : p.hom.app (op V) (i.hom.app (op V) a) = 0 :=
      ConcreteCategory.congr_hom (congrArg (fun f => f.hom.app (op V)) hz) a
    change p.hom.app (op V) (e - i.hom.app (op V) a) = _
    rw [map_sub, hz', sub_zero]
  · intro σ
    change (ρB σ).asIso.hom (e - i.hom.app (op V) a) = e - i.hom.app (op V) a
    rw [map_sub, ← ni, ha, map_add, hc, sub_add_eq_sub_sub, sub_sub_cancel]


/-- Primitives for every finite-Galois difference cocycle yield actual
global section lifting by geometric descent. -/
theorem exists_section_lift_of_fieldGalois_cocycle_primitives
    (K : Type u) [Field K]
    {A B Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (i : A ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (hprimitive : ∀ (L : Type u) [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L]
      (c : Gal(L/K) → A.obj.obj
        (op ((finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K L))))),
      (∀ σ τ, c (σ * τ) = (fieldGaloisSheafAction K L A σ).asIso.hom (c τ) + c σ) →
      ∃ a, ∀ σ : Gal(L/K), (fieldGaloisSheafAction K L A σ).asIso.hom a - a = c σ)
    (q : Q.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) :
    ∃ b : B.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))),
      p.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) b = q := by
  let X : Scheme.{u} := Spec (.of K)
  have : Epi p := hS.epi_g
  have : Sheaf.IsLocallySurjective p :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} p).mpr inferInstance
  obtain ⟨L, f, e, he⟩ :=
    exists_finiteGalois_mem_covering_sieve_of_field K (Presheaf.imageSieve p.hom q)
      (Presheaf.imageSieve_mem X.smallEtaleTopology p.hom q)
  let Y : FiniteEtale X := FiniteEtale.mk (ξ K L)
  let V : X.Etale := (finiteEtaleInclusion X).obj Y
  have hf : f = finiteEtaleCoverBaseMap X Y := by
    apply MorphismProperty.Over.Hom.ext
    exact (Category.comp_id f.left).symm.trans f.w
  change p.hom.app (op V) e = Q.obj.map f.op q at he
  rw [hf] at he
  let Q₀ : Sheaf X.smallEtaleTopology (Type u) :=
    (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj Q
  let B₀ : Sheaf X.smallEtaleTopology (Type u) :=
    (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj B
  have heinv (σ : Gal(L/K)) :
      (fieldGaloisSheafAction K L Q σ).asIso.hom (p.hom.app (op V) e) =
        p.hom.app (op V) e := by
    rw [he]
    exact finiteEtaleSheaf_restrict_invariant X Q₀ Y q
      (MulOpposite.unop
        (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L σ))
  obtain ⟨e', hp', he'⟩ := exists_fieldGalois_invariant_lift_of_cocycle_primitives K L i p hz hS
    (hprimitive L) e heinv
  have hinv (σ : Aut Y) :
      B₀.obj.map ((finiteEtaleInclusion X).map σ.asIso.hom).op e' = e' := by
    obtain ⟨τ, hτ⟩ :=
      (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L).surjective
        (MulOpposite.op σ)
    have h := he' τ
    change B.obj.map ((finiteEtaleInclusion X).map
      (MulOpposite.unop
        (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L τ)).asIso.hom).op e' =
          e' at h
    rw [hτ] at h
    exact h
  have : PreGaloisCategory.IsGalois Y :=
    EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L
  obtain ⟨b, hb, _⟩ := existsUnique_section_of_galois_invariant X B₀ Y e' hinv
  refine ⟨b, ?_⟩
  have : ConnectedSpace Y.left := FiniteEtale.connectedSpace_left_of_isConnected Y
  have : Surjective Y.hom :=
    IsFiniteEtale.surjective (show Y.left ⟶ X from Y.hom)
  apply finiteEtaleSheaf_restrict_injective X Q₀ Y
  have hn := ConcreteCategory.congr_hom
    (p.hom.naturality (finiteEtaleCoverBaseMap X Y).op) b
  change p.hom.app (op V) (B.obj.map (finiteEtaleCoverBaseMap X Y).op b) =
    Q.obj.map (finiteEtaleCoverBaseMap X Y).op
      (p.hom.app (op (Scheme.Etale.mk (𝟙 X))) b) at hn
  exact hn.symm.trans ((congrArg (p.hom.app (op V)) hb).trans (hp'.trans he))

/-- Actual derived degree-one sheaf cohomology vanishes when all its
finite-Galois section cocycles have primitives. -/
theorem etaleH1_eq_zero_of_fieldGalois_cocycle_primitives
    (K : Type u) [Field K]
    (A : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (hprimitive : ∀ (L : Type u) [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L]
      (c : Gal(L/K) → A.obj.obj
        (op ((finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K L))))),
      (∀ σ τ, c (σ * τ) = (fieldGaloisSheafAction K L A σ).asIso.hom (c τ) + c σ) →
      ∃ a, ∀ σ : Gal(L/K), (fieldGaloisSheafAction K L A σ).asIso.hom a - a = c σ)
    (a : Sheaf.H.{u} A 1) : a = 0 := by
  let X : Scheme.{u} := Spec (.of K)
  obtain ⟨B, i, p, hz, hS, hclass⟩ :=
    EtaleFundamentalGroups.Cohomology.exists_h1_extension X A a
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let Z : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let eT : (freeAbelianSheafYoneda X.smallEtaleTopology).obj T ≅ Z :=
    freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology hT
  let one : Z.obj.obj (op T) :=
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T Z eT.hom
  obtain ⟨b, hb⟩ := exists_section_lift_of_fieldGalois_cocycle_primitives K i p hz hS hprimitive one
  let d : (freeAbelianSheafYoneda X.smallEtaleTopology).obj T ⟶ B :=
    (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T B).symm b
  have hd : d ≫ p = eT.hom := by
    apply (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T Z).injective
    rw [freeAbelianSheafYonedaHomEquiv_postcomp]
    change p.hom.app (op T)
      (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T B
        ((freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T B).symm b)) = one
    rw [Equiv.apply_symm_apply]
    exact hb
  have hsplit : (eT.inv ≫ d) ≫ p = 𝟙 Z := by
    rw [Category.assoc, hd, eT.inv_hom_id]
  rw [← hclass]
  exact (EtaleFundamentalGroups.Cohomology.extClass_eq_zero_iff_exists_section hS).mpr
    ⟨eT.inv ≫ d, hsplit⟩


end EtaleCohomology
