/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Geometry.OriginalFiniteFieldLang
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTranslations
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Actual translations of finite-field Lang covers

Frobenius naturality proves that the original Lang map preserves the relative
group law. The same holds after extending constants. Translation by an actual
kernel section consequently preserves that same map and gives an automorphism
of its finite étale cover, and of every pullback cover. These automorphisms
commute with the actual geometric-fiber monodromy by functor naturality.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GoodReductionJacobian.RelativeGroupLaw

variable (k : Type u) [Field k] [Fintype k]
  (A : Scheme.{u}) [A.Over (Spec (CommRingCat.of k))]
  (G : RelativeGroupLaw k (A ↘ Spec (CommRingCat.of k))) (hc : G.IsCommutative)

local notation "f" => (A ↘ Spec (CommRingCat.of k))

/-- Original Frobenius preserves the given group law on every test scheme. -/
theorem originalFiniteFieldFrobeniusOver_mul {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s f) :
    NeronModelInfra.schemeHomOverComp (G.mul s x y)
        (originalFiniteFieldFrobeniusOver k A) =
      G.mul s (NeronModelInfra.schemeHomOverComp x (originalFiniteFieldFrobeniusOver k A))
        (NeronModelInfra.schemeHomOverComp y (originalFiniteFieldFrobeniusOver k A)) := by
  let : T.Over (Spec (CommRingCat.of k)) := ⟨s⟩
  have hT : T.finiteFieldFrobenius k ≫ s = s :=
    Scheme.finiteFieldFrobenius_comp_over T k
  have h (z : SchemeHomOver s f) :
      NeronModelInfra.schemeHomOverComp z (originalFiniteFieldFrobeniusOver k A) =
        GoodReductionJacobian.schemeHomOverComp (T.finiteFieldFrobenius k) hT z := by
    apply Subtype.ext
    exact (Scheme.finiteFieldFrobenius_naturality T k A z.val).symm
  exact (h (G.mul s x y)).trans
    ((G.mul_natural s s (T.finiteFieldFrobenius k) hT x y).trans
      (congrArg₂ (G.mul s) (h x).symm (h y).symm))

/-- The original Lang map is a homomorphism on all relative point groups. -/
theorem originalFiniteFieldLangMap_mul {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s f) :
    NeronModelInfra.schemeHomOverComp (G.mul s x y) (originalFiniteFieldLangMap k A G hc) =
      G.mul s (NeronModelInfra.schemeHomOverComp x (originalFiniteFieldLangMap k A G hc))
        (NeronModelInfra.schemeHomOverComp y (originalFiniteFieldLangMap k A G hc)) := by
  let : CommGroup (SchemeHomOver s f) := G.pointCommGroup hc s
  simp only [originalFiniteFieldLangMap, G.comp_langMap,
    originalFiniteFieldFrobeniusOver_mul]
  change
    (NeronModelInfra.schemeHomOverComp x (originalFiniteFieldFrobeniusOver k A) *
      NeronModelInfra.schemeHomOverComp y (originalFiniteFieldFrobeniusOver k A)) *
        (x * y)⁻¹ =
      (NeronModelInfra.schemeHomOverComp x (originalFiniteFieldFrobeniusOver k A) * x⁻¹) *
        (NeronModelInfra.schemeHomOverComp y (originalFiniteFieldFrobeniusOver k A) * y⁻¹)
  rw [mul_inv_rev, mul_comm y⁻¹ x⁻¹]
  exact mul_mul_mul_comm _ _ _ _

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "g" => pullback.snd f b
local notation "λΩ" => finiteFieldLangMap k Ω A G hc

/-- Evaluation of the geometric Lang map retains the original projection. -/
theorem finiteFieldLangMap_comp_point_toBase {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of Ω)) (x : SchemeHomOver s g) :
    baseChangePointToBase b (NeronModelInfra.schemeHomOverComp x λΩ) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase b x)
        (originalFiniteFieldLangMap k A G hc) := by
  apply Subtype.ext
  exact (Category.assoc x.val (λΩ).val (pullback.fst f b)).trans
    ((congrArg (x.val ≫ ·) (finiteFieldLangMap_comp_fst k A G hc Ω)).trans
      (Category.assoc x.val (pullback.fst f b)
        (originalFiniteFieldLangMap k A G hc).val).symm)

/-- The actual base-changed Lang map preserves the base-changed relative group law. -/
theorem finiteFieldLangMap_mul {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of Ω)) (x y : SchemeHomOver s g) :
    NeronModelInfra.schemeHomOverComp ((G.baseChange b).mul s x y) λΩ =
      (G.baseChange b).mul s (NeronModelInfra.schemeHomOverComp x λΩ)
        (NeronModelInfra.schemeHomOverComp y λΩ) := by
  apply (baseChangePointEquiv b («f» := f) s).injective
  change baseChangePointToBase b
      (NeronModelInfra.schemeHomOverComp ((G.baseChange b).mul s x y) λΩ) =
    baseChangePointToBase b ((G.baseChange b).mul s
      (NeronModelInfra.schemeHomOverComp x λΩ) (NeronModelInfra.schemeHomOverComp y λΩ))
  simp only [finiteFieldLangMap_comp_point_toBase, baseChangePointToBase_mul,
    originalFiniteFieldLangMap_mul]

/-- Translation by an actual rational point of the geometric Lang kernel
preserves the original base-changed Lang morphism. -/
theorem translate_comp_finiteFieldLangMap
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g)
    (ht : NeronModelInfra.schemeHomOverComp t λΩ = (G.baseChange b).one (𝟙 _)) :
    (G.baseChange b).translate t ≫ (λΩ).val = (λΩ).val := by
  let H := G.baseChange b
  let u : SchemeHomOver g g :=
    GoodReductionJacobian.schemeHomOverComp g (Category.comp_id g) t
  have hcomp : NeronModelInfra.schemeHomOverComp u λΩ =
      GoodReductionJacobian.schemeHomOverComp g (Category.comp_id g)
        (NeronModelInfra.schemeHomOverComp t λΩ) :=
    Subtype.ext (Category.assoc g t.val (λΩ).val)
  have hu : NeronModelInfra.schemeHomOverComp u λΩ = H.one g :=
    hcomp.trans
      ((congrArg (GoodReductionJacobian.schemeHomOverComp g (Category.comp_id g)) ht).trans
        (H.one_natural (𝟙 _) g g (Category.comp_id g)))
  have hm := finiteFieldLangMap_mul k A G hc Ω g (idPoint : SchemeHomOver g g) u
  rw [hu, H.mul_one] at hm
  have h' : NeronModelInfra.schemeHomOverComp
      ⟨H.translate t, H.translate_over t⟩ λΩ = λΩ :=
    hm.trans (schemeHomOverComp_id_left λΩ)
  exact congrArg Subtype.val h'

variable [IsAlgClosed Ω]
  (hA : AbelianSchemePropertyBundle k (A ↘ Spec (CommRingCat.of k)))

/-- The finite étale cover with precisely the actual base-changed Lang map. -/
def geometricLangCover : FiniteEtale (pullback f b) := by
  have hf : IsFinite (originalFiniteFieldLangMap k A G hc).val :=
    (originalFiniteFieldLangMap_finite_etale k A G hc Ω hA).1
  have : IsFinite (λΩ).val := MorphismProperty.of_isPullback
    (P := @IsFinite) (finiteFieldLangMap_isPullback k A G hc Ω).flip hf
  have : Etale (λΩ).val := etale_finiteFieldLangMap k Ω A G hc hA
  have : IsFiniteEtale (λΩ).val := ⟨⟩
  exact FiniteEtale.mk (λΩ).val

/-- A kernel section gives a deck automorphism of that actual finite étale cover. -/
def geometricLangCoverTranslation
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g)
    (ht : NeronModelInfra.schemeHomOverComp t λΩ = (G.baseChange b).one (𝟙 _)) :
    Aut (geometricLangCover k A G hc Ω hA) :=
  Aut.of (MorphismProperty.Over.isoMk ((G.baseChange b).sectionTranslationIso t)
    (translate_comp_finiteFieldLangMap k A G hc Ω t ht))

/-- The deck automorphism retains the original group-scheme translation. -/
theorem geometricLangCoverTranslation_hom_left
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g)
    (ht : NeronModelInfra.schemeHomOverComp t λΩ = (G.baseChange b).one (𝟙 _)) :
    (geometricLangCoverTranslation k A G hc Ω hA t ht).asIso.hom.left =
      (G.baseChange b).translate t := rfl

/-- Pulling back retains the actual covering and its kernel translations;
the pullback need not be connected. -/
def geometricLangPullbackTranslation {C : Scheme.{u}} (a : C ⟶ pullback f b)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g)
    (ht : NeronModelInfra.schemeHomOverComp t λΩ = (G.baseChange b).one (𝟙 _)) :
    Aut ((FiniteEtale.pullback a).obj (geometricLangCover k A G hc Ω hA)) :=
  (FiniteEtale.pullback a).mapAut (geometricLangCover k A G hc Ω hA)
    (geometricLangCoverTranslation k A G hc Ω hA t ht)

/-- On the Jacobian coordinate, the pulled-back automorphism is the same translation. -/
theorem geometricLangPullbackTranslation_fst {C : Scheme.{u}} (a : C ⟶ pullback f b)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g)
    (ht : NeronModelInfra.schemeHomOverComp t λΩ = (G.baseChange b).one (𝟙 _)) :
    (geometricLangPullbackTranslation k A G hc Ω hA a t ht).asIso.hom.left ≫
        pullback.fst (λΩ).val a =
      pullback.fst (λΩ).val a ≫ (G.baseChange b).translate t :=
  pullback.lift_fst _ _ _

/-- Native geometric monodromy commutes with the actual pulled-back deck translations. -/
theorem geometricLangPullbackTranslation_monodromy {C : Scheme.{u}}
    (a : C ⟶ pullback f b) (xi : Spec (CommRingCat.of Ω) ⟶ C)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g)
    (ht : NeronModelInfra.schemeHomOverComp t λΩ = (G.baseChange b).one (𝟙 _))
    (γ : π₁ᵉᵗ(xi))
    (z : (FiniteEtale.fiber xi).obj
      ((FiniteEtale.pullback a).obj (geometricLangCover k A G hc Ω hA))) :
    γ • (FiniteEtale.fiber xi).map
        (geometricLangPullbackTranslation k A G hc Ω hA a t ht).asIso.hom z =
      (FiniteEtale.fiber xi).map
        (geometricLangPullbackTranslation k A G hc Ω hA a t ht).asIso.hom (γ • z) :=
  mulAction_naturality _ _ _ _

end GoodReductionJacobian.RelativeGroupLaw
