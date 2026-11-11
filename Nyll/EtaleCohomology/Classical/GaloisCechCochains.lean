/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.InjectiveCechSections
public import Nyll.EtaleCohomology.Sites.GaloisCechSections
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.GaloisCovers.TripleProduct
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Deck coordinates on the original free abelian Cech cochains

An actual deck cochain defines a map from the original free edge sheaf,
using the actual self-product section and the existing section cochain.
Its triangle differential is computed on the original free generators.
Actual triple deck graphs also detect equality of maps from the original
free triangle sheaf. Thus pointwise deck calculations can be used in the
native two-step Cech presentation without changing its resolution.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open CategoryTheory.PreGaloisCategory

namespace EtaleCohomology

variable (X : Scheme.{u}) [ConnectedSpace X]
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
  (Y : FiniteEtale X) [IsGalois Y]

local notation "I" => finiteEtaleInclusion X
local notation "J" => X.smallEtaleTopology

omit [ConnectedSpace X] [IsGalois Y] in
/-- An actual deck graph gives its original free Cech edge. -/
def galoisCechEdge {T : X.Etale} (hT : IsTerminal T)
    (f : (I).obj Y ⟶ T) (σ : Aut Y) :
    CechEdge (fun a : (I).obj Y ⟶ (I).obj Y => a ≫ f) :=
  ⟨𝟙 _, (I).map σ.asIso.hom, hT.hom_ext _ _⟩

/-- Actual deck graphs detect equality of morphisms from the
original free edge sheaf, including morphisms to the divisor quotient. -/
theorem abelianCechEdgeHom_ext_galois
    {T : X.Etale} (hT : IsTerminal T) (f : (I).obj Y ⟶ T)
    (a b : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ F)
    (h : ∀ σ : Aut Y,
      (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F a).app (op ((I).obj Y)))
          (FreeAbelianGroup.of (galoisCechEdge X Y hT f σ)) =
        (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F b).app (op ((I).obj Y)))
          (FreeAbelianGroup.of (galoisCechEdge X Y hT f σ))) : a = b := by
  let P := cechEdgeFunctor (yoneda.map f)
  let a' := freeAbelianSheafHomEquiv X P F a
  let b' := freeAbelianSheafHomEquiv X P F b
  let p₀ : P.obj (op ((I).obj (Y ⨯ Y))) :=
    ⟨(I).map prod.fst, (I).map prod.snd, hT.hom_ext _ _⟩
  have hg (σ : Aut Y) : P.map ((I).map (prod.lift (𝟙 Y) σ.asIso.hom)).op p₀ =
      galoisCechEdge X Y hT f σ := by
    apply CechEdge.ext
    · change (I).map (prod.lift (𝟙 Y) σ.asIso.hom) ≫ (I).map prod.fst = 𝟙 _
      rw [← (I).map_comp, prod.lift_fst, (I).map_id]
    · change (I).map (prod.lift (𝟙 Y) σ.asIso.hom) ≫ (I).map prod.snd = (I).map σ.asIso.hom
      rw [← (I).map_comp, prod.lift_snd]
  have hs : a'.app (op ((I).obj (Y ⨯ Y))) p₀ = b'.app (op ((I).obj (Y ⨯ Y))) p₀ := by
    apply (galoisSelfProductSectionsAddEquiv X F Y).injective
    funext σ
    rw [galoisSelfProductSectionsAddEquiv_apply, galoisSelfProductSectionsAddEquiv_apply]
    have ha := ConcreteCategory.congr_hom (a'.naturality
      ((I).map (prod.lift (𝟙 Y) σ.asIso.hom)).op) p₀
    have hb := ConcreteCategory.congr_hom (b'.naturality
      ((I).map (prod.lift (𝟙 Y) σ.asIso.hom)).op) p₀
    simp only [ConcreteCategory.comp_apply] at ha hb
    rw [hg] at ha hb
    exact ha.symm.trans ((h σ).trans hb)
  apply (freeAbelianSheafHomEquiv X P F).injective
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro p
  let e := PreservesLimitPair.iso I Y Y
  let m : V.unop ⟶ (I).obj (Y ⨯ Y) := prod.lift p.first p.second ≫ e.inv
  have hm : P.map m.op p₀ = p := by
    apply CechEdge.ext
    · change m ≫ (I).map prod.fst = p.first
      rw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
    · change m ≫ (I).map prod.snd = p.second
      rw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]
  have ha := ConcreteCategory.congr_hom (a'.naturality m.op) p₀
  have hb := ConcreteCategory.congr_hom (b'.naturality m.op) p₀
  simp only [ConcreteCategory.comp_apply] at ha hb
  rw [hm] at ha hb
  exact ha.trans ((congrArg (F.obj.map m.op) hs).trans hb.symm)

omit [ConnectedSpace X] [IsGalois Y] in
/-- A specified divisor vertex has its original second-minus-first
deck difference on the actual free edge. -/
theorem abelianCechVertexBoundary_galois_coordinate
    {T : X.Etale} (hT : IsTerminal T) (f : (I).obj Y ⟶ T)
    (v : (freeAbelianSheafYoneda J).obj ((I).obj Y) ⟶ F) (σ : Aut Y) :
    (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F
      ((presheafToSheaf J AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat (yoneda.map f)) ≫ v)).app
      (op ((I).obj Y))) (FreeAbelianGroup.of (galoisCechEdge X Y hT f σ)) =
      F.obj.map ((I).map σ.asIso.hom).op
          (freeAbelianSheafYonedaHomEquiv J ((I).obj Y) F v) -
        freeAbelianSheafYonedaHomEquiv J ((I).obj Y) F v := by
  let q := (sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
    (yoneda.obj ((I).obj Y) ⋙ AddCommGrpCat.free) F v
  let q₀ : FreeAbelianGroup ((I).obj Y ⟶ (I).obj Y) →+
      F.obj.obj (op ((I).obj Y)) :=
    (q.app (op ((I).obj Y))).hom
  rw [Adjunction.homEquiv_naturality_left]
  change q₀
    (freeCechEdgeBoundary (fun k : (I).obj Y ⟶ (I).obj Y => k ≫ f)
      (FreeAbelianGroup.of (galoisCechEdge X Y hT f σ))) = _
  rw [freeCechEdgeBoundary, FreeAbelianGroup.lift_apply_of, map_sub]
  have hn := ConcreteCategory.congr_hom (q.naturality ((I).map σ.asIso.hom).op)
    (FreeAbelianGroup.of (𝟙 ((I).obj Y)))
  change q₀ (FreeAbelianGroup.of ((I).map σ.asIso.hom ≫ 𝟙 _)) =
    F.obj.map ((I).map σ.asIso.hom).op
      (q₀ (FreeAbelianGroup.of (𝟙 _))) at hn
  rw [Category.comp_id] at hn
  exact congrArg (fun z => z - q₀ (FreeAbelianGroup.of (𝟙 _))) hn

/-- An actual triple deck graph gives its original free Cech triangle. -/
def galoisCechTriangle {T : X.Etale} (hT : IsTerminal T)
    (f : (I).obj Y ⟶ T) (σ τ : Aut Y) :
    CechTriangle (fun a : (I).obj Y ⟶ (I).obj Y => a ≫ f) :=
  ⟨𝟙 _, (I).map σ.asIso.hom, (I).map (σ.asIso.hom ≫ τ.asIso.hom), hT.hom_ext _ _, hT.hom_ext _ _⟩

/-- Restriction to actual triple deck graphs detects equality of maps
from the same original free abelian triangle sheaf. -/
theorem abelianCechTriangleHom_ext_galois
    {T : X.Etale} (hT : IsTerminal T) (f : (I).obj Y ⟶ T)
    (a b : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (cechTriangleFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ F)
    (h : ∀ σ τ : Aut Y,
      (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F a).app (op ((I).obj Y)))
          (FreeAbelianGroup.of (galoisCechTriangle X Y hT f σ τ)) =
        (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F b).app (op ((I).obj Y)))
          (FreeAbelianGroup.of (galoisCechTriangle X Y hT f σ τ))) : a = b := by
  let a' := (sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F a
  let b' := (sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F b
  have hn (q : cechTriangleFunctor (yoneda.map f) ⋙ AddCommGrpCat.free ⟶ F.obj)
      {V W : X.Etale} (g : V ⟶ W)
      (t : (cechTriangleFunctor (yoneda.map f)).obj (op W)) :
      (q.app (op V))
          (FreeAbelianGroup.of ((cechTriangleFunctor (yoneda.map f)).map g.op t)) =
        F.obj.map g.op ((q.app (op W)) (FreeAbelianGroup.of t)) := by
    have hn := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
      (q.naturality g.op) (FreeAbelianGroup.of t)
    change (q.app (op V))
        (FreeAbelianGroup.map ((cechTriangleFunctor (yoneda.map f)).map g.op)
          (FreeAbelianGroup.of t)) =
      F.obj.map g.op ((q.app (op W)) (FreeAbelianGroup.of t)) at hn
    simpa only [FreeAbelianGroup.map_of_apply] using hn
  let t₀ : (cechTriangleFunctor (yoneda.map f)).obj
      (op ((I).obj (Y ⨯ (Y ⨯ Y)))) :=
    ⟨(I).map prod.fst, (I).map (prod.snd ≫ prod.fst), (I).map (prod.snd ≫ prod.snd),
      hT.hom_ext _ _, hT.hom_ext _ _⟩
  have hg (σ τ : Aut Y) :
      (cechTriangleFunctor (yoneda.map f)).map ((I).map (galoisTripleGraph Y σ τ)).op t₀ =
        galoisCechTriangle X Y hT f σ τ := by
    apply CechTriangle.ext
    · change (I).map (galoisTripleGraph Y σ τ) ≫ (I).map prod.fst = 𝟙 _
      rw [← (I).map_comp, galoisTripleGraph, prod.lift_fst, (I).map_id]
    · change (I).map (galoisTripleGraph Y σ τ) ≫ (I).map (prod.snd ≫ prod.fst) =
        (I).map σ.asIso.hom
      rw [← (I).map_comp, ← Category.assoc, galoisTripleGraph,
        prod.lift_snd, prod.lift_fst]
    · change (I).map (galoisTripleGraph Y σ τ) ≫ (I).map (prod.snd ≫ prod.snd) =
        (I).map (σ.asIso.hom ≫ τ.asIso.hom)
      rw [← (I).map_comp, ← Category.assoc, galoisTripleGraph,
        prod.lift_snd, prod.lift_snd]
  have hs : (a'.app (op ((I).obj (Y ⨯ (Y ⨯ Y))))) (FreeAbelianGroup.of t₀) =
      (b'.app (op ((I).obj (Y ⨯ (Y ⨯ Y))))) (FreeAbelianGroup.of t₀) := by
    apply galoisTripleProduct_sections_ext X
      ((sheafCompose J (forget AddCommGrpCat.{u})).obj F) Y
    intro σ τ
    change F.obj.map ((I).map (galoisTripleGraph Y σ τ)).op
        ((a'.app (op ((I).obj (Y ⨯ (Y ⨯ Y))))) (FreeAbelianGroup.of t₀)) =
      F.obj.map ((I).map (galoisTripleGraph Y σ τ)).op
        ((b'.app (op ((I).obj (Y ⨯ (Y ⨯ Y))))) (FreeAbelianGroup.of t₀))
    rw [← hn a', ← hn b', hg]
    exact h σ τ
  apply ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F).injective
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro t
  let e := PreservesLimitPair.iso I Y Y
  let e' := PreservesLimitPair.iso I Y (Y ⨯ Y)
  let m : V.unop ⟶ (I).obj (Y ⨯ (Y ⨯ Y)) :=
    prod.lift t.first (prod.lift t.second t.third ≫ e.inv) ≫ e'.inv
  have mf : m ≫ (I).map prod.fst = t.first := by
    dsimp only [m]
    rw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
  have ms : m ≫ (I).map prod.snd = prod.lift t.second t.third ≫ e.inv := by
    dsimp only [m]
    rw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]
  have hm : (cechTriangleFunctor (yoneda.map f)).map m.op t₀ = t := by
    apply CechTriangle.ext
    · change m ≫ (I).map prod.fst = t.first
      exact mf
    · change m ≫ (I).map (prod.snd ≫ prod.fst) = t.second
      rw [(I).map_comp, ← Category.assoc, ms, Category.assoc,
        PreservesLimitPair.iso_inv_fst, prod.lift_fst]
    · change m ≫ (I).map (prod.snd ≫ prod.snd) = t.third
      rw [(I).map_comp, ← Category.assoc, ms, Category.assoc,
        PreservesLimitPair.iso_inv_snd, prod.lift_snd]
  change (a'.app V) (FreeAbelianGroup.of t) = (b'.app V) (FreeAbelianGroup.of t)
  rw [← hm, hn a', hn b', hs]

/-- An arbitrary actual deck cochain as a map from the original free
abelian edge sheaf. It uses the existing self-pullback section cochain. -/
def galoisCechEdgeCochain {T : X.Etale} (f : (I).obj Y ⟶ T) [HasPullback f f]
    (c : Aut Y → F.obj.obj (op ((I).obj Y))) :
    (presheafToSheaf J AddCommGrpCat.{u}).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ F :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F).symm
    (cechSectionCochain J f F
      (F.obj.map
        (prod.lift (pullback.fst f f) (pullback.snd f f) ≫
          (PreservesLimitPair.iso I Y Y).inv).op
        ((galoisSelfProductSectionsAddEquiv X F Y).symm c)))

/-- The constructed edge map retains its value on every original
generator, before any cohomology class is formed. -/
theorem galoisCechEdgeCochain_generator
    {T : X.Etale} (f : (I).obj Y ⟶ T) [HasPullback f f]
    (c : Aut Y → F.obj.obj (op ((I).obj Y)))
    (V : X.Etale) (p : CechEdge (fun k : V ⟶ (I).obj Y => k ≫ f)) :
    (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F
      (galoisCechEdgeCochain X F Y f c)).app (op V))
        (FreeAbelianGroup.of p) =
      F.obj.map (prod.lift p.first p.second ≫ (PreservesLimitPair.iso I Y Y).inv).op
        ((galoisSelfProductSectionsAddEquiv X F Y).symm c) := by
  rw [galoisCechEdgeCochain, Equiv.apply_symm_apply]
  change (FreeAbelianGroup.lift fun q =>
      F.obj.map (pullback.lift q.first q.second q.same).op
        (F.obj.map
          (prod.lift (pullback.fst f f) (pullback.snd f f) ≫
            (PreservesLimitPair.iso I Y Y).inv).op
          ((galoisSelfProductSectionsAddEquiv X F Y).symm c)))
    (FreeAbelianGroup.of p) = _
  rw [FreeAbelianGroup.lift_apply_of]
  have hp : pullback.lift p.first p.second p.same ≫
      prod.lift (pullback.fst f f) (pullback.snd f f) =
        prod.lift p.first p.second := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, pullback.lift_fst, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, pullback.lift_snd, prod.lift_snd]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← Category.assoc, hp]

omit [ConnectedSpace X] [IsGalois Y] in
private theorem inclusion_pair_lift (U : FiniteEtale X) (a b : U ⟶ Y) :
    prod.lift ((I).map a) ((I).map b) ≫ (PreservesLimitPair.iso I Y Y).inv =
      (I).map (prod.lift a b) := by
  let e := PreservesLimitPair.iso I Y Y
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  have hfst : e.hom ≫ prod.fst = (I).map prod.fst :=
    (congrArg (fun k => k ≫ prod.fst) (PreservesLimitPair.iso_hom I Y Y)).trans
      (prodComparison_fst I Y Y)
  have hsnd : e.hom ≫ prod.snd = (I).map prod.snd :=
    (congrArg (fun k => k ≫ prod.snd) (PreservesLimitPair.iso_hom I Y Y)).trans
      (prodComparison_snd I Y Y)
  apply prod.hom_ext
  · rw [prod.lift_fst, Category.assoc, hfst, ← (I).map_comp, prod.lift_fst]
  · rw [prod.lift_snd, Category.assoc, hsnd, ← (I).map_comp, prod.lift_snd]

/-- The constructed original edge map has precisely its specified
deck value on every actual deck graph. -/
theorem galoisCechEdgeCochain_edge_coordinate
    {T : X.Etale} (hT : IsTerminal T) (f : (I).obj Y ⟶ T) [HasPullback f f]
    (c : Aut Y → F.obj.obj (op ((I).obj Y))) (σ : Aut Y) :
    (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F
      (galoisCechEdgeCochain X F Y f c)).app (op ((I).obj Y)))
        (FreeAbelianGroup.of (galoisCechEdge X Y hT f σ)) = c σ := by
  rw [galoisCechEdgeCochain_generator]
  change F.obj.map
      (prod.lift (𝟙 _) ((I).map σ.asIso.hom) ≫ (PreservesLimitPair.iso I Y Y).inv).op
      ((galoisSelfProductSectionsAddEquiv X F Y).symm c) = c σ
  rw [← (I).map_id Y, inclusion_pair_lift, ← galoisSelfProductSectionsAddEquiv_apply]
  exact congrFun ((galoisSelfProductSectionsAddEquiv X F Y).apply_symm_apply c) σ

/-- The differential of the original edge map on an original triple
generator is exactly the inhomogeneous deck differential. -/
theorem galoisCechEdgeCochain_triangle_coordinate
    {T : X.Etale} (hT : IsTerminal T) (f : (I).obj Y ⟶ T) [HasPullback f f]
    (c : Aut Y → F.obj.obj (op ((I).obj Y))) (σ τ : Aut Y) :
    (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F
      ((presheafToSheaf J AddCommGrpCat.{u}).map (freeCechTriangleBoundaryNat (yoneda.map f)) ≫
        galoisCechEdgeCochain X F Y f c)).app (op ((I).obj Y)))
        (FreeAbelianGroup.of (galoisCechTriangle X Y hT f σ τ)) =
      F.obj.map ((I).map σ.asIso.hom).op (c τ) - c (τ * σ) + c σ := by
  let e := PreservesLimitPair.iso I Y Y
  let z := (galoisSelfProductSectionsAddEquiv X F Y).symm c
  have hgeom := galoisCechSection_triangle_coordinate X F Y c σ τ
  change F.obj.map ((I).map (galoisTripleGraph Y σ τ)).op
      (F.obj.map ((I).map prod.snd).op z -
        F.obj.map ((I).map (prod.lift prod.fst (prod.snd ≫ prod.snd))).op z +
        F.obj.map ((I).map (prod.lift prod.fst (prod.snd ≫ prod.fst))).op z) = _ at hgeom
  have h₂₃ : galoisTripleGraph Y σ τ ≫ prod.snd =
      prod.lift σ.asIso.hom (σ.asIso.hom ≫ τ.asIso.hom) := by
    rw [galoisTripleGraph, prod.lift_snd]
  have h₁₃ : galoisTripleGraph Y σ τ ≫
      prod.lift prod.fst (prod.snd ≫ prod.snd) =
        prod.lift (𝟙 Y) (σ.asIso.hom ≫ τ.asIso.hom) := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, galoisTripleGraph, prod.lift_fst,
        prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, ← Category.assoc, h₂₃,
        prod.lift_snd, prod.lift_snd]
  have h₁₂ : galoisTripleGraph Y σ τ ≫
      prod.lift prod.fst (prod.snd ≫ prod.fst) = prod.lift (𝟙 Y) σ.asIso.hom := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, galoisTripleGraph, prod.lift_fst,
        prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, ← Category.assoc, h₂₃,
        prod.lift_fst, prod.lift_snd]
  simp only [map_add, map_sub, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, h₂₃, h₁₃, h₁₂] at hgeom
  let q : FreeAbelianGroup
      (CechEdge (fun a : (I).obj Y ⟶ (I).obj Y => a ≫ f)) →+
        F.obj.obj (op ((I).obj Y)) :=
    ((((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F
      (galoisCechEdgeCochain X F Y f c)).app (op ((I).obj Y)))).hom
  have hgen (p : CechEdge (fun a : (I).obj Y ⟶ (I).obj Y => a ≫ f)) :
      q (FreeAbelianGroup.of p) =
        F.obj.map (prod.lift p.first p.second ≫ e.inv).op z :=
    galoisCechEdgeCochain_generator X F Y f c ((I).obj Y) p
  rw [Adjunction.homEquiv_naturality_left]
  change q
      (freeCechTriangleBoundary (fun a : (I).obj Y ⟶ (I).obj Y => a ≫ f)
        (FreeAbelianGroup.of (galoisCechTriangle X Y hT f σ τ))) = _
  rw [freeCechTriangleBoundary, FreeAbelianGroup.lift_apply_of, map_add, map_sub]
  rw [hgen, hgen, hgen]
  change F.obj.map
      (prod.lift ((I).map σ.asIso.hom) ((I).map (σ.asIso.hom ≫ τ.asIso.hom)) ≫ e.inv).op z -
    F.obj.map (prod.lift (𝟙 _) ((I).map (σ.asIso.hom ≫ τ.asIso.hom)) ≫ e.inv).op z +
    F.obj.map (prod.lift (𝟙 _) ((I).map σ.asIso.hom) ≫ e.inv).op z = _
  rw [← (I).map_id Y, inclusion_pair_lift, inclusion_pair_lift, inclusion_pair_lift]
  exact hgeom

end EtaleCohomology
