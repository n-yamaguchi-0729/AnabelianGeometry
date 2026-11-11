/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Actual Cech primitives with injective sheaf coefficients

A section on a self-pullback defines a cochain on the free abelian
representable Cech complex. The triangle identity and injectivity then
produce an actual section primitive. No Galois comparison is assumed.
-/

@[expose] public section

noncomputable section
universe v u
open CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
  {V W : C} (f : V ⟶ W) [HasPullback f f]
  (I : Sheaf J AddCommGrpCat.{v})

/-- The free abelian cochain obtained by restricting an actual section
along pairs of arrows with equal composite. -/
def cechSectionCochain (z : I.obj.obj (op (pullback f f))) :
    cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free ⟶ I.obj where
  app T := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun p =>
    I.obj.map (pullback.lift p.first p.second p.same).op z)
  naturality {T U} g := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    change (FreeAbelianGroup.lift fun q =>
      I.obj.map (pullback.lift q.first q.second q.same).op z)
        (FreeAbelianGroup.map ((cechEdgeFunctor (yoneda.map f)).map g)
          (FreeAbelianGroup.of p)) =
      I.obj.map g (FreeAbelianGroup.lift (fun q =>
        I.obj.map (pullback.lift q.first q.second q.same).op z)
          (FreeAbelianGroup.of p))
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of]
    have hp : p.first ≫ f = p.second ≫ f := p.same
    have he : pullback.lift (g.unop ≫ p.first) (g.unop ≫ p.second)
        (by rw [Category.assoc, Category.assoc, hp]) =
        g.unop ≫ pullback.lift p.first p.second p.same := by
      apply pullback.hom_ext
      · simp only [pullback.lift_fst, Category.assoc]
      · simp only [pullback.lift_snd, Category.assoc]
    change I.obj.map (pullback.lift (g.unop ≫ p.first) (g.unop ≫ p.second) _).op z =
      I.obj.map g (I.obj.map (pullback.lift p.first p.second p.same).op z)
    rw [he, op_comp, I.obj.map_comp, Quiver.Hom.op_unop]
    rfl

/-- Injective coefficients make every actual degree-one Cech cocycle a
coboundary. The hypothesis is exactly the triangle cocycle identity. -/
theorem exists_injective_cechSection_primitive [Injective I]
    (z : I.obj.obj (op (pullback f f)))
    (hz : ∀ (T : C) (a b c : T ⟶ V)
      (hab : a ≫ f = b ≫ f) (hbc : b ≫ f = c ≫ f),
      I.obj.map (pullback.lift b c hbc).op z -
        I.obj.map (pullback.lift a c (hab.trans hbc)).op z +
        I.obj.map (pullback.lift a b hab).op z = 0) :
    ∃ s : I.obj.obj (op V),
      I.obj.map (pullback.snd f f).op s -
        I.obj.map (pullback.fst f f).op s = z := by
  let A := sheafificationAdjunction J AddCommGrpCat.{v}
  let zl := cechSectionCochain J f I z
  let zs := (A.homEquiv _ I).symm zl
  have hzlin : freeCechTriangleBoundaryNat (yoneda.map f) ≫ zl = 0 := by
    apply NatTrans.ext
    funext T
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro t
    change CechTriangle (fun a : T.unop ⟶ V => a ≫ f) at t
    change (FreeAbelianGroup.lift (fun p : CechEdge (fun a : T.unop ⟶ V => a ≫ f) =>
      I.obj.map (pullback.lift p.first p.second p.same).op z))
      (freeCechTriangleBoundary (fun a : T.unop ⟶ V => a ≫ f)
        (FreeAbelianGroup.of t)) = 0
    rw [freeCechTriangleBoundary, FreeAbelianGroup.lift_apply_of,
      map_add, map_sub, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
    exact hz T.unop t.first t.second t.third t.same₁ t.same₂
  have hzs : (presheafToSheaf J AddCommGrpCat.{v}).map
      (freeCechTriangleBoundaryNat (yoneda.map f)) ≫ zs = 0 := by
    apply (A.homEquiv _ I).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homAddEquiv_zero]
    change freeCechTriangleBoundaryNat (yoneda.map f) ≫
      (A.homEquiv _ I) ((A.homEquiv _ I).symm zl) = 0
    rw [Equiv.apply_symm_apply]
    exact hzlin
  obtain ⟨b, hb⟩ := exists_injective_freeCech_primitive J (yoneda.map f) I zs hzs
  let bl := (A.homEquiv _ I) b
  let s := freeAbelianSheafYonedaHomEquiv J V I b
  have heval (T : C) (a : T ⟶ V) :
      bl.app (op T) (FreeAbelianGroup.of a) = I.obj.map a.op s := by
    have h : (bl.app (op T)).hom
        (FreeAbelianGroup.map (fun k : V ⟶ V => a ≫ k)
          (FreeAbelianGroup.of (𝟙 V))) =
        (I.obj.map a.op).hom ((bl.app (op V)).hom (FreeAbelianGroup.of (𝟙 V))) :=
      ConcreteCategory.congr_hom (C := AddCommGrpCat.{v})
        (bl.naturality a.op) (FreeAbelianGroup.of (𝟙 V))
    rw [FreeAbelianGroup.map_of_apply, Category.comp_id] at h
    change (bl.app (op T)).hom (FreeAbelianGroup.of a) =
      (I.obj.map a.op).hom ((bl.app (op V)).hom (FreeAbelianGroup.of (𝟙 V)))
    exact h
  have hbl : freeCechEdgeBoundaryNat (yoneda.map f) ≫ bl = zl := by
    have h := congrArg (A.homEquiv _ I) hb
    rw [Adjunction.homEquiv_naturality_left] at h
    exact h.trans ((A.homEquiv _ I).apply_symm_apply zl)
  refine ⟨s, ?_⟩
  let p : CechEdge (fun a : pullback f f ⟶ V => a ≫ f) :=
    ⟨pullback.fst f f, pullback.snd f f, pullback.condition⟩
  let bP : FreeAbelianGroup (pullback f f ⟶ V) →+
      I.obj.obj (op (pullback f f)) := (bl.app (op (pullback f f))).hom
  have h := ConcreteCategory.congr_hom (C := AddCommGrpCat.{v})
    (congrArg (fun k => k.app (op (pullback f f))) hbl)
    (FreeAbelianGroup.of p)
  change bP
    (freeCechEdgeBoundary (fun a : pullback f f ⟶ V => a ≫ f)
      (FreeAbelianGroup.of p)) =
    (FreeAbelianGroup.lift (fun q : CechEdge (fun a : pullback f f ⟶ V => a ≫ f) =>
      I.obj.map (pullback.lift q.first q.second q.same).op z)) (FreeAbelianGroup.of p) at h
  rw [freeCechEdgeBoundary, FreeAbelianGroup.lift_apply_of,
    FreeAbelianGroup.lift_apply_of, bP.map_sub] at h
  change (bl.app (op (pullback f f)))
      (FreeAbelianGroup.of (pullback.snd f f)) -
    (bl.app (op (pullback f f)))
      (FreeAbelianGroup.of (pullback.fst f f)) =
    I.obj.map (pullback.lift p.first p.second p.same).op z at h
  rw [heval, heval] at h
  have hp : pullback.lift (pullback.fst f f) (pullback.snd f f)
      pullback.condition = 𝟙 (pullback f f) := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.id_comp]
    · simp only [pullback.lift_snd, Category.id_comp]
  rw [hp, op_id, I.obj.map_id] at h
  exact h

/-- The same injective primitive theorem for a binary self-product.
The triangle condition is tested on arbitrary triples of arrows. -/
theorem exists_injective_productSection_primitive
    [HasTerminal C] [HasPullbacks C] (V : C) [HasBinaryProduct V V]
    (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (z : I.obj.obj (op (V ⨯ V)))
    (hz : ∀ (T : C) (a b c : T ⟶ V),
      I.obj.map (prod.lift b c).op z -
        I.obj.map (prod.lift a c).op z +
        I.obj.map (prod.lift a b).op z = 0) :
    ∃ s : I.obj.obj (op V),
      I.obj.map (prod.snd : V ⨯ V ⟶ V).op s -
        I.obj.map (prod.fst : V ⨯ V ⟶ V).op s = z := by
  let f : V ⟶ ⊤_ C := terminal.from V
  let e : V ⨯ V ≅ pullback f f := prodIsoPullback V V
  let z' := I.obj.map e.inv.op z
  have hlift (T : C) (a b : T ⟶ V) (h : a ≫ f = b ≫ f) :
      pullback.lift a b h ≫ e.inv = prod.lift a b := by
    apply prod.hom_ext
    · rw [Category.assoc, prodIsoPullback_inv_fst, pullback.lift_fst, prod.lift_fst]
    · rw [Category.assoc, prodIsoPullback_inv_snd, pullback.lift_snd, prod.lift_snd]
  have hz' : ∀ (T : C) (a b c : T ⟶ V)
      (hab : a ≫ f = b ≫ f) (hbc : b ≫ f = c ≫ f),
      I.obj.map (pullback.lift b c hbc).op z' -
        I.obj.map (pullback.lift a c (hab.trans hbc)).op z' +
        I.obj.map (pullback.lift a b hab).op z' = 0 := by
    intro T a b c hab hbc
    change I.obj.map (pullback.lift b c hbc).op (I.obj.map e.inv.op z) -
      I.obj.map (pullback.lift a c (hab.trans hbc)).op (I.obj.map e.inv.op z) +
      I.obj.map (pullback.lift a b hab).op (I.obj.map e.inv.op z) = 0
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hlift]
    exact hz T a b c
  obtain ⟨s, hs⟩ := exists_injective_cechSection_primitive J f I z' hz'
  refine ⟨s, ?_⟩
  have h := congrArg (I.obj.map e.hom.op) hs
  change I.obj.map e.hom.op
    (I.obj.map (pullback.snd f f).op s - I.obj.map (pullback.fst f f).op s) =
      I.obj.map e.hom.op (I.obj.map e.inv.op z) at h
  have ef : e.hom ≫ pullback.fst f f = (prod.fst : V ⨯ V ⟶ V) :=
    prodIsoPullback_hom_fst V V
  have es : e.hom ≫ pullback.snd f f = (prod.snd : V ⨯ V ⟶ V) :=
    prodIsoPullback_hom_snd V V
  simp only [map_sub, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, es, ef, Iso.hom_inv_id, op_id] at h
  rw [I.obj.map_id (op (V ⨯ V))] at h
  exact h

/-- Injective Cech primitives commute with a product-preserving inclusion
of the actual covering category into the site. -/
theorem exists_injective_mappedProductSection_primitive
    {D : Type*} [Category D] [HasBinaryProducts D]
    [HasTerminal C] [HasPullbacks C]
    (H : D ⥤ C) [PreservesFiniteLimits H] (Y : D)
    (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (z : I.obj.obj (op (H.obj (Y ⨯ Y))))
    (hz : I.obj.map (H.map (prod.snd : Y ⨯ (Y ⨯ Y) ⟶ Y ⨯ Y)).op z -
      I.obj.map (H.map (prod.lift prod.fst (prod.snd ≫ prod.snd) :
        Y ⨯ (Y ⨯ Y) ⟶ Y ⨯ Y)).op z +
      I.obj.map (H.map (prod.lift prod.fst (prod.snd ≫ prod.fst) :
        Y ⨯ (Y ⨯ Y) ⟶ Y ⨯ Y)).op z = 0) :
    ∃ s : I.obj.obj (op (H.obj Y)),
      I.obj.map (H.map (prod.snd : Y ⨯ Y ⟶ Y)).op s -
        I.obj.map (H.map (prod.fst : Y ⨯ Y ⟶ Y)).op s = z := by
  let e := PreservesLimitPair.iso H Y Y
  let e' := PreservesLimitPair.iso H Y (Y ⨯ Y)
  have ef : e.hom ≫ prod.fst = H.map (prod.fst : Y ⨯ Y ⟶ Y) :=
    prodComparison_fst H Y Y
  have es : e.hom ≫ prod.snd = H.map (prod.snd : Y ⨯ Y ⟶ Y) :=
    prodComparison_snd H Y Y
  let l {T : C} (a b : T ⟶ H.obj Y) : T ⟶ H.obj (Y ⨯ Y) :=
    prod.lift a b ≫ e.inv
  have lf {T : C} (a b : T ⟶ H.obj Y) :
      l a b ≫ H.map prod.fst = a := by
    dsimp only [l]
    rw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
  have ls {T : C} (a b : T ⟶ H.obj Y) :
      l a b ≫ H.map prod.snd = b := by
    dsimp only [l]
    rw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]
  have lext {T : C} {a b : T ⟶ H.obj (Y ⨯ Y)}
      (hf : a ≫ H.map prod.fst = b ≫ H.map prod.fst)
      (hs : a ≫ H.map prod.snd = b ≫ H.map prod.snd) : a = b := by
    apply (cancel_mono e.hom).mp
    apply prod.hom_ext
    · simpa only [Category.assoc, ef] using hf
    · simpa only [Category.assoc, es] using hs
  let z' := I.obj.map e.inv.op z
  have hz' (T : C) (a b c : T ⟶ H.obj Y) :
      I.obj.map (prod.lift b c).op z' -
        I.obj.map (prod.lift a c).op z' +
        I.obj.map (prod.lift a b).op z' = 0 := by
    let m : T ⟶ H.obj (Y ⨯ (Y ⨯ Y)) := prod.lift a (l b c) ≫ e'.inv
    have mf : m ≫ H.map prod.fst = a := by
      dsimp only [m]
      rw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
    have ms : m ≫ H.map prod.snd = l b c := by
      dsimp only [m]
      rw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]
    have m₁₃ : m ≫ H.map (prod.lift prod.fst (prod.snd ≫ prod.snd)) = l a c := by
      apply lext
      · rw [Category.assoc, ← H.map_comp, prod.lift_fst, mf, lf]
      · rw [Category.assoc, ← H.map_comp, prod.lift_snd, H.map_comp,
          ← Category.assoc, ms, ls, ls]
    have m₁₂ : m ≫ H.map (prod.lift prod.fst (prod.snd ≫ prod.fst)) = l a b := by
      apply lext
      · rw [Category.assoc, ← H.map_comp, prod.lift_fst, mf, lf]
      · rw [Category.assoc, ← H.map_comp, prod.lift_snd, H.map_comp,
          ← Category.assoc, ms, lf, ls]
    have h := congrArg (I.obj.map m.op) hz
    simp only [map_add, map_sub, map_zero, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, ms, m₁₃, m₁₂] at h
    change I.obj.map (prod.lift b c).op (I.obj.map e.inv.op z) -
      I.obj.map (prod.lift a c).op (I.obj.map e.inv.op z) +
      I.obj.map (prod.lift a b).op (I.obj.map e.inv.op z) = 0
    simpa only [l, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using h
  obtain ⟨s, hs⟩ := exists_injective_productSection_primitive J (H.obj Y) I z' hz'
  refine ⟨s, ?_⟩
  have h := congrArg (I.obj.map e.hom.op) hs
  change I.obj.map e.hom.op
    (I.obj.map (prod.snd : H.obj Y ⨯ H.obj Y ⟶ H.obj Y).op s -
      I.obj.map (prod.fst : H.obj Y ⨯ H.obj Y ⟶ H.obj Y).op s) =
    I.obj.map e.hom.op (I.obj.map e.inv.op z) at h
  simp only [map_sub, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, ef, es, Iso.hom_inv_id, op_id] at h
  rw [I.obj.map_id (op (H.obj (Y ⨯ Y)))] at h
  exact h

end EtaleCohomology
