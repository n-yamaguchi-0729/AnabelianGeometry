/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ConnectedConstants
public import Nyll.EtaleCohomology.Sites.ModuleConstant
public import Nyll.EtaleCohomology.Sites.ModuleSetComparison
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Yoneda

/-!
# Arbitrary étale sheaves over a separably closed field are constant

The identity geometric point has its fibre functor corepresented by the
identity étale object. Its geometric stalk is therefore the actual module
or set of global sections. This single point is conservative. Since the
constant-sheaf adjunction unit is invertible on a connected scheme, the
triangle identity and this conservativity make its counit invertible.

The resulting constant models use the original global sections. Neither
the set nor the coefficient module is assumed finite or constructible.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The actual constant-sheaf counit identifies every set-valued étale
sheaf over a separably closed field with its constant global-sections model. -/
def etaleSetSheafConstantIso_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (Type u)) :
    (constantSheaf (Spec (CommRingCat.of k)).smallEtaleTopology (Type u)).obj
      (F.obj.obj (op (etaleBaseObject (Spec (CommRingCat.of k))))) ≅ F := by
  let S : Scheme.{u} := Spec (CommRingCat.of k)
  let T : S.Etale := etaleBaseObject S
  let Φ := Scheme.pointSmallEtale (𝟙 S)
  let ff := Functor.FullyFaithful.ofFullyFaithful (Scheme.Etale.forget S)
  let E : Φ.fiber.CorepresentableBy T :=
    { homEquiv := ff.homEquiv
      homEquiv_comp := fun g f => (Scheme.Etale.forget S).map_comp f g }
  let t₀ : Φ.fiber.obj T := E.homEquiv (𝟙 T)
  have hInitial : IsInitial (Φ.fiber.elementsMk T t₀) :=
    Functor.Elements.isInitialOfCorepresentableBy E
  have hGerm (G : Sheaf S.smallEtaleTopology (Type u)) :
      IsIso (Φ.toPresheafFiber T t₀ G.obj) :=
    (colimit.isColimit ((Functor.Elements.π Φ.fiber).op ⋙ G.obj)).isIso_ι_app_of_isTerminal
      _ hInitial.op
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) S
  let adj := constantSheafAdj S.smallEtaleTopology (Type u) hT
  let cff := etaleConstantSheafFullyFaithful S
  have : (constantSheaf S.smallEtaleTopology (Type u)).Full := cff.full
  have : (constantSheaf S.smallEtaleTopology (Type u)).Faithful := cff.faithful
  let ε : (constantSheaf S.smallEtaleTopology (Type u)).obj (F.obj.obj (op T)) ⟶ F :=
    adj.counit.app F
  have hGlobal : IsIso (ε.hom.app (op T)) := by
    have htriangle : adj.unit.app (F.obj.obj (op T)) ≫ ε.hom.app (op T) =
        𝟙 (F.obj.obj (op T)) := adj.right_triangle_components F
    exact isIso_of_hom_comp_eq_id (adj.unit.app (F.obj.obj (op T))) htriangle
  let C := (constantSheaf S.smallEtaleTopology (Type u)).obj (F.obj.obj (op T))
  let γC : C.obj.obj (op T) ⟶ Φ.presheafFiber.obj C.obj :=
    Φ.toPresheafFiber T t₀ C.obj
  let γF : F.obj.obj (op T) ⟶ Φ.presheafFiber.obj F.obj :=
    Φ.toPresheafFiber T t₀ F.obj
  have : IsIso γC := hGerm C
  have : IsIso γF := hGerm F
  have hn : γC ≫ Φ.presheafFiber.map ε.hom = ε.hom.app (op T) ≫ γF :=
    Φ.toPresheafFiber_naturality ε.hom T t₀
  have : IsIso (γC ≫ Φ.presheafFiber.map ε.hom) := by
    rw [hn]
    infer_instance
  have hStalk : IsIso (Φ.sheafFiber.map ε) := by
    change IsIso (Φ.presheafFiber.map ε.hom)
    exact IsIso.of_isIso_comp_left γC _
  let s : ∀ _ : PUnit.{u + 1}, Spec (CommRingCat.of k) ⟶ S := fun _ => 𝟙 S
  have hcover : ⋃ i : PUnit.{u + 1}, Set.range (s i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨PUnit.unit, x, rfl⟩
  have hpoints := Scheme.isConservative_pointSmallEtale s hcover
  have : IsIso ε := by
    apply ((hpoints.jointlyReflectIsomorphisms (Type u)).isIso_iff ε).mpr
    rintro ⟨_, ⟨i⟩⟩
    exact hStalk
  exact asIso ε

/-- Every étale module sheaf over a separably closed field is the constant
sheaf of its actual global sections, through the original constant counit. -/
def etaleModuleSheafConstantIso_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)) :
    (constantSheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (F.obj.obj (op (etaleBaseObject (Spec (CommRingCat.of k))))) ≅ F := by
  let S : Scheme.{u} := Spec (CommRingCat.of k)
  let cff := etaleConstantSheafFullyFaithful S
  have : (constantSheaf S.smallEtaleTopology (Type u)).Full := cff.full
  have : (constantSheaf S.smallEtaleTopology (Type u)).Faithful := cff.faithful
  have : Sheaf.IsConstant S.smallEtaleTopology ((etaleModuleUnderlying S Λ).obj F) :=
    Sheaf.isConstant_of_iso S.smallEtaleTopology
      (etaleSetSheafConstantIso_of_isSepClosed k ((etaleModuleUnderlying S Λ).obj F)).symm
  exact etaleModuleConstantIso S Λ F (MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) S)

end EtaleCohomology
