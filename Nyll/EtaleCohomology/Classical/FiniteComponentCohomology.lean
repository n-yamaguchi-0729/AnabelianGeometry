/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.FiniteLevelScalarApproximation
public import Nyll.EtaleCohomology.Classical.IrreducibleComponentCohomology
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# The original finite coefficient groups on the actual components

The proved component decomposition, with the original inverse-image
constant-sheaf comparison, gives an equivalence between the original
finite-level cohomology group and the original groups on the actual
component schemes. It preserves the original reduction maps.

The same equivalence is linear for the original adic scalar action:
at each finite level that action is the proved integer approximation,
so additivity already supplies the required scalar identity.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

/-- Actual etale restriction preserves the original constant
abelian sheaves through the same original inverse-image adjunction. -/
def etaleAbelianRestrictionConstantIso {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
        etaleRestriction f AddCommGrpCat.{u} ≅
      constantSheaf U.smallEtaleTopology AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (etaleAbelianPullbackRestrictionIso f).symm ≪≫
    etaleAbelianPullbackConstantIso f

/-- The original constant-sheaf comparison induces the same additive
cohomology equivalence for an abstract object of the small etale site. -/
def etaleRestrictionConstantCohomologyEquiv
    {X : Scheme.{u}} (V : X.Etale) (A : AddCommGrpCat.{u}) (i : ℕ) :
    Sheaf.H.{u}
      ((etaleRestriction V.hom AddCommGrpCat.{u}).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A)) i ≃+
      Sheaf.H.{u}
        ((constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).obj A) i :=
  ((Sheaf.functorH V.left.smallEtaleTopology i).mapIso
    ((etaleAbelianRestrictionConstantIso V.hom).app A)).addCommGroupIsoToAddEquiv

/-- An isomorphism of the original coefficient functors gives the
same naturality square on their native sheaf cohomology. -/
private theorem sheafCohomologyIso_naturality
    {Y : Scheme.{u}}
    {P Q : AddCommGrpCat.{u} ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
    (e : P ≅ Q) {A B : AddCommGrpCat.{u}} (φ : A ⟶ B) (i : ℕ)
    (a : Sheaf.H.{u} (P.obj A) i) :
    Sheaf.H.map (e.app B).hom i (Sheaf.H.map (P.map φ) i a) =
      Sheaf.H.map (Q.map φ) i (Sheaf.H.map (e.app A).hom i a) := by
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun η => Sheaf.H.map η i a) (e.hom.naturality φ)

variable (X : Scheme.{u}) [IsNoetherian X]
  (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))

local notation "U" => reducedIrreducibleComponentEtale X hdom

/-- Constant-coefficient cohomology decomposes into the original
constant-coefficient groups on the actual component schemes. -/
def reducedComponentsConstantCohomologyEquiv (A : AddCommGrpCat.{u}) (i : ℕ) :
    Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) i ≃+
      ∀ Z : irreducibleComponents X,
        Sheaf.H.{u} ((constantSheaf (U Z).left.smallEtaleTopology AddCommGrpCat.{u}).obj A) i :=
  (reducedIrreducibleComponentsCohomologyEquiv X hdom
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) i).trans
      (AddEquiv.piCongrRight fun Z =>
        etaleRestrictionConstantCohomologyEquiv (U Z) A i)

/-- The constant-coefficient decomposition retains every original
coefficient map, after the actual component constant-sheaf identifications. -/
theorem reducedComponentsConstantCohomologyEquiv_naturality
    {A B : AddCommGrpCat.{u}} (φ : A ⟶ B) (i : ℕ)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) i)
    (Z : irreducibleComponents X) :
    reducedComponentsConstantCohomologyEquiv X hdom B i
        (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map φ) i a) Z =
      Sheaf.H.map ((constantSheaf (U Z).left.smallEtaleTopology AddCommGrpCat.{u}).map φ) i
        (reducedComponentsConstantCohomologyEquiv X hdom A i a Z) := by
  exact (congrArg
    (Sheaf.H.map ((etaleAbelianRestrictionConstantIso (U Z).hom).app B).hom i)
    (reducedIrreducibleComponentsCohomologyEquiv_naturality X hdom
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map φ) i a Z)).trans
        (sheafCohomologyIso_naturality (Y := (U Z).left)
          (etaleAbelianRestrictionConstantIso (U Z).hom) φ i
          (reducedIrreducibleComponentsCohomologyEquiv X hdom
            ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) i a Z))

/-- The original finite coefficient cohomology is the actual finite
family of the same original groups on the component schemes. -/
def finiteLevelComponentCohomologyEquiv (ℓ n i : ℕ) :
    finiteLevelCohomology X ℓ n i ≃+
      ∀ Z : irreducibleComponents X, finiteLevelCohomology (U Z).left ℓ n i :=
  reducedComponentsConstantCohomologyEquiv X hdom (ellPowerCoefficients ℓ n) i

/-- Each original finite reduction becomes the original reduction
on the same actual component. -/
theorem finiteLevelComponentCohomologyEquiv_reduction (ℓ n i : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) i) (Z : irreducibleComponents X) :
    finiteLevelComponentCohomologyEquiv X hdom ℓ n i (finiteLevelReduction X ℓ n i a) Z =
      finiteLevelReduction (U Z).left ℓ n i
        (finiteLevelComponentCohomologyEquiv X hdom ℓ (n + 1) i a Z) :=
  reducedComponentsConstantCohomologyEquiv_naturality X hdom
    (AddCommGrpCat.ofHom (ellPowerReduction ℓ n)) i a Z

/-- The actual finite component comparison respects the original
adic scalar action, proved from its integer approximation. -/
theorem finiteLevelComponentCohomologyEquiv_smul
    (ℓ : ℕ) [Fact ℓ.Prime] (n i : ℕ) (r : ℤ_[ℓ])
    (a : finiteLevelCohomology X ℓ n i) (Z : irreducibleComponents X) :
    finiteLevelComponentCohomologyEquiv X hdom ℓ n i (r • a) Z =
      r • finiteLevelComponentCohomologyEquiv X hdom ℓ n i a Z := by
  rw [finiteLevelCohomology_smul_eq_appr, finiteLevelCohomology_smul_eq_appr]
  exact congrFun (map_nsmul (finiteLevelComponentCohomologyEquiv X hdom ℓ n i)
    (r.appr (n + 1)) a) Z

/-- The original finite-level component decomposition, with its
original adic linear structures on both sides. -/
def finiteLevelComponentCohomologyLinearEquiv (ℓ : ℕ) [Fact ℓ.Prime] (n i : ℕ) :
    finiteLevelCohomology X ℓ n i ≃ₗ[ℤ_[ℓ]]
      ∀ Z : irreducibleComponents X, finiteLevelCohomology (U Z).left ℓ n i where
  toAddEquiv := finiteLevelComponentCohomologyEquiv X hdom ℓ n i
  map_smul' r a := funext fun Z => finiteLevelComponentCohomologyEquiv_smul X hdom ℓ n i r a Z

end EtaleCohomology
