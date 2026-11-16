module

public import M9StacksIntegration.GenusNineCoarse
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase

/-!
# The independently universal smooth-curve coarse space over a field

The source is the native change of base of the actual smooth genus-`g` curve
stack: its objects are the strict pullback of actual curve families and actual
test schemes over `Spec K`. Separatedness and quasi-DM-ness are proved under
change of base, finite inertia is derived, and Keel--Mori then constructs the
coarse algebraic space directly over `K`.

This is distinct from merely restricting the integer-base coarse presheaf to
the field base. No comparison with that earlier restricted presheaf, no
integrality, and no comparison between different bounded big sites is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry

namespace M9StacksIntegration.GenusNineCoarseOverField

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The actual smooth genus-`g` curve stack on test schemes over `Spec K`. -/
def smoothStack (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.{u, u + 1} B (Spec (.of K)) hK :=
  Stack.changeOfBase B (Spec (.of K)) integerBase hK hZ
    (integerSiteObject B hZ hK).hom (GenusNineCoarse.smoothStack B hZ g hg)

theorem smoothStack_separated (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsSeparatedOver B (Spec (.of K)) hK (smoothStack B hZ K hK g hg) :=
  Stack.AlgebraicStacks.isSeparatedOver_changeOfBase B (Spec (.of K)) integerBase hK hZ
    (integerSiteObject B hZ hK).hom (GenusNineCoarse.smoothStack B hZ g hg)
    (GenusNineCoarse.smoothStack_separated B hZ g hg)

theorem smoothStack_quasiDM (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsQuasiDMOver B (Spec (.of K)) hK (smoothStack B hZ K hK g hg) :=
  Stack.AlgebraicStacks.isQuasiDMOver_changeOfBase B (Spec (.of K)) integerBase hK hZ
    (integerSiteObject B hZ hK).hom (GenusNineCoarse.smoothStack B hZ g hg)
    (GenusNineCoarse.smoothStack_quasiDM B hZ g hg)

/-- Finite inertia of the actual field-base smooth curve stack is a conclusion. -/
theorem smoothStack_finite_inertia (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsFinite B (Spec (.of K)) hK
      (Stack.inertiaProjectionAlgebraicStacks B (Spec (.of K)) hK
        (smoothStack B hZ K hK g hg)) :=
  GenusNineCoarse.finite_inertia_of_separated_quasiDM B (Spec (.of K)) hK
    (smoothStack B hZ K hK g hg) (smoothStack_separated B hZ K hK g hg)
    (smoothStack_quasiDM B hZ K hK g hg)

/-- An independently universal coarse algebraic space of the actual smooth
curve stack over `K`, constructed directly by the proved Keel--Mori theorem. -/
theorem exists_coarseSpace (g : ℕ) (hg : 2 ≤ g) :
    ∃ (M : AlgebraicSpaces B (Spec (.of K)) hK)
      (f : smoothStack B hZ K hK g hg ⟶ Stack.algebraicSpaceStack.{u, u + 1}
        B (Spec (.of K)) hK M.obj M.property),
      Stack.IsUniformCategoricalModuliSpace B (Spec (.of K)) hK M f.hom ∧
        Stack.AlgebraicStacks.IsSeparated B (Spec (.of K)) hK f ∧
        Stack.IsQuasiCompactMorphism B (Spec (.of K)) hK f ∧
        Stack.UniversalHomeomorphism B (Spec (.of K)) hK f :=
  Stack.exists_isUniformCategoricalModuliSpace_of_isFinite_inertia B (Spec (.of K)) hK
    (smoothStack B hZ K hK g hg) (smoothStack_finite_inertia B hZ K hK g hg)

def coarseSpace (g : ℕ) (hg : 2 ≤ g) : AlgebraicSpaces B (Spec (.of K)) hK :=
  (exists_coarseSpace B hZ K hK g hg).choose

def coarseMap (g : ℕ) (hg : 2 ≤ g) :
    smoothStack B hZ K hK g hg ⟶ Stack.algebraicSpaceStack.{u, u + 1}
      B (Spec (.of K)) hK (coarseSpace B hZ K hK g hg).obj
      (coarseSpace B hZ K hK g hg).property :=
  (exists_coarseSpace B hZ K hK g hg).choose_spec.choose

theorem coarseMap_uniform (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsUniformCategoricalModuliSpace B (Spec (.of K)) hK
      (coarseSpace B hZ K hK g hg) (coarseMap B hZ K hK g hg).hom :=
  (exists_coarseSpace B hZ K hK g hg).choose_spec.choose_spec.1

theorem coarseMap_universalHomeomorphism (g : ℕ) (hg : 2 ≤ g) :
    Stack.UniversalHomeomorphism B (Spec (.of K)) hK (coarseMap B hZ K hK g hg) :=
  (exists_coarseSpace B hZ K hK g hg).choose_spec.choose_spec.2.2.2

/-- The independently universal smooth genus-nine coarse algebraic space over
the actual field base. -/
abbrev genusNineCoarseSpace := coarseSpace B hZ K hK 9 (by decide)

end M9StacksIntegration.GenusNineCoarseOverField
