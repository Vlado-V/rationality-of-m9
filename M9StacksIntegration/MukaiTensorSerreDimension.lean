module

public import M9StacksIntegration.MukaiBundleUniqueness
public import M9StacksIntegration.MukaiHomExact
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom

/-!
# Serre dimension transport for the actual tensor-sequence endpoint

An actual isomorphism to the native sheaf-Hom is passed through native
H0 and the genuine scalar-compatible Serre equivalence. No equality of
cohomology dimensions is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiTensorSectionBound

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]

theorem rightEndpoint_finrank_eq_h1
    (hdim : topologicalKrullDim X ≤ 1) (C R : X.Modules) [C.IsCoherent]
    (e : R ≅ (MukaiHomExact.homFunctor C).obj
      (Stacks.Duality.dualizingSheafOverField f)) :
    Module.finrank k (cohomologyOverField k f R 0) =
      Module.finrank k (cohomologyOverField k f C 1) := by
  letI := modulesLinearOverField k f
  letI := finiteDimensional_cohomologyOverField_of_isProper k f C 1
  let h := MukaiBundleUniqueness.homH0SheafHomLinearEquiv k f C
    (Stacks.Duality.dualizingSheafOverField f)
  let q : cohomologyOverField k f R 0 ≃ₗ[k]
      cohomologyOverField k f ((Stacks.Algebraization.sheafHomFunctor X C).obj
        (Stacks.Duality.dualizingSheafOverField f)) 0 :=
    (cohomologyOverFieldIso k f e 0).toLinearEquiv
  calc
    Module.finrank k (cohomologyOverField k f R 0) =
        Module.finrank k (C ⟶ Stacks.Duality.dualizingSheafOverField f) :=
      q.finrank_eq.trans h.finrank_eq.symm
    _ = Module.finrank k (Module.Dual k (cohomologyOverField k f C 1)) :=
      (Stacks.Duality.homDualizingSheafLinearEquiv f hdim C
        (isQuasicoherent_of_isCoherent C)).finrank_eq
    _ = Module.finrank k (cohomologyOverField k f C 1) := Subspace.dual_finrank_eq

end M9Native.MukaiTensorSectionBound
