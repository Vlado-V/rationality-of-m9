module

public import M9StacksIntegration.FieldSectionsKernel
public import M9StacksIntegration.LinearSeriesFromCohomology

/-!
# No actual degree-eight net bounds an actual cohomology kernel

If the actual kernel of a sheaf map on `Spec k` computes the actual H0
of an actual degree-eight invertible sheaf on the original curve,
absence of a native degree-eight net bounds the actual linear kernel
by two. Both the curve and all section spaces stay over the stated
base field. No assertion about extension-field linear series is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.NoNetKernelBound

theorem linearKernel_finrank_le_two_of_no_degree_eight_net
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hno : ¬ Nonempty (LinearSeries k f hdim 8 2))
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : invertibleCurveDegree k f hdim L = 8)
    {M N : (Spec (.of k)).Modules} (v : M ⟶ N)
    (e : cohomologyOverField k f L 0 ≅ moduleSpecΓFunctor.obj (kernel v)) :
    Module.finrank k (LinearMap.ker (moduleSpecΓFunctor.map v).hom) ≤ 2 := by
  rw [FieldSectionsKernel.finrank_linearKernel_eq_of_iso k v _ e]
  exact LinearSeriesFromCohomology.finrank_H0_le_two_of_no_degree_eight_net
    k f hdim hno L hdeg

end M9Native.NoNetKernelBound
