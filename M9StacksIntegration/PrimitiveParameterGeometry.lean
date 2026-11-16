module

public import M9StacksIntegration.PrimitiveUniversalFieldAction
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-! Elementary consequences of the actual parameter-domain property.
These are consequences of the genuine tensor-domain provider, not a new
instance or substitute for that outstanding geometric theorem.
-/

noncomputable section

open scoped TensorProduct

namespace M9Native.PrimitiveParameterGeometry

open PrimitiveUniversalFieldAction

/-- Faithful scalar extension embeds the original group algebra into the
actual tensor parameter algebra. -/
theorem group_includeLeft_injective :
    Function.Injective (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing) :=
  Algebra.TensorProduct.includeLeft_injective (algebraMap ℂ E).injective

/-- Once the actual parameter algebra is proved to be a domain, the original
group algebra is a domain as an actual subring. This is deliberately not a
global instance, to avoid a cycle with the independent group-geometry proof. -/
theorem group_isDomain_of_parameter_domain [IsDomain TensorRing] : IsDomain A :=
  Function.Injective.isDomain
    (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing).toRingHom
    group_includeLeft_injective

theorem group_isReduced_of_parameter_domain [IsDomain TensorRing] : IsReduced A := by
  let : IsDomain A := group_isDomain_of_parameter_domain
  infer_instance

end M9Native.PrimitiveParameterGeometry
