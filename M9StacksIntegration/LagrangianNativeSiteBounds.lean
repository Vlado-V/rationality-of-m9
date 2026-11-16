module

public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-! Actual site bounds for the original universal LG family.
Containment of its parameter open and total scheme follows from the
original structural maps. A bounded base change retains its original
scheme and belongs to the same site. No arbitrary field containment is
asserted or supplied. -/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.LagrangianNativeSiteBounds
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth

universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})

/-- The actual original good parameter open belongs to any site
containing the original field spectrum. -/
theorem contains_goodOpen (hK : B.Contains (Spec (.of K))) :
    B.Contains (goodOpen K).toScheme := by
  letI : IsProper (parameterProjection K) := isProper_of_isProjectiveMorphism _
    (Grassmannian.isProjectiveMorphism_schemeOver 9 14 (Spec (.of K)))
  have hP : B.Contains (parameter K) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (parameterProjection K) hK
  exact Scheme.size_lt_of_isOpenImmersion (goodOpen K).ι hP

/-- Properness and smoothness bound the same original universal total
scheme; its containment is derived rather than an additional input. -/
theorem contains_total (hK : B.Contains (Spec (.of K))) : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (restrictedProjection K)
    (contains_goodOpen K B hK)

/-- The literal original pullback over every already bounded test scheme
is bounded. There is no membership requirement on unbounded tests. -/
theorem contains_pullback {T : Scheme.{u}} (hT : B.Contains T)
    (p : T ⟶ (goodOpen K).toScheme) :
    B.Contains (pullback (restrictedProjection K) p) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (pullback.snd (restrictedProjection K) p) hT

end M9Native.LagrangianNativeSiteBounds
