module

public import M9StacksIntegration.CurveDerivativeNormal
public import M9StacksIntegration.MukaiCohomologyParity

/-!
# Original cohomology maps of the actual curve derivative

All arrows are the original native maps of the genuine normal short
exact sequence. The boundary is selected from its proved native long
exact sequence. Original normal H1 vanishing proves surjectivity of the
original derivative on H1. Exactness then computes the cohomological
rank identity needed for a future actual morphism-deformation comparison.
No tangent classifier, source cohomology dimensions, map rank, or
surjectivity premise is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open M9Native.CurveTangentLineGeometry M9Native.CurveDerivativeNormal

universe u

namespace M9Native.CurveDerivativeCohomology

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
variable (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
variable [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY]
variable [Smooth pX] [Smooth pY]
variable (g : X ⟶ Y) (hg : g ≫ pY = pX)
variable (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)

include hnc

/-- The original actual derivative is injective on original H0. -/
theorem tangent_h0_map_injective :
    Function.Injective (cohomologyOverFieldMap k pX (tangentMap pX pY g hg) 0).hom :=
  MukaiCohomologyParity.cohomologyBoundary_injective_left k pX
    (normal_shortExact pX pY g hg hnc)

/-- The actual normal boundary, from the genuine original long exact sequence. -/
abbrev normalBoundary :
    cohomologyOverField k pX (normalSheaf pX pY g hg) 0 ⟶
      cohomologyOverField k pX (tangentLine pX) 1 :=
  MukaiCohomologyParity.cohomologyBoundary k pX (normal_shortExact pX pY g hg hnc) 0

/-- Exactness before the original normal boundary. -/
theorem normalBoundary_exact_before :
    Function.Exact (cohomologyOverFieldMap k pX
      (cokernel.π (tangentMap pX pY g hg)) 0).hom
        (normalBoundary pX pY g hg hnc).hom :=
  MukaiCohomologyParity.cohomologyBoundary_exact_middle k pX
    (normal_shortExact pX pY g hg hnc) 0

/-- Exactness after the original normal boundary. -/
theorem normalBoundary_exact_after :
    Function.Exact (normalBoundary pX pY g hg hnc).hom
      (cohomologyOverFieldMap k pX (tangentMap pX pY g hg) 1).hom :=
  MukaiCohomologyParity.cohomologyBoundary_exact_right k pX
    (normal_shortExact pX pY g hg hnc) 0

/-- Vanishing of the actual normal H1 derives surjectivity of the
original derivative map on actual H1. -/
theorem tangent_h1_map_surjective :
    Function.Surjective (cohomologyOverFieldMap k pX (tangentMap pX pY g hg) 1).hom := by
  let := normal_isCoherent pX pY g hg
  let := ModuleCat.subsingleton_of_isZero
    (normal_positive_cohomology_isZero pX pY g hg hnc 1 (by omega))
  have he := MukaiCohomologyParity.cohomologyBoundary_exact_left k pX
    (normal_shortExact pX pY g hg hnc) 1
  intro a
  exact (he a).mp (Subsingleton.elim _ _)

/-- Actual cohomological rank identity, without a supplied dimension or rank value. -/
theorem normal_cohomological_finrank_identity :
    Module.finrank k (cohomologyOverField k pX (normalSheaf pX pY g hg) 0) +
      Module.finrank k (cohomologyOverField k pX (tangentLine pX) 0) +
      Module.finrank k (cohomologyOverField k pX (pulledTangentLine pY g) 1) =
    Module.finrank k (cohomologyOverField k pX (pulledTangentLine pY g) 0) +
      Module.finrank k (cohomologyOverField k pX (tangentLine pX) 1) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  let := tangent_isInvertible pX
  let := pulledTangent_isInvertible pY g
  let : (tangentLine pX).IsCoherent := isCoherent_of_isInvertible' _
  let : (pulledTangentLine pY g).IsCoherent := isCoherent_of_isInvertible' _
  let := normal_isCoherent pX pY g hg
  let := finiteDimensional_cohomologyOverField_of_isProper k pX (tangentLine pX) 0
  let := finiteDimensional_cohomologyOverField_of_isProper k pX (tangentLine pX) 1
  let := finiteDimensional_cohomologyOverField_of_isProper k pX (pulledTangentLine pY g) 0
  let := finiteDimensional_cohomologyOverField_of_isProper k pX (pulledTangentLine pY g) 1
  let := finiteDimensional_cohomologyOverField_of_isProper k pX (normalSheaf pX pY g hg) 0
  have hd := MukaiParityLinear.finrank_add_range_eq
    (cohomologyOverFieldMap k pX (tangentMap pX pY g hg) 0).hom
    (cohomologyOverFieldMap k pX (cokernel.π (tangentMap pX pY g hg)) 0).hom
    (normalBoundary pX pY g hg hnc).hom
    (tangent_h0_map_injective pX pY g hg hnc)
    (MukaiCohomologyParity.cohomologyBoundary_exact_left k pX
      (normal_shortExact pX pY g hg hnc) 0)
    (normalBoundary_exact_before pX pY g hg hnc)
  have he := (cohomologyOverFieldMap k pX (tangentMap pX pY g hg) 1).hom.finrank_range_add_finrank_ker
  rw [(normalBoundary_exact_after pX pY g hg hnc).linearMap_ker_eq,
    LinearMap.range_eq_top.mpr (tangent_h1_map_surjective pX pY g hg hnc),
    finrank_top] at he
  dsimp only [normalSheaf]
  omega

end M9Native.CurveDerivativeCohomology
