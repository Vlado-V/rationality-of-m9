module

public import M9StacksIntegration.LagrangianPlucker
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LinearAction
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceDimension
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0

/-! The actual closed linear embedding of the primitive projective space
into the projective space with all native quotient-minor coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Module
universe u

namespace M9Native.LagrangianPluckerLinear

abbrev MinorIndex := Fin 3 ↪ Fin 6
variable (K : Type u) [Field K]
abbrev Third := M9Native.LagrangianField.Third K
abbrev Primitive := M9Native.LagrangianField.Primitive K
abbrev FullCoordinates := MinorIndex → K

/-- Each native coordinate is its actual exterior dual functional. -/
def coordinateLinearMap : FullCoordinates K →ₗ[K] Module.Dual K (Third K) :=
  (Pi.basisFun K MinorIndex).constr K (M9Native.LagrangianField.coordinate3 K)

theorem coordinate3_triple (j : Fin 20) :
    M9Native.LagrangianField.coordinate3 K (M9Native.LagrangianRing.triple j)=
      (M9Native.LagrangianField.thirdBasis20 K).coord j := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.pairingDual K (Fin 6 → K) 3
      (exteriorPower.ιMulti K 3 (fun k => LinearMap.proj (M9Native.LagrangianRing.triple j k)))
      (exteriorPower.ιMulti K 3 v)=
    ((Pi.basisFun K (Fin 6)).exteriorPower 3).repr (exteriorPower.ιMulti K 3 v)
      (M9Native.LagrangianRing.tripleEquiv.symm j)
  rw [exteriorPower.pairingDual_ιMulti_ιMulti,exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

theorem coordinateLinearMap_surjective : Function.Surjective (coordinateLinearMap K) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← (M9Native.LagrangianField.thirdBasis20 K).dualBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  refine ⟨Pi.basisFun K MinorIndex (M9Native.LagrangianRing.triple j),?_⟩
  rw [coordinateLinearMap,Basis.constr_basis]
  apply LinearMap.ext
  intro w
  simpa only [Basis.coord_apply,Basis.dualBasis_apply] using
    LinearMap.congr_fun (coordinate3_triple K j) w

/-- The genuine surjective restriction from all native coordinate forms
to the dual of the actual primitive contraction kernel. -/
def primitiveLinearMap : FullCoordinates K →ₗ[K] Module.Dual K (Primitive K) :=
  (M9Native.LagrangianField.Primitive K).subtype.dualMap.comp (coordinateLinearMap K)

theorem primitiveLinearMap_surjective : Function.Surjective (primitiveLinearMap K) := by
  let i : Primitive K →ₗ[K] Third K := (M9Native.LagrangianField.Primitive K).subtype
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext h
  have hs : Function.Surjective i.dualMap :=
    @LinearMap.dualMap_surjective_of_injective K (Primitive K) (Third K)
      inferInstance inferInstance inferInstance inferInstance inferInstance i hi
  exact hs.comp (coordinateLinearMap_surjective K)

abbrev primitiveGradedHom := SymPow.gradedSymAlgMap (primitiveLinearMap K)

theorem primitiveGradedHom_surjective : Function.Surjective (primitiveGradedHom K) :=
  SymPow.symAlgMap_surjective (primitiveLinearMap K) (primitiveLinearMap_surjective K)

/-- The actual projective morphism induced by the actual surjection on
coordinate forms. -/
def linearEmbedding : projectiveSpaceOfModule K (Module.Dual K (Primitive K)) ⟶
    projectiveSpaceOfModule K (FullCoordinates K) :=
  Proj.map (primitiveGradedHom K)
    (Proj.irrelevant_le_map_of_surjective _ (primitiveGradedHom_surjective K))

instance linearEmbedding_isClosedImmersion : IsClosedImmersion (linearEmbedding K) :=
  Proj.isClosedImmersion_map_of_surjective' _ (primitiveGradedHom_surjective K)

variable [CharZero K]

def primitiveBasis14 : Basis (Fin 14) K (Primitive K) :=
  (M9Native.LagrangianField.coordinateBasis14 K).map (M9Native.LagrangianField.primitiveEquiv K)

def primitiveProjectiveIso : projectiveSpaceOver 13 (Spec (.of K)) ≅
    projectiveSpaceOfModule K (Module.Dual K (Primitive K)) :=
  basisProjectiveSpaceIso (primitiveBasis14 K).dualBasis

/-- The global LG Plucker morphism now lands in the projective space of
its actual primitive exterior submodule, via the proved basis isomorphism. -/
def primitivePlucker : M9Native.LagrangianGrassmannian.space K ⟶
    projectiveSpaceOfModule K (Module.Dual K (Primitive K)) :=
  M9Native.LagrangianPlucker.primitivePlucker K ≫ (primitiveProjectiveIso K).hom

end M9Native.LagrangianPluckerLinear
