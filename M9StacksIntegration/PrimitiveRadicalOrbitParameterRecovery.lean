module

public import M9StacksIntegration.PrimitiveRadicalOrbitPoints
public import M9StacksIntegration.PrimitiveRadicalOrbitFieldGeneration
public import M9StacksIntegration.PrimitiveRhoGraphRecovery
public import M9StacksIntegration.PrimitiveGaussFieldExtension

/-! Actual recovery of both original parameter blocks from a normalized translated quotient. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

namespace M9Native.PrimitiveRadicalOrbitParameterRecovery

open PrimitiveRadicalOrbitFamily PrimitiveRadicalOrbitRings PrimitiveRadicalOrbitPoints
open PrimitiveRhoFiberChart PrimitiveRhoFiberNondegenerate MatrixChartFieldRecovery
open M9.GraphBundleDescent

variable (K : Type) [Field K] [Algebra ℂ K]

theorem primitiveAt_map (y : Point K) :
    primitiveAt K y =
      (PrimitiveRingCoordinates.primitiveMatrix gaussRing (algebraMap ℂ gaussRing)
        (PrimitiveGaussFamily.family ℂ)).map (leftPoint K y).toRingHom := by
  have hf : (leftPoint K y).toRingHom.comp (algebraMap ℂ gaussRing) = algebraMap ℂ K := by
    apply RingHom.ext
    intro c
    exact (leftPoint K y).commutes c
  have h := PrimitiveRingCoordinates.primitiveMatrix_map gaussRing (algebraMap ℂ gaussRing)
    (leftPoint K y).toRingHom (PrimitiveGaussFamily.family ℂ)
  rw [hf] at h
  exact h

theorem primitiveAt_entriesIn (E : Subfield K) (y : Point K)
    (hGauss : ∀ r : gaussRing, leftPoint K y r ∈ E) : EntriesIn E (primitiveAt K y) := by
  rw [primitiveAt_map]
  exact fun i j => hGauss _

def graphPoint (y : Point K) : parameterRing →ₐ[ℂ] K :=
  (rightPoint K y).comp localizationMap

theorem graphAt_eq (y : Point K) : graphAt K y =
    graphMatrix K
      ((universalBaseLocalized (K := ℂ) 0).map (graphPoint K y))
      ((universalBaseLocalized (K := ℂ) 1).map (graphPoint K y))
      (Matrix.GeneralLinearGroup.map (graphPoint K y).toRingHom (universalIsomorphism (K := ℂ))) := by
  change (parameterGraph.map localizationMap).map (rightPoint K y) = _
  rw [Matrix.map_map]
  exact graphMatrix_map (graphPoint K y).toRingHom _ _ _

theorem graph_parameters_mem (E : Subfield K) (y : Point K)
    (hP : EntriesIn E (graphAt K y)) :
    ∀ i : ParameterIndex, y (graphInclusion (MvPolynomial.X i)) ∈ E := by
  rw [graphAt_eq] at hP
  have hA := PrimitiveRhoGraphRecovery.entriesIn_base_left K E _ _ _ hP
  have hB := PrimitiveRhoGraphRecovery.entriesIn_base_right K E _ _ _ hP
  have hX := PrimitiveRhoGraphRecovery.entriesIn_fiber K E _ _ _ hP
  intro i
  rcases i with ⟨s,i,j⟩ | ⟨i,j⟩
  · fin_cases s
    · exact hA i j
    · exact hB i j
  · exact hX i j

abbrev sourceField := FractionRing coordinateRing

def genericPoint : Point sourceField := IsScalarTower.toAlgHom ℂ coordinateRing sourceField

theorem all_mem_of_gauss_graph (E : Subfield sourceField)
    (hC : ∀ c : ℂ, algebraMap ℂ sourceField c ∈ E)
    (hGauss : ∀ r : gaussRing, leftPoint sourceField genericPoint r ∈ E)
    (hP : EntriesIn E (graphAt sourceField genericPoint)) : ∀ x : sourceField, x ∈ E := by
  apply PrimitiveRadicalOrbitFieldGeneration.all_mem_of_parameters_mem E hC
  · intro i
    exact hGauss (gaussLocalization (MvPolynomial.X i))
  · exact graph_parameters_mem sourceField E genericPoint hP

end M9Native.PrimitiveRadicalOrbitParameterRecovery
