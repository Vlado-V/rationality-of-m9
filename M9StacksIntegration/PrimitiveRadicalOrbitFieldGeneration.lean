module

public import M9StacksIntegration.PrimitiveRadicalOrbitRings
public import Mathlib.FieldTheory.AlgebraicClosure

/-! The original thirteen-plus-thirty-two variables generate the actual source fraction field.
This records both literal localization blocks, without replacing the native source field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace M9Native.PrimitiveRadicalOrbitFieldGeneration

open PrimitiveRadicalOrbitFamily PrimitiveRadicalOrbitRings PrimitiveGaussCoordinates
open M9.GraphBundleDescent

abbrev L := FractionRing coordinateRing

theorem parameterFieldEmbedding_toRational (r : gaussRing) :
    parameterFieldEmbedding (toRational ℂ r) = coordinateFractionMap (gaussInclusion r) := by
  have he : parameterFieldEmbedding.toRingHom.comp (toRational ℂ) =
      coordinateFractionMap.comp gaussInclusion.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (localizer ℂ))
    apply RingHom.ext
    intro p
    change parameterFieldEmbedding
      (toRational ℂ (algebraMap (polynomial ℂ) gaussRing p)) = _
    rw [toRational_algebraMap,parameterFieldEmbedding_coordinate]
    rfl
  exact congrArg (fun f : gaussRing →+* L => f r) he

/-- Actual source-field generation from the original two parameter blocks. -/
theorem all_mem_of_parameters_mem (E : Subfield L)
    (hC : ∀ c : ℂ, algebraMap ℂ L c ∈ E)
    (hGauss : ∀ i : Fin 13,
      coordinateFractionMap (gaussInclusion (gaussLocalization (MvPolynomial.X i))) ∈ E)
    (hGraph : ∀ i : ParameterIndex,
      coordinateFractionMap (graphInclusion (MvPolynomial.X i)) ∈ E) : ∀ x : L, x ∈ E := by
  let ψ : MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ →ₐ[ℂ] L :=
    sourceRationalEquiv.symm.toAlgHom.comp (IsScalarTower.toAlgHom ℂ
      (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ) (FractionRing _))
  have hp (p : MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ) : ψ p ∈ E := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      change ψ (algebraMap ℂ (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ) c) ∈ E
      rw [ψ.commutes]
      exact hC c
    | add p q hp hq =>
      change ψ.toRingHom (p + q) ∈ E
      rw [ψ.map_add]
      exact E.add_mem hp hq
    | mul_X p i hp =>
      change ψ.toRingHom (p * MvPolynomial.X i) ∈ E
      rw [ψ.map_mul]
      apply E.mul_mem hp
      change sourceRationalEquiv.symm
        (algebraMap (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ) (FractionRing _)
          (MvPolynomial.X i)) ∈ E
      cases i with
      | inl i =>
        rw [← sourceRationalEquiv_gauss_X,AlgEquiv.symm_apply_apply]
        exact hGauss i
      | inr i =>
        rw [← sourceRationalEquiv_graph_X,AlgEquiv.symm_apply_apply]
        exact hGraph i
  intro x
  obtain ⟨p,q,_,hx⟩ := IsFractionRing.div_surjective
    (MvPolynomial (Fin 13 ⊕ ParameterIndex) ℂ) (sourceRationalEquiv x)
  have he : x = sourceRationalEquiv.symm
      (algebraMap _ (FractionRing _) p / algebraMap _ (FractionRing _) q) := by
    rw [hx,AlgEquiv.symm_apply_apply]
  rw [he]
  change sourceRationalEquiv.symm.toRingHom
    (algebraMap _ (FractionRing _) p / algebraMap _ (FractionRing _) q) ∈ E
  rw [map_div₀]
  exact E.div_mem (hp p) (hp q)

end M9Native.PrimitiveRadicalOrbitFieldGeneration
