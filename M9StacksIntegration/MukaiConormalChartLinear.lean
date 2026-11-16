module

public import M9StacksIntegration.MukaiConormalChartJets
public import M9StacksIntegration.MukaiConormalLinearJets

/-! The actual primitive dual-basis sums are the literal finite Euler
coefficient sums. Surjectivity is derived from the native differential
and its basis computations, rather than supplied as a first-jet premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module

universe u v

namespace M9Native.MukaiConormalChartLinear

open MukaiConormalChartJets MukaiConormalOriginCoordinates

variable (K : Type u) [Field K] [CharZero K]
variable (z : Spec (.of K) ⟶ chart K) (v : Fin 14 → Γ(chart K,⊤))

theorem valueMap_coordinates (w : Fin 14 → K) :
    valueMap K z v ((formsCoordinates K).symm w) =
      MukaiConormalLinearJets.valueMap K (valueVector K z v) w := by
  simp only [valueMap, LinearMap.coe_mk, AddHom.coe_mk, formsCoordinates_symm_basis]
  rfl

theorem derivativeMap_coordinates (w : Fin 14 → K) :
    derivativeMap K z v ((formsCoordinates K).symm w) =
      MukaiConormalLinearJets.derivativeMap K (derivativeVector K z v) w := by
  simp only [derivativeMap, LinearMap.coe_mk, AddHom.coe_mk, formsCoordinates_symm_basis]
  rfl

/-- The actual nonzero pivot makes the original primitive-form value
functional onto; no first-jet surjectivity is assumed. -/
theorem valueMap_surjective (i : Fin 14) (hi : value K z (v i) ≠ 0) :
    Function.Surjective (valueMap K z v) := by
  intro c
  obtain ⟨w,hw⟩ := MukaiConormalLinearJets.valueMap_surjective K (valueVector K z v) i hi c
  exact ⟨(formsCoordinates K).symm w, (valueMap_coordinates K z v w).trans hw⟩

/-- Exact ratio-value and ratio-differential computations, together with
the actual surjective cotangent map, derive actual first-jet surjectivity.
These are map computations, not an image equality supplied as data. -/
theorem firstJetMap_surjective_of_ratio_data
    {A : Type v} [AddCommGroup A] [Module K A]
    (i : Fin 14) (r : Fin 14 → K)
    (b : Basis {j : Fin 14 // j ≠ i} K A)
    (δ : A →ₗ[K] PointCotangent K z) (hδ : Function.Surjective δ)
    (hi : value K z (v i) ≠ 0)
    (hv : ∀ j, value K z (v j) = r j * value K z (v i))
    (hd : ∀ j : {j : Fin 14 // j ≠ i},
      derivative K z (v j.1) - r j.1 • derivative K z (v i) =
        value K z (v i) • δ (b j)) :
    Function.Surjective (firstJetMap K z v) := by
  let e : A →ₗ[K] Module.Dual K (LagrangianField.Primitive K) :=
    (formsCoordinates K).symm.toLinearMap.comp (MukaiConormalLinearJets.eulerMap K r i b)
  have he₁ : (valueMap K z v).comp e = 0 := by
    ext x
    change valueMap K z v ((formsCoordinates K).symm
      (MukaiConormalLinearJets.eulerMap K r i b x)) = 0
    rw [valueMap_coordinates]
    exact congrArg (fun t : A →ₗ[K] K => t x)
      (MukaiConormalLinearJets.valueMap_comp_eulerMap K (valueVector K z v) r i b hv)
  have he₂ : (derivativeMap K z v).comp e = value K z (v i) • δ := by
    ext x
    change derivativeMap K z v ((formsCoordinates K).symm
      (MukaiConormalLinearJets.eulerMap K r i b x)) = _
    rw [derivativeMap_coordinates]
    exact congrArg (fun t : A →ₗ[K] PointCotangent K z => t x)
      (MukaiConormalLinearJets.derivativeMap_comp_eulerMap K (derivativeVector K z v) r i b
        δ (value K z (v i)) hd)
  exact MukaiConormalLinearJets.prod_surjective_of_adjuster K
    (valueMap K z v) (derivativeMap K z v) e δ (value K z (v i)) hi
    (valueMap_surjective K z v i hi) hδ he₁ he₂

theorem finrank_ker_firstJetMap [Module.Finite K (PointCotangent K z)]
    (hT : finrank K (PointCotangent K z) = 6)
    (h : Function.Surjective (firstJetMap K z v)) :
    finrank K (LinearMap.ker (firstJetMap K z v)) = 7 := by
  have hdim : finrank K (Module.Dual K (LagrangianField.Primitive K)) = 14 :=
    (Module.finrank_eq_card_basis ((LagrangianPluckerLinear.primitiveBasis14 K).dualBasis)).trans
      (Fintype.card_fin 14)
  have he := (firstJetMap K z v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr h, finrank_top, Module.finrank_prod, Module.finrank_self, hT] at he
  omega

end M9Native.MukaiConormalChartLinear
