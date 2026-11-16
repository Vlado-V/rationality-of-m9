module

public import M9StacksIntegration.MukaiConormalFieldCoordinates
public import M9StacksIntegration.LagrangianPolynomialDifferentials

/-! Literal values and universal differentials of an actual section tuple
on the genuine affine-six chart. The field cotangent is the original
native pulled sheaf, with its original Spec-section scalar structure. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module
open scoped BigOperators

universe u

namespace M9Native.MukaiConormalChartJets

variable (K : Type u) [Field K]

abbrev chart := LagrangianChartCotangent.chart K
abbrev chartProjection := LagrangianChartCotangent.chartProjection K
abbrev chartCotangent := Scheme.Hom.relativeDifferentials (chartProjection K)

abbrev PointCotangent (z : Spec (.of K) ⟶ chart K) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pullback z).obj (chartCotangent K))

def value (z : Spec (.of K) ⟶ chart K) : Γ(chart K,⊤) →+* K :=
  (Scheme.ΓSpecIso (.of K)).hom.hom.comp z.appTop.hom

def derivative (z : Spec (.of K) ⟶ chart K) (s : Γ(chart K,⊤)) : PointCotangent K z :=
  pullbackGlobalSections z (chartCotangent K)
    ((Scheme.Hom.universalRelativeDerivation (chartProjection K)).d s)

def valueVector (z : Spec (.of K) ⟶ chart K) (v : Fin 14 → Γ(chart K,⊤)) : Fin 14 → K :=
  fun j => value K z (v j)

def derivativeVector (z : Spec (.of K) ⟶ chart K) (v : Fin 14 → Γ(chart K,⊤)) :
    Fin 14 → PointCotangent K z := fun j => derivative K z (v j)

variable [CharZero K]

/-- The literal original primitive-basis coefficient sum for the value. -/
def valueMap (z : Spec (.of K) ⟶ chart K) (v : Fin 14 → Γ(chart K,⊤)) :
    Module.Dual K (LagrangianField.Primitive K) →ₗ[K] K where
  toFun ell := ∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) * value K z (v j)
  map_add' ell m := by
    simp only [LinearMap.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a ell := by
    simp only [LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The literal original primitive-basis coefficient sum in the actual
field-point cotangent, before any choice of six coordinates. -/
def derivativeMap (z : Spec (.of K) ⟶ chart K) (v : Fin 14 → Γ(chart K,⊤)) :
    Module.Dual K (LagrangianField.Primitive K) →ₗ[K] PointCotangent K z where
  toFun ell := ∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) • derivative K z (v j)
  map_add' ell m := by
    simp only [LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a ell := by
    simp only [LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

def firstJetMap (z : Spec (.of K) ⟶ chart K) (v : Fin 14 → Γ(chart K,⊤)) :
    Module.Dual K (LagrangianField.Primitive K) →ₗ[K] K × PointCotangent K z :=
  (valueMap K z v).prod (derivativeMap K z v)

theorem firstJetMap_apply (z : Spec (.of K) ⟶ chart K) (v : Fin 14 → Γ(chart K,⊤))
    (ell : Module.Dual K (LagrangianField.Primitive K)) :
    firstJetMap K z v ell =
      (∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) * value K z (v j),
        ∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) • derivative K z (v j)) := rfl

end M9Native.MukaiConormalChartJets
