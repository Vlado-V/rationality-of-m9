module

public import M9StacksIntegration.LagrangianCotangentSymplectic
public import M9StacksIntegration.MukaiConormalFieldCoordinates

/-! Actual values and actual cotangent-valued first derivatives at a
rational field point. Coefficient naturality follows from the original
base triangle and universal relative derivation, rather than a scalar
or first-jet compatibility premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module
open scoped BigOperators

universe u v

namespace M9Native.LagrangianFieldJetCoefficients

open LagrangianSymplecticAction

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (b : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X)

abbrev Cotangent := moduleSpecΓFunctor.obj
  ((Scheme.Modules.pullback z).obj (Scheme.Hom.relativeDifferentials b))

def pointValue : Γ(X,⊤) →+* K :=
  (Scheme.ΓSpecIso (.of K)).hom.hom.comp z.appTop.hom

def pointDerivative : Γ(X,⊤) →+ Cotangent K b z where
  toFun s := pullbackGlobalSections z (Scheme.Hom.relativeDifferentials b)
    ((Scheme.Hom.universalRelativeDerivation b).d s)
  map_zero' := by rw [map_zero,map_zero]
  map_add' s t := by rw [map_add,map_add]

theorem pointValue_apply (s : Γ(X,⊤)) :
    pointValue K z s = (Scheme.ΓSpecIso (.of K)).hom (z.appTop s) := rfl

theorem pointDerivative_apply (s : Γ(X,⊤)) :
    pointDerivative K b z s = pullbackGlobalSections z (Scheme.Hom.relativeDifferentials b)
      ((Scheme.Hom.universalRelativeDerivation b).d s) := rfl

/-- The actual base identity forces the actual scalar pullback to be
exactly the original field scalar map. -/
theorem scalar_pullback (hz : z ≫ b = 𝟙 _) (a : K) :
    z.appTop (scalarMap K b a) = (Scheme.ΓSpecIso (.of K)).inv a := by
  have h := RingHom.congr_fun (scalarMap_comp K b z) a
  rw [hz,scalarMap_id] at h
  exact h.symm

theorem pointValue_scalar (hz : z ≫ b = 𝟙 _) (a : K) :
    pointValue K z (scalarMap K b a) = a := by
  rw [pointValue_apply,scalar_pullback K b z hz]
  exact (Scheme.ΓSpecIso (.of K)).inv_hom_id_apply a

/-- The original universal relative derivation kills the actual
constant coefficient from the base. -/
theorem scalar_derivative_zero (a : K) :
    (Scheme.Hom.universalRelativeDerivation b).d (scalarMap K b a) = 0 :=
  Scheme.Hom.universalRelativeDerivation_d_app_eq_zero b ⊤
    ((Scheme.ΓSpecIso (.of K)).inv a)

theorem pointDerivative_scalar_mul (hz : z ≫ b = 𝟙 _) (a : K) (s : Γ(X,⊤)) :
    pointDerivative K b z (scalarMap K b a * s) = a • pointDerivative K b z s := by
  rw [pointDerivative_apply,(Scheme.Hom.universalRelativeDerivation b).d_mul,
    scalar_derivative_zero K b,smul_zero,add_zero,
    SectionsEqualizer.pullbackGlobalSections_smul,scalar_pullback K b z hz]
  rfl

theorem pointValue_sum_constants {I : Type v} [Fintype I]
    (hz : z ≫ b = 𝟙 _) (c : I → K) (s : I → Γ(X,⊤)) :
    pointValue K z (∑ i, scalarMap K b (c i) * s i) =
      ∑ i, c i * pointValue K z (s i) := by
  simp only [map_sum,map_mul,pointValue_scalar K b z hz]

theorem pointDerivative_sum_constants {I : Type v} [Fintype I]
    (hz : z ≫ b = 𝟙 _) (c : I → K) (s : I → Γ(X,⊤)) :
    pointDerivative K b z (∑ i, scalarMap K b (c i) * s i) =
      ∑ i, c i • pointDerivative K b z (s i) := by
  simp only [map_sum,pointDerivative_scalar_mul K b z hz]

end M9Native.LagrangianFieldJetCoefficients
