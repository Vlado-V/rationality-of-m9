module

public import M9StacksIntegration.ProjectiveRatioFieldDifferential
public import M9StacksIntegration.DeterminantRankOneDifferential

/-!
# Actual local universal derivatives at an arbitrary field-valued point

The base of the relative differentials is arbitrary. Thus the field
of the point may be a genuine residue-field extension of the original
coefficient field. The entire coefficient action comes from the actual
local section pullback, not a supplied fibre comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.FieldPointLocalDerivation

open SpecFieldStalkSections SpecFieldPullbackSections

variable (K : Type u) [Field K] {X S : Scheme.{u}}
  (b : X ⟶ S) (z : Spec (.of K) ⟶ X)
  (U : X.Opens) (hz : z.base (point K) ∈ U)

abbrev Cotangent := moduleSpecΓFunctor.obj
  ((Scheme.Modules.pullback z).obj (Scheme.Hom.relativeDifferentials b))

/-- The actual local coefficient value at the original field-valued point. -/
def valueOnRingHom : Γ(X,U) →+* K :=
  (ProjectiveRatioFieldValues.scalarEquiv K).toRingHom.comp
    (z.appLE U ⊤ (preimageTop K z U hz)).hom

theorem valueOnRingHom_apply (r : Γ(X,U)) :
    valueOnRingHom K z U hz r = ProjectiveRatioFieldValues.valueOn K z U hz r := rfl

/-- The actual local universal derivative, pulled to the whole original field spectrum. -/
def derivativeOn : Γ(X,U) →+ Cotangent K b z where
  toFun r := pulledSection K z (Scheme.Hom.relativeDifferentials b) U hz
    ((Scheme.Hom.universalRelativeDerivation b).d r)
  map_zero' := by
    rw [map_zero]
    exact map_zero (pullbackSectionHom z
      (Scheme.Hom.relativeDifferentials b) U ⊤ (preimageTop K z U hz)).hom
  map_add' r s := by
    rw [map_add]
    exact ProjectiveRatioFieldDifferential.pulledSection_add K z
      (Scheme.Hom.relativeDifferentials b) U hz _ _

/-- Genuine local coefficients act through their actual point values. -/
@[instance_reducible]
def sectionModule : Module Γ(X,U) (Cotangent K b z) :=
  Module.compHom (Cotangent K b z) (valueOnRingHom K z U hz)

/-- The actual local derivative satisfies the genuine Leibniz identity. -/
def pointDerivation :
    letI := sectionModule K b z U hz
    Derivation ℤ Γ(X,U) (Cotangent K b z) := by
  letI := sectionModule K b z U hz
  apply Derivation.mk' (derivativeOn K b z U hz).toIntLinearMap
  intro a c
  change pulledSection K z (Scheme.Hom.relativeDifferentials b) U hz
      ((Scheme.Hom.universalRelativeDerivation b).d (a*c)) =
    valueOnRingHom K z U hz a • derivativeOn K b z U hz c +
      valueOnRingHom K z U hz c • derivativeOn K b z U hz a
  rw [(Scheme.Hom.universalRelativeDerivation b).d_mul,
    ProjectiveRatioFieldDifferential.pulledSection_add,
    ProjectiveRatioFieldDifferential.pulledSection_smul,
    ProjectiveRatioFieldDifferential.pulledSection_smul]
  rfl

/-- Rank at most one gives zero actual native derivative of the literal local determinant. -/
theorem derivativeOn_det_eq_zero_of_rank_le_one
    (A : Matrix (Fin 3) (Fin 3) Γ(X,U))
    (hr : (A.map (valueOnRingHom K z U hz)).rank ≤ 1) :
    derivativeOn K b z U hz A.det = 0 := by
  letI : Algebra Γ(X,U) K := (valueOnRingHom K z U hz).toAlgebra
  letI := sectionModule K b z U hz
  letI : IsScalarTower Γ(X,U) K (Cotangent K b z) :=
    ⟨fun r a m => mul_smul (valueOnRingHom K z U hz r) a m⟩
  exact DeterminantRankOneDifferential.derivation_det_eq_zero_of_rank_map_le_one
    (pointDerivation K b z U hz) A hr

end M9Native.FieldPointLocalDerivation
