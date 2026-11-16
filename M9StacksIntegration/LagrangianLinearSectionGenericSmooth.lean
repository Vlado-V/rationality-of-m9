module

public import M9StacksIntegration.LagrangianLinearSectionSmooth
public import M9StacksIntegration.SmoothRelativeDimensionSubtraction
public import M9StacksIntegration.LagrangianIncidenceDominance
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Smooth

/-! A genuine nonempty parameter open on which the original universal
LG linear-section family is proper and smooth of relative dimension one. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace M9Native.LagrangianLinearSectionGenericSmooth
open M9Native.LagrangianLinearSections M9Native.LagrangianLinearSectionSmooth
variable (K : Type u) [Field K]

instance parameterProjection_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 45 (parameterProjection K) :=
  AlgebraicGeometry.Grassmannian.smoothOfRelativeDimension_schemeOver 9 14 (Spec (.of K))

instance parameterProjection_smooth : Smooth (parameterProjection K) :=
  SmoothOfRelativeDimension.smooth 45 _

instance parameter_locallyNoetherian : IsLocallyNoetherian (parameter K) :=
  LocallyOfFiniteType.isLocallyNoetherian (parameterProjection K)

instance familyProjection_locallyOfFinitePresentation : LocallyOfFinitePresentation (familyProjection K) :=
  inferInstance

theorem family_regular [CharZero K] : IsRegular (family K) :=
  isRegular_of_smooth_over_field (absoluteProjection K)

def goodOpen : (parameter K).Opens := M9Native.ProperSmoothLocus.goodOpen (familyProjection K)

theorem goodOpen_nonempty [CharZero K] : (goodOpen K : Set (parameter K)).Nonempty := by
  let : Algebra K ((parameter K).residueField (genericPoint (parameter K))) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (parameterProjection K).appTop ≫
      (parameter K).Γevaluation (genericPoint (parameter K))).hom.toAlgebra
  have : CharZero ((parameter K).residueField (genericPoint (parameter K))) :=
    charZero_of_injective_algebraMap
      (algebraMap K ((parameter K).residueField (genericPoint (parameter K)))).injective
  exact M9Native.ProperSmoothLocus.goodOpen_nonempty (familyProjection K) (family_regular K)

def restrictedProjection : ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme ⟶ (goodOpen K).toScheme :=
  familyProjection K ∣_ goodOpen K

instance restrictedProjection_proper : IsProper (restrictedProjection K) :=
  M9Native.ProperSmoothLocus.restrict_proper (familyProjection K)

instance restrictedProjection_smooth : Smooth (restrictedProjection K) :=
  M9Native.ProperSmoothLocus.restrict_smooth (familyProjection K)

/-- The actual restricted family has relative dimension one, from actual dimensions 46 and 45. -/
instance restrictedProjection_smoothOfRelativeDimension [CharZero K] :
    SmoothOfRelativeDimension 1 (restrictedProjection K) := by
  let g : (goodOpen K).toScheme ⟶ Spec (.of K) := (goodOpen K).ι ≫ parameterProjection K
  have : SmoothOfRelativeDimension 45 g :=
    smoothOfRelativeDimension_comp (n:=0) (m:=45) _ _
  have h : restrictedProjection K ≫ g=
      ((familyProjection K) ⁻¹ᵁ goodOpen K).ι ≫ absoluteProjection K := by
    dsimp only [restrictedProjection,g]
    rw [← Category.assoc,morphismRestrict_ι,Category.assoc]
    rfl
  have : SmoothOfRelativeDimension (1+45) (restrictedProjection K ≫ g) := by
    rw [h]
    exact smoothOfRelativeDimension_comp (n:=0) (m:=46) _ _
  exact M9Native.SmoothRelativeDimensionSubtraction.smoothOfRelativeDimension_of_comp
    (restrictedProjection K) g 1 45

instance restrictedProjection_surjective [CharZero K] [IsAlgClosed K] :
    Surjective (restrictedProjection K) := by
  dsimp only [restrictedProjection,morphismRestrict]
  infer_instance

instance baseChange_smoothOfRelativeDimension [CharZero K] {T : Scheme.{u}}
    (p : T ⟶ (goodOpen K).toScheme) :
    SmoothOfRelativeDimension 1 (pullback.snd (restrictedProjection K) p) := inferInstance

instance baseChange_proper {T : Scheme.{u}} (p : T ⟶ (goodOpen K).toScheme) :
    IsProper (pullback.snd (restrictedProjection K) p) := inferInstance

instance baseChange_surjective [CharZero K] [IsAlgClosed K] {T : Scheme.{u}}
    (p : T ⟶ (goodOpen K).toScheme) :
    Surjective (pullback.snd (restrictedProjection K) p) := inferInstance

end M9Native.LagrangianLinearSectionGenericSmooth
end
