module

public import M9StacksIntegration.LagrangianPrimitiveQuadricVanishing
public import M9StacksIntegration.HomogeneousEquationPullback
public import M9StacksIntegration.LagrangianPolynomialPluckerEquivariance
public import M9StacksIntegration.LagrangianAdmissibleCharts

/-! A genuine finite family of homogeneous quadratic equations on the
original polynomial P13: the original twenty-one and their eight actual
admissible symplectic translates. All vanish scheme-theoretically on LG. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.LagrangianTranslatedQuadricFamily

open LagrangianPolynomialPluckerEquivariance LagrangianPrimitiveQuadricVanishing

variable (K : Type u) [Field K] [CharZero K]

def translatedForm (g : Matrix.symplecticGroup (Fin 3) K)
    (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) : polyGrading K 13 2 :=
  HomogeneousEquationPullback.imageForm K 13 13 2
    (NativeProjectiveLinear.substitution K 13 (primitiveGL K g).val)
    (LagrangianPrimitiveQuadrics.form K) i

def translatedIdeal (g : Matrix.symplecticGroup (Fin 3) K)
    (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    (AlgebraicGeometry.Proj (polyGrading K 13)).IdealSheafData :=
  HomogeneousEquationIdeal.equationIdeal K 13 2 (translatedForm K g) i

theorem substitution_surjective (g : Matrix.symplecticGroup (Fin 3) K) :
    Function.Surjective (NativeProjectiveLinear.substitution K 13 (primitiveGL K g).val) := by
  intro p
  refine ⟨NativeProjectiveLinear.substitution K 13 ((primitiveGL K g)⁻¹).val p, ?_⟩
  have h := congrArg (fun ψ : polyGrading K 13 →+*ᵍ polyGrading K 13 => ψ p)
    (NativeProjectiveLinear.substitution_comp K 13 ((primitiveGL K g)⁻¹).val (primitiveGL K g).val)
  rw [Units.inv_mul, NativeProjectiveLinear.substitution_one] at h
  exact h

theorem translatedIdeal_eq_comap (g : Matrix.symplecticGroup (Fin 3) K)
    (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    translatedIdeal K g i = (originalQuadricIdeal K i).comap
      (NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K g)).hom := by
  exact (HomogeneousEquationPullback.equationIdeal_comap K 13 13 2
    (NativeProjectiveLinear.substitution K 13 (primitiveGL K g).val)
    (substitution_surjective K g)
    (LagrangianPrimitiveQuadrics.form K) i).symm

theorem originalQuadric_comap_eq_bot (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    (originalQuadricIdeal K i).comap (polynomialPlucker K) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
  simpa only [Scheme.IdealSheafData.map_bot] using originalQuadric_le_kernel K i

/-- The actual polynomial-P13 action triangle and actual graded twist
pullback identify the translated equations on the original closed LG. -/
theorem translatedIdeal_le_kernel (g : Matrix.symplecticGroup (Fin 3) K)
    (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    translatedIdeal K g i ≤ (polynomialPlucker K).ker := by
  rw [translatedIdeal_eq_comap, ← Scheme.IdealSheafData.map_bot (polynomialPlucker K)]
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mpr
  have h : ((originalQuadricIdeal K i).comap
        (NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K g)).hom).comap
        (polynomialPlucker K) = ⊥ := by
    rw [← Scheme.IdealSheafData.comap_comp, ← action_polynomialPlucker,
      Scheme.IdealSheafData.comap_comp, originalQuadric_comap_eq_bot,
      Scheme.IdealSheafData.comap_bot]
  exact h.le

abbrev TranslationIndex := Unit ⊕ LagrangianAdmissibleMinors.Choice
abbrev FamilyIndex := TranslationIndex × LagrangianHomogeneousQuadrics.QuadricIndex.{u}

def familyForm (i : FamilyIndex.{u}) : polyGrading K 13 2 :=
  match i.1 with
  | Sum.inl _ => LagrangianPrimitiveQuadrics.form K i.2
  | Sum.inr s => translatedForm K (LagrangianAdmissibleCharts.swap K s) i.2

def familyIdeal : (AlgebraicGeometry.Proj (polyGrading K 13)).IdealSheafData :=
  ⨆ i, HomogeneousEquationIdeal.equationIdeal K 13 2 (familyForm K) i

theorem original_le_familyIdeal (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    originalQuadricIdeal K i ≤ familyIdeal K :=
  le_iSup (fun i => HomogeneousEquationIdeal.equationIdeal K 13 2 (familyForm K) i)
    (Sum.inl (), i)

theorem translated_swap_le_familyIdeal (s : LagrangianAdmissibleMinors.Choice)
    (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    translatedIdeal K (LagrangianAdmissibleCharts.swap K s) i ≤ familyIdeal K :=
  le_iSup (fun i => HomogeneousEquationIdeal.equationIdeal K 13 2 (familyForm K) i)
    (Sum.inr s, i)

/-- The actual finite quadratic zero scheme contains the original LG
as a closed subscheme, with its full structure. The reverse containment
is the separate chart-ideal/gluing theorem. -/
theorem familyIdeal_le_kernel : familyIdeal K ≤ (polynomialPlucker K).ker := by
  apply iSup_le
  intro i
  rcases i with ⟨t,i⟩
  cases t with
  | inl t => exact originalQuadric_le_kernel K i
  | inr s => exact translatedIdeal_le_kernel K (LagrangianAdmissibleCharts.swap K s) i

end M9Native.LagrangianTranslatedQuadricFamily
