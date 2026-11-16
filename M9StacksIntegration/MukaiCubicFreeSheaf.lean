module

public import M9StacksIntegration.MukaiCubicConstantSheaf
public import M9StacksIntegration.MukaiConstantFreeBasis
public import M9StacksIntegration.MukaiQuarticGradient
public import M9StacksIntegration.MukaiQuarticGradientTransport

/-!
# The genuine cubic in the original fourteen free-sheaf coordinates

The source basis is the dual of the actual native primitive basis. The
target is its actual dual basis. Both comparisons preserve each original
basis section, and their formulas use the original structural ring map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

namespace M9Native.MukaiCubicFreeSheaf

open MukaiBundleDeterminant MukaiPrimitiveQuartic MukaiCubicConstantSheaf
open MukaiConstantFreeBasis LinearIncidenceTensorCoordinates LagrangianMatrixChart

variable (K : Type u) [Field K] [CharZero K]

def formsBasis : Basis (Fin 14) K (Forms K) :=
  (LagrangianPluckerLinear.primitiveBasis14 K).dualBasis

def dualFormsBasis : Basis (Fin 14) K (Module.Dual K (Forms K)) :=
  (formsBasis K).dualBasis

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

def formsIso : constantObj (.of K) f (formModule K) ≅ freeOn X 14 :=
  constantBasisIso (.of K) f (formModule K) 14
    ((formsBasis K).reindex Equiv.ulift.symm)

def dualFormsIso : constantObj (.of K) f (dualFormModule K) ≅ freeOn X 14 :=
  constantBasisIso (.of K) f (dualFormModule K) 14
    ((dualFormsBasis K).reindex Equiv.ulift.symm)

def formSection (ell : Forms K) : Γ(freeOn X 14, ⊤) :=
  (formsIso K f).hom.app ⊤ (constantSection (.of K) f (formModule K) ell)

def dualFormSection (v : Module.Dual K (Forms K)) : Γ(freeOn X 14, ⊤) :=
  (dualFormsIso K f).hom.app ⊤ (constantSection (.of K) f (dualFormModule K) v)

theorem formSection_coordinates (ell : Forms K) (i : Fin 14) :
    freeSectionCoordinates X 14 (formSection K f ell) i =
      baseScalar (.of K) f (ell (LagrangianPluckerLinear.primitiveBasis14 K i)) := by
  have h := constantBasisIso_coordinates (.of K) f (formModule K) 14
    ((formsBasis K).reindex Equiv.ulift.symm) ell i
  simpa only [formSection, formsIso, constantSection, Basis.repr_reindex_apply, Equiv.symm_symm,
    Equiv.ulift_apply, formsBasis, Basis.dualBasis_repr] using h

theorem dualFormSection_coordinates (v : Module.Dual K (Forms K)) (i : Fin 14) :
    freeSectionCoordinates X 14 (dualFormSection K f v) i =
      baseScalar (.of K) f (v (formsBasis K i)) := by
  have h := constantBasisIso_coordinates (.of K) f (dualFormModule K) 14
    ((dualFormsBasis K).reindex Equiv.ulift.symm) v i
  simpa only [dualFormSection, dualFormsIso, constantSection, Basis.repr_reindex_apply, Equiv.symm_symm,
    Equiv.ulift_apply, dualFormsBasis, Basis.dualBasis_repr] using h

/-- The actual free-coordinate sheaf morphism, transported from the
canonical constant-bundle cubic rather than prescribed fiberwise. -/
def cubicFreeMap : tensor (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14) ⟶
    freeOn X 14 :=
  (tensorIso (tensorIso (formsIso K f).symm (formsIso K f).symm)
    (formsIso K f).symm).hom ≫ cubicMap K f ≫ (dualFormsIso K f).hom

theorem cubicFreeMap_section (a b c : Forms K) :
    (cubicFreeMap K f).app ⊤
      (tensorTop X (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14)
        (tensorTop X (freeOn X 14) (freeOn X 14) (formSection K f a) (formSection K f b))
        (formSection K f c)) =
      dualFormSection K f (primitiveCubic K a b c) := by
  have hcancel (ell : Forms K) : (formsIso K f).inv.app ⊤ (formSection K f ell) =
      constantSection (.of K) f (formModule K) ell :=
    congrArg (fun a => a.app ⊤ (constantSection (.of K) f (formModule K) ell))
      (formsIso K f).hom_inv_id
  change (dualFormsIso K f).hom.app ⊤ ((cubicMap K f).app ⊤
    ((tensorIso (tensorIso (formsIso K f).symm (formsIso K f).symm)
      (formsIso K f).symm).hom.app ⊤ _)) = _
  rw [tensorIso_tensorTop, tensorIso_tensorTop]
  simp only [Iso.symm_hom]
  rw [hcancel, hcancel, hcancel, cubicMap_section]
  rfl

def pointSection (v : LagrangianField.Primitive K) : Γ(freeOn X 14, ⊤) :=
  dualFormSection K f (Module.Dual.eval K (LagrangianField.Primitive K) v)

theorem pointSection_coordinates (v : LagrangianField.Primitive K) (i : Fin 14) :
    freeSectionCoordinates X 14 (pointSection K f v) i =
      baseScalar (.of K) f ((LagrangianPluckerLinear.primitiveBasis14 K).repr v i) := by
  rw [pointSection, dualFormSection_coordinates]
  simp only [formsBasis, Module.Dual.eval_apply, Basis.dualBasis_apply]

/-- The original local gradient, in actual global free-sheaf coordinates. -/
theorem cubicFreeMap_conormalForm (c : K) (S : LagrangianField.Symmetric3 K) :
    (cubicFreeMap K f).app ⊤
      (tensorTop X (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14)
        (tensorTop X (freeOn X 14) (freeOn X 14)
          (formSection K f (MukaiConormalPrimitive.conormalForm K (c,S)))
          (formSection K f (MukaiConormalPrimitive.conormalForm K (c,S))))
        (formSection K f (MukaiConormalPrimitive.conormalForm K (c,S)))) =
      dualFormSection K f ((4*S.val.det) •
        Module.Dual.eval K (LagrangianField.Primitive K) (MukaiConormalOrigin.originPoint K)) := by
  rw [cubicFreeMap_section, MukaiQuarticGradient.primitiveCubic_conormalForm_linear]

theorem dualFormSection_zero : dualFormSection K f 0 = 0 := by
  unfold dualFormSection constantSection
  rw [map_zero, map_zero, map_zero]

theorem dualFormSection_smul (a : K) (v : Module.Dual K (Forms K)) :
    dualFormSection K f (a • v) = baseScalar (.of K) f a • dualFormSection K f v := by
  change (dualFormsIso K f).hom.app ⊤
    (pullbackGlobalSections f (tilde (dualFormModule K))
      (topSection (.of K) (dualFormModule K) (a • v))) = _
  rw [pulled_topSec_smul, Scheme.Modules.Hom.app_smul]
  rfl

omit [CharZero K] in
theorem baseScalar_injective [Nonempty X] : Function.Injective (baseScalar (.of K) f) := by
  let : Nonempty (⊤ : X.Opens) := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨x, by trivial⟩⟩
  let : Nontrivial Γ(X, ⊤) := Scheme.component_nontrivial X ⊤
  exact (baseScalar (.of K) f).injective

theorem dualFormSection_injective [Nonempty X] : Function.Injective (dualFormSection K f) := by
  intro a b h
  apply (formsBasis K).ext
  intro i
  apply baseScalar_injective K f
  simpa only [dualFormSection_coordinates] using
    congrArg (fun t => freeSectionCoordinates X 14 t i) h

/-- Nonvanishing is derived from the actual exterior gradient and the
original structural field map on every nonempty scheme over the field. -/
theorem cubicFreeMap_conormalForm_ne_zero [Nonempty X]
    (c : K) (S : LagrangianField.Symmetric3 K) (hS : S.val.det ≠ 0) :
    (cubicFreeMap K f).app ⊤
      (tensorTop X (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14)
        (tensorTop X (freeOn X 14) (freeOn X 14)
          (formSection K f (MukaiConormalPrimitive.conormalForm K (c,S)))
          (formSection K f (MukaiConormalPrimitive.conormalForm K (c,S))))
        (formSection K f (MukaiConormalPrimitive.conormalForm K (c,S)))) ≠ 0 := by
  rw [cubicFreeMap_section]
  intro hz
  apply MukaiQuarticGradient.primitiveCubic_conormalForm_ne_zero K c S hS
  exact dualFormSection_injective K f (hz.trans (dualFormSection_zero K f).symm)

def tripleFormSection (a b c : Forms K) :
    Γ(tensor (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14), ⊤) :=
  tensorTop X (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14)
    (tensorTop X (freeOn X 14) (freeOn X 14) (formSection K f a) (formSection K f b))
    (formSection K f c)

theorem cubicFreeMap_transformed_conormalForm
    (g : Matrix.symplecticGroup (Fin 3) K) (c : K) (S : LagrangianField.Symmetric3 K) :
    (cubicFreeMap K f).app ⊤
      (tripleFormSection K f
        (MukaiQuarticGradientTransport.formsAction K g (MukaiConormalPrimitive.conormalForm K (c,S)))
        (MukaiQuarticGradientTransport.formsAction K g (MukaiConormalPrimitive.conormalForm K (c,S)))
        (MukaiQuarticGradientTransport.formsAction K g (MukaiConormalPrimitive.conormalForm K (c,S)))) =
      baseScalar (.of K) f (4*S.val.det) •
        pointSection K f (MukaiQuarticGradientTransport.transformedOrigin K g) := by
  change (cubicFreeMap K f).app ⊤
    (tensorTop X (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14)
      (tensorTop X (freeOn X 14) (freeOn X 14) _ _) _) = _
  rw [cubicFreeMap_section,
    MukaiQuarticGradientTransport.primitiveCubic_transformed_conormalForm,
    dualFormSection_smul]
  rfl

theorem cubicFreeMap_transformed_conormalForm_ne_zero [Nonempty X]
    (g : Matrix.symplecticGroup (Fin 3) K) (c : K) (S : LagrangianField.Symmetric3 K)
    (hS : S.val.det ≠ 0) :
    (cubicFreeMap K f).app ⊤
      (tripleFormSection K f
        (MukaiQuarticGradientTransport.formsAction K g (MukaiConormalPrimitive.conormalForm K (c,S)))
        (MukaiQuarticGradientTransport.formsAction K g (MukaiConormalPrimitive.conormalForm K (c,S)))
        (MukaiQuarticGradientTransport.formsAction K g (MukaiConormalPrimitive.conormalForm K (c,S)))) ≠ 0 := by
  change (cubicFreeMap K f).app ⊤
    (tensorTop X (tensor (freeOn X 14) (freeOn X 14)) (freeOn X 14)
      (tensorTop X (freeOn X 14) (freeOn X 14) _ _) _) ≠ 0
  rw [cubicFreeMap_section]
  intro hz
  apply MukaiQuarticGradientTransport.primitiveCubic_transformed_conormalForm_ne_zero K g c S hS
  exact dualFormSection_injective K f (hz.trans (dualFormSection_zero K f).symm)

end M9Native.MukaiCubicFreeSheaf
