module

public import M9StacksIntegration.LagrangianDeterminantAction

/-! The actual quotient-action matrix in an actual quotient frame,
proved with an abstract test scheme before affine specialization. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianDeterminantActionMatrix

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianSymplecticAction LagrangianDeterminantAction
open AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K]
  {T : Scheme.{u}} (f : T ⟶ space K) (g : Matrix.symplecticGroup (Fin 3) K)
  (e : (pullbackPresentation f (quotientOnLG K)).target ≅ freeOn T 3)

theorem framed_matrix :
    Stacks.FreeSheafMatrix.toMatrix
      ((pullbackPresentation (f ≫ action K g) (quotientOnLG K)).map ≫
        (quotientActionIso K f g ≪≫ e).hom) =
      Stacks.FreeSheafMatrix.toMatrix
        ((pullbackPresentation f (quotientOnLG K)).map ≫ e.hom) *
          constantMatrix K (f ≫ projection K) g := by
  have he : (pullbackPresentation (f ≫ action K g) (quotientOnLG K)).map ≫
      (quotientActionIso K f g ≪≫ e).hom =
      (constantFreeIso K (f ≫ projection K) g).hom ≫
        ((pullbackPresentation f (quotientOnLG K)).map ≫ e.hom) := by
    change (pullbackPresentation (f ≫ action K g) (quotientOnLG K)).map ≫
      ((quotientActionIso K f g).hom ≫ e.hom) = _
    calc
      _ = ((pullbackPresentation (f ≫ action K g) (quotientOnLG K)).map ≫
          (quotientActionIso K f g).hom) ≫ e.hom := (Category.assoc _ _ _).symm
      _ = ((constantFreeIso K (f ≫ projection K) g).hom ≫
          (pullbackPresentation f (quotientOnLG K)).map) ≫ e.hom :=
        congrArg (fun a => a ≫ e.hom) (quotientActionIso_triangle K f g)
      _ = _ := Category.assoc _ _ _
  rw [he,Stacks.FreeSheafMatrix.toMatrix_comp,constantFreeIso_matrix]

/-- Constant coefficient extension commutes with actual row multiplication. -/
theorem map_mul_scalar {R S k : Type*} [CommRing R] [CommRing S] [CommRing k]
    (M : Matrix (Fin 3) (Fin 6) R) (G : Matrix (Fin 6) (Fin 6) k)
    (κ : k →+* R) (φ : R →+* S) :
    M.map φ * G.map (φ.comp κ) = (M * G.map κ).map φ := by
  rw [Matrix.map_mul,Matrix.map_map]
  rfl

end M9Native.LagrangianDeterminantActionMatrix
