module

public import M9StacksIntegration.MukaiConormalBigCellFirstJet
public import M9StacksIntegration.MukaiConormalFieldCoordinates
public import M9StacksIntegration.LineFramePullback

/-! The actual standard LG field point and the actual determinant-line
frame obtained from its original normalized quotient. All fourteen
positive sections retain their native coefficients. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.MukaiConormalOriginFrame

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open MukaiConormalBigCellSections MukaiConormalBigCellFirstJet
open MukaiConormalOriginCoordinates LinearIncidenceTensorCoordinates

variable (K : Type u) [Field K]

def zeroPoint : Spec (.of K) ⟶ chart K :=
  Spec.map (CommRingCat.ofHom (originEval K).toRingHom)

def origin : Spec (.of K) ⟶ space K := zeroPoint K ≫ bigCell K

theorem zeroPoint_scalar (r : PolynomialRing K) :
    (zeroPoint K).appTop (MukaiConormalBigCellSections.scalarEquiv K r) =
      MukaiConormalFieldCoordinates.scalarEquiv K (originEval K r) := by
  change (Spec.map (CommRingCat.ofHom (originEval K).toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of (PolynomialRing K))).inv r) =
    (Scheme.ΓSpecIso (.of K)).inv ((originEval K).toRingHom r)
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem origin_over_base : origin K ≫ projection K = 𝟙 (Spec (.of K)) := by
  change (zeroPoint K ≫ bigCell K) ≫ projection K = _
  rw [Category.assoc, bigCell_projection]
  change Spec.map (CommRingCat.ofHom (originEval K).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PolynomialRing K)) = _
  rw [← Spec.map_comp]
  have hc : (CommRingCat.ofHom (MvPolynomial.C : K →+* PolynomialRing K)) ≫
      CommRingCat.ofHom (originEval K).toRingHom = 𝟙 (CommRingCat.of K) := by
    ext a
    exact (originEval K).commutes a
  rw [hc, Spec.map_id]

/-- No field-line identification is supplied: the frame comes from the
actual affine quotient frame and the canonical native unit comparison. -/
def determinantFrame :
    (Scheme.Modules.pullback (origin K)).obj (determinantLine K) ≅
      SheafOfModules.unit (Spec (.of K)).ringCatSheaf :=
  ((Scheme.Modules.pullbackComp (zeroPoint K) (bigCell K)).app (determinantLine K)).symm ≪≫
    LineFramePullback.pullbackFrame (zeroPoint K)
      ((Scheme.Modules.pullback (bigCell K)).obj (determinantLine K))
      (MukaiConormalBigCellSections.determinantIso K)

theorem determinantFrame_coordinate (j : Fin 14) :
    (determinantFrame K).hom.app ⊤
      (pullbackGlobalSections (origin K) (determinantLine K) (primitiveSections K j)) =
        MukaiConormalFieldCoordinates.scalarEquiv K (originEval K (sectionPolynomial K j)) := by
  change unitCoordinate (Spec (.of K))
    ((LineFramePullback.pullbackFrame (zeroPoint K)
      ((Scheme.Modules.pullback (bigCell K)).obj (determinantLine K))
      (MukaiConormalBigCellSections.determinantIso K)).hom.app ⊤
        (((Scheme.Modules.pullbackComp (zeroPoint K) (bigCell K)).inv.app
          (determinantLine K)).app ⊤
            (pullbackGlobalSections (zeroPoint K ≫ bigCell K) (determinantLine K)
              (primitiveSections K j)))) = _
  rw [LineFramePullback.pullbackComp_inv_apply,
    LineFramePullback.pullbackFrame_coordinate, determinantIso_coordinate]
  exact zeroPoint_scalar K _

theorem determinantFrame_pivot :
    (determinantFrame K).hom.app ⊤
      (pullbackGlobalSections (origin K) (determinantLine K)
        (primitiveSections K originPivot)) = (1 : Γ(Spec (.of K),⊤)) := by
  rw [determinantFrame_coordinate, sectionPolynomial_pivot, map_one, map_one]

variable [CharZero K]

theorem determinantFrame_coordinate_value (j : Fin 14) :
    (determinantFrame K).hom.app ⊤
      (pullbackGlobalSections (origin K) (determinantLine K) (primitiveSections K j)) =
        MukaiConormalFieldCoordinates.scalarEquiv K
          ((LagrangianPluckerLinear.primitiveBasis14 K).equivFun
            (MukaiConormalOrigin.originPoint K) j) := by
  rw [determinantFrame_coordinate, sectionPolynomial_origin_primitive]

end M9Native.MukaiConormalOriginFrame
