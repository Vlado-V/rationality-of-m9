module

public import M9StacksIntegration.LagrangianArbitraryPlaneIncidenceSmooth
public import M9StacksIntegration.ChowP1RegularSection

/-! The actual arbitrary-plane incidence has the genuine second-Chern
pushforward class. Actual dimension and regularity are derived from the
original independent plane and full native zero geometry, so no class,
regularity, dimension, or symplectic-plane premise is supplied. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.Chow Stacks.Chow.GenuineChern
universe u

namespace M9Native.LagrangianArbitraryPlaneIncidenceClass

open LagrangianGrassmannian LagrangianPluckerQuotient
open LagrangianArbitraryPlaneIncidence LagrangianArbitraryPlaneIncidenceSmooth
variable (K : Type u) [Field K] [CharZero K]

/-- The full native incidence fundamental class pushes to the actual
c2 of the original universal quotient, for every original independent
plane, including isotropic planes. Nilpotents are retained throughout. -/
theorem incidence_fundamental_push_eq_secondChern_associated
    (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    ChowLineProperPush.properPush (fieldChowSituation K)
      (incidenceInclusion K w ≫ LagrangianArbitraryPlaneIncidence.toLG K ≫ projection K)
      (projection K) (incidenceToLG K w) (Category.assoc _ _ _) 4
      (fundamentalChowClass (fieldChowSituation K)
        (incidenceInclusion K w ≫ LagrangianArbitraryPlaneIncidence.toLG K ≫ projection K) 4) =
      chernCap (fieldChowSituation K) 3 (projection K) (quotientOnLG K).target 6
        ⟨2,by decide⟩ (fundamentalChowClass (fieldChowSituation K) (projection K) 6) := by
  have hX : schemeDeltaDimension (fieldChowSituation K) (projection K) ≤ ((6 : ℤ) : EInt) := by
    simpa only [Nat.cast_ofNat] using
      SmoothRelativeChowDimension.schemeDeltaDimension_le_of_smooth_relative_dimension K (projection K) 6
  have hZ : schemeDeltaDimension (fieldChowSituation K)
      (incidenceInclusion K w ≫ LagrangianArbitraryPlaneIncidence.toLG K ≫ projection K) ≤ ((4 : ℤ) : EInt) := by
    simpa only [toBase,incidenceToLG,Category.assoc] using incidence_delta_dimension_le K w hw
  exact ChowP1RegularSection.compositePush_zeroFundamental_eq_secondChern
    (planeSource K) (quotientOnLG K).target (fieldChowSituation K) (projection K)
    (equationSection K w) (Iso.refl _) 6 hX hZ (regularSequence K w hw)

private theorem properPush_fundamental_base_canonical
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (qX : X ⟶ C.S) [LocallyOfFiniteType qX] (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ qY = qX) (k : ℤ) :
    ChowLineProperPush.properPush C qX qY p hp k (fundamentalChowClass C qX k) =
      ChowLineProperPush.properPush C (p ≫ qY) qY p rfl k
        (fundamentalChowClass C (p ≫ qY) k) := by
  subst qX
  rfl

/-- The same actual c2 push uses the canonical original structural map
incidenceToLG followed by the original ground-field projection, with
literal rfl as its proper-push triangle. -/
theorem incidence_fundamental_push_eq_secondChern
    (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    ChowLineProperPush.properPush (fieldChowSituation K)
      (toBase K w) (projection K) (incidenceToLG K w) rfl 4
      (fundamentalChowClass (fieldChowSituation K) (toBase K w) 4) =
      chernCap (fieldChowSituation K) 3 (projection K) (quotientOnLG K).target 6
        ⟨2,by decide⟩ (fundamentalChowClass (fieldChowSituation K) (projection K) 6) := by
  have h := properPush_fundamental_base_canonical (fieldChowSituation K)
    (incidenceInclusion K w ≫ LagrangianArbitraryPlaneIncidence.toLG K ≫ projection K)
    (projection K) (incidenceToLG K w) (Category.assoc _ _ _) 4
  exact h.symm.trans (incidence_fundamental_push_eq_secondChern_associated K w hw)

end M9Native.LagrangianArbitraryPlaneIncidenceClass
