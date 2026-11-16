module

public import M9StacksIntegration.MukaiPointLine
public import M9StacksIntegration.MukaiCubicCurveKernel
public import M9StacksIntegration.LagrangianPluckerGeneration

/-!
# The actual inverse determinant point line of the canonical LG map

The original universal fourteen-section epimorphism is pulled back along
the actual curve map and transported by its actual determinant isomorphism.
The basis columns are exactly the original third-exterior evaluation
sections. Dualizing this constructed epimorphism gives the genuine inverse
determinant line in the original free fourteen-coordinate sheaf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.MukaiCurvePointLine

open MukaiPrimitiveCanonicalEvaluation MukaiPointLine LagrangianMatrixChart
open LagrangianPluckerQuotient LagrangianSectionGeneration
open AlgebraicGeometry.Grassmannian SectionZeroIdealFactorization

variable (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)

def determinantQuotient : freeOn X 14 ⟶ Scheme.Modules.exteriorPower E (3 : ℤ) :=
  (pullbackFreeIso d.map 14).inv ≫
    (Scheme.Modules.pullback d.map).map (primitiveDeterminantMap K) ≫
      (d.determinantIso K f E).hom

instance determinantQuotient_epi : Epi (determinantQuotient K f E b d) := by
  let : Epi (primitiveDeterminantMap K) := LagrangianPluckerEpimorphism.primitiveDeterminantMap_epi K
  let : (Scheme.Modules.pullback d.map).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction d.map).isLeftAdjoint
  unfold determinantQuotient
  infer_instance

theorem determinantQuotient_column (j : Fin 14) :
    (determinantQuotient K f E b d).app ⊤ (freeBasisSection X 14 j) =
      (cohomologyOverFieldZeroLinearIso K f (Scheme.Modules.exteriorPower E (3 : ℤ))).hom
        (primitiveEvaluation K f E b ((LagrangianPluckerLinear.primitiveBasis14 K).dualBasis j)) := by
  change (d.determinantIso K f E).hom.app ⊤
    (((Scheme.Modules.pullback d.map).map (primitiveDeterminantMap K)).app ⊤
      ((pullbackFreeIso d.map 14).inv.app ⊤ (freeBasisSection X 14 j))) = _
  rw [FiniteFreeBasisPullback.inverse_freeBasisSection_pullback,
    pullback_map_app_pullbackGlobalSections]
  have hj : (primitiveDeterminantMap K).app ⊤
      (freeBasisSection (LagrangianGrassmannian.space K) 14 j) = primitiveSections K j :=
    sectionMap_top_basis _ _ _ j
  rw [hj]
  exact d.primitiveCoordinates K f E j

def curvePointLine : dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ)) ⟶ freeOn X 14 :=
  pointLineMap (determinantQuotient K f E b d)

theorem curvePointLine_coordinates
    (a : Γ(dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ)), ⊤)) (j : Fin 14) :
    freeSectionCoordinates X 14 ((curvePointLine K f E b d).app ⊤ a) j =
      evalAt (Scheme.Modules.exteriorPower E (3 : ℤ)) a
        ((cohomologyOverFieldZeroLinearIso K f (Scheme.Modules.exteriorPower E (3 : ℤ))).hom
          (primitiveEvaluation K f E b ((LagrangianPluckerLinear.primitiveBasis14 K).dualBasis j))) := by
  rw [curvePointLine, pointLineMap_coordinates, determinantQuotient_column]

variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

theorem curvePointLine_mono : Mono (curvePointLine K f E b d) := by
  apply pointLineMap_mono
  simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3

theorem curvePointSequence_shortExact :
    (pointSequence (determinantQuotient K f E b d)).ShortExact := by
  apply pointSequence_shortExact
  simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3

theorem curvePointLine_cokernel_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel (curvePointLine K f E b d)) 13 := by
  apply pointLineCokernel_rank
  simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3

end M9Native.MukaiCurvePointLine
