module

public import M9StacksIntegration.LagrangianNativeGenusNineFamily
public import M9StacksIntegration.NativeSmoothGenusCoarseClassifier
public import M9StacksIntegration.ASClassifierGeometricLift
public import M9StacksIntegration.AllTestNativeOriginalPullbacks

/-! The original universal Lagrangian family maps to the actual chosen
genus-nine coarse space. Its genuine Bertini point supplies an actual native
field-valued point of that same target. No classifying map, genus, bound,
point, or nonemptiness hypothesis is introduced. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite

namespace M9Native.LagrangianChosenCoarseFamily
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalPullbacks

universe u
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
  (hZ : B.Contains integerBase)

/-- The independently constructed actual field-base coarse space. -/
abbrev target : AlgebraicSpaces B (Spec (.of K)) hK :=
  M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK 9 (by decide)

/-- The actual native classifier of the original universal genus-nine family. -/
def fieldClassifier :
    BasedCategory.ofFunctor (Over.forget (LagrangianNativeGenusNineFamily.base K B hK)) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
        B hZ K hK 9 (by decide)).val.val :=
  NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK
    (LagrangianNativeGenusNineFamily.base K B hK)
    (LagrangianNativeGenusNineFamily.integerProjection K B hK hZ) 9 (by decide)
    (LagrangianNativeGenusNineFamily.original_schemeCurve K B hK hZ)

/-- The actual induced map to that same chosen native coarse space. -/
def nativeMap : schemeSpace (LagrangianNativeGenusNineFamily.base K B hK) ⟶
    target K B hK hZ :=
  ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK 9 (by decide))
    (fieldClassifier K B hK hZ)

/-- Its extension to every original test scheme retains the original base. -/
def originalMap :
    yoneda.obj ((boundedInclusion B K hK).obj (LagrangianNativeGenusNineFamily.base K B hK)) ⟶
      (originalPresheafFunctor K B hK).obj (target K B hK hZ) :=
  originalChart K B hK (target K B hK hZ)
    (LagrangianNativeGenusNineFamily.base K B hK) (nativeMap K B hK hZ).hom

/-- The actual value at any original field point, with no site cutoff on L. -/
def pointValue (L : Type u) [Field L] [Algebra K L]
    (x : M9StandaloneDraft.FieldPoint K L ⟶
      (boundedInclusion B K hK).obj (LagrangianNativeGenusNineFamily.base K B hK)) :
    ((originalPresheafFunctor K B hK).obj (target K B hK hZ)).obj
      (op (M9StandaloneDraft.FieldPoint K L)) :=
  (originalMap K B hK hZ).app (op (M9StandaloneDraft.FieldPoint K L)) x

/-- The constructed original Bertini point evaluated in the same coarse map. -/
def bertiniFieldPoint : Space.FieldValuedPoint B (Spec (.of K)) hK
    (target K B hK hZ).obj where
  carrier := K
  contained := hK
  toBase := 𝟙 (Spec (.of K))
  value := (nativeMap K B hK hZ).hom.app
    (op (siteObject B (Spec (.of K)) hK hK (𝟙 (Spec (.of K)))))
    (LagrangianNativeGenusNineFamily.bertiniPoint K B hK)

/-- The field-valued witness uses the original algebraically closed field. -/
theorem bertiniFieldPoint_isAlgClosed :
    IsAlgClosed (bertiniFieldPoint K B hK hZ).carrier := by
  change IsAlgClosed K
  infer_instance

/-- Actual native field-valued points of the chosen target are nonempty. -/
theorem fieldValuedPoints_nonempty :
    Nonempty (Space.FieldValuedPoint B (Spec (.of K)) hK (target K B hK hZ).obj) :=
  ⟨bertiniFieldPoint K B hK hZ⟩

/-- The genuine field witness supplies a point of the actual native target. -/
def bertiniPoint : Space.points B (Spec (.of K)) hK (target K B hK hZ).obj :=
  Space.FieldValuedPoint.class B (Spec (.of K)) hK (target K B hK hZ).obj
    (bertiniFieldPoint K B hK hZ)

/-- Nonemptiness is a conclusion for the actual chosen M9 space. -/
theorem points_nonempty :
    Nonempty (Space.points B (Spec (.of K)) hK (target K B hK hZ).obj) :=
  ⟨bertiniPoint K B hK hZ⟩

end M9Native.LagrangianChosenCoarseFamily
