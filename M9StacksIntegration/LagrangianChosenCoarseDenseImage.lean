module

public import M9StacksIntegration.LagrangianChosenCoarseFamily
public import M9StacksIntegration.AlgebraicSpaceIntegralOfDenseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-! The actual original good parameter open is irreducible and nonempty.
Its native point space therefore supplies the irreducible source for the
chosen coarse map. Density, reducedness and decency remain explicit true
geometric inputs here, produced independently by the moduli-density lane. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
attribute [local instance] Space.pointTopology

namespace M9Native.LagrangianChosenCoarseDenseImage
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth

universe u
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
  (hZ : B.Contains integerBase)

/-- The original canonical good open has a genuine point and is irreducible. -/
theorem original_irreducible : IrreducibleSpace (goodOpen K).toScheme := by
  letI : PreirreducibleSpace (goodOpen K).toScheme :=
    (goodOpen K).ι.isOpenEmbedding.preirreducibleSpace
  exact {
    toPreirreducibleSpace := inferInstance
    toNonempty := ⟨UniversalLagrangianNativeGenus.bertiniGoodPoint K
      (Classical.arbitrary (Spec (.of K)))⟩ }

/-- The native points are those of the same original irreducible open. -/
theorem native_irreducible : IrreducibleSpace
    (Space.points B (Spec (.of K)) hK
      (schemeSpace (LagrangianNativeGenusNineFamily.base K B hK)).obj) := by
  have h : IrreducibleSpace
      ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj
        (LagrangianNativeGenusNineFamily.base K B hK)) := original_irreducible K
  exact (Space.schemePointsHomeomorph B (Spec (.of K)) hK
    (LagrangianNativeGenusNineFamily.base K B hK)).irreducibleSpace_iff.2 h

/-- Actual image density gives irreducibility of the same chosen coarse space. -/
theorem target_irreducible_of_dense
    (hd : DenseRange (Space.pointsMap B (Spec (.of K)) hK
      (schemeSpace (LagrangianNativeGenusNineFamily.base K B hK)).obj
      (LagrangianChosenCoarseFamily.nativeMap K B hK hZ).hom)) :
    IrreducibleSpace (Space.points B (Spec (.of K)) hK
      (LagrangianChosenCoarseFamily.target K B hK hZ).obj) :=
  AlgebraicSpaceIntegralOfDenseImage.irreducible_of_dense_image B (Spec (.of K)) hK
    (LagrangianChosenCoarseFamily.nativeMap K B hK hZ)
    (native_irreducible K B hK) hd

/-- Density together with independently established target properties gives
actual native integrality, without assuming moduli irreducibility. -/
theorem target_integral_of_dense
    (hd : DenseRange (Space.pointsMap B (Spec (.of K)) hK
      (schemeSpace (LagrangianNativeGenusNineFamily.base K B hK)).obj
      (LagrangianChosenCoarseFamily.nativeMap K B hK hZ).hom))
    (hr : Space.HasEtaleLocalProperty B (Spec (.of K)) hK
      (LagrangianChosenCoarseFamily.target K B hK hZ).obj
      (fun Z : Scheme.{u} => IsReduced Z))
    (hdec : Space.IsDecentSpace B (Spec (.of K)) hK
      (LagrangianChosenCoarseFamily.target K B hK hZ).obj) :
    Space.IsIntegralSpace B (Spec (.of K)) hK
      (LagrangianChosenCoarseFamily.target K B hK hZ).obj :=
  AlgebraicSpaceIntegralOfDenseImage.integral_of_dense_irreducible_image
    B (Spec (.of K)) hK (LagrangianChosenCoarseFamily.nativeMap K B hK hZ)
    (native_irreducible K B hK) hd hr hdec

end M9Native.LagrangianChosenCoarseDenseImage
