module

public import M9StacksIntegration.MukaiThreeGeneratorRecognition

/-!
# The original determinant-kernel sequence of three generators

The actual kernel of an epimorphism from the literal free-three sheaf
to a rank-two bundle is the dual of its actual determinant line. The
comparison is derived from the native short-exact determinant theorem.
No complete section basis, cohomology count or degree is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
universe u

namespace M9Native.MukaiRankTwoGeneratorSequence

variable {X : Scheme.{u}} (F β : X.Modules)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
  (q : netFree X ⟶ F) [Epi q] (hdet : topExterior F 2 ≅ β)

/-- The genuine categorical kernel is the dual determinant line. -/
def kernelDualDeterminantIso : kernel q ≅ dualSheaf β := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel q) 1 :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
      q inferInstance 3 2 (netFree_rank X) inferInstance
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  let hprod : tensor (kernel q) β ≅ structureModule X :=
    tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf (kernel q)).symm hdet.symm ≪≫
      Scheme.Modules.exteriorPowerTensorExteriorPowerIso
        (kernel.ι q) q (kernel.condition q) hS 1 1 ≪≫
      freeTopExteriorIso 3 (netFree X) (Iso.refl _)
  exact tensorInverseNativeIso β (kernel q)
    (Stacks.SheafOfModules.Invertible.tensorProductBraiding
      X.presheaf X.ringCatSheaf.2 β (kernel q) ≪≫ hprod)

include hdet in
/-- The literal original epimorphism admits the actual dual-determinant
kernel sequence, without a supplied kernel isomorphism or exactness. -/
theorem exists_dualDeterminantSequence :
    ∃ (i : dualSheaf β ⟶ netFree X) (w : i ≫ q = 0),
      (ShortComplex.mk i q w).ShortExact := by
  let e := kernelDualDeterminantIso F β q hdet
  let i : dualSheaf β ⟶ netFree X := e.inv ≫ kernel.ι q
  have w : i ≫ q = 0 := by simp only [i, Category.assoc, kernel.condition, comp_zero]
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  let eS : S ≅ ShortComplex.mk i q w :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)
      (by simp [S,i]) (by simp [S])
  exact ⟨i,w,ShortComplex.shortExact_of_iso eS hS⟩

end M9Native.MukaiRankTwoGeneratorSequence
