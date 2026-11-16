module

public import M9StacksIntegration.CurveConstantRank
public import M9StacksIntegration.MukaiBundleTensor
public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerDeterminant
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant

/-!
# Actual kernel, image and quotient of a constant-rank-two three-system

On a reduced locally Noetherian scheme, an actual residue-rank-two map
from the actual free rank-three sheaf to a rank-three bundle has actual
categorical kernel, image and cokernel of ranks one, two and one. The
canonical image sequences are genuinely short exact. The determinant
line of the actual image is the genuine native determinant object; its
proved identification with the second exterior power and native
short-exact-sequence exterior comparison constructs its tensor relation
with the actual quotient, without a supplied determinant relation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundleDeterminant

namespace M9Native.RankTwoSubsystemBundles
universe u
variable {X : Scheme.{u}}

abbrev freeThree (X : Scheme.{u}) : X.Modules :=
  _root_.SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 3))

variable {G : X.Modules} (φ : freeThree X ⟶ G)

def kernelLine : X.Modules := kernel φ
def imageBundle : X.Modules := image φ
def alpha : X.Modules := cokernel φ

/-- The genuine native determinant of the actual rank-two image. -/
def beta : X.Modules := Scheme.Modules.determinant (imageBundle φ)

def kernelSequence : ShortComplex X.Modules :=
  CurveConstantRankSequences.kernelImageSequence φ

def quotientSequence : ShortComplex X.Modules :=
  CurveConstantRankSequences.imageCokernelSequence φ

theorem kernelSequence_shortExact : (kernelSequence φ).ShortExact :=
  CurveConstantRankSequences.kernelImageSequence_shortExact φ

theorem quotientSequence_shortExact : (quotientSequence φ).ShortExact :=
  CurveConstantRankSequences.imageCokernelSequence_shortExact φ

/-- The actual factorization retains the original evaluation map. -/
theorem factorization : factorThruImage φ ≫ image.ι φ = φ := image.fac φ

theorem freeThree_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeThree X) 3 :=
  SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv
    (ULift.{u} (Fin 3)) 3 Equiv.ulift

section Reduced
variable [IsReduced X] [IsLocallyNoetherian X]
  [hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 3]

/-- All three bundles and their ranks follow from actual fibre rank two;
reducedness is retained explicitly. -/
theorem ranks (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernelLine φ) 1 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle φ) 2 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha φ) 1 :=
  CurveConstantRank.ranks φ 3 3 2 freeThree_rank hG hr

theorem kernelLine_rank (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernelLine φ) 1 :=
  (ranks φ hr).1

theorem imageBundle_rank (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle φ) 2 :=
  (ranks φ hr).2.1

theorem alpha_rank (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha φ) 1 :=
  (ranks φ hr).2.2

theorem kernelLine_isInvertible (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (kernelLine φ) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernelLine φ) 1 :=
    kernelLine_rank φ hr
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

theorem alpha_isInvertible (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (alpha φ) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha φ) 1 := alpha_rank φ hr
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

theorem beta_isInvertible (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (beta φ) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle φ) 2 :=
    imageBundle_rank φ hr
  exact Scheme.Modules.isInvertible_determinant (imageBundle φ) 2

/-- The genuine determinant is compared with the actual top exterior power
by the native determinant theorem, rather than by an object declaration. -/
def betaExteriorIso (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    beta φ ≅ Scheme.Modules.exteriorPower (imageBundle φ) (2 : ℤ) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle φ) 2 :=
    imageBundle_rank φ hr
  exact (Scheme.Modules.exteriorPowerIsoDeterminant (imageBundle φ) 2).symm

/-- The actual quotient short exact sequence constructs the determinant
tensor relation. No line or determinant isomorphism is an input. -/
def betaTensorAlphaIso (hr : MukaiSemiIrreducible.EverywhereRank φ 2) :
    tensor (beta φ) (alpha φ) ≅ Scheme.Modules.exteriorPower G (3 : ℤ) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image φ) 2 :=
    imageBundle_rank φ hr
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel φ) 1 := alpha_rank φ hr
  exact tensorIso (betaExteriorIso φ hr)
      (Scheme.Modules.exteriorPowerOneIsoSelf (alpha φ)).symm ≪≫
    Scheme.Modules.exteriorPowerTensorExteriorPowerIso
      (image.ι φ) (cokernel.π φ) (quotientSequence φ).zero
      (quotientSequence_shortExact φ) 2 0

end Reduced
end M9Native.RankTwoSubsystemBundles
