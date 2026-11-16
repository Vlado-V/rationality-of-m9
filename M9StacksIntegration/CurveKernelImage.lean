module

public import M9StacksIntegration.MukaiGeneratedImageRank
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact

/-!
# Actual kernels and images of bundle maps on a regular integral curve

For an arbitrary actual morphism of finite locally free sheaves, its
categorical kernel and image are coherent torsion-free subsheaves of the
original bundles. Native regular-curve geometry makes both locally free.
The kernel-image sequence then splits locally. No map-rank or
cokernel-flatness assumption is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.CurveKernelImage

variable {X : Scheme.{u}} [IsIntegral X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X ≤ 1) {F G : X.Modules} (a : F ⟶ G)
    (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u,u,u} G)

include hreg hdim hF hG

theorem kernel_isFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel a) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let := hF
  let := hG
  let : F.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  let : G.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X G
  let : (kernel a).IsCoherent := _root_.SheafOfModules.kernel_isCoherent a
  let : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  let : (kernel a).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent (kernel a)
  have ht : IsTorsionFree F := (isTorsionFree_iff_isFiniteLocallyFree hreg hdim F).mpr hF
  exact (isTorsionFree_iff_isFiniteLocallyFree hreg hdim (kernel a)).mp
    (MukaiGeneratedImage.isTorsionFree_of_mono (kernel.ι a) ht)

theorem image_isFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image a) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let := hF
  let := hG
  let hFc : F.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  let hGc : G.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X G
  let : (Abelian.image a).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_image hFc hGc a
  let : (image a).IsCoherent := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (Abelian.imageIsoImage a).symm
  let : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  let : (image a).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent (image a)
  have ht : IsTorsionFree G := (isTorsionFree_iff_isFiniteLocallyFree hreg hdim G).mpr hG
  exact (isTorsionFree_iff_isFiniteLocallyFree hreg hdim (image a)).mp
    (MukaiGeneratedImage.isTorsionFree_of_mono (image.ι a) ht)

omit hreg hdim hF hG [IsIntegral X] in
theorem kernel_comp_factorThruImage : kernel.ι a ≫ factorThruImage a = 0 := by
  apply (cancel_mono (image.ι a)).mp
  rw [Category.assoc, image.fac, kernel.condition, zero_comp]

omit hreg hdim hF hG [IsIntegral X] in
def sequence : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι a) (factorThruImage a) (kernel_comp_factorThruImage a)

omit hreg hdim hF hG [IsIntegral X] in
theorem sequence_shortExact : (sequence a).ShortExact := by
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι (factorThruImage a)) (factorThruImage a)
      (kernel.condition (factorThruImage a))
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel (factorThruImage a) }
  let e : S ≅ sequence a := ShortComplex.isoMk (kernelFactorThruImage a)
    (Iso.refl F) (Iso.refl (image a)) (by simp [S, sequence]) (by simp [S, sequence])
  exact ShortComplex.shortExact_of_iso e hS

/-- The ORIGINAL kernel inclusion is locally a split monomorphism.
Its image quotient is derived to be locally free, rather than assumed. -/
theorem sequence_locally_split (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((sequence a).map (Scheme.Modules.restrictFunctor U.ι)).Splitting := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (sequence a).X₃ := by
    change SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image a)
    exact image_isFiniteLocallyFree hreg hdim a hF hG
  exact Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree
    (sequence a) (sequence_shortExact a) x

end M9Native.CurveKernelImage
