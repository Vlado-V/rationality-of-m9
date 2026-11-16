module

public import M9StacksIntegration.CurveBundleMonoDegreeIso

/-!
# Actual degree comparison for a rank-two image inclusion

The original monomorphism has its original coherent categorical
cokernel, supported in dimension zero. Actual degree additivity makes
the target degree equal to the source degree plus its native H0
dimension, proving monotonicity. A reverse degree inequality therefore
forces equality and the checked original-map isomorphism theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiImageComparison

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Native degree is monotone for the actual rank-two monomorphism,
using its actual zero-dimensional cokernel rather than a length premise. -/
theorem curveDegree_le_of_mono
    (hdim : topologicalKrullDim X ≤ 1) {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 2]
    (j : F ⟶ G) [Mono j] :
    curveDegree k f hdim F 2 ≤ curveDegree k f hdim G 2 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let hF : F.IsCoherent := CurveBundleMonoDegreeIso.bundle_isCoherent f F 2
  let hG : G.IsCoherent := CurveBundleMonoDegreeIso.bundle_isCoherent f G 2
  let : (cokernel j).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel hF hG j
  let : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hC := CurveBundleMonoDegreeIso.cokernel_support_dim_le_zero f hdim 2 j
  have hS : (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact :=
    { exact := ShortComplex.exact_cokernel j }
  have hd := MukaiGeneratedImage.degree_eq_add_quotient_h0 f hdim hS hC
  change curveDegree k f hdim G 2 = curveDegree k f hdim F 2 +
    Module.finrank k (cohomologyOverField k f (cokernel j) 0) at hd
  rw [hd]
  omega

/-- An opposite degree inequality forces the original rank-two
monomorphism to be an actual isomorphism. -/
theorem isIso_of_target_degree_le_source
    (hdim : topologicalKrullDim X ≤ 1) {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 2]
    (j : F ⟶ G) [Mono j]
    (hd : curveDegree k f hdim G 2 ≤ curveDegree k f hdim F 2) : IsIso j :=
  CurveBundleMonoDegreeIso.isIso_of_curveDegree_eq f hdim 2 j
    (le_antisymm (curveDegree_le_of_mono f hdim j) hd)

end M9Native.MukaiImageComparison
