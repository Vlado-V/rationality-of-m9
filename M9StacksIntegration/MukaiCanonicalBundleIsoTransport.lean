module

public import M9StacksIntegration.MukaiCurveIsoPullback
public import M9StacksIntegration.MukaiCanonicalBundleFromNet
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale

/-!
# The canonical Mukai bundle property under an actual curve isomorphism

An isomorphism over the original field pulls the actual canonical line
back to the original canonical line, through the native relative
differential map. Together with the scalar-preserving complete-section
comparison, this transports all five parts of the canonical generated
semi-irreducible bundle property. No polarization, section-space
identification, or semi-irreducibility compatibility is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiCanonicalBundleIsoTransport

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (e : X ≅ Y) (he : e.hom ≫ g = f)

/-- The actual étale differential map is invertible for the given
scheme isomorphism and its original over-field triangle. -/
def differentialsPullbackIso :
    (Scheme.Modules.pullback e.hom).obj (Scheme.Hom.relativeDifferentials g) ≅
      Scheme.Hom.relativeDifferentials f := by
  let hc : e.hom ≫ g = f ≫ 𝟙 (Spec (.of k)) :=
    he.trans (Category.comp_id f).symm
  let d := Scheme.Hom.relativeDifferentialsMap e.hom g f (𝟙 _) hc
  letI : IsIso d :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_etale e.hom g f (𝟙 _) hc
  exact asIso d

variable [IsProper f] [IsCurve k f] [Smooth f]
  [IsProper g] [IsCurve k g] [Smooth g]

/-- Pullback of the genuine canonical sheaf, obtained from the native
canonical/cotangent comparisons and the actual differential map. -/
def canonicalPullbackIso :
    (Scheme.Modules.pullback e.hom).obj (Stacks.Duality.dualizingSheafOverField g) ≅
      Stacks.Duality.dualizingSheafOverField f :=
  (Scheme.Modules.pullback e.hom).mapIso
      (SmoothCurveCanonicalDifferentials.canonicalDifferentialsIso g) ≪≫
    differentialsPullbackIso k f g e he ≪≫
      (SmoothCurveCanonicalDifferentials.canonicalDifferentialsIso f).symm

/-- The top exterior power of the actual pulled-back bundle is the
canonical sheaf on the source curve. -/
def topExteriorCanonicalPullbackIso (E : Y.Modules)
    (d : Scheme.Modules.exteriorPower E 3 ≅ Stacks.Duality.dualizingSheafOverField g) :
    Scheme.Modules.exteriorPower ((Scheme.Modules.pullback e.hom).obj E) 3 ≅
      Stacks.Duality.dualizingSheafOverField f :=
  (Scheme.Modules.exteriorPowerPullbackIso e.hom E 3).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso d ≪≫
      canonicalPullbackIso k f g e he

include he in
/-- All five original canonical Mukai properties transfer along the
actual isomorphism over the same field, including COMPLETE
semi-irreducibility for every independent section triple. -/
theorem isCanonicalGeneratedSemi_pullback (E : Y.Modules)
    (hE : MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi g E) :
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f
      ((Scheme.Modules.pullback e.hom).obj E) := by
  obtain ⟨hr, h6, ⟨d⟩, hgen, hsemi⟩ := hE
  let := hr
  refine ⟨isFiniteLocallyFreeOfRank_pullback e.hom E 3, ?_, ?_, ?_, ?_⟩
  · exact (MukaiCurveIsoPullback.finrank_h0_pullback k f g e he E).trans h6
  · exact ⟨topExteriorCanonicalPullbackIso k f g e he E d⟩
  · exact MukaiCurveIsoPullback.globallyGenerated_pullback e E hgen
  · exact MukaiCurveIsoPullback.completeSemiIrreducible_pullback k f g e he E 3 hsemi

end M9Native.MukaiCanonicalBundleIsoTransport
