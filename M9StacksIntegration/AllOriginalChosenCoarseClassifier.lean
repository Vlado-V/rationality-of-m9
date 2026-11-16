module

public import M9StacksIntegration.RelativeOriginalFamilyCoarseNaturality
public import M9StacksIntegration.AllTestSpecToAffineFamilyValues

/-! The actual chosen native genus coarse space receives a classifier for
ALL original families over ALL original bases. Actual finite-stage values
and their derived algebra-map naturality feed genuine affine normalization
and sheaf extension. No classifier, comparison, or coarseness is an input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Opposite

namespace M9Native.AllOriginalChosenCoarseClassifier
open RelativeOriginalFamilyCoarseValue RelativeOriginalFamilyCoarseNaturality
  M9StacksIntegration.AllTestNativeOriginalSpace
  M9StacksIntegration.AllTestAffineClassifierExtension
  M9StacksIntegration.AllTestSpecToAffineFamilyValues
  M9StacksIntegration.AllTestFamilyPullback

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g)

/-- The SAME chosen coarse space, as an actual full-original algebraic space. -/
abbrev space : M9StandaloneDraft.Space K :=
  originalSpaceOfNative K B hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).property

/-- Actual values for every K-algebra and every original family over its
spectrum, including zero algebras and nonschematic total spaces. -/
def specValues : SpecFamilyValues K g (space B hZ K hK g hg).obj where
  value := fun A _ _ F => valueSpec B hZ K hK g hg A F
  naturality := fun A R _ _ _ _ φ F G r hcart =>
    valueSpec_naturality B hZ K hK g hg A R φ F G r hcart

/-- The actual spectrum data derive honest values on every original affine base. -/
def affineValues : AffineFamilyValues K g (space B hZ K hK g hg).obj :=
  toAffineFamilyValues K (specValues B hZ K hK g hg)

/-- The actual classifier on the literal FULL original family category. -/
def classifier : M9StandaloneDraft.Classifier K g (space B hZ K hK g hg).obj :=
  extend K (affineValues B hZ K hK g hg) (space B hZ K hK g hg).isSheaf

/-- On every literal spectrum the full classifier is exactly the derived
finite-stage chosen value. No equality or compatibility is supplied. -/
theorem classifier_value_spec (A : Type u) [CommRing A] [Algebra K A]
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) :
    (classifier B hZ K hK g hg).value
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) F =
      valueSpec B hZ K hK g hg A F := by
  calc
    (classifier B hZ K hK g hg).value (specOverK K A) F =
        (affineValues B hZ K hK g hg).value (specOverK K A) inferInstance F :=
      extend_value_affine K (affineValues B hZ K hK g hg)
        (space B hZ K hK g hg).isSheaf (specOverK K A) inferInstance F
    _ = valueSpec B hZ K hK g hg A F :=
      toAffine_value_spec K (specValues B hZ K hK g hg) A F

/-- The exact genuine affine pullback formula, with the canonical K-algebra
and original coefficient compatibility derived by actual normalization. -/
theorem classifier_value_affine_formula
    (T : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left)
    (F : M9StandaloneDraft.Family K T g) :
    letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
    (classifier B hZ K hK g hg).value T F =
      (space B hZ K hK g hg).obj.map (canonicalSpecIso K T hT).inv.op
        (valueSpec B hZ K hK g hg Γ(T.left, ⊤)
          (pullbackFamily K F (canonicalSpecIso K T hT).hom)) := by
  letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
  exact (extend_value_affine K (affineValues B hZ K hK g hg)
    (space B hZ K hK g hg).isSheaf T hT F).trans
      (toAffine_value K (specValues B hZ K hK g hg) T hT F)

end M9Native.AllOriginalChosenCoarseClassifier
