module

public import M9StacksIntegration.BoundedPencilGraphPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomialFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-! Fixed graph-polynomial cover spaces over a genuine polarized family.
The space is the original native graph-Hilbert subfunctor of relative Hom.
Native Tag 0DPR proves finite presentation, including quasi-compactness,
from the actual proper-flat-finitely-presented source and actual ample
polarizations. The construction does not assume a Hurwitz space or its
dimension. Supplying the bounded genus-nine curve base is a separate step. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
universe u
namespace M9Native.FixedDegreeCoverSpace
open AlgebraicGeometry.Space BoundedPencilGraphPolynomial
variable {B : BigFppfSite.{u}}
variable {Z X Q : (BigFppfOver B integerBase (B.contains_integerBase))ᵒᵖ ⥤ Type u}
variable {z : Z ⟶ Q} {x : X ⟶ Q}
variable (hZ : IsAlgebraicSpace B integerBase (B.contains_integerBase) Z)
  (hX : IsAlgebraicSpace B integerBase (B.contains_integerBase) X)
  (hQ : IsAlgebraicSpace B integerBase (B.contains_integerBase) Q)
  (hsep : Space.IsSeparated B integerBase (B.contains_integerBase) x)
  (hxfp : Space.IsFinitePresentation B integerBase (B.contains_integerBase) x)
  (hfp : Space.IsFinitePresentation B integerBase (B.contains_integerBase) z)
  (hflat : Space.IsFlat B integerBase (B.contains_integerBase) z)
  (hproper : Space.IsProper B integerBase (B.contains_integerBase) z)
variable (N : Space.Modules.{u, u} B integerBase (B.contains_integerBase) Z hZ)
  [Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase (B.contains_integerBase) Z)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B integerBase (B.contains_integerBase) Z hZ).O)).property N]
variable (L : Space.Modules.{u, u} B integerBase (B.contains_integerBase) X hX)
  [Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase (B.contains_integerBase) X)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B integerBase (B.contains_integerBase) X hX).O)).property L]

abbrev coverLocus (d : ℕ) :=
  relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper
    (graphAmbientTensor z x hZ hX hQ N L) (graphPolynomial d)

def coverProjection (d : ℕ) :
    (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L d).toFunctor ⟶ Q :=
  (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L d).ι ≫
    relativeHomProjection B integerBase (B.contains_integerBase) Z X Q z x hZ hX hQ

variable (hN : Space.IsRelativelyAmple B integerBase (B.contains_integerBase)
    (ObjectProperty.homMk z : (⟨Z, hZ⟩ : AlgebraicSpaces B integerBase (B.contains_integerBase)) ⟶ ⟨Q, hQ⟩) N)
  (hL : Space.IsRelativelyAmple B integerBase (B.contains_integerBase)
    (ObjectProperty.homMk x : (⟨X, hX⟩ : AlgebraicSpaces B integerBase (B.contains_integerBase)) ⟶ ⟨Q, hQ⟩) L)

include hN hL in
theorem coverLocus_properties (d : ℕ) :
    IsAlgebraicSpace B integerBase (B.contains_integerBase)
      (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L d).toFunctor ∧
    Space.IsSeparated B integerBase (B.contains_integerBase)
      (coverProjection hZ hX hQ hsep hxfp hfp hflat hproper N L d) ∧
    Space.IsFinitePresentation B integerBase (B.contains_integerBase)
      (coverProjection hZ hX hQ hsep hxfp hfp hflat hproper N L d) :=
  isSeparated_and_isFinitePresentation_relativeHomHilbertPolynomial
    hZ hX hQ hsep hxfp hfp hflat hproper N L hN hL
    (p := graphNumericalPolynomial d) (graphNumericalPolynomial_eval d)

include hN hL in
theorem coverProjection_isQuasiCompact (d : ℕ) :
    Space.IsQuasiCompact B integerBase (B.contains_integerBase)
      (coverProjection hZ hX hQ hsep hxfp hfp hflat hproper N L d) :=
  (coverLocus_properties hZ hX hQ hsep hxfp hfp hflat hproper N L hN hL d).2.2.2.1

include hN hL in
theorem coverProjection_isFiniteType (d : ℕ) :
    Space.IsFiniteType B integerBase (B.contains_integerBase)
      (coverProjection hZ hX hQ hsep hxfp hfp hflat hproper N L d) :=
  Space.isFiniteType_of_isFinitePresentation B integerBase (B.contains_integerBase)
    (coverLocus_properties hZ hX hQ hsep hxfp hfp hflat hproper N L hN hL d).2.2

end M9Native.FixedDegreeCoverSpace
end
