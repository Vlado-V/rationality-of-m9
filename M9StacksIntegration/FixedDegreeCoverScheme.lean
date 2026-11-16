module

public import M9StacksIntegration.FixedDegreeCoverSpace

/-!
# Actual fixed graph-polynomial cover schemes over affine bases

The genuine native affine representability theorem gives a scheme with a
literal isomorphism to the fixed graph-Hilbert Hom locus and an original
quasi-compact finite-type projection. Its identity family is the actual
universal relative morphism. No parameter space or universal evaluation
is postulated.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace M9Native.FixedDegreeCoverScheme

open BoundedPencilGraphPolynomial FixedDegreeCoverSpace

variable {B : BigFppfSite.{u}}

variable (T : BigFppfOver B integerBase (B.contains_integerBase)) [IsAffine (((BigFppfOver.toScheme B integerBase (B.contains_integerBase))).obj T)]
  {Z X : (BigFppfOver B integerBase (B.contains_integerBase))ᵒᵖ ⥤ Type u}
  {z : Z ⟶ yoneda.obj T} {x : X ⟶ yoneda.obj T}
  (hZ : IsAlgebraicSpace B integerBase (B.contains_integerBase) Z)
  (hX : IsAlgebraicSpace B integerBase (B.contains_integerBase) X)
  (hQ : IsAlgebraicSpace B integerBase (B.contains_integerBase) (yoneda.obj T))
  (hsep : Space.IsSeparated B integerBase (B.contains_integerBase) x)
  (hxfp : Space.IsFinitePresentation B integerBase (B.contains_integerBase) x)
  (hfp : Space.IsFinitePresentation B integerBase (B.contains_integerBase) z)
  (hflat : Space.IsFlat B integerBase (B.contains_integerBase) z)
  (hproper : Space.IsProper B integerBase (B.contains_integerBase) z)
  (N : Space.Modules.{u,u} B integerBase (B.contains_integerBase) Z hZ)
  [Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase (B.contains_integerBase) Z)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B integerBase (B.contains_integerBase) Z hZ).O)).property N]
  (L : Space.Modules.{u,u} B integerBase (B.contains_integerBase) X hX)
  [Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase (B.contains_integerBase) X)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B integerBase (B.contains_integerBase) X hX).O)).property L]
  (hN : Space.IsRelativelyAmple B integerBase (B.contains_integerBase)
    (ObjectProperty.homMk z : (⟨Z,hZ⟩ : AlgebraicSpaces B integerBase (B.contains_integerBase)) ⟶
      ⟨yoneda.obj T,hQ⟩) N)
  (hL : Space.IsRelativelyAmple B integerBase (B.contains_integerBase)
    (ObjectProperty.homMk x : (⟨X,hX⟩ : AlgebraicSpaces B integerBase (B.contains_integerBase)) ⟶
      ⟨yoneda.obj T,hQ⟩) L)

include hN hL in
/-- The actual representing scheme and its actual finite-type projection,
for one of the genuine graph polynomials `(48+d)m-8`. -/
theorem exists_coverScheme (d : ℕ) :
    ∃ (Y : BigFppfOver B integerBase (B.contains_integerBase))
      (a : yoneda.obj Y ⟶
        (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L d).toFunctor)
      (q : Y ⟶ T), IsIso a ∧
      a ≫ coverProjection hZ hX hQ hsep hxfp hfp hflat hproper N L d = yoneda.map q ∧
      QuasiCompactFiniteType (((BigFppfOver.toScheme B integerBase (B.contains_integerBase))).map q) := by
  obtain ⟨Y,a,q,hpb,hq⟩ :=
    exists_isPullback_relativeHomHilbertPolynomial_of_isAffine T
      hZ hX hQ hsep hxfp hfp hflat hproper hN.1 hL.1
      (graphAmbientTensor z x hZ hX hQ N L)
      (isRelativelyAmple_graphAmbientTensor N L hN hL)
      (p := graphNumericalPolynomial d) (graphNumericalPolynomial_eval d)
  refine ⟨Y,a,q,hpb.isIso_fst_of_isIso inferInstance,?_,hq⟩
  exact hpb.w.trans (Category.comp_id _)

include hN hL in
/-- Each of the five positive degrees has an actual representing scheme.
The finite index comes from genuine native curve-map degree positivity. -/
theorem exists_five_coverSchemes :
    ∃ (Y : Fin 5 → BigFppfOver B integerBase (B.contains_integerBase))
      (a : ∀ i, yoneda.obj (Y i) ⟶
        (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L (degreeIndex i)).toFunctor)
      (q : ∀ i, Y i ⟶ T),
      (∀ i, IsIso (a i)) ∧
      (∀ i, a i ≫ coverProjection hZ hX hQ hsep hxfp hfp hflat hproper N L
        (degreeIndex i) = yoneda.map (q i)) ∧
      (∀ i, QuasiCompactFiniteType (((BigFppfOver.toScheme B integerBase (B.contains_integerBase))).map (q i))) := by
  choose Y a q ha hq hft using fun i : Fin 5 =>
    exists_coverScheme T hZ hX hQ hsep hxfp hfp hflat hproper N L hN hL (degreeIndex i)
  exact ⟨Y,a,q,ha,hq,hft⟩

/-- The actual universal relative morphism is the image of the literal
representing isomorphism under native relative-Hom representability. -/
def universalRelativeMorphism {Y : BigFppfOver B integerBase (B.contains_integerBase)} (d : ℕ)
    (a : yoneda.obj Y ⟶
      (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L d).toFunctor) :
    RelativeMorphism B integerBase (B.contains_integerBase) Z X (yoneda.obj T) z x (yoneda.obj Y) :=
  relativeHomEquiv B integerBase (B.contains_integerBase) Z X (yoneda.obj T) z x hZ hX hQ
    (yoneda.obj Y) (isAlgebraicSpace_yoneda B integerBase (B.contains_integerBase) Y)
    (a ≫ (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L d).ι)

/-- The universal cover lies over the SAME original representing
scheme projection, as derived from its literal Hom projection triangle. -/
theorem universalRelativeMorphism_base {Y : BigFppfOver B integerBase (B.contains_integerBase)}
    (d : ℕ) (a : yoneda.obj Y ⟶
      (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L d).toFunctor)
    (q : Y ⟶ T)
    (ha : a ≫ coverProjection hZ hX hQ hsep hxfp hfp hflat hproper N L d = yoneda.map q) :
    (universalRelativeMorphism T hZ hX hQ hsep hxfp hfp hflat hproper N L d a).base =
      yoneda.map q := by
  change (a ≫ (coverLocus hZ hX hQ hsep hxfp hfp hflat hproper N L d).ι) ≫
      relativeHomProjection B integerBase (B.contains_integerBase) Z X (yoneda.obj T)
        z x hZ hX hQ = yoneda.map q
  exact (Category.assoc _ _ _).trans ha

end M9Native.FixedDegreeCoverScheme
end
