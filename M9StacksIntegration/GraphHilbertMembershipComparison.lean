module

public import M9StacksIntegration.GraphHilbertResidueFibreComparison
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomial

/-! The original all-residue-point, all-integer Euler criterion for the
actual native relative-Hom graph Hilbert-polynomial locus. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
universe u

namespace M9Native.GraphHilbertMembershipComparison
open AlgebraicGeometry.Space GraphHilbertEulerComparison GraphHilbertResidueFibreComparison

section HilbertModule
variable {B₀ : BigFppfSite.{u}} {S₀ : Scheme.{u}} {hS₀ : B₀.Contains S₀}
  {X₀ Y₀ : AlgebraicSpaces B₀ S₀ hS₀} (f₀ : X₀ ⟶ Y₀)
  (hf₀ : IsFinitePresentation B₀ S₀ hS₀ f₀.hom)
  {T₀ : BigFppfOver B₀ S₀ hS₀} (y₀ : HilbertFamilyOver f₀ T₀)

/-- The actual Hilbert coherent module, at variable family arguments,
is the direct image of its support's structure sheaf. -/
def hilbertCohObjectModuleIso :
    (hilbertCohObject f₀ hf₀ y₀).F ≅
      pushforwardStructureSheaf B₀ S₀ hS₀
        (schemeBaseChangeSpace f₀ (CostructuredArrow.mk y₀.toBase))
        ⟨y₀.family.Z, y₀.family.closed⟩ :=
  hilbertFamilyQuotientIso f₀ hf₀ (CostructuredArrow.mk y₀.toBase) y₀.family

end HilbertModule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
  (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
  (hQ : IsAlgebraicSpace B S hS Q) (hsep : IsSeparated B S hS x)
  (hxfp : IsFinitePresentation B S hS x) (hfp : IsFinitePresentation B S hS z)
  (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
  (hz : yoneda.relativelyRepresentable z) {T : BigFppfOver B S hS}
  (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T))

/-- The actual coherent object classified by the actual native graph. -/
abbrev graphCohObject :=
  hilbertCohObject (graphAmbientMap B S hS z x hZ hX hQ)
    (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)
    (actualGraphFamily hZ hX hQ hsep hfp hflat hproper p)

/-- Its actual closed graph support. -/
def graphClosedSupport : ClosedSubspaces B S hS
    (schemeBaseChangeSpace (graphAmbientMap B S hS z x hZ hX hQ)
      (CostructuredArrow.mk p.base)).1 :=
  ⟨(actualGraphFamily hZ hX hQ hsep hfp hflat hproper p).family.Z,
    (actualGraphFamily hZ hX hQ hsep hfp hflat hproper p).family.closed⟩

/-- The actual graph module is the direct image of the actual support's
structure sheaf, by the Hilbert-to-Quot construction. -/
def graphModuleIso :
    (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper p).F ≅
      pushforwardStructureSheaf B S hS _
        (graphClosedSupport hZ hX hQ hsep hfp hflat hproper p) :=
  hilbertCohObjectModuleIso (graphAmbientMap B S hS z x hZ hX hQ)
    (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)
    (actualGraphFamily hZ hX hQ hsep hfp hflat hproper p)

/-- The original residue fibre of the actual source of the graph. -/
abbrev graphFibre (t : (BigFppfOver.toScheme B S hS).obj T) :=
  originalFibre (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper p)
    (graphSourceScheme hz p) (hz.snd p.base) t

/-- Its original projection to its actual residue field. -/
abbrev graphFibreProjection (t : (BigFppfOver.toScheme B S hS).obj T) :=
  originalFibreProjection (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper p)
    (graphSourceScheme hz p) (hz.snd p.base) t

variable (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS Z hZ)
  (L : AlgebraicGeometry.Space.Modules.{u, u} B S hS X hX)
  [hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z hZ).O).property N]
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O).property L]

instance graphCohAmbientTensor_isInvertible :
    Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS
        (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
          (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)).toCoherentSituation.X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS
          (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
            (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)).toCoherentSituation.X.1
          (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
            (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)).toCoherentSituation.X.2).O).property
      (graphAmbientTensor z x hZ hX hQ N L) :=
  isInvertible_graphAmbientTensor N L

/-- The actual map from the original residue fibre to the graph ambient. -/
abbrev graphFibreAmbientMap (t : (BigFppfOver.toScheme B S hS).obj T) :=
  originalFibreAmbientMap
    (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper p)
    (graphClosedSupport hZ hX hQ hsep hfp hflat hproper p)
    (graphSourceScheme hz p) (hz.snd p.base)
    (graphSupportIso hZ hX hQ hsep hfp hflat hproper hz p)
    (graphSupportIso_projection hZ hX hQ hsep hfp hflat hproper hz p) t

/-- The literal original restriction of the actual graph polarization. -/
abbrev graphFibreLine (t : (BigFppfOver.toScheme B S hS).obj T) :=
  originalFibreLine
    (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper p)
    (graphClosedSupport hZ hX hQ hsep hfp hflat hproper p)
    (graphSourceScheme hz p) (hz.snd p.base)
    (graphSupportIso hZ hX hQ hsep hfp hflat hproper hz p)
    (graphSupportIso_projection hZ hX hQ hsep hfp hflat hproper hz p) t
    (graphAmbientTensor z x hZ hX hQ N L)

/-- On each original residue fibre, the restricted graph line is the
tensor product of the actual source and target line readings. -/
def graphFibrePolarizationTensorIso (t : (BigFppfOver.toScheme B S hS).obj T) :
    graphFibreLine hZ hX hQ hsep hxfp hfp hflat hproper hz p N L t ≅
      Stacks.RelativeVeryAmple.tensorModules _
        (baseChangeModule B S hS (X := ⟨Z, hZ⟩) N
          (graphFibre hZ hX hQ hsep hxfp hfp hflat hproper hz p t)
          ((graphFibreAmbientMap hZ hX hQ hsep hxfp hfp hflat hproper hz p t).hom ≫
            pullback.fst z x))
        (baseChangeModule B S hS (X := ⟨X, hX⟩) L
          (graphFibre hZ hX hQ hsep hxfp hfp hflat hproper hz p t)
          ((graphFibreAmbientMap hZ hX hQ hsep hxfp hfp hflat hproper hz p t).hom ≫
            pullback.snd z x)) :=
  baseChangeModuleGraphAmbientTensorIso N L
    (graphFibre hZ hX hQ hsep hxfp hfp hflat hproper hz p t)
    (graphFibreAmbientMap hZ hX hQ hsep hxfp hfp hflat hproper hz p t).hom

/-- All integer powers of the actual original restricted graph line. -/
abbrev graphFibreLinePower (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℤ) :=
  originalFibreLinePower
    (hL := graphCohAmbientTensor_isInvertible hZ hX hQ hxfp hfp N L)
    (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper p)
    (graphClosedSupport hZ hX hQ hsep hfp hflat hproper p)
    (graphSourceScheme hz p) (hz.snd p.base)
    (graphSupportIso hZ hX hQ hsep hfp hflat hproper hz p)
    (graphSupportIso_projection hZ hX hQ hsep hfp hflat hproper hz p) t
    (graphAmbientTensor z x hZ hX hQ N L) n

/-- The actual native graph Hilbert condition is exactly the original
scheme graph-line Euler condition, at every point and every integer. -/
theorem graph_hasHilbertPolynomial_iff_originalEuler (P : ℤ → ℤ) :
    @CoherentObject.HasHilbertPolynomial B S hS
      (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)).toCoherentSituation
      (graphAmbientTensor z x hZ hX hQ N L)
      (graphCohAmbientTensor_isInvertible hZ hX hQ hxfp hfp N L) P
      (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper p) ↔
    ∀ (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℤ), P n =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        (Module.finrank (((BigFppfOver.toScheme B S hS).obj T).residueField t)
          (cohomologyOverField (((BigFppfOver.toScheme B S hS).obj T).residueField t)
            ((BigFppfOver.toScheme B S hS).map
              (graphFibreProjection hZ hX hQ hsep hxfp hfp hflat hproper hz p t))
            (graphFibreLinePower hZ hX hQ hsep hxfp hfp hflat hproper hz p N L t n) i) : ℤ) :=
  hasHilbertPolynomial_iff_originalFibreEuler
    (hL := graphCohAmbientTensor_isInvertible hZ hX hQ hxfp hfp N L)
    (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper p)
    (graphClosedSupport hZ hX hQ hsep hfp hflat hproper p)
    (graphSourceScheme hz p) (hz.snd p.base)
    (graphSupportIso hZ hX hQ hsep hfp hflat hproper hz p)
    (graphSupportIso_projection hZ hX hQ hsep hfp hflat hproper hz p)
    (graphAmbientTensor z x hZ hX hQ N L)
    (graphModuleIso hZ hX hQ hsep hxfp hfp hflat hproper p) P

/-- Membership in the actual native relative-Hom Hilbert-polynomial
locus is the original scheme Euler condition on the actual graph
fibres, for all residue points and all integer twists. -/
theorem mem_relativeHomHilbertPolynomial_iff_originalEuler
    (P : ℤ → ℤ) (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    s ∈ (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper
      (graphAmbientTensor z x hZ hX hQ N L) P).obj (op T) ↔
    ∀ (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℤ), P n =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        (Module.finrank (((BigFppfOver.toScheme B S hS).obj T).residueField t)
          (cohomologyOverField (((BigFppfOver.toScheme B S hS).obj T).residueField t)
            ((BigFppfOver.toScheme B S hS).map
              (graphFibreProjection hZ hX hQ hsep hxfp hfp hflat hproper hz
                (relativeHomSections B S hS Z X Q z x hZ hX hQ T s) t))
            (graphFibreLinePower hZ hX hQ hsep hxfp hfp hflat hproper hz
              (relativeHomSections B S hS Z X Q z x hZ hX hQ T s) N L t n) i) : ℤ) := by
  rw [mem_relativeHomHilbertPolynomial_iff]
  change @CoherentObject.HasHilbertPolynomial B S hS
    (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
      (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)).toCoherentSituation
    (graphAmbientTensor z x hZ hX hQ N L)
    (graphCohAmbientTensor_isInvertible hZ hX hQ hxfp hfp N L) P
    (graphCohObject hZ hX hQ hsep hxfp hfp hflat hproper
      (relativeHomSections B S hS Z X Q z x hZ hX hQ T s)) ↔ _
  exact graph_hasHilbertPolynomial_iff_originalEuler hZ hX hQ hsep hxfp hfp hflat hproper hz
    (relativeHomSections B S hS Z X Q z x hZ hX hQ T s) N L P

end M9Native.GraphHilbertMembershipComparison
