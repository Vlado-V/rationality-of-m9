module

public import StacksFrontier.AlgebraicGeometry.Curves.StableLocus.StableCurveLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree

/-!
# The genuine fixed-degree open of a polarized proper flat family

The degree function is the difference of the two actual fibre Euler
characteristics. Proper flat cohomology proves local constancy. Its value
at every original field-valued point is the original invertible curve
degree, using the actual pulled module and original structural field map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace M9Native.PolarizedCurveDegreeOpen

variable {X T : Scheme.{u}} (p : X ⟶ T)
  [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
  (N : X.Modules)
  [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]

/-- The same actual invertible module in the native Stacks spelling. -/
theorem stacksInvertible : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    X.presheaf _ N).mpr hN

/-- The literal Euler difference on original residue fibres. -/
def degreeFunction (t : T) : ℤ :=
  fibreEulerCharacteristic p N t -
    fibreEulerCharacteristic p (SheafOfModules.unit X.ringCatSheaf) t

include hN in
/-- Local constancy is derived from actual proper flat cohomology. -/
theorem isLocallyConstant_degreeFunction : IsLocallyConstant (degreeFunction p N) := by
  have hfp : FinitePresentation p := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨hNfp, hNflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible p N (stacksInvertible N)
  obtain ⟨hOfp, hOflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible p
    (SheafOfModules.unit X.ringCatSheaf) (Stacks.SheafOfModules.isInvertible_unit _ _)
  exact (isLocallyConstant_fibreEulerCharacteristic p hfp N hNfp hNflat).sub
    (isLocallyConstant_fibreEulerCharacteristic p hfp _ hOfp hOflat)

/-- The actual open and closed locus of the prescribed invertible degree. -/
def degreeOpen (d : ℤ) : T.Opens :=
  ⟨degreeFunction p N ⁻¹' {d}, (isLocallyConstant_degreeFunction p N).isOpen_fiber d⟩

theorem degreeOpen_isClosed (d : ℤ) : IsClosed (degreeOpen p N d : Set T) :=
  (isLocallyConstant_degreeFunction p N).isClosed_fiber d

include hN in
/-- The original fibre Euler characteristic is unchanged after passing
to the SAME fibre at any original field-valued point. -/
theorem fieldEuler_eq {K : Type u} [Field K] {V : Scheme.{u}}
    {y : Spec (.of K) ⟶ T} {q : V ⟶ X} {f : V ⟶ Spec (.of K)}
    (sq : IsPullback q f p y) :
    fibreEulerCharacteristic p N (y (IsLocalRing.closedPoint K)) =
      eulerSum K f ((Scheme.Modules.pullback q).obj N) := by
  have hfp : FinitePresentation p := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨hNfp, hNflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible p N (stacksInvertible N)
  rw [fibreEulerCharacteristic_eq_chiDerivedFibre p hfp N hNfp hNflat,
    chiDerivedFibre_eq_eulerSum p hfp N hNfp hNflat K y q f sq (IsLocalRing.closedPoint K)]

include hN in
/-- The degree function is the original native invertible curve degree,
without a field identification or a supplied degree equality. -/
theorem fieldDegree_eq {K : Type u} [Field K] {V : Scheme.{u}}
    {y : Spec (.of K) ⟶ T} {q : V ⟶ X} {f : V ⟶ Spec (.of K)}
    [IsProper f] (hdim : topologicalKrullDim V ≤ 1) (sq : IsPullback q f p y) :
    degreeFunction p N (y (IsLocalRing.closedPoint K)) =
      invertibleCurveDegree K f hdim ((Scheme.Modules.pullback q).obj N) := by
  rw [degreeFunction, fieldEuler_eq p N sq,
    fibreEulerCharacteristic_unit_eq_eulerSum p sq]
  rfl

/-- Membership in the fixed-degree open is equivalent to the genuine
original degree on every field-valued fibre. -/
theorem mem_degreeOpen_iff {K : Type u} [Field K] {V : Scheme.{u}}
    {y : Spec (.of K) ⟶ T} {q : V ⟶ X} {f : V ⟶ Spec (.of K)}
    [IsProper f] (hdim : topologicalKrullDim V ≤ 1) (sq : IsPullback q f p y) (d : ℤ) :
    y (IsLocalRing.closedPoint K) ∈ degreeOpen p N d ↔
      invertibleCurveDegree K f hdim ((Scheme.Modules.pullback q).obj N) = d := by
  change degreeFunction p N (y (IsLocalRing.closedPoint K)) = d ↔ _
  rw [fieldDegree_eq p N hdim sq]

/-- Every actual degree-d original curve lifts to the genuine degree-d
open, preserving both maps of its original cartesian fibre square. -/
theorem exists_lift_of_degree {K : Type u} [Field K] {V : Scheme.{u}}
    {y : Spec (.of K) ⟶ T} {q : V ⟶ X} {f : V ⟶ Spec (.of K)}
    [IsProper f] (hdim : topologicalKrullDim V ≤ 1) (sq : IsPullback q f p y) (d : ℤ)
    (hd : invertibleCurveDegree K f hdim ((Scheme.Modules.pullback q).obj N) = d) :
    ∃ (y' : Spec (.of K) ⟶ degreeOpen p N d)
      (q' : V ⟶ p ⁻¹ᵁ degreeOpen p N d),
      y' ≫ (degreeOpen p N d).ι = y ∧
        q' ≫ (p ⁻¹ᵁ degreeOpen p N d).ι = q ∧
          IsPullback q' f (p ∣_ degreeOpen p N d) y' :=
  exists_isPullback_restrict_of_mem p (degreeOpen p N d) sq
    ((mem_degreeOpen_iff p N hdim sq d).mpr hd)

/-- The restricted family carries the literal restricted original line,
and that line has the prescribed degree on EVERY original field fibre. -/
theorem restricted_fieldDegree {K : Type u} [Field K] {V : Scheme.{u}} (d : ℤ)
    {y : Spec (.of K) ⟶ degreeOpen p N d}
    {q : V ⟶ p ⁻¹ᵁ degreeOpen p N d} {f : V ⟶ Spec (.of K)}
    [IsProper f] (hdim : topologicalKrullDim V ≤ 1)
    (sq : IsPullback q f (p ∣_ degreeOpen p N d) y) :
    invertibleCurveDegree K f hdim ((Scheme.Modules.pullback q).obj
      ((Scheme.Modules.pullback (p ⁻¹ᵁ degreeOpen p N d).ι).obj N)) = d := by
  have hbig := sq.paste_horiz
    (isPullback_morphismRestrict p (degreeOpen p N d)).flip
  have hd := (mem_degreeOpen_iff p N hdim hbig d).mp
    (y (IsLocalRing.closedPoint K)).2
  let eN : (Scheme.Modules.pullback q).obj
      ((Scheme.Modules.pullback (p ⁻¹ᵁ degreeOpen p N d).ι).obj N) ≅
      (Scheme.Modules.pullback (q ≫ (p ⁻¹ᵁ degreeOpen p N d).ι)).obj N :=
    (Scheme.Modules.pullbackComp q (p ⁻¹ᵁ degreeOpen p N d).ι).app N
  exact (invertibleCurveDegree_eq_of_iso K f hdim eN).trans hd

end M9Native.PolarizedCurveDegreeOpen
end
