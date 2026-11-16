module

public import M9StacksIntegration.CurvePowerGraphRestrictions
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree

/-!
# The actual self-diagonal class on the one-fold curve power

The literal repeated-coordinate pullback of the actual graph divisor is
the negative pulled-back cotangent class. The actual coordinate is an
isomorphism over the field, so the genuine proper-curve degree is its
negative cotangent degree. Native smooth-curve duality then gives `2-2g`.

The two small coordinate-isomorphism proofs replay the proofs at lines
75-84 of the pinned native `Variety/Curve/CurvePowerDegreeTransport.lean`,
using only the original curve-power lift and its universal property.
No numerical Abel or Theta theorem is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerSelfClassDegree

section Coordinate
variable {S : Scheme.{u}} (C : Over S)

/-- The actual first projection of the actual one-fold power is an isomorphism. -/
def coordinateOneIso : power C 1 ≅ C where
  hom := coord C 1 0
  inv := lift 1 (fun _ => 𝟙 C)
  hom_inv_id := hom_ext 1 fun i => by
    fin_cases i
    exact (Category.assoc _ _ _).trans
      ((congrArg _ (lift_coord (C := C) 1 _ 0)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  inv_hom_id := lift_coord (C := C) 1 _ 0

/-- The same actual isomorphism on the underlying schemes. -/
def coordinateOneLeftIso : (power C 1).left ≅ C.left :=
  (Over.forget S).mapIso (coordinateOneIso C)

theorem coordinateOne_left_isIso : IsIso (coord C 1 0).left :=
  inferInstanceAs (IsIso (coordinateOneLeftIso C).hom)

theorem powerOne_dimension (hC : topologicalKrullDim C.left = 1) :
    topologicalKrullDim (power C 1).left = 1 := by
  let e := Scheme.homeoOfIso (coordinateOneLeftIso C)
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans hC

end Coordinate

section SelfClass
variable {S : Scheme.{u}} (C : Over S) [IsSeparated C.hom]
    [SmoothOfRelativeDimension 1 C.hom]

/-- The original actual relative-differential Picard class. -/
abbrev differentialsClass : Stacks.Picard.ofScheme C.left :=
  Stacks.SheafOfModules.picardClass C.left.presheaf C.left.ringCatIsSheaf
    (Scheme.Hom.relativeDifferentials C.hom)
    (DiagonalNormalPicard.differentials_isInvertible C.hom)

/-- The actual repeated-coordinate pullback used in the same-block diagonal step. -/
def selfClass1 : Stacks.Picard.ofScheme (power C 1).left :=
  Stacks.Picard.schemePullbackClass (reindex C ![(0 : Fin 1), 0]).left
    (CurvePowerGraphCartier.graphClass C 1 (coord C 1 0))

/-- The literal self-line is the negative cotangent class pulled back
along the actual first projection. This is a Picard identity, not a degree premise. -/
theorem selfClass1_eq_neg_pullback_differentials : selfClass1 C =
    -Stacks.Picard.schemePullbackClass (coord C 1 0).left (differentialsClass C) := by
  have h := CurvePowerGraphRestrictions.coordinate_graphClass_restrict_coordinate C 1 0 0
  exact h.symm.trans (CurvePowerGraphCartier.graph_self_class C 1 (coord C 1 0))

end SelfClass

section FieldDegree
variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]

/-- Genuine degree is preserved by the actual coordinate isomorphism over the field. -/
theorem degree_pullback_coordinateOne
    (hdim : topologicalKrullDim C.left ≤ 1)
    (hdim1 : topologicalKrullDim (power C 1).left ≤ 1)
    (x : Stacks.Picard.ofScheme C.left) :
    invertibleCurveDegreeHom k (power C 1).hom hdim1
        (Stacks.Picard.schemePullbackClass (coord C 1 0).left x) =
      invertibleCurveDegreeHom k C.hom hdim x := by
  let := coordinateOne_left_isIso C
  exact invertibleCurveDegreeHom_schemePullbackClass_of_isIso k (coord C 1 0).left
    (Over.w (coord C 1 0)) hdim hdim1 x

variable [SmoothOfRelativeDimension 1 C.hom]

/-- Degree of the actual self-line is minus the actual original cotangent degree. -/
theorem selfClass1_degree
    (hdim : topologicalKrullDim C.left ≤ 1)
    (hdim1 : topologicalKrullDim (power C 1).left ≤ 1) :
    invertibleCurveDegreeHom k (power C 1).hom hdim1 (selfClass1 C) =
      -@invertibleCurveDegree k _ C.left C.hom _ hdim
        (Scheme.Hom.relativeDifferentials C.hom)
        (DiagonalNormalPicard.differentials_isInvertible C.hom) := by
  rw [selfClass1_eq_neg_pullback_differentials, map_neg,
    degree_pullback_coordinateOne k C hdim hdim1 (differentialsClass C)]
  exact congrArg Neg.neg (invertibleCurveDegreeHom_picardClass k C.hom hdim
    (Scheme.Hom.relativeDifferentials C.hom)
    (DiagonalNormalPicard.differentials_isInvertible C.hom))

variable [IsCurve k C.hom] [IsAlgClosed k]

/-- Native smooth-curve duality supplies the actual canonical normalization. -/
theorem selfClass1_degree_genus
    (hdim1 : topologicalKrullDim (power C 1).left ≤ 1) :
    invertibleCurveDegreeHom k (power C 1).hom hdim1 (selfClass1 C) =
      2 - 2 * (genus C.hom : ℤ) := by
  let : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  have hdim : topologicalKrullDim C.left ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (f := C.hom)).le
  calc
    _ = -@invertibleCurveDegree k _ C.left C.hom _ hdim
        (Scheme.Hom.relativeDifferentials C.hom)
        (DiagonalNormalPicard.differentials_isInvertible C.hom) :=
      selfClass1_degree k C hdim hdim1
    _ = -(2 * (genus C.hom : ℤ) - 2) :=
      congrArg Neg.neg
        (SmoothCurveCanonicalDifferentials.differentials_degree_of_isAlgClosed C.hom hdim)
    _ = _ := by ring

/-- The literal actual self-line has degree minus sixteen on a genus-nine curve. -/
theorem selfClass1_degree_genus_nine
    (hdim1 : topologicalKrullDim (power C 1).left ≤ 1) (hg : genus C.hom = 9) :
    invertibleCurveDegreeHom k (power C 1).hom hdim1 (selfClass1 C) = -16 := by
  rw [selfClass1_degree_genus, hg]
  norm_num

end FieldDegree

end M9Native.CurvePowerSelfClassDegree
end
