module

public import M9StacksIntegration.MukaiCurveIsoPullback
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries

/-!
# Native linear series under an actual isomorphism over the original field

The line is the literal scheme-module pullback, and the chosen section
space is the image of the original subspace under the actual original-field
pullback equivalence on H0. Native all-degree cohomology invariance gives
the full integer line degree and the genus. The inverse curve isomorphism
then transports existence in both directions; nonpentagonality is needed
on only one of the two curves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.MukaiCurveIsoLinearSeries

/-- Invertibility of the literal native scheme pullback, with the two
native spellings compared explicitly. -/
theorem pullback_invertible {X Y : Scheme.{u}} (a : X ⟶ Y) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pullback a).obj L) := by
  letI : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L inferInstance
  have hp : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pullback a).obj L) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj a L
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hp

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (e : X ≅ Y) (he : e.hom ≫ g = f)

include he

section Proper

variable [IsProper f] [IsProper g]
  (hX : topologicalKrullDim X ≤ 1) (hY : topologicalKrullDim Y ≤ 1)

/-- The full native integer line degree is unchanged by the original
scheme isomorphism over k. No degree comparison is an input. -/
theorem degree_pullback (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L] :
    letI := pullback_invertible e.hom L
    invertibleCurveDegree k f hX ((Scheme.Modules.pullback e.hom).obj L) =
      invertibleCurveDegree k g hY L := by
  letI := pullback_invertible e.hom L
  letI : IsProper (e.hom ≫ g) := by simpa only [he] using (inferInstance : IsProper f)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible Y L
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback e.hom).obj L) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X _
  rw [invertibleCurveDegree_eq_curveDegree, invertibleCurveDegree_eq_curveDegree]
  simpa only [he] using curveDegree_pullback k e.hom g hX hY L 1

/-- Pullback of an actual native linear series, with its actual
original-K section subspace transported rather than replaced by a
new subspace of the same dimension. Basepoints are allowed. -/
def pullbackLinearSeries {d r : ℕ} (s : LinearSeries k g hY d r) :
    LinearSeries k f hX d r := by
  letI := s.isInvertible
  let h0 := MukaiCurveIsoPullback.h0PullbackEquiv k f g e he s.L
  refine
    { L := (Scheme.Modules.pullback e.hom).obj s.L
      isInvertible := pullback_invertible e.hom s.L
      degree_eq := ?_
      V := s.V.map h0.toLinearMap
      finrank_eq := ?_ }
  · exact (degree_pullback k f g e he hX hY s.L).trans s.degree_eq
  · exact (h0.finrank_map_eq s.V).trans s.finrank_eq

/-- The transported line is the literal native pullback. -/
@[simp] theorem pullbackLinearSeries_L {d r : ℕ} (s : LinearSeries k g hY d r) :
    (pullbackLinearSeries k f g e he hX hY s).L =
      (Scheme.Modules.pullback e.hom).obj s.L := rfl

/-- The transported section space is exactly the original subspace's
image under the original-field pullback equivalence. -/
@[simp] theorem pullbackLinearSeries_V {d r : ℕ} (s : LinearSeries k g hY d r) :
    (pullbackLinearSeries k f g e he hX hY s).V =
      s.V.map (MukaiCurveIsoPullback.h0PullbackEquiv k f g e he s.L).toLinearMap := rfl

/-- Existence of actual native linear series is invariant in all
degrees and dimensions, using the actual inverse isomorphism. -/
theorem nonempty_linearSeries_iff (d r : ℕ) :
    Nonempty (LinearSeries k f hX d r) ↔ Nonempty (LinearSeries k g hY d r) := by
  have hi : e.inv ≫ f = g := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  constructor
  · rintro ⟨s⟩
    exact ⟨pullbackLinearSeries k g f e.symm hi hY hX s⟩
  · rintro ⟨s⟩
    exact ⟨pullbackLinearSeries k f g e he hX hY s⟩

/-- Only one side's actual degree-five pencil obstruction is required. -/
theorem no_degree_five_pencil_iff :
    (¬ Nonempty (LinearSeries k f hX 5 1)) ↔
      ¬ Nonempty (LinearSeries k g hY 5 1) :=
  not_congr (nonempty_linearSeries_iff k f g e he hX hY 5 1)

/-- The same equivalence retains every actual pencil of degree at most
five, with no no-pencil premise on the other side. -/
theorem no_degree_le_five_pencil_iff :
    (∀ d : ℕ, d ≤ 5 → ¬ Nonempty (LinearSeries k f hX d 1)) ↔
      (∀ d : ℕ, d ≤ 5 → ¬ Nonempty (LinearSeries k g hY d 1)) := by
  constructor
  · intro h d hd
    exact (not_congr (nonempty_linearSeries_iff k f g e he hX hY d 1)).mp (h d hd)
  · intro h d hd
    exact (not_congr (nonempty_linearSeries_iff k f g e he hX hY d 1)).mpr (h d hd)

end Proper

/-- The original native genus is invariant, via the original-field
structure-sheaf cohomology comparison in degree one. -/
theorem genus_eq : genus f = genus g := by
  subst f
  rw [genus_eq_finrank_structureSheafCohomology, genus_eq_finrank_structureSheafCohomology]
  let hX := (structureSheafCohomologyIsoCohomologyOverField k (e.hom ≫ g) 1).toLinearEquiv.finrank_eq
  let hY := (structureSheafCohomologyIsoCohomologyOverField k g 1).toLinearEquiv.finrank_eq
  let hmid := finrank_cohomologyOverField_unit_pushforward k e.hom g 1
  exact hX.trans (hmid.trans hY.symm)

end M9Native.MukaiCurveIsoLinearSeries
