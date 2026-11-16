module

public import M9StacksIntegration.PencilBasepointRemoval
public import M9StacksIntegration.PencilDegreePullback
public import M9StacksIntegration.PencilProjectiveLineGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.PencilDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# Native pencils and actual bounded-degree maps to the projective line

The moving line is the literal native evaluation span of the original
pair, and its two lifted sections generate it. The projective morphism
and genuine pullback-twist isomorphism are constructed from that pair.
The actual native degree calculation bounds its function-field degree;
constant maps are excluded by the actual constant-global-functions
isomorphism.

Conversely, an actual degree-one point line on P1 has two sections by
native Riemann--Roch. Their actual injective pullback gives a native
pencil of the original morphism's field degree. Adding an actual
effective divisor pads every smaller degree to the required bound.
There is no basepoint-free, degree, section-independence, or generation
premise in the final equivalence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.LinearSeriesMorphism Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned
open M9Native.PencilBasepointRemoval M9Native.PencilDegreePullback
open M9Native.PencilProjectiveLineGeometry

universe u

namespace M9Native.PencilProjectiveLineBridge

attribute [local instance] isCurve_projectiveSpaceOver_one

section Predicate

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsCurve k f]

/-- An actual morphism to the original native P1, over the original
field, nonconstant and bounded in its native function-field degree. -/
def HasMapDegreeLE (N : ℕ) : Prop :=
  ∃ (p : X ⟶ Line k) (hp : p ≫ toBase k = f)
    (hnc : ¬ ∃ y : Line k, ∀ x : X, p.base x = y),
    curveMapDegree f (toBase k) p hp hnc ≤ N

end Predicate

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

omit [Smooth f] in
/-- Actual constant global functions give rank one for the original
native H0 of the structure sheaf. -/
theorem unit_cohomology_rank_eq_one :
    Module.rank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) = 1 := by
  let := isIso_globalSections_of_isAlgClosed k f
  have h1 : Module.finrank k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) = 1 :=
    finrank_cohomologyOverField_unit_zero_eq_one f
  let : Module.Finite k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) :=
    Module.finite_of_finrank_pos (by rw [h1]; decide)
  rw [← Module.finrank_eq_rank, h1, Nat.cast_one]

/-- The actual map attached to the original pair comes with the genuine
pullback-twist isomorphism onto its literal moving line, the original
coordinate pinning, a derived field-degree bound, and actual finiteness. -/
theorem exists_map_with_movingLine {d : ℕ} (A : LinearSeries k f hdim d 1)
    (b : Module.Basis (Fin 2) k A.V) :
    ∃ (p : X ⟶ Line k) (hp : p ≫ toBase k = f)
      (α : (Scheme.Modules.pullback
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} 1) ⟶ movingLine f hdim A b),
      IsIso α ∧
      (∀ i, α.app ⊤ (pullbackCoordSection
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) i) =
          movingSections f hdim A b i) ∧
      ∃ hnc : ¬ ∃ y : Line k, ∀ x : X, p.base x = y,
        curveMapDegree f (toBase k) p hp hnc ≤ d ∧ IsFinite p := by
  let := movingLine_isInvertible f hdim A b
  obtain ⟨p, hp, α, hαiso, hα⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse
      (movingSections f hdim A b) (movingSections_generate f hdim A b) f
  let αA := α ≫ movingInclusion f hdim A b
  have hαA (i : Fin 2) : αA.app ⊤ (pullbackCoordSection
      (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) i) =
        seriesSections A b i := by
    change (movingInclusion f hdim A b).app ⊤
      (α.app ⊤ (pullbackCoordSection
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) i)) = _
    rw [hα i, movingInclusion_sections]
  rcases Stacks.LinearSeriesMorphism.degreeOver_le_or_constant k f A b p hp αA hαA with
    ⟨hnc, hdegree⟩ | ⟨_, hconstant⟩
  · exact ⟨p, hp, α, hαiso, hα, hnc, hdegree,
      curveMap_isFinite f (toBase k) p hp hnc⟩
  · rw [unit_cohomology_rank_eq_one f] at hconstant
    exact (lt_irrefl _ hconstant).elim

/-- An arbitrary original native pencil, with its basepoints removed by
the actual evaluation span, gives an actual nonconstant finite P1 map. -/
theorem exists_finite_map_of_pencil {d : ℕ} (A : LinearSeries k f hdim d 1) :
    ∃ (p : X ⟶ Line k) (hp : p ≫ toBase k = f)
      (hnc : ¬ ∃ y : Line k, ∀ x : X, p.base x = y),
      curveMapDegree f (toBase k) p hp hnc ≤ d ∧ IsFinite p := by
  obtain ⟨b⟩ := Stacks.LinearSeriesMorphism.nonempty_basis A
  obtain ⟨p, hp, α, hαiso, hα, hnc, hdegree, hfinite⟩ :=
    exists_map_with_movingLine f hdim A b
  exact ⟨p, hp, hnc, hdegree, hfinite⟩

theorem hasMapDegreeLE_of_pencil {d : ℕ} (A : LinearSeries k f hdim d 1) :
    HasMapDegreeLE f d := by
  obtain ⟨p, hp, hnc, hd, _⟩ := exists_finite_map_of_pencil f hdim A
  exact ⟨p, hp, hnc, hd⟩

/-- The actual point line on P1 and its derived sections give the
reverse implication at the true field degree, padded by a genuine
effective divisor when that degree is smaller than the required bound. -/
theorem nonempty_pencil_of_hasMapDegreeLE (N : ℕ) (h : HasMapDegreeLE f N) :
    Nonempty (LinearSeries k f hdim N 1) := by
  obtain ⟨p, hp, hnc, hd⟩ := h
  obtain ⟨M, hM, hMdegree, hMsections⟩ := exists_degreeOne_line_with_two_sections k
  let := hM
  exact nonempty_pencil_of_curveMap_degree_le f (toBase k) hdim (lineDimension k)
    p hp hnc M hMdegree hMsections N hd

omit [Smooth f] in
/-- Every actual nonconstant map to P1 has strictly positive field
degree. The native dimension--degree bound applies to its actually
constructed pullback pencil, without a finiteness premise. -/
theorem curveMapDegree_positive (p : X ⟶ Line k) (hp : p ≫ toBase k = f)
    (hnc : ¬ ∃ y : Line k, ∀ x : X, p.base x = y) :
    0 < curveMapDegree f (toBase k) p hp hnc := by
  obtain ⟨M, hM, hMdegree, hMsections⟩ := exists_degreeOne_line_with_two_sections k
  let := hM
  obtain ⟨A⟩ := nonempty_pencil_of_curveMap f (toBase k)
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le (lineDimension k)
    p hp hnc M hMdegree hMsections
  let := isIso_globalSections_of_isAlgClosed k f
  have hbound := linearSeries_dimension_le_degree f A
  omega

/-- Both directions refer to the original native schemes, line bundles,
cohomology, and extension degree of function fields. Lower degrees are
included by the constructed effective-divisor padding. -/
theorem nonempty_pencil_iff_hasMapDegreeLE (N : ℕ) :
    Nonempty (LinearSeries k f hdim N 1) ↔ HasMapDegreeLE f N := by
  constructor
  · rintro ⟨A⟩
    exact hasMapDegreeLE_of_pencil f hdim A
  · exact nonempty_pencil_of_hasMapDegreeLE f hdim N

/-- The native degree-five-pencil predicate is precisely the existence
of an actual nonconstant map to native P1 of field degree at most five. -/
theorem degree_five_pencil_iff_map_degree_le_five :
    Nonempty (LinearSeries k f hdim 5 1) ↔ HasMapDegreeLE f 5 :=
  nonempty_pencil_iff_hasMapDegreeLE f hdim 5

/-- The nonpentagonal predicate used by the actual Mukai construction
has the same original-curve meaning as excluding these bounded-degree
maps. No genus hypothesis is needed for this comparison. -/
theorem no_degree_five_pencil_iff_no_map_degree_le_five :
    ¬ Nonempty (LinearSeries k f hdim 5 1) ↔ ¬ HasMapDegreeLE f 5 :=
  not_congr (degree_five_pencil_iff_map_degree_le_five f hdim)

/-- For a native degree-five pencil, the actual finite morphism has
one of the true degrees one through five, as required by the union of
the lower-degree Hurwitz loci. -/
theorem exists_finite_map_degree_one_to_five (A : LinearSeries k f hdim 5 1) :
    ∃ (p : X ⟶ Line k) (hp : p ≫ toBase k = f)
      (hnc : ¬ ∃ y : Line k, ∀ x : X, p.base x = y),
      1 ≤ curveMapDegree f (toBase k) p hp hnc ∧
        curveMapDegree f (toBase k) p hp hnc ≤ 5 ∧ IsFinite p := by
  obtain ⟨p, hp, hnc, hd, hfinite⟩ := exists_finite_map_of_pencil f hdim A
  exact ⟨p, hp, hnc, curveMapDegree_positive f p hp hnc, hd, hfinite⟩

end M9Native.PencilProjectiveLineBridge
