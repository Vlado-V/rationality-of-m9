module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Finite integral closed pieces of a Noetherian parameter scheme

The pieces are the actual irreducible components with their reduced induced
closed subscheme structures. The total scheme may be singular or nonreduced.
Every map from a field spectrum factors through one of these pieces, because
its source is reduced and irreducible. No field-size or factorization premise
is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace M9Native.FiniteIntegralComponentCover

variable (Y : Scheme.{u})

/-- The index consists of the actual irreducible components of `Y`. -/
abbrev Index := { Z : Set Y // Z ∈ irreducibleComponents Y }

/-- Noetherianness makes this actual index finite. -/
instance indexFintype [IsNoetherian Y] : Fintype (Index Y) :=
  (finite_irreducibleComponents_of_isNoetherian (X := Y)).fintype

/-- The closed subset underlying a component. -/
def componentClosed (i : Index Y) : Closeds Y :=
  ⟨i.1, isClosed_of_mem_irreducibleComponents _ i.2⟩

/-- Its actual radical vanishing ideal sheaf. -/
def componentIdeal (i : Index Y) : Y.IdealSheafData :=
  vanishingIdeal (componentClosed Y i)

/-- The component carries the reduced induced closed scheme structure. -/
def component (i : Index Y) : Scheme.{u} :=
  (componentIdeal Y i).subscheme

/-- The actual component inclusion into the original scheme. -/
def inclusion (i : Index Y) : component Y i ⟶ Y :=
  (componentIdeal Y i).subschemeι

instance inclusion_isClosedImmersion (i : Index Y) :
    IsClosedImmersion (inclusion Y i) :=
  inferInstanceAs (IsClosedImmersion (componentIdeal Y i).subschemeι)

/-- The inclusion has precisely the selected irreducible component as image. -/
theorem range_inclusion (i : Index Y) :
    Set.range (inclusion Y i) = (i.1 : Set Y) := by
  exact range_subschemeι_vanishingIdeal (componentClosed Y i)

/-- The reduced induced scheme on each actual irreducible component is integral. -/
instance component_isIntegral (i : Index Y) : IsIntegral (component Y i) := by
  have hirr : IsIrreducible (Set.range (componentIdeal Y i).subschemeι) := by
    change IsIrreducible (Set.range (inclusion Y i))
    rw [range_inclusion]
    exact i.2.1
  let : IrreducibleSpace (component Y i) :=
    irreducibleSpace_subscheme Y (componentIdeal Y i) hirr
  let : IsReduced (component Y i) :=
    isReduced_subscheme_vanishingIdeal (componentClosed Y i)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A component of a Noetherian scheme is still Noetherian. -/
instance component_isNoetherian [IsNoetherian Y] (i : Index Y) :
    IsNoetherian (component Y i) := by
  let : IsLocallyNoetherian (component Y i) :=
    LocallyOfFiniteType.isLocallyNoetherian (inclusion Y i)
  let : CompactSpace (component Y i) :=
    (inclusion Y i).isClosedEmbedding.compactSpace
  exact ⟨⟩

/-- The actual structural map of each piece remains locally of finite type
and quasi-compact. -/
theorem component_finiteType [IsNoetherian Y] {S : Scheme.{u}}
    (s : Y ⟶ S) [LocallyOfFiniteType s] (i : Index Y) :
    LocallyOfFiniteType (inclusion Y i ≫ s) ∧
      QuasiCompact (inclusion Y i ≫ s) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Every native site containing the total scheme contains the component
schemes, by the actual closed immersion size bound. -/
theorem contains_component (B : BigFppfSite.{u}) (hY : B.Contains Y) (i : Index Y) :
    B.Contains (component Y i) :=
  Scheme.size_lt_of_isClosedImmersion (inclusion Y i) hY

/-- Every original scheme point belongs to an actual component. -/
theorem exists_component_contains (y : Y) : ∃ i : Index Y, y ∈ (i.1 : Set Y) :=
  ⟨⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩,
    mem_irreducibleComponent⟩

/-- The actual integral closed schemes cover all points of the original scheme. -/
theorem exists_component_point (y : Y) :
    ∃ (i : Index Y) (x : component Y i), inclusion Y i x = y := by
  obtain ⟨i, hi⟩ := exists_component_contains Y y
  obtain ⟨x, hx⟩ := (range_inclusion Y i).symm ▸ hi
  exact ⟨i, x, hx⟩

/-- This is a covering of all points, with no reducedness assumption on `Y`. -/
theorem iUnion_range_inclusion :
    (⋃ i : Index Y, Set.range (inclusion Y i)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨i, x, hx⟩ := exists_component_point Y y
  exact Set.mem_iUnion.mpr ⟨i, x, hx⟩

/-- A map from any reduced irreducible scheme factors through one of the
actual reduced irreducible component schemes. Its image containment and
scheme-theoretic factorization are both derived. -/
theorem exists_component_lift_of_reduced_irreducible
    {T : Scheme.{u}} [IsReduced T] [IrreducibleSpace T] (a : T ⟶ Y) :
    ∃ (i : Index Y) (b : T ⟶ component Y i), b ≫ inclusion Y i = a := by
  have himage : IsIrreducible (Set.range a) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ T).image a a.continuous.continuousOn
  obtain ⟨Z, hZ, hrange⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (Set.range a) himage
  let i : Index Y := ⟨Z, hZ⟩
  have hs : Set.range a ⊆ ((componentIdeal Y i).support : Set Y) := by
    rw [componentIdeal, coe_support_vanishingIdeal]
    exact hrange
  obtain ⟨b, hb⟩ :=
    (exists_lift_subschemeι_iff_range_subset_support (componentIdeal Y i) a).mpr hs
  exact ⟨i, b, hb⟩

/-- Every original field-valued map factors through an integral component.
The field and the field-valued map have no native site cutoff hypothesis. -/
theorem exists_component_field_lift (L : Type u) [Field L]
    (a : Spec (.of L) ⟶ Y) :
    ∃ (i : Index Y) (b : Spec (.of L) ⟶ component Y i), b ≫ inclusion Y i = a :=
  exists_component_lift_of_reduced_irreducible Y a

/-- Finite type over a Noetherian base supplies the Noetherian hypothesis
used for the finite component index. In particular this applies over a field. -/
theorem noetherian_of_finiteType {S : Scheme.{u}} [IsNoetherian S]
    (s : Y ⟶ S) [LocallyOfFiniteType s] [QuasiCompact s] : IsNoetherian Y := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  exact ⟨⟩

end M9Native.FiniteIntegralComponentCover
