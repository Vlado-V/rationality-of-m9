module

public import M9StacksIntegration.ProperGenericSmoothness
public import M9StacksIntegration.BaseFieldPoints
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A dominant map in characteristic zero has a closed rational smooth point

The source is an actual integral finite-type scheme. Its genuine absolute
smooth locus contains its generic point. After restricting there, the
checked generic-fibre local-ring argument proves smoothness of the actual
map at that generic point. The original smooth locus therefore contains
an actual closed rational point. Properness is not required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace M9Native.DominantSmoothClosedPoint
universe u
variable (K : Type u) [Field K] [CharZero K]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual smooth locus of a dominant locally finitely presented map
of integral characteristic-zero varieties is nonempty. -/
theorem smoothLocus_nonempty
    (sX : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation sX]
    (sY : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [IsDominant f] :
    (f.smoothLocus : Set X).Nonempty := by
  let U : X.Opens := sX.smoothLocus
  have hη : genericPoint X ∈ U := sX.genericPoint_mem_smoothLocus_of_perfectField
  have : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  have : Smooth (U.ι ≫ sX) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    intro x _
    exact x.2
  have : IsDominant U.ι :=
    ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace U.ι⟩
  have : IsDominant (U.ι ≫ f) := inferInstance
  let : Algebra K (Y.residueField (genericPoint Y)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ sY.appTop ≫ Y.Γevaluation (genericPoint Y)).hom.toAlgebra
  have : CharZero (Y.residueField (genericPoint Y)) :=
    charZero_of_injective_algebraMap (algebraMap K (Y.residueField (genericPoint Y))).injective
  have hmap : (U.ι ≫ f) (genericPoint U) = genericPoint Y :=
    map_genericPoint_of_isDominant (U.ι ≫ f)
  have hsm : genericPoint U ∈ (U.ι ≫ f).smoothLocus :=
    M9Native.ProperGenericSmoothness.generic_preimage_subset_smoothLocus
      (U.ι ≫ f) (isRegular_of_smooth_over_field (U.ι ≫ sX))
      (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hmap)
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at hsm
  exact ⟨U.ι (genericPoint U), hsm⟩

/-- The same genuine geometric endpoint from ordinary local finite type
over the original field and local finite type of the actual map. -/
theorem smoothLocus_nonempty_of_locallyOfFiniteType
    (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    ∃ x : X, (f.stalkMap x).hom.FormallySmooth := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨x, hx⟩ := smoothLocus_nonempty K sX sY f
  exact ⟨x, Scheme.Hom.mem_smoothLocus.mp hx⟩

/-- Over an algebraically closed field, dominance forces an actual closed
point of the original source lying in the actual map's smooth locus. -/
theorem exists_closed_smooth_point [IsAlgClosed K]
    (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    ∃ x : X, IsClosed ({x} : Set X) ∧ (f.stalkMap x).hom.FormallySmooth := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨x, hx⟩ := nonempty_inter_closedPoints
    (smoothLocus_nonempty K sX sY f)
    f.smoothLocus.isOpen.isLocallyClosed
  exact ⟨x, hx.2, Scheme.Hom.mem_smoothLocus.mp hx.1⟩

/-- That closed smooth point has a genuine rational point over the SAME
original field, with its actual base triangle retained. -/
theorem exists_closed_rational_smooth_point [IsAlgClosed K]
    (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    ∃ (x : X) (σ : Spec (.of K) ⟶ X), IsClosed ({x} : Set X) ∧
      (f.stalkMap x).hom.FormallySmooth ∧ σ ≫ sX = 𝟙 _ ∧
        σ (IsLocalRing.closedPoint K) = x := by
  obtain ⟨x, hx, hsm⟩ := exists_closed_smooth_point K sX sY f
  exact ⟨x, pointOfClosedPoint sX x hx, hx, hsm,
    pointOfClosedPoint_comp sX x hx, pointOfClosedPoint_apply sX x hx _⟩

end M9Native.DominantSmoothClosedPoint
