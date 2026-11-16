module

public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import Mathlib.Topology.Baire.Lemmas

/-! Actual image dimensions and a dense open avoiding finitely many images.
Every image below comes from a genuine morphism of schemes over the original
field. The source-dimension bounds are geometric obligations, not dimensions
assigned to raw framed parameter counts. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set TopologicalSpace

universe u v
namespace M9Native.FiniteTypeImageAvoidance

section Topology

variable {Y : Type u} [TopologicalSpace Y]

/-- A genuinely lower-dimensional subset cannot be the whole space. -/
theorem ne_univ_of_dim_lt (Z : Set Y)
    (h : topologicalKrullDim Z < topologicalKrullDim Y) : Z ≠ univ := by
  intro heq
  rw [heq, topologicalKrullDim_univ] at h
  exact (lt_irrefl _ h)

/-- A finite union of proper closed subsets of an irreducible space has
dense open complement. No assertion of closure dimension is an input. -/
theorem dense_compl_finite_closed [IrreducibleSpace Y]
    {ι : Type v} [Finite ι] (Z : ι → Set Y)
    (hclosed : ∀ i, IsClosed (Z i)) (hproper : ∀ i, Z i ≠ univ) :
    Dense (⋃ i, Z i)ᶜ := by
  have hd : ∀ i, Dense (Z i)ᶜ := fun i =>
    (hclosed i).isOpen_compl.dense
      ((Set.ne_univ_iff_exists_notMem (Z i)).mp (hproper i))
  have h := (Set.finite_range (fun i => (Z i)ᶜ)).dense_sInter
    (by rintro _ ⟨i, rfl⟩; exact (hclosed i).isOpen_compl)
    (by rintro _ ⟨i, rfl⟩; exact hd i)
  simpa only [Set.sInter_range, Set.compl_iUnion] using h

/-- In particular genuine lower-dimensional closed subsets have a dense
open complement after a finite union. -/
theorem dense_compl_finite_lowerDim [IrreducibleSpace Y]
    {ι : Type v} [Finite ι] (Z : ι → Set Y)
    (hclosed : ∀ i, IsClosed (Z i))
    (hdim : ∀ i, topologicalKrullDim (Z i) < topologicalKrullDim Y) :
    Dense (⋃ i, Z i)ᶜ :=
  dense_compl_finite_closed Z hclosed (fun i => ne_univ_of_dim_lt (Z i) (hdim i))

end Topology

variable (K : Type u) [Field K]

/-- Closure-of-image dimension is bounded using the actual field-valued
structural square, rather than a general continuous-map assertion. -/
theorem closure_range_dim_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [NoetherianSpace X]
    (hf : f ≫ sY = sX) (d : WithBot ℕ∞) (hdim : topologicalKrullDim X ≤ d) :
    topologicalKrullDim (closure (Set.range f.base) : Set Y) ≤ d :=
  (AlgebraicGeometry.topologicalKrullDim_closure_range_le K f sX sY hf).trans hdim

/-- Actual morphisms from finitely many lower-dimensional parameter
schemes miss an actual dense nonempty open subscheme of the target. -/
theorem exists_dense_open_avoiding_images
    {ι : Type v} [Finite ι] (X : ι → Scheme.{u}) (Y : Scheme.{u})
    (sX : ∀ i, X i ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [∀ i, LocallyOfFiniteType (sX i)] [LocallyOfFiniteType sY]
    [∀ i, NoetherianSpace (X i)] [IrreducibleSpace Y]
    (f : ∀ i, X i ⟶ Y) (hf : ∀ i, f i ≫ sY = sX i)
    (hdim : ∀ i, topologicalKrullDim (X i) < topologicalKrullDim Y) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ (U : Set Y).Nonempty ∧
      ∀ i, Disjoint (Set.range (f i).base) (U : Set Y) := by
  let Z : ι → Set Y := fun i => closure (Set.range (f i).base)
  have hZdim : ∀ i, topologicalKrullDim (Z i) < topologicalKrullDim Y := fun i =>
    (AlgebraicGeometry.topologicalKrullDim_closure_range_le K (f i) (sX i) sY (hf i)).trans_lt
      (hdim i)
  have hd : Dense (⋃ i, Z i)ᶜ :=
    dense_compl_finite_lowerDim Z (fun _ => isClosed_closure) hZdim
  let U : Y.Opens := ⟨(⋃ i, Z i)ᶜ,
    (isClosed_iUnion_of_finite (fun _ => isClosed_closure)).isOpen_compl⟩
  refine ⟨U, hd, hd.nonempty, ?_⟩
  intro i
  apply Set.disjoint_left.mpr
  intro y hy hyU
  exact hyU (Set.mem_iUnion.mpr ⟨i, subset_closure hy⟩)

/-- The geometric 23-versus-24 case used for a low-gonality locus. The
actual parameter morphisms and their source-dimension bounds are retained. -/
theorem exists_dense_open_avoiding_dim_23_images
    {ι : Type v} [Finite ι] (X : ι → Scheme.{u}) (Y : Scheme.{u})
    (sX : ∀ i, X i ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [∀ i, LocallyOfFiniteType (sX i)] [LocallyOfFiniteType sY]
    [∀ i, NoetherianSpace (X i)] [IrreducibleSpace Y]
    (f : ∀ i, X i ⟶ Y) (hf : ∀ i, f i ≫ sY = sX i)
    (hX : ∀ i, topologicalKrullDim (X i) ≤ 23)
    (hY : topologicalKrullDim Y = 24) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ (U : Set Y).Nonempty ∧
      ∀ i, Disjoint (Set.range (f i).base) (U : Set Y) := by
  apply exists_dense_open_avoiding_images K X Y sX sY f hf
  intro i
  apply (hX i).trans_lt
  rw [hY]
  norm_num

end M9Native.FiniteTypeImageAvoidance
