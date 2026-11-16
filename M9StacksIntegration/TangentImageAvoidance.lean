module

public import M9StacksIntegration.TangentImageDominance
public import M9StacksIntegration.FiniteTypeImageAvoidance

/-!
# Actual finite-image avoidance from canonical tangent-image rank

The parameter schemes may have arbitrarily many actual framing directions.
The only numerical premise is a bound on the image of the actual canonical
tangent map at every actual closed point. Characteristic-zero dominance
then gives the contradiction, and the already-proved finite closed-set
lemma produces a genuine common dense open avoiding all actual images.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace M9Native.TangentImageAvoidance
universe u v

/-- Finitely many genuinely nondominant scheme maps to an integral target
miss a common actual nonempty dense open. -/
theorem exists_dense_open_avoiding_finite_nondominant
    {ι : Type v} [Finite ι] (X : ι → Scheme.{u}) (Y : Scheme.{u}) [IsIntegral Y]
    (f : ∀ i, X i ⟶ Y) (hd : ∀ i, ¬ IsDominant (f i)) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ (U : Set Y).Nonempty ∧
      ∀ i, Disjoint (Set.range (f i).base) (U : Set Y) := by
  let Z : ι → Set Y := fun i => closure (Set.range (f i).base)
  have hproper : ∀ i, Z i ≠ Set.univ := by
    intro i he
    apply hd i
    constructor
    exact (denseRange_iff_closure_range).mpr he
  have hDense : Dense (⋃ i, Z i)ᶜ :=
    FiniteTypeImageAvoidance.dense_compl_finite_closed Z (fun _ => isClosed_closure) hproper
  let U : Y.Opens := ⟨(⋃ i, Z i)ᶜ,
    (isClosed_iUnion_of_finite (fun _ => isClosed_closure)).isOpen_compl⟩
  refine ⟨U, hDense, hDense.nonempty, ?_⟩
  intro i
  apply Set.disjoint_left.mpr
  intro y hy hyU
  exact hyU (Set.mem_iUnion.mpr ⟨i, subset_closure hy⟩)

/-- An actual canonical tangent-image rank bound below the smooth target
dimension gives a common dense open avoiding finitely many actual images.
No source dimension or nondominance premise is supplied. -/
theorem exists_dense_open_avoiding_finite_tangentImage_rank_le
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {ι : Type v} [Finite ι] (X : ι → Scheme.{u}) (Y : Scheme.{u})
    [∀ i, IsIntegral (X i)] [IsIntegral Y]
    (sX : ∀ i, X i ⟶ Spec (.of K)) [∀ i, LocallyOfFiniteType (sX i)]
    (sY : Y ⟶ Spec (.of K)) (n m : ℕ) [SmoothOfRelativeDimension n sY]
    (f : ∀ i, X i ⟶ Y) [∀ i, LocallyOfFiniteType (f i)]
    (hf : ∀ i, f i ≫ sY = sX i) (hmn : m < n)
    (hbound : ∀ (i : ι) (x : X i) (hx : IsClosed ({x} : Set (X i))),
      Module.finrank (Y.residueField (f i x))
        (TangentImageDominance.tangentImageAtClosed K (sX i) sY (f i) (hf i) x hx) ≤ m) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ (U : Set Y).Nonempty ∧
      ∀ i, Disjoint (Set.range (f i).base) (U : Set Y) := by
  apply exists_dense_open_avoiding_finite_nondominant X Y f
  intro i
  exact TangentImageDominance.not_isDominant_of_tangentImage_rank_le K (sX i) sY
    (f i) (hf i) n m hmn (hbound i)

/-- The genuine `23 + r` versus `24 + r` form for an actual smooth moduli
chart with `r` additional directions. The actual tangent-image comparison
is retained as the explicit geometric obligation. -/
theorem exists_dense_open_avoiding_rank_twentyThree_add
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {ι : Type v} [Finite ι] (X : ι → Scheme.{u}) (Y : Scheme.{u})
    [∀ i, IsIntegral (X i)] [IsIntegral Y]
    (sX : ∀ i, X i ⟶ Spec (.of K)) [∀ i, LocallyOfFiniteType (sX i)]
    (sY : Y ⟶ Spec (.of K)) (r : ℕ) [SmoothOfRelativeDimension (24 + r) sY]
    (f : ∀ i, X i ⟶ Y) [∀ i, LocallyOfFiniteType (f i)]
    (hf : ∀ i, f i ≫ sY = sX i)
    (hbound : ∀ (i : ι) (x : X i) (hx : IsClosed ({x} : Set (X i))),
      Module.finrank (Y.residueField (f i x))
        (TangentImageDominance.tangentImageAtClosed K (sX i) sY (f i) (hf i) x hx) ≤ 23 + r) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ (U : Set Y).Nonempty ∧
      ∀ i, Disjoint (Set.range (f i).base) (U : Set Y) :=
  exists_dense_open_avoiding_finite_tangentImage_rank_le K X Y sX sY (24 + r) (23 + r)
    f hf (Nat.add_lt_add_right (by decide : 23 < 24) r) hbound

end M9Native.TangentImageAvoidance
