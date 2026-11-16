module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-! Integral open components of an actual smooth scheme over a field.
The components and their finite covering are derived from smoothness and
quasi-compactness. No irreducibility or integrality of the total scheme is
an input. These are the integral target pieces for componentwise avoidance.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace M9Native.SmoothIntegralComponentCover

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of K)) [Smooth p]

/-- The actual component through a point, with the open structure supplied
by smoothness over the field. -/
def componentOpen (x : X) : X.Opens :=
  ⟨connectedComponent x, Stacks.Chow.isOpen_connectedComponent_of_smooth p x⟩

/-- Every component is an integral scheme, even when the total scheme is
disconnected. -/
theorem component_integral (x : X) : IsIntegral (componentOpen p x).toScheme :=
  Stacks.Chow.isIntegral_connectedComponent_of_smooth p x
    (Stacks.Chow.isOpen_connectedComponent_of_smooth p x)

/-- Its actual structural morphism is smooth. -/
theorem component_smooth (x : X) : Smooth ((componentOpen p x).ι ≫ p) := by
  infer_instance

/-- A component of a quasi-compact smooth scheme is quasi-compact: it is
also closed in the original scheme. -/
theorem component_compact [CompactSpace X] (x : X) :
    CompactSpace (componentOpen p x).toScheme :=
  isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact

/-- Thus its actual field-base morphism is quasi-compact and locally of
finite type. -/
theorem component_finiteType [CompactSpace X] (x : X) :
    QuasiCompact ((componentOpen p x).ι ≫ p) ∧
      LocallyOfFiniteType ((componentOpen p x).ι ≫ p) := by
  let _ := component_compact p x
  exact ⟨inferInstance, inferInstance⟩

/-- Compactness selects finitely many of the actual integral open
components and these cover every original scheme point. -/
theorem exists_finite_component_cover [CompactSpace X] :
    ∃ t : Finset X, ∀ x : X, ∃ y ∈ t, x ∈ componentOpen p y := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y : X => connectedComponent y)
    (fun y => Stacks.Chow.isOpen_connectedComponent_of_smooth p y)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, mem_connectedComponent⟩)
  refine ⟨t, fun x => ?_⟩
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.mp hy
  exact ⟨y, hyt, hxy⟩

/-- The same original component schemes lie in every native site already
containing the total atlas; containment is derived from the open immersion. -/
theorem contains_component (B : BigFppfSite.{u}) (hX : B.Contains X) (x : X) :
    B.Contains (componentOpen p x).toScheme :=
  Scheme.size_lt_of_isOpenImmersion (componentOpen p x).ι hX

end M9Native.SmoothIntegralComponentCover
