module

public import M9StacksIntegration.CurveConstantRankFibers
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

/-! Upper semicontinuity of the actual residue-fibre dimension.

Only finite type is assumed.  Residue-field basis vectors lift to actual stalk
elements; Nakayama makes those lifts generate the stalk.  The native spreading
of a finite spanning family then supplies the required neighbourhood.  No
flatness or freeness assumption on the stalks enters.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.FiniteTypeFiberSemicontinuity

/-- Spanning a finite module over a local ring bounds the actual residue-fibre
dimension by the size of the spanning family. -/
theorem residue_finrank_le_card_of_span
    {A M : Type u} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] {I : Type u} [Fintype I]
    (g : I → M) (hg : Submodule.span A (Set.range g) = ⊤) :
    Module.finrank (IsLocalRing.ResidueField A)
      ((IsLocalRing.ResidueField A) ⊗[A] M) ≤ Fintype.card I := by
  let K := IsLocalRing.ResidueField A
  have hm := (IsLocalRing.map_tensorProduct_mk_eq_top
    (N := Submodule.span A (Set.range g))).mpr hg
  have hspan : Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[A] g i) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp] at hm
    apply (Submodule.restrictScalars_eq_top_iff A K _).mp
    rwa [Submodule.restrictScalars_span A K Ideal.Quotient.mk_surjective]
  have hsurj : Function.Surjective
      (Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[A] g i)) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  calc
    Module.finrank K (K ⊗[A] M) ≤ Module.finrank K (I →₀ K) :=
      LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = Fintype.card I :=
      Module.finrank_eq_card_basis (Finsupp.basisSingleOne (ι := I) (R := K))

set_option maxHeartbeats 200000 in
/-- The actual residue-fibre rank of a finite type module does not increase on
some neighbourhood of the given point, without assuming free stalks. -/
theorem exists_open_fiberRank_le {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∀ y ∈ U, Scheme.Modules.fiberRank F y ≤ Scheme.Modules.fiberRank F x := by
  classical
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : IsLocalRing A := X.isLocalRing x
  let : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf F x
  let K := IsLocalRing.ResidueField A
  let I := ULift.{u} (Fin (Module.finrank K (K ⊗[A] M)))
  let b : Module.Basis I K (K ⊗[A] M) :=
    (Module.finBasis K (K ⊗[A] M)).reindex Equiv.ulift.symm
  choose g hg using fun i : I =>
    TensorProduct.mk_surjective A M K Ideal.Quotient.mk_surjective (b i)
  have hspan : Submodule.span A (Set.range g) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis g b hg
  obtain ⟨U, -, hxU, s, hs⟩ :=
    Scheme.Modules.finite_germ_lifts F.val.presheaf x g
      (V := (⊤ : X.Opens)) (Set.mem_univ x)
  have hx : ⊤ ≤ Submodule.span A
      (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) := by
    rw [congrArg Set.range (funext hs)]
    exact hspan.ge
  obtain ⟨W, hWU, hxW, hW⟩ := Scheme.Modules.span_germs_near F s x hxU hx
  refine ⟨W, hxW, fun y hy => ?_⟩
  let : Module (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
  let : IsLocalRing (ToType (X.presheaf.stalk y)) := X.isLocalRing y
  let : Module.Finite (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F y
  let gy : I → ToType (F.presheaf.stalk y) :=
    fun i => TopCat.Presheaf.germ F.val.presheaf U y (hWU hy) (s i)
  have hgy : Submodule.span (X.presheaf.stalk y) (Set.range gy) = ⊤ :=
    top_unique (hW y hy)
  have hbound := residue_finrank_le_card_of_span
    (A := ToType (X.presheaf.stalk y)) (M := ToType (F.presheaf.stalk y)) gy hgy
  change Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk y))
      ((IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗[X.presheaf.stalk y]
        F.presheaf.stalk y) ≤ Module.finrank K (K ⊗[A] M)
  simpa only [I, Fintype.card_ulift, Fintype.card_fin] using hbound

/-- Genuine upper semicontinuity for every actual finite type sheaf module. -/
theorem isOpen_fiberRank_le {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (n : ℕ) : IsOpen {x : X | Scheme.Modules.fiberRank F x ≤ n} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨U, hxU, hU⟩ := exists_open_fiberRank_le F x
  exact ⟨(U : Set X), fun y hy => (hU y hy).trans hx, U.isOpen, hxU⟩

end M9Native.FiniteTypeFiberSemicontinuity
