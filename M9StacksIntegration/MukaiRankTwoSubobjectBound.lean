module

public import M9StacksIntegration.MukaiExtensionLineBounds
public import M9StacksIntegration.MukaiRankTwoSaturatedQuotient
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivityUnconditional

/-!
# The rank-two subobject section bound in Mukai Proposition 5.3

All sheaves, subobject maps, quotient maps, and degrees are the actual
native objects. The four-section criterion constructs two line bundles
inside the original rank-two subobject. Native H0 exactness and actual
degree additivity then produce three line bundles with two sections
whose degrees sum to sixteen, contradicting absence of a degree-five
pencil. The numerical hypotheses on the original exterior-power and
quotient section spaces are explicit geometric inputs; no rank-two
subobject section bound or semi-irreducibility is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiRankTwoSubobjectBound

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A monomorphism from a sheaf with a nonzero native H0 space is a
nonzero original sheaf morphism. -/
theorem hom_ne_zero_of_mono_of_h0_pos {L E : X.Modules} (j : L ⟶ E) [Mono j]
    (h0 : 0 < Module.finrank k (cohomologyOverField k f L 0)) : j ≠ 0 := by
  intro hj
  have hid : 𝟙 L = 0 := by
    apply (cancel_mono j).mp
    simp only [Category.id_comp,zero_comp,hj]
  have hz : IsZero L := (IsZero.iff_id_eq_zero _).mpr hid
  let : (cohomologyOverFieldFunctor k f 0).Additive := by
    dsimp [cohomologyOverFieldFunctor]
    infer_instance
  let : Subsingleton (cohomologyOverField k f L 0) :=
    ModuleCat.subsingleton_of_isZero ((cohomologyOverFieldFunctor k f 0).map_isZero hz)
  have hd : Module.finrank k (cohomologyOverField k f L 0) = 0 :=
    Module.finrank_zero_of_subsingleton
  omega

variable [IsAlgClosed k] [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)
variable (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
variable (S : ShortComplex X.Modules) (hS : S.ShortExact)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₁]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃]
variable [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
variable (hgen : MukaiSemiIrreducible.GloballyGenerated S.X₂)
variable (hA : invertibleCurveDegree k f hdim S.X₁ = 2)
variable (hB : invertibleCurveDegree k f hdim S.X₃ = 6)
variable (E α : X.Modules)
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
variable (i : S.X₂ ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
variable (hT : (ShortComplex.mk i p w).ShortExact)
variable (hnonsplit : ∀ t : α ⟶ E, t ≫ p ≠ 𝟙 _)
variable (hα : invertibleCurveDegree k f hdim α = 8)
variable (hn : ¬ Nonempty (LinearSeries k f hdim 7 2))

include hnp hS hgen hA hB hT hnonsplit hα hn

/-- Every actual rank-two subbundle with these actual quotient and
determinant section bounds has at most three global sections. -/
theorem h0_le_three_of_subobject
    (hreg : IsRegular X)
    (hdegree : curveDegree k f hdim E 3 = 16)
    (F ξ : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    [FiniteDimensional k (cohomologyOverField k f F 0)]
    [FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0)]
    (u : F ⟶ E) (v : E ⟶ ξ) (wv : u ≫ v = 0)
    (hU : (ShortComplex.mk u v wv).ShortExact)
    (hξ : 2 ≤ Module.finrank k (cohomologyOverField k f ξ 0))
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 4) :
    Module.finrank k (cohomologyOverField k f F 0) ≤ 3 := by
  by_contra h
  have hfour : 4 ≤ Module.finrank k (cohomologyOverField k f F 0) := by omega
  obtain ⟨L,N,j,q,wN,hL,hN,hseq,hLsections⟩ :=
    MukaiRankTwoSaturatedQuotient.exists_saturated_line_quotient k f F hreg hdim hfour hdet
  let := hL
  let := hN
  let : Mono j := hseq.mono_f
  let : Mono u := hU.mono_f
  have hju : j ≫ u ≠ 0 :=
    hom_ne_zero_of_mono_of_h0_pos k f (j ≫ u) (by omega)
  have hLtwo := MukaiExtensionLineBounds.h0_eq_two_of_nonzero_line_map
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn L hLsections (j ≫ u) hju
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} N 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X N
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ξ 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} N :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N 1
  let : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X L
  let : N.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X N
  let : FiniteDimensional k (cohomologyOverField k f L 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f L 0
  let : FiniteDimensional k (cohomologyOverField k f N 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f N 0
  obtain ⟨δ,hinj,hex,hδ,hδ'⟩ := exists_cohomologyOverField_longExactSequence k f hseq
  let j0 := (cohomologyOverFieldMap k f j 0).hom
  let q0 := (cohomologyOverFieldMap k f q 0).hom
  have hi : Function.Injective j0 := hinj
  have he : Function.Exact j0 q0 := hex 0
  have hd := LinearMap.finrank_range_add_finrank_ker q0
  rw [he.linearMap_ker_eq,LinearMap.finrank_range_of_inj hi,hLtwo] at hd
  have hr := Submodule.finrank_le (LinearMap.range q0)
  have hNsections : 2 ≤ Module.finrank k (cohomologyOverField k f N 0) := by omega
  have hFdegree := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk j q wN) hseq 1 2 1
  have hEdegree := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk u v wv) hU 2 3 1
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim L,
    ← invertibleCurveDegree_eq_curveDegree k f hdim N] at hFdegree
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim ξ] at hEdegree
  have htotal : invertibleCurveDegree k f hdim L + invertibleCurveDegree k f hdim N +
      invertibleCurveDegree k f hdim ξ = 16 := by
    calc
      _ = curveDegree k f hdim F 2 + invertibleCurveDegree k f hdim ξ := by rw [hFdegree]
      _ = curveDegree k f hdim E 3 := hEdegree.symm
      _ = 16 := hdegree
  exact (MukaiPencilDegreeBounds.degree_sum_ne_sixteen_of_two_sections
    f hdim hnp L N ξ hLsections hNsections hξ) htotal

end M9Native.MukaiRankTwoSubobjectBound
