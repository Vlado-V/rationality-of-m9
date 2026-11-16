module

public import M9StacksIntegration.LineSectionIdealSum

/-! The range of the actual successive cut is the intersection of the
actual original zero-ideal supports. This supplies the set-theoretic
component geometry while retaining the independently proved scheme structure. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace M9Native.LineSectionRangeSupport
open IteratedLineSectionCuts

variable {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

theorem range_cut (ss : List Γ(L, ⊤)) :
    Set.range (simultaneousCut L ss).hom = (LineSectionIdealSum.ideal L ss).support := by
  rw [← LineSectionIdealSum.cut_ker, Scheme.Hom.support_ker]
  exact (simultaneousCut L ss).hom.isClosedEmbedding.isClosed_range.closure_eq.symm

theorem mem_range_cut_iff (ss : List Γ(L, ⊤)) (x : X) :
    x ∈ Set.range (simultaneousCut L ss).hom ↔
      ∀ s ∈ ss, x ∈ (Stacks.Divisors.zeroScheme X L s).support := by
  rw [range_cut, LineSectionIdealSum.ideal, Scheme.IdealSheafData.support_iSup]
  change x ∈ ((⨅ s : {s : Γ(L, ⊤) // s ∈ ss},
    (Stacks.Divisors.zeroScheme X L s.1).support : Closeds X) : Set X) ↔ _
  rw [Closeds.coe_iInf, Set.mem_iInter]
  constructor
  · intro h s hs
    exact h ⟨s, hs⟩
  · intro h s
    exact h s.1 s.2

/-- Once the remaining projective equations imply the actual remaining
zero-support conditions, the prefix/tail intersection lies in the actual
final cut. No projective intersection or desired component conclusion is
given as an input. -/
theorem image_inter_of_tail_support (ss : List Γ(L, ⊤)) (i : ℕ)
    {P : Scheme.{u}} (j : X ⟶ P) (T : Set P)
    (hTail : ∀ x : X, j x ∈ T →
      ∀ s ∈ ss.drop i, x ∈ (Stacks.Divisors.zeroScheme X L s).support) :
    Set.range ((simultaneousCut L (ss.take i)).hom ≫ j) ∩ T ⊆
      Set.range ((simultaneousCut L ss).hom ≫ j) := by
  rintro _ ⟨⟨p, rfl⟩, hpT⟩
  let x := (simultaneousCut L (ss.take i)).hom p
  have hFirst : ∀ s ∈ ss.take i, x ∈ (Stacks.Divisors.zeroScheme X L s).support :=
    (mem_range_cut_iff L (ss.take i) x).mp ⟨p, rfl⟩
  have hLast := hTail x hpT
  have hAll : ∀ s ∈ ss, x ∈ (Stacks.Divisors.zeroScheme X L s).support := by
    intro s hs
    have hs' : s ∈ ss.take i ++ ss.drop i := by rwa [List.take_append_drop]
    rcases List.mem_append.mp hs' with hs' | hs'
    · exact hFirst s hs'
    · exact hLast s hs'
  obtain ⟨q, hq⟩ := (mem_range_cut_iff L ss x).mpr hAll
  refine ⟨q, ?_⟩
  simp only [Scheme.Hom.comp_apply]
  exact congrArg j hq

end M9Native.LineSectionRangeSupport
