module

public import M9StacksIntegration.LagrangianConormalRank

/-! The genuine conormal sequence and rank for an actual smooth curve immersed in LG. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianCurveConormal

private theorem first_rank {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (a c : ℕ)
    (h₁ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} S.X₁)
    (h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ a)
    (h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ c) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ (a-c) := by
  choose U hx r hr using fun x : X ↦
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict S.X₁ h₁ x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₁ (a-c)).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x ↦ ?_
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y,hx y⟩
  · let G := Scheme.Modules.restrictFunctor (U x).ι
    have hS' : (S.map G).ShortExact := hS.map_of_exact G
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (S.map G).X₁ (r x) := hr x
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (S.map G).X₂ a :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₂ a).mpr h₂).restrict (U x).ι)
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (S.map G).X₃ c :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₃ c).mpr h₃).restrict (U x).ι)
    have h := SheafOfModules.rank_add_of_shortExact (S.map G) hS' (r x) a c
      (⟨x,hx x⟩ : (U x).toScheme)
    have hrx : r x=a-c := by omega
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hrx ▸ hr x)

open LagrangianGrassmannian
variable (K : Type u) [Field K] {C : Scheme.{u}}
  (i : C ⟶ space K) [IsImmersion i]
  [SmoothOfRelativeDimension 1 (i ≫ projection K)]

/-- This is the actual native I/I² → i*ΩLG → ΩC complex. -/
abbrev sequence := Stacks.ConormalSequenceRight.conormalShortComplex i (projection K)

/-- Actual smoothness of the original curve supplies exactness of the
actual native conormal maps. -/
theorem sequence_shortExact : (sequence K i).ShortExact :=
  Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i (projection K)
    (SmoothOfRelativeDimension.smooth 1 (i ≫ projection K))

/-- The actual categorical defining-ideal conormal is compared through
the original native ideal bridge. -/
def sourceIso : (sequence K i).X₁ ≅ Stacks.Conormal.conormalSheaf i :=
  Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i

/-- The actual ambient differential rank pulls back to six. -/
theorem middle_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (sequence K i).X₂ 6 := by
  let := LagrangianDegree.lagrangianDifferentials_rank K
  exact isFiniteLocallyFreeOfRank_pullback i
    (Scheme.Hom.relativeDifferentials (projection K)) 6

/-- The actual smooth curve's native differential sheaf has rank one. -/
theorem quotient_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (sequence K i).X₃ 1 :=
  SmoothDifferentialsRankThin.relativeDifferentials_rank (i ≫ projection K) 1

/-- Exactness and genuine ranks six and one derive conormal rank five;
there is no conormal-rank or normal-isomorphism premise. -/
theorem sequence_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (sequence K i).X₁ 5 := by
  have h₂ := middle_rank K i
  have h₃ := quotient_rank K i
  have h₁ := Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact
    (sequence K i) (sequence_shortExact K i) h₂.isFiniteLocallyFree h₃.isFiniteLocallyFree
  exact first_rank (sequence K i) (sequence_shortExact K i) 6 1 h₁ h₂ h₃

/-- The original categorical ideal conormal also has actual rank five. -/
theorem conormal_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (Stacks.Conormal.conormalSheaf i) 5 :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (sourceIso K i) (sequence_rank K i)

end M9Native.LagrangianCurveConormal
