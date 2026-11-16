module

public import M9StacksIntegration.LagrangianConormalSequence
public import M9StacksIntegration.SmoothDifferentialsRankThin
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Smooth
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Kernel
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank

/-!
# Actual rank three of the LG-in-Grassmannian conormal

The original conormal is the actual kernel in the actual native short
exact sequence. Original smooth dimensions nine and six give the
actual differential ranks. Local rank additivity then derives rank3.
No codimension, conormal rank or section regularity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianDegree

private theorem shortExact_first_rank {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (a c : ℕ)
    (h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ a)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ c) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ (a - c) := by
  choose U hx r hr using fun x : X ↦
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict S.X₁ h₁ x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₁ (a - c)).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x ↦ ?_
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y, hx y⟩
  · let G := Scheme.Modules.restrictFunctor (U x).ι
    have hS' : (S.map G).ShortExact := hS.map_of_exact G
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₁
        (r x) := hr x
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₂ a :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₂ a).mpr h₂).restrict (U x).ι)
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₃ c :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₃ c).mpr h₃).restrict (U x).ι)
    have h := AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact (S.map G) hS' (r x) a c
      (⟨x, hx x⟩ : (U x).toScheme)
    have hrx : r x = a - c := by omega
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hrx ▸ hr x)


open M9Native.LagrangianGrassmannian

variable (K : Type u) [Field K]

/-- Actual differentials on the actual ambient Grassmannian have rank9. -/
theorem ambientDifferentials_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Hom.relativeDifferentials (grassmannianProjection K)) 9 := by
  let : SmoothOfRelativeDimension 9 (grassmannianProjection K) := by
    change SmoothOfRelativeDimension (3 * (6-3))
      (AlgebraicGeometry.Grassmannian.schemeOver.over 3 6 (base K)).hom
    infer_instance
  exact SmoothDifferentialsRankThin.relativeDifferentials_rank (grassmannianProjection K) 9

/-- Actual differentials on the original LG have rank6. -/
theorem lagrangianDifferentials_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Hom.relativeDifferentials (projection K)) 6 :=
  SmoothDifferentialsRankThin.relativeDifferentials_rank (projection K) 6

/-- The original sectionwise defining-ideal conormal has actual rank3. -/
theorem conormalSequence_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (conormalSequence K).X₁ 3 := by
  have h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (conormalSequence K).X₂ 9 := by
    let := ambientDifferentials_rank K
    exact isFiniteLocallyFreeOfRank_pullback (inclusion K)
      (Scheme.Hom.relativeDifferentials (grassmannianProjection K)) 9
  have h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (conormalSequence K).X₃ 6 :=
    lagrangianDifferentials_rank K
  have h₁ := Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact
    (conormalSequence K) (conormalSequence_shortExact K)
    h₂.isFiniteLocallyFree h₃.isFiniteLocallyFree
  exact shortExact_first_rank (conormalSequence K) (conormalSequence_shortExact K)
    9 6 h₁ h₂ h₃

/-- The genuine categorical-ideal conormal, with its native comparison,
also has rank3. -/
theorem conormalSheaf_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.Conormal.conormalSheaf (inclusion K)) 3 :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (conormalSequence_sourceIso K) (conormalSequence_rank K)

end M9Native.LagrangianDegree
