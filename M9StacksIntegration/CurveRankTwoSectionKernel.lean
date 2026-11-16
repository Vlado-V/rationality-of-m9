module

public import M9StacksIntegration.MukaiRankTwoSaturatedQuotient
public import M9StacksIntegration.MukaiRankTwoExteriorDegree
public import M9StacksIntegration.LineMapCokernelCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivityUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# A line kernel retaining a prescribed nonzero section

The line is the literal saturation of the evaluation of `(v,0)` in the
original rank-two bundle. Its quotient has rank one by native generic
rank additivity. The original section lifts to this line; a nonzero map
from that line to the given target line would be monic and could not
kill the lifted section. The actual short exact sequence therefore
factors the given map through the actual line quotient. Native degree
additivity and the nonzero line-map degree inequality give the bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace M9Native.CurveRankTwoSectionKernel

open MukaiEvaluationSaturation

/-- Rank one of the literal torsion-free quotient only needs the first
original section to be nonzero; the tuple need not be independent. -/
theorem quotient_rank_one_of_first_ne_zero
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) [F.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (s : Fin 2 → cohomologyOverField k f F 0)
    [(cokernel (MukaiSemiIrreducible.evaluation k f F s)).IsQuasicoherent]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hs : s 0 ≠ 0)
    (hw : ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 s) = 0) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (torsionFreeQuotient (MukaiSemiIrreducible.evaluation k f F s)) 1 := by
  let φ := MukaiSemiIrreducible.evaluation k f F s
  let hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  letI : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  letI : (saturation φ).IsCoherent := saturation_isCoherent φ
  letI : (torsionFreeQuotient φ).IsCoherent := torsionFreeQuotient_isCoherent φ
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (saturation φ) 1 :=
    MukaiSaturationRank.evaluation_saturation_rank_one k f F s hreg hdim hF hs hw
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (torsionFreeQuotient φ) :=
    torsionFreeQuotient_isFiniteLocallyFree φ hreg hdim hF
  have hadd := Scheme.Modules.fiberRank_genericPoint_add_of_shortExact
    (ShortComplex.mk (inclusion φ) (projection φ) (kernel.condition (projection φ)))
    (sequence_shortExact φ)
  have hFtwo := Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank
    F 2 (genericPoint X)
  have hLone := Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank
    (saturation φ) 1 (genericPoint X)
  have hQone : Scheme.Modules.fiberRank (torsionFreeQuotient φ) (genericPoint X) = 1 := by
    change Scheme.Modules.fiberRank F (genericPoint X) =
      Scheme.Modules.fiberRank (saturation φ) (genericPoint X) +
        Scheme.Modules.fiberRank (torsionFreeQuotient φ) (genericPoint X) at hadd
    rw [hFtwo, hLone] at hadd
    omega
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq
    (torsionFreeQuotient φ) 1 (genericPoint X) hQone

/-- A nonzero lifted raw section killed in a target line forces the
actual composite of sheaf maps to vanish. -/
theorem comp_eq_zero_of_killed_lift {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] {L F ξ : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property ξ]
    (j : L ⟶ F) (g : F ⟶ ξ) (z : Γ(L, ⊤)) (hz : z ≠ 0)
    (hkill : g.app ⊤ (j.app ⊤ z) = 0) : j ≫ g = 0 := by
  by_contra hne
  letI : Mono (j ≫ g) := LineMapCokernelCohomology.mono_of_ne_zero (j ≫ g) hne
  have hinj := Scheme.Modules.injective_app_of_mono (j ≫ g) ⊤
  apply hz
  apply hinj
  change g.app ⊤ (j.app ⊤ z) = (j ≫ g).app ⊤ 0
  rw [hkill, map_zero]

/-- A genuine nonzero rank-two-to-line map killing a prescribed nonzero
section has an actual line kernel carrying that same raw section. The
line-degree bound is derived from its actual quotient and determinant. -/
theorem exists_line_kernel
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    (F ξ : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property ξ]
    (g : F ⟶ ξ) (hg : g ≠ 0)
    (v : cohomologyOverField k f F 0) (hv : v ≠ 0)
    (hgv : cohomologyOverFieldMap k f g 0 v = 0) :
    letI := MukaiTwistBounds.exterior_two_isInvertible F
    ∃ (L N : X.Modules) (j : L ⟶ F) (p : F ⟶ N) (w : j ≫ p = 0)
      (hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L)
      (hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N),
      letI := hL
      letI := hN
      ∃ (t : N ⟶ ξ) (z : Γ(L, ⊤)),
        (ShortComplex.mk j p w).ShortExact ∧ Mono j ∧
        t ≠ 0 ∧ p ≫ t = g ∧ z ≠ 0 ∧
        j.app ⊤ z = (cohomologyOverFieldZeroLinearIso k f F).hom v ∧
        j ≫ g = 0 ∧
        invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le
            (Scheme.Modules.exteriorPower F 2) -
          invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le ξ ≤
          invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le L := by
  letI := MukaiTwistBounds.exterior_two_isInvertible F
  have hreg : IsRegular X := isRegular_of_smooth_over_field f
  let hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one f).le
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  letI := hF
  letI : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  let s : Fin 2 → cohomologyOverField k f F 0 := ![v, 0]
  let φ := MukaiSemiIrreducible.evaluation k f F s
  letI : (cokernel φ).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f F s
  have hs : s 0 ≠ 0 := hv
  have hw : ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 s) = 0 := by
    have he : exteriorPower.ιMulti k 2 s = 0 :=
      (exteriorPower.ιMulti k 2).map_coord_zero (1 : Fin 2) (by rfl)
    rw [he, map_zero]
  let L := saturation φ
  let N := torsionFreeQuotient φ
  let j : L ⟶ F := inclusion φ
  let p : F ⟶ N := projection φ
  have w : j ≫ p = 0 := kernel.condition p
  have hS : (ShortComplex.mk j p w).ShortExact := sequence_shortExact φ
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 :=
    MukaiSaturationRank.evaluation_saturation_rank_one k f F s hreg hdim hF hs hw
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} N 1 :=
    quotient_rank_one_of_first_ne_zero k f F s hreg hdim hs hw
  letI hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace L
  letI hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N :=
    Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace N
  let ℓ := MukaiSaturationSections.liftedSectionH0 k f φ
    (_root_.SheafOfModules.freeSection (ULift.up (0 : Fin 2)))
  have hℓ : cohomologyOverFieldMap k f j 0 ℓ = v :=
    (MukaiSaturationSections.cohomologyMap_liftedSectionH0 k f φ _).trans
      (MukaiSaturationSections.imageSectionH0_evaluation k f F s 0)
  let z : Γ(L, ⊤) := (cohomologyOverFieldZeroLinearIso k f L).hom ℓ
  have hjz : j.app ⊤ z = (cohomologyOverFieldZeroLinearIso k f F).hom v := by
    rw [← hℓ]
    exact (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f j ℓ).symm
  have hvraw : (cohomologyOverFieldZeroLinearIso k f F).hom v ≠ 0 := by
    intro hz
    apply hv
    apply (ModuleCat.mono_iff_injective
      (cohomologyOverFieldZeroLinearIso k f F).hom).mp inferInstance
    exact hz.trans (map_zero _).symm
  have hz : z ≠ 0 := by
    intro he
    apply hvraw
    rw [← hjz, he, map_zero]
  have hgraw : g.app ⊤ ((cohomologyOverFieldZeroLinearIso k f F).hom v) = 0 := by
    rw [← cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap, hgv, map_zero]
  have hjg : j ≫ g = 0 :=
    comp_eq_zero_of_killed_lift j g z hz (by rw [hjz]; exact hgraw)
  obtain ⟨t, ht⟩ := Cofork.IsColimit.desc' hS.gIsCokernel g
    (by simpa only [zero_comp] using hjg)
  have htne : t ≠ 0 := by
    intro he
    apply hg
    rw [← ht, he, comp_zero]
  have hNdeg := invertibleCurveDegree_le_of_hom_ne_zero k f hdim N ξ t htne
  have hadd := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk j p w) hS 1 2 1
  change curveDegree k f hdim F 2 = curveDegree k f hdim L 1 +
    curveDegree k f hdim N 1 at hadd
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim L,
    ← invertibleCurveDegree_eq_curveDegree k f hdim N] at hadd
  have hdet := MukaiTwistBounds.degree_exterior_two f F
  refine ⟨L, N, j, p, w, hL, hN, t, z, hS, hS.mono_f,
    htne, ht, hz, hjz, hjg, ?_⟩
  change invertibleCurveDegree k f hdim (Scheme.Modules.exteriorPower F 2) -
    invertibleCurveDegree k f hdim ξ ≤ invertibleCurveDegree k f hdim L
  rw [hdet]
  omega

end M9Native.CurveRankTwoSectionKernel
