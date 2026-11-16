module

public import M9StacksIntegration.ProjectiveSectionIso
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers

/-!
# Native projective evaluation for the actual unit module

The line-bundle construction and the construction from global functions
give the same actual projective morphism.  On every nonvanishing chart the
restricted pivot is a unit by the actual trivialization clause; native
pullback naturality and unit invariance then give the required pinning.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.ProjectiveSectionFunctions

open Stacks.ProjectiveFromSections

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

abbrev UnitLine (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

theorem restriction_appTop {X : Scheme.{u}} (U : X.Opens) (a : Γ(X, ⊤)) :
    U.topIso.inv (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a) = U.ι.appTop a := by
  have h : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ U.topIso.inv = U.ι.appTop := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, ← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h a

variable {X : Scheme.{u}} [Stacks.Ample.IsInvertibleModule X (UnitLine X)]
  {n : ℕ} (s : Fin (n + 1) → Γ(X, ⊤))
  (hs : GeneratesStalks (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s))
  (hspan : Ideal.span (Set.range s) = ⊤)

/-- A pivot of the unit-module family becomes a unit on its actual native
nonvanishing chart.  This follows directly from bijectivity of multiplication. -/
theorem pivot_unit (i : Fin (n + 1)) :
    IsUnit ((nvCover (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i).ι.appTop (s i)) := by
  let U := nvCover (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i
  obtain ⟨a, ha⟩ := (Stacks.NonvanishingSpelling.bijective_smul X (UnitLine X) (s i)
    (show U ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (UnitLine X) (s i) from le_rfl)).surjective
      (1 : Γ(X, U))
  have hunit : IsUnit (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s i)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨a, ?_⟩
    change a * X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s i) = 1 at ha
    simpa only [mul_comm] using ha
  exact (congrArg IsUnit (restriction_appTop U (s i))).mp (hunit.map U.topIso.inv.hom)

theorem chartRatio_mul_pivot (i j : Fin (n + 1)) :
    chartRatio (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i j *
        (nvCover (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i).ι.appTop (s i) =
      (nvCover (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i).ι.appTop (s j) := by
  let U := nvCover (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i
  have h := congrArg U.topIso.inv
    (ratio_smul (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i j)
  change U.topIso.inv (ratio (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i j *
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s i)) =
      U.topIso.inv (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s j)) at h
  rw [map_mul, restriction_appTop, restriction_appTop] at h
  exact h

/-- The two native constructions are the same actual morphism to the
integral projective space. -/
theorem toProjectiveSpaceAtUniverse_unit :
    Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse (X := X) (L := UnitLine X)
        (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) hs =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (X := X) s hspan := by
  let t : Stacks.ProjectiveSpaceModuli.GeneratingTuple X n := ⟨UnitLine X, inferInstance, s, hs⟩
  have hp : Stacks.ProjectiveSpaceModuli.IsPinned t
      (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (X := X) s hspan) := by
    intro i
    let U := nvCover (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i
    let r : Fin (n + 1) → Γ(U.toScheme, ⊤) := fun j => U.ι.appTop (s j)
    have hr : Ideal.span (Set.range r) = ⊤ :=
      Stacks.SectionsToProjectiveSpace.span_range_comp U.ι.appTop.hom s hspan
    let v : Γ(U.toScheme, ⊤)ˣ := (pivot_unit s i).unit
    have hv : (v : Γ(U.toScheme, ⊤)) = r i := (pivot_unit s i).unit_spec
    have hratio (j : Fin (n + 1)) :
        chartRatio (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i j =
          (↑(v⁻¹) : Γ(U.toScheme, ⊤)) * r j := by
      calc
        _ = chartRatio (L := UnitLine X)
            (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i j * (↑v * ↑(v⁻¹)) := by simp
        _ = (chartRatio (L := UnitLine X)
            (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i j * ↑v) * ↑(v⁻¹) := by
          rw [mul_assoc]
        _ = r j * ↑(v⁻¹) := by rw [hv, chartRatio_mul_pivot]
        _ = _ := mul_comm _ _
    have hf : (fun j => (↑(v⁻¹) : Γ(U.toScheme, ⊤)) * r j) =
        chartRatio (L := UnitLine X) (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) i :=
      funext (fun j => (hratio j).symm)
    have hscaled : Ideal.span (Set.range fun j => (↑(v⁻¹) : Γ(U.toScheme, ⊤)) * r j) = ⊤ := by
      rw [Stacks.SectionsToProjectiveSpace.span_range_unit_smul]
      exact hr
    have hA : U.ι ≫ Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (X := X) s hspan =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (X := U.toScheme) r hr :=
      Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality U.ι s hspan hr
    have hB : Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (X := U.toScheme)
          (fun j => (↑(v⁻¹) : Γ(U.toScheme, ⊤)) * r j) hscaled =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (X := U.toScheme) r hr :=
      Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance (v⁻¹) r hr hscaled
    exact hA.trans (hB.symm.trans
      (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr (X := U.toScheme)
        hf hscaled (span_range_chartRatio (L := UnitLine X) s i)))
  exact Stacks.ProjectiveSpaceModuli.eq_of_isPinned
    (t := t)
    (g := Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse (X := X) (L := UnitLine X) s hs)
    (g' := Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (X := X) s hspan)
    (fun i => ι_toProjectiveSpaceAtUniverse (X := X) (L := UnitLine X) s hs i) hp

/-- The equality preserves the original base morphism. -/
theorem toProjectiveSpaceOver_unit {S : Scheme.{u}} (f : X ⟶ S) :
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver (X := X) (L := UnitLine X)
        (show Fin (n + 1) → Γ(UnitLine X, ⊤) from s) hs f =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver (X := X) s hspan f := by
  apply pullback.hom_ext
  · simp only [Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst]
  · simp only [Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_snd]
    exact toProjectiveSpaceAtUniverse_unit s hs hspan

end M9Native.ProjectiveSectionFunctions
