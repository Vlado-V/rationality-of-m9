module

public import M9StacksIntegration.LagrangianFreeDualSections
public import M9StacksIntegration.MukaiConormalRank
public import M9StacksIntegration.SectionCokernelField
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.EpiIso
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact

/-!
# The actual dual point line in the original free coordinates

The coordinate morphism is defined by literal evaluation on each original
free basis section. Its inverse is constructed from the original
coordinate functionals. Thus the dual of an actual epimorphism onto a
line gives an actual line in the original free sheaf, with no choice of a
rank-one identification or unproved coordinate scalar.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiPointLine

open LagrangianMatrixChart LagrangianPluckerQuotient LagrangianSectionGeneration
open LagrangianIsotropicDual LagrangianLocalIsotropy LagrangianFreeDualSections
open LagrangianFreeMatrixPullback

variable {X : Scheme.{u}}

/-- Evaluation on the actual global section as a whole-sheaf morphism. -/
def sectionPairing (Q : X.Modules) (s : Γ(Q, ⊤)) :
    dualSheaf Q ⟶ SheafOfModules.unit X.ringCatSheaf :=
  topFunctional (dualSheaf Q) ((toDoubleDual Q).app ⊤ s)

theorem sectionPairing_apply (Q : X.Modules) (s : Γ(Q, ⊤)) (a : Γ(dualSheaf Q, ⊤)) :
    (sectionPairing Q s).app ⊤ a = evalAt Q a s := by
  rw [sectionPairing, topFunctional_top]
  exact toDoubleDual_val_app_apply Q ⊤ s a

def coordinatesMap (X : Scheme.{u}) (r : ℕ) : dualSheaf (freeOn X r) ⟶ freeOn X r :=
  ∑ i : Fin r, sectionPairing (freeOn X r) (freeBasisSection X r i) ≫
    SheafOfModules.ιFree (ULift.up.{u} i)

theorem coordinatesMap_projection (X : Scheme.{u}) (r : ℕ) (i : Fin r) :
    coordinatesMap X r ≫ SheafOfModules.freeProjection (ULift.up.{u} i) =
      sectionPairing (freeOn X r) (freeBasisSection X r i) := by
  classical
  unfold coordinatesMap
  rw [Preadditive.sum_comp, Finset.sum_eq_single i]
  · calc
      _ = sectionPairing (freeOn X r) (freeBasisSection X r i) ≫
          (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} i) ≫
            SheafOfModules.freeProjection (ULift.up.{u} i)) := Category.assoc _ _ _
      _ = sectionPairing (freeOn X r) (freeBasisSection X r i) ≫ 𝟙 _ :=
        congrArg (fun h => sectionPairing (freeOn X r) (freeBasisSection X r i) ≫ h)
          (SheafOfModules.ιFree_comp_freeProjection_self (R := X.ringCatSheaf) (ULift.up.{u} i))
      _ = _ := Category.comp_id _
  · intro j _ hji
    calc
      _ = sectionPairing (freeOn X r) (freeBasisSection X r j) ≫
          (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} j) ≫
            SheafOfModules.freeProjection (ULift.up.{u} i)) := Category.assoc _ _ _
      _ = sectionPairing (freeOn X r) (freeBasisSection X r j) ≫ 0 :=
        congrArg (fun h => sectionPairing (freeOn X r) (freeBasisSection X r j) ≫ h)
          (SheafOfModules.ιFree_comp_freeProjection_of_ne (R := X.ringCatSheaf)
            (show ULift.up.{u} j ≠ ULift.up.{u} i from fun h => hji (ULift.up.inj h)))
      _ = 0 := comp_zero
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem coordinatesMap_coordinates (X : Scheme.{u}) (r : ℕ)
    (a : Γ(dualSheaf (freeOn X r), ⊤)) (i : Fin r) :
    freeSectionCoordinates X r ((coordinatesMap X r).app ⊤ a) i =
      evalAt (freeOn X r) a (freeBasisSection X r i) := by
  rw [freeSectionCoordinates_apply, freeProj_eq_freeProjection]
  change (coordinatesMap X r ≫ SheafOfModules.freeProjection (ULift.up.{u} i)).app ⊤ a = _
  rw [coordinatesMap_projection, sectionPairing_apply]

def coordinateInverse (X : Scheme.{u}) (r : ℕ) : freeOn X r ⟶ dualSheaf (freeOn X r) :=
  sectionMap X (dualSheaf (freeOn X r)) (fun j =>
    functionalSection (freeOn X r) (SheafOfModules.freeProjection (ULift.up.{u} j)))

theorem coordinateInverse_comp_coordinatesMap (X : Scheme.{u}) (r : ℕ) :
    coordinateInverse X r ≫ coordinatesMap X r = 𝟙 (freeOn X r) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  ext i j
  rw [← freeCoordinates_map_basis]
  change freeSectionCoordinates X r
    ((coordinatesMap X r).app ⊤ ((coordinateInverse X r).app ⊤ (freeBasisSection X r j))) i = _
  rw [coordinatesMap_coordinates]
  unfold coordinateInverse
  rw [sectionMap_top_basis, evalAt_functionalSection]
  have h := freeCoordinates_basis X r j i
  rw [freeSectionCoordinates_apply, freeProj_eq_freeProjection] at h
  rw [Stacks.FreeSheafMatrix.toMatrix_id, Matrix.one_apply]
  have hif : (if j = i then (1 : Γ(X, ⊤)) else 0) =
      (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst j
      simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
  exact h.trans hif

instance coordinatesMap_isIso (X : Scheme.{u}) (r : ℕ) : IsIso (coordinatesMap X r) := by
  let : Epi (coordinatesMap X r) := epi_of_epi_fac (coordinateInverse_comp_coordinatesMap X r)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeOn X r) r :=
    SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf (freeOn X r)) r :=
    isFiniteLocallyFreeOfRank_dualSheaf (freeOn X r) r inferInstance
  exact SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfRank (coordinatesMap X r) r

def coordinatesIso (X : Scheme.{u}) (r : ℕ) : dualSheaf (freeOn X r) ≅ freeOn X r :=
  asIso (coordinatesMap X r)

/-- The actual dual of the original quotient, read in those exact coordinates. -/
def pointLineMap {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q) :
    dualSheaf Q ⟶ freeOn X r :=
  dualMap q ≫ coordinatesMap X r

theorem pointLineMap_coordinates {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q)
    (a : Γ(dualSheaf Q, ⊤)) (i : Fin r) :
    freeSectionCoordinates X r ((pointLineMap q).app ⊤ a) i =
      evalAt Q a (q.app ⊤ (freeBasisSection X r i)) := by
  change freeSectionCoordinates X r
    ((coordinatesMap X r).app ⊤ ((dualMap q).app ⊤ a)) i = _
  rw [coordinatesMap_coordinates]
  exact dualPairing_dualMap q a (Over.mk (𝟙 (⊤ : X.Opens))) (freeBasisSection X r i)

def pointCokernelProjection {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q) :
    freeOn X r ⟶ dualSheaf (kernel q) :=
  (coordinatesIso X r).inv ≫ dualMap (kernel.ι q)

theorem pointLineMap_comp {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q) :
    pointLineMap q ≫ pointCokernelProjection q = 0 := by
  change dualMap q ≫ ((coordinatesIso X r).hom ≫
    ((coordinatesIso X r).inv ≫ dualMap (kernel.ι q))) = 0
  rw [Iso.hom_inv_id_assoc]
  exact (dualMap_comp (kernel.ι q) q).symm.trans
    ((congrArg dualMap (kernel.condition q)).trans
      (SectionCokernelLocallyFree.dualMap_zero_map (kernel q) Q))

def pointSequence {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q) : ShortComplex X.Modules :=
  ShortComplex.mk (pointLineMap q) (pointCokernelProjection q) (pointLineMap_comp q)

theorem pointSequence_shortExact {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q) [Epi q]
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 1) :
    (pointSequence q).ShortExact := by
  let hF := SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r
  let hK := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    q inferInstance r 1 hF hQ
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  obtain ⟨w, hd⟩ := exists_dualSheaf_shortExact (kernel.ι q) q (kernel.condition q)
    hS.mono_f hS.epi_g hS.exact
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hK.isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hF.isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hQ.isFiniteLocallyFree)
  let e : ShortComplex.mk (dualMap q) (dualMap (kernel.ι q)) w ≅ pointSequence q :=
    ShortComplex.isoMk (Iso.refl _) (coordinatesIso X r) (Iso.refl _)
      (by rfl) (by
        change (coordinatesIso X r).hom ≫
          ((coordinatesIso X r).inv ≫ dualMap (kernel.ι q)) = dualMap (kernel.ι q) ≫ 𝟙 _
        rw [Category.comp_id, Iso.hom_inv_id_assoc])
  exact ShortComplex.shortExact_of_iso e hd

theorem pointLineMap_mono {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q) [Epi q]
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 1) : Mono (pointLineMap q) :=
  (pointSequence_shortExact q hQ).mono_f

theorem pointLineCokernel_rank {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q) [Epi q]
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 1) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel (pointLineMap q)) (r-1) := by
  let hF := SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r
  let hK := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    q inferInstance r 1 hF hQ
  let hD := isFiniteLocallyFreeOfRank_dualSheaf (kernel q) (r-1) hK
  let e : cokernel (pointLineMap q) ≅ dualSheaf (kernel q) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (pointLineMap q))
      (pointSequence_shortExact q hQ).gIsCokernel
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm hD

end M9Native.MukaiPointLine
