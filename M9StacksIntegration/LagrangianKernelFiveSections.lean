module

public import M9StacksIntegration.LagrangianCommonKernelZero
public import M9StacksIntegration.LagrangianPluckerGeneration

/-!
# Five actual determinant generators on the common-kernel locus

The five global sections are constructed from the actual native minor
sections, not supplied as a frame or generating tuple. Their literal
expansion of all fourteen primitive sections gives a factorization of
the original epimorphism. Thus they generate the actual determinant line
and define an actual native projective-four-space morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianKernelFiveSections

open LagrangianMatrixChart LagrangianPluckerQuotient LagrangianSectionGeneration
open LagrangianKernelPrimitiveSections LagrangianCommonKernelSpan

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
  {Q : X.Modules} (q : freeOn X 6 ⟶ Q)

/-- Five literal global determinant sections, with the native structural scalar action. -/
def fiveSections (a : Fin 5) : Γ(Scheme.Modules.exteriorPower Q 3, ⊤) :=
  (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom
    (fiveValues k (minorH0 k f q) a)

theorem primitiveSection_expansion
    (hq : q.app ⊤ (freeBasisSection X 6 0) = 0) (j : Fin 14) :
    primitiveSection X k (ExteriorEvaluation.baseRingMap k f) q j =
      ∑ a : Fin 5, ExteriorEvaluation.baseRingMap k f
        (embeddingFourteen k (Pi.single a 1) j) • fiveSections k f q a := by
  have hs := (primitiveH0_eq_projectedValues k f q j).trans
    (projectedValues_expansion k (minorH0 k f q)
      (minorH0_eq_zero_of_first_section_zero k f q hq) j)
  have hscalar (c : k) (s : cohomologyOverField k f (Scheme.Modules.exteriorPower Q 3) 0) :
      (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom (c • s) =
        ExteriorEvaluation.baseRingMap k f c •
          (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom s :=
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom.hom.map_smul c s
  have h := congrArg (fun s => (cohomologyOverFieldZeroLinearIso k f
    (Scheme.Modules.exteriorPower Q 3)).hom s) hs
  simpa only [primitiveH0, Iso.inv_hom_id_apply, map_sum, hscalar, fiveSections] using h

def coefficientSections (j : Fin 14) : Γ(freeOn X 5, ⊤) :=
  ∑ a : Fin 5, ExteriorEvaluation.baseRingMap k f
    (embeddingFourteen k (Pi.single a 1) j) • freeBasisSection X 5 a

def coefficientMap : freeOn X 14 ⟶ freeOn X 5 :=
  sectionMap X (freeOn X 5) (coefficientSections k f)

def fiveSectionMap : freeOn X 5 ⟶ Scheme.Modules.exteriorPower Q 3 :=
  sectionMap X (Scheme.Modules.exteriorPower Q 3) (fiveSections k f q)

/-- The original native fourteen-section morphism actually factors through the five constructed sections. -/
theorem primitiveSectionMap_factor
    (hq : q.app ⊤ (freeBasisSection X 6 0) = 0) :
    sectionMap X (Scheme.Modules.exteriorPower Q 3)
      (primitiveSection X k (ExteriorEvaluation.baseRingMap k f) q) =
        coefficientMap k f ≫ fiveSectionMap k f q := by
  have hv : (fun j : Fin 14 => (fiveSectionMap k f q).app ⊤ (coefficientSections k f j)) =
      primitiveSection X k (ExteriorEvaluation.baseRingMap k f) q := by
    funext j
    simp only [fiveSectionMap, coefficientSections, map_sum, Scheme.Modules.Hom.app_smul,
      sectionMap_top_basis]
    exact (primitiveSection_expansion k f q hq j).symm
  symm
  calc
    _ = sectionMap X (Scheme.Modules.exteriorPower Q 3)
        (fun j => (fiveSectionMap k f q).app ⊤ (coefficientSections k f j)) :=
      MukaiPrimitiveCanonicalEvaluation.sectionMap_postcomp (X := X)
        (coefficientSections k f) (fiveSectionMap k f q)
    _ = _ := congrArg (sectionMap X (Scheme.Modules.exteriorPower Q 3)) hv

variable [CharZero k] (l : X ⟶ LagrangianGrassmannian.space k)

/-- Actual epimorphy is inherited from the original universal primitive quotient. -/
theorem fiveSectionMap_epi (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤ (freeBasisSection X 6 0) = 0) :
    Epi (fiveSectionMap k f (LagrangianUniversalSections.quotientMap k l)) := by
  have h := LagrangianPluckerEpimorphism.primitiveSectionMap_epi k l
    (Iso.refl (LagrangianUniversalSections.bundle k l))
  have horig : Epi (sectionMap X
      (Scheme.Modules.exteriorPower (LagrangianUniversalSections.bundle k l) 3)
      (primitiveSection X k (ExteriorEvaluation.baseRingMap k f)
        (LagrangianUniversalSections.quotientMap k l))) := by
    simpa only [Iso.refl_hom, Category.comp_id, LagrangianUniversalSections.coefficients k f l hl] using h
  haveI : Epi (coefficientMap k f ≫
      fiveSectionMap k f (LagrangianUniversalSections.quotientMap k l)) := by
    rw [← primitiveSectionMap_factor k f _ hq]
    exact horig
  exact epi_of_epi (coefficientMap k f) _

theorem fiveSections_generatesStalks (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤ (freeBasisSection X 6 0) = 0) :
    Stacks.ProjectiveFromSections.GeneratesStalks
      (fiveSections k f (LagrangianUniversalSections.quotientMap k l)) :=
  generatesStalks_of_sectionMap_epi X _ _ (fiveSectionMap_epi k f l hl hq)

/-- The actual native projective map of the five derived generating sections. -/
def projectiveMap (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤ (freeBasisSection X 6 0) = 0) :
    X ⟶ AlgebraicGeometry.projectiveSpaceOver 4 (Spec (.of k)) := by
  letI := LagrangianPluckerGeneration.transportedDeterminant_isInvertibleModule k l
    (Iso.refl (LagrangianUniversalSections.bundle k l))
  exact Stacks.ProjectiveFromSections.toProjectiveSpaceOver
    (fiveSections k f (LagrangianUniversalSections.quotientMap k l))
    (fiveSections_generatesStalks k f l hl hq) f

theorem projectiveMap_fst (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤ (freeBasisSection X 6 0) = 0) :
    projectiveMap k f l hl hq ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} 4)) = f := by
  letI := LagrangianPluckerGeneration.transportedDeterminant_isInvertibleModule k l
    (Iso.refl (LagrangianUniversalSections.bundle k l))
  exact Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst
    (fiveSections k f (LagrangianUniversalSections.quotientMap k l))
    (fiveSections_generatesStalks k f l hl hq) f

/-- On the literal native common-kernel zero scheme every premise is derived. -/
def zeroProjectiveMap : LagrangianCommonKernelZero.zeroSpace k ⟶
    AlgebraicGeometry.projectiveSpaceOver 4 (Spec (.of k)) :=
  projectiveMap k (LagrangianCommonKernelZero.zeroProjection k)
    (LagrangianCommonKernelZero.zeroInclusion k) rfl
    (LagrangianCommonKernelZero.quotient_first_section_zero k)

theorem zeroProjectiveMap_fst :
    zeroProjectiveMap k ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} 4)) =
        LagrangianCommonKernelZero.zeroProjection k :=
  projectiveMap_fst k _ _ rfl (LagrangianCommonKernelZero.quotient_first_section_zero k)

end M9Native.LagrangianKernelFiveSections
