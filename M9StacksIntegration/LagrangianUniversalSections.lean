module

public import M9StacksIntegration.MukaiPrimitiveCanonicalEvaluation

/-!
# The actual six original sections of the restricted universal quotient

The source is the literal original six-dimensional constant space. The
target is the actual H0 of the actual universal quotient pulled back along
the given LG morphism. Its six basis sections are obtained from the
original quotient map, not from an assumed complete cohomology basis.
The kernel is identified with actual vanishing of the corresponding
constant global section. Injectivity and completeness are not assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianUniversalSections

open LagrangianMatrixChart LagrangianPluckerQuotient
open AlgebraicGeometry.Grassmannian

variable {X : Scheme.{u}} (k : Type u) [Field k]
  (f : X ⟶ Spec (.of k)) (l : X ⟶ LagrangianGrassmannian.space k)

/-- The literal original universal quotient, restricted to the original scheme. -/
abbrev quotient : QuotientPresentation X 3 6 := pullbackPresentation l (quotientOnLG k)

abbrev bundle : X.Modules := (quotient k l).target

abbrev quotientMap : freeOn X 6 ⟶ bundle k l := (quotient k l).map

/-- The actual restricted quotient has rank three by native pullback. -/
theorem bundle_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (bundle k l) 3 := by
  simpa using (quotient k l).finiteLocallyFree

/-- One of the literal original six quotient sections. -/
def quotientSection (i : Fin 6) : Γ(bundle k l, ⊤) :=
  (quotientMap k l).app ⊤ (freeBasisSection X 6 i)

/-- Its actual native cohomology class, in the original structural scalar action. -/
def sectionH0 (i : Fin 6) : cohomologyOverField k f (bundle k l) 0 :=
  (cohomologyOverFieldZeroLinearIso k f (bundle k l)).inv (quotientSection k l i)

/-- The original constant six-space maps into actual H0; this is not
assumed to be a complete basis or an injection. -/
def sectionMap : (Fin 6 → k) →ₗ[k] cohomologyOverField k f (bundle k l) 0 :=
  ∑ i : Fin 6, (LinearMap.proj i).smulRight (sectionH0 k f l i)

theorem sectionMap_apply (v : Fin 6 → k) :
    sectionMap k f l v = ∑ i : Fin 6, v i • sectionH0 k f l i := by
  simp only [sectionMap, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

theorem sectionMap_basis (i : Fin 6) :
    sectionMap k f l (Pi.single i 1) = sectionH0 k f l i := by
  classical
  simp [sectionMap_apply, Pi.single_apply]

/-- The original vector with its actual structural coefficients in the literal free sheaf. -/
def constantVector (v : Fin 6 → k) : Γ(freeOn X 6, ⊤) :=
  ∑ i : Fin 6, ExteriorEvaluation.baseRingMap k f (v i) • freeBasisSection X 6 i

/-- The actual H0/global-section comparison evaluates the original linear combination. -/
theorem sectionMap_sections (v : Fin 6 → k) :
    (cohomologyOverFieldZeroLinearIso k f (bundle k l)).hom (sectionMap k f l v) =
      ∑ i : Fin 6, ExteriorEvaluation.baseRingMap k f (v i) • quotientSection k l i := by
  have hscalar (a : k) (s : cohomologyOverField k f (bundle k l) 0) :
      (cohomologyOverFieldZeroLinearIso k f (bundle k l)).hom (a • s) =
        ExteriorEvaluation.baseRingMap k f a •
          (cohomologyOverFieldZeroLinearIso k f (bundle k l)).hom s :=
    (cohomologyOverFieldZeroLinearIso k f (bundle k l)).hom.hom.map_smul a s
  rw [sectionMap_apply, map_sum]
  simp only [hscalar, sectionH0, Iso.inv_hom_id_apply]

/-- The original quotient map, not a chosen complete evaluation, recovers the section map. -/
theorem sectionMap_constantVector (v : Fin 6 → k) :
    (cohomologyOverFieldZeroLinearIso k f (bundle k l)).hom (sectionMap k f l v) =
      (quotientMap k l).app ⊤ (constantVector k f v) := by
  rw [sectionMap_sections, constantVector, map_sum]
  simp only [Scheme.Modules.Hom.app_smul, quotientSection]

/-- A genuine relation among the original six sections is exactly an
actual constant-vector global section annihilated by the original quotient. -/
theorem sectionMap_ker_iff (v : Fin 6 → k) :
    sectionMap k f l v = 0 ↔ (quotientMap k l).app ⊤ (constantVector k f v) = 0 := by
  rw [← sectionMap_constantVector k f l v]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f (bundle k l)).hom).injective).symm

/-- The original LG coefficient map is the original structural scalar
map whenever the actual morphism lies over the original field. -/
theorem coefficients (hl : l ≫ LagrangianGrassmannian.projection k = f) :
    LagrangianPlucker.coefficientMap k l = ExteriorEvaluation.baseRingMap k f := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫
    (l ≫ LagrangianGrassmannian.projection k).appTop).hom = _
  rw [hl]
  have happ : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
    have h : X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ by simp)).op =
        𝟙 Γ(X, ⊤) := by
      change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) = _
      exact X.presheaf.map_id _
    rw [Scheme.Hom.appLE, h]
    exact Category.comp_id _
  change _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  rw [happ]

end M9Native.LagrangianUniversalSections
