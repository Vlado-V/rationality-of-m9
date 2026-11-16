module

public import M9StacksIntegration.LagrangianPrimitiveCovarianceLocal
public import M9StacksIntegration.LagrangianIsotropicRestriction

/-! Global covariance of the original primitive determinant sections.
Equality is descended along the actual LG matrix cover and then pulled
back to every test scheme.  No reducedness or pointwise detection is used. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianPrimitiveSectionCovariance

open AlgebraicGeometry.Grassmannian
open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianDeterminantSections LagrangianSymplecticAction LagrangianPullback
open LagrangianPluckerEpimorphism LagrangianPluckerTrivialization
open LagrangianSectionGeneration LagrangianPrimitiveSectionsPullback
open LagrangianPrimitiveCovarianceLocal LagrangianSigmaInvariance PrimitiveRingMatrices

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

private theorem hom_ext_openCover {X : Scheme.{u}} (U : X.OpenCover)
    {M N : X.Modules} {a b : M ⟶ N}
    (h : ∀ i, (Scheme.Modules.pullback (U.f i)).map a =
      (Scheme.Modules.pullback (U.f i)).map b) : a = b := by
  have hkey (i : U.I₀) (V : X.Opens) (hV : V ≤ (U.f i).opensRange) :
      a.app V = b.app V := by
    have he := Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
      (Scheme.Modules.restrictFunctorIsoPullback (U.f i)).symm (h i)
    have hV' : U.f i ''ᵁ (U.f i ⁻¹ᵁ V) = V := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr hV
    have hh := congrArg (fun ψ => Scheme.Modules.Hom.app ψ (U.f i ⁻¹ᵁ V)) he
    change a.app (U.f i ''ᵁ (U.f i ⁻¹ᵁ V)) = b.app (U.f i ''ᵁ (U.f i ⁻¹ᵁ V)) at hh
    rwa [hV'] at hh
  apply Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover
    (fun i => (U.f i).opensRange)
  · intro x
    obtain ⟨i, y, hy⟩ := U.exists_eq x
    exact ⟨i, Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩⟩
  · intro i
    apply Scheme.Modules.hom_ext
    intro V
    change a.app (((U.f i).opensRange).ι ''ᵁ V) =
      b.app (((U.f i).opensRange).ι ''ᵁ V)
    exact hkey i _ (((U.f i).opensRange).ι_image_le V)

/-- Actual global module sections are detected after pullback to an
actual open cover, including covers whose domains have their native models. -/
theorem sections_ext_openCover {X : Scheme.{u}} (U : X.OpenCover)
    (F : X.Modules) {s t : Γ(F, ⊤)}
    (h : ∀ i, pullbackGlobalSections (U.f i) F s =
      pullbackGlobalSections (U.f i) F t) : s = t := by
  have he : sectionMap X F (fun _ : Fin 1 => s) =
      sectionMap X F (fun _ : Fin 1 => t) := by
    apply hom_ext_openCover U
    intro i
    apply (cancel_epi (pullbackFreeIso (U.f i) 1).inv).mp
    rw [sectionMap_pullback, sectionMap_pullback]
    exact congrArg (sectionMap (U.X i) ((Scheme.Modules.pullback (U.f i)).obj F))
      (funext fun _ => h i)
  have hh := congrArg (fun φ : freeOn X 1 ⟶ F =>
    φ.app ⊤ (freeBasisSection X 1 0)) he
  simpa only [sectionMap_top_basis] using hh

variable (K : Type u) [Field K] [CharZero K]

/-- Precomposition by the original constant symmetry commutes with the
actual exterior-power pullback comparison. -/
theorem primitiveSection_precomp_pullback {X Y : Scheme.{u}}
    (f : Y ⟶ X) (b : X ⟶ Spec (.of K))
    (q : QuotientPresentation X 3 6) (g : Matrix.symplecticGroup (Fin 3) K)
    (j : Fin 14) :
    (exteriorPullbackIso f q.target 3).hom.app ⊤
      (pullbackGlobalSections f (Scheme.Modules.exteriorPower q.target 3)
        (primitiveSection X K (scalarMap K b) ((constantFreeIso K b g).hom ≫ q.map) j)) =
      primitiveSection Y K (scalarMap K (f ≫ b))
        ((constantFreeIso K (f ≫ b) g).hom ≫ (pullbackPresentation f q).map) j := by
  have h := primitiveSection_pullback f K (scalarMap K b) (transform K b g q) j
  have hm : (pullbackPresentation f (transform K b g q)).map =
      (constantFreeIso K (f ≫ b) g).hom ≫ (pullbackPresentation f q).map := by
    change (pullbackFreeIso f 6).inv ≫
      (Scheme.Modules.pullback f).map ((constantFreeIso K b g).hom ≫ q.map) = _
    rw [Functor.map_comp, ← Category.assoc, constantFreeIso_pullback_inv, Category.assoc]
    rfl
  rw [← scalarMap_comp, hm] at h
  exact h

/-- Actual exterior pullback transports every original finite primitive
linear combination, with the structural scalar map retained. -/
theorem primitiveSection_sum_pullback {X Y : Scheme.{u}}
    (f : Y ⟶ X) (b : X ⟶ Spec (.of K)) {r : ℕ}
    (q : QuotientPresentation X r 6) (c : Fin 14 → K) :
    (exteriorPullbackIso f q.target 3).hom.app ⊤
      (pullbackGlobalSections f (Scheme.Modules.exteriorPower q.target 3)
        (∑ a : Fin 14, scalarMap K b (c a) •
          primitiveSection X K (scalarMap K b) q.map a)) =
      ∑ a : Fin 14, scalarMap K (f ≫ b) (c a) •
        primitiveSection Y K (scalarMap K (f ≫ b)) (pullbackPresentation f q).map a := by
  simp only [map_sum, SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, primitiveSection_pullback, ← scalarMap_comp]
  rfl

/-- The actual universal primitive sections obey the raw transpose
matrix law globally on the original LG scheme. -/
theorem primitiveSection_precomp_universal (g : Matrix.symplecticGroup (Fin 3) K)
    (j : Fin 14) :
    primitiveSection (space K) K (scalarMap K (projection K))
      ((constantFreeIso K (projection K) g).hom ≫ (quotientOnLG K).map) j =
      ∑ a : Fin 14,
        scalarMap K (projection K)
          (matrix14 K K (RingHom.id K) (transposeSymplectic K g) j a) •
          primitiveSection (space K) K (scalarMap K (projection K)) (quotientOnLG K).map a := by
  apply sections_ext_openCover (LagrangianPlucker.matrixCover K)
    (Scheme.Modules.exteriorPower (quotientOnLG K).target 3)
  intro ι
  let f := (LagrangianPlucker.matrixCover K).f ι
  let e := chartQuotientIso K f ι (LagrangianPlucker.matrixChartIntegral K ι)
    (LagrangianPlucker.matrixChartIntegral_diagram K ι)
  apply (ConcreteCategory.bijective_of_isIso
    ((exteriorPullbackIso f (quotientOnLG K).target 3).hom.app ⊤)).injective
  rw [primitiveSection_precomp_pullback, primitiveSection_sum_pullback]
  apply primitiveSection_precomp_framed K (f ≫ projection K)
    (pullbackPresentation f (quotientOnLG K)).map e
  exact LagrangianIsotropicDual.annihilatesSigma_postcomp _ e.hom
    (LagrangianIsotropicRestriction.pulledQuotient_annihilates f (quotientOnLG K).map
      (lagrangianUniversal_annihilates K))

/-- The original primitive sections of the actual pulled-back universal
quotient obey the raw transpose matrix law over every test scheme. -/
theorem primitiveSection_precomp {T : Scheme.{u}} (f : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    primitiveSection T K (LagrangianPlucker.coefficientMap K f)
      ((constantFreeIso K (f ≫ projection K) g).hom ≫
        (pullbackPresentation f (quotientOnLG K)).map) j =
      ∑ a : Fin 14, LagrangianPlucker.coefficientMap K f
          (matrix14 K K (RingHom.id K) (transposeSymplectic K g) j a) •
        primitiveSection T K (LagrangianPlucker.coefficientMap K f)
          (pullbackPresentation f (quotientOnLG K)).map a := by
  have h := congrArg (fun s => (exteriorPullbackIso f (quotientOnLG K).target 3).hom.app ⊤
    (pullbackGlobalSections f (Scheme.Modules.exteriorPower (quotientOnLG K).target 3) s))
      (primitiveSection_precomp_universal K g j)
  rw [primitiveSection_precomp_pullback, primitiveSection_sum_pullback] at h
  exact h

/-- Global covariance under the actual determinant action, for every
original test scheme and all original fourteen primitive sections. -/
theorem determinantActionIso_primitive_covariance {T : Scheme.{u}} (f : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    (LagrangianDeterminantAction.determinantActionIso K f g).hom.app ⊤
      (pullbackGlobalSections (f ≫ action K g) (determinantLine K) (primitiveSections K j)) =
      ∑ a : Fin 14, LagrangianPlucker.coefficientMap K f
          (matrix14 K K (RingHom.id K) (transposeSymplectic K g) j a) •
        pullbackGlobalSections f (determinantLine K) (primitiveSections K a) := by
  rw [LagrangianDeterminantAction.determinantActionIso_primitive,
    primitiveSection_precomp]
  simp only [map_sum, Scheme.Modules.Hom.app_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have h := primitiveSections_pullback K f a
  rw [← h]
  exact congrArg (fun φ : (Scheme.Modules.pullback f).obj (determinantLine K) ⟶
      (Scheme.Modules.pullback f).obj (determinantLine K) =>
      φ.app ⊤ (pullbackGlobalSections f (determinantLine K) (primitiveSections K a)))
    (exteriorPullbackIso f (quotientOnLG K).target 3).hom_inv_id

/-- The transpose LG action pairs with the original raw primitive matrix,
with no change to the fourteen determinant sections. -/
theorem determinantActionIso_transpose_primitive_covariance {T : Scheme.{u}}
    (f : T ⟶ space K) (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    (LagrangianDeterminantAction.determinantActionIso K f (transposeSymplectic K g)).hom.app ⊤
      (pullbackGlobalSections (f ≫ action K (transposeSymplectic K g))
        (determinantLine K) (primitiveSections K j)) =
      ∑ a : Fin 14, LagrangianPlucker.coefficientMap K f
          (matrix14 K K (RingHom.id K) g j a) •
        pullbackGlobalSections f (determinantLine K) (primitiveSections K a) := by
  have ht : transposeSymplectic K (transposeSymplectic K g) = g := by
    apply Subtype.ext
    exact Matrix.transpose_transpose _
  simpa only [ht] using
    determinantActionIso_primitive_covariance K f (transposeSymplectic K g) j

end M9Native.LagrangianPrimitiveSectionCovariance
