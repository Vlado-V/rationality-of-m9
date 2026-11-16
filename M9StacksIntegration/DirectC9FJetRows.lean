module

public import M9StacksIntegration.CartierRestrictionImages
public import M9StacksIntegration.DirectC9JetLines
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology

/-!
# The actual unit-subline rows of the fixed-point F10 restrictions

Each row comes from the actual named Cartier sum sequence tensored by
the same actual degree-ten twist. Finite-flat concentration identifies
its actual derived images with the retained ordinary jet bundles.
The actual left image is the actual unit by the proved normalization
section and restricted-normal-line comparison. No splitting or
filtration of the jet bundles is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.CurvePower
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open ZeroObject

universe u

namespace M9Native.DirectC9FJetRows

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
  _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)
open DirectC9Bundles (restrictionPushforward)

/-- The genuine initial short exact row of an actual isomorphism,
proved with the ambient abelian category kept abstract. -/
theorem shortExact_iso_to_zero {A : Type*} [Category* A] [Abelian A]
    {M N : A} (e : M ≅ N) :
    (ShortComplex.mk e.inv (0 : M ⟶ (0 : A)) (by simp)).ShortExact := by
  let T := ShortComplex.mk e.inv (0 : M ⟶ (0 : A)) (by simp)
  have hT : T.Exact := by
    apply (T.exact_iff_epi rfl).2
    change Epi e.inv
    infer_instance
  have hm : Mono T.f := by
    change Mono e.inv
    infer_instance
  exact { exact := hT, mono_f := hm, epi_g := (isZero_zero A).epi T.g }

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom] (c₀ : power C 0 ⟶ C)

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

local instance fixedGraph_isClosedImmersion :
    IsClosedImmersion (Stacks.Hilbert.pointGraph C (power C 9) (constantPoint C c₀)) :=
  Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 9) _

omit [IsAlgClosed k] [IsProper C.hom] in
/-- The Cartier sum is the actual next fixed-point divisor; its
orientation is obtained by genuine commutativity of ideal products. -/
theorem point_mul_constantFamily (q : ℕ) :
    Stacks.Hilbert.pointIdeal C (power C 9) (constantPoint C c₀) *
      (constantFamily C c₀ q).ideal = (constantFamily C c₀ (q + 1)).ideal := by
  rw [constantFamily_successor_ideal, mul_comm]

/-- The actual first jet starts the subline tower at the actual
zero module. Its injection is the inverse of the proved unit iso. -/
theorem exists_initialUnitSubrow :
    ∃ (i : SheafOfModules.unit (power C 9).left.ringCatSheaf ⟶
        restrictionPushforward k C c₀ 0)
      (p : restrictionPushforward k C c₀ 0 ⟶ (0 : (power C 9).left.Modules))
      (w : i ≫ p = 0), (ShortComplex.mk i p w).ShortExact := by
  let e := (DirectC9JetLines.nonempty_firstJet_iso_unit k C c₀).some
  exact ⟨e.inv,0,by simp,shortExact_iso_to_zero e⟩

/-- Actual maps in the geometric subline direction. The same actual
degree-ten twist occurs in both ordinary restriction bundles. -/
theorem exists_unitSubrow (q : ℕ) :
    ∃ (i : SheafOfModules.unit (power C 9).left.ringCatSheaf ⟶
        restrictionPushforward k C c₀ (q + 1))
      (p : restrictionPushforward k C c₀ (q + 1) ⟶ restrictionPushforward k C c₀ q)
      (w : i ≫ p = 0), (ShortComplex.mk i p w).ShortExact := by
  let Y := familySpace C
  let π := familyProjection C
  let D := (constantFamily C c₀ q).ideal
  let P := Stacks.Hilbert.pointIdeal C (power C 9) (constantPoint C c₀)
  let Dn := (constantFamily C c₀ (q + 1)).ideal
  let L := DirectC9Cohomology.twistedLine k C c₀ 9
  let : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L :=
    DirectC9Cohomology.twistedLine_isInvertible k C c₀ 9
  let hD : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    (constantFamily C c₀ q).isEffectiveCartierDivisor_ideal
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ π) (q + 1) :=
    DirectC9Bundles.fixedDivisorProjection_rank k C c₀ q
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Dn.subschemeι ≫ π) ((q + 1) + 1) :=
    DirectC9Bundles.fixedDivisorProjection_rank k C c₀ (q + 1)
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (P.subschemeι ≫ π) 1 :=
    Stacks.Hilbert.isFiniteLocallyFreeOfRank_pointIdeal C (power C 9) (constantPoint C c₀)
  have hsub : P * D ≤ D := Scheme.IdealSheafData.mul_le_right P D
  obtain ⟨i₀,p₀,w₀,h₀⟩ := CartierRestrictionTensor.exists_tensorSum_shortExact D P L hD hsub
  let T := ShortComplex.mk i₀ p₀ w₀
  let K := Scheme.Modules.tensorObj (Stacks.Divisors.negativeTwist D) L
  let eK : (Scheme.Modules.pushforward (P.subschemeι ≫ π)).obj
      ((Scheme.Modules.pullback P.subschemeι).obj K) ≅
        SheafOfModules.unit (power C 9).left.ringCatSheaf :=
    GraphPointPushforward.pointPushforwardIso C (power C 9) (constantPoint C c₀) K ≪≫
      (DirectC9JetLines.nonempty_kernelTwist_sectionIso k C c₀ q).some
  let e₁ : derivedPushforwardModule π T.X₁ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj
        (SheafOfModules.unit (power C 9).left.ringCatSheaf) :=
    CartierRestrictionImages.derivedTensorKernelImageIso π D L P 1 ≪≫
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).mapIso eK
  have hprod : P * D = Dn := point_mul_constantFamily k C c₀ q
  let e₂ : derivedPushforwardModule π T.X₂ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj
        (restrictionPushforward k C c₀ (q + 1)) :=
    eqToIso (congrArg (fun I : Y.IdealSheafData => derivedPushforwardModule π
      (Scheme.Modules.tensorObj (Scheme.IdealSheafData.closedSubschemeStructureSheaf I) L))
        hprod) ≪≫
      CartierRestrictionImages.derivedTensorClosedImageIso π Dn L ((q + 1) + 1)
  let e₃ : derivedPushforwardModule π T.X₃ ≅
      (DerivedCategory.singleFunctor (power C 9).left.Modules 0).obj
        (restrictionPushforward k C c₀ q) :=
    CartierRestrictionImages.derivedTensorClosedImageIso π D L (q + 1)
  exact DirectImageTwoTerm.exists_shortExact_of_derivedImages π T h₀ _ _ _ e₁ e₂ e₃

/-- The actual complete fixed-jet tower, including its actual zero
stage; it retains the original ordinary restriction modules. -/
def jetStage : ℕ → (power C 9).left.Modules
  | 0 => 0
  | q + 1 => restrictionPushforward k C c₀ q

theorem jetStage_rank (q : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (jetStage k C c₀ q) q := by
  cases q with
  | zero => exact isFiniteLocallyFreeOfRank_zero_of_isZero (isZero_zero _)
  | succ q => exact DirectC9Bundles.restrictionPushforward_rank k C c₀ q

/-- Every actual stage has its actual unit SUBLINE row. This supplies
the ten genuine rows through the literal F10 stage. -/
theorem exists_stage_unitSubrow (q : ℕ) :
    ∃ (i : SheafOfModules.unit (power C 9).left.ringCatSheaf ⟶ jetStage k C c₀ (q + 1))
      (p : jetStage k C c₀ (q + 1) ⟶ jetStage k C c₀ q)
      (w : i ≫ p = 0), (ShortComplex.mk i p w).ShortExact := by
  cases q with
  | zero => exact exists_initialUnitSubrow k C c₀
  | succ q => exact exists_unitSubrow k C c₀ q

end M9Native.DirectC9FJetRows
