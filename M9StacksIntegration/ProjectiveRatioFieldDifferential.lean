module

public import M9StacksIntegration.ProjectiveRatioFieldValues
public import M9StacksIntegration.RelativeDifferentialsSpatialComposition
public import M9StacksIntegration.MukaiConormalCotangentTransport

/-! Actual native point differentials of projective ratios in an actual
O(1) frame. Product and chain rules retain the original pullback units. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf
  AlgebraicGeometry.projectiveSpaceAtUniverse
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace M9Native.ProjectiveRatioFieldDifferential

open SpecFieldStalkSections SpecFieldPullbackSections ProjectiveEulerFieldPoint
open ProjectiveRatioFieldValues
open Scheme.Hom MukaiConormalCotangentTransport

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] {T : Scheme.{u}} (z : space K ⟶ T)

theorem pulledSection_smul (M : T.Modules) (U : T.Opens)
    (hz : z.base (point K) ∈ U) (r : Γ(T,U)) (s : Γ(M,U)) :
    pulledSection K z M U hz (r • s) =
      valueOn K z U hz r • pulledSection K z M U hz s := by
  change pullbackSectionHom z M U ⊤ (preimageTop K z U hz) (r • s) =
    (scalarEquiv K).symm (scalarEquiv K (z.appLE U ⊤ (preimageTop K z U hz) r)) •
      pullbackSectionHom z M U ⊤ (preimageTop K z U hz) s
  rw [RingEquiv.symm_apply_apply]
  exact pullbackSectionHom_smul z M U ⊤ (preimageTop K z U hz) r s

theorem pulledSection_add (M : T.Modules) (U : T.Opens)
    (hz : z.base (point K) ∈ U) (a b : Γ(M,U)) :
    pulledSection K z M U hz (a+b) =
      pulledSection K z M U hz a + pulledSection K z M U hz b :=
  map_add (pullbackSectionHom z M U ⊤ (preimageTop K z U hz)).hom a b

variable (projection : T ⟶ Spec (.of K))

abbrev Target := moduleSpecΓFunctor.obj
  ((Scheme.Modules.pullback z).obj (relativeDifferentials projection))

def pointDerivative (s : Γ(T,⊤)) : Target K z projection :=
  pullbackGlobalSections z (relativeDifferentials projection)
    ((universalRelativeDerivation projection).d s)

theorem pointDerivative_local (U : T.Opens) (hz : z.base (point K) ∈ U)
    (s : Γ(T,⊤)) :
    pulledSection K z (relativeDifferentials projection) U hz
      ((universalRelativeDerivation projection).d
        ((T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s)) =
      pointDerivative K z projection s := by
  have hd : (universalRelativeDerivation projection).d
      ((T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) =
    ((relativeDifferentials projection).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op).hom ((universalRelativeDerivation projection).d s) :=
    (universalRelativeDerivation projection).d_map (homOfLE (le_top : U ≤ ⊤)).op s
  rw [hd]
  change pullbackSectionHom z (relativeDifferentials projection) U ⊤
    (preimageTop K z U hz)
      ((relativeDifferentials projection).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op ((universalRelativeDerivation projection).d s)) = _
  refine (pullbackSectionHom_map z (relativeDifferentials projection) ⊤ U le_top ⊤
    (preimageTop K z U hz) (show (⊤ : (space K).Opens) ≤ z ⁻¹ᵁ ⊤ from le_rfl)
      ((universalRelativeDerivation projection).d s)).trans ?_
  change Scheme.Modules.pullbackSection z (relativeDifferentials projection) ⊤ ⊤ le_rfl
      ((universalRelativeDerivation projection).d s) =
    pullbackGlobalSections z (relativeDifferentials projection)
      ((universalRelativeDerivation projection).d s)
  rw [pullbackGlobalSections_eq_unit]
  exact Scheme.Modules.pullbackSection_top z (relativeDifferentials projection) le_rfl _

variable {n : ℕ} (h : T ⟶ projectiveSpaceAtUniverse.{u} n)
variable (e : (Scheme.Modules.pullback h).obj (twistingSheafAtUniverse.{u} n) ≅
  SheafOfModules.unit T.ringCatSheaf)

def projectiveDifferential :
    (Scheme.Modules.pullback h).obj (relativeDifferentials (integralProjection n)) ⟶
      relativeDifferentials projection :=
  relativeDifferentialsMap h (integralProjection n) projection
    (specULiftZIsTerminal.from (Spec (.of K))) (specULiftZIsTerminal.hom_ext _ _)

def pointCotangentMap : cotangentSections (ULift.{u} ℤ) n K (z ≫ h) →ₗ[K]
    Target K z projection :=
  (moduleSpecΓFunctor.map
    (((Scheme.Modules.pullbackComp z h).app (relativeDifferentials (integralProjection n))).inv ≫
      (Scheme.Modules.pullback z).map (projectiveDifferential K projection h))).hom

variable (i : Fin (n+1))
variable (hp : image (ULift.{u} ℤ) n K (z ≫ h) ∈
  ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))

def ratioDerivative (j : Fin (n+1)) : Target K z projection :=
  pulledSection K z (relativeDifferentials projection)
    (h ⁻¹ᵁ ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) hp
      ((universalRelativeDerivation projection).d
        ((h.app (ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n)
          (MvPolynomial.X i))).hom (chartFracSection (ULift.{u} ℤ) n i j)))

/-- The actual cotangent map sends the actual pulled ratio differential
to the actual derivative of the pulled chart function. -/
theorem pointCotangentMap_ratioDifferential (j : Fin (n+1)) :
    pointCotangentMap K z projection h (ratioDifferential (ULift.{u} ℤ) n K (z ≫ h) i hp j) =
      ratioDerivative K z projection h i hp j := by
  let D : (projectiveSpaceAtUniverse.{u} n).Opens :=
    ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)
  let U := h ⁻¹ᵁ D
  let M := relativeDifferentials (integralProjection n)
  let s := (universalRelativeDerivation (integralProjection n)).d
    (chartFracSection (ULift.{u} ℤ) n i j)
  have hc := Scheme.Modules.pullbackSection_comp z h M D U ⊤ le_rfl
    (preimageTop K z U hp) (preimageTop K (z ≫ h) D hp) s
  have hi : (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp z h).app M).inv).hom
      (ratioDifferential (ULift.{u} ℤ) n K (z ≫ h) i hp j) =
    pulledSection K z ((Scheme.Modules.pullback h).obj M) U hp
      (Scheme.Modules.pullbackSection h M D U le_rfl s) := by
    have hh := congrArg (fun t => ((Scheme.Modules.pullbackComp z h).app M).inv.app ⊤ t) hc
    have hid := congrArg (fun a => a.app ⊤
      (pulledSection K z ((Scheme.Modules.pullback h).obj M) U hp
        (Scheme.Modules.pullbackSection h M D U le_rfl s)))
      ((Scheme.Modules.pullbackComp z h).app M).hom_inv_id
    exact hh.symm.trans hid
  change (moduleSpecΓFunctor.map ((Scheme.Modules.pullback z).map
    (projectiveDifferential K projection h))).hom
      ((moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp z h).app M).inv).hom
        (ratioDifferential (ULift.{u} ℤ) n K (z ≫ h) i hp j)) = _
  rw [hi,pulledSection_naturality]
  have hd := relativeDifferentialsMap_app_d
    (f := h) (p := integralProjection n) (p' := projection)
    (specULiftZIsTerminal.from (Spec (.of K))) (specULiftZIsTerminal.hom_ext _ _) D
      (chartFracSection (ULift.{u} ℤ) n i j)
  rw [Adjunction.homEquiv_unit] at hd
  change (projectiveDifferential K projection h).app U
      (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).app D s) =
    (universalRelativeDerivation projection).d
      ((h.app D).hom (chartFracSection (ULift.{u} ℤ) n i j)) at hd
  have hu : Scheme.Modules.pullbackSection h M D U le_rfl s =
      ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).app D s := by
    change (((Scheme.Modules.pullback h).obj M).presheaf.map (𝟙 (op U))).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).app D s) = _
    exact CategoryTheory.Functor.map_id_apply _ _ _
  rw [hu]
  exact congrArg (pulledSection K z (relativeDifferentials projection) U hp) hd

/-- The product rule in the actual native cotangent space, with all
values and differentials of the original coordinate functions retained. -/
theorem cleared_differential (j : Fin (n+1)) :
    coordinateValue K z h e i • ratioDerivative K z projection h i hp j +
      ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) n K (z ≫ h) i hp j •
        pointDerivative K z projection (framedCoordinate h e i) =
      pointDerivative K z projection (framedCoordinate h e j) := by
  let D : (projectiveSpaceAtUniverse.{u} n).Opens :=
    ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)
  let U := h ⁻¹ᵁ D
  have hp' : z.base (point K) ∈ U := hp
  have hs := LagrangianProjectiveRatio.framed_ratio_product h e i j
  have hd := congrArg (fun s => (universalRelativeDerivation projection).d s) hs
  rw [(universalRelativeDerivation projection).d_mul] at hd
  have hz := congrArg (pulledSection K z (relativeDifferentials projection) U hp') hd
  rw [pulledSection_add,pulledSection_smul,pulledSection_smul,
    pointDerivative_local,pointDerivative_local,valueOn_res] at hz
  have hr : valueOn K z U hp'
      ((h.app D).hom (chartFracSection (ULift.{u} ℤ) n i j)) =
        ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) n K (z ≫ h) i hp j := by
    rw [ProjectiveEulerFieldPoint.ratio,
      ← germ_chartFracSection_coordRatio K (ULift.{u} ℤ) n (z ≫ h) i hp j,
      evaluation_germ K (ULift.{u} ℤ) n (z ≫ h) D hp
        (chartFracSection (ULift.{u} ℤ) n i j)]
    apply congrArg (scalarEquiv K)
    exact (ConcreteCategory.congr_hom
      (Scheme.Hom.comp_appLE z h D ⊤ (preimageTop K (z ≫ h) D hp))
      (chartFracSection (ULift.{u} ℤ) n i j)).symm
  rw [hr] at hz
  exact (add_comm _ _).trans hz

theorem pointCotangentMap_basis (j : {j : Fin (n+1) // j ≠ i}) :
    pointCotangentMap K z projection h (cotangentBasis (ULift.{u} ℤ) n K (z ≫ h) i hp j) =
      (coordinateValue K z h e i ^ 2)⁻¹ •
        (coordinateValue K z h e i • pointDerivative K z projection (framedCoordinate h e j) -
          coordinateValue K z h e j • pointDerivative K z projection (framedCoordinate h e i)) := by
  rw [cotangentBasis_apply,pointCotangentMap_ratioDifferential]
  have hvi := coordinateValue_ne_zero K z h e i hp
  have hc := cleared_differential K z projection h e i hp j.1
  have hr := ratio_eq_coordinateValue_div K z h e i hp j.1
  have hc' := (eq_sub_iff_add_eq).mpr hc
  calc
    _ = (coordinateValue K z h e i)⁻¹ •
        (coordinateValue K z h e i • ratioDerivative K z projection h i hp j.1) := by
      rw [smul_smul,inv_mul_cancel₀ hvi,one_smul]
    _ = (coordinateValue K z h e i)⁻¹ •
        (pointDerivative K z projection (framedCoordinate h e j.1) -
          ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) n K (z ≫ h) i hp j.1 •
            pointDerivative K z projection (framedCoordinate h e i)) := congrArg _ hc'
    _ = _ := by
      rw [hr,smul_sub,smul_sub,smul_smul,smul_smul,smul_smul]
      congr 1
      · congr 1
        field_simp [hvi]
      · congr 1
        field_simp [hvi]

/-- Genuine pullback-congruence transport keeps the original named
projective point and its original basis. -/
def pointCotangentMapOfEq
    (π : space K ⟶ projectiveSpaceAtUniverse.{u} n) (hπ : π = z ≫ h) :
    cotangentSections (ULift.{u} ℤ) n K π →ₗ[K] Target K z projection :=
  (pointCotangentMap K z projection h).comp
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCongr hπ).app
      (relativeDifferentials (integralProjection n))).hom).hom

theorem pointCotangentMapOfEq_basis
    (π : space K ⟶ projectiveSpaceAtUniverse.{u} n) (hπ : π = z ≫ h)
    (hπi : image (ULift.{u} ℤ) n K π ∈
      ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))
    (j : {j : Fin (n+1) // j ≠ i}) :
    pointCotangentMapOfEq K z projection h π hπ
        (cotangentBasis (ULift.{u} ℤ) n K π i hπi j) =
      (coordinateValue K z h e i ^ 2)⁻¹ •
        (coordinateValue K z h e i • pointDerivative K z projection (framedCoordinate h e j) -
          coordinateValue K z h e j • pointDerivative K z projection (framedCoordinate h e i)) := by
  subst π
  simpa only [pointCotangentMapOfEq,Scheme.Modules.pullbackCongr,eqToIso_refl,
    Iso.app_hom,Iso.refl_hom,NatTrans.id_app,CategoryTheory.Functor.map_id,
    ModuleCat.hom_id,LinearMap.comp_id] using
      pointCotangentMap_basis K z projection h e i hπi j

end M9Native.ProjectiveRatioFieldDifferential
