module

public import M9StacksIntegration.LagrangianProjectiveRatio
public import M9StacksIntegration.ProjectiveEulerFieldPoint

/-! Native projective chart ratios at actual field-valued points, read
in any actual O(1) frame. The nonzero denominator is derived from the
true chart membership and the native nonvanishing locus. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
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

namespace M9Native.ProjectiveRatioFieldValues

open SpecFieldStalkSections SpecFieldPullbackSections ProjectiveEulerFieldPoint
open LinearIncidenceTensorCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

def scalarEquiv : Γ(space K,⊤) ≃+* K :=
  (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv

theorem scalarStalkEquiv_scalarEquiv (s : Γ(space K,⊤)) :
    scalarStalkEquiv K (scalarEquiv K s) =
      ((space K).presheaf.germ ⊤ (point K) trivial).hom s := by
  rw [scalarStalkEquiv_apply]
  change ((space K).presheaf.germ ⊤ (point K) trivial).hom
    ((scalarEquiv K).symm (scalarEquiv K s)) = _
  rw [RingEquiv.symm_apply_apply]

variable {T : Scheme.{u}} (z : space K ⟶ T)

def value (s : Γ(T,⊤)) : K := scalarEquiv K (z.appTop s)

def valueOn (U : T.Opens) (hz : z.base (point K) ∈ U) (s : Γ(T,U)) : K :=
  scalarEquiv K (z.appLE U ⊤ (preimageTop K z U hz) s)

theorem valueOn_res (U : T.Opens) (hz : z.base (point K) ∈ U) (s : Γ(T,⊤)) :
    valueOn K z U hz ((T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) =
      value K z s := by
  apply congrArg (scalarEquiv K)
  exact ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE z (preimageTop K z U hz) (homOfLE (le_top : U ≤ ⊤)).op) s

theorem evaluation_germ (R : Type u) [CommRing R] (n : ℕ)
    (q : space K ⟶ projectiveSpace R n) (U : (projectiveSpace R n).Opens)
    (hq : q.base (point K) ∈ U) (s : Γ(projectiveSpace R n,U)) :
    ProjectiveEulerFieldPoint.evaluation R n K q
      (((projectiveSpace R n).presheaf.germ U (q.base (point K)) hq).hom s) =
        valueOn K q U hq s := by
  apply (scalarStalkEquiv K).injective
  change scalarStalkEquiv K ((scalarStalkEquiv K).symm
    ((q.stalkMap (point K)).hom _)) =
      scalarStalkEquiv K (scalarEquiv K
        (q.appLE U ⊤ (preimageTop K q U hq) s))
  rw [RingEquiv.apply_symm_apply,scalarStalkEquiv_scalarEquiv]
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact ((space K).presheaf.germ_res_apply
    (homOfLE (preimageTop K q U hq)) (point K) trivial ((q.app U).hom s)).symm

/-- This equality holds for every homogeneous coordinate, including the
pivot; it is proved inside the actual native projective local ring. -/
theorem germ_chartFracSection_coordRatio (R : Type u) [CommRing R] (n : ℕ)
    (q : space K ⟶ projectiveSpace R n) (i : Fin (n+1))
    (hq : image R n K q ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (j : Fin (n+1)) :
    (((projectiveSpace R n).presheaf.germ
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
        (image R n K q) hq).hom (chartFracSection R n i j)) =
      coordRatio R n (image R n K q) i (chartNonzero R n K q i hq) j := by
  apply (AlgebraicGeometry.Proj.stalkIso' (polyGrading R n) (image R n K q)).injective
  apply HomogeneousLocalization.val_injective
  exact (congrArg HomogeneousLocalization.val
    (AlgebraicGeometry.Proj.stalkIso'_germ (polyGrading R n)
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
      (image R n K q) hq (chartFracSection R n i j))).trans
    ((chartFracSection_val R n i j ⟨image R n K q,hq⟩).trans
      (val_coordRatio R n (image R n K q) i (chartNonzero R n K q i hq) j).symm)

section Projective

variable {n : ℕ} (h : T ⟶ projectiveSpaceAtUniverse.{u} n)
variable (e : (Scheme.Modules.pullback h).obj (twistingSheafAtUniverse.{u} n) ≅
  SheafOfModules.unit T.ringCatSheaf)

def framedCoordinate (j : Fin (n+1)) : Γ(T,⊤) :=
  unitCoordinate T (e.hom.app ⊤ (pullbackCoordSection h j))

def coordinateValue (j : Fin (n+1)) : K := value K z (framedCoordinate h e j)

variable (i : Fin (n+1))
variable (hp : image (ULift.{u} ℤ) n K (z ≫ h) ∈
  ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))

include hp in
theorem coordinateValue_ne_zero : coordinateValue K z h e i ≠ 0 := by
  intro hzero
  let M := (Scheme.Modules.pullback h).obj (twistingSheafAtUniverse.{u} n)
  let s := pullbackCoordSection h i
  let eP := LineFramePullback.pullbackFrame z M e
  have hnv : point K ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback z).obj M) (pullbackGlobalSections z M s) :=
    mem_nonvanishingLocus_pullbackGlobalSections z M s
      (mem_nonvanishingLocus_pullbackGlobalSections h _ _
        (mem_nonvanishingLocus_coordGlobalSection i hp))
  have hzero' : z.appTop (framedCoordinate h e i) = 0 :=
    (scalarEquiv K).injective (hzero.trans (map_zero _).symm)
  have he := LineFramePullback.pullbackFrame_coordinate z M e s
  have ht : eP.hom.app ⊤ (pullbackGlobalSections z M s) = 0 := by
    change unitCoordinate (space K) (eP.hom.app ⊤ (pullbackGlobalSections z M s)) = 0
    exact he.trans hzero'
  have hs : pullbackGlobalSections z M s = 0 := by
    have hh := congrArg (fun t => eP.inv.app ⊤ t) ht
    have hid := congrArg (fun a => a.app ⊤ (pullbackGlobalSections z M s)) eP.hom_inv_id
    change eP.inv.app ⊤ (eP.hom.app ⊤ (pullbackGlobalSections z M s)) =
      eP.inv.app ⊤ 0 at hh
    exact hid.symm.trans (hh.trans (map_zero _))
  rw [hs,Stacks.Ample.nonvanishingLocus_zero] at hnv
  exact hnv

theorem ratio_mul_coordinateValue (j : Fin (n+1)) :
    ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) n K (z ≫ h) i hp j *
        coordinateValue K z h e i = coordinateValue K z h e j := by
  let D : (projectiveSpaceAtUniverse.{u} n).Opens :=
    ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)
  let U := h ⁻¹ᵁ D
  have hz : z.base (point K) ∈ U := hp
  have hr : ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) n K (z ≫ h) i hp j =
      valueOn K z U hz ((h.app D).hom (chartFracSection (ULift.{u} ℤ) n i j)) := by
    rw [ProjectiveEulerFieldPoint.ratio,
      ← germ_chartFracSection_coordRatio K (ULift.{u} ℤ) n (z ≫ h) i hp j,
      evaluation_germ K (ULift.{u} ℤ) n (z ≫ h) D hp
        (chartFracSection (ULift.{u} ℤ) n i j)]
    apply congrArg (scalarEquiv K)
    exact ConcreteCategory.congr_hom
      (Scheme.Hom.comp_appLE z h D ⊤ (preimageTop K (z ≫ h) D hp))
      (chartFracSection (ULift.{u} ℤ) n i j)
  have hs := LagrangianProjectiveRatio.framed_ratio_product h e i j
  have hv := congrArg (fun a => valueOn K z U hz a) hs
  change valueOn K z U hz
      ((h.app D).hom (chartFracSection (ULift.{u} ℤ) n i j) *
        (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (framedCoordinate h e i)) =
    valueOn K z U hz
      ((T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (framedCoordinate h e j)) at hv
  change (scalarEquiv K) ((z.appLE U ⊤ (preimageTop K z U hz)).hom (_ * _)) = _ at hv
  rw [map_mul,map_mul] at hv
  change valueOn K z U hz ((h.app D).hom (chartFracSection (ULift.{u} ℤ) n i j)) *
      valueOn K z U hz
        ((T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (framedCoordinate h e i)) =
    valueOn K z U hz
      ((T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (framedCoordinate h e j)) at hv
  rw [← hr,valueOn_res,valueOn_res] at hv
  exact hv

theorem ratio_eq_coordinateValue_div (j : Fin (n+1)) :
    ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) n K (z ≫ h) i hp j =
      coordinateValue K z h e j / coordinateValue K z h e i :=
  (eq_div_iff (coordinateValue_ne_zero K z h e i hp)).mpr
    (ratio_mul_coordinateValue K z h e i hp j)

/-- The original named point may use another parenthesization of the
same native composite; the ratio identity keeps that literal point. -/
theorem ratio_eq_coordinateValue_div_of_eq
    (π : space K ⟶ projectiveSpaceAtUniverse.{u} n) (hπ : π = z ≫ h)
    (hπi : image (ULift.{u} ℤ) n K π ∈
      ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))
    (j : Fin (n+1)) :
    ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) n K π i hπi j =
      coordinateValue K z h e j / coordinateValue K z h e i := by
  subst π
  exact ratio_eq_coordinateValue_div K z h e i hπi j

end Projective

end M9Native.ProjectiveRatioFieldValues
