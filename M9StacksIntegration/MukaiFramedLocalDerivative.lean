module

public import M9StacksIntegration.FieldPointDeterminantDifferential
public import M9StacksIntegration.FieldPointDualPairing
public import M9StacksIntegration.MukaiLocalCotangentPullback

/-!
# Local dual evaluation and an actual line frame

The local functional is pulled through the native dual base-change
map. In the actual line frame it is multiplication by an actual global
function. A genuine local pairing equal to one proves that function has
nonzero value at the point. These comparisons retain the original local
sections and the original field-point cotangent module.
The genuine local differential chain rule and Leibniz then prove
vanishing of the framed derivative from the actual ambient-local
derivative and the framed value, without a comparison premise.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.MukaiFramedLocalDerivative

open LagrangianFieldJetCoefficients

section LocalFrame

variable {A Y : Scheme.{u}} (h : A ⟶ Y) (L : Y.Modules)
  (U : Y.Opens) (hU : (⊤ : A.Opens) ≤ h ⁻¹ᵁ U)

/-- The original local dual section, pulled by the actual dual
base-change map and restricted to the whole source. -/
def localDual (τ : Γ(dualSheaf L,U)) :
    Γ(dualSheaf ((Scheme.Modules.pullback h).obj L),⊤) :=
  Scheme.Modules.Hom.app (X := A) (Stacks.Chow.pullbackDualMap h L) ⊤
    (Scheme.Modules.pullbackSection h (dualSheaf L) U ⊤ hU τ)

/-- The native dual pairing commutes with the genuine local pullback. -/
theorem evalAt_localDual (τ : Γ(dualSheaf L,U)) (m : Γ(L,U)) :
    evalAt ((Scheme.Modules.pullback h).obj L) (localDual h L U hU τ)
      (Scheme.Modules.pullbackSection h L U ⊤ hU m) =
        h.appLE U ⊤ hU (evalAt L τ m) := by
  let t := (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
    (dualSheaf L)).val.app (op U)) τ
  let v := (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app L).val.app (op U)) m
  let d : (Scheme.Modules.pullback h).obj (dualSheaf L) ⟶
      dualSheaf ((Scheme.Modules.pullback h).obj L) := Stacks.Chow.pullbackDualMap h L
  have hn := PresheafOfModules.naturality_apply d.val (homOfLE hU).op t
  have he := evalAt_map ((Scheme.Modules.pullback h).obj L) hU
    (d.app (h ⁻¹ᵁ U) t) v
  have hu : evalAt ((Scheme.Modules.pullback h).obj L) (d.app (h ⁻¹ᵁ U) t) v =
      h.app U (evalAt L τ m) :=
    LagrangianDualPullback.dualPullback_evaluation_unit h L U τ m
  change evalAt ((Scheme.Modules.pullback h).obj L)
    (d.app ⊤ (((Scheme.Modules.pullback h).obj (dualSheaf L)).presheaf.map
      (homOfLE hU).op t))
    (((Scheme.Modules.pullback h).obj L).presheaf.map (homOfLE hU).op v) = _
  exact (congrArg (fun a => evalAt ((Scheme.Modules.pullback h).obj L) a
    (((Scheme.Modules.pullback h).obj L).presheaf.map (homOfLE hU).op v)) hn).trans
      (he.trans (congrArg (fun a => A.presheaf.map (homOfLE hU).op a) hu))

/-- Restricting an original global section before local pullback gives
its original global pullback. -/
theorem pullbackSection_restrict_top (s : Γ(L,⊤)) :
    Scheme.Modules.pullbackSection h L U ⊤ hU
      (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) =
        pullbackGlobalSections h L s := by
  let η : L ⟶ (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback h).obj L) :=
    (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app L
  have hn := PresheafOfModules.naturality_apply η.val
    (homOfLE (show U ≤ ⊤ from le_top)).op s
  unfold Scheme.Modules.pullbackSection
  refine (congrArg (fun a => ((Scheme.Modules.pullback h).obj L).presheaf.map
    (homOfLE hU).op a) hn).trans ?_
  change ((Scheme.Modules.pullback h).obj L).presheaf.map (homOfLE hU).op
    (((Scheme.Modules.pullback h).obj L).presheaf.map
      ((TopologicalSpace.Opens.map h.base).map (homOfLE le_top)).op
      (η.val.app (op ⊤) s)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have hid : ((TopologicalSpace.Opens.map h.base).map (homOfLE (show U ≤ ⊤ from le_top))).op ≫
      (homOfLE hU).op = 𝟙 (op (⊤ : A.Opens)) := Subsingleton.elim _ _
  rw [hid]
  rfl

/-- The coefficient of an actual dual section in a genuine line frame. -/
def frameCoefficient {X : Scheme.{u}} (F : X.Modules)
    (e : F ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (α : Γ(dualSheaf F,⊤)) : Γ(X,⊤) :=
  evalAt F α (e.inv.app ⊤ (1 : Γ(X,⊤)))

/-- The genuine unit-sheaf frame coordinate, read as an actual
structure-sheaf function. -/
def frameValue {X : Scheme.{u}} (F : X.Modules)
    (e : F ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (t : Γ(F,⊤)) : Γ(X,⊤) := e.hom.app ⊤ t

/-- The actual functional is multiplication by its frame coefficient. -/
theorem evalAt_eq_frameCoefficient_mul {X : Scheme.{u}} (F : X.Modules)
    (e : F ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (α : Γ(dualSheaf F,⊤)) (t : Γ(F,⊤)) :
    evalAt F α t = frameCoefficient F e α * frameValue F e t := by
  have ht : e.inv.app ⊤ (frameValue F e t) = t :=
    congrArg (fun a : F ⟶ F => a.app ⊤ t) e.hom_inv_id
  have he (r : Γ(X,⊤)) : e.inv.app ⊤ r = r • e.inv.app ⊤ (1 : Γ(X,⊤)) := by
    have hr : (r : Γ(X,⊤)) = r • (1 : Γ(X,⊤)) := by simp
    calc
      _ = e.inv.app ⊤ (r • (1 : Γ(X,⊤))) := congrArg (e.inv.app ⊤) hr
      _ = _ := by rw [Scheme.Modules.Hom.app_smul]
  calc
    _ = evalAt F α (e.inv.app ⊤ (frameValue F e t)) := congrArg (evalAt F α) ht.symm
    _ = evalAt F α (frameValue F e t • e.inv.app ⊤ (1 : Γ(X,⊤))) :=
      congrArg (evalAt F α) (he _)
    _ = frameValue F e t * frameCoefficient F e α :=
      (evalAt_smul_right F _ α _).trans (smul_eq_mul _ _)
    _ = _ := mul_comm _ _

/-- The actual local equation is the frame multiplier times the actual
framed original global section. -/
theorem localEvaluation_eq_coefficient_mul
    (e : (Scheme.Modules.pullback h).obj L ≅
      (SheafOfModules.unit A.ringCatSheaf : A.Modules))
    (τ : Γ(dualSheaf L,U)) (s : Γ(L,⊤)) :
    h.appLE U ⊤ hU (evalAt L τ
      (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) =
        frameCoefficient ((Scheme.Modules.pullback h).obj L) e (localDual h L U hU τ) *
          frameValue ((Scheme.Modules.pullback h).obj L) e (pullbackGlobalSections h L s) := by
  rw [← evalAt_localDual h L U hU τ, pullbackSection_restrict_top h L U hU]
  exact evalAt_eq_frameCoefficient_mul _ e _ _

/-- A genuine local unit pairing forces the actual multiplier to have
nonzero value at the actual field point. -/
theorem frameCoefficient_value_ne_zero (K : Type u) [Field K]
    (z : Spec (.of K) ⟶ A)
    (e : (Scheme.Modules.pullback h).obj L ≅
      (SheafOfModules.unit A.ringCatSheaf : A.Modules))
    (τ : Γ(dualSheaf L,U)) (m : Γ(L,U)) (hm : evalAt L τ m = 1) :
    pointValue K z (frameCoefficient ((Scheme.Modules.pullback h).obj L) e
      (localDual h L U hU τ)) ≠ 0 := by
  have hp := evalAt_localDual h L U hU τ m
  rw [hm, map_one, evalAt_eq_frameCoefficient_mul _ e] at hp
  have hpoint := congrArg (pointValue K z) hp
  rw [map_mul,map_one] at hpoint
  intro hz
  rw [hz,zero_mul] at hpoint
  exact zero_ne_one hpoint

/-- Leibniz for arbitrary actual functions uses their actual point
values, so it needs no identity of base maps at the point. -/
theorem pointDerivative_mul (K : Type u) [Field K] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (u v : Γ(X,⊤)) :
    pointDerivative K q z (u*v) =
      pointValue K z u • pointDerivative K q z v +
        pointValue K z v • pointDerivative K q z u := by
  rw [pointDerivative_apply, (Scheme.Hom.universalRelativeDerivation q).d_mul,
    map_add, FieldPointDeterminantDifferential.pullback_smul_pointValue,
    FieldPointDeterminantDifferential.pullback_smul_pointValue]
  rfl

end LocalFrame

/-- Actual ambient-local derivative vanishing, together with the
actual framed value zero, implies the actual framed derivative zero.
The coefficient and its nonzero point value are derived from the
genuine local pairing equal to one. -/
theorem pointDerivative_eq_zero_of_local_dual_evaluation
    (K : Type u) [Field K] {A Y : Scheme.{u}}
    (b : Y ⟶ Spec (.of K)) (h : A ⟶ Y) (q : A ⟶ Spec (.of K))
    (hh : h ≫ b = q) (z : Spec (.of K) ⟶ A)
    (L : Y.Modules) (U : Y.Opens) (hU : (⊤ : A.Opens) ≤ h ⁻¹ᵁ U)
    (e : (Scheme.Modules.pullback h).obj L ≅
      (SheafOfModules.unit A.ringCatSheaf : A.Modules))
    (τ : Γ(dualSheaf L,U)) (m : Γ(L,U)) (hm : evalAt L τ m = 1)
    (s : Γ(L,⊤))
    (hv : pointValue K z (e.hom.app ⊤ (pullbackGlobalSections h L s)) = 0)
    (hd : SpecFieldPullbackSections.pulledSection K (z ≫ h)
      (Scheme.Hom.relativeDifferentials b) U
      (MukaiLocalCotangentPullback.point_mem K h z U hU)
      ((Scheme.Hom.universalRelativeDerivation b).d
        (evalAt L τ (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s))) = 0) :
    pointDerivative K q z (e.hom.app ⊤ (pullbackGlobalSections h L s)) = 0 := by
  have hu := frameCoefficient_value_ne_zero h L U hU K z e τ m hm
  have hv' : pointValue K z
      (frameValue ((Scheme.Modules.pullback h).obj L) e (pullbackGlobalSections h L s)) = 0 := hv
  have hd' := MukaiLocalCotangentPullback.pointDerivative_eq_zero_of_pulled_d_eq_zero
    K b h q hh z U hU
      (evalAt L τ (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) hd
  rw [localEvaluation_eq_coefficient_mul h L U hU e τ s,
    pointDerivative_mul K q z, hv', zero_smul, add_zero] at hd'
  exact (smul_eq_zero.mp hd').resolve_left hu

end M9Native.MukaiFramedLocalDerivative
