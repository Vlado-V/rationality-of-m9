module

public import M9StacksIntegration.SymmetricSquareDualSections
public import M9StacksIntegration.SymmetricSquareExteriorPairing

/-!
# Actual exterior power of the dual and dual of the exterior power

The original section evaluation pairing induces the determinant pairing.
On genuine free opens this is a perfect pairing, and its canonical
restriction equations glue the actual native sheaf isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant
open M9Native.SymmetricSquareBundleDeterminant
open M9Native.SymmetricSquareDualSections

universe u

namespace M9Native.SymmetricSquareExteriorDuality

variable {X : Scheme.{u}}

/-- The true dual frame supplied by the original free frame. -/
def dualFrame (F : X.Modules) (W : X.Opens) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    (dualSheaf F).over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I :=
  (freeIsoDualSheafOver X W F e.symm).symm

/-- The actual perfect exterior pairing on the original section modules. -/
def pairingEquivOn (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) (n : ℕ) :
    (⋀[Γ(X, U)]^n Γ(dualSheaf F, U)) ≃ₗ[Γ(X, U)]
      Module.Dual Γ(X, U) (⋀[Γ(X, U)]^n Γ(F, U)) := by
  letI := moduleFreeOn F W U h I e
  letI := moduleFiniteOn F W U h I e
  exact (exteriorCongr n (dualSectionsEquivOn F W U h I e)).trans
    (LinearEquiv.ofBijective (exteriorPower.pairingDual Γ(X, U) Γ(F, U) n)
      (exteriorPower.bijective_pairingDual Γ(X, U) Γ(F, U) n))

@[simp] theorem pairingEquivOn_apply (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (n : ℕ) (x : ⋀[Γ(X, U)]^n Γ(dualSheaf F, U)) :
    pairingEquivOn F W U h I e n x = exteriorPower.pairingDual Γ(X, U) Γ(F, U) n
      (exteriorPower.map n (dualSectionsMap F U) x) := rfl

/-- The genuine local exterior-dual isomorphism. -/
def localExteriorDualIso (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) (n : ℕ) :
    Γ(topExterior (dualSheaf F) n, U) ≃ₗ[Γ(X, U)] Γ(dualSheaf (topExterior F n), U) :=
  (exteriorSectionsEquivOn (dualSheaf F) W U h I (dualFrame F W I e) n).symm.trans
    ((pairingEquivOn F W U h I e n).trans
      ((LinearEquiv.arrowCongr (exteriorSectionsEquivOn F W U h I e n)
        (LinearEquiv.refl Γ(X, U) Γ(X, U))).trans
          (dualSectionsEquivOn (topExterior F n) W U h (Set.powersetCard I n)
            (exteriorPowerFreeOn F W n I e)).symm))

/-- Its actual evaluation is precisely the genuine determinant pairing. -/
theorem localExteriorDualIso_eval (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (n : ℕ) (x : Γ(topExterior (dualSheaf F) n, U)) (y : ⋀[Γ(X, U)]^n Γ(F, U)) :
    dualSectionsMap (topExterior F n) U (localExteriorDualIso F W U h I e n x)
        (exteriorSectionComparison F n U y) =
      exteriorPower.pairingDual Γ(X, U) Γ(F, U) n
        (exteriorPower.map n (dualSectionsMap F U)
          ((exteriorSectionsEquivOn (dualSheaf F) W U h I (dualFrame F W I e) n).symm x)) y := by
  let s := exteriorSectionsEquivOn (dualSheaf F) W U h I (dualFrame F W I e) n
  let t := exteriorSectionsEquivOn F W U h I e n
  let d := dualSectionsEquivOn (topExterior F n) W U h (Set.powersetCard I n)
    (exteriorPowerFreeOn F W n I e)
  change d (d.symm (LinearEquiv.arrowCongr t (LinearEquiv.refl Γ(X, U) Γ(X, U))
    (pairingEquivOn F W U h I e n (s.symm x)))) (t y) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.arrowCongr_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.refl_apply, pairingEquivOn_apply]

/-- The canonical comparisons, rather than a chosen transition law, force overlap agreement. -/
theorem localExteriorDualIso_agree (F : X.Modules) (W₁ W₂ U : X.Opens)
    (h₁ : U ≤ W₁) (h₂ : U ≤ W₂)
    (I₁ I₂ : Type u) [Finite I₁] [Finite I₂]
    (e₁ : F.over W₁ ≅ SheafOfModules.free (R := X.ringCatSheaf.over W₁) I₁)
    (e₂ : F.over W₂ ≅ SheafOfModules.free (R := X.ringCatSheaf.over W₂) I₂) (n : ℕ) :
    localExteriorDualIso F W₁ U h₁ I₁ e₁ n = localExteriorDualIso F W₂ U h₂ I₂ e₂ n := by
  have hs : exteriorSectionsEquivOn (dualSheaf F) W₁ U h₁ I₁ (dualFrame F W₁ I₁ e₁) n =
      exteriorSectionsEquivOn (dualSheaf F) W₂ U h₂ I₂ (dualFrame F W₂ I₂ e₂) n := by
    apply LinearEquiv.ext
    intro x
    simp only [exteriorSectionsEquivOn_apply]
  apply LinearEquiv.ext
  intro x
  apply (dualSectionsEquivOn (topExterior F n) W₁ U h₁ (Set.powersetCard I₁ n)
    (exteriorPowerFreeOn F W₁ n I₁ e₁)).injective
  simp only [dualSectionsEquivOn_apply]
  apply LinearMap.ext
  intro y
  obtain ⟨z, hz⟩ := (exteriorSectionsEquivOn F W₁ U h₁ I₁ e₁ n).surjective y
  have hsc := DFunLike.congr_fun (congrArg LinearEquiv.symm hs) x
  have hp := congrArg
    (fun v => exteriorPower.pairingDual Γ(X, U) Γ(F, U) n
      (exteriorPower.map n (dualSectionsMap F U) v) z) hsc
  have he : exteriorSectionComparison F n U z = y :=
    (exteriorSectionsEquivOn_apply F W₁ U h₁ I₁ e₁ n z).symm.trans hz
  exact (congrArg (fun v => dualSectionsMap (topExterior F n) U
      (localExteriorDualIso F W₁ U h₁ I₁ e₁ n x) v) he).symm.trans
    ((localExteriorDualIso_eval F W₁ U h₁ I₁ e₁ n x z).trans
      (hp.trans ((localExteriorDualIso_eval F W₂ U h₂ I₂ e₂ n x z).symm.trans
        (congrArg (fun v => dualSectionsMap (topExterior F n) U
          (localExteriorDualIso F W₂ U h₂ I₂ e₂ n x) v) he))))

/-- Restriction of the actual local determinant-dual maps follows from
original evaluation and the determinant pairing, tested on the original top basis. -/
theorem localExteriorDualIso_restrict (F : X.Modules) (W U V : X.Opens)
    (hVU : V ≤ U) (hUW : U ≤ W) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (η : I ≃ Fin 3) (x : Γ(topExterior (dualSheaf F) 3, U)) :
    (dualSheaf (topExterior F 3)).presheaf.map (homOfLE hVU).op
        (localExteriorDualIso F W U hUW I e 3 x) =
      localExteriorDualIso F W V (hVU.trans hUW) I e 3
        ((topExterior (dualSheaf F) 3).presheaf.map (homOfLE hVU).op x) := by
  let φ := (X.presheaf.map (homOfLE hVU).op).hom
  let f : Γ(F, U) →ₛₗ[φ] Γ(F, V) := F.val.restrictₛₗ (homOfLE hVU).op
  let g : Γ(dualSheaf F, U) →ₛₗ[φ] Γ(dualSheaf F, V) :=
    (dualSheaf F).val.restrictₛₗ (homOfLE hVU).op
  let bU := frameBasis F W U hUW I e η
  let bV := frameBasis F W V (hVU.trans hUW) I e η
  let yU := exteriorPower.ιMulti Γ(X, U) 3 bU
  let yV := exteriorPower.ιMulti Γ(X, V) 3 bV
  let sU := exteriorSectionsEquivOn (dualSheaf F) W U hUW I (dualFrame F W I e) 3
  let sV := exteriorSectionsEquivOn (dualSheaf F) W V (hVU.trans hUW) I (dualFrame F W I e) 3
  let xP := sU.symm x
  let xV := (topExterior (dualSheaf F) 3).presheaf.map (homOfLE hVU).op x
  let isoU := localExteriorDualIso F W U hUW I e 3
  let isoV := localExteriorDualIso F W V (hVU.trans hUW) I e 3
  let aV := (dualSheaf (topExterior F 3)).presheaf.map (homOfLE hVU).op (isoU x)
  have hxU : exteriorSectionComparison (dualSheaf F) 3 U xP = x :=
    (exteriorSectionsEquivOn_apply (dualSheaf F) W U hUW I (dualFrame F W I e) 3 xP).symm.trans
      (sU.apply_symm_apply x)
  have hxV : sV (ExteriorAlgebra.powMapₛₗ 3 φ g xP) = xV :=
    (exteriorSectionsEquivOn_apply (dualSheaf F) W V (hVU.trans hUW) I
      (dualFrame F W I e) 3 _).trans
        ((exteriorSectionComparison_restrict (dualSheaf F) 3 U V hVU xP).symm.trans
          (congrArg ((topExterior (dualSheaf F) 3).presheaf.map (homOfLE hVU).op) hxU))
  have hxP : ExteriorAlgebra.powMapₛₗ 3 φ g xP = sV.symm xV :=
    (sV.symm_apply_apply _).symm.trans (congrArg sV.symm hxV)
  have hb : ExteriorAlgebra.powMapₛₗ 3 φ f yU = yV := by
    rw [ExteriorAlgebra.powMapₛₗ_ιMulti]
    congr 1
    funext i
    exact frameBasis_restrict F W U V hVU hUW I e η i
  have hy : (topExterior F 3).presheaf.map (homOfLE hVU).op
      (exteriorSectionComparison F 3 U yU) = exteriorSectionComparison F 3 V yV :=
    (exteriorSectionComparison_restrict F 3 U V hVU yU).trans
      (congrArg (exteriorSectionComparison F 3 V) hb)
  have hp := SymmetricSquareExteriorPairing.pairing_semilinear
    (R := Γ(X, U)) (S := Γ(X, V)) (M := Γ(F, U)) (N := Γ(F, V))
    (A := Γ(dualSheaf F, U)) (B := Γ(dualSheaf F, V))
    φ f g (dualSectionsMap F U) (dualSectionsMap F V)
    (fun a m => dualSectionsMap_restrict F U V hVU a m) 3 xP yU
  have htop : dualSectionsMap (topExterior F 3) V aV (exteriorSectionComparison F 3 V yV) =
      dualSectionsMap (topExterior F 3) V (isoV xV) (exteriorSectionComparison F 3 V yV) := by
    calc
      _ = dualSectionsMap (topExterior F 3) V aV
          ((topExterior F 3).presheaf.map (homOfLE hVU).op
            (exteriorSectionComparison F 3 U yU)) :=
        congrArg (dualSectionsMap (topExterior F 3) V aV) hy.symm
      _ = φ (dualSectionsMap (topExterior F 3) U (isoU x)
          (exteriorSectionComparison F 3 U yU)) :=
        dualSectionsMap_restrict (topExterior F 3) U V hVU (isoU x) _
      _ = φ (exteriorPower.pairingDual Γ(X, U) Γ(F, U) 3
          (exteriorPower.map 3 (dualSectionsMap F U) xP) yU) :=
        congrArg φ (localExteriorDualIso_eval F W U hUW I e 3 x yU)
      _ = exteriorPower.pairingDual Γ(X, V) Γ(F, V) 3
          (exteriorPower.map 3 (dualSectionsMap F V) (ExteriorAlgebra.powMapₛₗ 3 φ g xP))
          (ExteriorAlgebra.powMapₛₗ 3 φ f yU) := hp.symm
      _ = exteriorPower.pairingDual Γ(X, V) Γ(F, V) 3
          (exteriorPower.map 3 (dualSectionsMap F V) (sV.symm xV)) yV :=
        congrArg₂ (fun a b => exteriorPower.pairingDual Γ(X, V) Γ(F, V) 3
          (exteriorPower.map 3 (dualSectionsMap F V) a) b) hxP hb
      _ = _ := (localExteriorDualIso_eval F W V (hVU.trans hUW) I e 3 xV yV).symm
  have hfun : (dualSectionsMap (topExterior F 3) V aV).comp
        (exteriorSectionComparison F 3 V) =
      (dualSectionsMap (topExterior F 3) V (isoV xV)).comp (exteriorSectionComparison F 3 V) := by
    apply (Stacks.ExteriorPower.topBasis bV).ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [LinearMap.comp_apply, Stacks.ExteriorPower.topBasis_apply] using htop
  apply (dualSectionsEquivOn (topExterior F 3) W V (hVU.trans hUW) (Set.powersetCard I 3)
    (exteriorPowerFreeOn F W 3 I e)).injective
  simp only [dualSectionsEquivOn_apply]
  apply LinearMap.ext
  intro z
  obtain ⟨y, hy⟩ := (exteriorSectionsEquivOn F W V (hVU.trans hUW) I e 3).surjective z
  have he : exteriorSectionComparison F 3 V y = z :=
    (exteriorSectionsEquivOn_apply F W V (hVU.trans hUW) I e 3 y).symm.trans hy
  exact (congrArg (dualSectionsMap (topExterior F 3) V aV) he).symm.trans
    ((DFunLike.congr_fun hfun y).trans (congrArg (dualSectionsMap (topExterior F 3) V (isoV xV)) he))

/-- The actual native determinant of the dual is the actual native dual determinant.
Every local compatibility is derived from original evaluation, not supplied as data. -/
def topExteriorDualIso (F : X.Modules)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3] :
    topExterior (dualSheaf F) 3 ≅ dualSheaf (topExterior F 3) := by
  classical
  let hdata := hF.exists_isFiniteLocallyFreeOfRankData
  let q := Classical.choose hdata
  have hq := Classical.choose_spec hdata
  let η (i : q.I) := Classical.choice (hq.2 i)
  letI : ∀ i : q.I, Finite (q.generators i).I :=
    fun i => Finite.of_equiv (Fin 3) (η i).symm
  let e (i : q.I) : F.over (q.X i) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (q.X i)) (q.generators i).I := by
    letI : IsIso (q.generators i).π := hq.1.isIso i
    exact (asIso (q.generators i).π).symm
  have hcov : ∀ x : X, ∃ i : q.I, x ∈ q.X i :=
    fun x => ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  let t (i : q.I) (U : X.Opens) (h : U ≤ q.X i) :=
    localExteriorDualIso F (q.X i) U h (q.generators i).I (e i) 3
  exact glueLocalLinearEquivs (topExterior (dualSheaf F) 3) (dualSheaf (topExterior F 3))
    q.X hcov t
    (fun i U V hVU hUW x => localExteriorDualIso_restrict F (q.X i) U V hVU hUW
      (q.generators i).I (e i) (η i) x)
    (fun i j U hi hj => localExteriorDualIso_agree F (q.X i) (q.X j) U hi hj
      (q.generators i).I (q.generators j).I (e i) (e j) 3)

end M9Native.SymmetricSquareExteriorDuality
