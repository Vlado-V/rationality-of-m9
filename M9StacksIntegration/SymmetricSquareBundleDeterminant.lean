module

public import M9StacksIntegration.SymmetricSquareFreeFrames
public import M9StacksIntegration.SymmetricSquareDeterminantNaturality
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictGlue

/-! Actual global determinant-line gluing for the native symmetric square. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.SymmetricSquareBundleDeterminant

variable {X : Scheme.{u}}

abbrev sourceLine (F : X.Modules) : X.Modules := topExterior (symmetricSquare F) 6

abbrev symmetricTargetLine (F : X.Modules) : X.Modules :=
  (Scheme.Modules.symmetricAlgebra X (topExterior F 3)).piece 4

/-- The actual local top-line isomorphism formed from the original
frame and the canonical native section comparisons. -/
def localLineIso (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (η : I ≃ Fin 3) : Γ(sourceLine F, U) ≃ₗ[Γ(X, U)] Γ(symmetricTargetLine F, U) :=
  (sourceSectionsEquiv F W U h I e).symm.trans
    ((SymmetricSquareDeterminantLinear.basisIso Γ(X, U) (frameBasis F W U h I e η)).trans
      (targetSectionsEquiv F W U h I e))

@[simp] theorem localLineIso_apply (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (η : I ≃ Fin 3) (x : Γ(sourceLine F, U)) :
    localLineIso F W U h I e η x = targetSectionsEquiv F W U h I e
      (SymmetricSquareDeterminantLinear.basisIso Γ(X, U) (frameBasis F W U h I e η)
        ((sourceSectionsEquiv F W U h I e).symm x)) := by
  simp only [localLineIso, LinearEquiv.trans_apply]

/-- Agreement on overlaps is a consequence of the genuine normalized
determinant character and the canonical comparisons. -/
theorem localLineIso_agree (F : X.Modules) (W₁ W₂ U : X.Opens)
    (h₁ : U ≤ W₁) (h₂ : U ≤ W₂)
    (I₁ I₂ : Type u) [Finite I₁] [Finite I₂]
    (e₁ : F.over W₁ ≅ SheafOfModules.free (R := X.ringCatSheaf.over W₁) I₁)
    (e₂ : F.over W₂ ≅ SheafOfModules.free (R := X.ringCatSheaf.over W₂) I₂)
    (η₁ : I₁ ≃ Fin 3) (η₂ : I₂ ≃ Fin 3) [Invertible (2 : Γ(X, U))] :
    localLineIso F W₁ U h₁ I₁ e₁ η₁ = localLineIso F W₂ U h₂ I₂ e₂ η₂ := by
  have hs : sourceSectionsEquiv F W₁ U h₁ I₁ e₁ = sourceSectionsEquiv F W₂ U h₂ I₂ e₂ := by
    apply LinearEquiv.ext
    intro x
    simp only [sourceSectionsEquiv_apply]
  have ht : targetSectionsEquiv F W₁ U h₁ I₁ e₁ = targetSectionsEquiv F W₂ U h₂ I₂ e₂ := by
    apply LinearEquiv.ext
    intro x
    simp only [targetSectionsEquiv_apply]
  have hb := SymmetricSquareDeterminantLinear.basisIso_independent Γ(X, U)
    (frameBasis F W₁ U h₁ I₁ e₁ η₁) (frameBasis F W₂ U h₂ I₂ e₂ η₂)
  apply LinearEquiv.ext
  intro x
  have hsx := DFunLike.congr_fun (congrArg LinearEquiv.symm hs) x
  have hbx := (congrArg
      (SymmetricSquareDeterminantLinear.basisIso Γ(X, U) (frameBasis F W₁ U h₁ I₁ e₁ η₁))
      hsx).trans (DFunLike.congr_fun hb ((sourceSectionsEquiv F W₂ U h₂ I₂ e₂).symm x))
  have htx := (congrArg (targetSectionsEquiv F W₁ U h₁ I₁ e₁) hbx).trans
    (DFunLike.congr_fun ht
      (SymmetricSquareDeterminantLinear.basisIso Γ(X, U) (frameBasis F W₂ U h₂ I₂ e₂ η₂)
        ((sourceSectionsEquiv F W₂ U h₂ I₂ e₂).symm x)))
  exact (localLineIso_apply F W₁ U h₁ I₁ e₁ η₁ x).trans
    (htx.trans (localLineIso_apply F W₂ U h₂ I₂ e₂ η₂ x).symm)

theorem sourceSectionsEquiv_restrict (F : X.Modules) (W U V : X.Opens)
    (hVU : V ≤ U) (hUW : U ≤ W) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (x : SymmetricSquareDeterminantLinear.Source Γ(X, U) Γ(F, U)) :
    (sourceLine F).presheaf.map (homOfLE hVU).op (sourceSectionsEquiv F W U hUW I e x) =
      sourceSectionsEquiv F W V (hVU.trans hUW) I e
        (SymmetricSquareDeterminantLinear.sourceMapSL
          (X.presheaf.map (homOfLE hVU).op).hom (F.val.restrictₛₗ (homOfLE hVU).op) x) := by
  simp only [sourceSectionsEquiv_apply]
  have hfirst := exteriorSectionComparison_restrict (symmetricSquare F) 6 U V hVU
    (exteriorPower.map 6 (symmetricSectionComparison F 2 U) x)
  have hsecond := congrArg (exteriorSectionComparison (symmetricSquare F) 6 V)
    (SymmetricSquareDeterminantLinear.exterior_commutingSquare
      (R := Γ(X, U)) (S := Γ(X, V))
      (M := SymPow.symmetricPower 2 Γ(X, U) Γ(F, U))
      (M' := Γ(symmetricSquare F, U))
      (N := SymPow.symmetricPower 2 Γ(X, V) Γ(F, V))
      (N' := Γ(symmetricSquare F, V))
      (X.presheaf.map (homOfLE hVU).op).hom
      (SymPow.symMapₛₗ 2 (X.presheaf.map (homOfLE hVU).op).hom
        (F.val.restrictₛₗ (homOfLE hVU).op))
      ((symmetricSquare F).val.restrictₛₗ (homOfLE hVU).op)
      (symmetricSectionComparison F 2 U) (symmetricSectionComparison F 2 V)
      (fun y => symmetricSectionComparison_restrict F 2 U V hVU y) 6 x)
  exact hfirst.trans hsecond

theorem targetSectionsEquiv_restrict (F : X.Modules) (W U V : X.Opens)
    (hVU : V ≤ U) (hUW : U ≤ W) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (x : SymmetricSquareDeterminantLinear.Target Γ(X, U) Γ(F, U)) :
    (symmetricTargetLine F).presheaf.map (homOfLE hVU).op (targetSectionsEquiv F W U hUW I e x) =
      targetSectionsEquiv F W V (hVU.trans hUW) I e
        (SymmetricSquareDeterminantLinear.targetMapSL
          (X.presheaf.map (homOfLE hVU).op).hom (F.val.restrictₛₗ (homOfLE hVU).op) x) := by
  simp only [targetSectionsEquiv_apply]
  have hfirst := symmetricSectionComparison_restrict (topExterior F 3) 4 U V hVU
    (SymPow.symMap 4 (exteriorSectionComparison F 3 U) x)
  have hsecond := congrArg (symmetricSectionComparison (topExterior F 3) 4 V)
    (SymmetricSquareDeterminantLinear.symmetric_commutingSquare
      (R := Γ(X, U)) (S := Γ(X, V))
      (M := ⋀[Γ(X, U)]^3 Γ(F, U)) (M' := Γ(topExterior F 3, U))
      (N := ⋀[Γ(X, V)]^3 Γ(F, V)) (N' := Γ(topExterior F 3, V))
      (X.presheaf.map (homOfLE hVU).op).hom
      (ExteriorAlgebra.powMapₛₗ 3 (X.presheaf.map (homOfLE hVU).op).hom
        (F.val.restrictₛₗ (homOfLE hVU).op))
      ((topExterior F 3).val.restrictₛₗ (homOfLE hVU).op)
      (exteriorSectionComparison F 3 U) (exteriorSectionComparison F 3 V)
      (fun y => exteriorSectionComparison_restrict F 3 U V hVU y) 4 x)
  exact hfirst.trans hsecond

/-- Restriction compatibility is derived from the actual frame and
the semilinear naturality of the polynomial operations. -/
theorem localLineIso_restrict (F : X.Modules) (W U V : X.Opens)
    (hVU : V ≤ U) (hUW : U ≤ W) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (η : I ≃ Fin 3) (x : Γ(sourceLine F, U)) :
    (symmetricTargetLine F).presheaf.map (homOfLE hVU).op
        (localLineIso F W U hUW I e η x) =
      localLineIso F W V (hVU.trans hUW) I e η
        ((sourceLine F).presheaf.map (homOfLE hVU).op x) := by
  let sU := sourceSectionsEquiv F W U hUW I e
  let sV := sourceSectionsEquiv F W V (hVU.trans hUW) I e
  let tU := targetSectionsEquiv F W U hUW I e
  let tV := targetSectionsEquiv F W V (hVU.trans hUW) I e
  let bU := frameBasis F W U hUW I e η
  let bV := frameBasis F W V (hVU.trans hUW) I e η
  let φ := (X.presheaf.map (homOfLE hVU).op).hom
  let f := F.val.restrictₛₗ (homOfLE hVU).op
  let y := sU.symm x
  have hy : sU y = x := sU.apply_symm_apply x
  have hs : sV (SymmetricSquareDeterminantLinear.sourceMapSL φ f y) =
      (sourceLine F).presheaf.map (homOfLE hVU).op x :=
    (sourceSectionsEquiv_restrict F W U V hVU hUW I e y).symm.trans
      (congrArg ((sourceLine F).presheaf.map (homOfLE hVU).op) hy)
  have hb := SymmetricSquareDeterminantLinear.basisIso_semilinear φ f bU bV
    (fun i => frameBasis_restrict F W U V hVU hUW I e η i) y
  have hs' : SymmetricSquareDeterminantLinear.sourceMapSL φ f y =
      sV.symm ((sourceLine F).presheaf.map (homOfLE hVU).op x) :=
    (sV.symm_apply_apply _).symm.trans (congrArg sV.symm hs)
  calc
    _ = (symmetricTargetLine F).presheaf.map (homOfLE hVU).op
        (tU (SymmetricSquareDeterminantLinear.basisIso Γ(X, U) bU y)) :=
      congrArg ((symmetricTargetLine F).presheaf.map (homOfLE hVU).op)
        (localLineIso_apply F W U hUW I e η x)
    _ = tV (SymmetricSquareDeterminantLinear.targetMapSL φ f
        (SymmetricSquareDeterminantLinear.basisIso Γ(X, U) bU y)) :=
      targetSectionsEquiv_restrict F W U V hVU hUW I e _
    _ = tV (SymmetricSquareDeterminantLinear.basisIso Γ(X, V) bV
        (SymmetricSquareDeterminantLinear.sourceMapSL φ f y)) := congrArg tV hb.symm
    _ = _ := (congrArg (fun z => tV (SymmetricSquareDeterminantLinear.basisIso Γ(X, V) bV z))
      hs').trans (localLineIso_apply F W V (hVU.trans hUW) I e η
        ((sourceLine F).presheaf.map (homOfLE hVU).op x)).symm

theorem localLineIso_symm_restrict (F : X.Modules) (W U V : X.Opens)
    (hVU : V ≤ U) (hUW : U ≤ W) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (η : I ≃ Fin 3) (y : Γ(symmetricTargetLine F, U)) :
    (sourceLine F).presheaf.map (homOfLE hVU).op
        ((localLineIso F W U hUW I e η).symm y) =
      (localLineIso F W V (hVU.trans hUW) I e η).symm
        ((symmetricTargetLine F).presheaf.map (homOfLE hVU).op y) := by
  apply (localLineIso F W V (hVU.trans hUW) I e η).injective
  rw [LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.apply_symm_apply] using
    (localLineIso_restrict F W U V hVU hUW I e η
      ((localLineIso F W U hUW I e η).symm y)).symm

/-- Invertibility of two on the scheme gives its actual invertibility
in the ring of functions on every open by the original restriction hom. -/
@[instance_reducible] def twoInvertibleOn [Invertible (2 : Γ(X, ⊤))] (U : X.Opens) :
    Invertible (2 : Γ(X, U)) := by
  let f := (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  exact
    { invOf := f (⅟ (2 : Γ(X, ⊤)))
      invOf_mul_self := by
        simpa only [map_mul, map_ofNat, map_one] using
          congrArg f (invOf_mul_self (2 : Γ(X, ⊤)))
      mul_invOf_self := by
        simpa only [map_mul, map_ofNat, map_one] using
          congrArg f (mul_invOf_self (2 : Γ(X, ⊤))) }

/-- Construct actual inverse sheaf maps from actual compatible local
linear equivalences. This isolates the native sheaf gluing from the
concrete symmetric/exterior operation types. -/
def glueLocalLinearEquivs {ι : Type u} (M N : X.Modules) (W : ι → X.Opens)
    (hcov : ∀ x : X, ∃ i : ι, x ∈ W i)
    (t : ∀ (i : ι) (U : X.Opens), U ≤ W i → Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U))
    (hres : ∀ (i : ι) (U V : X.Opens) (hVU : V ≤ U) (hUW : U ≤ W i) (x : Γ(M, U)),
      N.presheaf.map (homOfLE hVU).op (t i U hUW x) =
        t i V (hVU.trans hUW) (M.presheaf.map (homOfLE hVU).op x))
    (hagree : ∀ (i j : ι) (U : X.Opens) (hi : U ≤ W i) (hj : U ≤ W j),
      t i U hi = t j U hj) : M ≅ N := by
  have hinvres : ∀ (i : ι) (U V : X.Opens) (hVU : V ≤ U) (hUW : U ≤ W i) (y : Γ(N, U)),
      M.presheaf.map (homOfLE hVU).op ((t i U hUW).symm y) =
        (t i V (hVU.trans hUW)).symm (N.presheaf.map (homOfLE hVU).op y) := by
    intro i U V hVU hUW y
    apply (t i V (hVU.trans hUW)).injective
    rw [LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.apply_symm_apply] using
      (hres i U V hVU hUW ((t i U hUW).symm y)).symm
  let hforward := Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover
    (M := M) (N := N) W hcov (fun i U h x => t i U h x)
    (fun i U h x y => (t i U h).map_add x y)
    (fun i U h r x => (t i U h).map_smul r x)
    (fun i U V hUV hV x => (hres i V U hUV hV x).symm)
    (fun i j U hi hj x => DFunLike.congr_fun (hagree i j U hi hj) x)
  let hinverse := Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover
    (M := N) (N := M) W hcov (fun i U h x => (t i U h).symm x)
    (fun i U h x y => (t i U h).symm.map_add x y)
    (fun i U h r x => (t i U h).symm.map_smul r x)
    (fun i U V hUV hV x => (hinvres i V U hUV hV x).symm)
    (fun i j U hi hj x => DFunLike.congr_fun (congrArg LinearEquiv.symm (hagree i j U hi hj)) x)
  let f := Classical.choose hforward
  let g := Classical.choose hinverse
  have hf := Classical.choose_spec hforward
  have hg := Classical.choose_spec hinverse
  refine ⟨f, g, ?_, ?_⟩
  · apply Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_eq_of_cover W hcov
    intro i U hU
    ext x
    change g.app U (f.app U x) = x
    rw [hf i U hU, hg i U hU]
    exact (t i U hU).symm_apply_apply x
  · apply Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_eq_of_cover W hcov
    intro i U hU
    ext x
    change f.app U (g.app U x) = x
    rw [hg i U hU, hf i U hU]
    exact (t i U hU).apply_symm_apply x

/-- The actual global determinant-line isomorphism. The actual rank
condition supplies its cover and frames; all overlap and restriction
conditions are proved from the normalized determinant character. -/
def symmetricSquareDeterminantSymmetricIso (F : X.Modules)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3]
    [Invertible (2 : Γ(X, ⊤))] : sourceLine F ≅ symmetricTargetLine F := by
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
    localLineIso F (q.X i) U h (q.generators i).I (e i) (η i)
  have hagree : ∀ (i j : q.I) (U : X.Opens) (hi : U ≤ q.X i) (hj : U ≤ q.X j),
      t i U hi = t j U hj := by
    intro i j U hi hj
    letI := twoInvertibleOn (X := X) U
    exact localLineIso_agree F (q.X i) (q.X j) U hi hj
      (q.generators i).I (q.generators j).I (e i) (e j) (η i) (η j)
  exact glueLocalLinearEquivs (sourceLine F) (symmetricTargetLine F) q.X hcov t
    (fun i U V hVU hUW x => localLineIso_restrict F (q.X i) U V hVU hUW
      (q.generators i).I (e i) (η i) x) hagree

/-- The determinant of the actual native symmetric square of a
rank-three bundle is the actual fourth tensor power of its determinant. -/
def symmetricSquareDeterminantIso (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3]
    [Invertible (2 : Γ(X, ⊤))] :
    topExterior ((Scheme.Modules.symmetricAlgebra X F).piece 2) 6 ≅
      SheafOfModules.tensorPower (Opens.grothendieckTopology X) (topExterior F 3) 4 := by
  letI := Scheme.Modules.isInvertible_exteriorPower_self F 3
  exact symmetricSquareDeterminantSymmetricIso F ≪≫
    Stacks.SheafOfModules.symmetricPowerIsoTensorPowerOfIsInvertible X.sheaf (topExterior F 3)
      (nativeAlgebras (topExterior F 3)) 4

end M9Native.SymmetricSquareBundleDeterminant
