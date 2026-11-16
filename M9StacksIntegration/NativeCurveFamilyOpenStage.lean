module

public import M9StacksIntegration.NativeAffineOpenMembershipStage
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered

/-!
# Genuine open curve-family properties at a later affine stage

Given an ACTUAL family arrow to a stage of an ACTUAL affine limit, a
genuine open curve-family property at the limit holds at a later stage.
The later family and both arrows are constructed by the actual native
fibration. The original limit/transition maps and base identifications
are retained. The proof does not transport a property backwards along
the original family arrow, and does not assume limit preservation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.NativeCurveFamilyOpenStage
open NativeAffineOpenMembershipStage
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A genuinely open property of the ACTUAL limit family is realized by
an ACTUAL later-stage family, with exact base maps and commuting arrows. -/
theorem exists_property_at_later_stage
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigFppfOver B integerBase hZ) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B integerBase hZ).mapCone c))
    (haff : ∀ i, IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (D.obj i)))
    (G : CurveFamily B hZ) (hG : G.base = c.pt) (hPG : P G)
    (i : I) (Gi : CurveFamily B hZ) (hGi : Gi.base = D.obj i)
    (δ : G ⟶ Gi)
    (hδ : δ.baseMap = eqToHom hG ≫ c.π.app i ≫ eqToHom hGi.symm) :
    ∃ (j : I) (a : j ⟶ i) (H : CurveFamily B hZ)
      (hH : H.base = D.obj j) (χ : G ⟶ H) (η : H ⟶ Gi),
      P H ∧
      χ.baseMap = eqToHom hG ≫ c.π.app j ≫ eqToHom hH.symm ∧
      η.baseMap = eqToHom hH ≫ D.map a ≫ eqToHom hGi.symm ∧ χ ≫ η = δ := by
  obtain ⟨W, hW, hchar⟩ := hP Gi
  have hδmem : δ.baseMap ∈ W.obj (op G.base) :=
    (factorsThrough_subfunctor_iff W δ.baseMap).mp ((hchar G δ).mp hPG)
  have hlim : c.π.app i ≫ eqToHom hGi.symm ∈ W.obj (op c.pt) := by
    have h := W.map (eqToHom hG.symm).op hδmem
    change eqToHom hG.symm ≫ δ.baseMap ∈ W.obj (op c.pt) at h
    rw [hδ] at h
    simpa only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] using h
  obtain ⟨j, a, hja⟩ := exists_transition_comp_mem_open B integerBase hZ
    D c hc haff i (eqToHom hGi.symm) W hW hlim
  let b : D.obj j ⟶ Gi.base := D.map a ≫ eqToHom hGi.symm
  obtain ⟨H, η, hη⟩ := (curvesFiberedCategory B hZ).2.exists_lift b Gi rfl
  let : (curvesProjectionOver B hZ).IsHomLift b η := hη
  have hH : H.base = D.obj j := IsHomLift.domain_eq (curvesProjectionOver B hZ) b η
  have hηbase : η.baseMap = eqToHom hH ≫ b := by
    have h := IsHomLift.fac' (curvesProjectionOver B hZ) b η
    change η.baseMap = eqToHom hH ≫ b ≫ eqToHom (rfl : Gi.base = Gi.base) at h
    simpa only [eqToHom_refl, Category.comp_id] using h
  have hHmem : η.baseMap ∈ W.obj (op H.base) := by
    have h := W.map (eqToHom hH).op hja
    change eqToHom hH ≫ b ∈ W.obj (op H.base) at h
    rwa [← hηbase] at h
  have hPH : P H := (hchar H η).mpr ((factorsThrough_subfunctor_iff W η.baseMap).mpr hHmem)
  let v : G.base ⟶ H.base := eqToHom hG ≫ c.π.app j ≫ eqToHom hH.symm
  have hv : v ≫ η.baseMap = δ.baseMap := by
    rw [hηbase, hδ]
    change (eqToHom hG ≫ c.π.app j ≫ eqToHom hH.symm) ≫
      (eqToHom hH ≫ (D.map a ≫ eqToHom hGi.symm)) = _
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simpa only [Category.assoc] using
      congrArg (fun t => eqToHom hG ≫ t ≫ eqToHom hGi.symm) (c.w a)
  obtain ⟨χ, hχ, _⟩ := (curvesFiberedCategory B hZ).2.unique_lift η δ v hv
  exact ⟨j, a, H, hH, χ, η, hPH, hχ.1, hηbase, hχ.2⟩

end M9StacksIntegration.NativeCurveFamilyOpenStage
