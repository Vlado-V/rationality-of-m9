module

public import M9StacksIntegration.NativeChosenGenusObjectMembership
public import M9StacksIntegration.AllTestNativeFieldSchemeModel
public import M9StacksIntegration.NativeSchematicCurveFamily

/-! Typed native endpoints for a plain original field scheme model.
The proofs use an arbitrary original scheme, independently of any chosen
source-object recovery data. The actual coefficient base is retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
namespace M9Native.NativeFieldSchemeModelEndpoints
open NativeGenusNineFieldObjectCurve

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (L : Type u) [Field L] (hL : B.Contains (Spec (.of L))) (coefficient : K →+* L)
  (X : Over (Spec (.of L))) (hp : IsProper X.hom)

include hL hp in
theorem contains : B.Contains X.left := by
  let : IsProper X.hom := hp
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hL

abbrev total : BigFppfOver B integerBase hZ :=
  integerSiteObject B hZ (contains B L hL X hp)

def projection : total B hZ L hL X hp ⟶ integerFieldBase B hZ K hK L hL coefficient :=
  integerSiteMap B hZ (contains B L hL X hp) hL X.hom ≫
    eqToHom (integerFieldBase_eq B hZ K hK L hL coefficient).symm

theorem projection_original :
    (BigFppfOver.toScheme B integerBase hZ).map
      (projection B hZ K hK L hL coefficient X hp) = X.hom := by
  change X.hom ≫
    B.inclusion.map (eqToHom (integerFieldBase_eq B hZ K hK L hL coefficient).symm).left = _
  simp only [Over.eqToHom_left, eqToHom_map]
  exact Category.comp_id _

variable (g : ℕ) (hq : M9StandaloneDraft.SchemeCurve X.hom g)

include hq in
theorem projection_schemeCurve : M9StandaloneDraft.SchemeCurve
    ((BigFppfOver.toScheme B integerBase hZ).map
      (projection B hZ K hK L hL coefficient X hp)) g := by
  rw [projection_original]
  exact hq

abbrev family : CurveFamily B hZ :=
  M9StacksIntegration.NativeSchematicCurveFamily.schemeCurveFamily B hZ
    (projection B hZ K hK L hL coefficient X hp) g
    (projection_schemeCurve B hZ K hK L hL coefficient X hp g hq)

variable (hd : topologicalKrullDim X.left ≤ 1)

set_option maxHeartbeats 2000000 in
def comparison : @curveFamilyOfScheme L _ X hp B hZ hL hd ≅
    family B hZ K hK L hL coefficient X hp g hq := by
  apply M9StacksIntegration.AllTestNativeFieldSchemeModel.isoMk
    (F := @curveFamilyOfScheme L _ X hp B hZ hL hd)
    (G := family B hZ K hK L hL coefficient X hp g hq)
    (eqToIso (integerFieldBase_eq B hZ K hK L hL coefficient).symm)
    (Iso.refl (schemeSpace (total B hZ L hL X hp)))
  change 𝟙 _ ≫ schemeSpaceMap
      (integerSiteMap B hZ (contains B L hL X hp) hL X.hom ≫
        eqToHom (integerFieldBase_eq B hZ K hK L hL coefficient).symm) =
    schemeSpaceMap (integerSiteMap B hZ (contains B L hL X hp) hL X.hom) ≫
      schemeSpaceMap (eqToHom (integerFieldBase_eq B hZ K hK L hL coefficient).symm)
  rw [Category.id_comp]
  exact (schemeSpaceFunctor B integerBase hZ).map_comp _ _

set_option maxHeartbeats 2000000 in
/-- Opaque endpoint law, proved before any rich recovery package is instantiated. -/
theorem comparison_base :
    (comparison B hZ K hK L hL coefficient X hp g hq hd).hom.baseMap =
      eqToHom (integerFieldBase_eq B hZ K hK L hL coefficient).symm := rfl

section RecoveryLaws
variable {F G H : CurveFamily B hZ}

theorem recovery_comp_base (e : F ≅ G) (d : G ≅ H)
    (b : F.base = G.base) (c : G.base = H.base)
    (he : e.hom.baseMap = eqToHom b) (hd : d.hom.baseMap = eqToHom c) :
    (e ≪≫ d).hom.baseMap = eqToHom (b.trans c) := by
  change e.hom.baseMap ≫ d.hom.baseMap = _
  rw [he, hd]
  simp only [eqToHom_trans]

theorem homLift_id_of_base (T : BigFppfOver B integerBase hZ)
    (a : F ⟶ G) (hF : F.base = T) (hG : G.base = T)
    (ha : a.baseMap = eqToHom (hF.trans hG.symm)) :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 T) a := by
  apply IsHomLift.of_fac' _ _ _ hF hG
  change a.baseMap = _
  simpa using ha

theorem recovery_comp_symm_lift (T : BigFppfOver B integerBase hZ)
    (e : F ≅ G) (d : H ≅ G)
    (he : (curvesProjectionOver B hZ).IsHomLift (𝟙 T) e.hom)
    (hd : (curvesProjectionOver B hZ).IsHomLift (𝟙 T) d.hom) :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 T) (e ≪≫ d.symm).hom := by
  letI := hd
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 T) d.inv := inferInstance
  letI := he
  change (curvesProjectionOver B hZ).IsHomLift (𝟙 T) (e.hom ≫ d.inv)
  exact IsHomLift.comp_lift_id_left _ _ _ _
end RecoveryLaws

end M9Native.NativeFieldSchemeModelEndpoints
end
