module

public import M9StacksIntegration.LagrangianCrossFieldFiveSection
public import M9StacksIntegration.LagrangianFiveSectionAdjunction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale

/-! Actual differential-line adjunction for original incidence fibres.
The literal equation model is constructed from the original parameter,
and native differentials are transported by their canonical étale map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianFibreAdjunction

open LagrangianPluckerQuotient LagrangianLinearSections LagrangianCrossFieldFiveSection

/-- Transport by the actual canonical étale differential map, rather
than by an assumed differential comparison. -/
def differentialsIsoOfModel (K : Type u) [Field K] [CharZero K]
    {C : Scheme.{u}} (q : C ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 q]
    (s : Γ(LagrangianFiveSectionModel.equationBundle K,⊤))
    (e : C ≅ LagrangianFiveSectionModel.curve K s)
    (he : e.hom ≫ LagrangianFiveSectionModel.structureMap K s = q) :
    Scheme.Hom.relativeDifferentials q ≅
      (Scheme.Modules.pullback (e.hom ≫ LagrangianFiveSectionModel.inclusion K s)).obj
        (determinantLine K) := by
  have hi : e.inv ≫ q = LagrangianFiveSectionModel.structureMap K s := by
    rw [← he,← Category.assoc,e.inv_hom_id,Category.id_comp]
  letI : SmoothOfRelativeDimension 1 (e.inv ≫ q) :=
    inferInstanceAs (SmoothOfRelativeDimension (0+1) (e.inv ≫ q))
  letI : SmoothOfRelativeDimension 1 (LagrangianFiveSectionModel.structureMap K s) :=
    hi ▸ inferInstance
  let hc : e.hom ≫ LagrangianFiveSectionModel.structureMap K s = q ≫ 𝟙 _ :=
    he.trans (Category.comp_id q).symm
  let d := Scheme.Hom.relativeDifferentialsMap e.hom
    (LagrangianFiveSectionModel.structureMap K s) q (𝟙 _) hc
  letI : IsIso d := Scheme.Hom.isIso_relativeDifferentialsMap_of_etale e.hom
    (LagrangianFiveSectionModel.structureMap K s) q (𝟙 _) hc
  exact (asIso d).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso
      (LagrangianFiveSectionAdjunction.differentialsIsoCurveLine K s) ≪≫
        (Scheme.Modules.pullbackComp e.hom (LagrangianFiveSectionModel.inclusion K s)).app
          (determinantLine K)

variable {K L : Type u} [Field K] [Field L] [CharZero K]
  (φ : K →+* L) (p : Spec (.of L) ⟶ parameter K)
  (hp : p ≫ parameterProjection K = GrassmannianFieldBaseChange.specMap φ)

abbrev originalFibre : Scheme.{u} := pullback (familyProjection K) p

abbrev structureMap : originalFibre p ⟶ Spec (.of L) :=
  pullback.snd (familyProjection K) p

/-- The actual original fibre's native determinant line over the actual
extension-field LG, with its original immersion retained. -/
abbrev nativeLine : (originalFibre p).Modules :=
  (Scheme.Modules.pullback (nativeInclusion φ p hp)).obj (determinantLine L)

/-- This section is chosen from the proved actual original-fibre construction. -/
def modelSection : Γ(LagrangianFiveSectionModel.equationBundle L,⊤) := by
  letI : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
  exact Classical.choose (exists_fiveSectionIso φ p hp)

/-- This is the proved actual scheme comparison, not an isomorphism premise. -/
def modelIso : LagrangianFiveSectionModel.curve L (modelSection φ p hp) ≅ originalFibre p := by
  letI : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
  exact Classical.choose (Classical.choose_spec (exists_fiveSectionIso φ p hp))

theorem modelIso_toLG :
    (modelIso φ p hp).hom ≫ nativeInclusion φ p hp =
      LagrangianFiveSectionModel.inclusion L (modelSection φ p hp) := by
  letI : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
  exact (Classical.choose_spec (Classical.choose_spec (exists_fiveSectionIso φ p hp))).1

theorem modelIso_over :
    (modelIso φ p hp).hom ≫ structureMap p =
      LagrangianFiveSectionModel.structureMap L (modelSection φ p hp) := by
  letI : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
  exact (Classical.choose_spec (Classical.choose_spec (exists_fiveSectionIso φ p hp))).2.2

theorem modelIso_inv_toLG :
    (modelIso φ p hp).inv ≫ LagrangianFiveSectionModel.inclusion L (modelSection φ p hp) =
      nativeInclusion φ p hp := by
  rw [← modelIso_toLG φ p hp,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

/-- The actual native immersion is closed, as a consequence of the
constructed original zero-scheme comparison. -/
instance nativeInclusion_isClosedImmersion : IsClosedImmersion (nativeInclusion φ p hp) := by
  rw [← modelIso_inv_toLG φ p hp]
  infer_instance

/-- Actual smoothness of the original fibre gives the original native
differential sheaf its actual original determinant-line identification.
The equation model, field base change and all comparisons are derived. -/
def differentialsIsoNativeLine [SmoothOfRelativeDimension 1 (structureMap p)] :
    Scheme.Hom.relativeDifferentials (structureMap p) ≅ nativeLine φ p hp := by
  letI : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
  have hi : (modelIso φ p hp).inv ≫
      LagrangianFiveSectionModel.structureMap L (modelSection φ p hp) = structureMap p := by
    rw [← modelIso_over φ p hp,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  exact differentialsIsoOfModel L (structureMap p) (modelSection φ p hp)
      (modelIso φ p hp).symm hi ≪≫
    (Scheme.Modules.pullbackCongr (modelIso_inv_toLG φ p hp)).app (determinantLine L)

end M9Native.LagrangianFibreAdjunction
