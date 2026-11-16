module

public import M9StacksIntegration.LagrangianFieldBaseChange
public import M9StacksIntegration.LagrangianIncidenceFibres
public import M9StacksIntegration.LagrangianFibreFactorization

/-! The original incidence fibre at an actual extension-field point is
the literal pulled original zero scheme on the genuine native LG over
the extension field. Both original LG and extension-base maps are kept. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.LagrangianLinearSections

universe u

namespace M9Native.LagrangianCrossFieldParameter

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)
variable (p : Spec (.of L) ⟶ parameter K)
variable (hp : p ≫ parameterProjection K = GrassmannianFieldBaseChange.specMap φ)

def parameterPoint : Spec (.of L) ⟶ parameter L :=
  pullback.lift (𝟙 _) (p ≫ GrassmannianCharts.toIntegral K 9 14) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem parameterPoint_projection :
    parameterPoint p ≫ parameterProjection L = 𝟙 _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem parameterPoint_toIntegral :
    parameterPoint p ≫ GrassmannianCharts.toIntegral L 9 14 =
      p ≫ GrassmannianCharts.toIntegral K 9 14 := pullback.lift_snd _ _ _

include hp in
theorem parameterPoint_map : parameterPoint p ≫ GrassmannianFieldBaseChange.map φ 9 14 = p := by
  apply pullback.hom_ext
  · rw [Category.assoc, GrassmannianFieldBaseChange.map_projection,
      ← Category.assoc, parameterPoint_projection, Category.id_comp, hp]
  · rw [Category.assoc, GrassmannianFieldBaseChange.map_toIntegral, parameterPoint_toIntegral]

def toAmbient : LagrangianGrassmannian.space L ⟶ LagrangianLinearSections.ambient K :=
  pullback.lift (LagrangianFieldBaseChange.map φ) (LagrangianGrassmannian.projection L ≫ p)
    ((LagrangianFieldBaseChange.map_projection φ).trans
      (by simp only [Category.assoc, hp]))

@[reassoc (attr := simp)] theorem toAmbient_toLG :
    toAmbient φ p hp ≫ toLG K = LagrangianFieldBaseChange.map φ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem toAmbient_toParameter :
    toAmbient φ p hp ≫ toParameter K = LagrangianGrassmannian.projection L ≫ p :=
  pullback.lift_snd _ _ _

theorem toAmbient_isPullback : IsPullback (toAmbient φ p hp)
    (LagrangianGrassmannian.projection L) (toParameter K) p := by
  apply IsPullback.of_right (h₁₂ := toLG K) (h₂₂ := parameterProjection K)
  · simpa only [toAmbient_toLG, hp] using (LagrangianFieldBaseChange.map_isPullback φ)
  · exact toAmbient_toParameter φ p hp
  · exact IsPullback.of_hasPullback _ _

def zeroIdeal : (LagrangianGrassmannian.space L).IdealSheafData := (ideal K).comap (toAmbient φ p hp)
abbrev zeroScheme : Scheme.{u} := (zeroIdeal φ p hp).subscheme
abbrev zeroInclusion : zeroScheme φ p hp ⟶ LagrangianGrassmannian.space L :=
  (zeroIdeal φ p hp).subschemeι

def zeroSchemeIsoFibre : zeroScheme φ p hp ≅ pullback (familyProjection K) p :=
  (ideal K).comapIso (toAmbient φ p hp) ≪≫
    ((IsPullback.of_hasPullback (toAmbient φ p hp) (inclusion K)).flip.paste_vert
      (toAmbient_isPullback φ p hp)).isoPullback

@[reassoc (attr := simp)] theorem zeroSchemeIsoFibre_hom_base :
    (zeroSchemeIsoFibre φ p hp).hom ≫ pullback.snd (familyProjection K) p =
      zeroInclusion φ p hp ≫ LagrangianGrassmannian.projection L := by
  dsimp only [zeroSchemeIsoFibre, zeroInclusion, zeroScheme, zeroIdeal]
  simp only [Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_snd]
  rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]

@[reassoc (attr := simp)] theorem zeroSchemeIsoFibre_hom_toLG :
    (zeroSchemeIsoFibre φ p hp).hom ≫ pullback.fst (familyProjection K) p ≫ familyToLG K =
      zeroInclusion φ p hp ≫ LagrangianFieldBaseChange.map φ := by
  dsimp only [zeroSchemeIsoFibre, zeroInclusion, zeroScheme, zeroIdeal]
  simp only [Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_fst_assoc]
  change ((ideal K).comapIso (toAmbient φ p hp)).hom ≫
    pullback.snd (toAmbient φ p hp) (inclusion K) ≫ inclusion K ≫ toLG K = _
  rw [← pullback.condition_assoc]
  simp only [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst, toAmbient_toLG]

theorem comap_factorsThrough_iff {X Y T : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) (f : T ⟶ Y) :
    (∃ z : T ⟶ (I.comap g).subscheme, z ≫ (I.comap g).subschemeι = f) ↔
      (∃ z : T ⟶ I.subscheme, z ≫ I.subschemeι = f ≫ g) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ (I.comapIso g).hom ≫ pullback.snd g I.subschemeι, ?_⟩
    rw [Category.assoc, Category.assoc, ← pullback.condition]
    rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc, ← Category.assoc, hz]
  · rintro ⟨z, hz⟩
    refine ⟨pullback.lift f z hz.symm ≫ (I.comapIso g).inv, ?_⟩
    rw [← Scheme.IdealSheafData.comapIso_hom_fst I g, Category.assoc,
      Iso.inv_hom_id_assoc, pullback.lift_fst]

theorem zero_factorsThrough_iff {T : Scheme.{u}} (f : T ⟶ LagrangianGrassmannian.space L) :
    (∃ z : T ⟶ zeroScheme φ p hp, z ≫ zeroInclusion φ p hp = f) ↔
      (∃ z : T ⟶ family K, z ≫ inclusion K = f ≫ toAmbient φ p hp) :=
  comap_factorsThrough_iff (ideal K) (toAmbient φ p hp) f

end M9Native.LagrangianCrossFieldParameter
