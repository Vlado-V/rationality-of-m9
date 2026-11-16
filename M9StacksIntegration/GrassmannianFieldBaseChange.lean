module

public import M9StacksIntegration.GrassmannianCharts

/-! Actual native Grassmannians commute with field base change. The
comparison is the literal product map from their common integral model. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.GrassmannianFieldBaseChange

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L) (k n : ℕ)

abbrev specMap : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom φ)

def map : GrassmannianCharts.space L k n ⟶ GrassmannianCharts.space K k n :=
  pullback.lift (GrassmannianCharts.projection L k n ≫ specMap φ)
    (GrassmannianCharts.toIntegral L k n) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem map_projection :
    map φ k n ≫ GrassmannianCharts.projection K k n =
      GrassmannianCharts.projection L k n ≫ specMap φ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem map_toIntegral :
    map φ k n ≫ GrassmannianCharts.toIntegral K k n =
      GrassmannianCharts.toIntegral L k n := pullback.lift_snd _ _ _

theorem map_isPullback : IsPullback (map φ k n) (GrassmannianCharts.projection L k n)
    (GrassmannianCharts.projection K k n) (specMap φ) := by
  apply IsPullback.of_right (h₁₂ := GrassmannianCharts.toIntegral K k n)
    (h₂₂ := terminal.from (Spec (.of K)))
  · simpa only [map_toIntegral, terminal.comp_from] using
      (IsPullback.of_hasPullback (terminal.from (Spec (.of L)))
        (terminal.from (AlgebraicGeometry.Grassmannian.scheme.{u} k n))).flip
  · exact map_projection φ k n
  · exact (IsPullback.of_hasPullback (terminal.from (Spec (.of K)))
      (terminal.from (AlgebraicGeometry.Grassmannian.scheme.{u} k n))).flip

def baseChangeIso : GrassmannianCharts.space L k n ≅
    pullback (GrassmannianCharts.projection K k n) (specMap φ) :=
  (map_isPullback φ k n).isoPullback

@[reassoc (attr := simp)] theorem baseChangeIso_hom_fst :
    (baseChangeIso φ k n).hom ≫ pullback.fst _ _ = map φ k n :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)] theorem baseChangeIso_hom_snd :
    (baseChangeIso φ k n).hom ≫ pullback.snd _ _ =
      GrassmannianCharts.projection L k n := IsPullback.isoPullback_hom_snd _

end M9Native.GrassmannianFieldBaseChange
