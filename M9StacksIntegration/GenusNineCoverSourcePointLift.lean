module

public import M9StacksIntegration.GenusNineBoundedCoverFamilies

/-! The SAME original model point of an actual cover parameter gives
an actual Cartesian lift of the original curve to its universal source. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.GenusNineCoverSourcePointLift

open GenusNineCoverParameterSchemes GenusNineBoundedCoverFamilies

variable {K : Type u} [Field K] {B : BigFppfSite.{u}}
  {hK : B.Contains (Spec (.of K))} {m : ℕ}
  {D : GenusNineGroundFieldPolarizedModels.Model.{u} K m} {i : Fin 5}
  (P : Presentation K B hK D i)

abbrev originalMap : P.boundedFamily.total ⟶ D.total :=
  (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
    (RelativeCoverSchemeEvaluation.toOriginal (sourceMap K B hK D) (targetMap K B hK D)
      P.nativeFamily
      (Presentation.sourceRepresentable (K := K) (B := B) (hK := hK) (D := D)))

abbrev baseMap : P.boundedFamily.parameter ⟶ D.parameter :=
  (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map P.parameterMap

/-- The actual original universal source lies over its SAME actual
representing scheme projection to the original model base. -/
theorem originalSquare : IsPullback (originalMap P) P.boundedFamily.projection D.projection (baseMap P) := by
  have hb : RelativeCoverSchemeEvaluation.base (sourceMap K B hK D)
      (targetMap K B hK D) P.nativeFamily = P.parameterMap := by
    simp only [RelativeCoverSchemeEvaluation.base, P.nativeBase_eq, Functor.preimage_map]
  change IsPullback
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
      (RelativeCoverSchemeEvaluation.toOriginal (sourceMap K B hK D) (targetMap K B hK D)
        P.nativeFamily
        (Presentation.sourceRepresentable (K := K) (B := B) (hK := hK) (D := D))))
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
      (RelativeCoverSchemeEvaluation.projection (sourceMap K B hK D) (targetMap K B hK D)
        P.nativeFamily
        (Presentation.sourceRepresentable (K := K) (B := B) (hK := hK) (D := D))))
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (sourceMap K B hK D))
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map P.parameterMap)
  simpa only [hb] using
    RelativeCoverSchemeEvaluation.originalSourceSquare (sourceMap K B hK D) (targetMap K B hK D)
      P.nativeFamily
      (Presentation.sourceRepresentable (K := K) (B := B) (hK := hK) (D := D))

variable {L : Type u} [Field L] {C : Scheme.{u}}
  (y : Spec (.of L) ⟶ D.parameter) (r : C ⟶ D.total) (f : C ⟶ Spec (.of L))
  (sq : IsPullback r f D.projection y)
  (w : Spec (.of L) ⟶ P.boundedFamily.parameter) (hw : w ≫ (baseMap P) = y)

/-- The lift is constructed from the genuine source square and SAME
original model parameter; it is not a supplied curve isomorphism. -/
def lift : C ⟶ P.boundedFamily.total :=
  (originalSquare P).lift r (f ≫ w) (by rw [Category.assoc,hw]; exact sq.w)

theorem lift_toOriginal : lift P y r f sq w hw ≫ (originalMap P) = r :=
  (originalSquare P).lift_fst _ _ _

theorem lift_projection : lift P y r f sq w hw ≫ P.boundedFamily.projection = f ≫ w :=
  (originalSquare P).lift_snd _ _ _

/-- This is an actual original Cartesian fibre presentation, retaining
its original coefficient field and original structure map. -/
theorem lift_isPullback : IsPullback (lift P y r f sq w hw) f P.boundedFamily.projection w := by
  apply IsPullback.of_right (t := (originalSquare P)) (p := lift_projection P y r f sq w hw)
  simpa only [lift_toOriginal,hw] using sq

end M9Native.GenusNineCoverSourcePointLift
end
