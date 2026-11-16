module

public import M9StacksIntegration.GenusNinePolarizedSourceOpen
public import M9StacksIntegration.StandaloneCurveCohomology
public import M9StacksIntegration.CurveClassifierPullback
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange

/-! Genuine base change of an original polarized genus-nine family to
the original ground field. The original cartesian square, line, and every
field fibre are retained, and site bounds follow from actual finiteness. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.PolarizedCurveGroundFieldBaseChange

variable {X T : Scheme.{u}} (p : X ⟶ T) (s : T ⟶ integerBase)
  (K : Type u) [Field K]

abbrev coefficient : Spec (.of K) ⟶ integerBase :=
  specULiftZIsTerminal.from (Spec (.of K))

abbrev parameter : Scheme.{u} := pullback s (coefficient K)
abbrev parameterMap : parameter s K ⟶ T := pullback.fst s (coefficient K)
abbrev structureMap : parameter s K ⟶ Spec (.of K) := pullback.snd s (coefficient K)
abbrev total : Scheme.{u} := pullback p (parameterMap s K)
abbrev totalMap : total p s K ⟶ X := pullback.fst p (parameterMap s K)
abbrev projection : total p s K ⟶ parameter s K := pullback.snd p (parameterMap s K)

/-- This is the actual original source-family base-change square. -/
theorem originalSquare : IsPullback (totalMap p s K) (projection p s K) p (parameterMap s K) :=
  IsPullback.of_hasPullback p (parameterMap s K)

instance parameterAffine [IsAffine T] : IsAffine (parameter s K) := by
  dsimp only [parameter]
  infer_instance

/-- The actual original finite-type map to the ground field. -/
theorem parameterFiniteType [LocallyOfFinitePresentation s] [QuasiCompact s] :
    LocallyOfFiniteType (structureMap s K) ∧ QuasiCompact (structureMap s K) :=
  ⟨inferInstance, inferInstance⟩

variable [IsProper p] [SmoothOfRelativeDimension 1 p]

instance projectionProper : IsProper (projection p s K) := inferInstance
instance projectionSmoothRelativeDimension : SmoothOfRelativeDimension 1 (projection p s K) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (originalSquare p s K) inferInstance

/-- The full all-original-field scheme-curve condition survives the real square. -/
theorem schemeCurve (hp : M9StandaloneDraft.SchemeCurve p 9) :
    M9StandaloneDraft.SchemeCurve (projection p s K) 9 :=
  M9StacksIntegration.StandaloneCurveCohomology.schemeCurve_of_isPullback p
    (projection p s K) (totalMap p s K) (parameterMap s K) (originalSquare p s K) hp

variable (N : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]

abbrev line : (total p s K).Modules := (Scheme.Modules.pullback (totalMap p s K)).obj N

instance lineInvertible : SheafOfModules.IsInvertible (total p s K).presheaf
    (total p s K).ringCatSheaf.2 (line p s K N) := by
  dsimp only [line]
  infer_instance

/-- True relative ampleness follows along the actual cartesian source square. -/
theorem line_isRelativelyAmple (ha : Stacks.RelativeAmple.IsRelativelyAmple p N) :
    Stacks.RelativeAmple.IsRelativelyAmple (projection p s K) (line p s K N) :=
  Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback (originalSquare p s K) N ha

/-- The literal pulled source line has the same original reading on an
arbitrary actual original field square. -/
def fieldLineIso {V : Scheme.{u}}
    (q : V ⟶ total p s K) :
    (Scheme.Modules.pullback q).obj (line p s K N) ≅
      (Scheme.Modules.pullback (q ≫ totalMap p s K)).obj N :=
  (Scheme.Modules.pullbackComp q (totalMap p s K)).app N

/-- Original degree forty-eight is retained over EVERY original field,
with the actual line and actual structural field map. -/
theorem fieldDegree_eq
    (h48 : ∀ (L : Type u) [Field L] (V : Scheme.{u})
      (a : Spec (.of L) ⟶ T) (q : V ⟶ X) (f : V ⟶ Spec (.of L))
      [IsProper f], IsPullback q f p a → ∀ hd : topologicalKrullDim V ≤ 1,
        invertibleCurveDegree L f hd ((Scheme.Modules.pullback q).obj N) = 48)
    {L : Type u} [Field L] {V : Scheme.{u}} (a : Spec (.of L) ⟶ parameter s K)
    (q : V ⟶ total p s K) (f : V ⟶ Spec (.of L)) [IsProper f]
    (sq : IsPullback q f (projection p s K) a) (hd : topologicalKrullDim V ≤ 1) :
    invertibleCurveDegree L f hd ((Scheme.Modules.pullback q).obj (line p s K N)) = 48 :=
  (invertibleCurveDegree_eq_of_iso L f hd (fieldLineIso p s K N q)).trans
    (h48 L V (a ≫ parameterMap s K) (q ≫ totalMap p s K) f
      (sq.paste_horiz (originalSquare p s K)) hd)

/-- Every actual original field curve of the model lifts to the genuine
ground-field base change and keeps both original maps and its square. -/
theorem exists_original_curve_lift {L : Type u} [Field L] {V : Scheme.{u}}
    (a : Spec (.of L) ⟶ T) (r : V ⟶ X) (f : V ⟶ Spec (.of L))
    (σ : Spec (.of L) ⟶ Spec (.of K)) (sq : IsPullback r f p a) :
    ∃ (a' : Spec (.of L) ⟶ parameter s K) (r' : V ⟶ total p s K),
      a' ≫ parameterMap s K = a ∧ a' ≫ structureMap s K = σ ∧
      r' ≫ totalMap p s K = r ∧ IsPullback r' f (projection p s K) a' := by
  let a' : Spec (.of L) ⟶ parameter s K := pullback.lift a σ
    (specULiftZIsTerminal.hom_ext _ _)
  have ha' : a' ≫ parameterMap s K = a := pullback.lift_fst _ _ _
  have hs' : a' ≫ structureMap s K = σ := pullback.lift_snd _ _ _
  let r' : V ⟶ total p s K := pullback.lift r (f ≫ a') (by rw [Category.assoc, ha', sq.w])
  have hr' : r' ≫ totalMap p s K = r := pullback.lift_fst _ _ _
  have hp' : r' ≫ projection p s K = f ≫ a' := pullback.lift_snd _ _ _
  refine ⟨a',r',ha',hs',hr',?_⟩
  apply IsPullback.of_right (t := originalSquare p s K) (p := hp')
  simpa only [hr', ha'] using sq

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

include hK in
/-- The original parameter lies in the native site by actual finite type. -/
theorem parameter_contains [LocallyOfFinitePresentation s] [QuasiCompact s] :
    B.Contains (parameter s K) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (structureMap s K) hK

include hK in
/-- The actual total source lies in the same site by its true proper projection. -/
theorem total_contains [LocallyOfFinitePresentation s] [QuasiCompact s] :
    B.Contains (total p s K) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (projection p s K)
    (parameter_contains s K B hK)

end M9Native.PolarizedCurveGroundFieldBaseChange
end
