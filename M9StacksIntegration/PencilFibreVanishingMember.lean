module

public import M9StacksIntegration.PencilSectionsLinearComparison
public import M9StacksIntegration.RationalPointLineRelation
public import M9StacksIntegration.PencilLiftFourPointFibre
public import M9StacksIntegration.LagrangianPencilFibreTripleRank
public import M9StacksIntegration.LineFramePullback
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization

/-!
# An actual original pencil member through all four selected fibre points

The original moving-map comparison sends the two pulled target
coordinates to the original pencil basis. At the selected rational
point, the target line has dimension one. Its actual kernel supplies a
nonzero original pencil member. Pullback composition proves that this
member vanishes on every one of the four actual fibre points.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.PencilFibreVanishingMember

open PencilPullbackSections PencilFourPointFibre PencilSectionsLinearComparison
open Stacks.LinearSeriesMorphism

/-- The native zero-scheme universal property produces actual maps into
the FULL member divisor, including its nilpotent structure. -/
theorem member_factor_of_pullback_zero
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (A : LinearSeries K f hdim d 1) (x : A.V) (a : T ⟶ X)
    (ha : pullbackGlobalSections a A.L (PencilMemberDivisor.memberSection f hdim A x) = 0) :
    ∃ b : T ⟶ (PencilMemberDivisor.divisor f hdim A x).subscheme,
      b ≫ (PencilMemberDivisor.divisor f hdim A x).subschemeι = a := by
  let := A.isInvertible
  exact (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X A.L
    (PencilMemberDivisor.memberSection f hdim A x) a).mp ha

/-- This uses only the actual section-pinned comparison of a pencil
map and the original rational target point. The nonzero member and its
vanishing on the entire fibre are constructed. -/
theorem exists_member_vanishing_on_fibre
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (A : LinearSeries K f hdim d 1) (b : Module.Basis (Fin 2) K A.V)
    (r : Y ⟶ Spec (.of K)) (p : X ⟶ Y) (hp : p ≫ r = f)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L]
    (t : Fin 2 → Γ(L, ⊤))
    (α : (Scheme.Modules.pullback p).obj L ⟶ A.L)
    (hα : ∀ i, α.app ⊤ (pullbackGlobalSections p L (t i)) = seriesSections A b i)
    (q : Spec (.of K) ⟶ Y) (hq : q ≫ r = 𝟙 _) :
    ∃ x : A.V, x ≠ 0 ∧ ∀ a : Spec (.of K) ⟶ X, a ≫ p = q →
      pullbackGlobalSections a A.L (PencilMemberDivisor.memberSection f hdim A x) = 0 := by
  classical
  subst hp
  let S : A.V →ₗ[K] fieldGlobalSections K r L :=
    b.constr K (show Fin 2 → fieldGlobalSections K r L from t)
  let C := (Scheme.Modules.pullback q).obj L
  let W := fieldGlobalSections K (q ≫ r) C
  have hW : Module.finrank K W = 1 :=
    (cohomologyOverFieldZeroLinearIso K (q ≫ r) C).toLinearEquiv.finrank_eq.symm.trans
      (RationalPointLineRelation.pullback_h0_eq_one r q hq L)
  let : Module.Finite K W := Module.finite_of_finrank_pos (by rw [hW]; decide)
  let : Module.Finite K A.V := Module.finite_of_finrank_pos (by rw [A.finrank_eq]; decide)
  let E : A.V →ₗ[K] W := (globalSectionsPullback K r q L).comp S
  have hker : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [hW,A.finrank_eq]
    decide)
  obtain ⟨x,hx,hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hqzero : pullbackGlobalSections q L (S x) = 0 := hx
  let αMap : fieldGlobalSections K (p ≫ r) ((Scheme.Modules.pullback p).obj L) →ₗ[K]
      fieldGlobalSections K (p ≫ r) A.L :=
    ((restrictScalarsOverBase K (p ≫ r)).map
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map α)).hom
  let U : A.V →ₗ[K] fieldGlobalSections K (p ≫ r) A.L :=
    (αMap.comp (globalSectionsPullback K r p L)).comp S
  let V : A.V →ₗ[K] fieldGlobalSections K (p ≫ r) A.L :=
    (cohomologyOverFieldZeroLinearIso K (p ≫ r) A.L).hom.hom.comp A.V.subtype
  have hUV : U = V := by
    apply b.ext
    intro i
    simp only [U,V,LinearMap.comp_apply,S,Module.Basis.constr_basis]
    change α.app ⊤ (pullbackGlobalSections p L (t i)) =
      (cohomologyOverFieldZeroLinearIso K (p ≫ r) A.L).hom
        (b i : cohomologyOverField K (p ≫ r) A.L 0)
    exact (hα i).trans (seriesSections_eq_linear (p ≫ r) hdim A b i)
  have hOriginal : α.app ⊤ (pullbackGlobalSections p L (S x)) =
      PencilMemberDivisor.memberSection (p ≫ r) hdim A x :=
    LinearMap.congr_fun hUV x
  refine ⟨x,hxne,?_⟩
  intro a ha
  have hcompzero : pullbackGlobalSections (a ≫ p) L (S x) = 0 := by
    let e := (Scheme.Modules.pullbackCongr ha).app L
    have he : e.hom.app ⊤ (pullbackGlobalSections (a ≫ p) L (S x)) = 0 :=
      (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr ha L (S x)).trans hqzero
    have hleft (w : Γ((Scheme.Modules.pullback (a ≫ p)).obj L, ⊤)) :
        e.inv.app ⊤ (e.hom.app ⊤ w) = w :=
      (ConcreteCategory.congr_hom
        (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) (Iso.hom_inv_id e)) w).trans
          (CategoryTheory.id_apply w)
    calc
      pullbackGlobalSections (a ≫ p) L (S x) =
          e.inv.app ⊤ (e.hom.app ⊤ (pullbackGlobalSections (a ≫ p) L (S x))) :=
        (hleft _).symm
      _ = e.inv.app ⊤ 0 := congrArg (e.inv.app ⊤) he
      _ = 0 := (e.inv.app ⊤).hom.map_zero
  have hiterzero : pullbackGlobalSections a ((Scheme.Modules.pullback p).obj L)
      (pullbackGlobalSections p L (S x)) = 0 := by
    have hi := LineFramePullback.pullbackComp_inv_apply a p L (S x)
    simpa only [hcompzero,map_zero] using hi.symm
  have hn := SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections
    a α (pullbackGlobalSections p L (S x))
  rw [hiterzero,map_zero] at hn
  exact (congrArg (pullbackGlobalSections a A.L) hOriginal.symm).trans hn.symm

open LagrangianTransverseRestriction LagrangianPencilFibreTripleRank
open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned

/-- All inputs are the original transverse LG curve and its original
pencil. Every triple has actual canonical rank three; all four points
lie in the actual length-four member whose canonical rank is at most three. -/
theorem exists_original_fibre_and_member
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]
    (hM : Function.Surjective M.mulVec)
    (hdim : topologicalKrullDim (curve K M) ≤ 1)
    (A : LinearSeries K (curveProjection K M) hdim 4 1) :
    ∃ D : FourPointFibre K (curveProjection K M), ∃ x : A.V, x ≠ 0 ∧
      (∀ i : Fin 4, pullbackGlobalSections (curvePoint D i) A.L
        (PencilMemberDivisor.memberSection (curveProjection K M) hdim A x) = 0) ∧
      Module.finrank K (LinearMap.range
        (CanonicalDivisorSpan.canonicalRestriction (curveProjection K M)
          (PencilMemberDivisor.divisor (curveProjection K M) hdim A x))) ≤ 3 ∧
      ∀ j : Fin 4, Module.finrank K (LinearMap.range
        (CanonicalDivisorSpan.canonicalRestriction (curveProjection K M)
          (RationalPointDivisor.divisor (triplePoints D j)))) = 3 := by
  classical
  let : Smooth (curveProjection K M) := SmoothOfRelativeDimension.smooth 1 _
  let := isIso_globalSections_of_isAlgClosed K (curveProjection K M)
  obtain ⟨D,b,α,hα⟩ :=
    PencilLiftFourPointFibre.exists_original_lagrangian_fibre_with_section_pins M hM hdim A
  let z := projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of K))
  let L := (Scheme.Modules.pullback z).obj (twistingSheafAtUniverse.{u} 1)
  let : SheafOfModules.IsInvertible (PencilProjectiveLineGeometry.Line K).presheaf
      (PencilProjectiveLineGeometry.Line K).ringCatSheaf.property L :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback z (twistingSheafAtUniverse.{u} 1)
  let t : Fin 2 → Γ(L, ⊤) := pullbackCoordSection z
  let α' : (Scheme.Modules.pullback D.map).obj L ⟶ A.L :=
    ((Scheme.Modules.pullbackComp D.map z).hom.app (twistingSheafAtUniverse.{u} 1)) ≫ α
  have hpin (i : Fin 2) : α'.app ⊤ (pullbackGlobalSections D.map L (t i)) =
      seriesSections A b i := by
    change α.app ⊤
      (((Scheme.Modules.pullbackComp D.map z).hom.app (twistingSheafAtUniverse.{u} 1)).app ⊤
        (pullbackGlobalSections D.map L (pullbackCoordSection z i))) = _
    exact (congrArg (α.app ⊤)
      (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp D.map z
        (twistingSheafAtUniverse.{u} 1) (coordGlobalSection.{u} 1 i))).trans (hα i)
  obtain ⟨x,hx,hvan⟩ := exists_member_vanishing_on_fibre (curveProjection K M) hdim A b
    (PencilProjectiveLineGeometry.toBase K) D.map D.overBase L t α' hpin
    D.point D.point_overBase
  refine ⟨D,x,hx,fun i => hvan (curvePoint D i) (curvePoint_map D i),?_,?_⟩
  · exact PencilMemberDivisor.canonical_restriction_rank_le (curveProjection K M) hdim A x hx
  · intro j
    exact RationalPointDivisor.canonical_rank_three (curveProjection K M)
      (triplePoints D j) (triplePoints_injective D j) hdim
      (LagrangianNoTrigonal.no_g1_three_at_dimension K M hM hdim)

/-- The same actual fibre and original member, now with actual point
factorizations into its full zero scheme for the canonical evaluation
consumer. Every divisor and rank statement is still derived. -/
theorem exists_original_fibre_member_factors
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]
    (hM : Function.Surjective M.mulVec)
    (hdim : topologicalKrullDim (curve K M) ≤ 1)
    (A : LinearSeries K (curveProjection K M) hdim 4 1) :
    ∃ D : FourPointFibre K (curveProjection K M), ∃ x : A.V, x ≠ 0 ∧
      (∀ i : Fin 4, ∃ a : Spec (.of K) ⟶
          (PencilMemberDivisor.divisor (curveProjection K M) hdim A x).subscheme,
        a ≫ (PencilMemberDivisor.divisor (curveProjection K M) hdim A x).subschemeι =
          curvePoint D i) ∧
      Module.finrank K (LinearMap.range
        (CanonicalDivisorSpan.canonicalRestriction (curveProjection K M)
          (PencilMemberDivisor.divisor (curveProjection K M) hdim A x))) ≤ 3 ∧
      ∀ j : Fin 4, Module.finrank K (LinearMap.range
        (CanonicalDivisorSpan.canonicalRestriction (curveProjection K M)
          (RationalPointDivisor.divisor (triplePoints D j)))) = 3 := by
  obtain ⟨D,x,hx,hvan,hr,h3⟩ := exists_original_fibre_and_member M hM hdim A
  exact ⟨D,x,hx,fun i => member_factor_of_pullback_zero (curveProjection K M)
    hdim A x (curvePoint D i) (hvan i),hr,h3⟩

end M9Native.PencilFibreVanishingMember
