module

public import M9StacksIntegration.LagrangianProjectiveIntersection
public import M9StacksIntegration.MukaiProjectiveCoordinateTransport
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers

/-! Actual field-valued native projective coordinates for the fixed
fourteen-coordinate linear-section equations. Normalizing one nonzero
coordinate uses the proved native unit invariance of the projective map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.MukaiProjectiveEvaluationPoint M9Native.MukaiProjectiveCoordinateTransport
open M9Native.LagrangianProjectiveIntersection

universe u

namespace M9Native.LagrangianFieldCoordinates

variable (K : Type u) [Field K]

def values (s : Fin 14 → Γ(Spec (.of K), ⊤)) : Fin 14 → K :=
  fun j => (Scheme.ΓSpecIso (.of K)).hom (s j)

theorem scalarSections_values (s : Fin 14 → Γ(Spec (.of K), ⊤)) (j : Fin 14) :
    scalarSections K (values K s j) = s j :=
  (Scheme.ΓSpecIso (.of K)).hom_inv_id_apply (s j)

theorem values_ne_zero (s : Fin 14 → Γ(Spec (.of K), ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) : values K s ≠ 0 := by
  intro hz
  have hs0 : s = 0 := by
    funext j
    change s j = 0
    rw [← scalarSections_values K s j]
    have h := congrFun hz j
    change values K s j = 0 at h
    rw [h, map_zero]
  rw [hs0] at hs
  simp at hs

/-- The original native projective morphism lies in the actual linear
zero locus exactly when its actual global coordinate vector satisfies L. -/
theorem nativePoint_mem_linearSection_iff
    (q : Spec (.of K) ⟶ ambient K)
    (s : Fin 14 → Γ(Spec (.of K), ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (hq : q ≫ pullback.fst (terminal.from (Spec (.of K)))
      (terminal.from (projectiveSpaceAtUniverse.{u} 13)) = 𝟙 _)
    (hint : q ≫ projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse s hs)
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (x : Spec (.of K)) :
    q x ∈ linearSection K L ↔ L (values K s) = 0 := by
  let w := values K s
  have hw : w ≠ 0 := values_ne_zero K s hs
  obtain ⟨i, hi⟩ : ∃ i : Fin 14, w i ≠ 0 := by
    by_contra h
    exact hw (funext fun i => not_ne_iff.mp (not_exists.mp h i))
  let z : Coordinates K := (w i)⁻¹ • w
  have hzi : z i = 1 := by simp [z, hi]
  have hz : z ≠ 0 := by
    intro h
    have h0 := congrFun h i
    rw [hzi] at h0
    exact one_ne_zero h0
  let v : Γ(Spec (.of K), ⊤)ˣ :=
    Units.map (scalarSections K).toMonoidHom ((Units.mk0 (w i) hi)⁻¹)
  have hv (j : Fin 14) : scalarSections K (z j) = (v : Γ(Spec (.of K), ⊤)) * s j := by
    change scalarSections K ((w i)⁻¹ * w j) = _
    rw [map_mul]
    change scalarSections K ((w i)⁻¹) * scalarSections K (values K s j) = _
    rw [scalarSections_values]
    rfl
  have hsz := span_scalarSections K z i hzi
  have hscaled : Ideal.span (Set.range fun j => (v : Γ(Spec (.of K), ⊤)) * s j) = ⊤ := by
    rw [Stacks.SectionsToProjectiveSpace.span_range_unit_smul]
    exact hs
  have hproj : Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
      (fun j => scalarSections K (z j)) hsz =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse s hs := by
    exact (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr
      (funext hv) hsz hscaled).trans
      (Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance v s hs hscaled)
  let φ := Module.Dual.eval K (Coordinates K) z
  have hφj (j : Fin 14) : φ ((Pi.basisFun K (Fin 14)).dualBasis j) = z j := by simp [φ]
  have he := coordinateTransport_base K (Forms K) (Pi.basisFun K (Fin 14)).dualBasis
    q φ (evaluation_ne_zero K z hz) i ((hφj i).trans hzi) hq
    (hint.trans (hproj.symm.trans
      (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr
        (funext fun j => congrArg (scalarSections K) (hφj j).symm) hsz
        (span_scalarSections K _ i ((hφj i).trans hzi))))) x
  have hp : q x = coordinatePoint K z hz := by
    apply (coordinateIso K).hom.isClosedEmbedding.injective
    change (coordinateIso K).hom (q x) = (coordinateIso K).hom
      ((coordinateIso K).inv (ProjectiveSpaceOfModule.linearFunctionalPoint K (Forms K)
        (Module.Dual.eval K (Coordinates K) z) (evaluation_ne_zero K z hz)))
    rw [← Scheme.Hom.comp_apply (coordinateIso K).inv (coordinateIso K).hom,
      Iso.inv_hom_id]
    exact he
  rw [hp, coordinatePoint_mem_iff]
  change L ((w i)⁻¹ • w) = 0 ↔ L w = 0
  rw [map_smul, smul_eq_zero]
  simp [inv_ne_zero hi]

/-- The literal original LG chart coefficients, with the native projective
comparison and both original base morphisms supplied by proved definitions. -/
theorem lagrangianPoint_mem_linearSection_iff [CharZero K]
    (f : Spec (.of K) ⟶ LagrangianGrassmannian.space K)
    (hf : f ≫ LagrangianGrassmannian.projection K = 𝟙 _)
    (ι : Fin 3 ↪ Fin 6)
    (g : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k := 3) (n := 6) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _ =
      g ≫ AlgebraicGeometry.Grassmannian.chart 3 6 ι)
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) (x : Spec (.of K)) :
    LagrangianPlucker.primitivePlucker K (f x) ∈ linearSection K L ↔
      L (values K (LagrangianPlucker.chartCoordinates K f ι g)) = 0 := by
  apply nativePoint_mem_linearSection_iff K (f ≫ LagrangianPlucker.primitivePlucker K)
    (LagrangianPlucker.chartCoordinates K f ι g)
    (LagrangianPlucker.chartCoordinates_span K f ι g hfg) ?_ ?_ L x
  · rw [Category.assoc, LagrangianPlucker.primitivePlucker_projection, hf]
  · rw [Category.assoc, LagrangianPlucker.primitivePlucker_toIntegral]
    exact LagrangianPlucker.comp_integralPrimitivePlucker K f ι g hfg

theorem matrix_equation_iff (A : Matrix (Fin 5) (Fin 14) Γ(Spec (.of K), ⊤))
    (s : Fin 14 → Γ(Spec (.of K), ⊤)) :
    A.mulVec s = 0 ↔
      (A.map (Scheme.ΓSpecIso (.of K)).hom.hom).mulVec (values K s) = 0 := by
  let ρ := (Scheme.ΓSpecIso (.of K)).hom.hom
  constructor
  · intro h
    funext j
    change ((A.map ρ).mulVec (ρ ∘ s)) j = 0
    rw [← RingHom.map_mulVec, h]
    exact map_zero ρ
  · intro h
    funext j
    apply (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
    change ρ (A.mulVec s j) = ρ 0
    rw [RingHom.map_mulVec]
    have he := congrFun h j
    change ((A.map ρ).mulVec (ρ ∘ s)) j = 0 at he
    exact he.trans (map_zero ρ).symm

end M9Native.LagrangianFieldCoordinates
