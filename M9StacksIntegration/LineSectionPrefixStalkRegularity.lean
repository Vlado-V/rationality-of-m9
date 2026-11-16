module

public import M9StacksIntegration.LineSectionLocalEquations
public import M9StacksIntegration.LineSectionPrefixes

/-!
# Regular stalks of the actual prefix schemes along the final cut

The original full cut, the original take-prefix cut, and their actual closed
map are retained. The quotient descriptions by the original ordered scalar
equations are proved by `LineSectionLocalEquations`; the regular parameter
argument supplies every prefix quotient. No prefix-stalk regularity or
quotient-identification premise is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
namespace M9Native.LineSectionPrefixStalkRegularity
open IteratedLineSectionCuts LineSectionLocalEquations

variable {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

private def equationsQuotientCongr (ss : List Γ(L, ⊤)) (U : X.affineOpens)
    (e : Γ(L, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1)) {x y : X} (h : x = y)
    (hx : x ∈ U.1) (hy : y ∈ U.1) (i : ℕ) :
    (X.presheaf.stalk x ⧸ Ideal.ofList ((localEquations L ss U e x hx).take i)) ≃+*
      (X.presheaf.stalk y ⧸ Ideal.ofList ((localEquations L ss U e y hy).take i)) := by
  subst y
  exact RingEquiv.refl _

/-- Regular final geometry of complementary dimension makes the actual
original prefix stalks regular at the actual image of the chosen final point. -/
theorem regular_at_final_point
    (ss : List Γ(L, ⊤)) (z : (simultaneousCut L ss).left)
    (U : X.affineOpens) (hz : (simultaneousCut L ss).hom z ∈ U.1)
    (e : Γ(L, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1))
    (hR : IsRegularLocalRing (X.presheaf.stalk ((simultaneousCut L ss).hom z)))
    (hZ : IsRegularLocalRing ((simultaneousCut L ss).left.presheaf.stalk z))
    (hdim : ringKrullDim ((simultaneousCut L ss).left.presheaf.stalk z) + ss.length =
      ringKrullDim (X.presheaf.stalk ((simultaneousCut L ss).hom z)))
    (i : ℕ) (hi : i ≤ ss.length) :
    IsRegularLocalRing ((simultaneousCut L (ss.take i)).left.presheaf.stalk
      (LineSectionPrefixes.prefixHom L ss i z)) ∧
    ringKrullDim ((simultaneousCut L (ss.take i)).left.presheaf.stalk
      (LineSectionPrefixes.prefixHom L ss i z)) + i =
      ringKrullDim (X.presheaf.stalk ((simultaneousCut L ss).hom z)) := by
  let : IsRegularLocalRing (X.presheaf.stalk ((simultaneousCut L ss).hom z)) := hR
  let : IsRegularLocalRing ((simultaneousCut L ss).left.presheaf.stalk z) := hZ
  let E := stalkQuotientEquiv L ss z U hz e
  let : IsRegularLocalRing (X.presheaf.stalk ((simultaneousCut L ss).hom z) ⧸
      Ideal.ofList (localEquations L ss U e ((simultaneousCut L ss).hom z) hz)) :=
    IsRegularLocalRing.of_ringEquiv E.symm
  have hcodim : ringKrullDim (X.presheaf.stalk ((simultaneousCut L ss).hom z) ⧸
      Ideal.ofList (localEquations L ss U e ((simultaneousCut L ss).hom z) hz)) +
      (localEquations L ss U e ((simultaneousCut L ss).hom z) hz).length =
      ringKrullDim (X.presheaf.stalk ((simultaneousCut L ss).hom z)) := by
    rw [ringKrullDim_eq_of_ringEquiv E, localEquations_length]
    exact hdim
  have hpre := OrderedPrefixRegularity.regular_quotients_of_regular_final
    (X.presheaf.stalk ((simultaneousCut L ss).hom z))
    (localEquations L ss U e ((simultaneousCut L ss).hom z) hz)
    inferInstance hcodim i (by simpa only [localEquations_length] using hi)
  let p := LineSectionPrefixes.prefixHom L ss i z
  have hp : (simultaneousCut L (ss.take i)).hom p = (simultaneousCut L ss).hom z := by
    dsimp only [p]
    rw [← Scheme.Hom.comp_apply, LineSectionPrefixes.prefixHom_over]
  have hpU : (simultaneousCut L (ss.take i)).hom p ∈ U.1 := by rw [hp]; exact hz
  let F := stalkQuotientEquiv L (ss.take i) p U hpU e
  let G := equationsQuotientCongr L ss U e hp hpU hz i
  have hreg : IsRegularLocalRing (X.presheaf.stalk ((simultaneousCut L (ss.take i)).hom p) ⧸
      Ideal.ofList (localEquations L (ss.take i) U e
        ((simultaneousCut L (ss.take i)).hom p) hpU)) := by
    rw [localEquations_take]
    let : IsRegularLocalRing (X.presheaf.stalk ((simultaneousCut L ss).hom z) ⧸
      Ideal.ofList ((localEquations L ss U e ((simultaneousCut L ss).hom z) hz).take i)) := hpre.1
    exact IsRegularLocalRing.of_ringEquiv G.symm
  let : IsRegularLocalRing (X.presheaf.stalk ((simultaneousCut L (ss.take i)).hom p) ⧸
      Ideal.ofList (localEquations L (ss.take i) U e
        ((simultaneousCut L (ss.take i)).hom p) hpU)) := hreg
  refine ⟨IsRegularLocalRing.of_ringEquiv F, ?_⟩
  have hpd : ringKrullDim (X.presheaf.stalk ((simultaneousCut L (ss.take i)).hom p) ⧸
      Ideal.ofList (localEquations L (ss.take i) U e
        ((simultaneousCut L (ss.take i)).hom p) hpU)) + i =
      ringKrullDim (X.presheaf.stalk ((simultaneousCut L ss).hom z)) := by
    rw [localEquations_take, ringKrullDim_eq_of_ringEquiv G]
    exact hpre.2
  rw [ringKrullDim_eq_of_ringEquiv F] at hpd
  exact hpd

/-- The same actual prefix regularity with the local line frame chosen
internally from the original invertible sheaf. -/
theorem regular_at_final_point_unframed
    (ss : List Γ(L, ⊤)) (z : (simultaneousCut L ss).left)
    (hR : IsRegularLocalRing (X.presheaf.stalk ((simultaneousCut L ss).hom z)))
    (hZ : IsRegularLocalRing ((simultaneousCut L ss).left.presheaf.stalk z))
    (hdim : ringKrullDim ((simultaneousCut L ss).left.presheaf.stalk z) + ss.length =
      ringKrullDim (X.presheaf.stalk ((simultaneousCut L ss).hom z)))
    (i : ℕ) (hi : i ≤ ss.length) :
    IsRegularLocalRing ((simultaneousCut L (ss.take i)).left.presheaf.stalk
      (LineSectionPrefixes.prefixHom L ss i z)) ∧
    ringKrullDim ((simultaneousCut L (ss.take i)).left.presheaf.stalk
      (LineSectionPrefixes.prefixHom L ss i z)) + i =
      ringKrullDim (X.presheaf.stalk ((simultaneousCut L ss).hom z)) := by
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem ((simultaneousCut L ss).hom z)
  obtain ⟨g, hxg, _, ⟨e⟩⟩ :=
    exists_basicOpen_linearEquiv L U ((simultaneousCut L ss).hom z) hxU
  exact regular_at_final_point L ss z ⟨X.basicOpen g, U.2.basicOpen g⟩ hxg e hR hZ hdim i hi

end M9Native.LineSectionPrefixStalkRegularity
