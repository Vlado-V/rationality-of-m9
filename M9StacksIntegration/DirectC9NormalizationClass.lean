module

public import M9StacksIntegration.DirectC9FamilyDegree
public import M9StacksIntegration.CurvePowerGraphFixedRestrictions

/-!
# The actual inverse-normalization line has class minus the point sum

Every fixed graph has zero self-restriction over the original field.
Each actual moving graph restricts to the actual coordinate point line.
Additivity of the actual Cartier divisor classes therefore computes the
actual base normalization; no numerical or Chern-class premise is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 10000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.DirectC9NormalizationClass

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyClass)
open CurvePowerGraphRestrictions (pointClass coordinateMap)

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

abbrev normalizationSection : (power C 9).left ⟶ familySpace C :=
  Stacks.Hilbert.pointGraph C (power C 9) (constantPoint C c₀)

abbrev graphFamilyClass (y : power C 9 ⟶ C) : Stacks.Picard.ofScheme (familySpace C) :=
  familyClass C (GraphNormalPicard.graphFamily C (power C 9) y)

theorem familyAddPoint_class {d : ℕ} (D : Stacks.Hilbert.HilbertFamily C (power C 9) d)
    (y : power C 9 ⟶ C) (hy : IsClosedImmersion (Stacks.Hilbert.pointGraph C (power C 9) y)) :
    familyClass C (Stacks.Hilbert.familyAddPoint C (power C 9) D y hy) =
      familyClass C D + graphFamilyClass C y := by
  have hD : @Stacks.Divisors.IsEffectiveCartierDivisor (familySpace C) D.ideal :=
    D.isEffectiveCartierDivisor_ideal
  have hY : @Stacks.Divisors.IsEffectiveCartierDivisor (familySpace C)
      (Stacks.Hilbert.pointIdeal C (power C 9) y) :=
    (GraphNormalPicard.graphFamily C (power C 9) y).isEffectiveCartierDivisor_ideal
  exact @Stacks.Divisors.picardClass_mul (familySpace C) D.ideal
    (Stacks.Hilbert.pointIdeal C (power C 9) y) hD hY

theorem constantFamily_class (q : ℕ) :
    familyClass C (constantFamily C c₀ q) =
      (q + 1) • graphFamilyClass C (constantPoint C c₀) := by
  induction q with
  | zero => exact (one_nsmul _).symm
  | succ q ih =>
      change familyClass C (Stacks.Hilbert.familyAddPoint C (power C 9)
        (constantFamily C c₀ q) (constantPoint C c₀) _) = _
      rw [familyAddPoint_class,ih]
      exact (succ_nsmul (graphFamilyClass C (constantPoint C c₀)) (q + 1)).symm

abbrev pointClassAt (i : Fin 9) : Stacks.Picard.ofScheme (power C 9).left :=
  Stacks.Picard.schemePullbackClass (coordinateMap C 9 i).left (pointClass C c₀)

def pointSum : Stacks.Picard.ofScheme (power C 9).left := ∑ i : Fin 9, pointClassAt C c₀ i

def partialPointSum (j : ℕ) (hj : j ≤ 9) : Stacks.Picard.ofScheme (power C 9).left :=
  ∑ i : Fin j, pointClassAt C c₀ ⟨i.val,by omega⟩

def movingClassSum (j : ℕ) (hj : j ≤ 9) : Stacks.Picard.ofScheme (familySpace C) :=
  ∑ i : Fin j, graphFamilyClass C (coord C 9 ⟨i.val,by omega⟩)

theorem movingClassSum_successor (j : ℕ) (hj : j + 1 ≤ 9) :
    movingClassSum C (j + 1) hj = movingClassSum C j (by omega) +
      graphFamilyClass C (coord C 9 ⟨j,by omega⟩) := by
  rw [movingClassSum,Fin.sum_univ_castSucc]
  rfl

theorem partialFamily_class (j : ℕ) (hj : j ≤ 9) :
    familyClass C (partialFamily C c₀ j hj) =
      17 • graphFamilyClass C (constantPoint C c₀) + movingClassSum C j hj := by
  revert hj
  induction j with
  | zero =>
      intro hj
      change familyClass C (constantFamily C c₀ 16) =
        17 • graphFamilyClass C (constantPoint C c₀) + movingClassSum C 0 hj
      rw [movingClassSum,Fin.sum_univ_zero,add_zero]
      exact constantFamily_class C c₀ 16
  | succ j ih =>
      intro hj
      change familyClass C (Stacks.Hilbert.familyAddPoint C (power C 9)
        (partialFamily C c₀ j (by omega)) (coord C 9 ⟨j,by omega⟩) _) = _
      rw [familyAddPoint_class,ih,movingClassSum_successor]
      exact add_assoc _ _ _

theorem fixedGraph_sectionClass :
    Stacks.Picard.schemePullbackClass (normalizationSection C c₀)
      (graphFamilyClass C (constantPoint C c₀)) = 0 :=
  CurvePowerGraphRestrictions.constant_graphClass_restrict_constant C c₀ 9

theorem coordinateGraph_sectionClass (i : Fin 9) :
    Stacks.Picard.schemePullbackClass (normalizationSection C c₀) (graphFamilyClass C (coord C 9 i)) =
      pointClassAt C c₀ i :=
  CurvePowerGraphFixedRestrictions.coordinate_graphClass_restrict_constant C c₀ 9 i

theorem constantFamily_sectionClass (q : ℕ) :
    Stacks.Picard.schemePullbackClass (normalizationSection C c₀) (familyClass C (constantFamily C c₀ q)) = 0 := by
  rw [constantFamily_class]
  change (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
    ((q + 1) • graphFamilyClass C (constantPoint C c₀)) = 0
  have hf : (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
      (graphFamilyClass C (constantPoint C c₀)) = 0 := fixedGraph_sectionClass C c₀
  rw [map_nsmul,hf,nsmul_zero]

theorem movingClassSum_sectionClass (j : ℕ) (hj : j ≤ 9) :
    Stacks.Picard.schemePullbackClass (normalizationSection C c₀) (movingClassSum C j hj) =
      partialPointSum C c₀ j hj := by
  change (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
    (∑ i : Fin j, graphFamilyClass C (coord C 9 ⟨i.val,by omega⟩)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact coordinateGraph_sectionClass C c₀ ⟨i.val,by omega⟩

theorem partialFamily_sectionClass (j : ℕ) (hj : j ≤ 9) :
    Stacks.Picard.schemePullbackClass (normalizationSection C c₀) (familyClass C (partialFamily C c₀ j hj)) =
      partialPointSum C c₀ j hj := by
  rw [partialFamily_class]
  change (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
    (17 • graphFamilyClass C (constantPoint C c₀) + movingClassSum C j hj) = _
  have hf : (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
      (graphFamilyClass C (constantPoint C c₀)) = 0 := fixedGraph_sectionClass C c₀
  have hm : (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
      (movingClassSum C j hj) = partialPointSum C c₀ j hj := movingClassSum_sectionClass C c₀ j hj
  rw [map_add,map_nsmul,hf,nsmul_zero,zero_add,hm]

theorem partialPointSum_nine : partialPointSum C c₀ 9 (by omega) = pointSum C c₀ := by
  rfl

theorem totalFamily_sectionClass :
    Stacks.Picard.schemePullbackClass (normalizationSection C c₀) (familyClass C (totalFamily C c₀)) =
      pointSum C c₀ :=
  (partialFamily_sectionClass C c₀ 9 (by omega)).trans (partialPointSum_nine C c₀)

theorem baseline_sectionClass :
    Stacks.Picard.schemePullbackClass (normalizationSection C c₀)
      (@PoincareChern.lineClass (familySpace C) (baseline C c₀) (baseline_isInvertible C c₀)) =
        pointSum C c₀ := by
  rw [DirectC9FamilyDegree.baseline_class]
  change (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
    (familyClass C (totalFamily C c₀) - familyClass C (constantFamily C c₀ 17)) = _
  have ht : (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
      (familyClass C (totalFamily C c₀)) = pointSum C c₀ := totalFamily_sectionClass C c₀
  have hc : (Stacks.Picard.schemePullbackClassHom (normalizationSection C c₀))
      (familyClass C (constantFamily C c₀ 17)) = 0 := constantFamily_sectionClass C c₀ 17
  rw [map_sub,ht,hc,sub_zero]

/-- The actual retained normalization line has its actual integral Picard class. -/
theorem inverseNormalizationLine_class :
    @PoincareChern.lineClass (power C 9).left (inverseNormalizationLine C c₀)
      (DirectC9FamilyDegree.inverseNormalizationLine_isInvertible C c₀) = -pointSum C c₀ := by
  have hn := @DirectC9PoincareFamily.normalizationLine_class (familySpace C) (power C 9).left
    (normalizationSection C c₀) (baseline C c₀) (baseline_isInvertible C c₀)
  exact hn.trans (congrArg Neg.neg (baseline_sectionClass C c₀))

end M9Native.DirectC9NormalizationClass
