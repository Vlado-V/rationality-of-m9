module

public import M9StacksIntegration.ConicFrameRationalGamma
public import M9.ProjectiveNoName
public import Mathlib.FieldTheory.Fixed

/-! The actual independent two-cover tetrahedral action on the nested
rational field. The first factor acts on coefficients, and the second on
the outer variables. The latter action is conjugated through the frozen
actual variable-swap equivalence. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000

namespace M9Native.ConicFrameIndependentPairAction

open MvPolynomial
open M9.ProjectiveNoName
open ConicFrameGammaAction

attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Index := Fin 8
abbrev OneField := ConicFrameRationalGamma.L
abbrev PairField := FractionRing (MvPolynomial Index OneField)
abbrev PairAut := PairField ≃ₐ[ℂ] PairField

/-- Exactly the already proved one-cover native action in chart00. -/
abbrev oneRepresentation := ConicFrameRationalGamma.rationalRepresentation

def coefficientEmbedding : OneField →ₐ[ℂ] PairField :=
  IsScalarTower.toAlgHom ℂ OneField PairField

def outerEmbedding : OneField →ₐ[ℂ] PairField :=
  coefficientExtend ℂ Index OneField

def oneVariable (i : Index) : OneField :=
  algebraMap (MvPolynomial Index ℂ) OneField (X i)

def outerVariable (i : Index) : PairField :=
  algebraMap (MvPolynomial Index OneField) PairField (X i)

@[simp] theorem outerEmbedding_variable (i : Index) :
    outerEmbedding (oneVariable i) = outerVariable i :=
  coefficientExtend_variable ℂ Index OneField i

theorem pairAut_ext {f g : PairAut}
    (hC : ∀ x : OneField, f (coefficientEmbedding x) = g (coefficientEmbedding x))
    (hX : ∀ i : Index, f (outerVariable i) = g (outerVariable i)) : f = g := by
  have hh : f.toRingHom = g.toRingHom :=
    rationalRingHom_ext OneField Index f.toRingHom g.toRingHom hC hX
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun hh x)

theorem pairAut_ext_embeddings {f g : PairAut}
    (hC : ∀ x : OneField, f (coefficientEmbedding x) = g (coefficientEmbedding x))
    (hV : ∀ x : OneField, f (outerEmbedding x) = g (outerEmbedding x)) : f = g :=
  pairAut_ext hC (fun i => by simpa only [outerEmbedding_variable] using hV (oneVariable i))

def coefficientRepresentation : Gamma →* PairAut where
  toFun g := rationalCoefficientEquiv ℂ Index (oneRepresentation g)
  map_one' := by
    apply pairAut_ext
    · intro x
      change rationalCoefficientEquiv ℂ Index (oneRepresentation 1)
        (algebraMap OneField PairField x) = algebraMap OneField PairField x
      rw [rationalCoefficientEquiv_coefficient,map_one]
      rfl
    · intro i
      exact rationalCoefficientEquiv_variable ℂ Index (oneRepresentation 1) i
  map_mul' g h := by
    apply pairAut_ext
    · intro x
      change rationalCoefficientEquiv ℂ Index (oneRepresentation (g*h))
          (algebraMap OneField PairField x) =
        rationalCoefficientEquiv ℂ Index (oneRepresentation g)
          (rationalCoefficientEquiv ℂ Index (oneRepresentation h) (algebraMap OneField PairField x))
      rw [rationalCoefficientEquiv_coefficient,rationalCoefficientEquiv_coefficient,
        rationalCoefficientEquiv_coefficient,map_mul]
      rfl
    · intro i
      simp only [AlgEquiv.mul_apply,outerVariable,rationalCoefficientEquiv_variable]

@[simp] theorem coefficientRepresentation_coefficient (g : Gamma) (x : OneField) :
    coefficientRepresentation g (coefficientEmbedding x) =
      coefficientEmbedding (oneRepresentation g x) :=
  rationalCoefficientEquiv_coefficient ℂ Index (oneRepresentation g) x

@[simp] theorem coefficientRepresentation_variable (g : Gamma) (i : Index) :
    coefficientRepresentation g (outerVariable i) = outerVariable i :=
  rationalCoefficientEquiv_variable ℂ Index (oneRepresentation g) i

theorem coefficientRepresentation_outer (g : Gamma) (x : OneField) :
    coefficientRepresentation g (outerEmbedding x) = outerEmbedding x := by
  have hh : (coefficientRepresentation g).toRingHom.comp outerEmbedding.toRingHom =
      outerEmbedding.toRingHom := by
    apply rationalRingHom_ext ℂ Index
    · intro c
      change coefficientRepresentation g (outerEmbedding (algebraMap ℂ OneField c)) = _
      rw [outerEmbedding.commutes,(coefficientRepresentation g).commutes]
      exact (outerEmbedding.commutes c).symm
    · intro i
      change coefficientRepresentation g (outerEmbedding (oneVariable i)) = outerEmbedding (oneVariable i)
      rw [outerEmbedding_variable,coefficientRepresentation_variable]
  exact DFunLike.congr_fun hh x

def swap : PairAut := rationalVariableSwap ℂ Index Index

theorem swap_coefficient (x : OneField) : swap (coefficientEmbedding x) = outerEmbedding x := by
  have hh : swap.toRingHom.comp coefficientEmbedding.toRingHom = outerEmbedding.toRingHom := by
    apply rationalRingHom_ext ℂ Index
    · intro c
      change swap (coefficientEmbedding (algebraMap ℂ OneField c)) = outerEmbedding (algebraMap ℂ OneField c)
      rw [coefficientEmbedding.commutes,swap.commutes,outerEmbedding.commutes]
    · intro i
      change rationalVariableSwap ℂ Index Index
        (algebraMap OneField PairField (oneVariable i)) = outerEmbedding (oneVariable i)
      rw [outerEmbedding_variable]
      exact rationalVariableSwap_coefficient ℂ Index Index i
  exact DFunLike.congr_fun hh x

theorem swap_outer (x : OneField) : swap (outerEmbedding x) = coefficientEmbedding x := by
  have hh : swap.toRingHom.comp outerEmbedding.toRingHom = coefficientEmbedding.toRingHom := by
    apply rationalRingHom_ext ℂ Index
    · intro c
      change swap (outerEmbedding (algebraMap ℂ OneField c)) = coefficientEmbedding (algebraMap ℂ OneField c)
      rw [outerEmbedding.commutes,swap.commutes,coefficientEmbedding.commutes]
    · intro i
      change swap (outerEmbedding (oneVariable i)) = coefficientEmbedding (oneVariable i)
      rw [outerEmbedding_variable]
      exact rationalVariableSwap_outer ℂ Index Index i
  exact DFunLike.congr_fun hh x

theorem swap_squared : swap * swap = 1 := by
  apply pairAut_ext_embeddings
  · intro x
    change swap (swap (coefficientEmbedding x)) = coefficientEmbedding x
    rw [swap_coefficient,swap_outer]
  · intro x
    change swap (swap (outerEmbedding x)) = outerEmbedding x
    rw [swap_outer,swap_coefficient]

theorem swap_symm : swap.symm = swap :=
  inv_eq_of_mul_eq_one_left swap_squared

def outerRepresentation : Gamma →* PairAut :=
  (AlgEquiv.autCongr swap).toMonoidHom.comp coefficientRepresentation

theorem outerRepresentation_apply (g : Gamma) (x : PairField) :
    outerRepresentation g x = swap (coefficientRepresentation g (swap x)) := by
  change swap (coefficientRepresentation g (swap.symm x)) = _
  rw [swap_symm]

@[simp] theorem outerRepresentation_coefficient (g : Gamma) (x : OneField) :
    outerRepresentation g (coefficientEmbedding x) = coefficientEmbedding x := by
  rw [outerRepresentation_apply,swap_coefficient,coefficientRepresentation_outer,swap_outer]

@[simp] theorem outerRepresentation_outer (g : Gamma) (x : OneField) :
    outerRepresentation g (outerEmbedding x) = outerEmbedding (oneRepresentation g x) := by
  rw [outerRepresentation_apply,swap_outer,coefficientRepresentation_coefficient,swap_coefficient]

@[simp] theorem outerRepresentation_variable (g : Gamma) (i : Index) :
    outerRepresentation g (outerVariable i) = outerEmbedding (oneRepresentation g (oneVariable i)) := by
  rw [← outerEmbedding_variable,outerRepresentation_outer]

theorem representations_commute (g h : Gamma) :
    Commute (coefficientRepresentation g) (outerRepresentation h) := by
  apply pairAut_ext_embeddings
  · intro x
    simp only [AlgEquiv.mul_apply,outerRepresentation_coefficient,coefficientRepresentation_coefficient]
  · intro x
    simp only [AlgEquiv.mul_apply,outerRepresentation_outer,coefficientRepresentation_outer]

def pairRepresentation : Gamma × Gamma →* PairAut where
  toFun p := coefficientRepresentation p.1 * outerRepresentation p.2
  map_one' := by simp
  map_mul' p q := by
    change coefficientRepresentation (p.1*q.1) * outerRepresentation (p.2*q.2) = _
    rw [map_mul,map_mul]
    calc
      _ = coefficientRepresentation p.1 *
          (coefficientRepresentation q.1 * outerRepresentation p.2) * outerRepresentation q.2 := by
            simp only [mul_assoc]
      _ = coefficientRepresentation p.1 *
          (outerRepresentation p.2 * coefficientRepresentation q.1) * outerRepresentation q.2 := by
            rw [(representations_commute q.1 p.2).eq]
      _ = _ := by simp only [mul_assoc]

@[simp] theorem pairRepresentation_coefficient (p : Gamma × Gamma) (x : OneField) :
    pairRepresentation p (coefficientEmbedding x) = coefficientEmbedding (oneRepresentation p.1 x) := by
  change coefficientRepresentation p.1 (outerRepresentation p.2 (coefficientEmbedding x)) = _
  rw [outerRepresentation_coefficient,coefficientRepresentation_coefficient]

@[simp] theorem pairRepresentation_outer (p : Gamma × Gamma) (x : OneField) :
    pairRepresentation p (outerEmbedding x) = outerEmbedding (oneRepresentation p.2 x) := by
  change coefficientRepresentation p.1 (outerRepresentation p.2 (outerEmbedding x)) = _
  rw [outerRepresentation_outer,coefficientRepresentation_outer]

@[simp] theorem pairRepresentation_variable (p : Gamma × Gamma) (i : Index) :
    pairRepresentation p (outerVariable i) = outerEmbedding (oneRepresentation p.2 (oneVariable i)) := by
  rw [← outerEmbedding_variable,pairRepresentation_outer]

theorem pairRepresentation_injective : Function.Injective pairRepresentation := by
  intro p q hpq
  apply Prod.ext
  · apply ConicFrameRationalGamma.rationalRepresentation_injective
    ext x
    apply coefficientEmbedding.injective
    change coefficientEmbedding (oneRepresentation p.1 x) = coefficientEmbedding (oneRepresentation q.1 x)
    have hh := congrArg (fun σ : PairAut => σ (coefficientEmbedding x)) hpq
    simpa only [pairRepresentation_coefficient] using hh
  · apply ConicFrameRationalGamma.rationalRepresentation_injective
    ext x
    apply outerEmbedding.injective
    change outerEmbedding (oneRepresentation p.2 x) = outerEmbedding (oneRepresentation q.2 x)
    have hh := congrArg (fun σ : PairAut => σ (outerEmbedding x)) hpq
    simpa only [pairRepresentation_outer] using hh

theorem swap_pairRepresentation (p : Gamma × Gamma) (x : PairField) :
    swap (pairRepresentation p x) = pairRepresentation (p.2,p.1) (swap x) := by
  have hh : swap * pairRepresentation p = pairRepresentation (p.2,p.1) * swap := by
    apply pairAut_ext_embeddings
    · intro y
      simp only [AlgEquiv.mul_apply,pairRepresentation_coefficient,swap_coefficient,pairRepresentation_outer]
    · intro y
      simp only [AlgEquiv.mul_apply,pairRepresentation_outer,swap_outer,pairRepresentation_coefficient]
  exact DFunLike.congr_fun hh x

@[instance_reducible] def pairAction : MulSemiringAction (Gamma × Gamma) PairField :=
  MulSemiringAction.compHom PairField pairRepresentation

theorem pairAction_faithful : letI := pairAction; FaithfulSMul (Gamma × Gamma) PairField := by
  letI := pairAction
  refine ⟨fun {p q} hpq => pairRepresentation_injective ?_⟩
  ext x
  exact hpq x

theorem card_gammaPair : Fintype.card (Gamma × Gamma) = 576 := by
  norm_num [Fintype.card_prod,M9.TetrahedralGroup.card_gamma]

theorem finrank_fixedPair :
    letI := pairAction
    Module.finrank (FixedPoints.subfield (Gamma × Gamma) PairField) PairField = 576 := by
  letI := pairAction
  letI := pairAction_faithful
  exact (FixedPoints.finrank_eq_card (Gamma × Gamma) PairField).trans card_gammaPair

end M9Native.ConicFrameIndependentPairAction
