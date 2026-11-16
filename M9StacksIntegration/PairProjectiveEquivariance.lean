module

public import M9StacksIntegration.PairProjectiveRatios
public import M9StacksIntegration.ConicFrameGammaInvariant
public import M9.FrameQuotientActionComparison

/-! The actual ratio-field isomorphism intertwines the two original raw
matrix deck maps and the original swap. The target automorphisms below
are genuine restrictions of those ambient operators, not postulated
actions on an independently chosen rational field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000

namespace M9Native.PairProjectiveEquivariance

open MvPolynomial
open M9.ProjectiveNoName M9.FrameFieldElimination
open PairProjectiveRatios ConicFrameIndependentPairAction

abbrev Index := PairProjectiveRatios.Index
abbrev OneField := ConicFrameIndependentPairAction.OneField
abbrev PairField := ConicFrameIndependentPairAction.PairField
abbrev PF := PairProjectiveRatios.PF
abbrev Target := PairProjectiveRatios.Target
abbrev RawMat := Matrix (Fin 3) (Fin 3) PF

attribute [local instance] MvPolynomial.algebraMvPolynomial

def firstBlock : OneField →ₐ[ℂ] PF := pairRatioEmbedding.comp coefficientEmbedding
def secondBlock : OneField →ₐ[ℂ] PF := pairRatioEmbedding.comp outerEmbedding

theorem firstBlock_variable (i : Index) :
    firstBlock (oneVariable i) =
      firstFrame ℂ (affinePosition i).1 (affinePosition i).2 / firstFrame ℂ 0 0 :=
  pairRatioEmbedding_firstVariable i

theorem secondBlock_variable (i : Index) :
    secondBlock (oneVariable i) =
      secondFrame ℂ (affinePosition i).1 (affinePosition i).2 / secondFrame ℂ 0 0 := by
  change pairRatioEmbedding (outerEmbedding (oneVariable i)) = _
  rw [outerEmbedding_variable]
  exact pairRatioEmbedding_secondVariable i

/-- A field map with the specified actual normalized entries maps the
literal universal normalized frame to the original normalized matrix. -/
theorem genericFrame_map (φ : OneField →ₐ[ℂ] PF) (F : RawMat)
    (hF : F 0 0 ≠ 0)
    (hX : ∀ i : Index, φ (oneVariable i) = F (affinePosition i).1 (affinePosition i).2 / F 0 0) :
    ConicFrameRationalGamma.genericFrame.map φ.toRingHom = (F 0 0)⁻¹ • F := by
  ext i j
  change φ (ConicFrameRationalGamma.genericFrame i j) = (F 0 0)⁻¹ * F i j
  fin_cases i <;> fin_cases j
  · simpa [ConicFrameRationalGamma.genericFrame,ConicFrameProjective.normalizedFrame] using
      (inv_mul_cancel₀ hF).symm
  · change φ (oneVariable 0) = (F 0 0)⁻¹ * F 0 1
    exact (hX 0).trans (div_eq_inv_mul _ _)
  · change φ (oneVariable 1) = (F 0 0)⁻¹ * F 0 2
    exact (hX 1).trans (div_eq_inv_mul _ _)
  · change φ (oneVariable 2) = (F 0 0)⁻¹ * F 1 0
    exact (hX 2).trans (div_eq_inv_mul _ _)
  · change φ (oneVariable 3) = (F 0 0)⁻¹ * F 1 1
    exact (hX 3).trans (div_eq_inv_mul _ _)
  · change φ (oneVariable 4) = (F 0 0)⁻¹ * F 1 2
    exact (hX 4).trans (div_eq_inv_mul _ _)
  · change φ (oneVariable 5) = (F 0 0)⁻¹ * F 2 0
    exact (hX 5).trans (div_eq_inv_mul _ _)
  · change φ (oneVariable 6) = (F 0 0)⁻¹ * F 2 1
    exact (hX 6).trans (div_eq_inv_mul _ _)
  · change φ (oneVariable 7) = (F 0 0)⁻¹ * F 2 2
    exact (hX 7).trans (div_eq_inv_mul _ _)

theorem rightFrame_map (φ : OneField →ₐ[ℂ] PF) (F : RawMat)
    (hF : F 0 0 ≠ 0)
    (hX : ∀ i : Index, φ (oneVariable i) = F (affinePosition i).1 (affinePosition i).2 / F 0 0)
    (a : ConicFrameGammaAction.Gamma) :
    (ConicFrameGammaInvariant.rightFrame a).map φ.toRingHom =
      (F 0 0)⁻¹ • (F * (M9.TetrahedralGroup.matrix a).map (algebraMap ℂ PF)) := by
  have hc : ((M9.TetrahedralGroup.matrix a).map (algebraMap ℂ OneField)).map φ.toRingHom =
      (M9.TetrahedralGroup.matrix a).map (algebraMap ℂ PF) := by
    ext i j
    exact φ.commutes _
  rw [ConicFrameGammaInvariant.rightFrame,Matrix.map_mul,genericFrame_map φ F hF hX,hc,
    Matrix.smul_mul]

theorem block_rho_variable (φ : OneField →ₐ[ℂ] PF) (F : RawMat)
    (hF : F 0 0 ≠ 0)
    (hX : ∀ i : Index, φ (oneVariable i) = F (affinePosition i).1 (affinePosition i).2 / F 0 0)
    (a : ConicFrameGammaAction.Gamma) (i : Index) :
    φ (oneRepresentation a (oneVariable i)) =
      (F * (M9.TetrahedralGroup.matrix a).map (algebraMap ℂ PF))
          (affinePosition i).1 (affinePosition i).2 /
        (F * (M9.TetrahedralGroup.matrix a).map (algebraMap ℂ PF)) 0 0 := by
  have hr : oneRepresentation a (oneVariable i) =
      ConicFrameGammaInvariant.rightFrame a (affinePosition i).1 (affinePosition i).2 /
        ConicFrameGammaInvariant.rightFrame a 0 0 := by
    exact (ConicFrameGammaInvariant.rationalRepresentation_X_rightFrame a i).trans
      (div_eq_inv_mul _ _).symm
  rw [hr,map_div₀]
  have he (j k : Fin 3) :
      φ (ConicFrameGammaInvariant.rightFrame a j k) =
        (F * (M9.TetrahedralGroup.matrix a).map (algebraMap ℂ PF)) j k / F 0 0 := by
    have hh := congrFun (congrFun (rightFrame_map φ F hF hX a) j) k
    change φ (ConicFrameGammaInvariant.rightFrame a j k) =
      (F 0 0)⁻¹ * (F * (M9.TetrahedralGroup.matrix a).map (algebraMap ℂ PF)) j k at hh
    exact hh.trans (div_eq_inv_mul _ _).symm
  rw [he,he,div_div_div_cancel_right₀ hF]

/-- The full one-cover field action is compared with an actual ambient
matrix operator, by the literal normalized entries and fraction-field UP. -/
theorem block_rho_intertwine (φ : OneField →ₐ[ℂ] PF) (F : RawMat)
    (hF : F 0 0 ≠ 0)
    (hX : ∀ i : Index, φ (oneVariable i) = F (affinePosition i).1 (affinePosition i).2 / F 0 0)
    (a : ConicFrameGammaAction.Gamma) (D : PF ≃ₐ[ℂ] PF)
    (hD : F.map D.toRingHom = F * (M9.TetrahedralGroup.matrix a).map (algebraMap ℂ PF))
    (x : OneField) : φ (oneRepresentation a x) = D (φ x) := by
  have hh : φ.toRingHom.comp (oneRepresentation a).toRingHom = D.toRingHom.comp φ.toRingHom := by
    apply rationalRingHom_ext ℂ Index
    · intro c
      change φ (oneRepresentation a (algebraMap ℂ OneField c)) = D (φ (algebraMap ℂ OneField c))
      simp only [AlgEquiv.commutes,AlgHom.commutes]
    · intro i
      change φ (oneRepresentation a (oneVariable i)) = D (φ (oneVariable i))
      rw [block_rho_variable φ F hF hX a i,hX,map_div₀]
      have he (j k : Fin 3) : D (F j k) =
          (F * (M9.TetrahedralGroup.matrix a).map (algebraMap ℂ PF)) j k :=
        congrFun (congrFun hD j) k
      rw [he,he]
  exact DFunLike.congr_fun hh x

theorem block_fixed_of_entries (φ : OneField →ₐ[ℂ] PF) (F : RawMat)
    (hX : ∀ i : Index, φ (oneVariable i) = F (affinePosition i).1 (affinePosition i).2 / F 0 0)
    (D : PF ≃ₐ[ℂ] PF) (hD : ∀ j k, D (F j k) = F j k)
    (x : OneField) : D (φ x) = φ x := by
  have hh : D.toRingHom.comp φ.toRingHom = φ.toRingHom := by
    apply rationalRingHom_ext ℂ Index
    · intro c
      change D (φ (algebraMap ℂ OneField c)) = φ (algebraMap ℂ OneField c)
      simp only [AlgEquiv.commutes,AlgHom.commutes]
    · intro i
      change D (φ (oneVariable i)) = φ (oneVariable i)
      rw [hX,map_div₀,hD,hD]
  exact DFunLike.congr_fun hh x

theorem firstBlock_firstDeck (a : ConicFrameGammaAction.Gamma) (x : OneField) :
    firstBlock (oneRepresentation a x) =
      M9.FrameQuotientActionComparison.firstDeck (M9.FrameAction.tetrahedralGL a) (firstBlock x) := by
  apply block_rho_intertwine firstBlock (firstFrame ℂ)
    (firstFrame_ne_zero (0,0)) firstBlock_variable a
  ext i j
  exact M9.FrameQuotientActionComparison.firstDeck_firstFrame (M9.FrameAction.tetrahedralGL a) i j

theorem secondBlock_firstDeck (a : ConicFrameGammaAction.Gamma) (x : OneField) :
    M9.FrameQuotientActionComparison.firstDeck (M9.FrameAction.tetrahedralGL a) (secondBlock x) =
      secondBlock x :=
  block_fixed_of_entries secondBlock (secondFrame ℂ) secondBlock_variable _
    (M9.FrameQuotientActionComparison.firstDeck_secondFrame _) x

theorem firstBlock_secondDeck (b : ConicFrameGammaAction.Gamma) (x : OneField) :
    M9.FrameQuotientActionComparison.secondDeck (M9.FrameAction.tetrahedralGL b) (firstBlock x) =
      firstBlock x :=
  block_fixed_of_entries firstBlock (firstFrame ℂ) firstBlock_variable _
    (M9.FrameQuotientActionComparison.secondDeck_firstFrame _) x

theorem secondBlock_secondDeck (b : ConicFrameGammaAction.Gamma) (x : OneField) :
    secondBlock (oneRepresentation b x) =
      M9.FrameQuotientActionComparison.secondDeck (M9.FrameAction.tetrahedralGL b) (secondBlock x) := by
  apply block_rho_intertwine secondBlock (secondFrame ℂ)
    (secondFrame_ne_zero (0,0)) secondBlock_variable b
  ext i j
  exact M9.FrameQuotientActionComparison.secondDeck_secondFrame (M9.FrameAction.tetrahedralGL b) i j

theorem pairRatioEmbedding_firstDeck (a : ConicFrameGammaAction.Gamma) (z : PairField) :
    pairRatioEmbedding (coefficientRepresentation a z) =
      M9.FrameQuotientActionComparison.firstDeck (M9.FrameAction.tetrahedralGL a) (pairRatioEmbedding z) := by
  have hh : pairRatioEmbedding.toRingHom.comp (coefficientRepresentation a).toRingHom =
      (M9.FrameQuotientActionComparison.firstDeck (M9.FrameAction.tetrahedralGL a)).toRingHom.comp
        pairRatioEmbedding.toRingHom := by
    apply rationalRingHom_ext OneField Index
    · intro x
      change pairRatioEmbedding (coefficientRepresentation a (coefficientEmbedding x)) = _
      rw [coefficientRepresentation_coefficient]
      exact firstBlock_firstDeck a x
    · intro i
      change pairRatioEmbedding (coefficientRepresentation a (outerVariable i)) =
        M9.FrameQuotientActionComparison.firstDeck (M9.FrameAction.tetrahedralGL a)
          (pairRatioEmbedding (outerVariable i))
      simp only [← outerEmbedding_variable]
      rw [coefficientRepresentation_outer]
      exact (secondBlock_firstDeck a _).symm
  exact DFunLike.congr_fun hh z

theorem pairRatioEmbedding_secondDeck (b : ConicFrameGammaAction.Gamma) (z : PairField) :
    pairRatioEmbedding (outerRepresentation b z) =
      M9.FrameQuotientActionComparison.secondDeck (M9.FrameAction.tetrahedralGL b) (pairRatioEmbedding z) := by
  have hh : pairRatioEmbedding.toRingHom.comp (outerRepresentation b).toRingHom =
      (M9.FrameQuotientActionComparison.secondDeck (M9.FrameAction.tetrahedralGL b)).toRingHom.comp
        pairRatioEmbedding.toRingHom := by
    apply rationalRingHom_ext OneField Index
    · intro x
      change pairRatioEmbedding (outerRepresentation b (coefficientEmbedding x)) = _
      rw [outerRepresentation_coefficient]
      exact (firstBlock_secondDeck b x).symm
    · intro i
      change pairRatioEmbedding (outerRepresentation b (outerVariable i)) =
        M9.FrameQuotientActionComparison.secondDeck (M9.FrameAction.tetrahedralGL b)
          (pairRatioEmbedding (outerVariable i))
      simp only [← outerEmbedding_variable]
      rw [outerRepresentation_outer]
      exact secondBlock_secondDeck b _
  exact DFunLike.congr_fun hh z

theorem firstBlock_pairDeck (a b : ConicFrameGammaAction.Gamma) (x : OneField) :
    firstBlock (oneRepresentation a x) =
      M9.FrameQuotientActionComparison.pairDeck a b (firstBlock x) := by
  apply block_rho_intertwine firstBlock (firstFrame ℂ)
    (firstFrame_ne_zero (0,0)) firstBlock_variable a
  exact M9.FrameQuotientActionComparison.pairDeck_firstFrame a b

theorem secondBlock_pairDeck (a b : ConicFrameGammaAction.Gamma) (x : OneField) :
    secondBlock (oneRepresentation b x) =
      M9.FrameQuotientActionComparison.pairDeck a b (secondBlock x) := by
  apply block_rho_intertwine secondBlock (secondFrame ℂ)
    (secondFrame_ne_zero (0,0)) secondBlock_variable b
  exact M9.FrameQuotientActionComparison.pairDeck_secondFrame a b

theorem pairRatioEmbedding_pairDeck (a b : ConicFrameGammaAction.Gamma) (z : PairField) :
    pairRatioEmbedding (pairRepresentation (a,b) z) =
      M9.FrameQuotientActionComparison.pairDeck a b (pairRatioEmbedding z) := by
  change pairRatioEmbedding (coefficientRepresentation a (outerRepresentation b z)) =
    M9.FrameQuotientActionComparison.firstDeck (M9.FrameAction.tetrahedralGL a)
      (M9.FrameQuotientActionComparison.secondDeck (M9.FrameAction.tetrahedralGL b) (pairRatioEmbedding z))
  rw [pairRatioEmbedding_firstDeck,pairRatioEmbedding_secondDeck]

theorem firstBlock_swap (x : OneField) :
    M9.FrameQuotientActionComparison.pairSwap (firstBlock x) = secondBlock x := by
  have hh : M9.FrameQuotientActionComparison.pairSwap.toRingHom.comp firstBlock.toRingHom =
      secondBlock.toRingHom := by
    apply rationalRingHom_ext ℂ Index
    · intro c
      change M9.FrameQuotientActionComparison.pairSwap (firstBlock (algebraMap ℂ OneField c)) =
        secondBlock (algebraMap ℂ OneField c)
      simp only [AlgEquiv.commutes,AlgHom.commutes]
    · intro i
      change M9.FrameQuotientActionComparison.pairSwap (firstBlock (oneVariable i)) =
        secondBlock (oneVariable i)
      rw [firstBlock_variable,secondBlock_variable,map_div₀,
        M9.FrameQuotientActionComparison.pairSwap_firstFrame,
        M9.FrameQuotientActionComparison.pairSwap_firstFrame]
  exact DFunLike.congr_fun hh x

theorem secondBlock_swap (x : OneField) :
    M9.FrameQuotientActionComparison.pairSwap (secondBlock x) = firstBlock x := by
  have hh : M9.FrameQuotientActionComparison.pairSwap.toRingHom.comp secondBlock.toRingHom =
      firstBlock.toRingHom := by
    apply rationalRingHom_ext ℂ Index
    · intro c
      change M9.FrameQuotientActionComparison.pairSwap (secondBlock (algebraMap ℂ OneField c)) =
        firstBlock (algebraMap ℂ OneField c)
      simp only [AlgEquiv.commutes,AlgHom.commutes]
    · intro i
      change M9.FrameQuotientActionComparison.pairSwap (secondBlock (oneVariable i)) =
        firstBlock (oneVariable i)
      rw [secondBlock_variable,firstBlock_variable,map_div₀,
        M9.FrameQuotientActionComparison.pairSwap_secondFrame,
        M9.FrameQuotientActionComparison.pairSwap_secondFrame]
  exact DFunLike.congr_fun hh x

theorem pairRatioEmbedding_swap (z : PairField) :
    pairRatioEmbedding (swap z) =
      M9.FrameQuotientActionComparison.pairSwap (pairRatioEmbedding z) := by
  have hh : pairRatioEmbedding.toRingHom.comp swap.toRingHom =
      M9.FrameQuotientActionComparison.pairSwap.toRingHom.comp pairRatioEmbedding.toRingHom := by
    apply rationalRingHom_ext OneField Index
    · intro x
      change pairRatioEmbedding (swap (coefficientEmbedding x)) = _
      rw [swap_coefficient]
      exact (firstBlock_swap x).symm
    · intro i
      change pairRatioEmbedding (swap (outerVariable i)) =
        M9.FrameQuotientActionComparison.pairSwap (pairRatioEmbedding (outerVariable i))
      simp only [← outerEmbedding_variable]
      rw [swap_outer]
      exact (secondBlock_swap _).symm
  exact DFunLike.congr_fun hh z

/-- Both directions of preservation follow from the proved actual
ambient intertwining and the proved surjective ratio-field image. -/
theorem image_preservation (D : PF ≃ₐ[ℂ] PF) (σ : PairField ≃ₐ[ℂ] PairField)
    (h : ∀ z, pairRatioEmbedding (σ z) = D (pairRatioEmbedding z)) :
    (∀ x ∈ Target, D x ∈ Target) ∧ (∀ x ∈ Target, D.symm x ∈ Target) := by
  constructor
  · intro x hx
    have hx' : x ∈ pairRatioEmbedding.fieldRange := by
      rw [pairRatioEmbedding_fieldRange]
      exact hx
    obtain ⟨z,rfl⟩ := hx'
    change D (pairRatioEmbedding z) ∈ Target
    rw [← h]
    exact pairRatioEmbedding_mem _
  · intro x hx
    have hx' : x ∈ pairRatioEmbedding.fieldRange := by
      rw [pairRatioEmbedding_fieldRange]
      exact hx
    obtain ⟨z,rfl⟩ := hx'
    change D.symm (pairRatioEmbedding z) ∈ Target
    have he : D.symm (pairRatioEmbedding z) = pairRatioEmbedding (σ.symm z) := by
      apply D.injective
      rw [AlgEquiv.apply_symm_apply,← h,AlgEquiv.apply_symm_apply]
    rw [he]
    exact pairRatioEmbedding_mem _

def projectivePairDeck (a b : ConicFrameGammaAction.Gamma) : Target ≃ₐ[ℂ] Target :=
  M9.FrameQuotientActionComparison.restrictFieldEquiv Target
    (M9.FrameQuotientActionComparison.pairDeck a b)
    (image_preservation _ _ (pairRatioEmbedding_pairDeck a b)).1
    (image_preservation _ _ (pairRatioEmbedding_pairDeck a b)).2

def projectiveFirstDeck (a : ConicFrameGammaAction.Gamma) : Target ≃ₐ[ℂ] Target :=
  M9.FrameQuotientActionComparison.restrictFieldEquiv Target
    (M9.FrameQuotientActionComparison.firstDeck (M9.FrameAction.tetrahedralGL a))
    (image_preservation _ _ (pairRatioEmbedding_firstDeck a)).1
    (image_preservation _ _ (pairRatioEmbedding_firstDeck a)).2

def projectiveSecondDeck (b : ConicFrameGammaAction.Gamma) : Target ≃ₐ[ℂ] Target :=
  M9.FrameQuotientActionComparison.restrictFieldEquiv Target
    (M9.FrameQuotientActionComparison.secondDeck (M9.FrameAction.tetrahedralGL b))
    (image_preservation _ _ (pairRatioEmbedding_secondDeck b)).1
    (image_preservation _ _ (pairRatioEmbedding_secondDeck b)).2

def projectivePairSwap : Target ≃ₐ[ℂ] Target :=
  M9.FrameQuotientActionComparison.restrictFieldEquiv Target
    M9.FrameQuotientActionComparison.pairSwap
    (image_preservation _ _ pairRatioEmbedding_swap).1
    (image_preservation _ _ pairRatioEmbedding_swap).2

@[simp] theorem projectivePairDeck_coe (a b : ConicFrameGammaAction.Gamma) (x : Target) :
    (projectivePairDeck a b x : PF) = M9.FrameQuotientActionComparison.pairDeck a b x := rfl

@[simp] theorem projectivePairSwap_coe (x : Target) :
    (projectivePairSwap x : PF) = M9.FrameQuotientActionComparison.pairSwap x := rfl

@[simp] theorem projectiveFirstDeck_coe (a : ConicFrameGammaAction.Gamma) (x : Target) :
    (projectiveFirstDeck a x : PF) =
      M9.FrameQuotientActionComparison.firstDeck (M9.FrameAction.tetrahedralGL a) x := rfl

@[simp] theorem projectiveSecondDeck_coe (b : ConicFrameGammaAction.Gamma) (x : Target) :
    (projectiveSecondDeck b x : PF) =
      M9.FrameQuotientActionComparison.secondDeck (M9.FrameAction.tetrahedralGL b) x := rfl

theorem pairProjectiveEquiv_firstDeck (a : ConicFrameGammaAction.Gamma) (z : PairField) :
    pairProjectiveEquiv (coefficientRepresentation a z) =
      projectiveFirstDeck a (pairProjectiveEquiv z) := by
  apply Subtype.ext
  exact pairRatioEmbedding_firstDeck a z

theorem pairProjectiveEquiv_secondDeck (b : ConicFrameGammaAction.Gamma) (z : PairField) :
    pairProjectiveEquiv (outerRepresentation b z) =
      projectiveSecondDeck b (pairProjectiveEquiv z) := by
  apply Subtype.ext
  exact pairRatioEmbedding_secondDeck b z

theorem pairProjectiveEquiv_pairDeck (a b : ConicFrameGammaAction.Gamma) (z : PairField) :
    pairProjectiveEquiv (pairRepresentation (a,b) z) =
      projectivePairDeck a b (pairProjectiveEquiv z) := by
  apply Subtype.ext
  exact pairRatioEmbedding_pairDeck a b z

theorem pairProjectiveEquiv_swap (z : PairField) :
    pairProjectiveEquiv (swap z) = projectivePairSwap (pairProjectiveEquiv z) := by
  apply Subtype.ext
  exact pairRatioEmbedding_swap z

end M9Native.PairProjectiveEquivariance
