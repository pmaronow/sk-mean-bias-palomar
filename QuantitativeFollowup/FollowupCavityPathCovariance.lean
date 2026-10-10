module
public import QuantitativeFollowup.FollowupCavityPathNormalization
public import FourPapersCommon.GaussianSelectedHeatIntegrability

@[expose] public section

/-! A literal covariance formula for the actual simultaneously varied
path coefficient under the normalized Gaussian-coordinate marked law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ContDiff ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityPathFlatLaw (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) :
    Measure (CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T):=
  (finiteCascadeTreeGaussianFlatReferenceMeasure
    (S:=Configuration n) (I:=Fin n) (J:=AnisotropicCouplingIndex n) T).withDensity
      (fun p=>ENNReal.ofReal (finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s)
          a T (anisotropicRootEnergyMap D) 0 p))

instance cavityPathFlatLaw_probability (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) :
    IsProbabilityMeasure (cavityPathFlatLaw D s a i T b):=
  isProbabilityMeasure_finiteCascadeTreeGaussianFlatDensity _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

def cavityPathFlatScore (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (b : ℝ) (p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T):=
  cavityPathScoreGenerator D s a i T p.2 b (gaussianSelectedScale (cavitySelectedRootPathMask i T) b p.1)

theorem continuous_cavityPathScoreGenerator (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b) :
    Continuous (cavityPathScoreGenerator D s a i T σ b) := by
  have hs:=exponentialSmoothOn_cavityPathNumerator D s a i T hj σ (b/2) (3*b/2) (by linarith)
  have hgen:=continuous_gaussianSelectedHeatGenerator (cavitySelectedRootPathMask i T)
    (cavityPathNumerator D s a i T σ) (b/2) (3*b/2) b ⟨by linarith,by linarith⟩
      (contDiffOn_of_exponentialSmoothOn hs)
  have hnum : Continuous (fun y : CavityPathGaussianSpace T n=>cavityPathNumerator D s a i T σ (b,y)):=by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (hs.smooth (b,y) ⟨⟨by linarith,by linarith⟩,mem_univ y⟩).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt
  have he : cavityPathScoreGenerator D s a i T σ b=
      fun y=>gaussianSelectedHeatGenerator (cavitySelectedRootPathMask i T)
        (cavityPathNumerator D s a i T σ) b y/cavityPathNumerator D s a i T σ (b,y):=by
    funext y
    change _=cavityPathHeatGenerator D s a i T σ b y/_
    rw [cavityPathHeatGenerator_eq_score D s a i T hj σ b hb y]
    exact (mul_div_cancel_left₀ _ (Real.exp_ne_zero _)).symm
  rw [he]
  exact hgen.div hnum (fun y=>Real.exp_ne_zero _)

theorem measurable_cavityPathFlatScore (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (b : ℝ) (hb : 0<b) : Measurable (cavityPathFlatScore D s a i T b):=by
  apply measurable_from_prod_countable_left
  intro σ
  exact ((continuous_cavityPathScoreGenerator D s a i T hj σ b hb).comp
    (gaussianSelectedScale (cavitySelectedRootPathMask i T) b).continuous).measurable

theorem integrable_cavityPathSpinResponse_integrand (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b) :
    Integrable (fun z : CavityPathGaussianSpace T n=>
      cavityPathNumerator D s a i T σ (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)*
        cavityPathScoreGenerator D s a i T σ b (gaussianSelectedScale (cavitySelectedRootPathMask i T) b z))
        (stdGaussian (CavityPathGaussianSpace T n)):=by
  have hs:=exponentialSmoothOn_cavityPathNumerator D s a i T hj σ (b/2) (3*b/2) (by linarith)
  have hh:=integrable_gaussianSelectedHeatGenerator (cavitySelectedRootPathMask i T)
    (cavityPathNumerator D s a i T σ) (b/2) (3*b/2) b (by linarith)
      ⟨by linarith,by linarith⟩ hs
  change Integrable (fun z : CavityPathGaussianSpace T n=>cavityPathHeatGenerator D s a i T σ b
    (gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)) _ at hh
  simpa only [cavityPathHeatGenerator_eq_score D s a i T hj σ b hb] using hh

theorem integral_cavityPathFlatLaw_score_mul (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (b : ℝ) (hb : 0<b) :
    (∫p,F p.2*cavityPathFlatScore D s a i T b p∂cavityPathFlatLaw D s a i T b)=
      (∑σ,F σ*cavityPathSpinResponse D s a i T σ b)/cavityPathNormalizer D s a i j b:=by
  let f : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T→ℝ:=fun p=>
    F p.2*(cavityPathNumerator D s a i T p.2 (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b p.1)*
      cavityPathFlatScore D s a i T b p)
  have hm : Measurable f:=by
    apply measurable_from_prod_countable_left
    intro σ
    dsimp only [f, cavityPathFlatScore]
    have hs:=exponentialSmoothOn_cavityPathNumerator D s a i T hj σ (b/2) (3*b/2) (by linarith)
    have hn : Continuous (fun z : CavityPathGaussianSpace T n=>
        cavityPathNumerator D s a i T σ (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)):=by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (hs.smooth _ ⟨⟨by linarith,by linarith⟩,mem_univ _⟩).continuousAt.comp
        (continuous_const.prodMk (gaussianSelectedScale (cavitySelectedRootPathMask i T) b).continuous).continuousAt
    exact (continuous_const.mul (hn.mul ((continuous_cavityPathScoreGenerator D s a i T hj σ b hb).comp
      (gaussianSelectedScale (cavitySelectedRootPathMask i T) b).continuous))).measurable
  have hi : Integrable f ((stdGaussian (CavityPathGaussianSpace T n)).prod
      (Measure.count : Measure (TerminalSpins (Configuration n) T))):=by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    refine ⟨.of_forall fun σ=>?_,Integrable.of_finite⟩
    exact (integrable_cavityPathSpinResponse_integrand D s a i T hj σ b hb).const_mul (F σ)
  unfold cavityPathFlatLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_finiteCascadeTreeGaussianFlatDensity _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _).ennreal_ofReal
    (.of_forall fun _=>ENNReal.ofReal_lt_top) _]
  simp_rw [ENNReal.toReal_ofReal (finiteCascadeTreeGaussianFlatDensity_pos _ _ (anisotropicSchemeMass_nonneg s)
    _ _ _ _ _ _).le]
  have he (p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) :
      finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T (anisotropicRootEnergyMap D) 0 p •
          (F p.2*cavityPathFlatScore D s a i T b p)=f p/cavityPathNormalizer D s a i j b:=by
    rw [←cavityPathNumerator_scaled_eq_actual_density D s a i T p.2 b hb p.1]
    dsimp only [f]
    simp only [smul_eq_mul]
    unfold cavityPathNormalizer
    ring
  simp_rw [he]
  rw [integral_div,finiteCascadeTreeGaussianFlatReferenceMeasure,terminalSpinCountingLaw_eq_count,
    integral_prod_symm f hi,integral_count]
  dsimp only [f]
  simp_rw [integral_const_mul]
  rfl

theorem hasDerivAt_cavityPathMarkedExpectation_covariance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (b : ℝ) (hb : 0<b) :
    HasDerivAt (cavityPathMarkedExpectation D s a i T F)
      ((∫p,F p.2*cavityPathFlatScore D s a i T b p∂cavityPathFlatLaw D s a i T b)-
        cavityPathMarkedExpectation D s a i T F b*
          (∫p,cavityPathFlatScore D s a i T b p∂cavityPathFlatLaw D s a i T b)) b:=by
  have h1:=integral_cavityPathFlatLaw_score_mul D s a i T hj (fun _=>1) b hb
  simp only [one_mul] at h1
  rw [integral_cavityPathFlatLaw_score_mul D s a i T hj F b hb,h1]
  exact hasDerivAt_cavityPathMarkedExpectation D s a i T hj F b hb

end QuantitativeFollowup
