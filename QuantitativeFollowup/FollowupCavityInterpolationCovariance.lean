module
public import QuantitativeFollowup.FollowupCavityInterpolationRecords
public import QuantitativeFollowup.FollowupCavityInterpolationDerivative
public import FourPapersCommon.ExponentialHeatLinearIntegrability

@[expose] public section

/-! The simultaneous physical derivative as a covariance under the actual
retained-record probability law. Product Fubini, Gaussian integrability and
normalizer differentiation are proved rather than required as premises. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ContDiff ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem integrable_cavityInterpolationSpinResponse_integrand (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (alpha u b : ℝ) (hb : 0<b) :
    Integrable (fun z : CavityPathGaussianSpace T n=>
      cavityPathNumerator D s a i T σ (b,cavityInterpolationGaussianScale p i T u b z)*
        cavityInterpolationRecordScore D p s a i T alpha b
          (cavityPathFixedRecord D s i T σ (cavityInterpolationGaussianScale p i T u b z)))
            (stdGaussian (CavityPathGaussianSpace T n)) := by
  have hs:=exponentialSmoothOn_cavityPathNumerator D s a i T hj σ (b/2) (3*b/2) (by linarith)
  let S:=cavityInterpolationGaussianScale p i T u b
  have hP:=integrable_parameter_fderiv_linear (cavityPathNumerator D s a i T σ)
    (b/2) (3*b/2) b ⟨by linarith,by linarith⟩ hs S
  have hH (mask : AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T→Bool) (e) :
      Integrable (fun z : CavityPathGaussianSpace T n=>if mask e then
        fderiv ℝ (fderiv ℝ (fun y=>cavityPathNumerator D s a i T σ (b,y))) (S z)
          (EuclideanSpace.basisFun _ ℝ e) (EuclideanSpace.basisFun _ ℝ e) else 0)
          (stdGaussian (CavityPathGaussianSpace T n)) := by
    by_cases he:mask e=true
    · simp only [ite_eq_left he]
      exact integrable_parameter_hessian_linear_basis (cavityPathNumerator D s a i T σ)
        (b/2) (3*b/2) b ⟨by linarith,by linarith⟩ hs S e
    · simp only [ite_eq_right he]
      exact integrable_const 0
  have hi : Integrable (fun z : CavityPathGaussianSpace T n=>
      cavityInterpolationHeatGenerator D p s a i T σ alpha b (S z))
        (stdGaussian (CavityPathGaussianSpace T n)) :=
    ((hP.const_mul (-alpha)).add
      ((integrable_finsetSum _ (fun e _=>hH (cavityRootCouplingMask p T) e)).const_mul (1/2))).sub
        ((integrable_finsetSum _ (fun e _=>hH (cavitySelectedRootPathMask i T) e)).const_mul (alpha/2))
  simpa only [cavityInterpolationHeatGenerator_eq_record_score D p s a i T hj σ alpha b hb] using hi

def cavityInterpolationRecordedLaw (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (u b : ℝ) :=
  cavityPathRecordedLaw (anisotropicScaleRootCouplings D p u) s a i T b

theorem integral_cavityInterpolationRecordedLaw_score_mul (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (d alpha u : ℝ) (hb : 0<d-alpha*u) :
    (∫r,F (finiteCascadeRecordTerminalSpins T r.2)*cavityInterpolationRecordScore D p s a i T alpha (d-alpha*u) r
        ∂cavityInterpolationRecordedLaw D p s a i T u (d-alpha*u))=
      (∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha u)/
        (∑σ,cavityInterpolationSpinWeight D p s a i T σ u (d-alpha*u)) := by
  let b:=d-alpha*u
  let E:=anisotropicScaleRootCouplings D p u
  let S:=cavityInterpolationGaussianScale p i T u b
  let f : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T→ℝ:=fun z=>
    F z.2*(cavityPathNumerator D s a i T z.2 (b,S z.1)*
      cavityInterpolationRecordScore D p s a i T alpha b (cavityInterpolationPhysicalRecord D p s i T u b z))
  have hs (σ : TerminalSpins (Configuration n) T):=
    exponentialSmoothOn_cavityPathNumerator D s a i T hj σ (b/2) (3*b/2) (by dsimp only [b];linarith)
  have hn : Measurable (fun z : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T=>
      cavityPathNumerator D s a i T z.2 (b,S z.1)) := by
    apply measurable_from_prod_countable_left
    intro σ
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((hs σ).smooth _ ⟨⟨by dsimp only [b];linarith,by dsimp only [b];linarith⟩,mem_univ _⟩).continuousAt.comp
      (continuous_const.prodMk S.continuous).continuousAt
  have hscore := (measurable_cavityInterpolationRecordScore D p s a i T hj alpha b hb).comp
    (measurable_cavityInterpolationPhysicalRecord D p s i T u b)
  have hm : Measurable f:=((measurable_of_countable F).comp measurable_snd).mul (hn.mul hscore)
  have hi : Integrable f ((stdGaussian (CavityPathGaussianSpace T n)).prod
      (Measure.count : Measure (TerminalSpins (Configuration n) T))):=by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    refine ⟨.of_forall fun σ=>?_,Integrable.of_finite⟩
    dsimp only [f,S]
    simp_rw [cavityInterpolationPhysicalRecord_eq_fixed_record D p s i T u b hb]
    exact (integrable_cavityInterpolationSpinResponse_integrand D p s a i T hj σ alpha u b hb).const_mul (F σ)
  have hmr:=measurable_cavityInterpolationPhysicalRecord D p s i T u b
  change Measurable (cavityPathPhysicalRecord E s i T b) at hmr
  have hf : Measurable (fun r : CavityPathRecordSpace T n=>
      F (finiteCascadeRecordTerminalSpins T r.2)*cavityInterpolationRecordScore D p s a i T alpha b r):=
    ((measurable_of_countable F).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)).mul
      (measurable_cavityInterpolationRecordScore D p s a i T hj alpha b hb)
  change (∫r,F (finiteCascadeRecordTerminalSpins T r.2)*cavityInterpolationRecordScore D p s a i T alpha b r
    ∂cavityPathRecordedLaw E s a i T b)=_
  rw [←cavityPathFlatLaw_physical_records_map E s a i T b,integral_map hmr.aemeasurable hf.aestronglyMeasurable]
  simp_rw [show ∀z,finiteCascadeRecordTerminalSpins T (cavityPathPhysicalRecord E s i T b z).2=z.2 from
    fun z=>finiteCascadeRecordTerminalSpins_referenceRoot _ _ _ _ z.1 z.2]
  unfold cavityPathFlatLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_finiteCascadeTreeGaussianFlatDensity _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _).ennreal_ofReal
    (.of_forall fun _=>ENNReal.ofReal_lt_top) _]
  simp_rw [ENNReal.toReal_ofReal (finiteCascadeTreeGaussianFlatDensity_pos _ _ (anisotropicSchemeMass_nonneg s)
    _ _ _ _ _ _).le]
  have he (z : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) :
      finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance E i b) s) a T (anisotropicRootEnergyMap E) 0 z •
          (F z.2*cavityInterpolationRecordScore D p s a i T alpha b (cavityPathPhysicalRecord E s i T b z))=
        f z/cavityPathNormalizer E s a i j b:=by
    rw [←cavityPathNumerator_scaled_eq_actual_density E s a i T z.2 b hb z.1,
      cavityPathNumerator_scaleRootCouplings]
    dsimp only [f,S,E,cavityInterpolationPhysicalRecord,cavityInterpolationGaussianScale,cavityPathNormalizer]
    simp only [ContinuousLinearMap.comp_apply,smul_eq_mul]
    ring
  simp_rw [he]
  rw [integral_div,finiteCascadeTreeGaussianFlatReferenceMeasure,terminalSpinCountingLaw_eq_count,
    integral_prod_symm f hi,integral_count]
  dsimp only [f]
  simp_rw [integral_const_mul,cavityInterpolationPhysicalRecord_eq_fixed_record D p s i T u b hb]
  have hden : (∑σ,cavityInterpolationSpinWeight D p s a i T σ u b)=cavityPathNormalizer E s a i j b := by
    simp_rw [cavityInterpolationSpinWeight_eq_actual]
    exact sum_cavityPathSpinWeight_eq_normalizer E s a i T b hb
  rw [hden]
  rfl

theorem hasDerivAt_cavityInterpolationMarkedExpectation_recorded_covariance (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (d alpha u : ℝ)
    (ha : 0≤alpha) (hu : 0<u) (hb : 0<d-alpha*u) :
    HasDerivAt (fun q=>cavityInterpolationMarkedExpectation D p s a i T F q (d-alpha*q))
      ((∫r,F (finiteCascadeRecordTerminalSpins T r.2)*cavityInterpolationRecordScore D p s a i T alpha (d-alpha*u) r
          ∂cavityInterpolationRecordedLaw D p s a i T u (d-alpha*u))-
        cavityInterpolationMarkedExpectation D p s a i T F u (d-alpha*u)*
          (∫r,cavityInterpolationRecordScore D p s a i T alpha (d-alpha*u) r
            ∂cavityInterpolationRecordedLaw D p s a i T u (d-alpha*u))) u := by
  have h1:=integral_cavityInterpolationRecordedLaw_score_mul D p s a i T hj (fun _=>1) d alpha u hb
  simp only [one_mul] at h1
  rw [integral_cavityInterpolationRecordedLaw_score_mul D p s a i T hj F d alpha u hb,h1]
  exact hasDerivAt_cavityInterpolationMarkedExpectation D p s a i T hj F d alpha u ha hu hb

end QuantitativeFollowup
