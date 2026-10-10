module
public import QuantitativeFollowup.AnisotropicSpinSecondConditional
public import QuantitativeFollowup.AnisotropicSpinPathConditionals
public import FourPapersCommon.ConditionalPullback

@[expose] public section

/-! Literal terminal row-parameter differentiation under the actual single-leaf
law. The field-coordinate perturbation adds exactly theta times the terminal
single-spin feature. The variance-coefficient derivative is a separate identity. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def anisotropicSpinParameterPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : Fin n) (θ : ℝ) : ℝ :=
  anisotropicMeasureTailPotential D μ q
    (P+θ • anisotropicCoordinateDirection n e)

theorem anisotropicSpinParameter_terminal_feature (D : AnisotropicSpinModel n)
    (P : AnisotropicParameter n) (e : Fin n) (θ : ℝ)
    (σ : Configuration n) :
    anisotropicEnergyMap D
      (P+θ • anisotropicCoordinateDirection n e) σ=
        anisotropicEnergyMap D P σ+θ*(Paper.spinSign (σ e)) := by
  rw [map_add,map_smul]
  change anisotropicEnergyMap D P σ+θ*anisotropicTerminalLinear
    D σ (anisotropicCoordinateDirection n e)=_
  rw [anisotropicTerminalLinear_coordinate]

theorem hasDerivAt_anisotropicSpinParameterPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : Fin n) (θ : ℝ) :
    HasDerivAt (anisotropicSpinParameterPotential D μ q P e)
      (fderiv ℝ (anisotropicMeasureTailPotential D μ q)
        (P+θ • anisotropicCoordinateDirection n e)
          (anisotropicCoordinateDirection n e)) θ :=
  hasDerivAt_affine_line_of_differentiable _
    (anisotropicMeasureTailPotential_derivative_limit D μ q).2.differentiable_one
    _ _ θ

theorem hasDerivAt_anisotropicSpinParameterPotential_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : Fin n) :
    HasDerivAt (anisotropicSpinParameterPotential D μ q P e)
      (anisotropicMeasureTailMagnetization D μ q P e) 0 := by
  change HasDerivAt (anisotropicSpinParameterPotential D μ q P e)
    (fderiv ℝ (anisotropicMeasureTailPotential D μ q) P (anisotropicCoordinateDirection n e)) 0
  simpa only [zero_smul,add_zero] using
    hasDerivAt_anisotropicSpinParameterPotential D μ q P e 0

theorem hasDerivAt_anisotropicSpinParameterPotential_first_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : Fin n) :
    HasDerivAt (fun θ=>deriv (anisotropicSpinParameterPotential D μ q P e) θ)
      (anisotropicTailSpinSecond D μ q P e) 0 := by
  let U:=anisotropicMeasureTailPotential D μ q
  let K:=anisotropicCoordinateDirection n e
  let H:=P
  have hD : ContDiff ℝ 1 (fderiv ℝ U):=
    (anisotropicMeasureTailPotential_hessian_limit D μ q).2.fderiv_right (by norm_num)
  have hh:=(hD.differentiable_one (H+(0:ℝ) • K)).hasFDerivAt
  have hc:=hh.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).smul_const K |>.const_add H)
  have he:=hc.clm_apply (hasDerivAt_const (0:ℝ) K)
  have hd (θ : ℝ) := (hasDerivAt_anisotropicSpinParameterPotential D μ q P e θ).deriv
  simp_rw [hd]
  simpa only [Function.comp_def,id_eq,one_smul,zero_smul,add_zero,map_zero,
    anisotropicTailSpinSecond,U,H,K] using he

theorem anisotropic_marked_spin_second_nodeResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (e : Fin n) :
    (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
      anisotropicProcessSpinSecond D μ q e p.1)=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>1-Paper.parisiCDF μ q*(anisotropicProcessSpinResponse D μ q e p.1)^2-
        ∫r : Paper.Overlap,if q < r then anisotropicPastSpinSquareKernel D μ a q r e p.1 else 0
          ∂parisiFreeMeasure μ a :=
  (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).quasiMeasurePreserving.ae
    (anisotropic_spin_second_nodeResponse D μ a ha hμ q e)

theorem anisotropic_marked_spin_square_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap)
    (e : Fin n) :
    (anisotropicMeasureSpinPathLaw D μ a)[
      (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
        (anisotropicProcessSpinResponse D μ r e p.1)^2)|anisotropicSpinPast n (q:ℝ).toNNReal]
      =ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicPastSpinSquareKernel D μ a q r e p.1 := by
  let F:=fun p : AnisotropicDisorderBrownianSample n=>(anisotropicProcessSpinResponse D μ r e p)^2
  have hF : Measurable F:=(measurable_anisotropicProcessSpinResponse D μ r e).pow_const 2
  have hi : Integrable F (anisotropicMeasureSampleLaw D μ a):=
    (integrable_const (1:ℝ)).mono' hF.aestronglyMeasurable (.of_forall fun p=>by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessSpinResponse_bound D μ r e p) 2).trans_eq (by norm_num))
  have h:=condExp_comp_of_measurePreserving
    (anisotropicMeasureSpinPathLaw D μ a) (anisotropicMeasureSampleLaw D μ a) Prod.fst
    (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a)
    (anisotropicBrownianFiltration n (q:ℝ).toNNReal) ((anisotropicBrownianFiltration n).le _) F hF hi
  exact h.trans ((measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).quasiMeasurePreserving.ae
    (anisotropicPastSpinSquareKernel_condExp D μ a q r e))

theorem anisotropic_marked_spin_parameter_nodeResponse (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (e : Fin n) :
    ∀ᵐp : AnisotropicDisorderBrownianSample n×Configuration n ∂anisotropicMeasureSpinPathLaw D μ a,
      HasDerivAt (anisotropicSpinParameterPotential D μ q (anisotropicProcessParameter D μ q p.1) e)
        ((anisotropicMeasureSpinPathLaw D μ a)[
          fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
            Paper.spinSign (z.2 e)|
              anisotropicSpinPast n (q:ℝ).toNNReal] p) 0 ∧
      HasDerivAt (fun θ=>deriv
        (anisotropicSpinParameterPotential D μ q (anisotropicProcessParameter D μ q p.1) e) θ)
        (1-Paper.parisiCDF μ q*(anisotropicProcessSpinResponse D μ q e p.1)^2-
          ∫r : Paper.Overlap,if q < r then anisotropicPastSpinSquareKernel D μ a q r e p.1 else 0
            ∂parisiFreeMeasure μ a) 0 := by
  filter_upwards [anisotropicMeasureSpinPathLaw_spin_condExp D μ a q e,
    anisotropic_marked_spin_second_nodeResponse D μ a ha hμ q e] with p hfirst hsecond
  constructor
  · rw [hfirst]
    exact hasDerivAt_anisotropicSpinParameterPotential_zero D μ q _ e
  · rw [←hsecond]
    exact hasDerivAt_anisotropicSpinParameterPotential_first_zero D μ q _ e

end QuantitativeFollowup
