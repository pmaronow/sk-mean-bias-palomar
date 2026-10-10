module
public import QuantitativeFollowup.AnisotropicTailTimeFinite
public import FRSB.ParisiMeasureTopology
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! The genuine time equation for every actual probability profile,
obtained from finite Gaussian cells and their spatial jet limits. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem tendsto_integral_anisotropicDyadicTailTimeSource (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (a b : ℝ) :
    Tendsto (fun j => ∫t in a..b,anisotropicFiniteTailTimeSource D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) t P) atTop
      (𝓝 (∫t in a..b,anisotropicMeasureTailTimeSource D μ t P)) := by
  have hindex : Tendsto vectorDyadicIndex atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hp : Tendsto (fun j : ℕ => (2 : ℕ)^j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by omega : 1<(2 : ℕ))
    filter_upwards [hp.eventually (eventually_ge_atTop (b+1))] with j hj
    unfold vectorDyadicIndex
    omega
  have hweak : Tendsto (fun j => Paper.parisiGridMeasure μ (vectorDyadicIndex j)) atTop (𝓝 μ) :=
    (FRSB.tendsto_parisiGridMeasure μ).comp hindex
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound:=fun _ => anisotropicTailTimeSourceBound D)
  · exact .of_forall fun j => (measurable_anisotropicFiniteTailTimeSource D _ P).aestronglyMeasurable
  · exact .of_forall fun j => .of_forall fun t _ => norm_anisotropicFiniteTailTimeSource_le D _ t P
  · exact intervalIntegrable_const
  · filter_upwards [FRSB.ae_parisi_level_null μ] with t ht
    intro _
    have hα := FRSB.tendsto_parisiCDF_of_level_null hweak ht
    have hg := (tendstoUniformly_anisotropicDyadicTailDifferential D μ).tendsto_at
      (projIcc 0 1 zero_le_one t,P)
    have hh := (tendstoUniformly_anisotropicDyadicTailSecondDifferential D μ).tendsto_at
      (projIcc 0 1 zero_le_one t,P)
    simp only [anisotropicFiniteTailTimeSource,anisotropicMeasureTailTimeSource,
      FRSB.parisiSchemeMeasure_grid_eq,finiteStateGaussianGeneratorField]
    apply Tendsto.neg
    apply Tendsto.div_const
    apply tendsto_finsetSum
    intro i _
    let w := anisotropicUnitInput D (finiteStateGaussianBasis (Fin n) i)
    have hEval2 : Continuous (fun T : AnisotropicParameter n →L[ℝ] AnisotropicParameter n →L[ℝ] ℝ => T w w) :=
      (continuous_id.clm_apply continuous_const).clm_apply continuous_const
    have hEval1 : Continuous (fun T : AnisotropicParameter n →L[ℝ] ℝ => T w) :=
      continuous_id.clm_apply continuous_const
    exact (hEval2.continuousAt.tendsto.comp hh).add
      (hα.mul ((hEval1.continuousAt.tendsto.comp hg).pow 2))

theorem anisotropicMeasureTail_time_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (a b : Paper.Overlap) (hab : a≤b) :
    anisotropicMeasureTailPotential D μ b P-anisotropicMeasureTailPotential D μ a P =
      ∫t in (a:ℝ)..(b:ℝ),anisotropicMeasureTailTimeSource D μ t P := by
  have hleft := (tendsto_anisotropicDyadicTailPotential D μ b P).sub
    (tendsto_anisotropicDyadicTailPotential D μ a P)
  have hright := tendsto_integral_anisotropicDyadicTailTimeSource D μ P a b
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro j
  exact (anisotropicFiniteTail_time_integral D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) P a b hab).symm

theorem hasDerivAt_anisotropicMeasureTail_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (q : ℝ)
    (hq : q∈Ioo (0:ℝ) 1) (hCDF : ContinuousAt (Paper.parisiCDF μ) q) :
    HasDerivAt (fun t => anisotropicMeasureTailPotential D μ (projIcc 0 1 zero_le_one t) P)
      (anisotropicMeasureTailTimeSource D μ q P) q := by
  have hs := intervalIntegral.integral_hasDerivAt_right
    (anisotropicMeasureTailTimeSource_intervalIntegrable D μ P 0 q)
    (measurable_anisotropicMeasureTailTimeSource D μ P).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_anisotropicMeasureTailTimeSource D μ P q hCDF)
  have hd := hs.const_add (anisotropicMeasureTailPotential D μ 0 P)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
  have he := anisotropicMeasureTail_time_integral D μ P 0 ⟨t,ht.1.le,ht.2.le⟩ ht.1.le
  rw [projIcc_of_mem zero_le_one ⟨ht.1.le,ht.2.le⟩]
  change anisotropicMeasureTailPotential D μ ⟨t,ht.1.le,ht.2.le⟩ P = _
  simp only [Set.Icc.coe_zero,Subtype.coe_mk] at he
  linarith

theorem ae_hasDerivAt_anisotropicMeasureTail_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    ∀ᵐ q ∂volume, q∈Ioo (0:ℝ) 1 →
      HasDerivAt (fun t => anisotropicMeasureTailPotential D μ (projIcc 0 1 zero_le_one t) P)
        (anisotropicMeasureTailTimeSource D μ q P) q := by
  filter_upwards [(Paper.parisiCDF_monotone μ).countable_not_continuousAt.ae_notMem volume]
    with q hq hunit
  exact hasDerivAt_anisotropicMeasureTail_time D μ P q hunit (by simpa using hq)

end QuantitativeFollowup
