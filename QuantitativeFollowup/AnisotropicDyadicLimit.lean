module
public import QuantitativeFollowup.AnisotropicUniformGrid
public import QuantitativePaper.VectorDyadicLimit

@[expose] public section

/-! The arbitrary-profile anisotropic potential is the genuine uniform limit
of its dyadic finite Gaussian recursions. No diffusion or PDE identification
is assumed in this construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter QuantitativePaper
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
variable {n : ℕ}

def anisotropicDyadicPotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (j : ℕ) : AnisotropicParameter n → ℝ :=
  anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    (vectorDyadicIndex j+3)

theorem anisotropicDyadicPotential_succ_abs_sub_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (j : ℕ) (P : AnisotropicParameter n) :
    |anisotropicDyadicPotential D μ (j+1) P-anisotropicDyadicPotential D μ j P| ≤
      (2*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j := by
  unfold anisotropicDyadicPotential
  rw [vectorDyadicIndex_succ]
  have hh := anisotropicFinitePotential_grid_adjacent_abs_sub_le D μ (vectorDyadicIndex j) P
  rw [show 2*vectorDyadicIndex j+1+3=2*vectorDyadicIndex j+4 by omega]
  have he : 2*anisotropicProfileStabilityConstant D/(vectorDyadicIndex j+1 : ℕ)=
      (2*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j := by
    rw [vectorDyadicIndex_add_one,Nat.cast_pow,Nat.cast_ofNat,div_pow]
    ring
  exact he ▸ hh

theorem cauchySeq_anisotropicDyadicPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    CauchySeq (fun j => anisotropicDyadicPotential D μ j P) := by
  apply cauchySeq_of_le_geometric (1/2) (2*anisotropicProfileStabilityConstant D) (by norm_num)
  intro j
  rw [Real.dist_eq,abs_sub_comm]
  exact anisotropicDyadicPotential_succ_abs_sub_le D μ j P

def anisotropicMeasurePotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (P : AnisotropicParameter n) : ℝ :=
  limUnder atTop (fun j => anisotropicDyadicPotential D μ j P)

theorem tendsto_anisotropicDyadicPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    Tendsto (fun j => anisotropicDyadicPotential D μ j P) atTop
      (𝓝 (anisotropicMeasurePotential D μ P)) :=
  (cauchySeq_anisotropicDyadicPotential D μ P).tendsto_limUnder

theorem anisotropicDyadicPotential_limit_abs_sub_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (j : ℕ) (P : AnisotropicParameter n) :
    |anisotropicDyadicPotential D μ j P-anisotropicMeasurePotential D μ P| ≤
      (4*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j := by
  have hh := dist_le_of_le_geometric_of_tendsto (r:= (1/2 : ℝ))
    (C:=2*anisotropicProfileStabilityConstant D) (by norm_num)
    (fun l => by
      rw [Real.dist_eq,abs_sub_comm]
      exact anisotropicDyadicPotential_succ_abs_sub_le D μ l P)
    (tendsto_anisotropicDyadicPotential D μ P) j
  rw [Real.dist_eq] at hh
  have he : (2*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j/(1-(1/2 : ℝ))=
      (4*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j := by ring
  exact he ▸ hh

theorem tendstoUniformly_anisotropicDyadicPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly (anisotropicDyadicPotential D μ) (anisotropicMeasurePotential D μ) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hh : Tendsto (fun j : ℕ => (4*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ)<1)).const_mul (4*anisotropicProfileStabilityConstant D)
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with j hj
  intro P
  rw [Real.dist_eq,abs_sub_comm]
  exact (anisotropicDyadicPotential_limit_abs_sub_le D μ j P).trans_lt hj

theorem continuous_anisotropicMeasurePotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) : Continuous (anisotropicMeasurePotential D μ) := by
  apply (tendstoUniformly_anisotropicDyadicPotential D μ).continuous
  apply Eventually.frequently
  exact Eventually.of_forall (fun j => (contDiff_anisotropicFinitePotential D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (vectorDyadicIndex j+3)).continuous)

theorem anisotropicMeasurePotential_CDFDistance_abs_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    |anisotropicMeasurePotential D μ P-anisotropicMeasurePotential D ν P| ≤
      anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance μ ν := by
  have hleft := ((tendsto_anisotropicDyadicPotential D μ P).sub
    (tendsto_anisotropicDyadicPotential D ν P)).abs
  have herr : Tendsto (fun j : ℕ => (2 : ℝ)/(vectorDyadicIndex j+1 : ℕ)) atTop (𝓝 0) := by
    simp only [vectorDyadicIndex_add_one,Nat.cast_pow,Nat.cast_ofNat]
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ)<1)).const_mul (2 : ℝ)
    convert hh using 1
    · funext j
      rw [div_pow,one_pow]
      ring
    · simp
  have hright := ((tendsto_const_nhds (x:=Paper.parisiCDFDistance μ ν)).add herr).const_mul
    (anisotropicProfileStabilityConstant D)
  apply le_of_tendsto_of_tendsto hleft (by simpa only [add_zero] using hright)
  exact Eventually.of_forall (fun j => anisotropicFinitePotential_grid_profile_abs_sub_le D μ ν
    (vectorDyadicIndex j) P)

theorem anisotropicMeasurePotential_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    LipschitzWith ‖anisotropicEnergyMap D‖₊ (anisotropicMeasurePotential D μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro P Q
  apply le_of_tendsto
    ((tendsto_anisotropicDyadicPotential D μ P).dist (tendsto_anisotropicDyadicPotential D μ Q))
  exact Eventually.of_forall (fun j =>
    (anisotropicFinitePotential_lipschitz D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (vectorDyadicIndex j+3)).dist_le_mul P Q)

end QuantitativeFollowup
