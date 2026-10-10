module
public import QuantitativeFollowup.AnisotropicUniformTail
public import QuantitativeFollowup.AnisotropicDyadicLimit

@[expose] public section

/-! The actual arbitrary-profile anisotropic tail potential is constructed
simultaneously over the entire overlap interval, with uniform geometric error. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter QuantitativePaper
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000

def anisotropicDyadicTailPotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (j : ℕ) : AnisotropicParameter n → ℝ :=
  anisotropicTailRecursion D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q
    (vectorDyadicIndex j+3)

theorem anisotropicDyadicTailPotential_succ_abs_sub_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (j : ℕ) (P : AnisotropicParameter n) :
    |anisotropicDyadicTailPotential D μ q (j+1) P-anisotropicDyadicTailPotential D μ q j P| ≤
      (2*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j := by
  unfold anisotropicDyadicTailPotential
  rw [vectorDyadicIndex_succ]
  have hh := anisotropicTailRecursion_grid_adjacent_abs_sub_le D μ (vectorDyadicIndex j) q q.property P
  rw [show 2*vectorDyadicIndex j+1+3=2*vectorDyadicIndex j+4 by omega]
  have he : 2*anisotropicProfileStabilityConstant D/(vectorDyadicIndex j+1 : ℕ)=
      (2*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j := by
    rw [vectorDyadicIndex_add_one,Nat.cast_pow,Nat.cast_ofNat,div_pow]
    ring
  exact he ▸ hh

theorem cauchySeq_anisotropicDyadicTailPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    CauchySeq (fun j => anisotropicDyadicTailPotential D μ q j P) := by
  apply cauchySeq_of_le_geometric (1/2) (2*anisotropicProfileStabilityConstant D) (by norm_num)
  intro j
  rw [Real.dist_eq,abs_sub_comm]
  exact anisotropicDyadicTailPotential_succ_abs_sub_le D μ q j P

def anisotropicMeasureTailPotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) : ℝ :=
  limUnder atTop (fun j => anisotropicDyadicTailPotential D μ q j P)

theorem tendsto_anisotropicDyadicTailPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    Tendsto (fun j => anisotropicDyadicTailPotential D μ q j P) atTop
      (𝓝 (anisotropicMeasureTailPotential D μ q P)) :=
  (cauchySeq_anisotropicDyadicTailPotential D μ q P).tendsto_limUnder

theorem anisotropicDyadicTailPotential_limit_abs_sub_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (j : ℕ) (P : AnisotropicParameter n) :
    |anisotropicDyadicTailPotential D μ q j P-anisotropicMeasureTailPotential D μ q P| ≤
      (4*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j := by
  have hh := dist_le_of_le_geometric_of_tendsto (r:= (1/2 : ℝ))
    (C:=2*anisotropicProfileStabilityConstant D) (by norm_num)
    (fun l => by
      rw [Real.dist_eq,abs_sub_comm]
      exact anisotropicDyadicTailPotential_succ_abs_sub_le D μ q l P)
    (tendsto_anisotropicDyadicTailPotential D μ q P) j
  rw [Real.dist_eq] at hh
  have he : (2*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j/(1-(1/2 : ℝ))=
      (4*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j := by ring
  exact he ▸ hh

theorem tendstoUniformly_anisotropicDyadicTailPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly
      (fun j => fun z : Paper.Overlap×AnisotropicParameter n => anisotropicDyadicTailPotential D μ z.1 j z.2)
      (fun z => anisotropicMeasureTailPotential D μ z.1 z.2) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hh : Tendsto (fun j : ℕ => (4*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ)<1)).const_mul (4*anisotropicProfileStabilityConstant D)
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with j hj
  intro z
  rw [Real.dist_eq,abs_sub_comm]
  exact (anisotropicDyadicTailPotential_limit_abs_sub_le D μ z.1 j z.2).trans_lt hj

theorem anisotropicMeasureTailPotential_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    anisotropicMeasureTailPotential D μ ⟨0,by norm_num⟩ P=anisotropicMeasurePotential D μ P := by
  apply tendsto_nhds_unique (tendsto_anisotropicDyadicTailPotential D μ ⟨0,by norm_num⟩ P)
  simpa only [anisotropicDyadicTailPotential,anisotropicDyadicPotential,Subtype.coe_mk,
    anisotropicTailRecursion_zero D _ le_rfl] using tendsto_anisotropicDyadicPotential D μ P

theorem anisotropicMeasureTailPotential_one (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    anisotropicMeasureTailPotential D μ ⟨1,by norm_num⟩ P=anisotropicGridTerminalPotential D P := by
  apply tendsto_nhds_unique (tendsto_anisotropicDyadicTailPotential D μ ⟨1,by norm_num⟩ P)
  simpa only [anisotropicDyadicTailPotential,Subtype.coe_mk,
    anisotropicTailRecursion_one D _ le_rfl] using
      (tendsto_const_nhds (x:=anisotropicGridTerminalPotential D P))

theorem anisotropicMeasureTailPotential_CDFDistance_abs_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) :
    |anisotropicMeasureTailPotential D μ q P-anisotropicMeasureTailPotential D ν q P| ≤
      anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance μ ν := by
  have hleft := ((tendsto_anisotropicDyadicTailPotential D μ q P).sub
    (tendsto_anisotropicDyadicTailPotential D ν q P)).abs
  have herr : Tendsto (fun j : ℕ => (2 : ℝ)/(vectorDyadicIndex j+1 : ℕ)) atTop (𝓝 0) := by
    simp only [vectorDyadicIndex_add_one,Nat.cast_pow,Nat.cast_ofNat]
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ)<1)).const_mul (2 : ℝ)
    convert hh using 1
    · funext j;rw [div_pow,one_pow];ring
    · simp
  have hright := ((tendsto_const_nhds (x:=Paper.parisiCDFDistance μ ν)).add herr).const_mul
    (anisotropicProfileStabilityConstant D)
  apply le_of_tendsto_of_tendsto hleft (by simpa only [add_zero] using hright)
  exact Eventually.of_forall (fun j => anisotropicTailRecursion_grid_profile_abs_sub_le D μ ν
    (vectorDyadicIndex j) q q.property P)

end QuantitativeFollowup
