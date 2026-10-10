module
public import QuantitativeFollowup.AnisotropicTailTimeGenerator
public import QuantitativeFollowup.AnisotropicFiniteCell
public import FourPapersCommon.FiniteStateGaussianCurrentGenerator
public import FourPapersCommon.FiniteMeshIntegralEquation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! The actual finite anisotropic time equation, derived inside each
Gaussian cell and then telescoped through the full mesh. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

private theorem finiteTime_cell_unit (s : RSBScheme k) (i : ℕ) (hi : i≤k+1)
    {q : ℝ} (hq : q∈Icc (s.q i) (s.q (i+1))) : q∈Icc (0:ℝ) 1 :=
  ⟨(s.q_nonneg (by omega)).trans hq.1,hq.2.trans (s.q_le_one (by omega))⟩

theorem hasDerivAt_anisotropicFiniteTail_time_cell (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+1) (P : AnisotropicParameter n)
    {q : ℝ} (hq : q∈Ioo (s.q i) (s.q (i+1))) :
    HasDerivAt (fun t => anisotropicFiniteTailPotential D s (projIcc 0 1 zero_le_one t) P)
      (anisotropicFiniteTailTimeSource D s q P) q := by
  let F := anisotropicFinitePotential D s (k+1-i)
  have hF : ContDiff ℝ 2 F := (contDiff_anisotropicFinitePotential D s _).of_le (by simp)
  have hC : ∀H, ‖fderiv ℝ F H‖ ≤ (‖anisotropicEnergyMap D‖₊ : ℝ) :=
    norm_anisotropicFinitePotential_time_first_le D s _
  have hB : ∀H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ ((‖anisotropicEnergyMap D‖₊^2 : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_pow,coe_nnnorm] using norm_anisotropicFinitePotential_time_second_le D s (k+1-i)
  have hd := hasDerivAt_finiteStateGaussianStep_variance_currentGenerator
    (s.m i) (anisotropicUnitInput D) F hF ‖anisotropicEnergyMap D‖₊
    (‖anisotropicEnergyMap D‖₊^2) hC hB P (sub_pos.mpr hq.2)
  have hs := hd.comp q ((hasDerivAt_id q).const_sub (s.q (i+1)))
  have heq (t : ℝ) (ht : t∈Icc (s.q i) (s.q (i+1))) :
      anisotropicFiniteTailPotential D s (projIcc 0 1 zero_le_one t) =
        finiteStateGaussianStep (s.m i) (Real.sqrt (s.q (i+1)-t) • anisotropicUnitInput D) F := by
    unfold anisotropicFiniteTailPotential
    rw [projIcc_of_mem zero_le_one (finiteTime_cell_unit s i hi ht),
      anisotropicTailRecursion_eq_cell D s t i hi ht]
    exact funext (anisotropicGaussianShift_eq_finiteStateStep _ _ _)
  have hg : anisotropicFiniteTailTimeSource D s q P =
      -(finiteStateGaussianGeneratorField (s.m i) (anisotropicUnitInput D)
        (finiteStateGaussianStep (s.m i) (Real.sqrt (s.q (i+1)-q) • anisotropicUnitInput D) F) P) := by
    unfold anisotropicFiniteTailTimeSource
    rw [Paper.parisiCDF_scheme_cell s hi ⟨hq.1.le,hq.2⟩,heq q ⟨hq.1.le,hq.2.le⟩]
  rw [hg]
  have hn : finiteStateGaussianGeneratorField (s.m i) (anisotropicUnitInput D)
      (finiteStateGaussianStep (s.m i) (Real.sqrt (s.q (i+1)-q) • anisotropicUnitInput D) F) P * (-1) =
      -finiteStateGaussianGeneratorField (s.m i) (anisotropicUnitInput D)
        (finiteStateGaussianStep (s.m i) (Real.sqrt (s.q (i+1)-q) • anisotropicUnitInput D) F) P := by ring
  rw [hn] at hs
  apply hs.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
  exact congrFun (heq t ⟨ht.1.le,ht.2.le⟩) P

theorem anisotropicFiniteTail_time_cell_integral (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+1) (P : AnisotropicParameter n)
    (a b : ℝ) (ha : a∈Icc (s.q i) (s.q (i+1)))
    (hb : b∈Icc (s.q i) (s.q (i+1))) (hab : a≤b) :
    anisotropicFiniteTailPotential D s (projIcc 0 1 zero_le_one b) P-
      anisotropicFiniteTailPotential D s (projIcc 0 1 zero_le_one a) P =
        ∫t in a..b,anisotropicFiniteTailTimeSource D s t P := by
  apply Eq.symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact ((continuous_anisotropicFiniteTailPotential_joint D s).comp
      (show Continuous (fun t : ℝ => (projIcc 0 1 zero_le_one t,P)) from
        continuous_projIcc.prodMk continuous_const)).continuousOn
  · intro t ht
    exact hasDerivAt_anisotropicFiniteTail_time_cell D s i hi P
      ⟨ha.1.trans_lt ht.1,ht.2.trans_le hb.2⟩
  · exact anisotropicFiniteTailTimeSource_intervalIntegrable D s P a b

theorem anisotropicFiniteTail_time_integral (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (P : AnisotropicParameter n) (a b : Paper.Overlap) (hab : a≤b) :
    anisotropicFiniteTailPotential D s b P-anisotropicFiniteTailPotential D s a P =
      ∫t in (a:ℝ)..(b:ℝ),anisotropicFiniteTailTimeSource D s t P := by
  have hq : MonotoneOn s.q (Icc 0 (k+2)) := by
    intro i hi j hj hij
    exact s.q_mono' j hj.2 i hij
  have he := finiteMesh_integralEquation (k+2) s.q hq s.q_zero s.q_top
    (fun t => anisotropicFiniteTailPotential D s (projIcc 0 1 zero_le_one t) P)
    (fun t => anisotropicFiniteTailTimeSource D s t P)
    (anisotropicFiniteTailTimeSource_intervalIntegrable D s P 0 1)
    (fun i hi a ha b hb hab => anisotropicFiniteTail_time_cell_integral D s i (by omega) P a b ha hb hab)
    a b a.property b.property hab
  simpa only [projIcc_of_mem zero_le_one a.property,projIcc_of_mem zero_le_one b.property] using he

end QuantitativeFollowup
