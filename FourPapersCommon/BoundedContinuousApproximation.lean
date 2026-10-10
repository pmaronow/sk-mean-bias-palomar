module
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Bounded measurable real functions admit continuous approximations
with the identical uniform bound and genuine almost-everywhere convergence.
The proof uses continuous density in L2 and clamps only after selecting
an almost-everywhere convergent subsequence. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem exists_continuous_bounded_ae_approximation {α : Type*}
    [PseudoMetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] [ν.WeaklyRegular]
    (f : α→ℝ) (hf : Measurable f) (K : ℝ) (hK : 0≤K) (hB : ∀x,|f x|≤K) :
    ∃g : ℕ→α→ℝ,(∀j,Continuous (g j)) ∧ (∀j x,|g j x|≤K) ∧
      ∀ᵐx ∂ν,Tendsto (fun j=>g j x) atTop (𝓝 (f x)) := by
  have hLp : MemLp f 2 ν:=MemLp.of_bound hf.aestronglyMeasurable K
    (.of_forall fun x=>by simpa only [Real.norm_eq_abs] using hB x)
  have he (j : ℕ) : ENNReal.ofReal ((1 : ℝ)/((j : ℝ)+1))≠0 := by
    rw [ne_eq,ENNReal.ofReal_eq_zero]
    exact not_le.mpr (by positivity)
  choose g hg hgm using fun j : ℕ=>hLp.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (he j)
  have hlim : Tendsto (fun j=>eLpNorm (fun x=>g j x-f x) 2 ν) atTop (𝓝 0) := by
    have hzero : Tendsto (fun _ : ℕ=>(0 : ℝ≥0∞)) atTop (𝓝 0):=tendsto_const_nhds
    have hupper : Tendsto (fun j : ℕ=>ENNReal.ofReal ((1 : ℝ)/((j : ℝ)+1))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
        tendsto_one_div_add_atTop_nhds_zero_nat
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hzero hupper (fun _=>bot_le) fun j=>?_
    change eLpNorm ((g j : α→ℝ)-f) 2 ν≤_
    rw [eLpNorm_sub_comm]
    exact hg j
  obtain ⟨ns,hns,hAE⟩:=(tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞)≠0) hlim).exists_seq_tendsto_ae
  let clamp : ℝ→ℝ:=fun y=>(projIcc (-K) K (by linarith) y : ℝ)
  have hc : Continuous clamp:=continuous_subtype_val.comp continuous_projIcc
  refine ⟨fun j x=>clamp (g (ns j) x),fun j=>hc.comp (g (ns j)).continuous,?_,?_⟩
  · intro j x
    exact abs_le.mpr (projIcc (-K) K (by linarith) (g (ns j) x)).property
  · filter_upwards [hAE] with x hx
    have h:=hc.tendsto (f x) |>.comp hx
    have hfclamp : clamp (f x)=f x := by
      dsimp only [clamp]
      rw [projIcc_of_mem (by linarith) (abs_le.mp (hB x))]
    rwa [hfclamp] at h

end FourPapersCommon
