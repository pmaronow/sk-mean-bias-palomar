module
public import Paper.ParisiGridScheme
public import Mathlib.Probability.CDF

@[expose] public section

/-! Genuine right continuity of every overlap CDF and the exact CDF at
upward grid nodes, including atoms at zero and one. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 700000

theorem parisiCDF_eq_real_cdf (μ : ParisiMeasure) :
    parisiCDF μ=cdf ((μ : Measure Paper.Overlap).map (fun q : Paper.Overlap=>(q : ℝ))) := by
  letI : IsProbabilityMeasure ((μ : Measure Paper.Overlap).map (fun q : Paper.Overlap=>(q : ℝ))) :=
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance
  funext t
  rw [cdf_eq_real,Measure.real,Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  rfl

theorem parisiCDF_right_continuous (μ : ParisiMeasure) (q : ℝ) :
    ContinuousWithinAt (parisiCDF μ) (Ici q) q := by
  rw [parisiCDF_eq_real_cdf]
  exact (cdf _).right_continuous q

theorem monotone_parisiGridRound (n : ℕ) : Monotone (parisiGridRound n) := by
  intro x y hxy
  change (Nat.ceil ((n+1 : ℕ)*(x : ℝ)) : ℝ)/(n+1 : ℕ)≤
    (Nat.ceil ((n+1 : ℕ)*(y : ℝ)) : ℝ)/(n+1 : ℕ)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hxy' : (x : ℝ)≤y := hxy
  exact_mod_cast Nat.ceil_mono
    (mul_le_mul_of_nonneg_left hxy' (by positivity : (0 : ℝ)≤(n+1 : ℕ)))

theorem parisiGridRound_idempotent (n : ℕ) (q : Paper.Overlap) :
    parisiGridRound n (parisiGridRound n q)=parisiGridRound n q := by
  apply Subtype.ext
  change (Nat.ceil ((n+1 : ℕ)*
    ((Nat.ceil ((n+1 : ℕ)*(q : ℝ)) : ℝ)/(n+1 : ℕ))) : ℝ)/(n+1 : ℕ)=
      (Nat.ceil ((n+1 : ℕ)*(q : ℝ)) : ℝ)/(n+1 : ℕ)
  rw [mul_div_cancel₀ _ (by positivity : (n+1 : ℕ)≠(0 : ℝ))]
  simp

theorem parisiCDF_grid_at_round (μ : ParisiMeasure) (n : ℕ) (q : Paper.Overlap) :
    parisiCDF (parisiGridMeasure μ n) (parisiGridRound n q)=
      parisiCDF μ (parisiGridRound n q) := by
  have hS : MeasurableSet {x : Paper.Overlap | (x : ℝ)≤parisiGridRound n q} :=
    (isClosed_le continuous_subtype_val continuous_const).measurableSet
  unfold parisiCDF parisiGridMeasure
  rw [ProbabilityMeasure.map_apply' μ (measurable_parisiGridRound n).aemeasurable hS]
  congr 1
  congr 1
  ext x
  change (parisiGridRound n x : ℝ)≤parisiGridRound n q ↔ (x : ℝ)≤parisiGridRound n q
  constructor
  · exact fun hx=>(le_parisiGridRound n x).trans hx
  · intro hx
    have h:=(monotone_parisiGridRound n) hx
    rwa [parisiGridRound_idempotent] at h

theorem tendsto_parisiCDF_grid_at_round (μ : ParisiMeasure) (q : Paper.Overlap) :
    Tendsto (fun n=>parisiCDF (parisiGridMeasure μ n) (parisiGridRound n q)) atTop
      (𝓝 (parisiCDF μ q)) := by
  simp_rw [parisiCDF_grid_at_round]
  have hq : Tendsto (fun n=>(parisiGridRound n q : ℝ)) atTop (𝓝[ Ici (q : ℝ)] (q : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨
      (continuous_subtype_val.tendsto q).comp (tendsto_parisiGridRound q),
      .of_forall fun n=>le_parisiGridRound n q⟩
  exact (parisiCDF_right_continuous μ q).tendsto.comp hq

end FourPapersCommon
