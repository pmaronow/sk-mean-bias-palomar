module
public import QuantitativePaper.VectorFiniteHessianStrict

@[expose] public section

/-! Strict spin-cube bounds for the actual finite Gaussian response. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem vectorStepResponse_abs_lt_one {n : ℕ} (f v : Field n→ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (hB : ∀x,|v x| ≤ 1)
    (hstrict : ∀x,|v x| < 1) (c m : ℝ) (x : Field n) :
    |vectorStepResponse c m f v x| < 1 := by
  have hU:=vectorStepResponse_pos f (fun z=>1-v z) K hf (measurable_const.sub hv) 2
    (fun z=>(abs_sub _ _).trans (by norm_num only [abs_one];linarith [hB z]))
    (fun z=>sub_pos.mpr (abs_lt.mp (hstrict z)).2) c m x
  rw [vectorStepResponse_sub f (fun _=>1) v K hf measurable_const hv 1 1
    (fun _=>by norm_num) hB,vectorStepResponse_const f K hf c m 1 x] at hU
  have hL:=vectorStepResponse_pos f (fun z=>1+v z) K hf (measurable_const.add hv) 2
    (fun z=>(abs_add_le _ _).trans (by norm_num only [abs_one];linarith [hB z]))
    (fun z=>by linarith [(abs_lt.mp (hstrict z)).1]) c m x
  rw [vectorStepResponse_add f (fun _=>1) v K hf measurable_const hv 1 1
    (fun _=>by norm_num) hB,vectorStepResponse_const f K hf c m 1 x] at hL
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem vectorMagnetization_component_abs_lt_one {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    |vectorMagnetization s β t p j x i| < 1 := by
  change |vectorObservableResponse s β t p (fun σ=>Paper.spinSign (σ i)) j 0 x| < 1
  induction j generalizing x with
  | zero => exact terminalMean_spin_abs_lt_one _ i
  | succ j ih =>
    apply vectorStepResponse_abs_lt_one _ _ _
      (vectorPerturbedRecursion_lipschitz s β t p _ j 0)
      ((measurable_vectorObservableResponse s β t p _ j).comp (measurable_const.prodMk measurable_id))
      (fun z=>abs_vectorObservableResponse_le s β t p _ 1 (fun σ=>by simp) j 0 z) ih

end QuantitativePaper
