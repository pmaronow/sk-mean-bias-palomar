module
public import QuantitativePaper.VectorCrossStepResponse
public import QuantitativePaper.VectorBinaryCovariance

@[expose] public section

/-! The actual derivative of a terminal observable in another terminal-spin
offset direction, throughout the finite Gaussian recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000

def vectorObservableCrossResponse {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) : ℕ → ℝ → Field n → ℝ
  | 0 => fun y x=>terminalCovariance (terminalTilt (vectorTerminalExponent n β t p x) b y) b d
  | j+1 => fun y=>vectorStepCrossResponse ((1-t) * (β^2 * (s.q (k+2-j)-s.q (k+1-j))))
      (s.m (k+1-j)) (vectorPerturbedRecursion s β t p b j y)
      (vectorObservableResponse s β t p b j y) (vectorConditionalMean s β t p b d j y)
      (vectorObservableCrossResponse s β t p b d j y)

def observableCrossBound (R S : ℝ≥0) (j : ℕ) : ℝ≥0:=2 * (j+1) * R * S

theorem abs_terminalCovariance_le {n : ℕ} (E b d : Configuration n → ℝ) (R S : ℝ≥0)
    (hb : ∀σ,|b σ| ≤ R) (hd : ∀σ,|d σ| ≤ S) :
    |terminalCovariance E b d| ≤ 2 * (R:ℝ) * S := by
  have hbd (σ:Configuration n) : |b σ * d σ| ≤ (R:ℝ) * S:=by
    rw [abs_mul]
    exact mul_le_mul (hb σ) (hd σ) (abs_nonneg _) R.coe_nonneg
  have h1:=terminalMean_bound E _ ((R:ℝ) * S) hbd
  have h2:=terminalMean_bound E b R hb
  have h3:=terminalMean_bound E d S hd
  have hm : |terminalMean E b * terminalMean E d| ≤ (R:ℝ) * S:=by
    rw [abs_mul]
    exact mul_le_mul h2 h3 (abs_nonneg _) R.coe_nonneg
  unfold terminalCovariance
  have hab : |terminalMean E (fun σ=>b σ * d σ)-terminalMean E b * terminalMean E d|≤
      |terminalMean E (fun σ=>b σ * d σ)|+|terminalMean E b * terminalMean E d|:=by
    simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (terminalMean E (fun σ=>b σ * d σ)) 0 (terminalMean E b * terminalMean E d))
  exact hab.trans (by linarith)

theorem measurable_vectorObservableCrossResponse {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (j : ℕ) :
    Measurable (fun w:ℝ×Field n=>vectorObservableCrossResponse s β t p b d j w.1 w.2) := by
  induction j with
  | zero =>
    unfold vectorObservableCrossResponse terminalCovariance terminalMean terminalWeight terminalPartition
      terminalTilt vectorTerminalExponent fieldDot
    fun_prop
  | succ j ih =>
    let f:=vectorPerturbedRecursion s β t p b j
    let v:=vectorObservableResponse s β t p b j
    let w:=vectorConditionalMean s β t p b d j
    let h:=vectorObservableCrossResponse s β t p b d j
    have hf:=measurable_vectorPerturbedRecursion s β t p b j
    have hv:=measurable_vectorObservableResponse s β t p b j
    have hw:=measurable_vectorConditionalMean s β t p b d j
    have h1:=measurable_vectorStepResponse_parameter f h hf ih
      ((1-t) * (β^2 * (s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
    have h2:=measurable_vectorStepResponse_parameter f (fun y x=>v y x * w y x) hf (hv.mul hw)
      ((1-t) * (β^2 * (s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
    have h3:=measurable_vectorStepResponse_parameter f v hf hv
      ((1-t) * (β^2 * (s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
    have h4:=measurable_vectorStepResponse_parameter f w hf hw
      ((1-t) * (β^2 * (s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
    exact h1.add (measurable_const.mul (h2.sub (h3.mul h4)))

theorem abs_vectorObservableCrossResponse_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (R S : ℝ≥0)
    (hb : ∀σ,|b σ| ≤ R) (hd : ∀σ,|d σ| ≤ S)
    (j : ℕ) (y : ℝ) (x : Field n) :
    |vectorObservableCrossResponse s β t p b d j y x| ≤ observableCrossBound R S j := by
  induction j generalizing x with
  | zero => simpa [vectorObservableCrossResponse,observableCrossBound] using abs_terminalCovariance_le _ b d R S hb hd
  | succ j ih =>
    have h:=abs_vectorStepCrossResponse_le _ _ _ _ _ (vectorPerturbedRecursion_lipschitz s β t p b j y)
      R S (observableCrossBound R S j)
      (fun z=>abs_vectorObservableResponse_le s β t p b R hb j y z)
      (fun z=>abs_vectorConditionalMean_le s β t p b d S hd j y z) ih
      ((1-t) * (β^2 * (s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j)) x
    have hm0:=s.m_nonneg (Nat.sub_le (k+1) j)
    have hm1:=s.m_le_one (Nat.sub_le (k+1) j)
    rw [abs_of_nonneg hm0] at h
    apply h.trans
    have hh:=mul_le_mul_of_nonneg_right hm1 (show 0 ≤ (R:ℝ) * S by positivity)
    simp only [observableCrossBound,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast,
      NNReal.coe_one,NNReal.coe_ofNat,Nat.cast_add] at  * 
    push_cast
    nlinarith

theorem hasDerivAt_vectorConditionalMean_offset {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (R S : ℝ≥0)
    (hb : ∀σ,|b σ| ≤ R) (hd : ∀σ,|d σ| ≤ S)
    (j : ℕ) (y : ℝ) (x : Field n) :
    HasDerivAt (fun r=>vectorConditionalMean s β t p b d j r x)
      (vectorObservableCrossResponse s β t p b d j y x) y := by
  induction j generalizing y x with
  | zero => exact hasDerivAt_terminalMean_tilt _ b d y
  | succ j ih =>
    exact hasDerivAt_vectorStepResponse_cross _ _ _ _ (Real.sqrt (n:ℝ)).toNNReal R S
      (observableCrossBound R S j) (vectorPerturbedRecursion_lipschitz s β t p b j)
      (fun y=>(measurable_vectorObservableResponse s β t p b j).comp (measurable_const.prodMk measurable_id))
      (fun y=>(measurable_vectorConditionalMean s β t p b d j).comp (measurable_const.prodMk measurable_id))
      (fun y=>(measurable_vectorObservableCrossResponse s β t p b d j).comp (measurable_const.prodMk measurable_id))
      (fun y z=>abs_vectorObservableResponse_le s β t p b R hb j y z)
      (fun y z=>abs_vectorConditionalMean_le s β t p b d S hd j y z)
      (fun y z=>abs_vectorObservableCrossResponse_le s β t p b d R S hb hd j y z)
      (fun y z=>hasDerivAt_vectorPerturbedRecursion s β t p b R hb j y z)
      (fun y z=>ih y z) _ _ x y

theorem vectorConditionalMean_zero_independent {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (e b d : Configuration n → ℝ) (j : ℕ) (x : Field n) :
    vectorConditionalMean s β t p e d j 0 x=vectorConditionalMean s β t p b d j 0 x := by
  induction j generalizing x with
  | zero => simp [vectorConditionalMean]
  | succ j ih =>
    simp only [vectorConditionalMean,vectorPerturbedRecursion_zero]
    congr 1
    exact funext ih

theorem vectorObservableCrossResponse_self {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) (y : ℝ) (x : Field n) :
    vectorObservableCrossResponse s β t p b b j y x=vectorObservableSecondResponse s β t p b j y x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    simp only [vectorObservableCrossResponse,vectorObservableSecondResponse,vectorConditionalMean_self,
      vectorStepCrossResponse,vectorStepSecondResponse]
    rw [show vectorObservableCrossResponse s β t p b b j y=vectorObservableSecondResponse s β t p b j y from funext ih]
    simp only [←pow_two]

end QuantitativePaper
