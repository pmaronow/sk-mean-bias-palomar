module
public import QuantitativePaper.VectorBinaryCrossResponse

@[expose] public section

/-! Actual sharp offset-response domination. The binary spin covariance
bound is preserved by the positive mass-increment decomposition. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2600000

theorem vectorObservableCrossResponse_binary_defect_bound {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ)
    (hb : ∀σ,b σ=1 ∨ b σ= -1) (hd : ∀σ,|d σ|≤1) (j : ℕ) (x : Field n) :
    |vectorObservableCrossResponse s β t p b d j 0 x-observableDepthMass s j*
      vectorConditionalCrossCovariance s β t p (fun _=>0) b d j 0 x|≤
    vectorObservableCrossResponse s β t p b b j 0 x-observableDepthMass s j*
      vectorConditionalCrossCovariance s β t p (fun _=>0) b b j 0 x := by
  have hb1 (σ:Configuration n) : |b σ|≤1:=by
    rcases hb σ with h|h <;> rw [h] <;> norm_num
  induction j generalizing x with
  | zero =>
    simp only [vectorObservableCrossResponse,observableDepthMass,ite_true,one_mul,
      vectorConditionalCrossCovariance,vectorConditionalMean,terminalTilt_zero]
    simp only [terminalCovariance,sub_self,abs_zero,le_refl]
  | succ j ih =>
    let a:=observableDepthMass s j
    let m:=s.m (k+1-j)
    let c:=(1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    let f:=vectorRecursion s β t p j
    let H:=vectorObservableCrossResponse s β t p b d j 0
    let J:=vectorObservableCrossResponse s β t p b b j 0
    let C:=vectorConditionalCrossCovariance s β t p (fun _=>0) b d j 0
    let D:=vectorConditionalCrossCovariance s β t p (fun _=>0) b b j 0
    have hf:=vectorRecursion_lipschitz s β t p j
    have hm0:0≤ m:=s.m_nonneg (Nat.sub_le _ _)
    have hm1:m≤1:=s.m_le_one (Nat.sub_le _ _)
    have hma:m≤a:=observableDepthMass_step_le s j
    have hH : Measurable H:=(measurable_vectorObservableCrossResponse s β t p b d j).comp
      (measurable_const.prodMk measurable_id)
    have hJ : Measurable J:=(measurable_vectorObservableCrossResponse s β t p b b j).comp
      (measurable_const.prodMk measurable_id)
    have hC : Measurable C:=(measurable_vectorConditionalCrossCovariance s β t p (fun _=>0) b d j).comp
      (measurable_const.prodMk measurable_id)
    have hD : Measurable D:=(measurable_vectorConditionalCrossCovariance s β t p (fun _=>0) b b j).comp
      (measurable_const.prodMk measurable_id)
    have hHb (z:Field n) : |H z|≤observableCrossBound 1 1 j:=
      abs_vectorObservableCrossResponse_le s β t p b d 1 1 hb1 hd j 0 z
    have hJb (z:Field n) : |J z|≤observableCrossBound 1 1 j:=
      abs_vectorObservableCrossResponse_le s β t p b b 1 1 hb1 hb1 j 0 z
    have hCb (z:Field n) : |C z|≤1:=
      abs_vectorConditionalCrossCovariance_binary_le_one s β t p (fun _=>0) b d hb hd j 0 z
    have hDb (z:Field n) : |D z|≤1:=
      abs_vectorConditionalCrossCovariance_binary_le_one s β t p (fun _=>0) b b hb hb1 j 0 z
    have hU : Measurable (fun z=>H z-m*C z):=hH.sub (measurable_const.mul hC)
    have hV : Measurable (fun z=>J z-m*D z):=hJ.sub (measurable_const.mul hD)
    have hUb (z:Field n) : |H z-m*C z|≤(observableCrossBound 1 1 j:ℝ)+1:=by
      have hc : |m*C z|≤1:=by
        rw [abs_mul,abs_of_nonneg hm0]
        exact (mul_le_mul hm1 (hCb z) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
      have hh : |H z-m*C z|≤|H z|+|m*C z|:=by
        simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (H z) 0 (m*C z))
      exact hh.trans (add_le_add (hHb z) hc)
    have hVb (z:Field n) : |J z-m*D z|≤(observableCrossBound 1 1 j:ℝ)+1:=by
      have hc : |m*D z|≤1:=by
        rw [abs_mul,abs_of_nonneg hm0]
        exact (mul_le_mul hm1 (hDb z) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
      have hh : |J z-m*D z|≤|J z|+|m*D z|:=by
        simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (J z) 0 (m*D z))
      exact hh.trans (add_le_add (hJb z) hc)
    have hpoint (z:Field n) : |H z-m*C z|≤J z-m*D z:=by
      have hi:=abs_le.mp (ih z)
      have hc:=abs_le.mp (vectorConditionalCrossCovariance_binary_bound s β t p (fun _=>0) b d hb hd j 0 z)
      change -(J z-a*D z)≤H z-a*C z ∧ H z-a*C z≤J z-a*D z at hi
      change -D z≤C z ∧ C z≤D z at hc
      have hl:=mul_le_mul_of_nonneg_left hc.1 (sub_nonneg.mpr hma)
      have hu:=mul_le_mul_of_nonneg_left hc.2 (sub_nonneg.mpr hma)
      apply abs_le.mpr
      constructor <;> nlinarith
    have hupper:=vectorStepResponse_mono f (fun z=>H z-m*C z) (fun z=>J z-m*D z) _ hf
      hU hV _ _ hUb hVb (fun z=>(abs_le.mp (hpoint z)).2) c m x
    have hlower:=vectorStepResponse_mono f (fun z=>(-1:ℝ)*(H z-m*C z)) (fun z=>J z-m*D z) _ hf
      (measurable_const.mul hU) hV _ _
      (fun z=>by simpa only [neg_one_mul,abs_neg] using hUb z) hVb
      (fun z=>by have hh:=(abs_le.mp (hpoint z)).1;linarith) c m x
    rw [vectorStepResponse_mul_const] at hlower
    rw [observableDepthMass_succ,
      vectorObservableCrossResponse_defect_step s β t p b d hb1 hd j x,
      vectorObservableCrossResponse_defect_step s β t p b b hb1 hb1 j x]
    exact abs_le.mpr ⟨by linarith, hupper⟩

theorem abs_vectorObservableCrossResponse_binary_le_self {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ)
    (hb : ∀σ,b σ=1 ∨ b σ= -1) (hd : ∀σ,|d σ|≤1) (j : ℕ) (x : Field n) :
    |vectorObservableCrossResponse s β t p b d j 0 x|≤
      vectorObservableSecondResponse s β t p b j 0 x := by
  have ha:=observableDepthMass_nonneg s j
  have hi:=abs_le.mp (vectorObservableCrossResponse_binary_defect_bound s β t p b d hb hd j x)
  have hc:=abs_le.mp (vectorConditionalCrossCovariance_binary_bound s β t p (fun _=>0) b d hb hd j 0 x)
  have hl:=mul_le_mul_of_nonneg_left hc.1 ha
  have hu:=mul_le_mul_of_nonneg_left hc.2 ha
  rw [←vectorObservableCrossResponse_self]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Literal sharp derivative of a binary spin mean in any bounded spin-offset
direction. The derivative is obtained from the actual normalized recursion. -/
theorem binary_spin_offset_derivative_bound {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ)
    (hb : ∀σ,b σ=1 ∨ b σ= -1) (hd : ∀σ,|d σ|≤1) (j : ℕ) (x : Field n) :
    HasDerivAt (fun y=>vectorConditionalMean s β t p d b j y x)
      (vectorObservableCrossResponse s β t p d b j 0 x) 0 ∧
    |vectorObservableCrossResponse s β t p d b j 0 x|≤
      vectorObservableSecondResponse s β t p b j 0 x := by
  have hb1 (σ:Configuration n) : |b σ|≤1:=by rcases hb σ with h|h <;> rw [h] <;> norm_num
  refine ⟨hasDerivAt_vectorConditionalMean_offset s β t p d b 1 1 hd hb1 j 0 x,?_⟩
  rw [vectorObservableCrossResponse_zero_symm]
  exact abs_vectorObservableCrossResponse_binary_le_self s β t p b d hb hd j x

end QuantitativePaper
