module
public import QuantitativePaper.VectorCrossObservableResponse
public import QuantitativePaper.VectorHessianComparison

@[expose] public section

/-! The sharp response estimate for a binary spin, from the genuine finite
Cole--Hopf recursion. Positive mass increments preserve the terminal
covariance domination. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2400000

theorem vectorObservableCrossResponse_zero_symm {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (j : ℕ) (x : Field n) :
    vectorObservableCrossResponse s β t p b d j 0 x=
      vectorObservableCrossResponse s β t p d b j 0 x := by
  induction j generalizing x with
  | zero => simpa only [vectorObservableCrossResponse,terminalTilt_zero] using terminalCovariance_symm _ b d
  | succ j ih =>
    simp only [vectorObservableCrossResponse,vectorPerturbedRecursion_zero,vectorStepCrossResponse]
    rw [show vectorObservableCrossResponse s β t p b d j 0=
      vectorObservableCrossResponse s β t p d b j 0 from funext ih]
    have hb : vectorObservableResponse s β t p b j 0=
      vectorConditionalMean s β t p d b j 0:=by
      funext z
      rw [←vectorConditionalMean_self]
      exact vectorConditionalMean_zero_independent s β t p b d b j z
    have hd : vectorObservableResponse s β t p d j 0=
      vectorConditionalMean s β t p b d j 0:=by
      funext z
      rw [←vectorConditionalMean_self]
      exact vectorConditionalMean_zero_independent s β t p d b d j z
    rw [hb,hd]
    have hprod : (fun z=>vectorConditionalMean s β t p d b j 0 z*
        vectorConditionalMean s β t p b d j 0 z)=fun z=>vectorConditionalMean s β t p b d j 0 z*
        vectorConditionalMean s β t p d b j 0 z:=by funext z;ring
    rw [hprod]
    ring

theorem vectorConditionalCrossCovariance_zero_self {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) (x : Field n) :
    vectorConditionalCrossCovariance s β t p (fun _=>0) b b j 0 x=
      vectorObservableCovariance s β t p b j 0 x := by
  unfold vectorConditionalCrossCovariance vectorObservableCovariance
  rw [vectorConditionalMean_zero_independent s β t p (fun _=>0) b (fun σ=>b σ*b σ) j x,
    vectorConditionalMean_zero_independent s β t p (fun _=>0) b b j x,vectorConditionalMean_self]
  congr 1
  · congr 1
    funext σ
    ring
  · ring

/-- Exact cancellation of the current mass times the terminal covariance.
The remaining term propagates by the genuine positive Gaussian operator. -/
theorem vectorObservableCrossResponse_defect_step {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ)
    (hb : ∀σ,|b σ|≤1) (hd : ∀σ,|d σ|≤1) (j : ℕ) (x : Field n) :
    vectorObservableCrossResponse s β t p b d (j+1) 0 x-
      s.m (k+1-j)*vectorConditionalCrossCovariance s β t p (fun _=>0) b d (j+1) 0 x=
    vectorStepResponse ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
      (vectorRecursion s β t p j) (fun z=>vectorObservableCrossResponse s β t p b d j 0 z-
        s.m (k+1-j)*vectorConditionalCrossCovariance s β t p (fun _=>0) b d j 0 z) x := by
  let f:=vectorRecursion s β t p j
  let B:=vectorConditionalMean s β t p (fun _=>0) b j 0
  let D:=vectorConditionalMean s β t p (fun _=>0) d j 0
  let W:=vectorConditionalMean s β t p (fun _=>0) (fun σ=>b σ*d σ) j 0
  let H:=vectorObservableCrossResponse s β t p b d j 0
  let C:=vectorConditionalCrossCovariance s β t p (fun _=>0) b d j 0
  let c:=(1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
  let m:=s.m (k+1-j)
  have hf:=vectorRecursion_lipschitz s β t p j
  have hB : Measurable B:=(measurable_vectorConditionalMean s β t p (fun _=>0) b j).comp
    (measurable_const.prodMk measurable_id)
  have hD : Measurable D:=(measurable_vectorConditionalMean s β t p (fun _=>0) d j).comp
    (measurable_const.prodMk measurable_id)
  have hW : Measurable W:=(measurable_vectorConditionalMean s β t p (fun _=>0) _ j).comp
    (measurable_const.prodMk measurable_id)
  have hH : Measurable H:=(measurable_vectorObservableCrossResponse s β t p b d j).comp
    (measurable_const.prodMk measurable_id)
  have hC : Measurable C:=(measurable_vectorConditionalCrossCovariance s β t p (fun _=>0) b d j).comp
    (measurable_const.prodMk measurable_id)
  have hBb (z:Field n) : |B z|≤1:=abs_vectorConditionalMean_le s β t p (fun _=>0) b 1 hb j 0 z
  have hDb (z:Field n) : |D z|≤1:=abs_vectorConditionalMean_le s β t p (fun _=>0) d 1 hd j 0 z
  have hbd (σ:Configuration n) : |b σ*d σ|≤1:=by
    rw [abs_mul]
    exact (mul_le_mul (hb σ) (hd σ) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hWb (z:Field n) : |W z|≤1:=abs_vectorConditionalMean_le s β t p (fun _=>0) _ 1 hbd j 0 z
  have hBDb (z:Field n) : |B z*D z|≤1:=by
    rw [abs_mul]
    exact (mul_le_mul (hBb z) (hDb z) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hCb (z:Field n) : |C z|≤2:=by
    change |W z-B z*D z|≤2
    have hh : |W z-B z*D z|≤|W z|+|B z*D z|:=by
      simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (W z) 0 (B z*D z))
    exact hh.trans (by linarith [hWb z,hBDb z])
  have hHb (z:Field n) : |H z|≤observableCrossBound 1 1 j:=
    abs_vectorObservableCrossResponse_le s β t p b d 1 1 hb hd j 0 z
  have hmean : vectorStepResponse c m f C x=vectorStepResponse c m f W x-
      vectorStepResponse c m f (fun z=>B z*D z) x:=
    vectorStepResponse_sub f W (fun z=>B z*D z) _ hf hW (hB.mul hD) 1 1 hWb hBDb c m x
  have hstep : vectorStepResponse c m f (fun z=>H z-m*C z) x=
      vectorStepResponse c m f H x-m*vectorStepResponse c m f C x:=by
    rw [vectorStepResponse_sub f H (fun z=>m*C z) _ hf hH (measurable_const.mul hC)
      (observableCrossBound 1 1 j) (|m| *2) hHb (fun z=>by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hCb z) (abs_nonneg m)) c m x,
      vectorStepResponse_mul_const]
  have hB0 : vectorObservableResponse s β t p b j 0=B:=by
    funext z
    rw [←vectorConditionalMean_self]
    exact vectorConditionalMean_zero_independent s β t p b (fun _=>0) b j z
  have hD0 : vectorConditionalMean s β t p b d j 0=D:=by
    funext z
    exact vectorConditionalMean_zero_independent s β t p b (fun _=>0) d j z
  change vectorObservableCrossResponse s β t p b d (j+1) 0 x-m*
    vectorConditionalCrossCovariance s β t p (fun _=>0) b d (j+1) 0 x=
    vectorStepResponse c m f (fun z=>H z-m*C z) x
  rw [hstep,hmean]
  simp only [vectorObservableCrossResponse,vectorStepCrossResponse,vectorPerturbedRecursion_zero,
    vectorConditionalCrossCovariance,vectorConditionalMean,hB0,hD0]
  change vectorStepResponse c m f H x+m*(vectorStepResponse c m f (fun z=>B z*D z) x-
    vectorStepResponse c m f B x*vectorStepResponse c m f D x)-
    m*(vectorStepResponse c m f W x-vectorStepResponse c m f B x*vectorStepResponse c m f D x)=_
  ring

end QuantitativePaper
