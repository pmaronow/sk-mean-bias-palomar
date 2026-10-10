module
public import QuantitativePaper.VectorProfileClosedReaction
public import QuantitativePaper.VectorFiniteExpectedContinuityCheckpoint

@[expose] public section

/-! The true fractional finite diffusion expectations of closed retained
observables are continuous, with a genuine integrable Wiener envelope. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileRetainedExpectation (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ)
    (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (F : ℝ→VectorProfileParameter n×Field n→ℝ) (q : ℝ) : ℝ:=
  let S:=vectorProfileScheme s₀ s₁ θ hθ
  ∫sample : VectorDisorderBrownianSample n,
    F q ((θ,sample.1),vectorFiniteState S β t ht q.toNNReal sample)
    ∂vectorFiniteDisorderTilt S β t outer

theorem continuousOn_vectorProfileRetainedExpectation
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Icc (0:ℝ) 1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hθAB : θ∈Ioo A B)
    (F : ℝ→VectorProfileParameter n×Field n→ℝ)
    (hF : RetainedExponentialContinuousOn F (Icc (s₀.q i) (s₀.q (i+1)))
      (vectorProfileRetainedDomain n A B)) :
    ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F)
      (Icc (s₀.q i) (s₀.q (i+1))) := by
  obtain ⟨C,R,hC,hR,hbound⟩:=hF.bound
  let G : ℝ×((Couplings n×ℝ)×Field n)→ℝ:=fun w=>F w.1 ((θ,w.2.1),w.2.2)
  have hG : ContinuousOn G (Icc (s₀.q i) (s₀.q (i+1))×ˢuniv):=by
    apply hF.continuous.comp
      (f:=fun w : ℝ×((Couplings n×ℝ)×Field n)=>(w.1,((θ,w.2.1),w.2.2)))
      (g:=fun w : ℝ×(VectorProfileParameter n×Field n)=>F w.1 w.2)
      (show Continuous (fun w : ℝ×((Couplings n×ℝ)×Field n)=>
        (w.1,((θ,w.2.1),w.2.2))) by fun_prop).continuousOn
    intro w hw
    exact ⟨hw.1,hθAB⟩
  apply continuousOn_vectorFinite_expected_exp_test (vectorProfileScheme s₀ s₁ θ hθ)
    β t outer ht (s₀.q i) (s₀.q (i+1)) (s₀.q_nonneg (by omega))
    (s₀.q_le_one (by omega)) G hG (C*Real.exp R) R (by positivity) hR
  intro q hq p x
  have hn : ‖(((θ,p),x) : VectorProfileParameter n×Field n)‖≤1+‖p‖+‖x‖:=by
    change max (max |θ| ‖p‖) ‖x‖≤1+‖p‖+‖x‖
    have hθ1 : |θ|≤1:=abs_le.mpr ⟨by linarith [hθ.1],hθ.2⟩
    apply max_le
    · apply max_le
      · linarith [norm_nonneg p,norm_nonneg x]
      · linarith [norm_nonneg x]
    · linarith [norm_nonneg p]
  have hb:=hbound q hq ((θ,p),x) hθAB
  change |F q ((θ,p),x)|≤_
  rw [←Real.norm_eq_abs]
  apply hb.trans
  apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hn hR)) hC).trans_eq
  rw [show R*(1+‖p‖+‖x‖)=R+R*(‖p‖+‖x‖) by ring,Real.exp_add]
  ring

theorem continuousOn_vectorProfileRetainedSecondVariation_expectation (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) (i : ℕ) (hi : i≤k+1) :
    ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
      ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileRetainedSecondVariation (n:=n) s₀ s₁ β t i))
      (Icc (s₀.q i) (s₀.q (i+1))) := by
  apply continuousOn_vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
    ⟨hθ.1.le,hθ.2.le⟩ i hi (θ/2) ((θ+1)/2)
    (show θ∈Ioo (θ/2) ((θ+1)/2) from ⟨by linarith [hθ.1],by linarith [hθ.2]⟩)
  exact retainedExponentialContinuousOn_vectorProfileRetainedSecondVariation hn
    s₀ s₁ β t ht i hi _ _ (by linarith [hθ.1]) (by linarith [hθ.2])

theorem continuousOn_vectorProfileRetainedCurvaturePairing_expectation (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) (i : ℕ) (hi : i≤k+1) :
    ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
      ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i))
      (Icc (s₀.q i) (s₀.q (i+1))) := by
  apply continuousOn_vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
    ⟨hθ.1.le,hθ.2.le⟩ i hi (θ/2) ((θ+1)/2)
    (show θ∈Ioo (θ/2) ((θ+1)/2) from ⟨by linarith [hθ.1],by linarith [hθ.2]⟩)
  exact retainedExponentialContinuousOn_vectorProfileRetainedCurvaturePairing hn
    s₀ s₁ β t ht i hi _ _ (by linarith [hθ.1]) (by linarith [hθ.2])

theorem continuousOn_vectorProfileRetainedTraceReaction_expectation (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) (i : ℕ) (hi : i≤k+1) :
    ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
      ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i))
      (Icc (s₀.q i) (s₀.q (i+1))) := by
  apply continuousOn_vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
    ⟨hθ.1.le,hθ.2.le⟩ i hi (θ/2) ((θ+1)/2)
    (show θ∈Ioo (θ/2) ((θ+1)/2) from ⟨by linarith [hθ.1],by linarith [hθ.2]⟩)
  exact retainedExponentialContinuousOn_vectorProfileRetainedTraceReaction hn
    s₀ s₁ β t ht i hi _ _ (by linarith [hθ.1]) (by linarith [hθ.2])

end QuantitativePaper
