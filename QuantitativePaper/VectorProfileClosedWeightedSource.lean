module
public import QuantitativePaper.VectorProfileClosedSignedSource
public import FourPapersCommon.ClosedSignedSourceFTC

@[expose] public section

/-! Actual time-tested source identities extend across closed cells.
The test coefficients multiply true integrable expected sources, and
all cropped stochastic identities are the already checked literal ones. -/
noncomputable section
open MeasureTheory Set Filter StochasticCalculus
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfile_closed_tested_source_interval
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (i : ℕ) (hi : i≤k+1)
    (R : ℝ→VectorProfileParameter n×Field n→ℝ)
    (F H : VectorProfileCellParameter n×Field n→ℝ)
    (hR : ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ R)
      (Icc (s₀.q i) (s₀.q (i+1))))
    (hRi : ∀q : ℝ≥0,(q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))→
      Integrable (fun sample : VectorDisorderBrownianSample n=>
        R q ((θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ hθ) β t ht q sample))
        (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ hθ) β t outer))
    (he : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      R q ((θ,p),x)=F ((q,θ,p),x))
    (hHi : ∀q : ℝ≥0,(q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))→
      Integrable (fun sample : VectorDisorderBrownianSample n=>
        H ((q,θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ hθ) β t ht q sample))
        (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ hθ) β t outer))
    (hH : IntegrableOn (fun q : ℝ=>
      vectorProfileCellExpectation s₀ s₁ β t outer θ ht hθ H q.toNNReal)
      (Ioc (s₀.q i) (s₀.q (i+1))) volume)
    (w w₁ : ℝ→ℝ) (hw : ContinuousOn w (Icc (s₀.q i) (s₀.q (i+1))))
    (hw₁ : ContinuousOn w₁ (Icc (s₀.q i) (s₀.q (i+1))))
    (hc : ∀a b : ℝ≥0,a≤b→s₀.q i<(a:ℝ)→(b:ℝ)<s₀.q (i+1)→
      VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht hθ
        (fun z=>w z.1.1*F z) (fun z=>w₁ z.1.1*F z+w z.1.1*H z) a b) :
    let ER:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ R
    let EH:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht hθ H
    w (s₀.q (i+1))*ER (s₀.q (i+1))-w (s₀.q i)*ER (s₀.q i)=
      ∫q in (s₀.q i)..(s₀.q (i+1)),w₁ q*ER q+w q*EH q.toNNReal := by
  let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
  let ER:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht hθ R
  have hg : IntegrableOn (fun q : ℝ=>w₁ q*ER q+w q*E H q.toNNReal)
      (Ioc (s₀.q i) (s₀.q (i+1))) volume:=by
    exact ((hw₁.mul hR).integrableOn_Icc.mono_set Ioc_subset_Icc_self).add
      (hH.continuousOn_mul_of_subset hw isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self)
  have hEq (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) :
      E F q=ER q:=by
    exact (vectorProfileRetainedExpectation_eq_cell s₀ s₁ β t outer θ ht hθ R F q (he q hq)).symm
  have hW (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) :
      E (fun z=>w z.1.1*F z) q=w q*ER q:=by
    change (∫sample,w q*F ((q,θ,sample.1),vectorFiniteState _ β t ht q sample)∂vectorFiniteDisorderTilt _ β t outer)=_
    rw [integral_const_mul]
    exact congrArg (fun v : ℝ=>w q*v) (hEq q hq)
  have hS (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) :
      E (fun z=>w₁ z.1.1*F z+w z.1.1*H z) q=w₁ q*ER q+w q*E H q:=by
    have hFi := (hRi q hq).congr (.of_forall fun sample=>he q hq sample.1 _)
    have hHp:=hHi q hq
    have heI:=integral_add (hFi.const_mul (w₁ q)) (hHp.const_mul (w q))
    change (∫sample,w₁ q*F ((q,θ,sample.1),vectorFiniteState _ β t ht q sample)+
      w q*H ((q,θ,sample.1),vectorFiniteState _ β t ht q sample)∂vectorFiniteDisorderTilt _ β t outer)=_
    rw [heI,integral_const_mul,integral_const_mul]
    change w₁ q*E F q+w q*E H q=_
    rw [hEq q hq]
  apply closed_integrable_source_ftc _ _ _ _ (s₀.q_mono i (by omega)) (hw.mul hR) hg
  intro l hl u hu hlu
  have hl0 : 0≤l:=(s₀.q_nonneg (by omega)).trans hl.1.le
  have hu0 : 0≤u:=(s₀.q_nonneg (by omega)).trans hu.1.le
  let a : ℝ≥0:=⟨l,hl0⟩
  let b : ℝ≥0:=⟨u,hu0⟩
  obtain ⟨hcI,hcE⟩:=hc a b hlu hl.1 hu.2
  obtain ⟨_,hconv⟩:=nnreal_source_interval_to_real _ a b hlu hcI
  change w (b:ℝ)*ER (b:ℝ)-w (a:ℝ)*ER (a:ℝ)=
    ∫q in (a:ℝ)..(b:ℝ),w₁ q*ER q+w q*E H q.toNNReal
  rw [←hW b hu,←hW a hl,hcE,hconv]
  have hab : (a:ℝ)≤(b:ℝ):=hlu
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
  have hq0 : 0≤q:=hl0.trans hq.1.le
  have hqi : (q.toNNReal:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1)):=by
    rw [Real.coe_toNNReal _ hq0]
    exact ⟨hl.1.trans hq.1,hq.2.trans_lt hu.2⟩
  simpa only [Real.coe_toNNReal _ hq0] using hS q.toNNReal hqi

end QuantitativePaper
