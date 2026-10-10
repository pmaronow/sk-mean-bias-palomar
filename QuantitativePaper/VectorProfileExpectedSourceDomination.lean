module
public import QuantitativePaper.VectorProfileSourceIntegrable
public import QuantitativePaper.VectorProfileExpectedSource
public import QuantitativePaper.VectorProfileSourceDomination
public import QuantitativePaper.VectorProfileRetainedIntegrable
public import QuantitativePaper.VectorProfileClosedTraceSquare

@[expose] public section

/-! The literal expected signed pairing source is dominated by genuine
closed-cell integrable positive energies and the actual Hessian trace. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology MatrixOrder
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfile_expected_curvature_source_abs_bound (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) :
    let E:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    |E (vectorProfileFieldCurvaturePairingSource (n:=n) s₀ s₁ β t i) q|≤
      |(1-t)*(β*(s₁.m i-s₀.m i))| *
        vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
          (fun q z=>‖vectorProfileRetainedTraceSquare (n:=n) s₀ s₁ β t i q z‖) q+
      E (vectorProfileFieldSecondVariationSource s₀ s₁ β t i) q/(2*(1-t))+
      E (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q := by
  let hθ01 : θ∈Icc (0:ℝ) 1:=⟨hθ.1.le,hθ.2.le⟩
  let s:=vectorProfileScheme s₀ s₁ θ hθ01
  let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  let X:=vectorFiniteState (n:=n) s β t ht.le
  let S : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i ((q,θ,sample.1),X q sample)
  let Z : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    vectorProfileFieldSecondVariationSource s₀ s₁ β t i ((q,θ,sample.1),X q sample)
  let N : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    vectorProfileFieldTraceTimeSource s₀ s₁ β t i ((q,θ,sample.1),X q sample)
  let T : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    ‖vectorProfileRetainedTraceSquare (n:=n) s₀ s₁ β t i q ((θ,sample.1),X q sample)‖
  let v:=(1-t)*(β*(s₁.m i-s₀.m i))
  have hS : Integrable S P:=integrable_vectorProfile_curvature_pairing_source hn
    s₀ s₁ β t outer θ hβ.ne' ht i hi hθ q hq
  have hZ : Integrable Z P:=integrable_vectorProfile_second_variation_source hn
    s₀ s₁ β t outer θ hβ ht i hi hθ q hq
  have hN : Integrable N P:=integrable_vectorProfile_trace_time_source hn
    s₀ s₁ β t outer θ hβ ht i hi hθ q hq
  have hT : Integrable T P:=by
    exact (integrable_vectorProfile_retained_observable s₀ s₁ β t outer θ ht.le hθ01 i hi
      (θ/2) ((θ+1)/2) ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
      (vectorProfileRetainedTraceSquare (n:=n) s₀ s₁ β t i)
      (retainedExponentialContinuousOn_vectorProfileRetainedTraceSquare (n:=n) s₀ s₁ β t ht.le i hi
        _ _ (by linarith [hθ.1]) (by linarith [hθ.2])) q ⟨hq.1.le,hq.2.le⟩).norm
  have hB : Integrable (fun sample=>|v| *T sample+Z sample/(2*(1-t))+N sample) P:=
    ((hT.const_mul |v|).add (hZ.div_const (2*(1-t)))).add hN
  have he := integral_mono_ae hS.norm hB (.of_forall fun sample=>by
    have hh:=vectorProfileFieldCurvaturePairingSource_abs_bound s₀ s₁ β t hβ ht i hi
      (q,θ,sample.1) hq hθ (X q sample)
    have htr:=vectorProfileRetainedTraceSquare_eq_physical s₀ s₁ β t hβ.ne' i hi
      q ⟨hq.1.le,hq.2.le⟩ ((θ,sample.1),X q sample) hθ01
    dsimp only at htr hh
    rw [←htr,abs_mul,←Real.norm_eq_abs] at hh
    exact hh)
  have hnI:=norm_integral_le_integral_norm S (μ:=P)
  have he1:=integral_add ((hT.const_mul |v|).add (hZ.div_const (2*(1-t)))) hN
  have he2:=integral_add (hT.const_mul |v|) (hZ.div_const (2*(1-t)))
  simp only [Pi.add_apply] at he1 he2
  rw [he1,he2,integral_const_mul,integral_div] at he
  change |∫sample,S sample∂P|≤_
  rw [←Real.norm_eq_abs]
  apply hnI.trans
  have hRet : vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le hθ01
      (fun q z=>‖vectorProfileRetainedTraceSquare (n:=n) s₀ s₁ β t i q z‖) q=
        ∫sample,T sample∂P:=by
    unfold vectorProfileRetainedExpectation
    simp only [Real.toNNReal_coe]
    rfl
  rw [hRet]
  exact he

end QuantitativePaper
