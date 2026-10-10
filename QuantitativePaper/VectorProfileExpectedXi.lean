module
public import QuantitativePaper.ResponseIntegralCauchySchwarz
public import QuantitativePaper.VectorProfileActualXi
public import QuantitativePaper.VectorProfileRetainedPhysicalTrace
public import QuantitativePaper.VectorProfileActualClosedWeightedSource

@[expose] public section

/-! Actual expected Xi Cauchy–Schwarz. Integrability follows from the
proved scalar generator sources and retained closed-cell observables. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology MatrixOrder
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfile_expected_Xi_cauchy_schwarz (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) (φ δ : ℝ) :
    let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    let R:=vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (δ*R (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i) q+
      φ*E (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) q-
      (1-t)*(β*(s₁.m i-s₀.m i))*φ*
        R (vectorProfileRetainedTraceSquare s₀ s₁ β t i) q)^2≤
      (E (vectorProfileFieldSecondVariationSource s₀ s₁ β t i) q/(1-t))*
      (δ^2*R (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i) q+
        2*(2*δ*φ*R (vectorProfileRetainedTraceReaction s₀ s₁ β t i) q+
          φ^2*E (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q)) := by
  let hθ01 : θ∈Icc (0:ℝ) 1:=⟨hθ.1.le,hθ.2.le⟩
  let s:=vectorProfileScheme s₀ s₁ θ hθ01
  let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  let X:=vectorFiniteState (n:=n) s β t ht.le
  let arg : VectorDisorderBrownianSample n→VectorProfileCellParameter n×Field n:=
    fun ω=>((q,θ,ω.1),X q ω)
  let retained : VectorDisorderBrownianSample n→VectorProfileParameter n×Field n:=
    fun ω=>((θ,ω.1),X q ω)
  let H:=fun ω=>vectorProfileCellHessianMatrix s₀ s₁ β t i (arg ω).1
    (vectorProfileCellJointGradient s₀ s₁ β t i (arg ω))
  let B:=fun ω=>vectorProfileCellBMatrix s₀ s₁ β t i (arg ω).1
    (vectorProfileCellJointGradient s₀ s₁ β t i (arg ω))
  let A:=fun ω=>CFC.sqrt (H ω)*B ω*H ω
  let Xi:=fun ω=>vectorProfileCellFieldXi s₀ s₁ β t i φ δ (arg ω)
  let Z:=fun ω=>vectorProfileFieldSecondVariationSource s₀ s₁ β t i (arg ω)
  let S:=fun ω=>vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i (arg ω)
  let N:=fun ω=>vectorProfileFieldTraceTimeSource s₀ s₁ β t i (arg ω)
  let R:=fun ω=>vectorProfileRetainedCurvaturePairing s₀ s₁ β t i q (retained ω)
  let T:=fun ω=>vectorProfileRetainedTraceSquare s₀ s₁ β t i q (retained ω)
  let V:=fun ω=>vectorProfileRetainedPhysicalTrace s₀ s₁ β t i q (retained ω)
  let J:=fun ω=>vectorProfileRetainedTraceReaction s₀ s₁ β t i q (retained ω)
  let v:=(1-t)*(β*(s₁.m i-s₀.m i))*φ
  have hZ : Integrable Z P:=integrable_vectorProfile_second_variation_source hn s₀ s₁ β t outer θ hβ ht i hi hθ q hq
  have hS : Integrable S P:=integrable_vectorProfile_curvature_pairing_source hn s₀ s₁ β t outer θ hβ.ne' ht i hi hθ q hq
  have hN : Integrable N P:=integrable_vectorProfile_trace_time_source hn s₀ s₁ β t outer θ hβ ht i hi hθ q hq
  have hR : Integrable R P:=integrable_vectorProfile_retained_pairing hn s₀ s₁ β t outer θ ht.le i hi hθ q ⟨hq.1.le,hq.2.le⟩
  have hJ : Integrable J P:=integrable_vectorProfile_retained_reaction hn s₀ s₁ β t outer θ ht.le i hi hθ q ⟨hq.1.le,hq.2.le⟩
  have hV : Integrable V P:=integrable_vectorProfile_retained_physical_trace s₀ s₁ β t outer θ ht.le i hi hθ q ⟨hq.1.le,hq.2.le⟩
  have hT : Integrable T P:=integrable_vectorProfile_retained_observable s₀ s₁ β t outer θ ht.le hθ01 i hi
    (θ/2) ((θ+1)/2) ⟨by linarith [hθ.1],by linarith [hθ.2]⟩ _
    (retainedExponentialContinuousOn_vectorProfileRetainedTraceSquare s₀ s₁ β t ht.le i hi
      _ _ (by linarith [hθ.1]) (by linarith [hθ.2])) q ⟨hq.1.le,hq.2.le⟩
  have eA (ω) : responseMatrixFrobeniusSquare (A ω)=Z ω/(1-t):=by
    unfold Z vectorProfileFieldSecondVariationSource
    change responseMatrixFrobeniusSquare (A ω)=(1-t)*responseMatrixFrobeniusSquare (A ω)/(1-t)
    field_simp [show 1-t≠0 by linarith]
  have ePair (ω) : responseMatrixPair (A ω) (Xi ω)=δ*R ω+φ*S ω-v*T ω:=by
    have hh:=vectorProfileCellFieldXi_curvature_pairing s₀ s₁ β t hβ ht i hi
      (q,θ,ω.1) hq hθ (X q ω) φ δ
    have hR':=vectorProfileRetainedCurvaturePairing_eq_field s₀ s₁ β t hβ.ne' ht i hi
      q hq (retained ω) hθ
    have hT':=vectorProfileRetainedTraceSquare_eq_physical s₀ s₁ β t hβ.ne' i hi
      q ⟨hq.1.le,hq.2.le⟩ (retained ω) hθ01
    dsimp only at hh hR' hT'
    rw [←hR',←hT'] at hh
    exact hh
  have eXi (ω) : responseMatrixFrobeniusSquare (Xi ω)=δ^2*V ω+2*(2*δ*φ*J ω+φ^2*N ω):=by
    have hh:=vectorProfileCellFieldXi_energy s₀ s₁ β t hβ ht i hi (q,θ,ω.1) hq hθ (X q ω) φ δ
    have hV':=vectorProfileRetainedPhysicalTrace_eq_physical s₀ s₁ β t hβ.ne' i hi
      q ⟨hq.1.le,hq.2.le⟩ (retained ω) hθ01
    have hJ':=(vectorProfileRetainedTraceReaction_eq_field s₀ s₁ β t hβ.ne' ht i hi q hq (retained ω) hθ).trans
      (vectorProfileCellFieldTraceTimeExtension_eq_time s₀ s₁ β t hβ.ne' ht i hi (q,θ,ω.1) hq hθ (X q ω)).symm
    dsimp only at hh hV' hJ'
    rw [←hV',←hJ'] at hh
    exact hh
  have hA : Integrable (fun ω=>responseMatrixFrobeniusSquare (A ω)) P:=
    (hZ.div_const (1-t)).congr (.of_forall fun ω=>(eA ω).symm)
  have hPair : Integrable (fun ω=>responseMatrixPair (A ω) (Xi ω)) P:=
    (((hR.const_mul δ).add (hS.const_mul φ)).sub (hT.const_mul v)).congr (.of_forall fun ω=>(ePair ω).symm)
  have hXi : Integrable (fun ω=>responseMatrixFrobeniusSquare (Xi ω)) P:=
    ((hV.const_mul (δ^2)).add (((hJ.const_mul (2*δ*φ)).add (hN.const_mul (φ^2))).const_mul 2)).congr (.of_forall fun ω=>(eXi ω).symm)
  have hh:=response_integral_matrix_pair_cauchy_schwarz P A Xi hA hXi hPair
  simp_rw [eA,ePair,eXi] at hh
  have e₁:=integral_sub ((hR.const_mul δ).add (hS.const_mul φ)) (hT.const_mul v)
  have e₂:=integral_add (hR.const_mul δ) (hS.const_mul φ)
  have e₃:=integral_add (hV.const_mul (δ^2)) (((hJ.const_mul (2*δ*φ)).add (hN.const_mul (φ^2))).const_mul 2)
  have e₄:=integral_add (hJ.const_mul (2*δ*φ)) (hN.const_mul (φ^2))
  simp only [Pi.add_apply,Pi.sub_apply] at e₁ e₂ e₃ e₄
  rw [e₁,e₂,integral_const_mul,integral_const_mul,
    integral_const_mul,integral_div,
    e₃,
    integral_const_mul,integral_const_mul,
    e₄,integral_const_mul,integral_const_mul] at hh
  have eRet (F : ℝ→VectorProfileParameter n×Field n→ℝ) :
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le hθ01 F q=
        ∫ω,F q (retained ω)∂P:=by
    unfold vectorProfileRetainedExpectation
    simp only [Real.toNNReal_coe]
    rfl
  dsimp only
  simp_rw [eRet]
  exact hh

end QuantitativePaper
