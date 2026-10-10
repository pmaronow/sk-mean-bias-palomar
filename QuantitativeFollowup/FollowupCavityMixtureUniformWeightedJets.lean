module
public import QuantitativeFollowup.FollowupCavityMixtureUniformMeanJets
public import QuantitativeFollowup.FollowupCavityMixtureFieldObservableJets
public import QuantitativeFollowup.FollowupCavityMixtureOuterContinuity

@[expose] public section

/-! Common relative and exponential bounds for the true outer Gaussian
numerators. Input maps may vary, while normalization remains literal. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff Topology BigOperators
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityOuterPosteriorNormalizer_uniform_relative_jets (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a) (s : ℝ) (N r : ℕ) :
    ∃C:ℕ→ℝ,(∀i,0≤C i) ∧ ∀(L : ℕ→Field n→L[ℝ]FiniteStateField S)
      (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) i,i≤r → ∀H,
      ‖iteratedFDeriv ℝ i (cavityOuterPosteriorNormalizer V a L s N R) H‖≤
        C i*cavityOuterPosteriorNormalizer V a L s N R H :=by
  let K:=finiteJetPowerBound (finiteStateSpatialJetBound S n) r
  have hK:1≤K:=finiteJetPowerBound_ge_one _ _
  refine ⟨gaussianJetCoefficient s K,fun i=>gaussianJetCoefficient_nonneg s K
    (zero_le_one.trans hK) i,?_⟩
  intro L R i hi H
  rw [cavityOuterPosteriorNormalizer_eq_gaussianShiftPartition V a ha L s N R]
  exact norm_iteratedFDeriv_gaussianShiftPartition_le r i _
    ((contDiff_finiteStateGaussianTerminalCascade V a ha L N).of_le (by simp)) 1
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) K (zero_le_one.trans hK)
    (fun j hj hjr Q=>(norm_finiteStateCascade_jet_le_uniform V a ha ha1 hdec L N j hj Q).trans
      (finite_jet_bound_le_power _ r j hj hjr)) (R.comp (cavityOuterGaussianCoordinates J)) s hi H

theorem cavityOuterPosteriorWeightedMean_uniform_relative_jets (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (s : ℝ) (N r : ℕ) (G : ℕ→ℝ) (hG : ∀i,0≤G i) :
    ∃C:ℕ→ℝ,(∀i,0≤C i) ∧ ∀(L : ℕ→Field n→L[ℝ]FiniteStateField S)
      (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
      (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
      (W : (Fin N→Field n)→L[ℝ]FiniteStateField S),
      (∀i H,‖iteratedFDeriv ℝ i f H‖≤G i) → ∀i,i≤r → ∀H,
      ‖iteratedFDeriv ℝ i (cavityOuterPosteriorWeightedMean V a L s N R f W) H‖≤
        C i*cavityOuterPosteriorNormalizer V a L s N R H :=by
  classical
  obtain ⟨Z,hZ,hZb⟩:=cavityOuterPosteriorNormalizer_uniform_relative_jets (n:=n) (J:=J)
    V a ha ha1 hdec s N r
  choose M hM hMb using fun i=>cavityOuterPosteriorMean_uniform_jet_bound (n:=n) (J:=J)
    V a ha ha1 hdec s N i G hG
  refine ⟨cavityProductJetBound Z M,fun i=>cavityProductJetBound_nonneg Z M hZ hM i,?_⟩
  intro L R f hf W hfb i hi H
  have he:cavityOuterPosteriorWeightedMean V a L s N R f W=
    fun Q=>cavityOuterPosteriorNormalizer V a L s N R Q*cavityOuterPosteriorMean V a L s N R f W Q:=
    funext (cavityOuterPosteriorWeightedMean_eq_normalizer_mul V a ha L s N R f hf W)
  rw [he]
  apply (norm_iteratedFDeriv_mul_le
    (contDiff_cavityOuterPosteriorNormalizer V a ha L s N R)
    (contDiff_cavityOuterPosteriorMean V a ha ha1 hdec L s N R f hf W) H (by simp)).trans
  have hh:∀j∈Finset.range (i+1),
    (i.choose j:ℝ)*‖iteratedFDeriv ℝ j (cavityOuterPosteriorNormalizer V a L s N R) H‖*
      ‖iteratedFDeriv ℝ (i-j) (cavityOuterPosteriorMean V a L s N R f W) H‖≤
      ((i.choose j:ℝ)*Z j*M (i-j))*cavityOuterPosteriorNormalizer V a L s N R H:=by
    intro j hj
    have hjr:j≤r:=by have:=Finset.mem_range.mp hj;omega
    have hz:=hZb L R j hjr H
    have hm:=hMb (i-j) L R f hf W (fun t _ Q=>hfb t Q) H
    have hx:=mul_le_mul hz hm (norm_nonneg _) (mul_nonneg (hZ _)
      (finiteCascadeTreeGaussianNormalizer_pos V a ha L s N R H).le)
    have hy:=mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg (i.choose j))
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hy
  exact (Finset.sum_le_sum hh).trans_eq (by simp only [cavityProductJetBound,Finset.sum_mul])

end QuantitativeFollowup
