module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterLogJets
public import FourPapersCommon.FiniteStateCascadeAllJets

@[expose] public section

/-! Common spatial log-density jet bounds for all Gaussian input maps.
The constants do not depend on a varying positive variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityOuterPosteriorLogNormalizer_uniform_positive_jets (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (s : ℝ) (N r : ℕ) :
    ∃K:ℝ,1≤K ∧ ∀(L : ℕ→Field n→L[ℝ]FiniteStateField S)
      (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
      (i : ℕ), 1 ≤ i → i ≤ r → ∀ H,
      ‖iteratedFDeriv ℝ i (fun Q=>Real.log (cavityOuterPosteriorNormalizer V a L s N R Q)) H‖≤K^i :=by
  let U:=finiteStateSpatialJetBound S n
  let K:=finiteJetPowerBound U r
  have hK:1≤K:=finiteJetPowerBound_ge_one U r
  let G:=fun i=>(i.factorial:ℝ)*logJetCoefficient i*(gaussianDerivativePowerBound s K r)^i
  refine ⟨finiteJetPowerBound G r,finiteJetPowerBound_ge_one G r,?_⟩
  intro L R i hi hir H
  rw [cavityOuterPosteriorNormalizer_eq_gaussianShiftPartition V a ha L s N R]
  apply (norm_iteratedFDeriv_log_gaussianShiftPartition_le r i _
    ((contDiff_finiteStateGaussianTerminalCascade V a ha L N).of_le (by simp)) 1
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) K (zero_le_one.trans hK)
    (fun j hj hjr Q=>(norm_finiteStateCascade_jet_le_uniform V a ha ha1 hdec L N j hj Q).trans
      (finite_jet_bound_le_power U r j hj hjr))
    (R.comp (cavityOuterGaussianCoordinates J)) s hi hir H).trans
  exact finite_jet_bound_le_power G r i hi hir

theorem cavityOuterPosteriorLogDensity_uniform_positive_jets (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (s : ℝ) (N r : ℕ) :
    ∃K:ℝ,1≤K ∧ ∀(L : ℕ→Field n→L[ℝ]FiniteStateField S)
      (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
      (i : ℕ),1 ≤ i → i ≤ r → ∀H p,
      ‖iteratedFDeriv ℝ i (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H‖≤K^i :=by
  obtain ⟨D,hD,hDB⟩:=cavityOuterPosteriorLogNormalizer_uniform_positive_jets (n:=n) (J:=J) V a ha ha1 hdec s N r
  let B:=fun i=>|s| *finiteStateSpatialJetBound S n i+1+finiteStateSpatialJetBound S n i+D^i
  refine ⟨finiteJetPowerBound B r,finiteJetPowerBound_ge_one B r,?_⟩
  intro L R i hi hir H p
  have hU:ContDiff ℝ ∞ (fun Q=>finiteStateGaussianTerminalCascade V a L N (Q+R p.1)):=
    (contDiff_finiteStateGaussianTerminalCascade V a ha L N).comp (contDiff_id.add contDiff_const)
  have hP:ContDiff ℝ ∞ (fun Q=>cascadePosteriorLogDensity V a L N (Q+R p.1) p.2):=
    (contDiff_cascadePosteriorLogDensity V a ha L N p.2.2).comp
      ((contDiff_id.add contDiff_const).prodMk contDiff_const)
  have hZ:=contDiff_log_cavityOuterPosteriorNormalizer V a ha L s N R
  change ‖iteratedFDeriv ℝ i (fun Q=>s • finiteStateGaussianTerminalCascade V a L N (Q+R p.1)+
    cascadePosteriorLogDensity V a L N (Q+R p.1) p.2-
    Real.log (cavityOuterPosteriorNormalizer V a L s N R Q)) H‖≤_
  have he : iteratedFDeriv ℝ i (fun Q=>s • finiteStateGaussianTerminalCascade V a L N (Q+R p.1)+
      cascadePosteriorLogDensity V a L N (Q+R p.1) p.2-
      Real.log (cavityOuterPosteriorNormalizer V a L s N R Q)) H=
      iteratedFDeriv ℝ i (fun Q=>s • finiteStateGaussianTerminalCascade V a L N (Q+R p.1)+
        cascadePosteriorLogDensity V a L N (Q+R p.1) p.2) H-
      iteratedFDeriv ℝ i (fun Q=>Real.log (cavityOuterPosteriorNormalizer V a L s N R Q)) H :=by
    simpa only [Pi.sub_def] using iteratedFDeriv_sub_apply (i:=i)
      ((hU.const_smul s |>.add hP).of_le (by simp)).contDiffAt
      (hZ.of_le (by simp)).contDiffAt
  rw [he]
  have hUb:‖iteratedFDeriv ℝ i (fun Q=>finiteStateGaussianTerminalCascade V a L N (Q+R p.1)) H‖≤
      finiteStateSpatialJetBound S n i:=by
    rw [iteratedFDeriv_comp_add_right]
    exact norm_finiteStateCascade_jet_le_uniform V a ha ha1 hdec L N i hi _
  have hPb:‖iteratedFDeriv ℝ i (fun Q=>cascadePosteriorLogDensity V a L N (Q+R p.1) p.2) H‖≤
      1+finiteStateSpatialJetBound S n i:=by
    rw [iteratedFDeriv_comp_add_right (f:=fun Q=>cascadePosteriorLogDensity V a L N Q p.2)]
    apply norm_cascadePosteriorLogDensity_jet_le V a ha ha1 hdec L i 1
      (finiteStateSpatialJetBound S n i) (finiteStateSpatialJetBound_nonneg S n i)
      (fun j Q=>norm_finiteStateCascade_jet_le_uniform V a ha ha1 hdec L j i hi Q)
    intro w Q σ
    by_cases hi1:i=1
    · rw [hi1];exact norm_cascadeTerminal_affine_firstJet_le_one V w Q σ
    · rw [cascadeTerminal_affine_higherJet_zero V w Q σ i (by omega),norm_zero];norm_num
  have hsum : iteratedFDeriv ℝ i (fun Q=>s • finiteStateGaussianTerminalCascade V a L N (Q+R p.1)+
      cascadePosteriorLogDensity V a L N (Q+R p.1) p.2) H=
      s • iteratedFDeriv ℝ i (fun Q=>finiteStateGaussianTerminalCascade V a L N (Q+R p.1)) H+
      iteratedFDeriv ℝ i (fun Q=>cascadePosteriorLogDensity V a L N (Q+R p.1) p.2) H :=by
    have hx:=iteratedFDeriv_add_apply (i:=i) (x:=H)
      ((hU.const_smul s).of_le (by simp)).contDiffAt (hP.of_le (by simp)).contDiffAt
    simpa only [Pi.add_def,iteratedFDeriv_const_smul_apply' (i:=i) (x:=H) (hU.of_le (by simp)).contDiffAt] using hx
  rw [hsum]
  have hn:=norm_sub_le
    (s • iteratedFDeriv ℝ i (fun Q=>finiteStateGaussianTerminalCascade V a L N (Q+R p.1)) H+
      iteratedFDeriv ℝ i (fun Q=>cascadePosteriorLogDensity V a L N (Q+R p.1) p.2) H)
    (iteratedFDeriv ℝ i (fun Q=>Real.log (cavityOuterPosteriorNormalizer V a L s N R Q)) H)
  have hab:‖s • iteratedFDeriv ℝ i (fun Q=>finiteStateGaussianTerminalCascade V a L N (Q+R p.1)) H+
      iteratedFDeriv ℝ i (fun Q=>cascadePosteriorLogDensity V a L N (Q+R p.1) p.2) H‖≤
      |s| *finiteStateSpatialJetBound S n i+(1+finiteStateSpatialJetBound S n i) :=by
    refine (norm_add_le _ _).trans (add_le_add ?_ hPb)
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hUb (abs_nonneg s)
  exact hn.trans ((add_le_add hab (hDB L R i hi hir H)).trans
    (by simpa only [B,add_assoc] using finite_jet_bound_le_power B r i hi hir))

end QuantitativeFollowup
