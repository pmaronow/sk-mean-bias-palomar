module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterNormalizer
public import FourPapersCommon.FiniteStateCascadeAllJets

@[expose] public section

/-! Smoothness and honest global positive-jet bounds of the complete outer
posterior log density, including its actual partition correction. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityOuterPosteriorLogNormalizer_eq_mass_step (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    (fun H=>Real.log (cavityOuterPosteriorNormalizer V a L s N R H))=
      fun H=>s*gaussianShiftColeHopf (R.comp (cavityOuterGaussianCoordinates J)) s
        (finiteStateGaussianTerminalCascade V a L N) H :=by
  rw [cavityOuterPosteriorNormalizer_eq_gaussianShiftPartition V a ha L s N R]
  funext H
  by_cases hs:s=0
  · simp [hs,gaussianShiftPartition]
  · simp only [gaussianShiftColeHopf,hs,ite_false]
    exact (mul_div_cancel₀ _ hs).symm

theorem cavityOuterPosteriorLogNormalizer_bounded_positive_jets (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    ∃K:ℝ,1≤K ∧ ∀i,1 ≤ i → i ≤ r → ∀H : FiniteStateField S,
      ‖iteratedFDeriv ℝ i (fun Q=>Real.log (cavityOuterPosteriorNormalizer V a L s N R Q)) H‖≤K^i :=by
  obtain ⟨hU,C,hC,hUB⟩:=finiteStateGaussianTerminalCascade_smooth_bounded_jets V a ha L r N
  obtain ⟨hG,D,hD,hDB⟩:=gaussianShiftColeHopf_smooth_bounded_jets r _ hU 1
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) C hC hUB
    (R.comp (cavityOuterGaussianCoordinates J)) s
  let B:=fun i=>|s| *D^i
  refine ⟨finiteJetPowerBound B r,finiteJetPowerBound_ge_one B r,?_⟩
  intro i hi hir H
  rw [cavityOuterPosteriorLogNormalizer_eq_mass_step V a ha L s N R]
  change ‖iteratedFDeriv ℝ i (fun Q=>s • gaussianShiftColeHopf
    (R.comp (cavityOuterGaussianCoordinates J)) s (finiteStateGaussianTerminalCascade V a L N) Q) H‖≤_
  rw [iteratedFDeriv_const_smul_apply' (i:=i) (hG.of_le (by exact_mod_cast hir)).contDiffAt,
    norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hDB i hi hir H) (abs_nonneg s)).trans
    (finite_jet_bound_le_power B r i hi hir)

theorem contDiff_cavityOuterPosteriorLogDensity_joint (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (σ:S) :
    ContDiff ℝ ∞ (fun p : FiniteStateField S×(FiniteStateGaussianInput J×(Fin N→Field n))=>
      cavityOuterPosteriorLogDensity V a L s N R p.1 (p.2.1,(p.2.2,σ))) :=by
  have hQ:ContDiff ℝ ∞ (fun p : FiniteStateField S×(FiniteStateGaussianInput J×(Fin N→Field n))=>
      p.1+R p.2.1):=contDiff_fst.add (R.contDiff.comp (contDiff_fst.comp contDiff_snd))
  exact (contDiff_const.mul ((contDiff_finiteStateGaussianTerminalCascade V a ha L N).comp hQ)).add
    ((contDiff_cascadePosteriorLogDensity V a ha L N σ).comp
      (hQ.prodMk (contDiff_snd.comp contDiff_snd))) |>.sub
        ((contDiff_log_cavityOuterPosteriorNormalizer V a ha L s N R).comp contDiff_fst)

theorem cavityOuterPosteriorLogDensity_bounded_positive_jets (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    ∃K:ℝ,1≤K ∧ ∀i,1 ≤ i → i ≤ r → ∀H p,
      ‖iteratedFDeriv ℝ i (fun Q=>cavityOuterPosteriorLogDensity V a L s N R Q p) H‖≤K^i :=by
  obtain ⟨D,hD,hDB⟩:=cavityOuterPosteriorLogNormalizer_bounded_positive_jets V a ha L s N r R
  let B:=fun i=>|s| *finiteStateSpatialJetBound S n i+1+finiteStateSpatialJetBound S n i+D^i
  refine ⟨finiteJetPowerBound B r,finiteJetPowerBound_ge_one B r,?_⟩
  intro i hi hir H p
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
  exact hn.trans ((add_le_add hab (hDB i hi hir H)).trans
    (by simpa only [B,add_assoc] using finite_jet_bound_le_power B r i hi hir))

end QuantitativeFollowup
