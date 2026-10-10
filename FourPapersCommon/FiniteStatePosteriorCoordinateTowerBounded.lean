module
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerTransport
public import FourPapersCommon.FiniteStateCascadeRecurrence

@[expose] public section

/-! The honest whole Gaussian posterior backward tower for bounded functions
of an arbitrary retained raw input and a terminal feature. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1200000

theorem integral_history_backward_observation_upto {State : Type*} [MeasurableSpace State]
    (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ→Kernel State State) (hκ : ∀i,IsMarkovKernel (κ i)) (N i : ℕ) (hi : i≤N)
    (f : ℕ→State→ℝ) (hf : ∀i,i≤N→Measurable (f i))
    (R : ℝ) (hR : ∀i,i≤N→∀x,|f i x|≤R)
    (hb : ∀i,i<N→∀x,f i x=∫y,f (i+1) y ∂κ i x)
    (g : State→ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀x,|g x|≤B) :
    (∫h,g (historyObservation N i h)*f N (h (Fin.last N)) ∂finiteHistoryLaw ν κ N)=
      ∫h,g (h (Fin.last i))*f i (h (Fin.last i)) ∂finiteHistoryLaw ν κ i := by
  induction N with
  | zero =>
    have hi0 : i=0 := by omega
    subst i
    simp
  | succ N ih =>
    by_cases hii : i=N+1
    · subst i
      simp
    · have hi' : i≤N := by omega
      rw [integral_history_observation_step ν κ hκ N i hi' g (f (N+1)) hg (hf _ le_rfl)
        B R hB (hR _ le_rfl)]
      simp_rw [←hb N (Nat.lt_succ_self _)]
      exact ih hi' (fun i hi=>hf i (hi.trans (Nat.le_succ _)))
        (fun i hi=>hR i (hi.trans (Nat.le_succ _)))
        (fun i hi=>hb i (hi.trans (Nat.lt_succ_self _)))

 theorem independentHistory_latest_noise {E Z : Type*}
    (u : ℕ→(E×Z)→Z→(E×Z)) (hu : ∀i p z,(u i p z).2=z)
    (m : ℕ) (x : E×Z) (z : Fin m→Z) (i : Fin m) :
    (independentHistory u m (x,z) i.succ).2=z i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.lastCases ?_ (fun k=>?_) i
    · simp only [independentHistory,Fin.succ_last,Fin.snoc_last,hu]
    · have he : k.castSucc.succ=k.succ.castSucc := by ext;rfl
      rw [he]
      simp only [independentHistory,Fin.snoc_castSucc]
      exact ih (fun k=>z k.castSucc) k

variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

theorem posteriorCoordinateHistory_noise
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N : ℕ)
    (H : FiniteStateField S) (z : Fin N→FiniteStateGaussianInput I) (r : Fin N) :
    (historyObservation N (r.val+1) (posteriorCoordinateHistory L N H z)).2=z r := by
  have he : Fin.ofNat (N+1) (r.val+1)=r.succ := by
    ext
    simp only [Fin.val_ofNat,Fin.val_succ,Nat.mod_eq_of_lt (by omega : r.val+1<N+1)]
  rw [historyObservation,he]
  exact independentHistory_latest_noise (posteriorCoordinateUpdate L N) (fun _ _ _=>rfl) N (H,0) z r

private theorem posteriorCoordinate_backward_feature (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (N i : ℕ) (hi : i<N)
    (p : PosteriorCoordinateState S I) (K : FiniteStateField S) :
    fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-i)) p.1 K=
      ∫y,fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-(i+1))) y.1 K
        ∂posteriorCoordinateKernel V a L N i p := by
  have hd : N-i=(N-1-i)+1 := by omega
  have he : N-(i+1)=N-1-i := by omega
  rw [hd,he,fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L,
    posteriorCoordinateKernel_apply V a ha L]
  have hmap : Measurable (posteriorCoordinateUpdate L N i p) :=
    (measurable_posteriorCoordinateUpdate L N i).comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (fun y : PosteriorCoordinateState S I=>
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-1-i)) y.1 K) :=
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-1-i)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const).measurable.comp measurable_fst
  rw [integral_map hmap.aemeasurable hf.aestronglyMeasurable]
  rw [finiteStateGaussianCascadeKernel]
  change (∫y,fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-1-i)) y K
    ∂finiteStateGaussianStepKernel (a (N-1-i)) (L (N-1-i))
      (finiteStateGaussianTerminalCascade V a L (N-1-i)) p.1)=_
  rw [finiteStateGaussianStepKernel_apply _ _ _
    (contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-1-i)).continuous.measurable,
    finiteStateGaussianStepLaw_eq_map_tilted _ _ _
    (contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-1-i)).continuous.measurable p.1,
    integral_map (by fun_prop)
      (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-1-i)).continuous_fderiv
        (by norm_num)).clm_apply continuous_const).aestronglyMeasurable]
  rfl

/-- A terminal feature paired with a bounded function of any actual raw
Gaussian input equals the true current-input/remaining-spin law averaged
against the genuine retained normalized prefix. -/
theorem cascadePosteriorGaussianLaw_coordinate_feature_tower_bounded (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (N : ℕ) (H K : FiniteStateField S) (r : Fin N)
    (g : FiniteStateGaussianInput I→ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀z,|g z|≤B) :
    (∫z,g (z.1 r)*K z.2 ∂cascadePosteriorGaussianLaw V a L N H)=
      ∫h,(∫z,g z.1*K z.2 ∂finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val)
        (h (Fin.last r.val)).1) ∂posteriorCoordinateHistoryLaw V a L N H r.val := by
  have hB0 : 0≤B := (abs_nonneg (g 0)).trans (hB 0)
  haveI:=cascadePosteriorGaussianLaw_probability V a ha L N H
  haveI:=posteriorCoordinatePosteriorLaw_probability V a ha L N H
  haveI:=posteriorCoordinateHistoryLaw_probability V a ha L N H N
  have hcurrent : Measurable (fun p : FiniteHistory (PosteriorCoordinateState S I) N×S=>
      g (historyObservation N (r.val+1) p.1).2*K p.2) :=
    (hg.comp (measurable_snd.comp ((measurable_historyObservation _ _).comp measurable_fst))).mul
      ((measurable_of_finite (fun σ:S=>K σ)).comp measurable_snd)
  have hi : Integrable (fun p : FiniteHistory (PosteriorCoordinateState S I) N×S=>
      g (historyObservation N (r.val+1) p.1).2*K p.2) (posteriorCoordinatePosteriorLaw V a L N H) :=
    source_bounded_integrable _ _ hcurrent (B*‖K‖) (fun p=>by
      rw [abs_mul]
      exact mul_le_mul (hB _) (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K p.2)
        (abs_nonneg _) hB0)
  have hm := integral_map (μ:=cascadePosteriorGaussianLaw V a L N H)
    (measurable_posteriorCoordinateJointMap L N H).aemeasurable
    hcurrent.aestronglyMeasurable
  rw [cascadePosteriorGaussianLaw_augmented_map V a ha L N H] at hm
  have hstart : (∫z,g (z.1 r)*K z.2 ∂cascadePosteriorGaussianLaw V a L N H)=
      ∫p,g (historyObservation N (r.val+1) p.1).2*K p.2
        ∂posteriorCoordinatePosteriorLaw V a L N H := by
    rw [hm]
    apply integral_congr_ae
    exact .of_forall fun z=>by simp only [posteriorCoordinateJointMap,posteriorCoordinateHistory_noise]
  rw [hstart,posteriorCoordinatePosteriorLaw,Measure.integral_compProd hi]
  simp_rw [integral_const_mul,posteriorCoordinateTerminalKernel,Kernel.comap_apply,
    integral_finiteStateGibbsKernel,←fderiv_gtStateLogPartition_apply]
  have hzero : finiteStateGaussianTerminalCascade V a L (N-N)=gtStateLogPartition V := by
    simp [finiteStateGaussianTerminalCascade,finiteStateGaussianCascade]
  rw [←hzero]
  change (∫h,g (historyObservation N (r.val+1) h).2*
    fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-N)) (h (Fin.last N)).1 K
    ∂finiteHistoryLaw (Measure.dirac (H,0)) (posteriorCoordinateKernel V a L N) N)=_
  rw [integral_history_backward_observation_upto (Measure.dirac (H,0))
    (posteriorCoordinateKernel V a L N) (posteriorCoordinateKernel_markov V a ha L N)
    N (r.val+1) (by omega)
    (fun i p=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-i)) p.1 K)
    (fun i _=>(((contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-i)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const).measurable.comp measurable_fst)
    ‖K‖ (fun i _ p=>finiteStateCascadeFirst_abs_le V a ha L (N-i) p.1 K)
    (fun i hi p=>posteriorCoordinate_backward_feature V a ha L N i hi p K)
    (fun p=>g p.2) (hg.comp measurable_snd) B (fun p=>hB p.2)]
  haveI:=posteriorCoordinateHistoryLaw_probability V a ha L N H r.val
  haveI:=posteriorCoordinateKernel_markov V a ha L N r.val
  let J := fun p : FiniteHistory (PosteriorCoordinateState S I) r.val×PosteriorCoordinateState S I=>
    g p.2.2*fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-(r.val+1))) p.2.1 K
  have hJm : Measurable J := (hg.comp (measurable_snd.comp measurable_snd)).mul
    ((((contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-(r.val+1))).continuous_fderiv
      (by norm_num)).clm_apply continuous_const).measurable.comp (measurable_fst.comp measurable_snd))
  have hJi : Integrable J ((posteriorCoordinateHistoryLaw V a L N H r.val) ⊗ₘ
      (posteriorCoordinateKernel V a L N r.val).comap (fun h=>h (Fin.last r.val)) (by fun_prop)) :=
    source_bounded_integrable _ _ hJm (B*‖K‖) (fun p=>by
      rw [abs_mul]
      exact mul_le_mul (hB _) (finiteStateCascadeFirst_abs_le V a ha L _ _ K)
        (abs_nonneg _) hB0)
  rw [finiteHistoryLaw,(historySplit r.val).symm.measurableEmbedding.integral_map]
  simp only [historySplit_symm_apply,Fin.snoc_last]
  change (∫p,J p ∂((posteriorCoordinateHistoryLaw V a L N H r.val) ⊗ₘ
      (posteriorCoordinateKernel V a L N r.val).comap (fun h=>h (Fin.last r.val)) (by fun_prop)))=_
  rw [Measure.integral_compProd hJi]
  apply integral_congr_ae
  exact .of_forall fun h=>by
    dsimp only [J]
    have hmap : Measurable (posteriorCoordinateUpdate L N r.val (h (Fin.last r.val))) :=
      (measurable_posteriorCoordinateUpdate L N r.val).comp (measurable_const.prodMk measurable_id)
    have hf : Measurable (fun p : PosteriorCoordinateState S I=>g p.2*
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L (N-(r.val+1))) p.1 K) :=
      (hg.comp measurable_snd).mul
        ((((contDiff_one_finiteStateGaussianTerminalCascade V a ha L (N-(r.val+1))).continuous_fderiv
          (by norm_num)).clm_apply continuous_const).measurable.comp measurable_fst)
    rw [Kernel.comap_apply,posteriorCoordinateKernel_apply V a ha L,
      integral_map hmap.aemeasurable hf.aestronglyMeasurable]
    have he : N-(r.val+1)=N-1-r.val := by omega
    rw [he]
    haveI:=finiteStateGaussianCoordinateSpinLaw_probability V a ha L (N-1-r.val) (h (Fin.last r.val)).1
    have hib : Integrable (fun z : FiniteStateGaussianInput I×S=>g z.1*K z.2)
        (finiteStateGaussianCoordinateSpinLaw V a L (N-1-r.val) (h (Fin.last r.val)).1) :=
      source_bounded_integrable _ _ ((hg.comp measurable_fst).mul
        ((measurable_of_finite (fun σ:S=>K σ)).comp measurable_snd)) (B*‖K‖) (fun z=>by
          rw [abs_mul]
          exact mul_le_mul (hB _) (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2)
            (abs_nonneg _) hB0)
    haveI:=finiteStateGaussianCoordinateSpinKernel_markov V a ha L (N-1-r.val) (h (Fin.last r.val)).1
    haveI:=isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
      _ (finiteStateGaussianTerminalCascade_lipschitz V a ha L (N-1-r.val)) (L (N-1-r.val))
      (h (Fin.last r.val)).1 (a (N-1-r.val)))
    rw [finiteStateGaussianCoordinateSpinLaw,Measure.integral_compProd hib]
    simp_rw [finiteStateGaussianCoordinateSpinKernel,Kernel.comap_apply,integral_const_mul,
      ←fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L (N-1-r.val)]
    rfl

end FourPapersCommon
