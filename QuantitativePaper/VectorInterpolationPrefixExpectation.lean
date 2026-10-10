module
public import QuantitativePaper.VectorInterpolationGibbsMean
public import QuantitativePaper.VectorFiniteTiltedKernelPairing

@[expose] public section

/-! The actual outer Gaussian tilt and chronological kernel prefix identify
cascade expectations with the constructed finite diffusion node law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorFiniteDisorderTilt_map_initial_disorder (s : RSBScheme k) (β t a : ℝ) :
    (vectorFiniteDisorderTilt (n:=n) s β t a).map Prod.fst=vectorOuterLaw s β t a := by
  have he:=map_withDensity_pullback (vectorDisorderBrownianMeasure n) Prod.fst measurable_fst
    (fun p=>ENNReal.ofReal (vectorOuterWeight s β t a p))
    (measurable_vectorOuterWeight s β t a).ennreal_ofReal
  rw [(hasLaw_initialVectorDisorder n).map_eq] at he
  exact he

theorem vectorRootInterpolation_outer_kernel (s : RSBScheme k) (β t a : ℝ)
    (ha : 0 ≤ a) (ht : t ≤ 1) (hq : s.q 1=0) :
    finiteStateGaussianCascadeKernel (vectorRootInterpolationMass s a)
      (vectorRootInterpolationScaledDirection (n:=n) s β t)
      (gtStateLogPartition (fun _ : Configuration n=>0)) (k+1) 0=
      (vectorOuterLaw s β t a).map (fun p=>vectorInterpolationStateMap β t (p,0)) := by
  let F:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationScaledDirection (n:=n) s β t) (k+1)
  have hF : Measurable F:=(contDiff_one_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha)
    (vectorRootInterpolationScaledDirection s β t) (k+1)).continuous.measurable
  have hL (z : VectorInterpolationInput n) :
      vectorRootInterpolationScaledDirection s β t (k+1) z=
        vectorInterpolationStateMap β t (vectorInterpolationDisorder n z,0) := by
    simp only [vectorRootInterpolationScaledDirection,vectorRootInterpolationIncreasing,
      le_refl,decide_true,finiteStateScheduleScale,ite_true,vectorRootInterpolationDirection,
      lt_self_iff_false,ite_false,vectorInterpolationDisorderDirection,
      vectorInterpolationStateMap,vectorInterpolationState,map_zero,add_zero,smul_apply,
      ContinuousLinearMap.comp_apply]
    rfl
  have he (z : VectorInterpolationInput n) :
      F (0+vectorRootInterpolationScaledDirection s β t (k+1) z)=
        vectorRecursion s β t (vectorInterpolationDisorder n z) (k+2) 0 := by
    rw [zero_add,hL]
    have hh:=vectorRootInterpolationCascade_eq_recursion (n:=n) s β t a ht (k+1) le_rfl
      (vectorInterpolationDisorder n z) 0
    rw [finiteStateGaussianScheduledTerminalCascade_eq_current] at hh
    rw [←vectorRecursion_remove_root_zero_cell s β t hq] at hh
    exact hh
  change finiteStateGaussianStepKernel (vectorRootInterpolationMass s a (k+1))
    (vectorRootInterpolationScaledDirection (n:=n) s β t (k+1)) F 0=_
  rw [show vectorRootInterpolationMass s a (k+1)=a by simp [vectorRootInterpolationMass]]
  rw [finiteStateGaussianStepKernel_apply a _ F hF,
    finiteStateGaussianStepLaw_eq_map_tilted a _ F hF 0]
  simp_rw [he]
  have hm : Measurable (fun p : Couplings n×ℝ=>a*vectorRecursion s β t p (k+2) 0):=
    measurable_const.mul ((measurable_vectorRecursion s β t (k+2)).comp
      (measurable_id.prodMk measurable_const))
  have htilt:=tilted_map_eq (stdGaussian (VectorInterpolationInput n))
    (vectorInterpolationDisorder n) (measurable_vectorInterpolationDisorder n) _ hm
  rw [stdGaussian_map_vectorInterpolationDisorder] at htilt
  rw [show vectorOuterLaw (n:=n) s β t a=(completionLaw n).tilted
    (fun p=>a*vectorRecursion s β t p (k+2) 0) from rfl,htilt,
    Measure.map_map (by
      exact (measurable_vectorInterpolationStateMap β t).comp (measurable_id.prodMk measurable_const))
      (measurable_vectorInterpolationDisorder n)]
  congr 1
  exact funext (fun z=>by simpa only [zero_add,Function.comp_def] using hL z)

theorem vectorFinite_reverse_prefix_expectation (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (hq : s.q 1=0) (p : ℕ) (hp : p≤k+1)
    (F : VectorState n→ℝ) (hF : Measurable F) (C : ℝ) (hC : 0≤C)
    (hb : ∀x,|F x|≤C) :
    (∫d,sourceKernelExpectation (fun j=>vectorProfileKernel s β t (k+1-(p+j)))
      (k+1-p) F (d,0)∂vectorOuterLaw s β t a)=
      ∫sample,F (vectorFiniteJointState s β t ht.le (s.q (k+2-p)).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
  let Q:=fun j=>vectorProfileKernel (n:=n) s β t (k+1-(p+j))
  have hQ j : IsMarkovKernel (Q j):=vectorProfileKernel_markov s β t _
  have hme j : Measurable (sourceKernelExpectation Q j F):=
    sourceKernelExpectation_measurable Q F hF j
  have hbe j x : |sourceKernelExpectation Q j F x|≤C:=
    sourceKernelExpectation_abs_le Q hQ F hF C hC hb j x
  have hstep (j : ℕ) (hj : j≤k+1-p) :
      (∫sample,sourceKernelExpectation Q j F
        (vectorFiniteJointState s β t ht.le (s.q (k+2-(p+j))).toNNReal sample)
          ∂vectorFiniteDisorderTilt s β t a)=
      ∫sample,F (vectorFiniteJointState s β t ht.le (s.q (k+2-p)).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
    induction j with
    | zero => simp only [sourceKernelExpectation,Nat.add_zero]
    | succ j ih =>
      have hi : k+1-(p+j)≤k+1:=Nat.sub_le _ _
      have hid : k+1-(p+j)+1=k+2-(p+j):=by omega
      have hid' : k+2-(p+(j+1))=k+1-(p+j):=by omega
      have hpai:=vectorFinite_cell_kernel_pairing_tilt s β t a hβ ht
        (k+1-(p+j)) hi (sourceKernelExpectation Q j F) (hme j) C
        (fun x=>by simpa only [Real.norm_eq_abs] using hbe j x)
        (fun _=>1) measurable_const 1 (by simp)
      simp only [one_mul,hid] at hpai
      rw [hid',sourceKernelExpectation]
      change (∫sample,(∫y,sourceKernelExpectation Q j F y∂vectorProfileKernel s β t
        (k+1-(p+j)) (vectorFiniteJointState s β t ht.le
          (s.q (k+1-(p+j))).toNNReal sample))∂vectorFiniteDisorderTilt s β t a)=_
      rw [←hpai]
      exact ih (by omega)
  have hh:=hstep (k+1-p) le_rfl
  have hi : k+2-(p+(k+1-p))=1:=by omega
  rw [hi,hq,Real.toNNReal_zero] at hh
  have hinit (sample : VectorDisorderBrownianSample n) :
      vectorFiniteJointState s β t ht.le 0 sample=(sample.1,0):=by
    simp [vectorFiniteJointState,vectorFiniteState_zero]
  simp_rw [hinit] at hh
  rw [←vectorFiniteDisorderTilt_map_initial_disorder s β t a]
  change (∫d,sourceKernelExpectation Q (k+1-p) F (d,0)∂
    (vectorFiniteDisorderTilt s β t a).map Prod.fst)=_
  rw [integral_map measurable_fst.aemeasurable (f:=fun d : Couplings n×ℝ=>
    sourceKernelExpectation Q (k+1-p) F (d,0))
      ((hme (k+1-p)).comp (show Measurable (fun d : Couplings n×ℝ=>(d,(0 : Field n))) by
        fun_prop)).aestronglyMeasurable]
  exact hh

theorem vectorRootInterpolation_expectation_eq_finite_node (s : RSBScheme k) (β t a : ℝ)
    (ha : 0 ≤ a) (hβ : β≠0) (ht : t<1) (hq : s.q 1=0) (p : ℕ) (hp : p≤k+1)
    (F : FiniteStateField (Configuration n)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hb : ∀x,|F x|≤C) :
    sourceKernelExpectation (fun j=>finiteStateGaussianCascadeKernel
      (vectorRootInterpolationMass s a) (vectorRootInterpolationScaledDirection (n:=n) s β t)
      (gtStateLogPartition (fun _ : Configuration n=>0)) (p+j)) (k+2-p) F 0=
      ∫sample,F (vectorInterpolationStateMap β t
        (vectorFiniteJointState s β t ht.le (s.q (k+2-p)).toNNReal sample))
        ∂vectorFiniteDisorderTilt s β t a := by
  let N:=k+1-p
  let Q:=fun j=>finiteStateGaussianCascadeKernel (vectorRootInterpolationMass s a)
    (vectorRootInterpolationScaledDirection (n:=n) s β t)
    (gtStateLogPartition (fun _ : Configuration n=>0)) (p+j)
  let R:=fun j=>vectorProfileKernel (n:=n) s β t (k+1-(p+j))
  have hmap j (hj : j<N) x : (R j x).map (vectorInterpolationStateMap β t)=
      Q j (vectorInterpolationStateMap β t x) := by
    have hi : 1 ≤ k+1-(p+j):=by dsimp [N] at hj;omega
    have hi' : k+1-(p+j)≤k+1:=Nat.sub_le _ _
    have hid : k+1-(k+1-(p+j))=p+j:=by dsimp [N] at hj;omega
    simpa only [R,Q,hid] using vectorProfileKernel_spin_field_map s β t a ha ht.le
      (k+1-(p+j)) hi hi' x
  have he x : sourceKernelExpectation R N (fun y=>F (vectorInterpolationStateMap β t y)) x=
      sourceKernelExpectation Q N F (vectorInterpolationStateMap β t x):=
    sourceKernelExpectation_map_intertwining R Q (vectorInterpolationStateMap β t)
      (measurable_vectorInterpolationStateMap β t) N hmap F hF x
  have hN : k+2-p=N+1:=by dsimp [N];omega
  have hpN : p+N=k+1:=by dsimp [N];omega
  change sourceKernelExpectation Q (k+2-p) F 0=_
  rw [hN,sourceKernelExpectation]
  change (∫y,sourceKernelExpectation Q N F y∂finiteStateGaussianCascadeKernel
    (vectorRootInterpolationMass s a) (vectorRootInterpolationScaledDirection s β t)
    (gtStateLogPartition (fun _=>0)) (p+N) 0)=_
  rw [hpN,vectorRootInterpolation_outer_kernel s β t a ha ht.le hq]
  rw [integral_map (show Measurable (fun d : Couplings n×ℝ=>
      vectorInterpolationStateMap β t (d,(0 : Field n))) by
      unfold vectorInterpolationStateMap vectorInterpolationState;fun_prop).aemeasurable
      (sourceKernelExpectation_measurable Q F hF N).aestronglyMeasurable]
  simp_rw [←he]
  rw [←hN]
  exact vectorFinite_reverse_prefix_expectation s β t a hβ ht hq p hp
    (fun y=>F (vectorInterpolationStateMap β t y))
    (hF.comp (measurable_vectorInterpolationStateMap β t)) C hC (fun y=>hb _)

end QuantitativePaper
