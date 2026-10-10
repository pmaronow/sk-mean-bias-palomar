module
public import QuantitativePaper.VectorInterpolationRootSchedule
public import QuantitativePaper.VectorConditionalLaw
public import FourPapersCommon.KernelExpectationIntertwining

@[expose] public section

/-! Genuine normalized Gaussian kernel transport from the retained vector
state to its finite-spin energy field. The disorder remains in the state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorInterpolationStateMap (β t : ℝ) (p : VectorState n) :
    FiniteStateField (Configuration n) := vectorInterpolationState n β t p.1 p.2

theorem measurable_vectorInterpolationStateMap (β t : ℝ) :
    Measurable (vectorInterpolationStateMap (n:=n) β t) := by
  unfold vectorInterpolationStateMap vectorInterpolationState
  fun_prop

theorem vectorStateKernel_eq_map_tilted
    (f : (Couplings n×ℝ)→Field n→ℝ)
    (hf : Measurable (fun p : VectorState n=>f p.1 p.2))
    (c m : ℝ) (p : VectorState n) :
    vectorStateKernel c m f p=
      ((fieldGaussian n).tilted (fun z=>m*f p.1 (fieldShift c p.2 z))).map
        (fun z=>(p.1,fieldShift c p.2 z)) := by
  let T : Field n→VectorState n:=fun z=>(p.1,fieldShift c p.2 z)
  have hT : Measurable T:=by unfold T fieldShift;fun_prop
  have hw : Measurable (fun y : VectorState n=>ENNReal.ofReal (vectorStateWeight c m f p y)):=
    ((measurable_vectorStateWeight f hf c m).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [vectorStateKernel_apply f hf c m p,vectorGaussianStateKernel_apply]
  change ((fieldGaussian n).map T).withDensity _=_
  rw [←map_withDensity_pullback (fieldGaussian n) T hT _ hw]
  rfl

theorem vectorGaussianStateKernel_spin_field_map (β t c : ℝ) (p : VectorState n) :
    (vectorGaussianStateKernel c p).map (vectorInterpolationStateMap β t)=
      finiteStateGaussianRawKernel (vectorInterpolationFieldDirection n c)
        (vectorInterpolationStateMap β t p) := by
  rw [vectorGaussianStateKernel_apply,Measure.map_map
    (measurable_vectorInterpolationStateMap β t) (by unfold fieldShift;fun_prop),
    finiteStateGaussianRawKernel_apply]
  rw [←stdGaussian_map_vectorInterpolationField n,
    Measure.map_map ((measurable_vectorInterpolationStateMap β t).comp
      (show Measurable (fun z : Field n=>(p.1,fieldShift c p.2 z)) by
        unfold fieldShift;fun_prop)) (measurable_vectorInterpolationField n)]
  congr 1
  funext z
  exact vectorInterpolationState_field_shift β t p.1 p.2 (vectorInterpolationField n z) c

theorem vectorStateKernel_spin_field_map
    (f : (Couplings n×ℝ)→Field n→ℝ)
    (hf : Measurable (fun p : VectorState n=>f p.1 p.2))
    (F : FiniteStateField (Configuration n)→ℝ) (hF : Measurable F)
    (β t c m : ℝ) (he : ∀p : VectorState n,F (vectorInterpolationStateMap β t p)=f p.1 p.2)
    (p : VectorState n) :
    (vectorStateKernel c m f p).map (vectorInterpolationStateMap β t)=
      finiteStateGaussianStepKernel m (vectorInterpolationFieldDirection n c) F
        (vectorInterpolationStateMap β t p) := by
  rw [finiteStateGaussianStepKernel_apply m _ F hF]
  rw [vectorStateKernel_eq_map_tilted f hf c m p,
    Measure.map_map (measurable_vectorInterpolationStateMap β t) (by unfold fieldShift;fun_prop),
    finiteStateGaussianStepLaw_eq_map_tilted m _ F hF]
  have hshift (z : VectorInterpolationInput n) :
      vectorInterpolationStateMap β t (p.1,fieldShift c p.2 (vectorInterpolationField n z))=
        vectorInterpolationStateMap β t p+vectorInterpolationFieldDirection n c z :=
    vectorInterpolationState_field_shift β t p.1 p.2 (vectorInterpolationField n z) c
  have htilt : ((stdGaussian (VectorInterpolationInput n)).tilted
      (fun z=>m*f p.1 (fieldShift c p.2 (vectorInterpolationField n z)))).map
        (vectorInterpolationField n)=
      (fieldGaussian n).tilted (fun z=>m*f p.1 (fieldShift c p.2 z)) := by
    rw [←stdGaussian_map_vectorInterpolationField n,
      tilted_map_eq _ _ (measurable_vectorInterpolationField n) _ (by
        exact measurable_const.mul (hf.comp
          (show Measurable (fun z : Field n=>(p.1,fieldShift c p.2 z)) by
            unfold fieldShift;fun_prop)))]
  rw [←htilt,Measure.map_map (by
    exact (measurable_vectorInterpolationStateMap β t).comp (by unfold fieldShift;fun_prop))
      (measurable_vectorInterpolationField n)]
  have hh : (fun z : VectorInterpolationInput n=>m*f p.1
      (fieldShift c p.2 (vectorInterpolationField n z)))=
      fun z=>m*F (vectorInterpolationStateMap β t p+vectorInterpolationFieldDirection n c z) := by
    funext z
    rw [←he (p.1,fieldShift c p.2 (vectorInterpolationField n z)),hshift]
  rw [hh]
  congr 1
  exact funext hshift

def vectorRootInterpolationScaledDirection {k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (j : ℕ) : VectorInterpolationInput n→L[ℝ]FiniteStateField (Configuration n) :=
  finiteStateScheduleScale (vectorRootInterpolationIncreasing s j) t •
    vectorRootInterpolationDirection s β j

theorem vectorRootInterpolationScaledDirection_field {k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (j : ℕ) (hj : j<k+1) :
    vectorRootInterpolationScaledDirection (n:=n) s β t j=
      vectorInterpolationFieldDirection n ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) := by
  have hq:=s.q_mono (k+1-j) (by omega)
  rw [show k+1-j+1=k+2-j by omega] at hq
  have hv : 0≤β^2*(s.q (k+2-j)-s.q (k+1-j)):=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hq)
  simp only [vectorRootInterpolationScaledDirection,vectorRootInterpolationIncreasing,
    vectorRootInterpolationDirection,if_pos hj,show ¬ (k+1≤j) by omega,
    decide_false,finiteStateScheduleScale,Bool.false_eq_true,ite_false,
    vectorInterpolationFieldDirection,smul_smul]
  rw [Real.sqrt_mul (sub_nonneg.mpr ht)]

theorem vectorProfileKernel_spin_field_map {k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (ha : 0 ≤ a) (ht : t≤1) (i : ℕ) (hi0 : 1 ≤ i) (hi : i ≤ k+1) (p : VectorState n) :
    (vectorProfileKernel s β t i p).map (vectorInterpolationStateMap β t)=
      finiteStateGaussianCascadeKernel (vectorRootInterpolationMass s a)
        (vectorRootInterpolationScaledDirection (n:=n) s β t) (gtStateLogPartition (fun _=>0))
        (k+1-i) (vectorInterpolationStateMap β t p) := by
  let U:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationScaledDirection s β t) (k+1-i)
  have hU : Measurable U:=(contDiff_one_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha)
    (vectorRootInterpolationScaledDirection s β t) (k+1-i)).continuous.measurable
  have he (y : VectorState n) : U (vectorInterpolationStateMap β t y)=
      vectorRecursion s β t y.1 (k+1-i) y.2 := by
    have he0:=vectorRootInterpolationCascade_eq_recursion s β t a ht (k+1-i) (by omega) y.1 y.2
    rw [finiteStateGaussianScheduledTerminalCascade_eq_current] at he0
    exact he0
  rw [vectorProfileKernel,if_pos hi]
  change (vectorStateKernel _ _ _ p).map _=
    finiteStateGaussianStepKernel _ _ U _
  have hid : k+1-(k+1-i)=i:=by omega
  have hid' : k+2-(k+1-i)=i+1:=by omega
  rw [vectorRootInterpolationMass,if_pos (show k+1-i<k+1 by omega),hid,
    vectorRootInterpolationScaledDirection_field s β t ht (k+1-i) (by omega),hid,hid']
  exact vectorStateKernel_spin_field_map _ (measurable_vectorRecursion s β t _) U hU
    β t _ _ he p

end QuantitativePaper
