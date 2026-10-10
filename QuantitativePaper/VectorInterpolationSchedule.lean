module
public import QuantitativePaper.VectorInterpolationNoise
public import QuantitativePaper.VectorTerminalLinear
public import QuantitativePaper.FiniteVectorFunctional
public import FourPapersCommon.GenericFiniteStateCascadeEndpointContinuity

@[expose] public section

/-! The actual finite vector interpolation as a signed covariance schedule.
The final increasing-covariance level is the fractional completed-disorder
average; all preceding decreasing-covariance levels are the field recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def vectorInterpolationFieldLinear (n : ℕ) : VectorInterpolationInput n →L[ℝ] Field n :=
  LinearMap.toContinuousLinearMap
    { toFun:=vectorInterpolationField n
      map_add':=by intro x y;ext i;simp [vectorInterpolationField]
      map_smul':=by intro c x;ext i;simp [vectorInterpolationField] }

def vectorInterpolationDisorderLinear (n : ℕ) : VectorInterpolationInput n →L[ℝ] Couplings n×ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun:=vectorInterpolationDisorder n
      map_add':=by intro x y;ext e <;> simp [vectorInterpolationDisorder,mul_add]
      map_smul':=by intro c x;ext e <;> simp [vectorInterpolationDisorder,mul_assoc,mul_left_comm] }

def vectorSpinFieldEmbedding (n : ℕ) : Field n →L[ℝ] FiniteStateField (Configuration n) :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun x=>WithLp.toLp 2 (fun σ=>fieldDot x σ)
      map_add':=by intro x y;ext σ;simp [fieldDot,add_mul,Finset.sum_add_distrib]
      map_smul':=by intro c x;ext σ;simp [fieldDot,mul_assoc,Finset.mul_sum] }

def vectorDisorderFieldEmbedding (n : ℕ) (β : ℝ) :
    (Couplings n×ℝ) →L[ℝ] FiniteStateField (Configuration n) :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun p=>WithLp.toLp 2 (fun σ=>β*(energyLinear n σ p.1+p.2))
      map_add':=by intro x y;ext σ;simp [mul_add];ring
      map_smul':=by intro c x;ext σ;simp [mul_assoc];ring }

def vectorInterpolationState (n : ℕ) (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    FiniteStateField (Configuration n) :=
  Real.sqrt t • vectorDisorderFieldEmbedding n β p+vectorSpinFieldEmbedding n x

theorem vectorTerminalPotential_eq_interpolation_state (n : ℕ) (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) :
    vectorTerminalPotential n β t p x=gtStateLogPartition (fun _=>0)
      (vectorInterpolationState n β t p x) := by
  unfold vectorTerminalPotential terminalPotential terminalPartition gtStateLogPartition gtStatePartition
  congr 2
  funext σ
  simp only [vectorInterpolationState,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    vectorDisorderFieldEmbedding,vectorSpinFieldEmbedding,LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_toLp,energyLinear_apply,zero_add,vectorTerminalExponent]
  ring

def vectorInterpolationMass {k : ℕ} (s : RSBScheme k) (a : ℝ) (j : ℕ) : ℝ :=
  if j<k+2 then s.m (k+1-j) else a

def vectorInterpolationDirection {n k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    VectorInterpolationInput n →L[ℝ] FiniteStateField (Configuration n) :=
  if j<k+2 then Real.sqrt (β^2*(s.q (k+2-j)-s.q (k+1-j))) •
    ((vectorSpinFieldEmbedding n).comp (vectorInterpolationFieldLinear n))
  else (vectorDisorderFieldEmbedding n β).comp (vectorInterpolationDisorderLinear n)

def vectorInterpolationIncreasing {k : ℕ} (_s : RSBScheme k) (j : ℕ) : Bool :=
  decide (k+2≤j)

theorem vectorInterpolationMass_nonneg {k : ℕ} (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (j : ℕ) :
    0≤vectorInterpolationMass s a j := by
  unfold vectorInterpolationMass
  split_ifs with hj
  · exact s.m_nonneg (Nat.sub_le _ _)
  · exact ha

theorem vectorInterpolationState_field_shift {n : ℕ} (β t : ℝ) (p : Couplings n×ℝ)
    (x z : Field n) (v : ℝ) :
    vectorInterpolationState n β t p (fieldShift v x z)=
      vectorInterpolationState n β t p x+Real.sqrt v • vectorSpinFieldEmbedding n z := by
  simp only [vectorInterpolationState,fieldShift,map_add,map_smul]
  abel

theorem vectorInterpolation_field_step {n : ℕ} (β t m v : ℝ) (p : Couplings n×ℝ)
    (x : Field n) (F : FiniteStateField (Configuration n)→ℝ) (f : Field n→ℝ)
    (hf : Continuous f)
    (he : ∀y,F (vectorInterpolationState n β t p y)=f y) :
    finiteStateGaussianStep m (Real.sqrt v •
      ((vectorSpinFieldEmbedding n).comp (vectorInterpolationFieldLinear n))) F
        (vectorInterpolationState n β t p x)=vectorColeHopfStep v m f x := by
  have hh : (fun z : VectorInterpolationInput n=>F (vectorInterpolationState n β t p x+
      (Real.sqrt v • ((vectorSpinFieldEmbedding n).comp (vectorInterpolationFieldLinear n))) z))=
      fun z=>f (fieldShift v x (vectorInterpolationField n z)) := by
    funext z
    rw [←he]
    congr 1
    exact (vectorInterpolationState_field_shift β t p x (vectorInterpolationField n z) v).symm
  unfold finiteStateGaussianStep sourceLogAverage vectorColeHopfStep vectorStepPartition
  rw [hh]
  split_ifs
  · have hi:=integral_map (μ:=stdGaussian (VectorInterpolationInput n)) (measurable_vectorInterpolationField n).aemeasurable
      (hf.comp (show Continuous (fieldShift v x) by unfold fieldShift;fun_prop)).aestronglyMeasurable
    rw [stdGaussian_map_vectorInterpolationField] at hi
    exact hi.symm
  · have hi:=integral_map (μ:=stdGaussian (VectorInterpolationInput n)) (measurable_vectorInterpolationField n).aemeasurable
      (Real.continuous_exp.comp
        ((hf.comp (show Continuous (fieldShift v x) by unfold fieldShift;fun_prop)).const_mul m)).aestronglyMeasurable
    rw [stdGaussian_map_vectorInterpolationField] at hi
    exact congrArg (fun y : ℝ=>Real.log y/m) hi.symm

theorem vectorInterpolationCascade_eq_recursion {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1) (j : ℕ) (hj : j≤k+2) (p : Couplings n×ℝ) (x : Field n) :
    finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
      (vectorInterpolationMass s a) (vectorInterpolationDirection (n:=n) s β)
      (vectorInterpolationIncreasing s) j t (vectorInterpolationState n β t p x)=
      vectorRecursion s β t p j x := by
  induction j generalizing x with
  | zero => exact (vectorTerminalPotential_eq_interpolation_state n β t p x).symm
  | succ j ih =>
    have hj' : j<k+2 := by omega
    have hq : 0≤β^2*(s.q (k+2-j)-s.q (k+1-j)) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (by
        have hh:=s.q_mono (k+1-j) (by omega)
        simpa only [show k+1-j+1=k+2-j by omega] using hh))
    simp only [finiteStateGaussianScheduledTerminalCascade,vectorInterpolationMass,
      vectorInterpolationDirection,if_pos hj',vectorInterpolationIncreasing,vectorRecursion,
      finiteStateScheduleScale,show ¬k+2≤j by omega,decide_false, Bool.false_eq_true,ite_false]
    rw [smul_smul,←Real.sqrt_mul (sub_nonneg.mpr ht)]
    apply vectorInterpolation_field_step
    · exact (vectorRecursion_lipschitz s β t p j).continuous
    · exact fun y=>ih (by omega) y

theorem vectorInterpolationCascade_eq_outer_average {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1) :
    finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
      (vectorInterpolationMass s a) (vectorInterpolationDirection (n:=n) s β)
      (vectorInterpolationIncreasing s) (k+3) t 0=
      sourceLogAverage (completionLaw n) a (fun p=>vectorRecursion s β t p (k+2) 0) := by
  have hidx : k+3=(k+2)+1 := by omega
  rw [hidx,finiteStateGaussianScheduledTerminalCascade]
  simp only [vectorInterpolationMass,vectorInterpolationDirection,lt_self_iff_false,ite_false,
    vectorInterpolationIncreasing,le_refl,decide_true,finiteStateScheduleScale,ite_true]
  have he : (fun z : VectorInterpolationInput n=>
      finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
        (vectorInterpolationMass s a) (vectorInterpolationDirection (n:=n) s β)
        (vectorInterpolationIncreasing s) (k+2) t
        (0+(Real.sqrt t • ((vectorDisorderFieldEmbedding n β).comp
          (vectorInterpolationDisorderLinear n))) z))=
      fun z=>vectorRecursion s β t (vectorInterpolationDisorder n z) (k+2) 0 := by
    funext z
    have hp : 0+(Real.sqrt t • ((vectorDisorderFieldEmbedding n β).comp
        (vectorInterpolationDisorderLinear n))) z=
        vectorInterpolationState n β t (vectorInterpolationDisorder n z) 0 := by
      simp only [vectorInterpolationState,map_zero,add_zero,zero_add,smul_apply,
        ContinuousLinearMap.comp_apply]
      rfl
    rw [hp]
    exact vectorInterpolationCascade_eq_recursion s β t a ht (k+2) le_rfl _ _
  have hm : Measurable (fun p : Couplings n×ℝ=>vectorRecursion s β t p (k+2) 0) :=
    (measurable_vectorRecursion s β t (k+2)).comp (measurable_id.prodMk measurable_const)
  unfold finiteStateGaussianStep sourceLogAverage
  rw [he]
  split_ifs
  · have hi:=integral_map (μ:=stdGaussian (VectorInterpolationInput n))
      (measurable_vectorInterpolationDisorder n).aemeasurable hm.aestronglyMeasurable
    rw [stdGaussian_map_vectorInterpolationDisorder] at hi
    exact hi.symm
  · have hi:=integral_map (μ:=stdGaussian (VectorInterpolationInput n))
      (measurable_vectorInterpolationDisorder n).aemeasurable
      (Real.measurable_exp.comp (hm.const_mul a)).aestronglyMeasurable
    rw [stdGaussian_map_vectorInterpolationDisorder] at hi
    exact congrArg (fun y : ℝ=>Real.log y/a) hi.symm

theorem finiteVectorFunctional_eq_interpolation_schedule {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1) (ha : a≠0) :
    finiteVectorFunctional n s β t a=
      finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
        (vectorInterpolationMass s a) (vectorInterpolationDirection (n:=n) s β)
        (vectorInterpolationIncreasing s) (k+3) t 0/(n:ℝ)-
      (1-t)*(β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q) := by
  rw [vectorInterpolationCascade_eq_outer_average s β t a ht]
  simp only [sourceLogAverage,ha,ite_false,finiteVectorFunctional]
  congr 1
  ring

theorem continuous_vectorInterpolationCascade {n k : ℕ} (s : RSBScheme k)
    (β a : ℝ) (ha : 0≤a) (j : ℕ) :
    Continuous (fun w : ℝ×FiniteStateField (Configuration n)=>
      finiteStateGaussianScheduledTerminalCascade (fun _=>0) (vectorInterpolationMass s a)
        (vectorInterpolationDirection (n:=n) s β) (vectorInterpolationIncreasing s) j w.1 w.2) := by
  let mass:=vectorInterpolationMass s a
  let A:=vectorInterpolationDirection (n:=n) s β
  let up:=vectorInterpolationIncreasing s
  have hmass:=vectorInterpolationMass_nonneg s a ha
  induction j with
  | zero => exact (contDiff_gtStateLogPartition (fun _=>0)).continuous.comp continuous_snd
  | succ j ih =>
    change Continuous (fun w : ℝ×FiniteStateField (Configuration n)=>finiteStateGaussianStep (mass j)
      (finiteStateScheduleScale (up j) w.1 • A j)
      (finiteStateGaussianScheduledTerminalCascade (fun _=>0) mass A up j w.1) w.2)
    have hLip (w : ℝ×FiniteStateField (Configuration n)) : LipschitzWith 1
        (finiteStateGaussianScheduledTerminalCascade (fun _=>0) mass A up j w.1) := by
      rw [finiteStateGaussianScheduledTerminalCascade_eq_current]
      exact finiteStateGaussianTerminalCascade_lipschitz _ mass hmass _ j
    have hscale : Continuous (fun w : ℝ×FiniteStateField (Configuration n)=>
        finiteStateScheduleScale (up j) w.1 • A j) := by
      unfold finiteStateScheduleScale
      split_ifs <;> fun_prop
    exact continuous_finiteStateGaussianStep_family (mass j)
      (fun w : ℝ×FiniteStateField (Configuration n)=>fun H=>
        finiteStateGaussianScheduledTerminalCascade (fun _=>0) mass A up j w.1 H)
      (ih.comp ((continuous_fst.fst).prodMk continuous_snd)) 1 hLip
      (fun w=>finiteStateScheduleScale (up j) w.1 • A j) hscale
      (fun w=>w.2) continuous_snd

def finiteVectorInterpolationTime {n k : ℕ} (s : RSBScheme k) (β a : ℝ) (ha : 0≤a) (t : ℝ) : ℝ :=
  finiteStateGaussianScheduledTerminalTime (fun _ : Configuration n=>0)
    (vectorInterpolationMass s a) (vectorInterpolationMass_nonneg s a ha)
    (vectorInterpolationDirection (n:=n) s β) (vectorInterpolationIncreasing s) (k+3) t 0/(n:ℝ)+
    β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q

theorem hasDerivAt_finiteVectorFunctional_interpolation {n k : ℕ} (s : RSBScheme k)
    (β a : ℝ) (ha : 0<a) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u=>finiteVectorFunctional n s β u a)
      (finiteVectorInterpolationTime (n:=n) s β a ha.le t) t := by
  have hd:=hasDerivAt_finiteStateGaussianScheduledTerminal_time
    (fun _ : Configuration n=>0) (vectorInterpolationMass s a) (vectorInterpolationMass_nonneg s a ha.le)
    (vectorInterpolationDirection (n:=n) s β) (vectorInterpolationIncreasing s) (k+3) t ht 0
  let C:=β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q
  have hc:=((hasDerivAt_id t).const_sub 1).mul_const C
  simp only [neg_mul,one_mul] at hc
  have hf:=hd.div_const (n:ℝ) |>.sub hc
  have he : (fun u=>finiteVectorFunctional n s β u a)=ᶠ[𝓝 t]
      fun u=>finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
        (vectorInterpolationMass s a) (vectorInterpolationDirection (n:=n) s β)
        (vectorInterpolationIncreasing s) (k+3) u 0/(n:ℝ)-(1-u)*C := by
    filter_upwards [isOpen_Iio.mem_nhds ht.2] with u hu
    exact finiteVectorFunctional_eq_interpolation_schedule s β u a hu.le ha.ne'
  convert hf.congr_of_eventuallyEq he using 1 <;> simp only [finiteVectorInterpolationTime,C] <;> ring

theorem continuousOn_finiteVectorInterpolationTime {n k : ℕ} (s : RSBScheme k)
    (β a : ℝ) (ha : 0≤a) :
    ContinuousOn (finiteVectorInterpolationTime (n:=n) s β a ha) (Ioo (0:ℝ) 1) := by
  have hc:=continuousOn_finiteStateGaussianScheduledTerminal_time
    (fun _ : Configuration n=>0) (vectorInterpolationMass s a) (vectorInterpolationMass_nonneg s a ha)
    (vectorInterpolationDirection (n:=n) s β) (vectorInterpolationIncreasing s) (k+3)
  exact ((hc.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun t ht=>⟨ht,mem_univ _⟩)).div_const (n:ℝ)).add_const _

theorem continuousOn_finiteVectorFunctional_interpolation {n k : ℕ} (s : RSBScheme k)
    (β a : ℝ) (ha : 0<a) :
    ContinuousOn (fun t=>finiteVectorFunctional n s β t a) (Icc (0:ℝ) 1) := by
  have h:=((continuous_vectorInterpolationCascade (n:=n) s β a ha.le (k+3)).comp
    (continuous_id.prodMk (continuous_const : Continuous
      (fun _ : ℝ=>(0 : FiniteStateField (Configuration n)))))).div_const (n:ℝ)
  let C:=β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q
  have hh : ContinuousOn (fun t : ℝ =>
      finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
        (vectorInterpolationMass s a) (vectorInterpolationDirection (n:=n) s β)
        (vectorInterpolationIncreasing s) (k+3) t 0/(n:ℝ)-(1-t)*C) (Icc 0 1) :=
    (h.sub (((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).sub
      continuous_id).mul_const C)).continuousOn
  exact hh.congr (fun t ht=>finiteVectorFunctional_eq_interpolation_schedule
    (n:=n) s β t a ht.2 ha.ne')

theorem finiteVectorInterpolationTime_eq_covariance_responses {n k : ℕ} (s : RSBScheme k)
    (β a : ℝ) (ha : 0≤a) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    finiteVectorInterpolationTime (n:=n) s β a ha t=
      ((1/2:ℝ)*∑j∈Finset.range (k+3),
        (if vectorInterpolationIncreasing s j then (1:ℝ) else -1)*
          finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0)
            (vectorInterpolationMass s a)
            (fun i=>finiteStateScheduleScale (vectorInterpolationIncreasing s i) t •
              vectorInterpolationDirection (n:=n) s β i)
            j (k+3-j) 0 (vectorInterpolationDirection (n:=n) s β j))/(n:ℝ)+
        β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q := by
  rw [finiteVectorInterpolationTime,finiteStateGaussianScheduledTerminal_time_eq_responses
    (fun _ : Configuration n=>0) (vectorInterpolationMass s a)
    (vectorInterpolationMass_nonneg s a ha)]
  exact ht

end QuantitativePaper
