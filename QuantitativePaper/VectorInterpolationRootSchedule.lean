module
public import QuantitativePaper.VectorInterpolationCovariance
public import FourPapersCommon.FiniteStateCascadePrefix

@[expose] public section

/-! The root-floor interpolation with its genuinely zero first field cell
removed. All retained masses are decreasing, including the final fractional
disorder mass. This removes a zero-variance layer, not an atom of the measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

def vectorRootInterpolationMass {k : ℕ} (s : RSBScheme k) (a : ℝ) (j : ℕ) : ℝ :=
  if j<k+1 then s.m (k+1-j) else a

def vectorRootInterpolationDirection {n k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    VectorInterpolationInput n →L[ℝ] FiniteStateField (Configuration n) :=
  if j<k+1 then vectorInterpolationFieldDirection n
    (β^2*(s.q (k+2-j)-s.q (k+1-j)))
  else vectorInterpolationDisorderDirection n β

def vectorRootInterpolationIncreasing {k : ℕ} (_s : RSBScheme k) (j : ℕ) : Bool :=
  decide (k+1≤j)

theorem vectorRootInterpolationMass_nonneg {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (j : ℕ) : 0≤vectorRootInterpolationMass s a j := by
  unfold vectorRootInterpolationMass
  split_ifs with hj
  · exact s.m_nonneg (Nat.sub_le _ _)
  · exact ha

theorem vectorRootInterpolationMass_antitone {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (ha : a ≤ s.m 1) : Antitone (vectorRootInterpolationMass s a) := by
  intro i j hij
  unfold vectorRootInterpolationMass
  split_ifs with hi hj
  · exact s.m_mono' (k+1-i) (by omega) (k+1-j) (by omega)
  · omega
  · exact ha.trans (s.m_mono' (k+1-i) (by omega) 1 (by omega))
  · exact le_rfl

theorem vectorRootInterpolationCascade_eq_recursion {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1) (j : ℕ) (hj : j≤k+1) (p : Couplings n×ℝ) (x : Field n) :
    finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
      (vectorRootInterpolationMass s a) (vectorRootInterpolationDirection (n:=n) s β)
      (vectorRootInterpolationIncreasing s) j t (vectorInterpolationState n β t p x)=
      vectorRecursion s β t p j x := by
  rw [finiteStateGaussianScheduledTerminalCascade_eq_current]
  have he:=finiteStateGaussianTerminalCascade_congr_prefix (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorInterpolationMass s a)
    (fun i=>finiteStateScheduleScale (vectorRootInterpolationIncreasing s i) t •
      vectorRootInterpolationDirection (n:=n) s β i)
    (fun i=>finiteStateScheduleScale (vectorInterpolationIncreasing s i) t •
      vectorInterpolationDirection (n:=n) s β i) j
    (fun i hi=>by simp [vectorRootInterpolationMass,vectorInterpolationMass,
      show i<k+1 by omega,show i<k+2 by omega])
    (fun i hi=>by simp [vectorRootInterpolationDirection,vectorInterpolationDirection,
      vectorRootInterpolationIncreasing,vectorInterpolationIncreasing,
      vectorInterpolationFieldDirection,vectorInterpolationDisorderDirection,
      show i<k+1 by omega,show i<k+2 by omega,
      show ¬ (k+1 ≤ i) by omega,show ¬ (k+2 ≤ i) by omega])
  rw [he,←finiteStateGaussianScheduledTerminalCascade_eq_current]
  exact vectorInterpolationCascade_eq_recursion s β t a ht j (by omega) p x

theorem vectorRecursion_remove_root_zero_cell {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hq : s.q 1=0) (p : Couplings n×ℝ) (x : Field n) :
    vectorRecursion s β t p (k+2) x=vectorRecursion s β t p (k+1) x := by
  rw [show k+2=(k+1)+1 by omega,vectorRecursion]
  simp [hq,s.q_zero,vectorColeHopfStep_zero_variance]

theorem vectorRootInterpolationCascade_eq_outer_average {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1) (hq : s.q 1=0) :
    finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
      (vectorRootInterpolationMass s a) (vectorRootInterpolationDirection (n:=n) s β)
      (vectorRootInterpolationIncreasing s) (k+2) t 0=
      sourceLogAverage (completionLaw n) a (fun p=>vectorRecursion s β t p (k+2) 0) := by
  rw [show k+2=(k+1)+1 by omega,finiteStateGaussianScheduledTerminalCascade]
  simp only [vectorRootInterpolationMass,vectorRootInterpolationDirection,
    lt_self_iff_false,ite_false,vectorRootInterpolationIncreasing,le_refl,decide_true,
    finiteStateScheduleScale,ite_true,vectorInterpolationDisorderDirection]
  have he : (fun z : VectorInterpolationInput n=>
      finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
        (vectorRootInterpolationMass s a) (vectorRootInterpolationDirection (n:=n) s β)
        (vectorRootInterpolationIncreasing s) (k+1) t
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
    rw [hp,vectorRootInterpolationCascade_eq_recursion s β t a ht (k+1) le_rfl,
      vectorRecursion_remove_root_zero_cell s β t hq]
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

theorem finiteVectorFunctional_eq_root_interpolation_schedule {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1) (ha : a≠0) (hq : s.q 1=0) :
    finiteVectorFunctional n s β t a=
      finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
        (vectorRootInterpolationMass s a) (vectorRootInterpolationDirection (n:=n) s β)
        (vectorRootInterpolationIncreasing s) (k+2) t 0/(n:ℝ)-
      (1-t)*(β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q) := by
  rw [vectorRootInterpolationCascade_eq_outer_average s β t a ht hq]
  simp only [sourceLogAverage,ha,ite_false,finiteVectorFunctional]
  congr 1
  ring

end QuantitativePaper
