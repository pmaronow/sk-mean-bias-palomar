module
public import QuantitativeFollowup.ScalarFutureSquare
public import FRSB.StoppedOptimalProcess
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! A literal terminal spin is sampled from the constructed diffusion.
Its Gibbs probability is exp(eY_1)/(2 cosh Y_1), and adjoining it
preserves every scalar path marginal. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def scalarSpinWeight (x : ℝ) (e : Bool) : ℝ :=
  Real.exp (Paper.spinSign e*x)/(2*Real.cosh x)

theorem scalarSpinWeight_pos (x : ℝ) (e : Bool) : 0 < scalarSpinWeight x e :=
  div_pos (Real.exp_pos _) (mul_pos (by norm_num) (Real.cosh_pos _))

theorem scalarSpinWeight_sum (x : ℝ) : ∑ e : Bool,scalarSpinWeight x e=1 := by
  simp only [Fintype.sum_bool,scalarSpinWeight,Paper.spinSign,Bool.false_eq_true,ite_false,ite_true,
    neg_one_mul,one_mul]
  rw [←add_div,Real.cosh_eq]
  have hp : 0 < Real.exp x+Real.exp (-x) := add_pos (Real.exp_pos _) (Real.exp_pos _)
  field_simp

theorem scalarSpinPMF_sum (x : ℝ) :
    ∑ e : Bool,ENNReal.ofReal (scalarSpinWeight x e)=1 := by
  rw [←ENNReal.ofReal_sum_of_nonneg (fun e _ => (scalarSpinWeight_pos x e).le),scalarSpinWeight_sum]
  norm_num

def scalarSpinPMF (x : ℝ) : PMF Bool :=
  PMF.ofFintype (fun e => ENNReal.ofReal (scalarSpinWeight x e)) (scalarSpinPMF_sum x)

def scalarSpinLaw (x : ℝ) : Measure Bool := (scalarSpinPMF x).toMeasure

instance scalarSpinLaw_probability (x : ℝ) : IsProbabilityMeasure (scalarSpinLaw x) :=
  PMF.toMeasure.isProbabilityMeasure _

theorem integral_scalarSpinLaw (x : ℝ) (f : Bool → ℝ) :
    (∫ e,f e ∂scalarSpinLaw x)=∑ e : Bool,scalarSpinWeight x e*f e := by
  rw [scalarSpinLaw,PMF.integral_eq_sum]
  simp only [scalarSpinPMF,PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (scalarSpinWeight_pos x _).le,smul_eq_mul]

theorem integral_scalarSpinLaw_sign (x : ℝ) :
    (∫ e,Paper.spinSign e ∂scalarSpinLaw x)=Real.tanh x := by
  rw [integral_scalarSpinLaw]
  simp only [Fintype.sum_bool,scalarSpinWeight,Paper.spinSign,Bool.false_eq_true,ite_false,ite_true,
    neg_one_mul,one_mul,mul_neg_one,mul_one]
  rw [Real.tanh_eq_sinh_div_cosh,Real.sinh_eq]
  field_simp
  ring

def scalarTerminalSpinKernel (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) :
    Kernel Paper.BrownianSample Bool where
  toFun ω := scalarSpinLaw (parisiPhysicalSplitState β 0 μ 1 ω)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [scalarSpinLaw,PMF.toMeasure_apply _ hS,tsum_fintype]
    apply Finset.measurable_sum
    intro e _
    by_cases he : e∈S
    · simp only [Set.indicator_of_mem he,scalarSpinPMF,PMF.ofFintype_apply,scalarSpinWeight]
      have hX : Measurable (parisiPhysicalSplitState β 0 μ 1) :=
        (measurable_parisiPhysicalSplitState_past β 0 hβ μ 1).mono
          (canonicalBrownianFiltration.le _) le_rfl
      exact ((Real.measurable_exp.comp (hX.const_mul _)).div
        (Real.continuous_cosh.measurable.comp hX |>.const_mul 2)).ennreal_ofReal
    · simp only [Set.indicator_of_notMem he]
      exact measurable_const

instance scalarTerminalSpinKernel_isMarkov (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) : IsMarkovKernel (scalarTerminalSpinKernel β hβ μ) :=
  ⟨fun ω => (show IsProbabilityMeasure
    (scalarSpinLaw (parisiPhysicalSplitState β 0 μ 1 ω)) from inferInstance)⟩

def scalarMarkedSpinLaw (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) :
    Measure (Paper.BrownianSample×Bool) :=
  canonicalBrownianMeasure ⊗ₘ scalarTerminalSpinKernel β hβ μ

instance scalarMarkedSpinLaw_probability (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) : IsProbabilityMeasure (scalarMarkedSpinLaw β hβ μ) := by
  unfold scalarMarkedSpinLaw
  infer_instance

theorem scalarMarkedSpinLaw_fst (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) :
    (scalarMarkedSpinLaw β hβ μ).fst=canonicalBrownianMeasure :=
  Measure.fst_compProd _ _

theorem integral_scalarMarkedSpinLaw_sample (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (f : Paper.BrownianSample → ℝ) (hf : Measurable f) :
    (∫ z,f z.1 ∂scalarMarkedSpinLaw β hβ μ)=∫ ω,f ω ∂canonicalBrownianMeasure := by
  rw [←scalarMarkedSpinLaw_fst β hβ μ]
  exact (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm

theorem integral_scalarMarkedSpinLaw_terminal_sign (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (f : Paper.BrownianSample → ℝ) (hf : Measurable f)
    (K : ℝ) (hb : ∀ ω,‖f ω‖ ≤ K) :
    (∫ z,f z.1*Paper.spinSign z.2 ∂scalarMarkedSpinLaw β hβ μ)=
      ∫ ω,f ω*M β μ 1 ω ∂canonicalBrownianMeasure := by
  have hm : Measurable (fun z : Paper.BrownianSample×Bool => f z.1*Paper.spinSign z.2) :=
    (hf.comp measurable_fst).mul ((measurable_of_finite Paper.spinSign).comp measurable_snd)
  have hi : Integrable (fun z : Paper.BrownianSample×Bool => f z.1*Paper.spinSign z.2)
      (scalarMarkedSpinLaw β hβ μ) := by
    apply (integrable_const K).mono' hm.aestronglyMeasurable
    exact .of_forall fun z => by
      rw [norm_mul]
      have hs : ‖Paper.spinSign z.2‖=1 := by cases z.2 <;> norm_num [Paper.spinSign]
      rw [hs,mul_one]
      exact hb z.1
  rw [scalarMarkedSpinLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun ω => by
    change (∫ e,f ω*Paper.spinSign e ∂scalarSpinLaw
      (parisiPhysicalSplitState β 0 μ 1 ω))=_
    rw [integral_const_mul,integral_scalarSpinLaw_sign]
    have he := scalarGradient_physicalSplitState β hβ μ 1 ω
    change parisiGradient β μ (1,parisiPhysicalSplitState β 0 μ 1 ω)=M β μ 1 ω at he
    rw [parisiGradient_terminal β μ] at he
    rw [he]

end QuantitativeFollowup
