module
public import QuantitativeFollowup.ScalarGaussianHistory
public import QuantitativeFollowup.ScalarMarkedSpin
public import FourPapersCommon.CompProdComapMap
public import FRSB.FiniteForwardWeight
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section

/-! Literal finite marked-spin densities of the actual scalar diffusion.
The density is obtained from the constructed conditional transition laws,
not postulated as a Gaussian representation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon Paper FRSB SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

section Mark
variable {A : Type*} [MeasurableSpace A]

def scalarSpinMarkKernel (f : A → ℝ) (hf : Measurable f) : Kernel A Bool where
  toFun a := scalarSpinLaw (f a)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [scalarSpinLaw,PMF.toMeasure_apply _ hS,tsum_fintype]
    apply Finset.measurable_sum
    intro e _
    by_cases he : e∈S
    · simp only [Set.indicator_of_mem he,scalarSpinPMF,PMF.ofFintype_apply,scalarSpinWeight]
      exact ((Real.measurable_exp.comp (hf.const_mul _)).div
        (Real.continuous_cosh.measurable.comp hf |>.const_mul 2)).ennreal_ofReal
    · simp only [Set.indicator_of_notMem he]
      exact measurable_const

instance scalarSpinMarkKernel_markov (f : A → ℝ) (hf : Measurable f) :
    IsMarkovKernel (scalarSpinMarkKernel f hf) :=
  ⟨fun a => (show IsProbabilityMeasure (scalarSpinLaw (f a)) from inferInstance)⟩

theorem scalarSpinLaw_eq_count_withDensity (x : ℝ) :
    scalarSpinLaw x=(Measure.count : Measure Bool).withDensity
      (fun e => ENNReal.ofReal (scalarSpinWeight x e)) := by
  ext S hS
  rw [withDensity_apply _ hS,←lintegral_indicator hS,lintegral_count,tsum_fintype,
    scalarSpinLaw,PMF.toMeasure_apply _ hS,tsum_fintype]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e∈S
  · simp only [Set.indicator_of_mem he,scalarSpinPMF,PMF.ofFintype_apply]
  · simp only [Set.indicator_of_notMem he]

theorem measurable_scalarSpinMarkWeight (f : A → ℝ) (hf : Measurable f) :
    Measurable (fun p : A×Bool => ENNReal.ofReal (scalarSpinWeight (f p.1) p.2)) := by
  unfold scalarSpinWeight
  have hs : Measurable (fun p : A×Bool => Paper.spinSign p.2) :=
    (measurable_of_finite Paper.spinSign).comp measurable_snd
  exact ((Real.measurable_exp.comp (hs.mul (hf.comp measurable_fst))).div
    (Real.continuous_cosh.measurable.comp (hf.comp measurable_fst) |>.const_mul 2)).ennreal_ofReal

theorem scalarSpinMarkKernel_eq_withDensity (f : A → ℝ) (hf : Measurable f) :
    scalarSpinMarkKernel f hf=(Kernel.const A (Measure.count : Measure Bool)).withDensity
      (fun a e => ENNReal.ofReal (scalarSpinWeight (f a) e)) := by
  ext a : 1
  rw [Kernel.withDensity_apply _ (measurable_scalarSpinMarkWeight f hf),Kernel.const_apply]
  exact scalarSpinLaw_eq_count_withDensity _

end Mark

variable {k : ℕ}

def scalarSelectedHistory (s : RSBScheme k) (β : ℝ) (hβ : β≠0) :
    Paper.BrownianSample → (Fin (k+3)→ℝ) :=
  FRSB.historySample (Paper.selectedParisiItoState β 0 hβ (Paper.parisiSchemeMeasure s))
    (FRSB.forwardSchemeTime s 1) (k+2)

theorem measurable_scalarSelectedHistory (s : RSBScheme k) (β : ℝ) (hβ : β≠0) :
    Measurable (scalarSelectedHistory s β hβ) :=
  FRSB.measurable_historySample _
    (fun r => ((FRSB.stronglyAdapted_selectedParisiState β 0 hβ _ r).mono
      (Paper.canonicalBrownianFiltration.le r)).measurable) _ _

theorem parisiPhysicalSplitState_eq_selected (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (ω : Paper.BrownianSample) :
    parisiPhysicalSplitState β 0 μ q ω=Paper.selectedParisiItoState β 0 hβ μ (q : ℝ).toNNReal ω := by
  rw [parisiPhysicalSplitState,parisiNoiseStatePath_canonical β 0 hβ]
  have hi := Paper.selectedParisiItoState_eq β 0 hβ μ (t := (q : ℝ).toNNReal)
    (by rw [Real.coe_toNNReal _ q.property.1];exact q.property.2) ω
  rw [Real.coe_toNNReal _ q.property.1] at hi
  exact hi.symm

def scalarHistorySpinKernel (n : ℕ) : Kernel (Fin (n+1)→ℝ) Bool :=
  scalarSpinMarkKernel (fun h => h (Fin.last n)) (measurable_pi_apply _)

instance scalarHistorySpinKernel_markov (n : ℕ) : IsMarkovKernel (scalarHistorySpinKernel n) :=
  scalarSpinMarkKernel_markov _ _

theorem scalarMarkedSpinLaw_history_map (s : RSBScheme k) (β : ℝ) (hβ : β≠0) :
    (scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s)).map
      (fun p => (scalarSelectedHistory s β hβ p.1,p.2))=
      (Paper.canonicalBrownianMeasure.map (scalarSelectedHistory s β hβ)) ⊗ₘ
        scalarHistorySpinKernel (k+2) := by
  have he := compProd_comap_map_history Paper.canonicalBrownianMeasure
    (scalarSelectedHistory s β hβ) (measurable_scalarSelectedHistory s β hβ)
    (scalarHistorySpinKernel (k+2))
  have hker : (scalarHistorySpinKernel (k+2)).comap (scalarSelectedHistory s β hβ)
      (measurable_scalarSelectedHistory s β hβ)=scalarTerminalSpinKernel β hβ (Paper.parisiSchemeMeasure s) := by
    ext ω : 1
    change scalarSpinLaw (scalarSelectedHistory s β hβ ω (Fin.last (k+2)))=
      scalarSpinLaw (parisiPhysicalSplitState β 0 (Paper.parisiSchemeMeasure s) 1 ω)
    rw [parisiPhysicalSplitState_eq_selected β hβ]
    simp only [scalarSelectedHistory,FRSB.historySample,Fin.val_last,
      FRSB.forwardSchemeTime_top s 1 (by norm_num) le_rfl,Real.toNNReal_one]
    congr 2
    change (1 : ℝ≥0) = Real.toNNReal (1 : ℝ)
    exact Real.toNNReal_one.symm
  rw [hker] at he
  exact he

def scalarFiniteHistoryDensity (s : RSBScheme k) (β : ℝ)
    (p : (Fin (k+3)→ℝ)×Bool) : ℝ≥0∞ :=
  (1/2 : ℝ≥0∞)*ENNReal.ofReal (Real.exp (Paper.spinSign p.2*p.1 (Fin.last (k+2))-
    ∑i∈Finset.range (k+1),(s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 (i+1),p.1 (Fin.ofNat (k+3) (i+1)))))

end QuantitativeFollowup
