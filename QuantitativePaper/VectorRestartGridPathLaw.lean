module
public import QuantitativePaper.VectorRestartGridKernels
public import QuantitativePaper.VectorFourierTests
public import QuantitativePaper.VectorTailPosterior
public import FourPapersCommon.FiniteHistoryPrefix

@[expose] public section

/-! The whole retained path law of the genuinely restarted finite-grid
diffusion. Its initial state is a fixed Dirac state; every transition is
identified from its full-Wiener-past Itô pairing. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorRestartJointState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : VectorState n:=
  (p,vectorRestartState μ β t ht q p x r sample)

theorem adapted_vectorRestartJointState (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (r : ℝ≥0) :
    Measurable[vectorBrownianFiltration n r] (vectorRestartJointState μ β t ht q p x r):=
  measurable_const.prodMk (stronglyAdapted_vectorRestartState μ β t ht q p x r).measurable

theorem vectorRestartGrid_kernel_pairing (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (vectorRestartGridElapsed μ j q i)] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    (∫sample,Z sample*G (vectorRestartGridJointState μ j β t ht.le q p x (i+1) sample)
      ∂vectorDisorderBrownianMeasure n)=
      ∫sample,Z sample*(∫y,G y∂vectorRestartGridKernel μ j β t q i
        (vectorRestartGridJointState μ j β t ht.le q p x i sample))
        ∂vectorDisorderBrownianMeasure n := by
  have hZg:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hg:Measurable G:=hG.regularity.continuous.measurable
  have hgb:∀y,‖G y‖≤hG.bounds 0:=fun y=>by
    simpa only [norm_iteratedFDeriv_zero] using hG.jets 0 (by omega) y
  have hleft:Integrable (fun sample=>Z sample*G
      (vectorRestartGridJointState μ j β t ht.le q p x (i+1) sample))
      (vectorDisorderBrownianMeasure n):=by
    apply (integrable_const ((C:ℝ)*hG.bounds 0)).mono'
      (hZg.mul (hg.comp (measurable_vectorRestartGridJointState μ j β t ht.le q p x _))).aestronglyMeasurable
    exact .of_forall fun sample=>by
      simp only [Pi.mul_apply,Function.comp_apply]
      rw [norm_mul]
      exact mul_le_mul (hC sample) (hgb _) (norm_nonneg _) C.coe_nonneg
  have hkernel:=stronglyMeasurable_kernelObservable
    (vectorRestartGridKernel (n:=n) μ j β t q i) G hg
  have hright:Integrable (fun sample=>Z sample*(∫y,G y∂vectorRestartGridKernel μ j β t q i
      (vectorRestartGridJointState μ j β t ht.le q p x i sample)))
      (vectorDisorderBrownianMeasure n):=by
    apply (integrable_const ((C:ℝ)*hG.bounds 0)).mono'
      (hZg.mul (hkernel.measurable.comp
        (measurable_vectorRestartGridJointState μ j β t ht.le q p x i))).aestronglyMeasurable
    exact .of_forall fun sample=>by
      simp only [Pi.mul_apply,Function.comp_apply]
      rw [norm_mul]
      exact mul_le_mul (hC sample)
        (by
          simpa using norm_integral_le_of_norm_le_const
            (μ:=vectorRestartGridKernel μ j β t q i
              (vectorRestartGridJointState μ j β t ht.le q p x i sample))
            (Filter.Eventually.of_forall hgb)) (norm_nonneg _) C.coe_nonneg
  have he:=(vectorRestartGrid_backward_identity μ j β t hβ ht q p x i hi hG Z hZ C hC).2
  simp_rw [mul_sub] at he
  rw [integral_sub hleft hright] at he
  exact sub_eq_zero.mp he

theorem vectorRestartGrid_restricted_transition_law (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    (A : Set (VectorDisorderBrownianSample n))
    (hA : MeasurableSet[vectorBrownianFiltration n (vectorRestartGridElapsed μ j q i)] A) :
    ((vectorDisorderBrownianMeasure n).restrict A).map
      (vectorRestartGridJointState μ j β t ht.le q p x (i+1))=
      (vectorRestartGridKernel μ j β t q i) ∘ₘ
        ((vectorDisorderBrownianMeasure n).restrict A).map
          (vectorRestartGridJointState μ j β t ht.le q p x i) := by
  apply restricted_transitionLaw_of_weighted_fourier
    (vectorBrownianFiltration n (vectorRestartGridElapsed μ j q i))
    (vectorDisorderBrownianMeasure n) ((vectorBrownianFiltration n).le _) _ _
    (measurable_vectorRestartGridJointState μ j β t ht.le q p x i)
    (measurable_vectorRestartGridJointState μ j β t ht.le q p x (i+1))
    (vectorRestartGridKernel μ j β t q i) ?_ ?_ A hA
  · intro L Z hZ hb
    exact vectorRestartGrid_kernel_pairing μ j β t hβ ht q p x i hi (vectorCosineTestData L)
      Z hZ 1 (by simpa only [NNReal.coe_one] using hb)
  · intro L Z hZ hb
    exact vectorRestartGrid_kernel_pairing μ j β t hβ ht q p x i hi (vectorSineTestData L)
      Z hZ 1 (by simpa only [NNReal.coe_one] using hb)

def vectorRestartGridHistory (μ : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (N : ℕ)
    (sample : VectorDisorderBrownianSample n) : FiniteHistory (VectorState n) N:=
  historySample (vectorRestartJointState (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
    β t ht q p x) (vectorRestartGridElapsed μ j q) N sample

theorem vectorRestartGridHistory_law (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N≤vectorDyadicIndex j+3) :
    (vectorDisorderBrownianMeasure n).map (vectorRestartGridHistory μ j β t ht.le q p x N)=
      finiteHistoryLaw (Measure.dirac (p,x)) (vectorRestartGridKernel μ j β t q) N := by
  let ν:=Paper.parisiGridMeasure μ (vectorDyadicIndex j)
  have he:=historySample_law_of_restricted_up_to
    (vectorDisorderBrownianMeasure n) (vectorBrownianFiltration n)
    (vectorRestartJointState ν β t ht.le q p x)
    (adapted_vectorRestartJointState ν β t ht.le q p x)
    (vectorRestartGridElapsed μ j q) (vectorDyadicIndex j+3)
    (fun a b hab hb=>Real.toNNReal_le_toNNReal (sub_le_sub_right
      (max_le_max_left (q:ℝ) ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_mono'
        b hb a hab)) _))
    (vectorRestartGridKernel μ j β t q) (fun _=>inferInstance)
    (fun i hi A hA=>vectorRestartGrid_restricted_transition_law μ j β t hβ ht q p x i
      (by omega) A hA) N hN
  have hzero:vectorRestartGridElapsed μ j q 0=0:=by
    unfold vectorRestartGridElapsed
    rw [(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_zero,
      max_eq_left q.property.1,sub_self,Real.toNNReal_zero]
  have hinit:(vectorDisorderBrownianMeasure n).map
      (vectorRestartJointState ν β t ht.le q p x 0)=Measure.dirac (p,x):=by
    have hf:vectorRestartJointState ν β t ht.le q p x 0=(fun _=>(p,x)):=by
      funext sample
      simp [vectorRestartJointState,vectorRestartState_zero]
    rw [hf]
    simp
  rw [hzero,hinit] at he
  exact he

theorem vectorRestartGrid_full_history_law (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) :
    (vectorDisorderBrownianMeasure n).map
      (vectorRestartGridHistory μ j β t ht.le q p x (vectorDyadicIndex j+3))=
      vectorTailFieldLaw (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        q q.property) β t p x (vectorDyadicIndex j+3) := by
  rw [vectorRestartGridHistory_law μ j β t hβ ht q p x _ le_rfl]
  unfold vectorTailFieldLaw
  have hh:vectorDyadicIndex j+1+1+2-(vectorDyadicIndex j+3)=1:=by omega
  rw [hh]
  congr 1
  funext i
  simp only [vectorRestartGridKernel,Nat.add_comm]

end QuantitativePaper
