module
public import QuantitativeFollowup.AnisotropicVarianceRestartCell
public import QuantitativePaper.VectorFourierTests

@[expose] public section

/-! Actual elapsed-time Gaussian transition kernels of the restarted
anisotropic diffusion. Zero-width cells are identity kernels; remaining
cells are identified from their true backward Itô pairing and Fourier law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def anisotropicRestartElapsed (s : RSBScheme k) (q : Paper.Overlap) (i : ℕ) : ℝ≥0 :=
  (max (q:ℝ) (s.q i)-(q:ℝ)).toNNReal

def anisotropicFiniteRestartJointState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (i : ℕ)
    (sample : VectorDisorderBrownianSample n) : VectorState n :=
  (sample.1,anisotropicFiniteRestartState D s g q x (anisotropicRestartElapsed s q i) sample)

theorem adapted_anisotropicFiniteRestartJointState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (i : ℕ) :
    Measurable[vectorBrownianFiltration n (anisotropicRestartElapsed s q i)]
      (anisotropicFiniteRestartJointState D s g q x i) :=
  (stronglyMeasurable_initialVectorDisorder n _).measurable.prodMk
    (stronglyAdapted_anisotropicFiniteRestartState D s g q x _).measurable

theorem measurable_anisotropicFiniteRestartJointState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (i : ℕ) :
    Measurable (anisotropicFiniteRestartJointState D s g q x i) :=
  (adapted_anisotropicFiniteRestartJointState D s g q x i).mono ((vectorBrownianFiltration n).le _) le_rfl

def anisotropicFiniteRestartKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (i : ℕ) : Kernel (VectorState n) (VectorState n) :=
  anisotropicWhitenedFiniteKernel D (vectorClampedScheme s q q.property) g (i+1)

instance anisotropicFiniteRestartKernel_markov (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (i : ℕ) :
    IsMarkovKernel (anisotropicFiniteRestartKernel D s g q i) := by
  unfold anisotropicFiniteRestartKernel
  infer_instance

theorem anisotropicFiniteRestartKernel_response (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (i : ℕ) (hi : i≤k+1)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G) (z : VectorState n) :
    (∫y,G y∂anisotropicFiniteRestartKernel D s g q i z)=
      vectorJointResponse (anisotropicWhitenedFiniteJointPotential D (vectorClampedScheme s q q.property)
        (k+1-i) g) G (max (q:ℝ) (s.q (i+1))-max (q:ℝ) (s.q i)) (s.m i) z := by
  have he:=anisotropicWhitenedFiniteKernel_jointResponse D (vectorClampedScheme s q q.property) g (i+1) hG z
  have hidx : k+1+1-(i+1)=k+1-i:=by omega
  simpa only [anisotropicFiniteRestartKernel,hidx,
    vectorClampedScheme_overlap_succ,vectorClampedScheme_mass_succ] using he

theorem anisotropicFiniteRestart_kernel_backward_pairing (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (i : ℕ) (hi : i≤k+1) {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (anisotropicRestartElapsed s q i)] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(G (anisotropicFiniteRestartJointState D s g q x (i+1) sample)-
      ∫y,G y∂anisotropicFiniteRestartKernel D s g q i (anisotropicFiniteRestartJointState D s g q x i sample)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*(G (anisotropicFiniteRestartJointState D s g q x (i+1) sample)-
      ∫y,G y∂anisotropicFiniteRestartKernel D s g q i (anisotropicFiniteRestartJointState D s g q x i sample))
      ∂vectorDisorderBrownianMeasure n)=0 := by
  by_cases hsmall : s.q (i+1)≤(q:ℝ)
  · have hsmall0 : s.q i≤(q:ℝ):=(s.q_mono i (by omega)).trans hsmall
    have he (sample : VectorDisorderBrownianSample n) :
        G (anisotropicFiniteRestartJointState D s g q x (i+1) sample)-
          ∫y,G y∂anisotropicFiniteRestartKernel D s g q i
            (anisotropicFiniteRestartJointState D s g q x i sample)=0 := by
      rw [anisotropicFiniteRestartKernel_response D s g q i hi hG]
      simp only [anisotropicFiniteRestartJointState,anisotropicRestartElapsed,max_eq_left hsmall,
        max_eq_left hsmall0,sub_self,Real.toNNReal_zero,anisotropicFiniteRestartState_zero,
        vectorJointResponse,vectorStepResponse_zero]
    have hz : (fun sample=>Z sample*(G (anisotropicFiniteRestartJointState D s g q x (i+1) sample)-
      ∫y,G y∂anisotropicFiniteRestartKernel D s g q i
        (anisotropicFiniteRestartJointState D s g q x i sample)))=(fun _=>0) := by
      funext sample
      rw [he,mul_zero]
    rw [hz]
    exact ⟨integrable_const 0,by simp⟩
  · have hlarge : (q:ℝ)<s.q (i+1):=lt_of_not_ge hsmall
    let v : ℝ:=max (q:ℝ) (s.q i)
    have hv : v∈Icc (s.q i) (s.q (i+1)):=
      ⟨le_max_right _ _,max_le hlarge.le (s.q_mono i (by omega))⟩
    have hqv : (q:ℝ)≤v:=le_max_left _ _
    have hh:=anisotropicFiniteRestart_cell_backward_pairing D s g q x i hi v hv hqv hG Z hZ C hC
    have hF : anisotropicWhitenedFiniteJointPotential D (vectorClampedScheme s q q.property)
        (k+1-i) g=anisotropicWhitenedFiniteJointPotential D s (k+1-i) g := by
      funext p
      unfold anisotropicWhitenedFiniteJointPotential
      rw [←anisotropicTailRecursion_eq_clamped D s q q.property (by omega),
        anisotropicTailRecursion_prefix_of_le D s q (by omega)
          (by simpa only [show k+2-(k+1-i)=i+1 from by omega] using hlarge.le)]
    simpa only [anisotropicFiniteRestartKernel_response D s g q i hi hG,hF,
      anisotropicFiniteRestartJointState,anisotropicRestartElapsed,max_eq_right hlarge.le,v] using hh

theorem anisotropicFiniteRestart_restricted_transition_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (i : ℕ) (hi : i≤k+1) (A : Set (VectorDisorderBrownianSample n))
    (hA : MeasurableSet[vectorBrownianFiltration n (anisotropicRestartElapsed s q i)] A) :
    ((vectorDisorderBrownianMeasure n).restrict A).map (anisotropicFiniteRestartJointState D s g q x (i+1))=
      (anisotropicFiniteRestartKernel D s g q i) ∘ₘ
        ((vectorDisorderBrownianMeasure n).restrict A).map (anisotropicFiniteRestartJointState D s g q x i) := by
  apply restricted_transitionLaw_of_weighted_fourier
    (vectorBrownianFiltration n (anisotropicRestartElapsed s q i)) (vectorDisorderBrownianMeasure n)
    ((vectorBrownianFiltration n).le _) _ _ (measurable_anisotropicFiniteRestartJointState D s g q x _)
    (measurable_anisotropicFiniteRestartJointState D s g q x _) (anisotropicFiniteRestartKernel D s g q i)
    ?_ ?_ A hA
  · intro L Z hZ hC
    have hh:=anisotropicFiniteRestart_kernel_backward_pairing D s g q x i hi (vectorCosineTestData L)
      Z hZ 1 (by simpa only [NNReal.coe_one] using hC)
    have hZm:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
    have hleft : Integrable (fun sample=>Z sample*Real.cos
        (L (anisotropicFiniteRestartJointState D s g q x (i+1) sample)))
          (vectorDisorderBrownianMeasure n) :=
      (integrable_const (1:ℝ)).mono'
        (hZm.mul (Real.measurable_cos.comp (L.continuous.measurable.comp
          (measurable_anisotropicFiniteRestartJointState D s g q x _)))).aestronglyMeasurable
        (.of_forall fun sample=>by
          simp only [norm_mul,Real.norm_eq_abs]
          have hz : |Z sample|≤1 := by simpa only [Real.norm_eq_abs] using hC sample
          exact (mul_le_mul hz (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)).trans_eq (by simp))
    have hright:=hleft.sub hh.1
    have hright' : Integrable (fun sample=>Z sample*∫y,Real.cos (L y)∂
        anisotropicFiniteRestartKernel D s g q i (anisotropicFiniteRestartJointState D s g q x i sample))
          (vectorDisorderBrownianMeasure n) := by
      convert hright using 1
      ext sample
      simp only [Pi.sub_apply]
      ring
    have he:=hh.2
    simp_rw [mul_sub] at he
    rw [integral_sub hleft hright'] at he
    exact sub_eq_zero.mp he
  · intro L Z hZ hC
    have hh:=anisotropicFiniteRestart_kernel_backward_pairing D s g q x i hi (vectorSineTestData L)
      Z hZ 1 (by simpa only [NNReal.coe_one] using hC)
    have hZm:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
    have hleft : Integrable (fun sample=>Z sample*Real.sin
        (L (anisotropicFiniteRestartJointState D s g q x (i+1) sample)))
          (vectorDisorderBrownianMeasure n) :=
      (integrable_const (1:ℝ)).mono'
        (hZm.mul (Real.measurable_sin.comp (L.continuous.measurable.comp
          (measurable_anisotropicFiniteRestartJointState D s g q x _)))).aestronglyMeasurable
        (.of_forall fun sample=>by
          simp only [norm_mul,Real.norm_eq_abs]
          have hz : |Z sample|≤1 := by simpa only [Real.norm_eq_abs] using hC sample
          exact (mul_le_mul hz (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)).trans_eq (by simp))
    have hright:=hleft.sub hh.1
    have hright' : Integrable (fun sample=>Z sample*∫y,Real.sin (L y)∂
        anisotropicFiniteRestartKernel D s g q i (anisotropicFiniteRestartJointState D s g q x i sample))
          (vectorDisorderBrownianMeasure n) := by
      convert hright using 1
      ext sample
      simp only [Pi.sub_apply]
      ring
    have he:=hh.2
    simp_rw [mul_sub] at he
    rw [integral_sub hleft hright'] at he
    exact sub_eq_zero.mp he

end QuantitativeFollowup
