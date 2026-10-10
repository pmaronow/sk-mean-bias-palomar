module
public import QuantitativeFollowup.AnisotropicWhitenedFiniteState
public import QuantitativeFollowup.AnisotropicFiniteJointResponseData
public import QuantitativePaper.VectorFiniteKernelPairing
public import QuantitativePaper.VectorFourierTests

@[expose] public section

/-! Genuine whole-past Gaussian transition laws of the finite anisotropic
diffusion, conditional on fixed physical disorder. The proof instantiates
the actual backward Itô identity and Fourier uniqueness, including repeated
levels and zero mass, rather than assuming the desired transition law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def anisotropicWhitenedFiniteJointState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : VectorState n :=
  (sample.1,anisotropicWhitenedFiniteState D s g r sample)

theorem measurable_anisotropicWhitenedFiniteJointState (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (r : ℝ≥0) :
    Measurable (anisotropicWhitenedFiniteJointState D s g r) :=
  measurable_fst.prodMk (measurable_vectorAdditiveState _ _ _ _ _)

def anisotropicWhitenedFiniteKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (i : ℕ) : Kernel (VectorState n) (VectorState n) :=
  vectorStateKernel (s.q (i+1)-s.q i) (s.m i)
    (fun _ : Couplings n×ℝ=>anisotropicWhitenedFinitePotential D s (k+1-i) g)

theorem measurable_anisotropicWhitenedFiniteJointPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (j : ℕ) :
    Measurable (anisotropicWhitenedFiniteJointPotential D s j g) :=
  (anisotropicWhitenedFiniteJointPotential_smooth_bounded_jets D s 3 j g).1.continuous.measurable

instance anisotropicWhitenedFiniteKernel_markov (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) :
    IsMarkovKernel (anisotropicWhitenedFiniteKernel D s g i) :=
  isMarkovKernel_vectorStateKernel _ (measurable_anisotropicWhitenedFiniteJointPotential D s g _)
    (‖anisotropicEnergyMap D‖₊*‖anisotropicWhiteJointInput D‖₊)
    (fun p=>lipschitzWith_fieldSlice (anisotropicWhitenedFiniteJointPotential_lipschitz D s _ g) p) _ _

theorem anisotropicWhitenedFinite_cell_backward_pairing (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i ≤ k+1)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C) :
    Integrable (fun sample=>Z sample*(G (anisotropicWhitenedFiniteJointState D s g (s.q (i+1)).toNNReal sample)-
      vectorJointResponse (anisotropicWhitenedFiniteJointPotential D s (k+1-i) g) G
        (s.q (i+1)-s.q i) (s.m i)
        (anisotropicWhitenedFiniteJointState D s g (s.q i).toNNReal sample)))
      (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*(G (anisotropicWhitenedFiniteJointState D s g (s.q (i+1)).toNNReal sample)-
      vectorJointResponse (anisotropicWhitenedFiniteJointPotential D s (k+1-i) g) G
        (s.q (i+1)-s.q i) (s.m i)
        (anisotropicWhitenedFiniteJointState D s g (s.q i).toNNReal sample))
      ∂vectorDisorderBrownianMeasure n)=0 := by
  let a := (s.q i).toNNReal
  let Q := (s.q (i+1)).toNNReal
  have ha : (a : ℝ)=s.q i := Real.coe_toNNReal _ (s.q_nonneg (by omega))
  have hQ : (Q : ℝ)=s.q (i+1) := Real.coe_toNNReal _ (s.q_nonneg (by omega))
  have haQ : a ≤ Q := by
    apply NNReal.coe_le_coe.mp
    rw [ha,hQ]
    exact s.q_mono i (by omega)
  have hh := vector_jointResponse_endpoint_martingale_past
    (anisotropicWhitenedFiniteJointResponseData D s (k+1-i) g hG)
    (vectorItoCharacteristics_anisotropicWhitenedFiniteState D s g)
    (by norm_num : (1 : ℝ)^2=1) (by norm_num : (0 : ℝ)<1) a Q haQ
    (fun r hr sample=>by
      have hr' : (r : ℝ)∈Ioo (s.q i) (s.q (i+1)) := by rw [←ha,←hQ];exact hr
      simpa only [one_smul,one_mul,hQ,anisotropicWhitenedFiniteJointPotential_apply] using
        anisotropicWhitenedFinite_actual_cell_drift D s g i hi r hr' sample)
    Z hZ C hC
  simpa only [ha,hQ,one_mul,anisotropicWhitenedFiniteJointState] using hh

theorem anisotropicWhitenedFiniteKernel_jointResponse (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G) (x : VectorState n) :
    (∫y,G y ∂anisotropicWhitenedFiniteKernel D s g i x)=
      vectorJointResponse (anisotropicWhitenedFiniteJointPotential D s (k+1-i) g) G
        (s.q (i+1)-s.q i) (s.m i) x := by
  change (∫y,G y ∂vectorStateKernel (s.q (i+1)-s.q i) (s.m i)
    (fun p x=>anisotropicWhitenedFiniteJointPotential D s (k+1-i) g (p,x)) x)=_
  rw [integral_vectorStateKernel_response _
    (measurable_anisotropicWhitenedFiniteJointPotential D s g _)
    (‖anisotropicEnergyMap D‖₊*‖anisotropicWhiteJointInput D‖₊)
    (fun p=>lipschitzWith_fieldSlice (anisotropicWhitenedFiniteJointPotential_lipschitz D s _ g) p)
    _ hG.regularity.continuous.measurable]
  rfl

theorem anisotropicWhitenedFinite_cell_kernel_pairing (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i ≤ k+1)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C) :
    (∫sample,Z sample*G (anisotropicWhitenedFiniteJointState D s g (s.q (i+1)).toNNReal sample)
      ∂vectorDisorderBrownianMeasure n)=
    ∫sample,Z sample*(∫y,G y ∂anisotropicWhitenedFiniteKernel D s g i
      (anisotropicWhitenedFiniteJointState D s g (s.q i).toNNReal sample))
      ∂vectorDisorderBrownianMeasure n := by
  have hmZ := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hg : Measurable G := hG.regularity.continuous.measurable
  have hb : ∀y,‖G y‖ ≤ hG.bounds 0 := fun y=>by simpa only [norm_iteratedFDeriv_zero] using hG.jets 0 (by omega) y
  have hi1 : Integrable (fun sample=>Z sample*G
      (anisotropicWhitenedFiniteJointState D s g (s.q (i+1)).toNNReal sample))
      (vectorDisorderBrownianMeasure n) :=
    (integrable_const ((C : ℝ)*hG.bounds 0)).mono'
      (hmZ.mul (hg.comp (measurable_anisotropicWhitenedFiniteJointState D s g _))).aestronglyMeasurable
      (.of_forall fun sample=>by rw [norm_mul];exact mul_le_mul (hC sample) (hb _) (norm_nonneg _) C.coe_nonneg)
  have hk := stronglyMeasurable_kernelObservable (anisotropicWhitenedFiniteKernel D s g i) G hg
  have hi2 : Integrable (fun sample=>Z sample*(∫y,G y ∂anisotropicWhitenedFiniteKernel D s g i
      (anisotropicWhitenedFiniteJointState D s g (s.q i).toNNReal sample)))
      (vectorDisorderBrownianMeasure n) :=
    (integrable_const ((C : ℝ)*hG.bounds 0)).mono'
      (hmZ.mul (hk.measurable.comp (measurable_anisotropicWhitenedFiniteJointState D s g _))).aestronglyMeasurable
      (.of_forall fun sample=>by
        rw [norm_mul]
        have hb' : ‖∫y,G y ∂anisotropicWhitenedFiniteKernel D s g i
            (anisotropicWhitenedFiniteJointState D s g (s.q i).toNNReal sample)‖ ≤ hG.bounds 0 := by
          simpa using (norm_integral_le_of_norm_le_const
            (μ := anisotropicWhitenedFiniteKernel D s g i
              (anisotropicWhitenedFiniteJointState D s g (s.q i).toNNReal sample))
            (Filter.Eventually.of_forall hb))
        exact mul_le_mul (hC sample) hb' (norm_nonneg _) C.coe_nonneg)
  have he := (anisotropicWhitenedFinite_cell_backward_pairing D s g i hi hG Z hZ C hC).2
  simp_rw [←anisotropicWhitenedFiniteKernel_jointResponse D s g i hG] at he
  simp_rw [mul_sub] at he
  rw [integral_sub hi1 hi2] at he
  exact sub_eq_zero.mp he

theorem anisotropicWhitenedFinite_restricted_transition_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i ≤ k+1)
    (A : Set (VectorDisorderBrownianSample n))
    (hA : MeasurableSet[vectorBrownianFiltration n (s.q i).toNNReal] A) :
    ((vectorDisorderBrownianMeasure n).restrict A).map
      (anisotropicWhitenedFiniteJointState D s g (s.q (i+1)).toNNReal)=
      (anisotropicWhitenedFiniteKernel D s g i) ∘ₘ
        ((vectorDisorderBrownianMeasure n).restrict A).map
          (anisotropicWhitenedFiniteJointState D s g (s.q i).toNNReal) := by
  apply restricted_transitionLaw_of_weighted_fourier
    (vectorBrownianFiltration n (s.q i).toNNReal) (vectorDisorderBrownianMeasure n)
    ((vectorBrownianFiltration n).le _) _ _
    (measurable_anisotropicWhitenedFiniteJointState D s g _)
    (measurable_anisotropicWhitenedFiniteJointState D s g _) (anisotropicWhitenedFiniteKernel D s g i)
    ?_ ?_ A hA
  · intro L Z hZ hZb
    exact anisotropicWhitenedFinite_cell_kernel_pairing D s g i hi (vectorCosineTestData L)
      Z hZ 1 (by simpa only [NNReal.coe_one] using hZb)
  · intro L Z hZ hZb
    exact anisotropicWhitenedFinite_cell_kernel_pairing D s g i hi (vectorSineTestData L)
      Z hZ 1 (by simpa only [NNReal.coe_one] using hZb)

end QuantitativeFollowup
