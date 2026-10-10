module
public import QuantitativePaper.VectorRestartFiniteCellBackward
public import QuantitativePaper.VectorFiniteKernelPairing

@[expose] public section

/-! The genuine remaining finite-grid kernels from a fixed restart. Clamping
adds only inactive zero-variance transitions; the initial law is a Dirac state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorRestartGridElapsed (μ : Paper.ParisiMeasure) (j : ℕ) (q : Paper.Overlap)
    (i : ℕ) : ℝ≥0:=
  (max (q:ℝ) ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)-(q:ℝ)).toNNReal

def vectorRestartGridJointState (μ : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (i : ℕ)
    (sample : VectorDisorderBrownianSample n) : VectorState n:=
  (p,vectorRestartState (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht q p x
    (vectorRestartGridElapsed μ j q i) sample)

def vectorRestartGridKernel (μ : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ)
    (q : Paper.Overlap) (i : ℕ) : Kernel (VectorState n) (VectorState n):=
  vectorProfileKernel (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    q q.property) β t (i+1)

instance vectorRestartGridKernel_markov (μ : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ)
    (q : Paper.Overlap) (i : ℕ) : IsMarkovKernel (vectorRestartGridKernel (n:=n) μ j β t q i):=by
  unfold vectorRestartGridKernel
  exact vectorProfileKernel_markov _ β t _

theorem adapted_vectorRestartGridJointState (μ : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (i : ℕ) :
    Measurable[vectorBrownianFiltration n (vectorRestartGridElapsed μ j q i)]
      (vectorRestartGridJointState μ j β t ht q p x i):=
  measurable_const.prodMk (stronglyAdapted_vectorRestartState _ β t ht q p x _).measurable

theorem measurable_vectorRestartGridJointState (μ : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (i : ℕ) :
    Measurable (vectorRestartGridJointState μ j β t ht q p x i):=
  (adapted_vectorRestartGridJointState μ j β t ht q p x i).mono
    ((vectorBrownianFiltration n).le _) le_rfl

theorem vectorRestartGridKernel_response (μ : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ)
    (q : Paper.Overlap) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G) (z : VectorState n) :
    (∫y,G y∂vectorRestartGridKernel μ j β t q i z)=
      vectorStepResponse (((1-t)*β^2)*
        (max (q:ℝ) ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))-
          max (q:ℝ) ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)))
        ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).m i)
        (vectorTailRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q z.1
          (vectorDyadicIndex j+2-i)) (fun y=>G (z.1,y)) z.2 := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  have he:=vectorProfileKernel_jointResponse (vectorClampedScheme s q q.property)
    β t (i+1) (by omega) hG z
  rw [show vectorDyadicIndex j+1+1+1-(i+1)=vectorDyadicIndex j+2-i by omega] at he
  rw [vectorClampedScheme_overlap_succ,vectorClampedScheme_overlap_succ,
    vectorClampedScheme_mass_succ] at he
  dsimp only [vectorJointResponse] at he
  rw [←vectorTailRecursion_eq_clamped s β t q q.property z.1 (by omega)] at he
  exact he

theorem vectorRestartGrid_backward_identity (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (vectorRestartGridElapsed μ j q i)] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(G (vectorRestartGridJointState μ j β t ht.le q p x (i+1) sample)-
      ∫y,G y∂vectorRestartGridKernel μ j β t q i
        (vectorRestartGridJointState μ j β t ht.le q p x i sample))) (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*(G (vectorRestartGridJointState μ j β t ht.le q p x (i+1) sample)-
      ∫y,G y∂vectorRestartGridKernel μ j β t q i
        (vectorRestartGridJointState μ j β t ht.le q p x i sample))∂vectorDisorderBrownianMeasure n)=0 := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  by_cases hsmall : s.q (i+1)≤(q:ℝ)
  · have hsmall0 : s.q i≤(q:ℝ):=(s.q_mono i (by omega)).trans hsmall
    dsimp only [s] at hsmall hsmall0
    have he (sample:VectorDisorderBrownianSample n) :
        G (vectorRestartGridJointState μ j β t ht.le q p x (i+1) sample)-
          ∫y,G y∂vectorRestartGridKernel μ j β t q i
            (vectorRestartGridJointState μ j β t ht.le q p x i sample)=0:=by
      rw [vectorRestartGridKernel_response μ j β t q i hi hG]
      simp only [vectorRestartGridJointState,vectorRestartGridElapsed,
        max_eq_left hsmall,max_eq_left hsmall0,sub_self,Real.toNNReal_zero,
        mul_zero,vectorStepResponse_zero,vectorRestartState_zero]
    have hz : (fun sample=>Z sample*(G (vectorRestartGridJointState μ j β t ht.le q p x (i+1) sample)-
      ∫y,G y∂vectorRestartGridKernel μ j β t q i
        (vectorRestartGridJointState μ j β t ht.le q p x i sample)))=(fun _=>0):=by
      funext sample
      rw [he,mul_zero]
    rw [hz]
    exact ⟨integrable_const 0,by simp⟩
  · have hlarge : (q:ℝ)<s.q (i+1):=lt_of_not_ge hsmall
    let v:ℝ:=max (q:ℝ) (s.q i)
    have hv : v∈Icc (s.q i) (s.q (i+1)):=
      ⟨le_max_right _ _,max_le hlarge.le (s.q_mono i (by omega))⟩
    have hqv : (q:ℝ)≤v:=le_max_left _ _
    have hh:=vectorRestart_grid_cell_backward_identity μ j β t hβ ht q p x i hi v hv hqv hG
      Z hZ C hC
    have hprefix (y:Field n) : vectorTailRecursion s β t q p (vectorDyadicIndex j+2-i) y=
        vectorRecursion s β t p (vectorDyadicIndex j+2-i) y:=by
      rw [vectorTailRecursion_prefix_of_le s β t q p (by omega)]
      simpa only [show vectorDyadicIndex j+3-(vectorDyadicIndex j+2-i)=i+1 by omega] using hlarge.le
    have hf : vectorTailRecursion s β t q p (vectorDyadicIndex j+2-i)=
        vectorRecursion s β t p (vectorDyadicIndex j+2-i):=funext hprefix
    dsimp only [s,v] at hh hf hlarge
    simp only [vectorRestartGridKernel_response μ j β t q i hi hG,
      vectorRestartGridJointState,vectorRestartGridElapsed,Prod.fst,Prod.snd,
      max_eq_right hlarge.le,hf]
    exact hh

end QuantitativePaper
