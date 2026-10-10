module
public import QuantitativePaper.VectorDiagonalProjection
public import FourPapersCommon.CompProdComapMap

@[expose] public section

/-! Adding or removing the common diagonal completion Gaussian leaves the
actual terminal Gibbs marks unchanged. The full marked sample law is
transported exactly, retaining its diffusion sample and terminal spin. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 700000

theorem terminalLaw_add_const (E : Configuration n→ℝ) (c : ℝ) :
    terminalLaw (fun σ=>c+E σ)=terminalLaw E := by
  have hw (σ : Configuration n) : terminalWeight (fun τ=>c+E τ) σ=terminalWeight E σ := by
    unfold terminalWeight terminalPartition
    simp_rw [Real.exp_add]
    rw [←Finset.mul_sum]
    exact mul_div_mul_left _ _ (Real.exp_ne_zero c)
  apply Measure.ext_of_singleton
  intro σ
  simp only [terminalLaw,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton σ),
    terminalPMF,PMF.ofFintype_apply,hw]

theorem vectorTerminalLaw_diagonal_shift (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    terminalLaw (vectorTerminalExponent n β t p x)=
      terminalLaw (vectorTerminalExponent n β t (p.1,0) x) := by
  have he : vectorTerminalExponent n β t p x=
      fun σ=>β*Real.sqrt t*p.2+vectorTerminalExponent n β t (p.1,0) x σ := by
    funext σ
    simp only [vectorTerminalExponent,add_zero]
    ring
  rw [he,terminalLaw_add_const]

def vectorCompletedTerminalKernel (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1) :
    Kernel (VectorDisorderBrownianSample n) (Configuration n) :=
  (terminalSpinKernel (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2)
    (measurable_vectorTerminalExponent_state n β t)).comap
      (vectorMeasureJointState μ β t ht 1) (measurable_vectorMeasureJointState μ β t ht 1)

instance vectorCompletedTerminalKernel_markov (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) : IsMarkovKernel (vectorCompletedTerminalKernel (n:=n) μ β t ht) := by
  unfold vectorCompletedTerminalKernel
  infer_instance

theorem vectorCompletedTerminalKernel_removeDiagonal (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    (vectorCompletedTerminalKernel (n:=n) μ β t ht).comap
      vectorRemoveDiagonalSample measurable_vectorRemoveDiagonalSample =
      vectorCompletedTerminalKernel μ β t ht := by
  ext sample A hA
  simp only [Kernel.comap_apply,vectorCompletedTerminalKernel,vectorMeasureJointState]
  change terminalLaw (vectorTerminalExponent n β t ((sample.1.1,0))
      (vectorMeasureState μ β t ht 1 (vectorRemoveDiagonalSample sample))) A =
    terminalLaw (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample)) A
  rw [vectorMeasureState_diagonal_shift μ β t ht 1 le_rfl sample,
    vectorTerminalLaw_diagonal_shift β t sample.1]

def vectorRemoveDiagonalMarked (z : VectorDisorderBrownianSample n×Configuration n) :
    VectorDisorderBrownianSample n×Configuration n := (vectorRemoveDiagonalSample z.1,z.2)

theorem measurable_vectorRemoveDiagonalMarked : Measurable (vectorRemoveDiagonalMarked (n:=n)) :=
  (measurable_vectorRemoveDiagonalSample.comp measurable_fst).prodMk measurable_snd

theorem vectorMeasureSpinPathLaw_removeDiagonal (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    (vectorMeasureSpinPathLaw (n:=n) μ β t a ht).map vectorRemoveDiagonalMarked =
      ((vectorMeasureDisorderTilt μ β t a).map vectorRemoveDiagonalSample) ⊗ₘ
        vectorCompletedTerminalKernel μ β t ht := by
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have he := compProd_comap_map_history (vectorMeasureDisorderTilt (n:=n) μ β t a)
    vectorRemoveDiagonalSample measurable_vectorRemoveDiagonalSample
    (vectorCompletedTerminalKernel μ β t ht)
  rw [vectorCompletedTerminalKernel_removeDiagonal μ β t ht] at he
  exact he

end QuantitativePaper
