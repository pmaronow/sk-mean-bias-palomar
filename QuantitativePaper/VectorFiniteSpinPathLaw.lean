module
public import QuantitativePaper.VectorFiniteTiltedPathLaw
public import FourPapersCommon.CompProdComapMap

@[expose] public section

/-! The actual finite diffusion history and its terminal Gibbs spin have
the exact constructed posterior law, including every field coordinate and
the normalized fractional initial-disorder tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

def vectorFiniteSpinPathLaw (s : RSBScheme k) (β t a : ℝ) (ht : t≤1) :
    Measure (VectorDisorderBrownianSample n×Configuration n) :=
  (vectorFiniteDisorderTilt s β t a) ⊗ₘ
    ((terminalSpinKernel (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2)
      (measurable_vectorTerminalExponent_state n β t)).comap
        (vectorFiniteJointState s β t ht 1) (measurable_vectorFiniteJointState s β t ht 1))

theorem vectorFiniteSpinPathLaw_probability (s : RSBScheme k) (β t a : ℝ) (ht : t≤1) :
    IsProbabilityMeasure (vectorFiniteSpinPathLaw (n:=n) s β t a ht) := by
  haveI := vectorFiniteDisorderTilt_probability (n:=n) s β t a
  unfold vectorFiniteSpinPathLaw
  infer_instance

theorem vectorFiniteSpinPathLaw_map (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) :
    (vectorFiniteSpinPathLaw s β t a ht.le).map
      (fun p=>(vectorFiniteHistory s β t ht.le (k+2) p.1,p.2))=
      vectorJointLaw (n:=n) s β t a := by
  let H := vectorFiniteHistory (n:=n) s β t ht.le (k+2)
  let K := (terminalSpinKernel (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2)
    (measurable_vectorTerminalExponent_state n β t)).comap
      (fun history : FiniteHistory (VectorState n) (k+2)=>history (Fin.last (k+2)))
      (measurable_pi_apply _)
  have hH : Measurable H := measurable_vectorFiniteHistory s β t ht.le _
  have hker : K.comap H hH=
      ((terminalSpinKernel (fun p : VectorState n=>vectorTerminalExponent n β t p.1 p.2)
        (measurable_vectorTerminalExponent_state n β t)).comap
          (vectorFiniteJointState s β t ht.le 1) (measurable_vectorFiniteJointState s β t ht.le 1)) := by
    ext sample : 1
    change terminalLaw (vectorTerminalExponent n β t (H sample (Fin.last (k+2))).1
        (H sample (Fin.last (k+2))).2)=
      terminalLaw (vectorTerminalExponent n β t sample.1 (vectorFiniteState s β t ht.le 1 sample))
    simp only [H,vectorFiniteHistory,historySample,Fin.val_last,s.q_top,Real.toNNReal_one,
      vectorFiniteJointState]
  haveI := vectorFiniteDisorderTilt_probability (n:=n) s β t a
  have he := compProd_comap_map_history (vectorFiniteDisorderTilt s β t a) H hH K
  rw [hker,vectorFinite_tilted_full_history_law s β t a hβ ht] at he
  exact he

end QuantitativePaper
