module
public import QuantitativeFollowup.AnisotropicFiniteMeasureStateAgreement
public import QuantitativeFollowup.AnisotropicTerminalPathLaw
public import FourPapersCommon.KernelSamplingMap

@[expose] public section

/-! The whole native marked path at the original nodes of a finite scheme
has that scheme's actual chronological Markov history law. The terminal
Gibbs spin is retained; no single-node moment identification replaces this
joint law. Repeated observation nodes remain in the history. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityNativeSchemeHistory (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (sample : AnisotropicDisorderBrownianSample n) :
    FiniteHistory (AnisotropicParameter n) (k+2) :=
  fun i=>anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
    (anisotropicSchemeNode s i (by omega)) sample

theorem cavityNativeSchemeHistory_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : cavityNativeSchemeHistory D s=anisotropicFiniteWienerHistory D s (k+2) :=by
  funext sample i
  have hi : (i:ℕ)≤k+2:=by omega
  have he:=anisotropicFiniteWienerHistory_node D s sample i hi
  rw [historyExtended_fin] at he
  rw [cavityNativeSchemeHistory,anisotropicProcessParameter_scheme_eq_finite]
  exact he.symm

theorem measurable_cavityNativeSchemeHistory (D : AnisotropicSpinModel n) (s : RSBScheme k) :
    Measurable (cavityNativeSchemeHistory D s) :=by
  rw [cavityNativeSchemeHistory_eq_finite]
  exact measurable_anisotropicFiniteWienerHistory D s (k+2)

theorem cavityNativeSchemeHistory_terminal (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (sample : AnisotropicDisorderBrownianSample n) :
    cavityNativeSchemeHistory D s sample (Fin.last (k+2))=
      anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) 1 sample :=by
  have he : anisotropicSchemeNode s (k+2) le_rfl=(1:Paper.Overlap):=by
    apply Subtype.ext
    exact s.q_top
  simp only [cavityNativeSchemeHistory,Fin.val_last,he]

theorem cavityNativeSchemeHistory_law (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    (anisotropicMeasureSampleLaw D (Paper.parisiSchemeMeasure s) a).map
      (cavityNativeSchemeHistory D s)=anisotropicFiniteHistoryLaw D s a :=by
  rw [cavityNativeSchemeHistory_eq_finite,anisotropicMeasureSampleLaw_scheme_eq_finite]
  exact anisotropicFiniteWiener_history_law D s a (k+2) le_rfl

theorem cavityNativeSchemeMarkedHistory_law (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    (anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a).map
      (Prod.map (cavityNativeSchemeHistory D s) id)=anisotropicFiniteJointLaw D s a :=by
  have hs (sample : AnisotropicDisorderBrownianSample n) :
      (anisotropicMeasureTerminalKernel D (Paper.parisiSchemeMeasure s) sample).map id=
        anisotropicFiniteTerminalKernel D s (cavityNativeSchemeHistory D s sample) :=by
    rw [Measure.map_id]
    change anisotropicTerminalSpinKernel D
      (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) 1 sample)=
        anisotropicFiniteSpinKernel D s 0
          (cavityNativeSchemeHistory D s sample (Fin.last (k+2)))
    rw [anisotropicFiniteSpinKernel_zero_eq_terminalKernel,cavityNativeSchemeHistory_terminal]
  rw [anisotropicMeasureSpinPathLaw,
    map_compProd_map_pair _ _ (anisotropicFiniteTerminalKernel D s)
      (cavityNativeSchemeHistory D s) id (measurable_cavityNativeSchemeHistory D s) measurable_id hs,
    cavityNativeSchemeHistory_law]
  rfl

end QuantitativeFollowup
