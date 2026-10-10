module
public import QuantitativeFollowup.AnisotropicPairConditionalLimit

@[expose] public section

/-! Actual single-spin posterior responses and their terminal Gibbs moments. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 800000

def anisotropicFiniteTailSpinResponse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) : ℝ :=
  anisotropicFiniteTailMagnetization D s q P i

def anisotropicProcessSpinResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (i : Fin n) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  anisotropicProcessMagnetization D μ q sample i

theorem anisotropicFiniteTailSpinResponse_node (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (hj : j≤k+2) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicFiniteTailSpinResponse D s (anisotropicSchemeNode s j hj) P i=
      ∫σ,Paper.spinSign (σ i) ∂anisotropicFiniteSpinKernel D s (k+2-j) P := by
  rw [anisotropicFiniteTailSpinResponse,anisotropicFiniteTailMagnetization_node,
    anisotropicMagnetization_eq_spin_mean]

theorem anisotropicFiniteTailSpinResponse_one (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicFiniteTailSpinResponse D s 1 P i=anisotropicTerminalFeatureMean D (fun σ=>Paper.spinSign (σ i)) P := by
  have hn : anisotropicSchemeNode s (k+2) le_rfl=(1 : Paper.Overlap) := Subtype.ext s.q_top
  rw [←hn,anisotropicFiniteTailSpinResponse_node,Nat.sub_self,anisotropicFiniteSpinKernel_zero_eq_terminalKernel]
  rfl

theorem anisotropicFiniteTailSpinResponse_bound (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    ‖anisotropicFiniteTailSpinResponse D s q P i‖≤1 :=
  anisotropicFiniteTailMagnetization_component_bound D s q P i

theorem anisotropicProcessSpinResponse_bound (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (i : Fin n) (sample : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicProcessSpinResponse D μ q i sample‖≤1 :=
  anisotropicMeasureTailMagnetization_component_bound D μ q _ i

theorem measurable_anisotropicProcessSpinResponse (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (i : Fin n) : Measurable (anisotropicProcessSpinResponse D μ q i) := by
  have hm := (measurable_uncurry_anisotropicProcessMagnetization D μ).comp
    ((measurable_const (a:=q)).prodMk measurable_id)
  have h := (EuclideanSpace.proj i).continuous.measurable.comp hm
  change Measurable (fun sample=>anisotropicProcessMagnetization D μ q sample i)
  simpa only [Function.comp_def,id_eq,EuclideanSpace.proj,PiLp.proj_apply] using h

theorem tendsto_anisotropicProcessSpinResponse_moving (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (sample : AnisotropicDisorderBrownianSample n) (i : Fin n)
    {qj : ℕ→Paper.Overlap} {q : Paper.Overlap} (hq : Tendsto qj atTop (𝓝 q)) :
    Tendsto (fun j=>anisotropicFiniteTailSpinResponse D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (qj j) (anisotropicFiniteProcessParameter D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (qj j) sample) i)
      atTop (𝓝 (anisotropicProcessSpinResponse D μ q i sample)) := by
  exact (EuclideanSpace.proj i).continuous.continuousAt.tendsto.comp
    (tendsto_anisotropicFiniteProcessMagnetization_moving_time D μ sample hq)

end QuantitativeFollowup
