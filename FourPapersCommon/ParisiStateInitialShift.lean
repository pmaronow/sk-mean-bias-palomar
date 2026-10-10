module
public import Paper.ParisiRestartState

@[expose] public section

/-! Joint measurability in initial state and noise for the actual scalar
Picard solution, obtained by moving the initial state into additive noise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 900000

def parisiInitialShiftNoise (β x : ℝ) (W : C(Paper.Overlap,ℝ)) : C(Paper.Overlap,ℝ) where
  toFun t := W t+x/β
  continuous_toFun := W.continuous.add continuous_const

theorem measurable_parisiInitialShiftNoise (β : ℝ) :
    Measurable (fun z : ℝ×C(Paper.Overlap,ℝ)=>parisiInitialShiftNoise β z.1 z.2) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  have he : Measurable (fun W : C(Paper.Overlap,ℝ)=>W t) :=
    (ProbabilityTheory.ContinuousMap.measurable_iff_eval
      (fun W : C(Paper.Overlap,ℝ)=>W)).mp measurable_id t
  exact (he.comp measurable_snd).add (measurable_fst.div_const β)

theorem parisiStatePath_initial_shift (β : ℝ) (hβ : β≠0) (x : ℝ)
    (μ : ParisiMeasure) (v : ℝ→ℝ→ℝ) (hv : Continuous (Function.uncurry v))
    (hv1 : ∀t y,‖v t y‖≤1) (hvL : ∀t,LipschitzWith 1 (v t))
    (W : C(Paper.Overlap,ℝ)) :
    parisiStatePath β x μ v hv hv1 hvL 1 zero_le_one W=
      parisiStatePath β 0 μ v hv hv1 hvL 1 zero_le_one (parisiInitialShiftNoise β x W) := by
  let N:=parisiNoiseExtension zero_le_one W
  let Z:=parisiNoiseExtension zero_le_one (parisiInitialShiftNoise β x W)
  have hN : Continuous N := continuous_parisiNoiseExtension zero_le_one W
  have hZ : Continuous Z := continuous_parisiNoiseExtension zero_le_one _
  let X:=parisiStateReal β x μ v hv hv1 hvL 1 zero_le_one N hN
  have he:=parisiStateReal_unique β 0 μ v hv hv1 hvL 1 zero_le_one Z hZ X
    (continuous_parisiStateReal β x μ v hv hv1 hvL 1 zero_le_one N hN) (by
      intro t ht
      have hi:=parisiStateReal_integral_equation β x μ v hv hv1 hvL 1 zero_le_one N hN ht
      change X t=x+β*N t+_ at hi
      have hn : Z t=N t+x/β := rfl
      rw [hn]
      rw [hi]
      field_simp
      <;> ring)
  ext t
  simp only [parisiStatePath_apply]
  exact he t.property

theorem measurable_parisiStatePath_initial_noise (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (v : ℝ→ℝ→ℝ) (hv : Continuous (Function.uncurry v))
    (hv1 : ∀t y,‖v t y‖≤1) (hvL : ∀t,LipschitzWith 1 (v t)) :
    Measurable (fun z : ℝ×C(Paper.Overlap,ℝ)=>
      parisiStatePath β z.1 μ v hv hv1 hvL 1 zero_le_one z.2) := by
  have hm:=(measurable_parisiStatePath β 0 μ v hv hv1 hvL 1 zero_le_one).comp
    (measurable_parisiInitialShiftNoise β)
  convert hm using 1
  funext z
  exact parisiStatePath_initial_shift β hβ z.1 μ v hv hv1 hvL z.2

end FourPapersCommon
