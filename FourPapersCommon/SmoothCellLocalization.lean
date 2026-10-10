module
public import FourPapersCommon.SmoothCutoffJetBounds

@[expose] public section

/-! Actual compact smooth localization of a function smooth only on an
open time cell. Time is localized separately from the growing spatial ball. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [HasContDiffBump E]

def cellLocalizedFunction (ρ : ℝ→ℝ) (j : ℕ) (f : ℝ×E→ℝ) : ℝ×E→ℝ :=
  fun w=>ρ w.1*expandingSmoothCutoff j w.2*f w

theorem contDiff_cellLocalizedFunction (ρ : ℝ→ℝ) (j : ℕ) (f : ℝ×E→ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hρ : ContDiff ℝ ∞ ρ)
    (hs : tsupport ρ⊆U) (hf : ContDiffOn ℝ ∞ f (Prod.fst ⁻¹' U)) :
    ContDiff ℝ ∞ (cellLocalizedFunction ρ j f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro w
  by_cases hw : w.1∈U
  · have hfAt := (hf w hw).contDiffAt ((hU.preimage continuous_fst).mem_nhds hw)
    exact ((hρ.comp contDiff_fst).contDiffAt.mul
      ((contDiff_expandingSmoothCutoff j).comp contDiff_snd).contDiffAt).mul hfAt
  · have hnot : w.1∉tsupport ρ:=fun h=>hw (hs h)
    have hz : ρ=ᶠ[𝓝 w.1] (fun _=>0):=notMem_tsupport_iff_eventuallyEq.mp hnot
    apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hz.comp_tendsto continuous_fst.continuousAt] with v hv
    dsimp only [Function.comp_def] at hv
    simp only [cellLocalizedFunction,hv,zero_mul]

theorem hasCompactSupport_cellLocalizedFunction (ρ : ℝ→ℝ) (j : ℕ) (f : ℝ×E→ℝ)
    (hρ : HasCompactSupport ρ) : HasCompactSupport (cellLocalizedFunction ρ j f) := by
  apply HasCompactSupport.intro (hρ.prod (hasCompactSupport_expandingSmoothCutoff (E:=E) j))
  intro w hw
  by_cases ht : w.1∈tsupport ρ
  · have hx : w.2∉tsupport (expandingSmoothCutoff (E:=E) j):=fun hx=>hw ⟨ht,hx⟩
    have hz:=Function.notMem_support.mp (fun h=>hx (subset_tsupport _ h))
    simp only [cellLocalizedFunction,hz,mul_zero,zero_mul]
  · have hz:=Function.notMem_support.mp (fun h=>ht (subset_tsupport _ h))
    simp only [cellLocalizedFunction,hz,zero_mul]

theorem cellLocalizedFunction_eventually_eq (ρ : ℝ→ℝ) (f : ℝ×E→ℝ)
    (q : ℝ) (x : E) (hρ : ρ=ᶠ[𝓝 q] (fun _=>1)) :
    ∀ᶠj : ℕ in atTop,cellLocalizedFunction ρ j f=ᶠ[𝓝 (q,x)]f := by
  filter_upwards [expandingSmoothCutoff_eventually_one x] with j hj
  filter_upwards [hρ.comp_tendsto continuous_fst.continuousAt,
    hj.comp_tendsto continuous_snd.continuousAt] with w hw hx
  dsimp only [Function.comp_def] at hw hx
  simp only [cellLocalizedFunction,hw,hx,one_mul]

theorem cellLocalizedFunction_eventually_derivative_eq (ρ : ℝ→ℝ) (f : ℝ×E→ℝ)
    (q : ℝ) (x : E) (hρ : ρ=ᶠ[𝓝 q] (fun _=>1)) (r : ℕ) :
    ∀ᶠj : ℕ in atTop,iteratedFDeriv ℝ r (cellLocalizedFunction ρ j f) (q,x)=
      iteratedFDeriv ℝ r f (q,x) := by
  filter_upwards [cellLocalizedFunction_eventually_eq ρ f q x hρ] with j hj
  exact (hj.iteratedFDeriv ℝ r).self_of_nhds

theorem exists_cellTimeCutoff (l a b u : ℝ) (hla : l<a) (hab : a≤b) (hbu : b<u) :
    ∃ρ : ℝ→ℝ,ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ⊆Ioo l u ∧
      (∀q,ρ q∈Icc (0:ℝ) 1) ∧ (∀q∈Icc a b,ρ=ᶠ[𝓝 q] (fun _=>1)) := by
  let ε:=min (a-l) (u-b)/4
  have hε : 0<ε:=div_pos (lt_min (sub_pos.mpr hla) (sub_pos.mpr hbu)) (by norm_num)
  have hεa : 4*ε≤a-l:=by dsimp [ε];linarith [min_le_left (a-l) (u-b)]
  have hεb : 4*ε≤u-b:=by dsimp [ε];linarith [min_le_right (a-l) (u-b)]
  let c:=(a+b)/2
  let B : ContDiffBump c := {
    rIn := (b-a)/2+ε
    rOut := (b-a)/2+2*ε
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  refine ⟨B,B.contDiff,B.hasCompactSupport,?_,fun q=>⟨B.nonneg,B.le_one⟩,?_⟩
  · intro q hq
    rw [B.tsupport_eq] at hq
    have ha:=abs_le.mp (show |q-c|≤(b-a)/2+2*ε from by
      simpa only [Metric.mem_closedBall,Real.dist_eq,B] using hq)
    dsimp [c] at ha
    constructor <;> linarith
  · intro q hq
    apply B.eventuallyEq_one_of_mem_ball
    rw [Metric.mem_ball,Real.dist_eq]
    change |q-c|<(b-a)/2+ε
    apply abs_lt.mpr
    dsimp [c]
    constructor <;> linarith [hq.1,hq.2]

end FourPapersCommon
