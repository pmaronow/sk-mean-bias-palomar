module
public import QuantitativeFollowup.FollowupCavityGeneratedAppendMarkBudget
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-! A selected origin may carry a fork/edge/component payload as well as
its new clock. The true kernel pushlaw retains that payload while its
actual clock projection controls the appended mark budget. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
variable {H G Q : Type*} [MeasurableSpace H] [MeasurableSpace G] [MeasurableSpace Q]
  [MeasurableSingletonClass Q] {m f : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def cavityGeneratedPayloadClockKernel (κ : Kernel H G)
    (τ : H×G→Q) : Kernel H Q := (Kernel.id×ₖκ).map τ

theorem cavityGeneratedPayloadClockKernel_apply
    (κ : Kernel H G) [IsSFiniteKernel κ]
    (τ : H×G→Q) (hτ : Measurable τ) (h : H) :
    cavityGeneratedPayloadClockKernel κ τ h=(κ h).map (fun g=>τ (h,g)) := by
  rw [cavityGeneratedPayloadClockKernel,Kernel.map_apply _ hτ,Kernel.prod_apply,
    Kernel.id_apply,Measure.dirac_prod,Measure.map_map hτ measurable_prodMk_left]
  rfl

instance cavityGeneratedPayloadClockKernel_sfinite
    (κ : Kernel H G) [IsSFiniteKernel κ] (τ : H×G→Q) :
    IsSFiniteKernel (cavityGeneratedPayloadClockKernel κ τ) := by
  unfold cavityGeneratedPayloadClockKernel
  infer_instance

theorem cavityGenerated_compProd_payload_clock_map
    (M : Measure H) [SFinite M] (κ : Kernel H G) [IsSFiniteKernel κ]
    (τ : H×G→Q) (hτ : Measurable τ) :
    (M⊗ₘκ).map (fun z=>(z.1,τ z))=M⊗ₘcavityGeneratedPayloadClockKernel κ τ := by
  ext s hs
  have hg : Measurable (fun z : H×G=>(z.1,τ z)) := measurable_fst.prodMk hτ
  rw [Measure.map_apply hg hs,Measure.compProd_apply (hs.preimage hg),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro h
  rw [cavityGeneratedPayloadClockKernel_apply κ τ hτ]
  have hτh : Measurable (fun g : G=>τ (h,g)) := hτ.comp measurable_prodMk_left
  rw [Measure.map_apply hτh (measurable_prodMk_left hs)]
  rfl

def cavityGeneratedPayloadExtendedMarks (marks : Fin m→H→Q) (τ : H×G→Q) :
    Fin (m+1)→H×G→Q := Fin.snoc (fun i z=>marks i z.1) τ

theorem cavityGeneratedPayloadExtendedMarks_measurable
    (marks : Fin m→H→Q) (hmarks : ∀i,Measurable (marks i))
    (τ : H×G→Q) (hτ : Measurable τ) (i : Fin (m+1)) :
    Measurable (cavityGeneratedPayloadExtendedMarks marks τ i) := by
  cases i using Fin.lastCases with
  | last => simpa only [cavityGeneratedPayloadExtendedMarks,Fin.snoc_last] using hτ
  | cast i => simpa only [cavityGeneratedPayloadExtendedMarks,Fin.snoc_castSucc,Function.comp_def] using
      (hmarks i).comp measurable_fst

theorem cavityGeneratedMarkBudget_payload_compProd
    (ν : Measure Q) (M : Measure H) [SFinite M]
    (κ : Kernel H G) [IsSFiniteKernel κ]
    (τ : H×G→Q) (hτ : Measurable τ)
    (marks : Fin m→H→Q) (hmarks : ∀i,Measurable (marks i))
    (idx : Fin f→Fin m) (k C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M marks C)
    (hmass : ∀ᵐh∂M,κ h univ≤k)
    (hdom : ∀ᵐh∂M,(κ h).map (fun g=>τ (h,g))≤
      k•ν+∑j : Fin f,Measure.dirac (marks (idx j) h)) :
    cavityGeneratedMarkBudget ν (M⊗ₘκ) (cavityGeneratedPayloadExtendedMarks marks τ)
      ((k+(f:ℝ≥0∞))*C) := by
  let η := cavityGeneratedPayloadClockKernel κ τ
  have hm : ∀ᵐh∂M,η h univ≤k := by
    filter_upwards [hmass] with h hh
    change cavityGeneratedPayloadClockKernel κ τ h univ≤k
    rw [cavityGeneratedPayloadClockKernel_apply κ τ hτ]
    have hτh : Measurable (fun g : G=>τ (h,g)) := hτ.comp measurable_prodMk_left
    rw [Measure.map_apply hτh MeasurableSet.univ,preimage_univ]
    exact hh
  have hd : ∀ᵐh∂M,η h≤k•ν+∑j : Fin f,Measure.dirac (marks (idx j) h) := by
    simpa only [η,cavityGeneratedPayloadClockKernel_apply κ τ hτ] using hdom
  have hB := cavityGeneratedMarkBudget_compProd ν M η marks hmarks idx k C hM hm hd
  have he := cavityGenerated_compProd_payload_clock_map M κ τ hτ
  have hg : Measurable (fun z : H×G=>(z.1,τ z)) := measurable_fst.prodMk hτ
  refine ⟨?_,?_⟩
  · have hh := hB.1
    rw [←he,Measure.map_apply hg MeasurableSet.univ,preimage_univ] at hh
    exact hh
  · intro i
    have hh := hB.2 i
    rw [←he,Measure.map_map (cavityGeneratedExtendedMarks_measurable marks hmarks i) hg] at hh
    have hi : cavityGeneratedExtendedMarks marks i∘(fun z : H×G=>(z.1,τ z))=
        cavityGeneratedPayloadExtendedMarks marks τ i := by
      funext z
      cases i using Fin.lastCases <;>
        simp only [Function.comp_apply,cavityGeneratedExtendedMarks,cavityGeneratedPayloadExtendedMarks,
          Fin.snoc_last,Fin.snoc_castSucc]
    simpa only [hi] using hh

theorem cavityGeneratedMarkBudget_kernel_payload_append
    (ν : Measure Q) (M : Measure (CavityGeneratedHistory Q m)) [SFinite M]
    (κ : Kernel (CavityGeneratedHistory Q m) G) [IsSFiniteKernel κ]
    (τ : CavityGeneratedHistory Q m×G→Q) (hτ : Measurable τ)
    (idx : Fin f→Fin m) (k C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks C)
    (hmass : ∀ᵐh∂M,κ h univ≤k)
    (hdom : ∀ᵐh∂M,(κ h).map (fun g=>τ (h,g))≤
      k•ν+∑j : Fin f,Measure.dirac (h (idx j))) :
    cavityGeneratedMarkBudget ν ((M⊗ₘκ).map (fun z=>Fin.snoc z.1 (τ z)))
      cavityGeneratedHistoryMarks ((k+(f:ℝ≥0∞))*C) := by
  have hB := cavityGeneratedMarkBudget_payload_compProd ν M κ τ hτ cavityGeneratedHistoryMarks
    cavityGeneratedHistoryMarks_measurable idx k C hM hmass hdom
  have hg : Measurable (fun z : CavityGeneratedHistory Q m×G=>(Fin.snoc z.1 (τ z) : CavityGeneratedHistory Q (m+1))) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hτ
    | cast i => simpa only [Fin.snoc_castSucc,Function.comp_def] using (measurable_pi_apply i).comp measurable_fst
  apply cavityGeneratedMarkBudget_map ν _ _ _ cavityGeneratedHistoryMarks_measurable _ hB _ hg
  intro i
  funext z
  cases i using Fin.lastCases <;>
    simp only [Function.comp_apply,cavityGeneratedHistoryMarks,cavityGeneratedPayloadExtendedMarks,
      Fin.snoc_last,Fin.snoc_castSucc]

end QuantitativeFollowup
