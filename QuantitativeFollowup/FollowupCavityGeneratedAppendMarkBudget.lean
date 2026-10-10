module
public import QuantitativeFollowup.FollowupCavityGeneratedMarkProgramBudget
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-! Appending a clock chosen by an actual history-dependent kernel.
The kernel's total mass and its domination by fresh mass and genuine
inherited mark indices imply the complete extended-history budget.
The source receiver supplies those kernel estimates and fork indices. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
variable {H Q : Type*} [MeasurableSpace H] [MeasurableSpace Q]
  [MeasurableSingletonClass Q] {m f : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem cavityGenerated_compProd_mass_le
    (M : Measure H) [SFinite M] (κ : Kernel H Q) [IsSFiniteKernel κ]
    (k C : ℝ≥0∞) (hM : M univ≤C)
    (hmass : ∀ᵐh∂M,κ h univ≤k) : (M⊗ₘκ) univ≤k*C := by
  rw [Measure.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  exact (lintegral_mono_ae hmass).trans
    (by simpa only [lintegral_const,mul_comm] using mul_le_mul_left hM k)

theorem cavityGenerated_compProd_fst_le
    (M : Measure H) [SFinite M] (κ : Kernel H Q) [IsSFiniteKernel κ]
    (k : ℝ≥0∞) (hmass : ∀ᵐh∂M,κ h univ≤k) :
    (M⊗ₘκ).map Prod.fst≤k•M := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply measurable_fst hs]
  have he : (Prod.fst⁻¹' s : Set (H×Q))=s×ˢuniv := by ext z; simp
  rw [he,Measure.compProd_apply_prod hs MeasurableSet.univ]
  exact (lintegral_mono_ae (ae_restrict_of_ae hmass)).trans_eq
    (by simp only [lintegral_const,Measure.restrict_apply_univ,Measure.smul_apply,smul_eq_mul])

theorem cavityGenerated_compProd_snd_le
    (ν : Measure Q) (M : Measure H) [SFinite M]
    (κ : Kernel H Q) [IsSFiniteKernel κ]
    (marks : Fin m→H→Q) (hmarks : ∀i,Measurable (marks i))
    (idx : Fin f→Fin m) (k C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M marks C)
    (hdom : ∀ᵐh∂M,κ h≤k•ν+∑j : Fin f,Measure.dirac (marks (idx j) h)) :
    (M⊗ₘκ).map Prod.snd≤((k+(f:ℝ≥0∞))*C)•ν := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply measurable_snd hs]
  have he : (Prod.snd⁻¹' s : Set (H×Q))=univ×ˢs := by ext z; simp
  rw [he,Measure.compProd_apply_prod MeasurableSet.univ hs,Measure.restrict_univ]
  let g (j : Fin f) (h : H) : ℝ≥0∞ := s.indicator 1 (marks (idx j) h)
  have hg (j : Fin f) : Measurable (g j) :=
    (measurable_const.indicator hs).comp (hmarks (idx j))
  have hgint (j : Fin f) : (∫⁻h,g j h∂M)≤C*ν s := by
    change (∫⁻h,s.indicator 1 (marks (idx j) h)∂M)≤C*ν s
    have he := lintegral_map (μ:=M) (f:=s.indicator (1 : Q→ℝ≥0∞))
      ((measurable_const : Measurable (1 : Q→ℝ≥0∞)).indicator hs) (hmarks (idx j))
    rw [←he,lintegral_indicator_one hs]
    simpa only [Measure.smul_apply,smul_eq_mul] using hM.2 (idx j) s
  have hd : ∀ᵐh∂M,κ h s≤k*ν s+∑j : Fin f,g j h := by
    filter_upwards [hdom] with h hh
    simpa only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      Measure.coe_finsetSum,Finset.sum_apply,Measure.dirac_apply' _ hs,g] using hh s
  calc
    (∫⁻h,κ h s∂M)≤∫⁻h,k*ν s+∑j : Fin f,g j h∂M := lintegral_mono_ae hd
    _ = (k*ν s)*M univ+∑j : Fin f,∫⁻h,g j h∂M := by
      rw [lintegral_add_left measurable_const,lintegral_const,
        lintegral_finsetSum Finset.univ (fun j _=>hg j)]
    _ ≤ (k*ν s)*C+∑_j : Fin f,C*ν s := by
      exact add_le_add (by simpa only [mul_comm] using mul_le_mul_left hM.1 (k*ν s))
        (Finset.sum_le_sum fun j _=>hgint j)
    _ = (((k+(f:ℝ≥0∞))*C)•ν) s := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Measure.smul_apply,smul_eq_mul]
      ring

theorem cavityGeneratedMarkBudget_compProd
    (ν : Measure Q) (M : Measure H) [SFinite M]
    (κ : Kernel H Q) [IsSFiniteKernel κ]
    (marks : Fin m→H→Q) (hmarks : ∀i,Measurable (marks i))
    (idx : Fin f→Fin m) (k C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M marks C)
    (hmass : ∀ᵐh∂M,κ h univ≤k)
    (hdom : ∀ᵐh∂M,κ h≤k•ν+∑j : Fin f,Measure.dirac (marks (idx j) h)) :
    cavityGeneratedMarkBudget ν (M⊗ₘκ) (cavityGeneratedExtendedMarks marks)
      ((k+(f:ℝ≥0∞))*C) := by
  have hconst : k*C≤(k+(f:ℝ≥0∞))*C := by
    rw [add_mul]
    exact le_add_right le_rfl
  refine ⟨(cavityGenerated_compProd_mass_le M κ k C hM.1 hmass).trans hconst,?_⟩
  intro i
  cases i using Fin.lastCases with
  | last =>
      simpa only [cavityGeneratedExtendedMarks,Fin.snoc_last] using
        cavityGenerated_compProd_snd_le ν M κ marks hmarks idx k C hM hdom
  | cast i =>
      simp only [cavityGeneratedExtendedMarks,Fin.snoc_castSucc]
      change (M⊗ₘκ).map (marks i∘Prod.fst)≤((k+(f:ℝ≥0∞))*C)•ν
      rw [←Measure.map_map (hmarks i) measurable_fst]
      apply (Measure.map_mono (cavityGenerated_compProd_fst_le M κ k hmass) (hmarks i)).trans
      rw [Measure.map_smul k (hmarks i).aemeasurable]
      have hmul : k•M.map (marks i)≤k•(C•ν) := by
        apply Measure.le_iff.mpr
        intro s hs
        simp only [Measure.smul_apply,smul_eq_mul]
        simpa only [Measure.smul_apply,smul_eq_mul,mul_comm] using mul_le_mul_left (hM.2 i s) k
      exact hmul.trans (by simpa only [smul_smul] using cavityGenerated_smul_mono ν hconst)

theorem cavityGeneratedMarkBudget_kernel_append
    (ν : Measure Q) (M : Measure (CavityGeneratedHistory Q m)) [SFinite M]
    (κ : Kernel (CavityGeneratedHistory Q m) Q) [IsSFiniteKernel κ]
    (idx : Fin f→Fin m) (k C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks C)
    (hmass : ∀ᵐh∂M,κ h univ≤k)
    (hdom : ∀ᵐh∂M,κ h≤k•ν+∑j : Fin f,Measure.dirac (h (idx j))) :
    cavityGeneratedMarkBudget ν ((M⊗ₘκ).map cavityGeneratedHistoryAppend)
      cavityGeneratedHistoryMarks ((k+(f:ℝ≥0∞))*C) := by
  exact cavityGeneratedMarkBudget_append_map ν _ _
    (cavityGeneratedMarkBudget_compProd ν M κ cavityGeneratedHistoryMarks
      cavityGeneratedHistoryMarks_measurable idx k C hM hmass hdom)

end QuantitativeFollowup
