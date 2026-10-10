module
public import QuantitativeFollowup.FollowupCavityGeneratedAppendMarkPayloadBudget

@[expose] public section

/-! A finite family of old forest charts spends one common history budget.
The payload carrier may depend on the chart. Only the genuine common
inherited-index list enters the new constant; the number of charts does not. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
variable {I H Q : Type*} [Fintype I] [MeasurableSpace H] [MeasurableSpace Q]
  [MeasurableSingletonClass Q] {m f : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem cavityGenerated_compProd_snd_le_raw
    (ν : Measure Q) (M : Measure H) [SFinite M]
    (κ : Kernel H Q) [IsSFiniteKernel κ]
    (marks : Fin m→H→Q) (hmarks : ∀j,Measurable (marks j))
    (idx : Fin f→Fin m) (k : ℝ≥0∞)
    (hdom : ∀ᵐh∂M,κ h≤k•ν+∑j : Fin f,Measure.dirac (marks (idx j) h)) :
    (M⊗ₘκ).map Prod.snd≤(k*M univ)•ν+∑j : Fin f,M.map (marks (idx j)) := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply measurable_snd hs]
  have he : (Prod.snd⁻¹' s : Set (H×Q))=univ×ˢs := by ext z; simp
  rw [he,Measure.compProd_apply_prod MeasurableSet.univ hs,Measure.restrict_univ]
  let g (j : Fin f) (h : H) : ℝ≥0∞ := s.indicator 1 (marks (idx j) h)
  have hg (j : Fin f) : Measurable (g j) :=
    (measurable_const.indicator hs).comp (hmarks (idx j))
  have hgint (j : Fin f) : (∫⁻h,g j h∂M)=(M.map (marks (idx j))) s := by
    change (∫⁻h,s.indicator 1 (marks (idx j) h)∂M)=_
    have he := lintegral_map (μ:=M) (f:=s.indicator (1 : Q→ℝ≥0∞))
      ((measurable_const : Measurable (1 : Q→ℝ≥0∞)).indicator hs) (hmarks (idx j))
    rw [←he,lintegral_indicator_one hs]
  have hd : ∀ᵐh∂M,κ h s≤k*ν s+∑j : Fin f,g j h := by
    filter_upwards [hdom] with h hh
    simpa only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      Measure.coe_finsetSum,Finset.sum_apply,Measure.dirac_apply' _ hs,g] using hh s
  calc
    (∫⁻h,κ h s∂M)≤∫⁻h,k*ν s+∑j : Fin f,g j h∂M := lintegral_mono_ae hd
    _ = (k*ν s)*M univ+∑j : Fin f,(M.map (marks (idx j))) s := by
      rw [lintegral_add_left measurable_const,lintegral_const,
        lintegral_finsetSum Finset.univ (fun j _=>hg j)]
      simp only [hgint]
    _ = ((k*M univ)•ν+∑j : Fin f,M.map (marks (idx j))) s := by
      simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,
        Measure.coe_finsetSum,Finset.sum_apply]
      ring

theorem cavityGeneratedMarkBudget_indexed_compProd
    (ν : Measure Q) (M : I→Measure H) [∀i,SFinite (M i)]
    (κ : I→Kernel H Q) [∀i,IsSFiniteKernel (κ i)]
    (marks : Fin m→H→Q) (hmarks : ∀j,Measurable (marks j))
    (idx : Fin f→Fin m) (k C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν (∑i,M i) marks C)
    (hmass : ∀i,∀ᵐh∂M i,κ i h univ≤k)
    (hdom : ∀i,∀ᵐh∂M i,κ i h≤k•ν+∑j : Fin f,Measure.dirac (marks (idx j) h)) :
    cavityGeneratedMarkBudget ν (∑i,M i⊗ₘκ i)
      (cavityGeneratedExtendedMarks marks) ((k+(f:ℝ≥0∞))*C) := by
  classical
  have hconst : k*C≤(k+(f:ℝ≥0∞))*C := by
    rw [add_mul]
    exact le_add_right le_rfl
  have hmassSum : (∑i,M i⊗ₘκ i) univ≤k*C := by
    simp only [Measure.coe_finsetSum,Finset.sum_apply]
    calc
      (∑i,(M i⊗ₘκ i) univ)≤∑i,k*(M i) univ := by
        apply Finset.sum_le_sum
        intro i hi
        exact cavityGenerated_compProd_mass_le (M i) (κ i) k ((M i) univ) le_rfl (hmass i)
      _ = k*(∑i,M i) univ := by
        simp only [Measure.coe_finsetSum,Finset.sum_apply,Finset.mul_sum]
      _ ≤ k*C := by simpa only [mul_comm] using mul_le_mul_left hM.1 k
  refine ⟨hmassSum.trans hconst,?_⟩
  intro j
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply (cavityGeneratedExtendedMarks_measurable marks hmarks j) hs]
  simp only [Measure.coe_finsetSum,Finset.sum_apply]
  cases j using Fin.lastCases with
  | last =>
      have hi (i : I) : (M i⊗ₘκ i) ((cavityGeneratedExtendedMarks marks (Fin.last m))⁻¹' s)
          ≤(k*(M i) univ)*ν s+∑j : Fin f,(M i).map (marks (idx j)) s := by
        have hh := cavityGenerated_compProd_snd_le_raw ν (M i) (κ i) marks hmarks idx k (hdom i)
        have hh' := hh s
        rw [Measure.map_apply measurable_snd hs] at hh'
        simpa only [cavityGeneratedExtendedMarks,Fin.snoc_last,
          Measure.add_apply,Measure.smul_apply,smul_eq_mul,
          Measure.coe_finsetSum,Finset.sum_apply] using hh'
      have hmark (j : Fin f) : (∑i,(M i).map (marks (idx j)) s)≤C*ν s := by
        have hh := hM.2 (idx j) s
        rw [Measure.map_apply (hmarks (idx j)) hs] at hh
        simp only [Measure.coe_finsetSum,Finset.sum_apply] at hh
        simpa only [Measure.map_apply (hmarks (idx j)) hs,
          Measure.smul_apply,smul_eq_mul] using hh
      calc
        (∑i,(M i⊗ₘκ i) ((cavityGeneratedExtendedMarks marks (Fin.last m))⁻¹' s))
            ≤∑i,((k*(M i) univ)*ν s+∑j : Fin f,(M i).map (marks (idx j)) s) :=
          Finset.sum_le_sum fun i _=>hi i
        _ = (k*ν s)*(∑i,M i) univ+∑j : Fin f,∑i,(M i).map (marks (idx j)) s := by
          rw [Finset.sum_add_distrib,Finset.sum_comm]
          simp only [Measure.coe_finsetSum,Finset.sum_apply]
          congr 1
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ (k*ν s)*C+∑_j : Fin f,C*ν s := by
          exact add_le_add (by simpa only [mul_comm] using mul_le_mul_left hM.1 (k*ν s))
            (Finset.sum_le_sum fun j _=>hmark j)
        _ = (((k+(f:ℝ≥0∞))*C)•ν) s := by
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
            Measure.smul_apply,smul_eq_mul]
          ring
  | cast j =>
      have hi (i : I) : (M i⊗ₘκ i) ((cavityGeneratedExtendedMarks marks j.castSucc)⁻¹' s)
          ≤k*(M i).map (marks j) s := by
        have hh := Measure.map_mono
          (cavityGenerated_compProd_fst_le (M i) (κ i) k (hmass i)) (hmarks j)
        have hh' := hh s
        rw [Measure.map_map (hmarks j) measurable_fst,
          Measure.map_smul k (hmarks j).aemeasurable,
          Measure.map_apply ((hmarks j).comp measurable_fst) hs] at hh'
        simpa only [cavityGeneratedExtendedMarks,Fin.snoc_castSucc,
          Function.comp_def,Measure.smul_apply,smul_eq_mul] using hh'
      have hmark : (∑i,(M i).map (marks j) s)≤C*ν s := by
        have hh := hM.2 j s
        rw [Measure.map_apply (hmarks j) hs] at hh
        simp only [Measure.coe_finsetSum,Finset.sum_apply] at hh
        simpa only [Measure.map_apply (hmarks j) hs,Measure.smul_apply,smul_eq_mul] using hh
      calc
        (∑i,(M i⊗ₘκ i) ((cavityGeneratedExtendedMarks marks j.castSucc)⁻¹' s))
            ≤∑i,k*(M i).map (marks j) s := Finset.sum_le_sum fun i _=>hi i
        _ = k*(∑i,(M i).map (marks j) s) := (Finset.mul_sum _ _ _).symm
        _ ≤ k*(C*ν s) := by simpa only [mul_comm] using mul_le_mul_left hmark k
        _ ≤ (((k+(f:ℝ≥0∞))*C)•ν) s := by
          simpa only [Measure.smul_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm]
            using mul_le_mul_right hconst (ν s)

theorem cavityGeneratedMarkBudget_indexed_kernel_payload_append
    {G : I→Type*} [∀i,MeasurableSpace (G i)]
    (ν : Measure Q) (M : I→Measure (CavityGeneratedHistory Q m)) [∀i,SFinite (M i)]
    (κ : (i : I)→Kernel (CavityGeneratedHistory Q m) (G i)) [∀i,IsSFiniteKernel (κ i)]
    (τ : (i : I)→CavityGeneratedHistory Q m×G i→Q) (hτ : ∀i,Measurable (τ i))
    (idx : Fin f→Fin m) (k C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν (∑i,M i) cavityGeneratedHistoryMarks C)
    (hmass : ∀i,∀ᵐh∂M i,κ i h univ≤k)
    (hdom : ∀i,∀ᵐh∂M i,(κ i h).map (fun g=>τ i (h,g))≤
      k•ν+∑j : Fin f,Measure.dirac (h (idx j))) :
    cavityGeneratedMarkBudget ν (∑i,(M i⊗ₘκ i).map (fun z=>Fin.snoc z.1 (τ i z)))
      cavityGeneratedHistoryMarks ((k+(f:ℝ≥0∞))*C) := by
  classical
  let η (i : I) := cavityGeneratedPayloadClockKernel (κ i) (τ i)
  have hm (i : I) : ∀ᵐh∂M i,η i h univ≤k := by
    filter_upwards [hmass i] with h hh
    change cavityGeneratedPayloadClockKernel (κ i) (τ i) h univ≤k
    rw [cavityGeneratedPayloadClockKernel_apply (κ i) (τ i) (hτ i)]
    have hτh : Measurable (fun g : G i=>τ i (h,g)) :=
      (hτ i).comp measurable_prodMk_left
    rw [Measure.map_apply hτh MeasurableSet.univ,preimage_univ]
    exact hh
  have hd (i : I) : ∀ᵐh∂M i,η i h≤k•ν+∑j : Fin f,Measure.dirac (h (idx j)) := by
    simpa only [η,cavityGeneratedPayloadClockKernel_apply (κ i) (τ i) (hτ i)] using hdom i
  have hb := cavityGeneratedMarkBudget_append_map ν _ _
    (cavityGeneratedMarkBudget_indexed_compProd ν M η cavityGeneratedHistoryMarks
      cavityGeneratedHistoryMarks_measurable idx k C hM hm hd)
  have he : (∑i,M i⊗ₘη i).map cavityGeneratedHistoryAppend=
      ∑i,(M i⊗ₘκ i).map (fun z=>Fin.snoc z.1 (τ i z)) := by
    ext s hs
    rw [Measure.map_apply cavityGeneratedHistoryAppend_measurable hs]
    simp only [Measure.coe_finsetSum,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have hg : Measurable (fun z : CavityGeneratedHistory Q m×G i=>(z.1,τ i z)) :=
      measurable_fst.prodMk (hτ i)
    rw [←cavityGenerated_compProd_payload_clock_map (M i) (κ i) (τ i) (hτ i),
      Measure.map_apply hg (hs.preimage cavityGeneratedHistoryAppend_measurable)]
    have ha : Measurable (fun z : CavityGeneratedHistory Q m×G i=>
        (Fin.snoc z.1 (τ i z) : CavityGeneratedHistory Q (m+1))) := by
      simpa only [Function.comp_def,cavityGeneratedHistoryAppend] using
        cavityGeneratedHistoryAppend_measurable.comp hg
    rw [Measure.map_apply ha hs]
    rfl
  simpa only [he] using hb

end QuantitativeFollowup
