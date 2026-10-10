module
public import QuantitativePaper.LocalSmoothIntegralJets
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Fixed unit-interval integration on an open parameter domain, with exact
higher derivative identities and genuine exponential jet bounds. Only the
actual interval is used for regularity and domination hypotheses. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem compact_parameter_integral_smooth_exp_jets_on_open (N : ℕ)
    (f : E→ℝ→F) (U : Set E) (hU : IsOpen U)
    (hf : ∀r∈Icc (0:ℝ) 1, ContDiffOn ℝ N (fun x=>f x r) U)
    (hmeas : ∀j, j≤N → ∀x∈U, AEStronglyMeasurable
      (fun r=>iteratedFDeriv ℝ j (fun y=>f y r) x) (volume.restrict (Icc (0:ℝ) 1)))
    (K D : ℝ) (hK : 0≤K) (hD : 0≤D)
    (hjets : ∀j, j≤N → ∀x∈U, ∀r∈Icc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ j (fun y=>f y r) x‖≤(K*Real.exp (D*‖x‖))^(j+1)) :
    ContDiffOn ℝ N (fun x=>∫r in Icc (0:ℝ) 1,f x r) U ∧
      (∀j, j≤N → ∀x∈U,
        iteratedFDeriv ℝ j (fun y=>∫r in Icc (0:ℝ) 1,f y r) x=
          ∫r in Icc (0:ℝ) 1,iteratedFDeriv ℝ j (fun y=>f y r) x) ∧
      ∀j, j≤N → ∀x∈U,
        ‖iteratedFDeriv ℝ j (fun y=>∫r in Icc (0:ℝ) 1,f y r) x‖≤
          (K*Real.exp (D*‖x‖))^(j+1) := by
  let S := Icc (0:ℝ) 1
  let G : E→ℝ→F := fun x r=>S.indicator (f x) r
  have he (j : ℕ) (x : E) (r : ℝ) :
      iteratedFDeriv ℝ j (fun y=>G y r) x=
        S.indicator (fun t=>iteratedFDeriv ℝ j (fun y=>f y t) x) r := by
    by_cases hr : r∈S
    · have hg : (fun y=>G y r)=(fun y=>f y r) := by
        funext y
        exact indicator_of_mem hr _
      rw [hg,indicator_of_mem hr]
    · have hg : (fun y=>G y r)=(fun _=>0) := by
        funext y
        exact indicator_of_notMem hr _
      rw [hg,indicator_of_notMem hr]
      by_cases hj : j=0
      · subst j
        ext v
        simp only [iteratedFDeriv_zero_apply,ContinuousMultilinearMap.zero_apply]
      · rw [iteratedFDeriv_const_of_ne hj]
        rfl
  have hgs : ∀r,ContDiffOn ℝ N (fun x=>G x r) U := by
    intro r
    by_cases hr : r∈S
    · have hg : (fun y=>G y r)=(fun y=>f y r) := by
        funext y
        exact indicator_of_mem hr _
      rw [hg]
      exact hf r hr
    · have hg : (fun y=>G y r)=(fun _=>0) := by
        funext y
        exact indicator_of_notMem hr _
      rw [hg]
      exact contDiffOn_const
  have hgm : ∀j,j≤N → ∀x∈U,AEStronglyMeasurable
      (fun r=>iteratedFDeriv ℝ j (fun y=>G y r) x) volume := by
    intro j hj x hx
    simp_rw [he]
    exact (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr (hmeas j hj x hx)
  have hgb : ∀x∈U,∃s∈𝓝 x,s⊆U ∧ ∃B : ℕ→ℝ→ℝ,
      (∀j,j≤N → Integrable (B j) volume) ∧
      ∀j,j≤N → ∀y∈s,∀r,‖iteratedFDeriv ℝ j (fun u=>G u r) y‖≤B j r := by
    intro x hx
    let C := K*Real.exp (D*(‖x‖+1))
    refine ⟨Metric.ball x 1 ∩ U,inter_mem (Metric.ball_mem_nhds x (by norm_num))
      (hU.mem_nhds hx),inter_subset_right,
      fun j=>S.indicator (fun _=>C^(j+1)),?_,?_⟩
    · intro j _
      have hi : IntegrableOn (fun _ : ℝ=>C^(j+1)) S volume :=
        integrableOn_const (by simp [S,Real.volume_Icc])
      exact hi.integrable_indicator measurableSet_Icc
    · intro j hj y hy r
      rw [he]
      dsimp only
      by_cases hr : r∈S
      · simp only [indicator_of_mem hr]
        apply (hjets j hj y hy.2 r hr).trans
        apply pow_le_pow_left₀ (by positivity)
        apply mul_le_mul_of_nonneg_left ?_ hK
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (norm_le_norm_add_const_of_dist_le hy.1.le) hD)
      · simp only [indicator_of_notMem hr]
        simp
  have hG := contDiffOn_integral_of_dominated_derivatives N volume G U hU hgs hgm hgb
  have hGi : (fun x=>∫r,G x r)=(fun x=>∫r in Icc (0:ℝ) 1,f x r) := by
    funext x
    exact integral_indicator measurableSet_Icc
  rw [hGi] at hG
  have hJet (j : ℕ) (hj : j≤N) (x : E) (hx : x∈U) :
      iteratedFDeriv ℝ j (fun y=>∫r in Icc (0:ℝ) 1,f y r) x=
        ∫r in Icc (0:ℝ) 1,iteratedFDeriv ℝ j (fun y=>f y r) x := by
    rw [←hGi,iteratedFDeriv_integral_of_locally_dominated_derivatives N volume G U hU
      hgs hgm hgb j hj x hx]
    simp_rw [he]
    exact integral_indicator measurableSet_Icc
  refine ⟨hG,hJet,?_⟩
  intro j hj x hx
  rw [hJet j hj x hx]
  have hn := norm_integral_le_of_norm_le_const
    (f:=fun r=>iteratedFDeriv ℝ j (fun y=>f y r) x)
    (μ:=volume.restrict (Icc (0:ℝ) 1))
    (C:=(K*Real.exp (D*‖x‖))^(j+1)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hjets j hj x hx r hr)
  simpa [Measure.real,Real.volume_Icc] using hn

end QuantitativePaper
