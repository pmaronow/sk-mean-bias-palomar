module
public import HexagonPaper.EdgeLikelihoodAction
public import HexagonPaper.EdgeLikelihoodStoppedHistory
public import HexagonPaper.EdgeLikelihoodStoppedAction

@[expose] public section

/-! The genuine prefix density equals the literal full-profile clamped
potential action. Both endpoint atoms are retained in the measure integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

private theorem edge_stopped_sum_range (f : ℕ → ℝ) (H M : ℕ) (hHM : H ≤ M)
    (hf : ∀ i, H ≤ i → i < M → f i = 0) :
    ∑ i ∈ Finset.range M, f i = ∑ i ∈ Finset.range H, f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono hHM)
  intro i hi hin
  exact hf i (by simpa only [Finset.mem_range, not_lt] using hin)
    (Finset.mem_range.mp hi)

theorem edge_stopped_finite_reference_density_action
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n)
    (q h : Paper.Overlap) (hqh : (q : ℝ) ≤ h) (x : Field n)
    (H : ℕ) (hH : H ≤ k+2) (hstop : s.q H = (h : ℝ))
    (sample : VectorDisorderBrownianSample n) :
    finiteHistoryDensity (edgeRestartFiniteWeight D s q) H
      (edgeReferenceBrownianHistory D s g q x H sample) =
        edgeStoppedLikelihood D (Paper.parisiSchemeMeasure s) q h
          (edgeReferencePath D g q x sample) := by
  let μ := Paper.parisiSchemeMeasure s
  let Z := edgeReferencePath D g q x sample
  let node : ℕ → Paper.Overlap := fun i =>
    anisotropicSchemeNode s (min i (k+2)) (min_le_right _ _)
  let F : ℕ → ℝ := fun i => anisotropicMeasureTailPotential D μ
    (edgeIntervalClamp q h (node i)) (Z (edgeIntervalClamp q h (node i)))
  let a : ℕ → ℝ := fun i => (vectorClampedScheme s q q.property).m (i+1)
  have hn (i : ℕ) (hi : i ≤ k+2) : node i = anisotropicSchemeNode s i hi := by
    dsimp only [node]
    congr 1
    exact min_eq_left hi
  have hclamp (i : ℕ) (hi : i ≤ H) :
      edgeIntervalClamp q h (node i) = anisotropicClampOverlap q (node i) := by
    apply Subtype.ext
    rw [hn i (hi.trans hH)]
    change min (max (q : ℝ) (s.q i)) (h : ℝ) = max (q : ℝ) (s.q i)
    apply min_eq_left
    exact max_le hqh (by rw [←hstop]; exact s.q_mono' H hH i hi)
  have htail (i : ℕ) (hi : H ≤ i) (hiM : i ≤ k+2) :
      edgeIntervalClamp q h (node i) = h := by
    apply Subtype.ext
    rw [hn i hiM]
    change min (max (q : ℝ) (s.q i)) (h : ℝ) = (h : ℝ)
    apply min_eq_right
    rw [←hstop]
    exact (s.q_mono' i hiM H hi).trans (le_max_right _ _)
  have hpot (i : ℕ) (hi : i ≤ H) :
      F i = anisotropicFinitePotential D (vectorClampedScheme s q q.property)
        (k+2-i) ((edgeReferenceBrownianHistory D s g q x H sample) ⟨i, by omega⟩) := by
    dsimp only [F]
    rw [hclamp i hi, hn i (hi.trans hH), edge_native_potential_at_clamped_node D s q i
      (hi.trans hH)]
    congr 1
  have hfzero (i : ℕ) (hi : H ≤ i) (hiM : i < k+2) :
      a i * (F (i+1) - F i) = 0 := by
    dsimp only [F]
    rw [htail i hi (by omega), htail (i+1) (by omega) (by omega), sub_self, mul_zero]
  have hsum := edge_stopped_sum_range (fun i => a i * (F (i+1) - F i)) H (k+2) hH hfzero
  rw [edge_restart_finite_history_density_exp D s q H hH]
  have he : (∑i : Fin H,
      (vectorClampedScheme s q q.property).m (i+1) *
        (anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+1-(i:ℕ))
          ((edgeReferenceBrownianHistory D s g q x H sample) i.succ) -
        anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+2-(i:ℕ))
          ((edgeReferenceBrownianHistory D s g q x H sample) i.castSucc))) =
        ∑ i ∈ Finset.range H, a i * (F (i+1) - F i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpot (i:ℕ) (by omega), hpot ((i:ℕ)+1) (by omega),
      show k+2-((i:ℕ)+1) = k+1-(i:ℕ) by omega]
    rfl
  rw [he, ←hsum, weighted_difference_sum a F (k+1)]
  have ha0 : a 0 = 0 := by
    dsimp only [a]
    simpa only [Nat.zero_add, s.m_zero] using vectorClampedScheme_mass_succ s q q.property 0
  have haTop : a (k+1) = 1 := by
    dsimp only [a]
    simpa only [Nat.add_assoc, s.m_top] using vectorClampedScheme_mass_succ s q q.property (k+1)
  have hFTop : F (k+2) = anisotropicMeasureTailPotential D μ h (Z h) := by
    dsimp only [F]
    rw [htail (k+2) hH le_rfl]
  rw [ha0, haTop, zero_mul, one_mul, sub_zero, hFTop]
  change ENNReal.ofReal (Real.exp (anisotropicMeasureTailPotential D μ h (Z h) -
    ∑i ∈ Finset.range (k+1), (a (i+1) - a i) * F (i+1))) =
      ENNReal.ofReal (Real.exp (anisotropicMeasureTailPotential D μ h (Z h) -
        ∫r, anisotropicMeasureTailPotential D μ (edgeIntervalClamp q h r)
          (Z (edgeIntervalClamp q h r)) ∂(μ : Measure Paper.Overlap)))
  congr 2
  congr 1
  rw [FRSB.integral_parisiSchemeMeasure,
    ← Fin.sum_univ_eq_sum_range (fun i : ℕ => (a (i+1) - a i) * F (i+1)) (k+1)]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [a]
  rw [vectorClampedScheme_mass_succ, vectorClampedScheme_mass_succ]
  congr 1
  dsimp only [F]
  rw [hn ((i:ℕ)+1) (by omega)]
  rfl

end HexagonPaper
