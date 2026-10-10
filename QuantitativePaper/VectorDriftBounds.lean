module
public import QuantitativePaper.VectorWeightedDrift

@[expose] public section

/-! Bounded measurable vector drifts have genuine Lipschitz integral paths.
The bounds also control every weighted partition sum independently of its
mesh, permitting expectation limits by dominated convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace QuantitativePaper

theorem integrableOn_bounded_vector_drift {n : ℕ} (d : ℝ≥0 → Field n)
    (hd : Measurable d) (D : ℝ≥0) (hD : ∀ s,‖d s‖ ≤ D) (r t : ℝ≥0) :
    IntegrableOn d (Ioc r t) nonnegativeLebesgueMeasure := by
  apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top r t)
    (C := (D : ℝ))).mono' hd.aestronglyMeasurable
  exact .of_forall hD

theorem vectorIntegratedDrift_sub {n : ℕ} (d : ℝ≥0 → Field n)
    {r t : ℝ≥0} (hrt : r ≤ t)
    (hd : IntegrableOn d (Ioc 0 t) nonnegativeLebesgueMeasure) :
    vectorIntegratedDrift d t-vectorIntegratedDrift d r =
      ∫ s in Ioc r t,d s ∂nonnegativeLebesgueMeasure := by
  have hdiff : Ioc (0 : ℝ≥0) t \ Ioc 0 r = Ioc r t := by
    ext s
    simp only [Set.mem_sdiff,Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hs0,hst⟩,hnot⟩
      exact ⟨lt_of_not_ge (fun hsr=>hnot ⟨hs0,hsr⟩),hst⟩
    · rintro ⟨hrs,hst⟩
      exact ⟨⟨lt_of_le_of_lt (bot_le : (0 : ℝ≥0)≤r) hrs,hst⟩,
        fun hs=>not_le_of_gt hrs hs.2⟩
  rw [vectorIntegratedDrift,vectorIntegratedDrift,← hdiff]
  exact (setIntegral_sdiff measurableSet_Ioc hd (Ioc_subset_Ioc_right hrt)).symm

theorem vectorIntegratedDrift_increment_bound {n : ℕ} (d : ℝ≥0 → Field n)
    (hd : Measurable d) (D : ℝ≥0) (hD : ∀ s,‖d s‖ ≤ D)
    {r t : ℝ≥0} (hrt : r ≤ t) :
    ‖vectorIntegratedDrift d t-vectorIntegratedDrift d r‖ ≤ D*((t : ℝ)-(r : ℝ)) := by
  rw [vectorIntegratedDrift_sub d hrt (integrableOn_bounded_vector_drift d hd D hD 0 t)]
  have hb := norm_setIntegral_le_of_norm_le_const
    (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top r t))
    (fun s (_ : s∈Ioc r t)=>hD s)
  simpa only [Measure.real,nonnegativeLebesgueMeasure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrt))] using hb

theorem vectorIntegratedDrift_lipschitz {n : ℕ} (d : ℝ≥0 → Field n)
    (hd : Measurable d) (D : ℝ≥0) (hD : ∀ s,‖d s‖ ≤ D) :
    LipschitzWith D (vectorIntegratedDrift d) := by
  apply LipschitzWith.of_dist_le_mul
  intro r t
  rcases le_total r t with hrt | htr
  · rw [dist_comm,dist_eq_norm,NNReal.dist_eq,abs_of_nonpos
      (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hrt))]
    simpa only [neg_sub] using vectorIntegratedDrift_increment_bound d hd D hD hrt
  · rw [dist_eq_norm,NNReal.dist_eq,abs_of_nonneg
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr htr))]
    exact vectorIntegratedDrift_increment_bound d hd D hD htr

def vectorWeightedDriftApprox {n : ℕ} (d : ℝ≥0 → Field n)
    (w : ℝ≥0 → Field n →L[ℝ] ℝ) (t : ℝ≥0) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,w (uniformPartitionTime t N j)
    (vectorIntegratedDrift d (uniformPartitionTime t N (j+1))-
      vectorIntegratedDrift d (uniformPartitionTime t N j))

theorem vectorWeightedDriftApprox_bound {n : ℕ} (d : ℝ≥0 → Field n)
    (hd : Measurable d) (D : ℝ≥0) (hD : ∀ s,‖d s‖ ≤ D)
    (w : ℝ≥0 → Field n →L[ℝ] ℝ) (K : ℝ≥0) (t : ℝ≥0)
    (hK : ∀ s∈Icc 0 t,‖w s‖ ≤ K) {N : ℕ} (hN : 0 < N) :
    |vectorWeightedDriftApprox d w t N| ≤ K*D*t := by
  have hb (j : ℕ) (hj : j∈Finset.range N) :
      |w (uniformPartitionTime t N j)
        (vectorIntegratedDrift d (uniformPartitionTime t N (j+1))-
          vectorIntegratedDrift d (uniformPartitionTime t N j))| ≤
        (K : ℝ)*D*((t : ℝ)/(N : ℝ)) := by
    have hji : j<N := Finset.mem_range.mp hj
    have htime := uniformPartitionTime_mem_Icc_of_le t hN hji.le
    have hrt := monotone_uniformPartitionTime t N (Nat.le_add_right j 1)
    have hh := vectorIntegratedDrift_increment_bound d hd D hD hrt
    have hdist := dist_uniformPartitionTime_succ_eq t hN j
    have hlen : ((uniformPartitionTime t N (j+1) : ℝ≥0) : ℝ)-
        ((uniformPartitionTime t N j : ℝ≥0) : ℝ) = (t : ℝ)/(N : ℝ) := by
      rw [NNReal.dist_eq,abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrt))] at hdist
      simpa only [NNReal.coe_div,NNReal.coe_natCast] using hdist
    rw [hlen] at hh
    calc
      _ ≤ ‖w (uniformPartitionTime t N j)‖*
          ‖vectorIntegratedDrift d (uniformPartitionTime t N (j+1))-
            vectorIntegratedDrift d (uniformPartitionTime t N j)‖ := by
        simpa only [Real.norm_eq_abs] using
          (w (uniformPartitionTime t N j)).le_opNorm _
      _ ≤ (K : ℝ)*(D*((t : ℝ)/(N : ℝ))) :=
        mul_le_mul (hK _ htime) hh (norm_nonneg _) K.coe_nonneg
      _ = _ := by ring
  calc
    _ ≤ ∑ j∈Finset.range N,
        |w (uniformPartitionTime t N j)
          (vectorIntegratedDrift d (uniformPartitionTime t N (j+1))-
            vectorIntegratedDrift d (uniformPartitionTime t N j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈Finset.range N,(K : ℝ)*D*((t : ℝ)/(N : ℝ)) :=
      Finset.sum_le_sum hb
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      have hne : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp

end QuantitativePaper
