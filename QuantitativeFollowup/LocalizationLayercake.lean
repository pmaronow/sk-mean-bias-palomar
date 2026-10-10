module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic

@[expose] public section

/-! The actual four-piece layer-cake decomposition in the isolation
argument. The negative level set is split at its threshold-dependent
boundary; measurability and integrability are proved for this moving cut. -/
noncomputable section
open Set MeasureTheory Filter Function
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def localizationLevelSet (psi : ℝ → ℝ) (q L A : ℝ) (j : Fin 4) : Set ℝ :=
  if j=0 then {x | x∈Ioo (0 : ℝ) q ∧ A<psi x}
  else if j=1 then {x | x∈Ioo (0 : ℝ) (q-A/(2*L)) ∧ psi x < -A}
  else if j=2 then {x | x∈Ioo (0 : ℝ) q ∧ q-A/(2*L)≤x ∧ psi x < -A}
  else {x | x∈Icc q 1 ∧ A<psi x}

def localizationLevelMass (psi : ℝ → ℝ) (q L A : ℝ) (j : Fin 4) : ℝ :=
  volume.real (localizationLevelSet psi q L A j)

theorem measurable_localizationLevelSet (psi : ℝ → ℝ) (hpsi : Measurable psi)
    (q L A : ℝ) (j : Fin 4) : MeasurableSet (localizationLevelSet psi q L A j) := by
  fin_cases j <;> norm_num only [localizationLevelSet]
  · exact measurableSet_Ioo.inter (measurableSet_lt measurable_const hpsi)
  · exact measurableSet_Ioo.inter (measurableSet_lt hpsi measurable_const)
  · exact measurableSet_Ioo.inter (measurableSet_Ici.inter (measurableSet_lt hpsi measurable_const))
  · exact measurableSet_Icc.inter (measurableSet_lt measurable_const hpsi)

theorem measurable_localizationLevelMass (psi : ℝ → ℝ) (hpsi : Measurable psi)
    (q L : ℝ) (j : Fin 4) : Measurable (fun A => localizationLevelMass psi q L A j) := by
  have hm : Measurable (fun p : ℝ×ℝ => psi p.2) := hpsi.comp measurable_snd
  fin_cases j
  · have hs : MeasurableSet {p : ℝ×ℝ | p.2∈Ioo (0 : ℝ) q ∧ p.1<psi p.2} :=
      (measurable_snd measurableSet_Ioo).inter (measurableSet_lt measurable_fst hm)
    exact (measurable_measure_prodMk_left (ν := volume) hs).ennreal_toReal
  · have hs : MeasurableSet {p : ℝ×ℝ | p.2∈Ioo (0 : ℝ) (q-p.1/(2*L)) ∧ psi p.2 < -p.1} :=
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.sub (measurable_fst.div_const _)))).inter
          (measurableSet_lt hm measurable_fst.neg)
    exact (measurable_measure_prodMk_left (ν := volume) hs).ennreal_toReal
  · have hs : MeasurableSet {p : ℝ×ℝ | p.2∈Ioo (0 : ℝ) q ∧ q-p.1/(2*L)≤p.2 ∧ psi p.2 < -p.1} :=
      (measurable_snd measurableSet_Ioo).inter
        ((measurableSet_le (measurable_const.sub (measurable_fst.div_const _)) measurable_snd).inter
          (measurableSet_lt hm measurable_fst.neg))
    exact (measurable_measure_prodMk_left (ν := volume) hs).ennreal_toReal
  · have hs : MeasurableSet {p : ℝ×ℝ | p.2∈Icc q 1 ∧ p.1<psi p.2} :=
      (measurable_snd measurableSet_Icc).inter (measurableSet_lt measurable_fst hm)
    exact (measurable_measure_prodMk_left (ν := volume) hs).ennreal_toReal

theorem localizationLevelSet_subset_unit (psi : ℝ → ℝ) (q L A : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hA : 0<A) (j : Fin 4) :
    localizationLevelSet psi q L A j ⊆ Ioc (0 : ℝ) 1 := by
  have hcut : q-A/(2*L)≤q := sub_le_self _ (by positivity)
  intro x hx
  fin_cases j <;> simp [localizationLevelSet] at hx
  · exact ⟨hx.1.1, hx.1.2.le.trans hq.2.le⟩
  · exact ⟨hx.1.1, hx.1.2.le.trans (hcut.trans hq.2.le)⟩
  · exact ⟨hx.1.1, hx.1.2.le.trans hq.2.le⟩
  · exact ⟨hq.1.trans_le hx.1.1, hx.1.2⟩

theorem localizationLevelMass_nonneg_le_one (psi : ℝ → ℝ) (q L A : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hA : 0<A) (j : Fin 4) :
    0 ≤ localizationLevelMass psi q L A j ∧ localizationLevelMass psi q L A j ≤ 1 := by
  refine ⟨measureReal_nonneg, ?_⟩
  have hh := measureReal_mono (μ := volume) (localizationLevelSet_subset_unit psi q L A hq hL hA j)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  simpa only [localizationLevelMass, Real.volume_real_Ioc, sub_zero, max_eq_left zero_le_one] using hh

theorem localizationLevelSet_partition (psi : ℝ → ℝ) (q L A : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hA : 0<A)
    (hpost : ∀x∈Icc q 1, 0≤psi x) :
    {x : ℝ | x∈Ioc (0 : ℝ) 1 ∧ A < |psi x|} = ⋃j : Fin 4, localizationLevelSet psi q L A j := by
  ext x
  constructor
  · rintro ⟨hx, hpx⟩
    by_cases hxq : x<q
    · by_cases hsign : 0≤psi x
      · exact mem_iUnion.mpr ⟨0, by
          simp only [localizationLevelSet, Fin.isValue, ite_true, mem_ofPred_eq, mem_Ioo]
          exact ⟨⟨hx.1, hxq⟩, by simpa only [abs_of_nonneg hsign] using hpx⟩⟩
      · have hp : psi x < -A := by rw [abs_of_neg (lt_of_not_ge hsign)] at hpx; linarith
        by_cases hxb : x<q-A/(2*L)
        · exact mem_iUnion.mpr ⟨1, by simp only [localizationLevelSet, Fin.isValue, ite_true]; exact ⟨⟨hx.1,hxb⟩,hp⟩⟩
        · exact mem_iUnion.mpr ⟨2, by simp only [localizationLevelSet, Fin.isValue, ite_true]; exact ⟨⟨hx.1,hxq⟩,le_of_not_gt hxb,hp⟩⟩
    · exact mem_iUnion.mpr ⟨3, by
        simp only [localizationLevelSet, Fin.isValue]
        exact ⟨⟨le_of_not_gt hxq,hx.2⟩,by simpa only [abs_of_nonneg (hpost x ⟨le_of_not_gt hxq,hx.2⟩)] using hpx⟩⟩
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    refine ⟨localizationLevelSet_subset_unit psi q L A hq hL hA j hj, ?_⟩
    fin_cases j <;> simp [localizationLevelSet] at hj
    · exact hj.2.trans_le (le_abs_self _)
    · have hh := neg_le_abs (psi x); linarith [hj.2]
    · have hh := neg_le_abs (psi x); linarith [hj.2.2]
    · exact hj.2.trans_le (le_abs_self _)

theorem localizationLevelSet_pairwiseDisjoint (psi : ℝ → ℝ) (q L A : ℝ)
    (hL : 0<L) (hA : 0<A) : Pairwise (Disjoint on localizationLevelSet psi q L A) := by
  have hcut : q-A/(2*L)≤q := sub_le_self _ (by positivity)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals apply Set.disjoint_left.mpr
  all_goals intro x hx hy
  all_goals simp [localizationLevelSet] at hx hy
  all_goals rcases hx with ⟨hx,hpx⟩
  all_goals rcases hy with ⟨hy,hpy⟩
  all_goals rcases hx with ⟨hx0,hx1⟩
  all_goals rcases hy with ⟨hy0,hy1⟩
  all_goals linarith

theorem localizationLevelMass_sum (psi : ℝ → ℝ) (hpsi : Measurable psi) (q L A : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hA : 0<A)
    (hpost : ∀x∈Icc q 1, 0≤psi x) :
    (volume.restrict (Ioc (0 : ℝ) 1)).real {x : ℝ | A < |psi x|} =
      ∑j : Fin 4, localizationLevelMass psi q L A j := by
  have hms : MeasurableSet {x : ℝ | A < |psi x|} := by
    simpa only [Real.norm_eq_abs] using measurableSet_lt measurable_const hpsi.norm
  rw [Measure.real, Measure.restrict_apply hms]
  have he : {x : ℝ | A < |psi x|} ∩ Ioc (0 : ℝ) 1 =
      {x : ℝ | x∈Ioc (0 : ℝ) 1 ∧ A < |psi x|} := by ext x; simp [and_comm]
  rw [he,localizationLevelSet_partition psi q L A hq hL hA hpost]
  exact measureReal_iUnion_fintype (localizationLevelSet_pairwiseDisjoint psi q L A hL hA)
    (measurable_localizationLevelSet psi hpsi q L A)
    (fun j => (measure_mono (localizationLevelSet_subset_unit psi q L A hq hL hA j)).trans_lt
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) |>.ne)

theorem localizationLevelMass_zero_above (psi : ℝ → ℝ) (q L beta A : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hbeta : 0<beta) (hA : beta≤A)
    (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta) (j : Fin 4) :
    localizationLevelMass psi q L A j = 0 := by
  have hA0 : 0<A := hbeta.trans_le hA
  have hempty : localizationLevelSet psi q L A j = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hb := hbound x ⟨(localizationLevelSet_subset_unit psi q L A hq hL hA0 j hx).1.le,
      (localizationLevelSet_subset_unit psi q L A hq hL hA0 j hx).2⟩
    fin_cases j <;> simp [localizationLevelSet] at hx
    · linarith [hx.2, le_abs_self (psi x)]
    · linarith [hx.2, neg_le_abs (psi x)]
    · linarith [hx.2.2, neg_le_abs (psi x)]
    · linarith [hx.2, le_abs_self (psi x)]
  simp only [localizationLevelMass,hempty,measureReal_empty]

theorem integrable_localizationLevelMass (psi : ℝ → ℝ) (hpsi : Measurable psi) (q L beta : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hbeta : 0<beta)
    (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta) (j : Fin 4) :
    IntegrableOn (fun A => localizationLevelMass psi q L A j) (Ioi (0 : ℝ)) volume := by
  have hi : Integrable ((Ioc (0 : ℝ) beta).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioc
  apply (hi.mono_measure Measure.restrict_le_self).mono'
    (measurable_localizationLevelMass psi hpsi q L j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with A hA
  change |localizationLevelMass psi q L A j| ≤ (Ioc (0 : ℝ) beta).indicator (fun _ : ℝ => (1 : ℝ)) A
  rw [abs_of_nonneg (show 0≤localizationLevelMass psi q L A j from measureReal_nonneg)]
  by_cases hAb : A≤beta
  · rw [indicator_of_mem (show A∈Ioc (0 : ℝ) beta from ⟨hA,hAb⟩)]
    exact (localizationLevelMass_nonneg_le_one psi q L A hq hL hA j).2
  · rw [localizationLevelMass_zero_above psi q L beta A hq hL hbeta (le_of_not_ge hAb) hbound j]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem localization_layercake (psi : ℝ → ℝ) (hpsi : Measurable psi) (q L beta : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hbeta : 0<beta)
    (hbound : ∀x∈Icc (0 : ℝ) 1, |psi x|≤beta)
    (hpost : ∀x∈Icc q 1, 0≤psi x) :
    (∫ x in (0 : ℝ)..1, |psi x|) =
      ∑j : Fin 4, ∫ A : ℝ in Ioi 0, localizationLevelMass psi q L A j := by
  have hi : Integrable (fun x => |psi x|) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply Integrable.of_bound hpsi.norm.aestronglyMeasurable beta
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa only [Real.norm_eq_abs, abs_abs] using hbound x ⟨hx.1.le,hx.2⟩
  rw [intervalIntegral.integral_of_le zero_le_one,hi.integral_eq_integral_meas_lt (.of_forall (fun _ => abs_nonneg _))]
  rw [←integral_finsetSum Finset.univ (fun j _ => integrable_localizationLevelMass psi hpsi q L beta hq hL hbeta hbound j)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro A hA
  exact localizationLevelMass_sum psi hpsi q L A hq hL hA hpost

end QuantitativeFollowup
