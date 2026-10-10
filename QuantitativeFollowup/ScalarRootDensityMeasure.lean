module
public import QuantitativeFollowup.ScalarTrialDensity
public import QuantitativeFollowup.ScalarRootGrowth

@[expose] public section

/-! Actual near-root lower density domination, including the literal
measure inequality used by Lemma 5.9 of the quantitative follow-up. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory Paper FRSB
open scoped Topology ENNReal NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 600000

theorem scalar_zero_floor_free_measure_eq (β : ℝ) (hβ : 0≤β) (μ : Paper.ParisiMeasure) :
    (scalarTrialStieltjes β hβ 0 μ).measure=ENNReal.ofReal β • (μ:Measure Paper.Overlap).map Subtype.val := by
  let c : ℝ≥0:=⟨β,hβ⟩
  have he : c • cdf ((μ:Measure Paper.Overlap).map Subtype.val)=scalarTrialStieltjes β hβ 0 μ := by
    ext x
    change β*cdf ((μ:Measure Paper.Overlap).map Subtype.val) x=max 0 (β*parisiCDF μ x)
    rw [parisiCDF_eq_realCDF,max_eq_right (mul_nonneg hβ (cdf_nonneg _ _))]
  rw [←he,StieltjesFunction.measure_smul,measure_cdf]
  ext S
  change (c:ℝ≥0∞)*((μ:Measure Paper.Overlap).map Subtype.val) S=
    ENNReal.ofReal β*((μ:Measure Paper.Overlap).map Subtype.val) S
  rw [←ENNReal.ofReal_coe_nnreal (p:=c)]
  rfl

theorem scalar_root_density_ge_linear_slope (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (k T : ℝ) (hT : T∈Ioo (0:ℝ) q)
    (hgrowth : ∀r∈Icc (0:ℝ) T,k*r≤β*parisiCDF μ r) :
    k≤β*parisiSmoothDensity β μ q 0 := by
  let ρ:=parisiSmoothDensity β μ q 0
  have hd:=(momentQuotient_hasDerivAt_endpoints_of_support_interval
    β hβ.ne' μ hmin q hq.1 hq.2.le hsupp).1.Ioi_of_Ici
  have hl : Tendsto (slope (momentQuotient β μ) 0) (𝓝[>] 0) (𝓝 ρ):=
    (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ)∉Ioi (0:ℝ) from by simp)).mp hd
  apply ge_of_tendsto (hl.const_mul β)
  filter_upwards [Ioo_mem_nhdsGT hT.1] with r hr
  have hh:=hgrowth r ⟨hr.1.le,hr.2.le⟩
  have hc:=parisiCDF_eq_momentQuotient_on_support_interval β hβ.ne' μ hmin q hq.1 hq.2.le hsupp r
    ⟨hr.1.le,hr.2.trans hT.2⟩
  simp only [slope_def_field,momentQuotient_initial_zero,sub_zero]
  rw [←hc,←mul_div_assoc]
  exact (le_div_iff₀ hr.1).mpr hh

theorem scalar_root_density_measure_lower_of_linear_growth (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (k T₀ : ℝ) (hk : 0<k) (hT₀ : T₀∈Ioo (0:ℝ) q)
    (hgrowth : ∀r∈Icc (0:ℝ) T₀,k*r≤β*parisiCDF μ r) :
    ∃T : ℝ,T∈Ioc (0:ℝ) T₀ ∧
      ENNReal.ofReal (k/2) • volume.restrict (Icc (0:ℝ) T)≤
        (scalarTrialStieltjes β hβ.le 0 μ).measure.restrict (Icc (0:ℝ) T) := by
  let ρ:=parisiSmoothDensity β μ q
  have hρ:= (parisiSmoothDensity_regular_of_support_interval β hβ.ne' μ hmin q hq.1 hq.2.le hsupp).1.continuousOn
  have hkρ:=scalar_root_density_ge_linear_slope β hβ μ hmin q hq hsupp k T₀ hT₀ hgrowth
  have hd : k/(2*β)<ρ 0 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hβ)).mpr
    dsimp only [ρ] at *
    nlinarith
  have hev : ∀ᶠx in 𝓝[Icc (0:ℝ) q] (0:ℝ),k/(2*β)<ρ x:=
    (hρ 0 ⟨le_rfl,hq.1.le⟩).eventually (eventually_gt_nhds hd)
  obtain ⟨U,hU,hsub⟩:=mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
  obtain ⟨e,he,hball⟩:=Metric.mem_nhds_iff.mp hU
  let T:=min T₀ (e/2)
  have hT : 0<T:=lt_min hT₀.1 (half_pos he)
  have hTT₀ : T≤T₀:=min_le_left _ _
  have hTq : T<q:=hTT₀.trans_lt hT₀.2
  have hlower : ∀x∈Icc (0:ℝ) T,k/2≤β*ρ x := by
    intro x hx
    have hxU : x∈U := hball (by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
      exact (hx.2.trans (min_le_right _ _)).trans_lt (half_lt_self he))
    have hh:=hsub ⟨hxU,⟨hx.1,hx.2.trans hTq.le⟩⟩
    have hc:=(div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hβ)).mp hh
    linarith
  have hreal:=parisiMeasure_eq_density_add_atom_of_support_interval β hβ.ne' μ hmin q hq.1 hq.2.le hsupp
  have hr : ((μ:Measure Paper.Overlap).map Subtype.val).restrict (Icc (0:ℝ) T)=
      (volume.restrict (Icc (0:ℝ) T)).withDensity (fun x=>ENNReal.ofReal (ρ x)) := by
    rw [hreal,Measure.restrict_add,Measure.restrict_smul,restrict_dirac' measurableSet_Icc,
      ite_eq_right (by simp only [mem_Icc];intro h;linarith [h.2]),smul_zero,add_zero,
      restrict_withDensity measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
    rw [inter_eq_left.mpr (show Icc (0:ℝ) T⊆Ico (0:ℝ) q from fun x hx=>⟨hx.1,hx.2.trans_lt hTq⟩)]
  refine ⟨T,⟨hT,hTT₀⟩,?_⟩
  rw [scalar_zero_floor_free_measure_eq β hβ.le μ,Measure.restrict_smul,hr,
    ←withDensity_smul' (ENNReal.ofReal β) _ ENNReal.ofReal_ne_top,←withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [Pi.smul_apply,smul_eq_mul,←ENNReal.ofReal_mul hβ.le]
  exact ENNReal.ofReal_le_ofReal (hlower x hx)

theorem scalar_root_density_measure_lower (β : ℝ) (hβ : 1<β) :
    ∃k T₀ T : ℝ,0<k ∧ 0<T₀ ∧ T₀<1 ∧ T∈Ioc (0:ℝ) T₀ ∧
      (∀r∈Icc (0:ℝ) T₀,k*r≤β*parisiCDF (parisiMinimizer β 0) r) ∧
      ENNReal.ofReal (k/2) • volume.restrict (Icc (0:ℝ) T)≤
        (scalarTrialStieltjes β (zero_le_one.trans hβ.le) 0 (parisiMinimizer β 0)).measure.restrict (Icc (0:ℝ) T) := by
  have hβ0 : 0<β:=zero_lt_one.trans hβ
  obtain ⟨q,hq,hsupp⟩:=minimizer_full_support β hβ _ (isParisiMinimizer_selected β 0)
  obtain ⟨k,T₀,hk,hT₀,hgrowth⟩:=scalar_minimizer_cdf_linear_lower β hβ0 _ (isParisiMinimizer_selected β 0) q hq hsupp
  obtain ⟨T,hT,hmeasure⟩:=scalar_root_density_measure_lower_of_linear_growth β hβ0 _
    (isParisiMinimizer_selected β 0) q hq hsupp k T₀ hk hT₀ hgrowth
  exact ⟨k,T₀,T,hk,hT₀.1,hT₀.2.trans hq.2,hT,hgrowth,hmeasure⟩

end QuantitativeFollowup
