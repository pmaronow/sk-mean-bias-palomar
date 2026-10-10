module
public import QuantitativeFollowup.FollowupCavityThirdRestMomentThermalMoments
public import QuantitativeFollowup.FollowupCavityThreeEndpointPhysical
public import QuantitativeFollowup.FollowupCavityThirdMoment
public import FourPapersCommon.VectorCubicBounds

@[expose] public section

/-! Actual two-fresh endpoint transport and the one-site cubic error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem cavityThreeDescendantLaw_pair_projection (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:Paper.Overlap) :
    (cavityThreeDescendantLaw D μ a q).map (Prod.map id Prod.fst)=
      anisotropicFreshTerminalPairLaw D μ a q := by
  unfold cavityThreeDescendantLaw anisotropicFreshTerminalPairLaw
  rw [←Measure.compProd_map measurable_fst,←Kernel.fst_eq,Kernel.fst_prod]

theorem cavityVectorThreeDescendantLaw_pair_projection (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (ht:t≤1) (q:Paper.Overlap) :
    (cavityVectorThreeDescendantLaw (n:=n) μ β t a ht q).map (Prod.map id Prod.fst)=
      vectorConditionalReplicaLaw (n:=n) μ β t a ht q := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  unfold cavityVectorThreeDescendantLaw vectorConditionalReplicaLaw
  rw [←Measure.compProd_map measurable_fst,←Kernel.fst_eq,Kernel.fst_prod]

theorem followup_cavity_one_cubic_pair_integral (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (q:Paper.Overlap) :
    cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a q=
      ∫z,|cavityRestOverlap n z.2.1 z.2.2-(q:ℝ)|^3
        ∂vectorConditionalReplicaLaw μ β (1-ρ) a (by linarith[hρ.1]) q := by
  let F:=fun z:Configuration (n+1)×Configuration (n+1)=>|cavityRestOverlap n z.1 z.2-(q:ℝ)|^3
  let D:=followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩
  rw [cavityCubicPairMoment_eq_fresh]
  have h1:=integral_map (μ:=anisotropicFreshTerminalPairLaw D μ a q)
    measurable_snd.aemeasurable (measurable_of_finite F).aestronglyMeasurable
  have h2:=integral_map (μ:=cavityThreeDescendantLaw D μ a q)
    (measurable_id.prodMap measurable_fst).aemeasurable
    ((measurable_of_finite F).comp measurable_snd).aestronglyMeasurable
  rw [cavityThreeDescendantLaw_pair_projection] at h2
  have h3:=followup_cavity_one_three_descendant_integral hn μ β ρ a hβ hρ q
    (fun z=>F z.1)
  have h4:=integral_map (μ:=cavityVectorThreeDescendantLaw (n:=n+1) μ β (1-ρ) a
    (by linarith[hρ.1]) q) (measurable_id.prodMap measurable_fst).aemeasurable
    ((measurable_of_finite F).comp measurable_snd).aestronglyMeasurable
  rw [cavityVectorThreeDescendantLaw_pair_projection] at h4
  exact h1.trans (h2.trans (h3.trans h4.symm))

theorem cavityRestOverlap_full_difference_le (hn:0<n) (σ τ:Configuration (n+1)) :
    |cavityRestOverlap n σ τ-overlap (n+1) σ τ|≤2/((n+1:ℕ):ℝ) := by
  have hnR:(n:ℝ)≠0:=by positivity
  have hNR:((n+1:ℕ):ℝ)≠0:=by positivity
  have he : cavityRestOverlap n σ τ-overlap (n+1) σ τ=
      (cavityRestOverlap n σ τ-Paper.spinSign (σ (Fin.last n))*Paper.spinSign (τ (Fin.last n)))/
        ((n+1:ℕ):ℝ) := by
    unfold cavityRestOverlap overlap
    rw [Fin.sum_univ_castSucc]
    field_simp
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  rw [he,abs_div,abs_of_pos (by positivity : 0<((n+1:ℕ):ℝ))]
  apply (div_le_div_iff_of_pos_right (by positivity)).mpr
  have hs (b:Bool) : |Paper.spinSign b|=1 := by cases b <;> norm_num [Paper.spinSign]
  have hb:=abs_sub (cavityRestOverlap n σ τ)
    (Paper.spinSign (σ (Fin.last n))*Paper.spinSign (τ (Fin.last n)))
  rw [abs_mul,hs,hs,mul_one] at hb
  linarith [cavityRestOverlap_abs_le_one n σ τ]

theorem cavityRestOverlap_centered_cubic_pointwise (hn:0<n)
    (σ τ:Configuration (n+1)) (S q:ℝ) :
    |cavityRestOverlap n σ τ-q|^3≤
      16*|overlap (n+1) σ τ-S|^3+16*|S-q|^3+32/((n+1:ℕ):ℝ)^3 := by
  have h1:=norm_add_cube_le (overlap (n+1) σ τ-q)
    (cavityRestOverlap n σ τ-overlap (n+1) σ τ)
  have h2:=norm_add_cube_le (overlap (n+1) σ τ-S) (S-q)
  simp only [Real.norm_eq_abs] at h1 h2
  have he1 : overlap (n+1) σ τ-q+(cavityRestOverlap n σ τ-overlap (n+1) σ τ)=
    cavityRestOverlap n σ τ-q := by ring
  have he2 : overlap (n+1) σ τ-S+(S-q)=overlap (n+1) σ τ-q := by ring
  rw [he1] at h1
  rw [he2] at h2
  have h3:=pow_le_pow_left₀ (abs_nonneg _) (cavityRestOverlap_full_difference_le hn σ τ) 3
  have hp : (2/((n+1:ℕ):ℝ))^3=8/((n+1:ℕ):ℝ)^3 := by ring
  rw [hp] at h3
  calc
    _≤4*(|overlap (n+1) σ τ-q|^3+|cavityRestOverlap n σ τ-overlap (n+1) σ τ|^3):=h1
    _≤4*(4*(|overlap (n+1) σ τ-S|^3+|S-q|^3)+8/((n+1:ℕ):ℝ)^3):=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by norm_num)
    _=_:=by ring

theorem followup_cavity_one_cubic_pair_thermal_le (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (q:Paper.Overlap) :
    cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a q≤
      64*(foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
        foundationMeanCovariance (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q)+
      16*(∫z,|vectorSelfOverlap (n:=n+1) μ β (1-ρ) (by linarith[hρ.1]) q z-(q:ℝ)|^3
        ∂vectorMeasureSpinPathLaw μ β (1-ρ) a (by linarith[hρ.1]))+
      32/((n+1:ℕ):ℝ)^3 := by
  let ht:1-ρ<1:=by linarith[hρ.1]
  let P:=vectorConditionalReplicaLaw (n:=n+1) μ β (1-ρ) a ht.le q
  let S:=vectorSelfOverlap (n:=n+1) μ β (1-ρ) ht.le q
  let R:=fun z:VectorMarkedSample (n+1)×(Configuration (n+1)×Configuration (n+1))=>
    overlap (n+1) z.2.1 z.2.2
  let X:=fun z:VectorMarkedSample (n+1)×(Configuration (n+1)×Configuration (n+1))=>R z-S z.1
  let Y:=fun z:VectorMarkedSample (n+1)×(Configuration (n+1)×Configuration (n+1))=>S z.1-(q:ℝ)
  let Z:=fun z:VectorMarkedSample (n+1)×(Configuration (n+1)×Configuration (n+1))=>
    cavityRestOverlap n z.2.1 z.2.2-(q:ℝ)
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n+1) μ β (1-ρ) a ht.le
  have hmS:Measurable S:=measurable_vectorSelfOverlap μ β (1-ρ) ht.le q
  have hmR:Measurable R:=(measurable_of_finite (fun z:Configuration (n+1)×Configuration (n+1)=>
    overlap (n+1) z.1 z.2)).comp measurable_snd
  have hmX:Measurable X:=hmR.sub (hmS.comp measurable_fst)
  have hmY:Measurable Y:=(hmS.comp measurable_fst).sub measurable_const
  have hmZ:Measurable Z:=((measurable_of_finite (fun z:Configuration (n+1)×Configuration (n+1)=>
    cavityRestOverlap n z.1 z.2)).comp measurable_snd).sub measurable_const
  have hX (z):|X z|≤2 := by
    have hR:=abs_le.mp (abs_vectorOverlap_le_one (by omega) z.2.1 z.2.2)
    have hS:=vectorSelfOverlap_bounds (by omega) μ β (1-ρ) ht.le q z.1
    rw [abs_le]; constructor <;> dsimp only [X,R,S] <;> linarith
  have hY (z):|Y z|≤1 := by
    exact norm_vectorCenteredSelfOverlap_le_one (by omega) μ β (1-ρ) ht.le q z.1
  have hZ (z):|Z z|≤2 := by
    have hR:=abs_le.mp (cavityRestOverlap_abs_le_one n z.2.1 z.2.2)
    rw [abs_le]; constructor <;> dsimp only [Z] <;> linarith[q.property.1,q.property.2]
  have hi {f:VectorMarkedSample (n+1)×(Configuration (n+1)×Configuration (n+1))→ℝ}
      (hm:Measurable f) (B:ℝ) (hb:∀z,|f z|≤B) : Integrable (fun z=>|f z|^3) P := by
    apply (integrable_const (B^3)).mono' (hm.abs.pow_const 3).aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb z) 3
  have hiX:=hi hmX 2 hX
  have hiY:=hi hmY 1 hY
  have hiZ:=hi hmZ 2 hZ
  have hh:=integral_mono hiZ (((hiX.const_mul 16).add (hiY.const_mul 16)).add
      (integrable_const (32/((n+1:ℕ):ℝ)^3))) (fun z=>
    cavityRestOverlap_centered_cubic_pointwise hn z.2.1 z.2.2 (S z.1) q)
  simp only [Pi.add_apply] at hh
  have hadd:=integral_add ((hiX.const_mul 16).add (hiY.const_mul 16))
    (integrable_const (32/((n+1:ℕ):ℝ)^3))
  have hfirst:=integral_add (hiX.const_mul 16) (hiY.const_mul 16)
  simp only [Pi.add_apply] at hadd hfirst
  rw [hadd,hfirst] at hh
  simp only [integral_const_mul,integral_const,probReal_univ,one_smul] at hh
  have hbase:P.map Prod.fst=vectorMeasureSpinPathLaw (n:=n+1) μ β (1-ρ) a ht.le := by
    change (vectorMeasureSpinPathLaw (n:=n+1) μ β (1-ρ) a ht.le⊗ₘ
      (vectorConditionalTerminalSpinKernel μ β (1-ρ) a ht.le q×ₖ
        vectorConditionalTerminalSpinKernel μ β (1-ρ) a ht.le q)).fst=_
    rw [Measure.fst_compProd]
  have hy:=integral_map (μ:=P) (f:=fun z:VectorMarkedSample (n+1)=>|S z-(q:ℝ)|^3)
    measurable_fst.aemeasurable
    ((hmS.sub measurable_const).abs.pow_const 3).aestronglyMeasurable
  rw [hbase] at hy
  have hx:=vectorConditionalReplica_centered_cubic_thermal_le (n:=n+1) (by omega) μ β (1-ρ) a hβ.ne' ht q
  have hA:=foundationThermalTrace_nonneg (n:=n+1) μ β (1-ρ) a ht.le q
  rw [followup_cavity_one_cubic_pair_integral hn μ β ρ a hβ hρ q]
  change (∫z,|Z z|^3∂P)≤_
  have hy' : (∫z,|Y z|^3∂P)=∫z,|S z-(q:ℝ)|^3
      ∂vectorMeasureSpinPathLaw (n:=n+1) μ β (1-ρ) a ht.le := hy.symm
  rw [hy'] at hh
  change (∫z,|X z|^3∂P)≤_ at hx
  linarith

end QuantitativeFollowup
