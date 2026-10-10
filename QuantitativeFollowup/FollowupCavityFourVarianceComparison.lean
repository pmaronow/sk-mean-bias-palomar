module
public import QuantitativeFollowup.FollowupCavityFourEndpointContact
public import QuantitativeFollowup.FollowupCavityFourNativeIncrement
public import QuantitativeFollowup.FollowupCavityFourMomentRegularity
public import QuantitativeFollowup.FollowupCavityCubicSupremum
public import QuantitativeFollowup.SupportingSourceNormalization
public import QuantitativePaper.VectorReplicaDefectMeasurability

@[expose] public section

/-! Coefficient-one integrated comparison for the actual native cavity
rest observable. Streaming, minimizer contact and site symmetry are all
consumed as proved model identities, not as estimate premises. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n:ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavitySelectedSpinOverlap_erased_last (σ τ:Configuration (n+1)) :
    cavitySelectedSpinOverlap (Finset.univ.erase (Fin.last n)) σ τ=
      cavityRestOverlap n σ τ := by
  unfold cavitySelectedSpinOverlap cavityRestOverlap
  simp only [Finset.card_erase_of_mem (Finset.mem_univ (Fin.last n)),Finset.card_univ,
    Fintype.card_fin,Nat.add_sub_cancel]
  congr 1
  have h1:=Finset.sum_erase_add (Finset.univ:Finset (Fin (n+1)))
    (fun i=>Paper.spinSign (σ i)*Paper.spinSign (τ i)) (Finset.mem_univ (Fin.last n))
  have h2:=Fin.sum_univ_castSucc (fun i:Fin (n+1)=>Paper.spinSign (σ i)*Paper.spinSign (τ i))
  linarith

theorem variance_vectorMeasureSelfSquare_eq_marked (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (ht:t≤1) (q:Paper.Overlap) :
    variance (vectorMeasureSelfSquare (n:=n) μ β t ht q) (vectorMeasureDisorderTilt μ β t a)=
      variance (vectorSelfOverlap (n:=n) μ β t ht q) (vectorMeasureSpinPathLaw μ β t a ht) := by
  have hm:Measurable (vectorMeasureSelfSquare (n:=n) μ β t ht q):=
    (((adapted_vectorMeasureSpinMean μ β t ht q).mono
      ((vectorBrownianFiltration n).le _) le_rfl).norm.pow_const 2).div_const _
  have h:=variance_map (μ:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht)
    hm.aemeasurable measurable_fst.aemeasurable
  rw [(measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht).map_eq] at h
  exact h

theorem integrable_variance_vectorSelfOverlap (hn:0<n) (μ:Paper.ParisiMeasure)
    (β t a:ℝ) (ht:t≤1) (ν:Measure Paper.Overlap) [IsFiniteMeasure ν] :
    Integrable (fun q:Paper.Overlap=>variance (vectorSelfOverlap (n:=n) μ β t ht q)
      (vectorMeasureSpinPathLaw μ β t a ht)) ν := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  apply (integrable_const (1:ℝ)).mono'
    (measurable_variance_vectorSelfOverlap hn μ β t a ht).aestronglyMeasurable
  exact .of_forall fun q=>by
    rw [Real.norm_of_nonneg (variance_nonneg _ _)]
    have h:=variance_le_sq_of_bounded (μ:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht)
      (.of_forall (vectorSelfOverlap_bounds hn μ β t ht q))
      (measurable_vectorSelfOverlap μ β t ht q).aemeasurable
    norm_num at h
    linarith

theorem followup_cavity_four_native_variance_comparison (hn:0<n)
    (μ:Paper.ParisiMeasure) (β ρ a:ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (ha:a∈Ioo (0:ℝ) 1) (hμ:μ∈scalarFloor a)
    (hmin:∀ν∈scalarFloor a,vectorMeasureFunctional (n+1) μ β (1-ρ) a≤
      vectorMeasureFunctional (n+1) ν β (1-ρ) a) :
    (∫q:Paper.Overlap,variance (fun sample=>anisotropicSelectedMeanSquare
      (Finset.univ.erase (Fin.last n)) (anisotropicProcessMagnetization
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q sample))
      (anisotropicMeasureSampleLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)∂parisiFreeMeasure μ a)≤
      followupSourceMeanVarianceIntegral (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1])+
        720*β^2*Real.exp (21*β^2)*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ+
        1/(4*(n:ℝ)^2) := by
  let ν:=parisiFreeMeasure μ a
  let D0:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let D1:=followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩
  let J:Finset (Fin (n+1)):=Finset.univ.erase (Fin.last n)
  let Φ:=fun (D:AnisotropicSpinModel (n+1)) (q:Paper.Overlap)=>
    ∫z,(cavitySelectedSpinOverlap J z.2.1.1 z.2.1.2-(q:ℝ))*
      (cavitySelectedSpinOverlap J z.2.2.1 z.2.2.2-(q:ℝ))∂cavityFourDescendantLaw D μ a q
  let V:=fun q:Paper.Overlap=>variance (vectorSelfOverlap (n:=n+1) μ β (1-ρ)
    (by linarith[hρ.1]) q) (vectorMeasureSpinPathLaw μ β (1-ρ) a (by linarith[hρ.1]))
  let C:=360*β^2*Real.exp (21*β^2)
  let c:=1/(4*(n:ℝ)^2)
  have hfloor:a≤Paper.parisiCDF μ 0:=scalarFloor_cdf_lower hμ (by norm_num)
  have hi0:=integrable_cavityFourDescendant_centered_product D0 μ a J ν
  have hi1:=integrable_cavityFourDescendant_centered_product D1 μ a J ν
  have hiV:Integrable V ν:=integrable_variance_vectorSelfOverlap (by omega) μ β (1-ρ) a (by linarith[hρ.1]) ν
  have hiχ:=integrable_cavityCubicPairMoment D0 μ a
  have hvariance:=integral_mono
    (integrable_cavitySelectedSelfOverlap_variance D0 μ a J ν) hi0
    (fun q=>cavityFourDescendant_variance_le D0 μ a q J)
  have hstream (q:Paper.Overlap):Φ D0 q≤Φ D1 q+C*(cavityThirdMoment D0 μ a+cavityCubicPairMoment D0 μ a q) := by
    have h:=followupCavityFourDescendant_sub_le hn β ρ hβ hρ μ a ⟨ha.1.le,ha.2.le⟩ hfloor
      q 0 ⟨le_rfl,zero_le_one⟩ 1 0 ⟨zero_le_one,le_rfl⟩ ⟨le_rfl,zero_le_one⟩
    dsimp only at h
    simp only [zero_sub,abs_neg,abs_one,mul_one] at h
    have he:∀D,Φ D q=∫z,cavityFourRestPairProduct n q z.2∂cavityFourDescendantLaw D μ a q := by
      intro D
      simp only [Φ,J,cavitySelectedSpinOverlap_erased_last,cavityFourRestPairProduct]
    rw [←he D0,←he D1] at h
    have hh:=le_abs_self (Φ D0 q-Φ D1 q)
    dsimp only [C,D0,D1] at *
    linarith
  have hcomparison:=integral_mono hi0
    (hi1.add (((integrable_const (cavityThirdMoment D0 μ a)).add hiχ).const_mul C)) hstream
  have hcontact:∀ᵐq∂ν,Φ D1 q≤V q+c := by
    filter_upwards [ν.support_mem_ae] with q hq
    have h:=followup_cavity_one_four_centered_product_le hn μ β ρ a hβ hρ ha hμ hmin q hq
    rw [variance_vectorMeasureSelfSquare_eq_marked] at h
    exact h
  have hendpoint:=integral_mono_ae hi1 (hiV.add (integrable_const c)) hcontact
  have hierr:Integrable (fun q:Paper.Overlap=>C*(cavityThirdMoment D0 μ a+cavityCubicPairMoment D0 μ a q)) ν :=
    by simpa only [Pi.add_apply] using
      (((integrable_const (cavityThirdMoment D0 μ a)).add hiχ).const_mul C)
  simp only [Pi.add_apply] at hcomparison
  rw [integral_add (f:=Φ D1)
    (g:=fun q:Paper.Overlap=>C*(cavityThirdMoment D0 μ a+cavityCubicPairMoment D0 μ a q))
    hi1 hierr,integral_const_mul,
    integral_add (f:=fun _:Paper.Overlap=>cavityThirdMoment D0 μ a)
      (g:=cavityCubicPairMoment D0 μ a) (integrable_const _) hiχ,integral_const] at hcomparison
  simp only [Pi.add_apply] at hendpoint
  rw [integral_add hiV (integrable_const c),integral_const] at hendpoint
  have hmass:ν.real univ≤1 := by
    dsimp only [ν]
    rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith[ha.2])]
    linarith[ha.1]
  have hM:=cavityThirdMoment_nonneg D0 μ a
  have hC:0≤C:=by dsimp only [C];positivity
  have hc:0≤c:=by dsimp only [c];positivity
  have hMc:=mul_le_mul_of_nonneg_right hmass hM
  have hMcC:=mul_le_mul_of_nonneg_left hMc hC
  have hcc:=mul_le_mul_of_nonneg_right hmass hc
  have hsup:=cavityThirdMoment_le_physicalSupremum (n:=n) μ β ρ a hβ hρ
    ⟨ha.1.le,ha.2.le⟩ 0 ⟨le_rfl,zero_le_one⟩
  have hmult:=mul_le_mul_of_nonneg_left hsup hC
  change _≤(∫q,V q∂ν)+720*β^2*Real.exp (21*β^2)*cavityPhysicalCubicSupremum n μ β ρ a hβ hρ+c
  dsimp only [cavityThirdMoment] at hcomparison
  simp only [smul_eq_mul] at hcomparison hendpoint
  dsimp only [C,cavityThirdMoment] at hcomparison hmult hMcC
  dsimp only [ν,Φ,V,D0,J] at hvariance hcomparison hendpoint hMcC hcc hmult ⊢
  nlinarith only [hvariance,hcomparison,hendpoint,hMcC,hcc,hmult]

end QuantitativeFollowup
