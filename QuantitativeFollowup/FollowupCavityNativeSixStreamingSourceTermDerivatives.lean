module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternCellDerivatives
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginComponentDerivative
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginParameterDerivative
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTermwiseSecondBracket

@[expose] public section

/-! Actual parameter derivatives of the fixed original-leaf, original-fresh,
cross, current and independent normalizer source terms. Every supporting
component derivative and Fubini hypothesis is discharged from the genuine
physical model and true normalized marked laws. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem hasDerivWithinAt_nativeStreamingSourceOriginal_parameter_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>∑i : ObservationLeaf T,∑k : ObservationLeaf T,
      nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.original i k) t)
      (∑i : ObservationLeaf T,∑k : ObservationLeaf T,
        (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.original i k)) (Icc (0:ℝ) 1) u := by
  have hi (i : ObservationLeaf T) : HasDerivWithinAt
      (fun t => ∑k : ObservationLeaf T,
        nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.original i k) t)
      (∑k : ObservationLeaf T,
        (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.original i k))
      (Icc (0:ℝ) 1) u := by
    simpa only [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ =>
        hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
          q hq hJ hzero htop T F (.original i k) trivial u hu))
  simpa only [Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hi i))

theorem hasDerivWithinAt_nativeStreamingSourceOriginalFresh_weight_parameter_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (i : ObservationLeaf T) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.originalFresh i o) t))
      (nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.originalFresh i o))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingOriginWeightIntegral_of_components μ a q T a
  · intro v
    exact hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
      q hq hJ hzero htop T F (.originalFresh i (.vertex v)) trivial u hu
  · intro e
    exact hasDerivWithinAt_nativeStreamingPattern_originalFresh_edge_integral_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF i e u hu

theorem hasDerivWithinAt_nativeStreamingSourceCross_parameter_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>nativeStreamingOriginWeightIntegral μ a q T a
        (fun p=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.cross o p) t)))
      (nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>nativeStreamingOriginWeightIntegral μ a q T a
          (fun p=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.cross o p)))) (Icc (0:ℝ) 1) u := by
  apply hasDerivWithinAt_nativeStreamingOriginPairWeightIntegral_of_components
    μ a q T T a a _ _ (Icc (0:ℝ) 1) u hu
  · intro v w
    exact hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
      q hq hJ hzero htop T F (.cross (.vertex v) (.vertex w)) ⟨trivial,trivial⟩ u hu
  · intro v e
    exact hasDerivWithinAt_nativeStreamingPattern_cross_vertex_edge_integral_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF v e u hu
  · intro e w
    exact hasDerivWithinAt_nativeStreamingPattern_cross_edge_vertex_integral_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e w u hu
  · intro e f
    have h := hasDerivWithinAt_nativeStreamingPattern_cross_edges_integral_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e f u hu
    have hi := nativeStreamingPattern_cross_edges_integral_regularities_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e f u hu
    rw [integral_prod_symm _ hi.2] at h
    apply h.congr_of_mem ?_ hu
    intro t ht
    exact (integral_prod_symm _ (nativeStreamingPattern_cross_edges_integral_regularities_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e f t ht).1).symm
  · intro t ht e w
    exact (nativeStreamingPattern_cross_edge_vertex_integral_regularities_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e w t ht).1
  · intro t ht e f
    exact (nativeStreamingPattern_cross_edges_integral_regularities_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e f t ht).1
  · intro e w
    exact (nativeStreamingPattern_cross_edge_vertex_integral_regularities_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e w u hu).2
  · intro e f
    exact (nativeStreamingPattern_cross_edges_integral_regularities_actual
      hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF e f u hu).2

theorem hasDerivWithinAt_nativeStreamingSourceCurrent_parameter_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>nativeStreamingOriginWeightIntegral μ a q T a
      (fun o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
        nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.current o) t))
      (nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
          ((followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.current o)))) (Icc (0:ℝ) 1) u := by
  let B := 7*β^2*((FiniteCascadeGenealogy.leafCount (asGenealogy T)+2:ℕ):ℝ)^2*(2*C)
  have hB : 0≤B := by dsimp [B]; positivity
  have h : HasDerivWithinAt
      (fun t=>nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
          nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.current o) t))
      (nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
          nativeStreamingPatternParameterDerivative β ρ hβ hρ μ a q T F (.current o) u))
      (Icc (0:ℝ) 1) u := by
    apply hasDerivWithinAt_nativeStreamingOriginWeightIntegral μ a q T a
      (fun t o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
        nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.current o) t)
      (fun t o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
        nativeStreamingPatternParameterDerivative β ρ hβ hρ μ a q T F (.current o) t)
      (2*C) B (by positivity) hB
    · intro v t ht
      simpa only [nativeStreamingPatternParameterDerivative,dif_pos ht] using
        (hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
          q hq hJ hzero htop T F (.current (.vertex v)) trivial t ht).const_mul
          (Paper.parisiCDF μ (q v.depth))
    · intro e r hr t ht
      simpa only [nativeStreamingPatternParameterDerivative,dif_pos ht] using
        (hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
          q hq hJ hzero htop T F (.current (.edge e r)) hr t ht).const_mul
          (Paper.parisiCDF μ r)
    · intro e t ht
      simp only [nativeStreamingOriginLevel,nativeStreamingPatternParameterMoment,dif_pos ht]
      exact ((Paper.parisiCDF_measurable μ).comp measurable_subtype_coe).aestronglyMeasurable.mul
        (aestronglyMeasurable_nativeStreamingPatternMoment_current_edge_Ioc
          (followupCavitySpinModel n β ρ hβ hρ t ht) μ a q hq T F e)
    · intro e r hr
      have hzero0 : (0:ℝ)∈Icc (0:ℝ) 1 := by norm_num
      simp only [nativeStreamingOriginLevel,nativeStreamingPatternParameterMoment,dif_pos hzero0,abs_mul,
        abs_of_nonneg (Paper.parisiCDF_nonneg μ r)]
      exact (mul_le_mul (Paper.parisiCDF_le_one μ r)
        (abs_nativeStreamingPatternMoment_le (followupCavitySpinModel n β ρ hβ hρ 0 hzero0)
          μ a q T F C hC hF (.current (.edge e r))) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · intro e r hr t ht
      simp only [nativeStreamingOriginLevel,nativeStreamingPatternParameterDerivative,dif_pos ht,abs_mul,
        abs_of_nonneg (Paper.parisiCDF_nonneg μ r)]
      simpa only [B,abs_mul] using (mul_le_mul (Paper.parisiCDF_le_one μ r)
        (abs_nativeStreamingPattern_source_derivative_le hn β ρ hβ hρ μ a ha hfloor
          q hq hJ hzero htop T F C hC hF (.current (.edge e r)) hr t ht)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · exact hu
  simpa only [nativeStreamingPatternParameterDerivative,dif_pos hu] using h

theorem hasDerivWithinAt_nativeStreamingSourceNormalizer_parameter_actual
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t=>a*∫l,nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (.normalizer l) t ∂parisiFreeMeasure μ a)
      (a*∫l,(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (.normalizer l) ∂parisiFreeMeasure μ a) (Icc (0:ℝ) 1) u :=
  (hasDerivWithinAt_nativeStreamingPattern_normalizer_integral_actual hn β ρ hβ hρ μ a ha hfloor q hq hJ hzero htop T F C hC hF u hu).const_mul a

end QuantitativeFollowup
