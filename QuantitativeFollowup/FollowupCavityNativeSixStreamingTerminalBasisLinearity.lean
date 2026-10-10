module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalBasisLinearityMoments

@[expose] public section

/-! Raw six-term source recombination in the finite terminal basis. The
probability law, both old-tree attachment weights and independent normalizer
stay fixed. This proof does not divide by a physical coupling. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem finite_test_bound (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    ∃C : ℝ,0≤C∧∀σ,|F σ|≤C := by
  classical
  refine ⟨∑σ,|F σ|,Finset.sum_nonneg (fun _ _=>abs_nonneg _),?_⟩
  intro σ
  exact Finset.single_le_sum (f:=fun τ=>|F τ|) (fun _ _=>abs_nonneg _) (Finset.mem_univ σ)

private theorem moment_integrable {X : Type*} [MeasurableSpace X]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (M : Measure X) [IsFiniteMeasure M] (P : X→NativeStreamingAttachmentPattern T)
    (hm : AEStronglyMeasurable (fun x=>nativeStreamingPatternMoment D μ a q T F (P x)) M) :
    Integrable (fun x=>nativeStreamingPatternMoment D μ a q T F (P x)) M := by
  obtain ⟨C,hC,hF⟩ := finite_test_bound T F
  apply (integrable_const (2*C)).mono' hm
  exact .of_forall fun x=>by
    simpa only [Real.norm_eq_abs] using abs_nativeStreamingPatternMoment_le D μ a q T F C hC hF (P x)

private theorem masked_integrable {X : Type*} [MeasurableSpace X]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (M : Measure X) [IsFiniteMeasure M] (P : X→NativeStreamingAttachmentPattern T)
    (mask : X→Prop)
    (hm : AEStronglyMeasurable (fun x=>if mask x then nativeStreamingPatternMoment D μ a q T F (P x) else 0) M) :
    Integrable (fun x=>if mask x then nativeStreamingPatternMoment D μ a q T F (P x) else 0) M := by
  classical
  obtain ⟨C,hC,hF⟩ := finite_test_bound T F
  apply (integrable_const (2*C)).mono' hm
  exact .of_forall fun x=>by
    by_cases hx : mask x
    · simpa only [if_pos hx,Real.norm_eq_abs] using abs_nativeStreamingPatternMoment_le D μ a q T F C hC hF (P x)
    · simp only [if_neg hx,norm_zero]; positivity

private theorem cross_fixed_edge_slice_integrable
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (e f : NativeStreamingEdge T) (r : Paper.Overlap)
    (hr : r∈Ioc (q (e.depth+1)) (q e.depth)) :
    Integrable (fun l=>nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) (.edge f l)))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (f.depth+1)) (q f.depth))) := by
  let c := finiteCascadeCommonPathDepth T (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
  let G := fun z : Paper.Overlap×Paper.Overlap=>nativeStreamingDefectSpinTest T F
    (nativeStreamingSelectedCommonClock c e.depth f.depth z.1 z.2 (q c))
  have hG σ : Continuous (fun z=>G z σ) :=
    continuous_nativeStreamingEdgePairDefectSpinTest T F c e.depth f.depth (q c) σ
  have hsection : Measurable (fun l : Paper.Overlap=>(r,l)) := measurable_const.prodMk measurable_id
  have hm := (measurable_nativeStreamingEdgePairFamilyHalfClosedMoment D μ a q hq T e f ∅ G hG).comp
    hsection
  apply moment_integrable D μ a q T F _ _ (hm.aestronglyMeasurable.congr ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
  have hcond : nativeStreamingEdgePairHalfClosedCondition q e f (r,l) := ⟨hr,hl⟩
  simp only [Function.comp_def,nativeStreamingEdgePairFamilyHalfClosedMoment,hcond,ite_true,
    nativeStreamingPatternMoment,nativeStreamingOriginCrossProbability,nativeStreamingOriginCommonClock,G,c]

private theorem future_fixed_edge_slice_integrable
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (e : NativeStreamingEdge T) (r : Paper.Overlap)
    (hr : r∈Ioc (q (e.depth+1)) (q e.depth)) (j : ℕ) :
    Integrable (fun l=>if r<l then nativeStreamingPatternMoment D μ a q T F (.future (.edge e r) j l) else 0)
      ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))) := by
  classical
  let G := fun z : Paper.Overlap×Paper.Overlap=>nativeStreamingDefectSpinTest T F z.2
  have hG σ : Continuous (fun z=>G z σ) :=
    continuous_nativeStreamingDefectSpinTest_clock T F _ continuous_snd σ
  have hsection : Measurable (fun l : Paper.Overlap=>(r,l)) := measurable_const.prodMk measurable_id
  have hm := (measurable_nativeStreamingEdgeFutureFamilyHalfClosedMoment D μ a q hq T e j ∅ G hG).comp
    hsection
  apply masked_integrable D μ a q T F _ _ _ (hm.aestronglyMeasurable.congr ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
  simp only [Function.comp_def,nativeStreamingEdgeFutureFamilyHalfClosedMoment,nativeStreamingEdgeFutureHalfClosedCondition,
    hr.1,hr.2,hl.1,hl.2,true_and,nativeStreamingPatternMoment,nativeStreamingOriginFutureProbability,G]

private theorem masked_basis_integral {X : Type*} [MeasurableSpace X]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (M : Measure X) (P : X→NativeStreamingAttachmentPattern T) (mask : X→Prop)
    (hi : ∀σ,Integrable (fun x=>if mask x then
      nativeStreamingPatternMoment D μ a q T (fun τ=>if τ=σ then 1 else 0) (P x) else 0) M) :
    (∫x,if mask x then nativeStreamingPatternMoment D μ a q T F (P x) else 0∂M)=
      ∑σ,F σ*(∫x,if mask x then nativeStreamingPatternMoment D μ a q T
        (fun τ=>if τ=σ then 1 else 0) (P x) else 0∂M) := by
  classical
  have hb x : (if mask x then nativeStreamingPatternMoment D μ a q T F (P x) else 0)=
      ∑σ,F σ*(if mask x then nativeStreamingPatternMoment D μ a q T
        (fun τ=>if τ=σ then 1 else 0) (P x) else 0) := by
    by_cases hx : mask x
    · simp only [if_pos hx]
      exact nativeStreamingPatternMoment_terminal_basis D μ a q T F (P x)
    · simp only [if_neg hx,mul_zero,Finset.sum_const_zero]
  rw [integral_congr_ae (.of_forall hb),integral_finsetSum _ (fun σ _=>(hi σ).const_mul (F σ))]
  simp_rw [integral_const_mul]

private theorem cross_inner_basis
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (o : NativeStreamingOrigin T)
    (hi : ∀σ e,Integrable (fun r=>nativeStreamingPatternMoment D μ a q T
      (fun τ=>if τ=σ then 1 else 0) (.cross o (.edge e r)))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))) :
    nativeStreamingOriginWeightIntegral μ a q T a (fun p=>nativeStreamingPatternMoment D μ a q T F (.cross o p))=
      ∑σ,F σ*nativeStreamingOriginWeightIntegral μ a q T a (fun p=>nativeStreamingPatternMoment D μ a q T
        (fun τ=>if τ=σ then 1 else 0) (.cross o p)) := by
  classical
  have hf : (fun p=>nativeStreamingPatternMoment D μ a q T F (.cross o p))=
      fun p=>∑σ,F σ*nativeStreamingPatternMoment D μ a q T (fun τ=>if τ=σ then 1 else 0) (.cross o p) :=
    funext fun p=>nativeStreamingPatternMoment_terminal_basis D μ a q T F (.cross o p)
  rw [hf,nativeStreamingOriginWeightIntegral_sum μ a q T a _ (fun σ e=>(hi σ e).const_mul (F σ))]
  simp_rw [nativeStreamingOriginWeightIntegral_const_mul]

private theorem future_inner_basis
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (o : NativeStreamingOrigin T)
    (hi : ∀σ j,Integrable (fun l=>if nativeStreamingOriginLevel q o<l then
      nativeStreamingPatternMoment D μ a q T (fun τ=>if τ=σ then 1 else 0) (.future o j l) else 0)
      ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))) :
    nativeStreamingPatternFutureIntegral D μ a q T F o=
      ∑σ,F σ*nativeStreamingPatternFutureIntegral D μ a q T (fun τ=>if τ=σ then 1 else 0) o := by
  classical
  unfold nativeStreamingPatternFutureIntegral
  have hh (j : ℕ) := masked_basis_integral D μ a q T F
    ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))
    (fun l=>.future o j l) (fun l=>nativeStreamingOriginLevel q o<l) (fun σ=>hi σ j)
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Finset.mul_sum]

private theorem cross_outer_edge_integrable
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (e : NativeStreamingEdge T) :
    Integrable (fun r=>nativeStreamingOriginWeightIntegral μ a q T a
      (fun p=>nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) p)))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  apply (nativeStreamingOriginWeightIntegral_parameter_fubini
    ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) μ a q T a
    (fun r p=>nativeStreamingPatternMoment D μ a q T F (.cross (.edge e r) p)) ?_ ?_).1
  · intro v
    exact moment_integrable D μ a q T F _ _
      (aestronglyMeasurable_nativeStreamingPatternMoment_cross_edge_vertex_Ioc D μ a q hq T F e v)
  · intro f
    exact moment_integrable D μ a q T F _ _
      (aestronglyMeasurable_nativeStreamingPatternMoment_cross_edges_Ioc_prod D μ a q hq T F e f)

private theorem future_outer_edge_integrable
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (e : NativeStreamingEdge T) :
    Integrable (fun r=>nativeStreamingPatternFutureIntegral D μ a q T F (.edge e r))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))) := by
  classical
  apply integrable_finsetSum _
  intro j _
  have hi := masked_integrable D μ a q T F
    (((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))).prod
      ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))))
    (fun z=>.future (.edge e z.1) j z.2) (fun z=>z.1<z.2)
    (aestronglyMeasurable_nativeStreamingPatternMoment_future_edge_Ioc_prod D μ a q hq T F e j)
  exact hi.integral_prod_left

theorem nativeStreamingSourceSixBracket_terminal_basis
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    nativeStreamingSourceSixBracket D μ a q T F=
      ∑σ,F σ*nativeStreamingSourceSixBracket D μ a q T (fun τ=>if τ=σ then 1 else 0) := by
  classical
  have hO : nativeStreamingSourceOriginalTerm D μ a q T F=
      ∑σ,F σ*nativeStreamingSourceOriginalTerm D μ a q T (fun τ=>if τ=σ then 1 else 0) := by
    simp only [nativeStreamingSourceOriginalTerm]
    have hb i k := nativeStreamingPatternMoment_terminal_basis D μ a q T F (.original i k)
    simp_rw [hb]
    have hcomm (i : ObservationLeaf T) :
        (∑k : ObservationLeaf T,∑σ,F σ*nativeStreamingPatternMoment D μ a q T
          (fun τ=>if τ=σ then 1 else 0) (.original i k))=
        ∑σ,∑k : ObservationLeaf T,F σ*nativeStreamingPatternMoment D μ a q T
          (fun τ=>if τ=σ then 1 else 0) (.original i k) := Finset.sum_comm
    simp_rw [hcomm]
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum]
  have hOF : nativeStreamingSourceOriginalFreshTerm D μ a q T F=
      ∑σ,F σ*nativeStreamingSourceOriginalFreshTerm D μ a q T (fun τ=>if τ=σ then 1 else 0) := by
    simp only [nativeStreamingSourceOriginalFreshTerm]
    have hb i : nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>nativeStreamingPatternMoment D μ a q T F (.originalFresh i o))=
        ∑σ,F σ*nativeStreamingOriginWeightIntegral μ a q T a
          (fun o=>nativeStreamingPatternMoment D μ a q T (fun τ=>if τ=σ then 1 else 0) (.originalFresh i o)) := by
      have hf : (fun o=>nativeStreamingPatternMoment D μ a q T F (.originalFresh i o))=
          fun o=>∑σ,F σ*nativeStreamingPatternMoment D μ a q T (fun τ=>if τ=σ then 1 else 0) (.originalFresh i o) :=
        funext fun o=>nativeStreamingPatternMoment_terminal_basis D μ a q T F (.originalFresh i o)
      rw [hf,nativeStreamingOriginWeightIntegral_sum μ a q T a _
        (fun σ e=>(moment_integrable D μ a q T _ _ _
          (aestronglyMeasurable_nativeStreamingPatternMoment_originalFresh_edge_Ioc D μ a q hq T _ i e)).const_mul (F σ))]
      simp_rw [nativeStreamingOriginWeightIntegral_const_mul]
    simp_rw [hb]
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  have hX : nativeStreamingSourceCrossTerm D μ a q T F=
      ∑σ,F σ*nativeStreamingSourceCrossTerm D μ a q T (fun τ=>if τ=σ then 1 else 0) := by
    unfold nativeStreamingSourceCrossTerm
    rw [nativeStreamingOriginWeightIntegral_congr_ae_edges μ a q T a _
      (fun o=>∑σ,F σ*nativeStreamingOriginWeightIntegral μ a q T a
        (fun p=>nativeStreamingPatternMoment D μ a q T (fun τ=>if τ=σ then 1 else 0) (.cross o p))) ?_ ?_]
    · rw [nativeStreamingOriginWeightIntegral_sum μ a q T a _
        (fun σ e=>(cross_outer_edge_integrable D μ a q hq T _ e).const_mul (F σ))]
      simp_rw [nativeStreamingOriginWeightIntegral_const_mul]
    · intro v
      exact cross_inner_basis D μ a q T F (.vertex v) (fun σ e=>moment_integrable D μ a q T _ _ _
        (aestronglyMeasurable_nativeStreamingPatternMoment_cross_vertex_edge_Ioc D μ a q hq T _ v e))
    · intro e
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact cross_inner_basis D μ a q T F (.edge e r)
        (fun σ f=>cross_fixed_edge_slice_integrable D μ a q hq T _ e f r hr)
  have hC : nativeStreamingSourceCurrentTerm D μ a q T F=
      ∑σ,F σ*nativeStreamingSourceCurrentTerm D μ a q T (fun τ=>if τ=σ then 1 else 0) := by
    unfold nativeStreamingSourceCurrentTerm
    have heq : (fun o=>Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
        nativeStreamingPatternMoment D μ a q T F (.current o))=
        fun o=>∑σ,F σ*(Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
          nativeStreamingPatternMoment D μ a q T (fun τ=>if τ=σ then 1 else 0) (.current o)) := by
      funext o
      rw [nativeStreamingPatternMoment_terminal_basis,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    rw [heq,nativeStreamingOriginWeightIntegral_sum μ a q T a _ ?_]
    · simp_rw [nativeStreamingOriginWeightIntegral_const_mul]
    · intro σ e
      apply Integrable.const_mul
      simp only [nativeStreamingOriginLevel]
      apply (moment_integrable D μ a q T _ _ _
        (aestronglyMeasurable_nativeStreamingPatternMoment_current_edge_Ioc D μ a q hq T _ e)).bdd_mul (c:=1)
        (((Paper.parisiCDF_measurable μ).comp measurable_subtype_coe).aestronglyMeasurable)
      exact .of_forall fun r=>by
        change ‖Paper.parisiCDF μ (r:ℝ)‖≤1
        rw [Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ r)]
        exact Paper.parisiCDF_le_one μ r
  have hFu : nativeStreamingSourceFutureTerm D μ a q T F=
      ∑σ,F σ*nativeStreamingSourceFutureTerm D μ a q T (fun τ=>if τ=σ then 1 else 0) := by
    unfold nativeStreamingSourceFutureTerm
    rw [nativeStreamingOriginWeightIntegral_congr_ae_edges μ a q T a _
      (fun o=>∑σ,F σ*nativeStreamingPatternFutureIntegral D μ a q T (fun τ=>if τ=σ then 1 else 0) o) ?_ ?_]
    · rw [nativeStreamingOriginWeightIntegral_sum μ a q T a _
        (fun σ e=>(future_outer_edge_integrable D μ a q hq T _ e).const_mul (F σ))]
      simp_rw [nativeStreamingOriginWeightIntegral_const_mul]
    · intro v
      exact future_inner_basis D μ a q T F (.vertex v) (fun σ j=>masked_integrable D μ a q T _ _ _ _
        (aestronglyMeasurable_nativeStreamingPatternMoment_future_vertex_Ioc D μ a q hq T _ v j))
    · intro e
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact future_inner_basis D μ a q T F (.edge e r)
        (fun σ j=>future_fixed_edge_slice_integrable D μ a q hq T _ e r hr j)
  have hN : nativeStreamingSourceNormalizerTerm D μ a q T F=
      ∑σ,F σ*nativeStreamingSourceNormalizerTerm D μ a q T (fun τ=>if τ=σ then 1 else 0) := by
    unfold nativeStreamingSourceNormalizerTerm
    have hh := masked_basis_integral D μ a q T F (parisiFreeMeasure μ a) (fun l=>.normalizer l)
      (fun _=>True) (fun σ=>by
        simp only [ite_true]
        exact moment_integrable D μ a q T _ _ _
          (aestronglyMeasurable_nativeStreamingPatternMoment_normalizer D μ a q T _))
    simp only [ite_true] at hh
    rw [hh,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp only [nativeStreamingSourceSixBracket,hO,hOF,hX,hC,hFu,hN,mul_add,Finset.mul_sum,Finset.sum_add_distrib]

end QuantitativeFollowup
