module
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixMeasure
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayloadMeasurable
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternValueBounds

@[expose] public section

/-! One actual component source is exactly the six selected payload
integrals. Every measurability and finite bound is derived from the
genuine marked laws and the finite terminal test. The streaming
prefactor is outside this raw identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem finite_test_bound (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    ∃C : ℝ,0≤C∧∀σ,|F σ|≤C := by
  classical
  refine ⟨∑σ,|F σ|,Finset.sum_nonneg (fun _ _=>abs_nonneg _),?_⟩
  intro σ
  exact Finset.single_le_sum (f := fun τ=>|F τ|) (fun _ _=>abs_nonneg _)
    (Finset.mem_univ σ)

private theorem selection_floor (μ : Paper.ParisiMeasure) (a : ℝ)
    (hμ : μ∈scalarFloor a) (q : ℕ → Paper.Overlap) (hqJ : q J=0) :
    a≤Paper.parisiCDF μ (q J) := by
  rw [hqJ]
  exact scalarFloor_cdf_lower hμ (by norm_num)

theorem integral_cavityGeneratedSelectedOriginalFreshPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1) (hqJ : q J=0)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) :
    (∫g,cavityGeneratedSelectedOriginalFreshPayload D μ a q T F i g
      ∂cavityGeneratedOriginSelectionMeasure μ a q T a)=
      nativeStreamingOriginWeightIntegral μ a q T a
        (fun o=>nativeStreamingPatternMoment D μ a q T F (.originalFresh i o)) := by
  obtain ⟨C,hC,hF⟩ := finite_test_bound T F
  exact integral_cavityGeneratedSelectedOriginPayload μ a q hq0 T a
    (selection_floor μ a hμ q hqJ) _
    (measurable_cavityGeneratedSelectedOriginalFreshPayload D μ a q hq T F i)
    (2*C) (by positivity)
    (fun o=>abs_nativeStreamingPatternMoment_le D μ a q T F C hC hF _)

theorem integral_cavityGeneratedSelectedCurrentPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1) (hqJ : q J=0)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    (∫g,cavityGeneratedSelectedCurrentPayload D μ a q T F g
      ∂cavityGeneratedOriginSelectionMeasure μ a q T a)=
      nativeStreamingSourceCurrentTerm D μ a q T F := by
  obtain ⟨C,hC,hF⟩ := finite_test_bound T F
  apply integral_cavityGeneratedSelectedOriginPayload μ a q hq0 T a
    (selection_floor μ a hμ q hqJ) _
    (measurable_cavityGeneratedSelectedCurrentPayload D μ a q hq T F)
    (2*C) (by positivity)
  intro o
  rw [abs_mul,abs_of_nonneg (Paper.parisiCDF_nonneg μ _)]
  have hp := abs_nativeStreamingPatternMoment_le D μ a q T F C hC hF (.current o)
  have hc := mul_le_mul (Paper.parisiCDF_le_one μ (nativeStreamingOriginLevel q o)) hp
    (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  simpa only [one_mul] using hc

theorem integral_cavityGeneratedSelectedCrossPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1) (hqJ : q J=0)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    (∫z,cavityGeneratedSelectedCrossPayload D μ a q T F z
      ∂(cavityGeneratedOriginSelectionMeasure μ a q T a).prod
        (cavityGeneratedOriginSelectionMeasure μ a q T a))=
      nativeStreamingSourceCrossTerm D μ a q T F := by
  obtain ⟨C,hC,hF⟩ := finite_test_bound T F
  exact integral_cavityGeneratedSelectedOriginPayload_double μ a ha hμ q hq hq0 T a
    (selection_floor μ a hμ q hqJ)
    (fun o p=>nativeStreamingPatternMoment D μ a q T F (.cross o p))
    (measurable_cavityGeneratedSelectedCrossPayload D μ a q hq T F)
    (2*C) (by positivity)
    (fun o p=>abs_nativeStreamingPatternMoment_le D μ a q T F C hC hF _)

private theorem originCellMask_sum {I : Type*} (L : Finset I)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (Φ : I → NativeStreamingOrigin T → ℝ) (o : NativeStreamingOrigin T) :
    cavityGeneratedOriginCellMask q T (fun p=>∑i∈L,Φ i p) o=
      ∑i∈L,cavityGeneratedOriginCellMask q T (Φ i) o := by
  cases o with
  | vertex v => rfl
  | edge e r =>
      by_cases hr : r∈Ioc (q (e.depth+1)) (q e.depth) <;>
        simp only [cavityGeneratedOriginCellMask,hr,ite_true,ite_false,Finset.sum_const_zero]

theorem integral_cavityGeneratedSelectedFuturePayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1) (hqJ : q J=0)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    (∫z,cavityGeneratedSelectedFuturePayload D μ a q T F z
      ∂(cavityGeneratedOriginSelectionMeasure μ a q T a).prod (parisiFreeMeasure μ a))=
      nativeStreamingSourceFutureTerm D μ a q T F := by
  obtain ⟨C,hC,hF⟩ := finite_test_bound T F
  let Φ := fun j (l : Paper.Overlap) (o : NativeStreamingOrigin T) =>
    if l∈Ioc (q (j+1)) (q j) ∧ nativeStreamingOriginLevel q o<l then
      nativeStreamingPatternMoment D μ a q T F (.future o j l) else 0
  have hb j l o : |Φ j l o|≤2*C := by
    by_cases ht : l∈Ioc (q (j+1)) (q j) ∧ nativeStreamingOriginLevel q o<l
    · simpa only [Φ,if_pos ht] using
        abs_nativeStreamingPatternMoment_le D μ a q T F C hC hF (.future o j l)
    · simp only [Φ,if_neg ht,abs_zero]
      positivity
  have hs l o : |∑j∈Finset.range J,Φ j l o|≤(J:ℝ)*(2*C) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun j _=>hb j l o)).trans
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact le_rfl
  have he (z : CavityGeneratedOriginSelection T × Paper.Overlap) :
      cavityGeneratedSelectedOriginPayload q T (fun o=>∑j∈Finset.range J,Φ j z.2 o) z.1=
        cavityGeneratedSelectedFuturePayload D μ a q T F z := by
    exact originCellMask_sum (Finset.range J) q T (fun j=>Φ j z.2)
      (cavityGeneratedOriginSelectionOrigin T z.1)
  have hm : Measurable (fun z : CavityGeneratedOriginSelection T × Paper.Overlap =>
      cavityGeneratedSelectedOriginPayload q T (fun o=>∑j∈Finset.range J,Φ j z.2 o) z.1) := by
    simpa only [he] using measurable_cavityGeneratedSelectedFuturePayload D μ a q hq T F
  have hi := integral_cavityGeneratedSelectedOriginPayload_parameter (parisiFreeMeasure μ a)
    μ a q hq0 T a (selection_floor μ a hμ q hqJ)
    (fun l o=>∑j∈Finset.range J,Φ j l o) hm ((J:ℝ)*(2*C)) (by positivity) hs
  simp_rw [he] at hi
  rw [hi]
  apply nativeStreamingOriginWeightIntegral_congr_ae_edges μ a q T a
  · intro v
    have hc j : Integrable (fun l=>Φ j l (.vertex v)) (parisiFreeMeasure μ a) :=
      (integrable_const (2*C)).mono'
        (measurable_cavityGeneratedSelectedFutureOriginCell D μ a q hq T F (.vertex v) j
          trivial).aestronglyMeasurable
        (.of_forall fun l=>by simpa only [Real.norm_eq_abs] using hb j l (.vertex v))
    rw [integral_finset_sum _ (fun j _=>hc j)]
    apply Finset.sum_congr rfl
    intro j _
    change (∫l,Φ j l (.vertex v) ∂parisiFreeMeasure μ a)=_
    have hh : (fun l=>Φ j l (.vertex v))=
        (Ioc (q (j+1)) (q j)).indicator (fun l=>if nativeStreamingOriginLevel q (.vertex v)<l then
          nativeStreamingPatternMoment D μ a q T F (.future (.vertex v) j l) else 0) := by
      funext l
      by_cases hcell : l∈Ioc (q (j+1)) (q j)
      · simp only [Φ,Set.indicator_of_mem hcell,hcell,true_and,ite_true]
      · simp only [Φ,Set.indicator_of_notMem hcell,hcell,false_and,ite_false]
    rw [hh,integral_indicator measurableSet_Ioc]
  · intro e
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hc j : Integrable (fun l=>Φ j l (.edge e r)) (parisiFreeMeasure μ a) :=
      (integrable_const (2*C)).mono'
        (measurable_cavityGeneratedSelectedFutureOriginCell D μ a q hq T F (.edge e r) j
          hr).aestronglyMeasurable
        (.of_forall fun l=>by simpa only [Real.norm_eq_abs] using hb j l (.edge e r))
    rw [integral_finset_sum _ (fun j _=>hc j)]
    apply Finset.sum_congr rfl
    intro j _
    have hh : (fun l=>Φ j l (.edge e r))=
        (Ioc (q (j+1)) (q j)).indicator (fun l=>if nativeStreamingOriginLevel q (.edge e r)<l then
          nativeStreamingPatternMoment D μ a q T F (.future (.edge e r) j l) else 0) := by
      funext l
      by_cases hcell : l∈Ioc (q (j+1)) (q j)
      · simp only [Φ,Set.indicator_of_mem hcell,hcell,true_and,ite_true]
      · simp only [Φ,Set.indicator_of_notMem hcell,hcell,false_and,ite_false]
    rw [hh,integral_indicator measurableSet_Ioc]

theorem nativeStreamingSourceSixBracket_eq_selected_payload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hq0 : q 0=1) (hqJ : q J=0)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingSourceSixBracket D μ a q T F=
      cavityGeneratedSelectedSourceSixBracket D μ a q T F := by
  unfold nativeStreamingSourceSixBracket cavityGeneratedSelectedSourceSixBracket
  simp only [nativeStreamingSourceOriginalFreshTerm,nativeStreamingSourceNormalizerTerm]
  simp_rw [integral_cavityGeneratedSelectedOriginalFreshPayload D μ a ha hμ q hq hq0 hqJ T F,
    integral_cavityGeneratedSelectedCurrentPayload D μ a ha hμ q hq hq0 hqJ T F,
    integral_cavityGeneratedSelectedCrossPayload D μ a ha hμ q hq hq0 hqJ T F,
    integral_cavityGeneratedSelectedFuturePayload D μ a ha hμ q hq hq0 hqJ T F]

end QuantitativeFollowup
