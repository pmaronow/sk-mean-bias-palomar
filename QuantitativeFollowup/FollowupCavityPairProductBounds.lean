module
public import QuantitativeFollowup.FollowupCavityNormalizerMarkedCubic

@[expose] public section

/-! Genuine uniform integrability of the physical two-pair observables
and their one-defect streaming products under finite marked laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityProfileLevel_coe_for_streaming (s : RSBScheme k) (d : ℕ) :
    (cavityProfileLevel s d : ℝ)=s.q (k+2-d) :=
  scalarSchemeTransportNode_coe s (k+2-d) (Nat.sub_le _ _)

theorem cavityPhysicalCommonOverlap_eq_profileLevel (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T) :
    cavityPhysicalCommonOverlap s T v w=
      (cavityProfileLevel s (finiteCascadeCommonPathDepth T v w):ℝ) := by
  rw [cavityProfileLevel_coe_for_streaming]
  rfl

theorem cavityRecordedPairProduct_abs_le_four (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i l : Fin 2 → ObservationLeaf T)
    (r : CavityPathRecordSpace T (n+1)) : |cavityRecordedPairProduct s T i l r|≤4 := by
  rw [cavityRecordedPairProduct,abs_mul]
  exact (mul_le_mul (cavityRecordedLeafPairDefect_abs_le_two s T _ _ _)
    (cavityRecordedLeafPairDefect_abs_le_two s T _ _ _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem integrable_cavityRecordedPairProduct (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i l : Fin 2 → ObservationLeaf T)
    (P : Measure (CavityPathRecordSpace T (n+1))) [IsFiniteMeasure P] :
    Integrable (cavityRecordedPairProduct s T i l) P := by
  apply (integrable_const (4:ℝ)).mono' (measurable_cavityRecordedPairProduct s T i l).aestronglyMeasurable
  exact .of_forall fun r => by simpa only [Real.norm_eq_abs] using cavityRecordedPairProduct_abs_le_four s T i l r

theorem integrable_bounded_pair_mul_cavityDefect {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (F : Ω → ℝ) (hF : Measurable F) (hFb : ∀ω,|F ω|≤4)
    (σ τ : Ω → Configuration (n+1)) (hσ : Measurable σ) (hτ : Measurable τ) (q : Paper.Overlap) :
    Integrable (fun ω => F ω*cavitySpinOverlapDefect n q (σ ω) (τ ω)) P := by
  have hm := hF.mul ((measurable_of_finite (fun w : Configuration (n+1) × Configuration (n+1) =>
    cavitySpinOverlapDefect n q w.1 w.2)).comp (hσ.prodMk hτ))
  apply (integrable_const (8:ℝ)).mono' hm.aestronglyMeasurable
  exact .of_forall fun ω => by
    change ‖F ω*cavitySpinOverlapDefect n q (σ ω) (τ ω)‖≤8
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (hFb ω) (cavitySpinOverlapDefect_abs_le_two n q q.property _ _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem abs_weighted_integral_sum_le {Ω A : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (xs : List (ℝ × A)) (f : A → Ω → ℝ)
    (hw : ∀c∈xs,0≤c.1) (hf : ∀a,Integrable (f a) P) :
    |(xs.map (fun c => c.1*(∫ω,f c.2 ω ∂P))).sum| ≤
      (xs.map (fun c => c.1*(∫ω,|f c.2 ω| ∂P))).sum := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
      simp only [List.map_cons,List.sum_cons]
      have hi := ih (fun d hd => hw d (by simp [hd]))
      have hc : |c.1*(∫ω,f c.2 ω ∂P)| ≤ c.1*(∫ω,|f c.2 ω| ∂P) := by
        rw [abs_mul,abs_of_nonneg (hw c (by simp))]
        exact mul_le_mul_of_nonneg_left (by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ:=P) (f:=f c.2))) (hw c (by simp))
      exact (abs_add_le _ _).trans (add_le_add hc hi)

theorem abs_list_sum_le {A : Type*} (xs : List A) (f g : A → ℝ)
    (h : ∀a∈xs,|f a|≤g a) :
    |(xs.map f).sum|≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (h a (by simp))
      (ih (fun b hb => h b (by simp [hb]))))

theorem abs_weighted_list_sum_le {A : Type*} (xs : List (ℝ×A)) (f g : A → ℝ)
    (hw : ∀c∈xs,0≤c.1) (h : ∀a,|f a|≤g a) :
    |(xs.map (fun c=>c.1*f c.2)).sum|≤(xs.map (fun c=>c.1*g c.2)).sum := by
  apply abs_list_sum_le
  intro c hc
  rw [abs_mul,abs_of_nonneg (hw c hc)]
  exact mul_le_mul_of_nonneg_left (h c.2) (hw c hc)

end QuantitativeFollowup
