module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginWeightIntegral
public import FourPapersCommon.WithinIntegralDerivative
public import FourPapersCommon.WithinDerivativeMeasurable

@[expose] public section

/-! Parameter differentiation of the actual recursive origin weights.
Only the callbacks vary. Edge derivatives are measurable by actual
within secants, and their uniform bound gives the integrable Lipschitz
dominator. All original Ioc cells and incoming coefficients are retained,
including empty cells and closed parameter endpoints. -/
noncomputable section
open Set Filter MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem hasDerivWithinAt_origin_edge_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F G : ℝ → Ω → ℝ) (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hm : ∀u ∈ Icc (0:ℝ) 1, AEStronglyMeasurable (F u) P)
    (hbase : ∀ᵐr ∂P, ‖F 0 r‖ ≤ A)
    (hb : ∀ᵐr ∂P, ∀u ∈ Icc (0:ℝ) 1, ‖G u r‖ ≤ B)
    (hd : ∀ᵐr ∂P, ∀u ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt (fun t => F t r) (G u r) (Icc (0:ℝ) 1) u)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t => ∫r, F t r ∂P) (∫r, G u r ∂P)
      (Icc (0:ℝ) 1) u := by
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hi0 : Integrable (F 0) P :=
    (integrable_const A).mono' (hm 0 hzero) hbase
  have hgm (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : AEStronglyMeasurable (G t) P :=
    aestronglyMeasurable_of_ae_hasDerivWithinAt_Icc01 F (G t) t ht hm
      (hd.mono fun r hr => hr t ht)
  have hlu : ∀ᵐr ∂P, ‖F 0 r-F u r‖ ≤ B*‖0-u‖ := by
    filter_upwards [hd,hb] with r hr hbr
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hr hbr (convex_Icc 0 1) hu hzero
  have hiu : Integrable (F u) P :=
    integrable_of_norm_sub_le (hm u hu) hi0 (integrable_const (B*‖0-u‖)) hlu
  exact hasDerivWithinAt_integral_of_uniform_derivative F G (fun _ => B)
    (Icc (0:ℝ) 1) (convex_Icc 0 1) u hu hm hiu hgm (integrable_const B) hb hd

theorem hasDerivWithinAt_nativeStreamingOriginWeightIntegral
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {J : ℕ} (T : FiniteTerminalGenealogy J) (incoming : ℝ)
    (Φ Ψ : ℝ → NativeStreamingOrigin T → ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hV : ∀v : FiniteCascadeRecordVertex T, ∀u ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt (fun t => Φ t (.vertex v)) (Ψ u (.vertex v)) (Icc (0:ℝ) 1) u)
    (hE : ∀e : NativeStreamingEdge T, ∀r ∈ Icc (q (e.depth+1)) (q e.depth),
      ∀u ∈ Icc (0:ℝ) 1,
        HasDerivWithinAt (fun t => Φ t (.edge e r)) (Ψ u (.edge e r)) (Icc (0:ℝ) 1) u)
    (hm : ∀e : NativeStreamingEdge T, ∀u ∈ Icc (0:ℝ) 1,
      AEStronglyMeasurable (fun r => Φ u (.edge e r))
        ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth))))
    (hbase : ∀e : NativeStreamingEdge T, ∀r ∈ Icc (q (e.depth+1)) (q e.depth),
      |Φ 0 (.edge e r)| ≤ A)
    (hb : ∀e : NativeStreamingEdge T, ∀r ∈ Icc (q (e.depth+1)) (q e.depth),
      ∀u ∈ Icc (0:ℝ) 1, |Ψ u (.edge e r)| ≤ B)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (fun t => nativeStreamingOriginWeightIntegral μ a q T incoming (Φ t))
      (nativeStreamingOriginWeightIntegral μ a q T incoming (Ψ u)) (Icc (0:ℝ) 1) u := by
  induction T generalizing incoming with
  | leaf =>
      exact (hV (.root .leaf) u hu).const_mul (1-incoming)
  | @advance j T ih =>
      have hc : HasDerivWithinAt
          (fun t => nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
            (fun o => Φ t (nativeStreamingOriginChild o)))
          (nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
            (fun o => Ψ u (nativeStreamingOriginChild o))) (Icc (0:ℝ) 1) u := by
        apply ih
        · intro v t ht; exact hV (.child v) t ht
        · intro e r hr t ht; exact hE (.child e) r hr t ht
        · intro e t ht; exact hm (.child e) t ht
        · intro e r hr; exact hbase (.child e) r hr
        · intro e r hr t ht; exact hb (.child e) r hr t ht
      have he : HasDerivWithinAt
          (fun t => ∫r in Ioc (q (j+1)) (q j), Φ t (.edge (.here T) r) ∂parisiFreeMeasure μ a)
          (∫r in Ioc (q (j+1)) (q j), Ψ u (.edge (.here T) r) ∂parisiFreeMeasure μ a)
          (Icc (0:ℝ) 1) u := by
        apply hasDerivWithinAt_origin_edge_integral
          ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)))
          (fun t r => Φ t (.edge (.here T) r)) (fun t r => Ψ t (.edge (.here T) r))
          A B hA hB (hm (.here T))
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          simpa only [Real.norm_eq_abs] using hbase (.here T) r ⟨hr.1.le,hr.2⟩
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          intro t ht
          simpa only [Real.norm_eq_abs] using hb (.here T) r ⟨hr.1.le,hr.2⟩ t ht
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          intro t ht
          exact hE (.here T) r ⟨hr.1.le,hr.2⟩ t ht
        · exact hu
      exact (hc.add he).add
        ((hV (.root T.advance) u hu).const_mul (Paper.parisiCDF μ (q (j+1))-incoming))
  | @fork j T U ihT ihU =>
      have hl : HasDerivWithinAt
          (fun t => nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
            (fun o => Φ t (nativeStreamingOriginLeft o)))
          (nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
            (fun o => Ψ u (nativeStreamingOriginLeft o))) (Icc (0:ℝ) 1) u := by
        apply ihT
        · intro v t ht; exact hV (.left v) t ht
        · intro e r hr t ht; exact hE (.left e) r hr t ht
        · intro e t ht; exact hm (.left e) t ht
        · intro e r hr; exact hbase (.left e) r hr
        · intro e r hr t ht; exact hb (.left e) r hr t ht
      have hr : HasDerivWithinAt
          (fun t => nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
            (fun o => Φ t (nativeStreamingOriginRight o)))
          (nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
            (fun o => Ψ u (nativeStreamingOriginRight o))) (Icc (0:ℝ) 1) u := by
        apply ihU
        · intro v t ht; exact hV (.right v) t ht
        · intro e r her t ht; exact hE (.right e) r her t ht
        · intro e t ht; exact hm (.right e) t ht
        · intro e r her; exact hbase (.right e) r her
        · intro e r her t ht; exact hb (.right e) r her t ht
      exact (hl.add hr).add
        ((hV (.root (.fork T U)) u hu).const_mul (2*Paper.parisiCDF μ (q j)-incoming))

end QuantitativeFollowup
