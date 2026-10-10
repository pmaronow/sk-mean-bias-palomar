module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternDerivativeBounds
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternValueBounds
public import FourPapersCommon.WithinIntegralDerivative
public import FourPapersCommon.WithinDerivativeMeasurable

@[expose] public section

/-! Genuine within-parameter dominated differentiation for actual pattern
integrals. The selector validity and slice measurability are structural
inputs to this supporting consumer; concrete source cells supply them.
The derivative, baseline integrability and envelope are proved from the
actual marked probabilities and enlarged-tree source response. -/
noncomputable section
open Set Filter MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ} {Ω : Type*} [MeasurableSpace Ω]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingPatternParameterDerivative
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (P : NativeStreamingAttachmentPattern T) (u : ℝ) : ℝ :=
  if hu : u∈Icc (0:ℝ) 1 then
    (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F P else 0

theorem integrable_nativeStreamingPatternParameterMoment_of_measurable
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (P : Measure Ω) [IsFiniteMeasure P]
    (pattern : Ω→NativeStreamingAttachmentPattern T)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1)
    (hm : AEStronglyMeasurable
      (fun x=>nativeStreamingPatternMoment (followupCavitySpinModel n β ρ hβ hρ u hu)
        μ a q T F (pattern x)) P) :
    Integrable (fun x=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F
      (pattern x) u) P := by
  simp only [nativeStreamingPatternParameterMoment,dif_pos hu]
  exact (integrable_const (2*C)).mono' hm (.of_forall fun x=>by
    simpa only [Real.norm_eq_abs] using abs_nativeStreamingPatternMoment_le
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F C hC hF (pattern x))

theorem hasDerivWithinAt_nativeStreamingPattern_selected_integral
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (P : Measure Ω) [IsFiniteMeasure P]
    (pattern : Ω→NativeStreamingAttachmentPattern T)
    (hvalid : ∀ᵐx∂P,nativeStreamingPatternValid q (pattern x))
    (hm : ∀(v : ℝ)(hv : v∈Icc (0:ℝ) 1),AEStronglyMeasurable
      (fun x=>nativeStreamingPatternMoment (followupCavitySpinModel n β ρ hβ hρ v hv)
        μ a q T F (pattern x)) P)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (fun v=>∫x,nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (pattern x) v ∂P)
      (∫x,(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (pattern x) ∂P)
      (Icc (0:ℝ) 1) u := by
  let H := fun v x=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (pattern x) v
  let G := fun v x=>nativeStreamingPatternParameterDerivative β ρ hβ hρ μ a q T F (pattern x) v
  let B := 7*β^2*((FiniteCascadeGenealogy.leafCount (asGenealogy T)+2:ℕ):ℝ)^2*(2*C)
  have hHm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (H v) P := by
    simpa only [H,nativeStreamingPatternParameterMoment,dif_pos hv] using hm v hv
  have hd : ∀ᵐx∂P,∀v∈Icc (0:ℝ) 1,
      HasDerivWithinAt (fun w=>H w x) (G v x) (Icc (0:ℝ) 1) v := by
    filter_upwards [hvalid] with x hx
    intro v hv
    simpa only [H,G,nativeStreamingPatternParameterDerivative,dif_pos hv] using
      hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
        q hq hJ hzero htop T F (pattern x) hx v hv
  have hGm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (G v) P :=
    aestronglyMeasurable_of_ae_hasDerivWithinAt_Icc01 H (G v) v hv hHm
      (hd.mono fun x hx=>hx v hv)
  have hb : ∀ᵐx∂P,∀v∈Icc (0:ℝ) 1,‖G v x‖≤B := by
    filter_upwards [hvalid] with x hx
    intro v hv
    simpa only [G,nativeStreamingPatternParameterDerivative,dif_pos hv,Real.norm_eq_abs,B] using
      abs_nativeStreamingPattern_source_derivative_le hn β ρ hβ hρ μ a ha hfloor
        q hq hJ hzero htop T F C hC hF (pattern x) hx v hv
  have hi : Integrable (H u) P :=
    integrable_nativeStreamingPatternParameterMoment_of_measurable β ρ hβ hρ μ a q T F
      C hC hF P pattern u hu (hm u hu)
  have h := hasDerivWithinAt_integral_of_uniform_derivative H G (fun _=>B)
    (Icc (0:ℝ) 1) (convex_Icc 0 1) u hu hHm hi hGm (integrable_const B) hb hd
  simpa only [H,G,nativeStreamingPatternParameterDerivative,dif_pos hu] using h

theorem hasDerivWithinAt_nativeStreamingPattern_masked_integral
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (P : Measure Ω) [IsFiniteMeasure P]
    (pattern : Ω→NativeStreamingAttachmentPattern T) (mask : Ω→Prop)
    (hvalid : ∀ᵐx∂P,nativeStreamingPatternValid q (pattern x))
    (hm : ∀(v : ℝ)(hv : v∈Icc (0:ℝ) 1),AEStronglyMeasurable
      (fun x=>if mask x then nativeStreamingPatternMoment (followupCavitySpinModel n β ρ hβ hρ v hv)
        μ a q T F (pattern x) else 0) P)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (fun v=>∫x,if mask x then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (pattern x) v else 0 ∂P)
      (∫x,if mask x then (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (pattern x) else 0 ∂P)
      (Icc (0:ℝ) 1) u := by
  let H := fun v x=>if mask x then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (pattern x) v else 0
  let G := fun v x=>if mask x then nativeStreamingPatternParameterDerivative β ρ hβ hρ μ a q T F (pattern x) v else 0
  let B := 7*β^2*((FiniteCascadeGenealogy.leafCount (asGenealogy T)+2:ℕ):ℝ)^2*(2*C)
  have hHm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (H v) P := by
    simpa only [H,nativeStreamingPatternParameterMoment,dif_pos hv] using hm v hv
  have hd : ∀ᵐx∂P,∀v∈Icc (0:ℝ) 1,
      HasDerivWithinAt (fun w=>H w x) (G v x) (Icc (0:ℝ) 1) v := by
    filter_upwards [hvalid] with x hx
    intro v hv
    by_cases hmask : mask x
    · simpa only [H,G,if_pos hmask,nativeStreamingPatternParameterDerivative,dif_pos hv] using
        hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
          q hq hJ hzero htop T F (pattern x) hx v hv
    · simpa only [H,G,if_neg hmask] using (hasDerivWithinAt_const v (Icc (0:ℝ) 1) (0:ℝ))
  have hGm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (G v) P :=
    aestronglyMeasurable_of_ae_hasDerivWithinAt_Icc01 H (G v) v hv hHm
      (hd.mono fun x hx=>hx v hv)
  have hb : ∀ᵐx∂P,∀v∈Icc (0:ℝ) 1,‖G v x‖≤B := by
    filter_upwards [hvalid] with x hx
    intro v hv
    by_cases hmask : mask x
    · simpa only [G,if_pos hmask,nativeStreamingPatternParameterDerivative,dif_pos hv,Real.norm_eq_abs,B] using
        abs_nativeStreamingPattern_source_derivative_le hn β ρ hβ hρ μ a ha hfloor
          q hq hJ hzero htop T F C hC hF (pattern x) hx v hv
    · simp only [G,if_neg hmask,norm_zero]
      dsimp [B]; positivity
  have hi : Integrable (H u) P := (integrable_const (2*C)).mono' (hHm u hu) (.of_forall fun x=>by
    by_cases hmask : mask x
    · simpa only [H,if_pos hmask,nativeStreamingPatternParameterMoment,dif_pos hu,Real.norm_eq_abs] using
        abs_nativeStreamingPatternMoment_le (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a q T F C hC hF (pattern x)
    · simp only [H,if_neg hmask,norm_zero]
      positivity)
  have h := hasDerivWithinAt_integral_of_uniform_derivative H G (fun _=>B)
    (Icc (0:ℝ) 1) (convex_Icc 0 1) u hu hHm hi hGm (integrable_const B) hb hd
  simpa only [H,G,nativeStreamingPatternParameterDerivative,dif_pos hu] using h

theorem nativeStreamingPattern_selected_integral_regularities
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (P : Measure Ω) [IsFiniteMeasure P]
    (pattern : Ω→NativeStreamingAttachmentPattern T)
    (hvalid : ∀ᵐx∂P,nativeStreamingPatternValid q (pattern x))
    (hm : ∀(v : ℝ)(hv : v∈Icc (0:ℝ) 1),AEStronglyMeasurable
      (fun x=>nativeStreamingPatternMoment (followupCavitySpinModel n β ρ hβ hρ v hv)
        μ a q T F (pattern x)) P)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun x=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (pattern x) u) P ∧
    Integrable (fun x=>(followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (pattern x)) P := by
  let H := fun v x=>nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (pattern x) v
  let G := fun v x=>nativeStreamingPatternParameterDerivative β ρ hβ hρ μ a q T F (pattern x) v
  let B := 7*β^2*((FiniteCascadeGenealogy.leafCount (asGenealogy T)+2:ℕ):ℝ)^2*(2*C)
  have hHm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (H v) P := by
    simpa only [H,nativeStreamingPatternParameterMoment,dif_pos hv] using hm v hv
  have hd : ∀ᵐx∂P,∀v∈Icc (0:ℝ) 1,
      HasDerivWithinAt (fun w=>H w x) (G v x) (Icc (0:ℝ) 1) v := by
    filter_upwards [hvalid] with x hx
    intro v hv
    simpa only [H,G,nativeStreamingPatternParameterDerivative,dif_pos hv] using
      hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
        q hq hJ hzero htop T F (pattern x) hx v hv
  have hGm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (G v) P :=
    aestronglyMeasurable_of_ae_hasDerivWithinAt_Icc01 H (G v) v hv hHm
      (hd.mono fun x hx=>hx v hv)
  have hb : ∀ᵐx∂P,∀v∈Icc (0:ℝ) 1,‖G v x‖≤B := by
    filter_upwards [hvalid] with x hx
    intro v hv
    simpa only [G,nativeStreamingPatternParameterDerivative,dif_pos hv,Real.norm_eq_abs,B] using
      abs_nativeStreamingPattern_source_derivative_le hn β ρ hβ hρ μ a ha hfloor
        q hq hJ hzero htop T F C hC hF (pattern x) hx v hv
  have hi : Integrable (H u) P :=
    integrable_nativeStreamingPatternParameterMoment_of_measurable β ρ hβ hρ μ a q T F
      C hC hF P pattern u hu (hm u hu)
  have hiG : Integrable (G u) P := (integrable_const B).mono' (hGm u hu)
    (hb.mono fun x hx=>hx u hu)
  simpa only [H,G,nativeStreamingPatternParameterDerivative,dif_pos hu] using And.intro hi hiG

theorem nativeStreamingPattern_masked_integral_regularities
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (P : Measure Ω) [IsFiniteMeasure P]
    (pattern : Ω→NativeStreamingAttachmentPattern T) (mask : Ω→Prop)
    (hvalid : ∀ᵐx∂P,nativeStreamingPatternValid q (pattern x))
    (hm : ∀(v : ℝ)(hv : v∈Icc (0:ℝ) 1),AEStronglyMeasurable
      (fun x=>if mask x then nativeStreamingPatternMoment (followupCavitySpinModel n β ρ hβ hρ v hv)
        μ a q T F (pattern x) else 0) P)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (fun x=>if mask x then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (pattern x) u else 0) P ∧
    Integrable (fun x=>if mask x then (followupCavityAlpha n β ρ/2)*nativeStreamingPatternSourceResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F (pattern x) else 0) P := by
  let H := fun v x=>if mask x then nativeStreamingPatternParameterMoment β ρ hβ hρ μ a q T F (pattern x) v else 0
  let G := fun v x=>if mask x then nativeStreamingPatternParameterDerivative β ρ hβ hρ μ a q T F (pattern x) v else 0
  let B := 7*β^2*((FiniteCascadeGenealogy.leafCount (asGenealogy T)+2:ℕ):ℝ)^2*(2*C)
  have hHm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (H v) P := by
    simpa only [H,nativeStreamingPatternParameterMoment,dif_pos hv] using hm v hv
  have hd : ∀ᵐx∂P,∀v∈Icc (0:ℝ) 1,
      HasDerivWithinAt (fun w=>H w x) (G v x) (Icc (0:ℝ) 1) v := by
    filter_upwards [hvalid] with x hx
    intro v hv
    by_cases hmask : mask x
    · simpa only [H,G,if_pos hmask,nativeStreamingPatternParameterDerivative,dif_pos hv] using
        hasDerivWithinAt_nativeStreamingPattern_source_response hn β ρ hβ hρ μ a ha hfloor
          q hq hJ hzero htop T F (pattern x) hx v hv
    · simpa only [H,G,if_neg hmask] using (hasDerivWithinAt_const v (Icc (0:ℝ) 1) (0:ℝ))
  have hGm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (G v) P :=
    aestronglyMeasurable_of_ae_hasDerivWithinAt_Icc01 H (G v) v hv hHm
      (hd.mono fun x hx=>hx v hv)
  have hb : ∀ᵐx∂P,∀v∈Icc (0:ℝ) 1,‖G v x‖≤B := by
    filter_upwards [hvalid] with x hx
    intro v hv
    by_cases hmask : mask x
    · simpa only [G,if_pos hmask,nativeStreamingPatternParameterDerivative,dif_pos hv,Real.norm_eq_abs,B] using
        abs_nativeStreamingPattern_source_derivative_le hn β ρ hβ hρ μ a ha hfloor
          q hq hJ hzero htop T F C hC hF (pattern x) hx v hv
    · simp only [G,if_neg hmask,norm_zero]
      dsimp [B]; positivity
  have hi : Integrable (H u) P := (integrable_const (2*C)).mono' (hHm u hu) (.of_forall fun x=>by
    by_cases hmask : mask x
    · simpa only [H,if_pos hmask,nativeStreamingPatternParameterMoment,dif_pos hu,Real.norm_eq_abs] using
        abs_nativeStreamingPatternMoment_le (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a q T F C hC hF (pattern x)
    · simp only [H,if_neg hmask,norm_zero]
      positivity)
  have hiG : Integrable (G u) P := (integrable_const B).mono' (hGm u hu)
    (hb.mono fun x hx=>hx u hu)
  simpa only [H,G,nativeStreamingPatternParameterDerivative,dif_pos hu] using And.intro hi hiG

end QuantitativeFollowup
