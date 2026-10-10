module
public import QuantitativeFollowup.ScalarTransportFunctionalDerivative

@[expose] public section

/-! The actual convex supporting curve has a genuine second transport
derivative. A continuous extension is used only outside the physical strip;
on every transported overlap it is exactly the paper's tail primitive. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarGammaExtension (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  Gamma β μ (projIcc 0 1 zero_le_one q)

def scalarGammaTailExtension (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  ∫r in q..1,scalarGammaExtension β μ r-r

def scalarTransportSupportingCurve (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) : ℝ :=
  β^2/2*((∫q : Paper.Overlap,scalarGammaTailExtension β μ (scalarLevelTransport φ u q)
    ∂(μ:Measure Paper.Overlap))-
    ∫q : Paper.Overlap,scalarGammaTailExtension β μ q ∂(μ:Measure Paper.Overlap))

def scalarTransportSupportDerivative (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) : ℝ :=
  β^2/2*(∫q : Paper.Overlap,φ q*((scalarLevelTransport φ u q:ℝ)-
    Gamma β μ (scalarLevelTransport φ u q)) ∂(μ:Measure Paper.Overlap))

theorem continuous_scalarGammaExtension (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) :
    Continuous (scalarGammaExtension β μ) :=
  (continuousOn_Gamma β hβ μ).comp_continuous
    (continuous_subtype_val.comp (continuous_projIcc (a:=(0:ℝ)) (b:=1) (h:=zero_le_one)))
    (fun q=>(projIcc 0 1 zero_le_one q).property)

theorem scalarGammaExtension_eq (β : ℝ) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : scalarGammaExtension β μ q=Gamma β μ q := by
  simp only [scalarGammaExtension,projIcc_of_mem zero_le_one hq]

theorem scalarGammaTailExtension_eq (β : ℝ) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) : scalarGammaTailExtension β μ q=scalarGammaTail β μ q := by
  unfold scalarGammaTailExtension scalarGammaTail
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le q.property.2] at hr
  change scalarGammaExtension β μ r-r=Gamma β μ r-r
  rw [scalarGammaExtension_eq β μ r ⟨q.property.1.trans hr.1,hr.2⟩]

theorem hasDerivAt_scalarGammaTailExtension (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (q : ℝ) :
    HasDerivAt (scalarGammaTailExtension β μ) (q-scalarGammaExtension β μ q) q := by
  have hc := (continuous_scalarGammaExtension β hβ μ).sub continuous_id
  convert! intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable q 1)
    (hc.stronglyMeasurableAtFilter volume (𝓝 q)) hc.continuousAt using 1
  change q-scalarGammaExtension β μ q=-(scalarGammaExtension β μ q-q)
  ring

theorem hasDerivAt_scalarGammaExtension_interior (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    HasDerivAt (scalarGammaExtension β μ) (GammaPrime β μ q) q := by
  have he : scalarGammaExtension β μ=ᶠ[𝓝 q] Gamma β μ := by
    filter_upwards [isOpen_Ioo.mem_nhds hq] with r hr
    exact scalarGammaExtension_eq β μ r ⟨hr.1.le,hr.2.le⟩
  exact (hasDerivAt_Gamma_GammaPrime β hβ μ hq).congr_of_eventuallyEq he

theorem scalarTransportSupportingCurve_convex_support (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (u : ℝ) :
    scalarTransportSupportingCurve β μ φ u≤
      scalarTransportFunctional β μ φ u-scalarTransportFunctional β μ φ 0 := by
  simpa only [scalarTransportSupportingCurve,scalarGammaTailExtension_eq] using
    scalarTransportFunctional_convex_support β hβ μ φ u

theorem scalarTransportSupportingCurve_zero (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) : scalarTransportSupportingCurve β μ φ 0=0 := by
  simp only [scalarTransportSupportingCurve,scalarLevelTransport_zero,sub_self,mul_zero]

theorem hasDerivAt_scalarTransportSupportingCurve (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) :
    HasDerivAt (scalarTransportSupportingCurve β (parisiSchemeMeasure s) φ)
      (scalarTransportSupportDerivative β (parisiSchemeMeasure s) φ u) u := by
  have hq (q : Paper.Overlap) : HasDerivAt
      (fun v : ℝ=>scalarGammaTailExtension β (parisiSchemeMeasure s) (scalarLevelTransport φ v q))
      (φ q*((scalarLevelTransport φ u q:ℝ)-Gamma β (parisiSchemeMeasure s) (scalarLevelTransport φ u q))) u := by
    have hd := (hasDerivAt_scalarGammaTailExtension β hβ (parisiSchemeMeasure s)
      (scalarLevelTransport φ u q)).comp u
      (hasDerivAt_scalarLevelTransport_coe φ L hφ h0 h1 u hu q)
    rw [scalarGammaExtension_eq β _ _ (scalarLevelTransport φ u q).property] at hd
    convert! hd using 1
    ring
  exact ((hasDerivAt_scalarScheme_integral s _ _ u hq).sub_const _).const_mul (β^2/2)

theorem hasDerivAt_scalarTransportSupportDerivative_zero (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) :
    HasDerivAt (scalarTransportSupportDerivative β (parisiSchemeMeasure s) φ)
      (β^2/2*(∫q : Paper.Overlap,φ q^2*(1-GammaPrime β (parisiSchemeMeasure s) q)
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap))) 0 := by
  have hq (q : Paper.Overlap) : HasDerivAt
      (fun v : ℝ=>φ q*((scalarLevelTransport φ v q:ℝ)-
        Gamma β (parisiSchemeMeasure s) (scalarLevelTransport φ v q)))
      (φ q^2*(1-GammaPrime β (parisiSchemeMeasure s) q)) 0 := by
    by_cases he : q=0 ∨ q=1
    · have hz : φ q=0 := by rcases he with rfl|rfl <;> assumption
      simp only [hz,zero_mul,zero_pow (by decide : 2≠0)]
      exact hasDerivAt_const 0 0
    · have hqi : (q:ℝ)∈Ioo (0:ℝ) 1 := by
        have hn0 : (q:ℝ)≠0 := fun hh=>he (.inl (Subtype.ext hh))
        have hn1 : (q:ℝ)≠1 := fun hh=>he (.inr (Subtype.ext hh))
        exact ⟨lt_of_le_of_ne q.property.1 hn0.symm,lt_of_le_of_ne q.property.2 hn1⟩
      have hT := hasDerivAt_scalarLevelTransport_coe φ L hφ h0 h1 0 (by simp) q
      have hbase : HasDerivAt (Gamma β (parisiSchemeMeasure s))
          (GammaPrime β (parisiSchemeMeasure s) q) (scalarLevelTransport φ 0 q) := by
        simpa only [scalarLevelTransport_zero] using
          hasDerivAt_Gamma_GammaPrime β hβ (parisiSchemeMeasure s) hqi
      have hG := hbase.comp 0 hT
      convert! ((hT.sub hG).const_mul (φ q)) using 1
      ring
  exact (hasDerivAt_scalarScheme_integral s _ _ 0 hq).const_mul (β^2/2)

end QuantitativeFollowup
