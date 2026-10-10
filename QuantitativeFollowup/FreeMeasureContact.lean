module
public import QuantitativeFollowup.ParisiFreeMeasure
public import Paper.JTVariational

@[expose] public section

/-! The constrained linear variational problem is exactly the minimum-support
condition for the actual free measure. The prescribed root atom cancels in
every comparison; the free measure is constructed, not assumed. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

theorem parisiMix_mem_scalarFloor {s : ℝ} {μ ν : Paper.ParisiMeasure}
    (hμ : μ∈scalarFloor s) (hν : ν∈scalarFloor s) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    parisiMix μ ν r∈scalarFloor s := by
  rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero] at hμ hν ⊢
  rw [parisiCDF_mix μ ν r 0 hr]
  nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hμ),
    mul_nonneg hr.1 (sub_nonneg.mpr hν)]

theorem rootDiracTrial_mem_scalarFloor (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (q : Paper.Overlap) :
    parisiMix (diracOverlap 0 (by norm_num))
      (Measure.dirac q).toProbabilityMeasure (1-s)∈scalarFloor s := by
  rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero,
    parisiCDF_mix _ _ _ _ (show 1-s∈Icc (0:ℝ) 1 from ⟨by linarith [hs.2],by linarith [hs.1]⟩)]
  have hzero : parisiCDF (diracOverlap 0 (by norm_num)) 0=1 := by
    simp [parisiCDF,diracOverlap]
  rw [hzero]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.2)
    (parisiCDF_nonneg (Measure.dirac q).toProbabilityMeasure 0)]

theorem integral_root_add_free (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (G : Paper.Overlap→ℝ) (hG : Continuous G) :
    (∫q,G q∂(μ:Measure Paper.Overlap))=s*G zeroOverlap+
      ∫q,G q∂parisiFreeMeasure μ s := by
  have hi : Integrable G (parisiFreeMeasure μ s) := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hG.continuousOn.integrableOn_compact (μ:=parisiFreeMeasure μ s) isCompact_univ
  have hr : Integrable G (ENNReal.ofReal s • Measure.dirac zeroOverlap) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [←root_add_parisiFreeMeasure μ s hs hμ,integral_add_measure hr hi,
    integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal hs.1]
  rfl

theorem constrained_integral_minimum_iff_free_support_argmin
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hs1 : s<1)
    (hμ : μ∈scalarFloor s) (G : Paper.Overlap→ℝ) (hG : Continuous G) :
    (∀ν∈scalarFloor s,(∫q,G q∂(μ:Measure Paper.Overlap))≤∫q,G q∂(ν:Measure Paper.Overlap)) ↔
      (parisiFreeMeasure μ s).support⊆overlapArgmin G := by
  let η:=parisiFreeMeasure μ s
  have hmass : η.real univ=1-s := by
    rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2)]
  have hi : Integrable G η := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hG.continuousOn.integrableOn_compact (μ:=η) isCompact_univ
  have hpos : 0<1-s := sub_pos.mpr hs1
  constructor
  · intro hmin
    let m:ℝ:=(∫q,G q∂η)/(1-s)
    have hpoint (q : Paper.Overlap) : m≤G q := by
      have hb:=hmin _ (rootDiracTrial_mem_scalarFloor s hs q)
      rw [integral_root_add_free μ s hs hμ G hG,
        integral_parisiMix hG _ _ _ (show 1-s∈Icc (0:ℝ) 1 from
          ⟨by linarith [hs.2],by linarith [hs.1]⟩)] at hb
      simp only [Measure.toProbabilityMeasure,diracOverlap,ProbabilityMeasure.toMeasure,integral_dirac] at hb
      change s*G zeroOverlap+(∫q,G q∂η)≤(1-(1-s))*G zeroOverlap+(1-s)*G q at hb
      apply (div_le_iff₀ hpos).mpr
      change (∫q,G q∂η)≤G q*(1-s)
      linarith
    have hm : (1-s)*m=∫q,G q∂η := by dsimp only [m];field_simp
    have hiz : Integrable (fun q=>G q-m) η:=hi.sub (integrable_const m)
    have hz : (∫q,G q-m∂η)=0 := by
      rw [integral_sub hi (integrable_const m),integral_const,hmass,smul_eq_mul,hm,sub_self]
    have hae: (fun q=>G q-m)=ᵐ[η]0:=
      (integral_eq_zero_iff_of_nonneg (fun q=>sub_nonneg.mpr (hpoint q)) hiz).mp hz
    have hlevel : {q | G q=m}∈ae η := by
      filter_upwards [hae] with q hq
      exact sub_eq_zero.mp hq
    have hsupport:=Measure.support_subset_of_isClosed (isClosed_eq hG continuous_const) hlevel
    intro q hq y
    exact (hsupport hq).trans_le (hpoint y)
  · intro hsupport
    have hη : η≠0 := by
      intro hz
      have hh:=parisiFreeMeasure_univ μ s
      change η univ=ENNReal.ofReal (1-s) at hh
      rw [hz] at hh
      have hh' : 1-s≤0 := by simpa using hh.symm
      linarith
    obtain ⟨x,hx⟩:=η.nonempty_support hη
    have hxminimum:=hsupport hx
    have hae:G=ᵐ[η](fun _=>G x) := by
      filter_upwards [Measure.support_mem_ae (μ:=η)] with q hq
      exact le_antisymm (hsupport hq x) (hxminimum q)
    have hvalue : (∫q,G q∂η)=(1-s)*G x := by
      rw [integral_congr_ae hae,integral_const,hmass,smul_eq_mul]
    intro ν hν
    rw [integral_root_add_free μ s hs hμ G hG,
      integral_root_add_free ν s hs hν G hG,hvalue]
    have hiν : Integrable G (parisiFreeMeasure ν s) := by
      simpa only [IntegrableOn,Measure.restrict_univ] using
        hG.continuousOn.integrableOn_compact (μ:=parisiFreeMeasure ν s) isCompact_univ
    have hb:=integral_mono (integrable_const (G x)) hiν hxminimum
    rw [integral_const,Measure.real,parisiFreeMeasure_univ,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2),smul_eq_mul] at hb
    exact add_le_add_right hb _

end QuantitativeFollowup
