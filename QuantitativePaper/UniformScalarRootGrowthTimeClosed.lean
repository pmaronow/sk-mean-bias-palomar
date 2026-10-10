module
public import QuantitativePaper.UniformScalarRootGrowthJets

@[expose] public section

/-! Continuous-profile time equations through both closed endpoints. The
continuous representative is recovered from the actual weak PDE by FTC. -/
noncomputable section
open Set MeasureTheory Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 900000

theorem scalarSpatialField_closed_profile_time (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (g : ℝ→ℝ) (hg : Continuous g) (b : ℝ)
    (hb : b∈Ioc (0:ℝ) 1) (he : EqOn (parisiCDF μ) g (Ioo 0 b))
    (j : ℕ) (q x : ℝ) (hq : q∈Icc (0:ℝ) b) :
    HasDerivWithinAt (fun s=>parisiSpatialField β μ j (s,x))
      (QuantitativeFollowup.continuousProfileTimeField β μ g j (q,x)) (Icc 0 b) q := by
  let V : ℝ→ℝ:=fun s=>QuantitativeFollowup.continuousProfileTimeField β μ g j (s,x)
  have hV : Continuous V:=
    (QuantitativeFollowup.continuous_continuousProfileTimeField β μ g hg j).comp
      (continuous_id.prodMk continuous_const)
  have hprim (r : ℝ) (hr : r∈Icc (0:ℝ) b) :
      (∫s in (0:ℝ)..r,V s)+parisiSpatialField β μ j (0,x)=parisiSpatialField β μ j (r,x) := by
    have hFTC:=QuantitativeFollowup.parisiTimeField_interval_integral β hβ μ j 0 r
      le_rfl hr.1 (hr.2.trans hb.2) (by
        intro s hs
        have hev : parisiCDF μ=ᶠ[𝓝 s] g:=he.eventuallyEq_of_mem
          (isOpen_Ioo.mem_nhds ⟨hs.1,hs.2.trans_le hr.2⟩)
        exact hg.continuousAt.congr_of_eventuallyEq hev) x
    have heq : (∫s in (0:ℝ)..r,V s)=(∫s in (0:ℝ)..r,parisiTimeField β μ j (s,x)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hr.1
      intro s hs
      dsimp only [V,QuantitativeFollowup.continuousProfileTimeField,parisiTimeField]
      rw [he ⟨hs.1,hs.2.trans_le hr.2⟩]
    rw [heq,hFTC]
    ring
  have hd:=(intervalIntegral.integral_hasDerivAt_right (hV.intervalIntegrable 0 q)
    hV.aestronglyMeasurable.stronglyMeasurableAtFilter hV.continuousAt).add_const
      (parisiSpatialField β μ j (0,x))
  exact hd.hasDerivWithinAt.congr (fun r hr=>(hprim r hr).symm) (hprim q hq).symm

theorem scalarEnergyJet_two_closed_profile_time (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) (g : ℝ→ℝ) (hg : Continuous g) (b : ℝ)
    (hb : b∈Ioc (0:ℝ) 1) (he : EqOn (parisiCDF μ) g (Ioo 0 b))
    (q x : ℝ) (hq : q∈Icc (0:ℝ) b) :
    HasDerivWithinAt (fun s=>scalarEnergySpatialJet β μ 2 (s,x))
      (β^2*QuantitativeFollowup.continuousProfileTimeField β μ g 3 (q,β*x))
      (Icc 0 b) q :=
  (scalarSpatialField_closed_profile_time β hβ μ g hg b hb he 3 q (β*x) hq).const_mul (β^2)

end QuantitativePaper
