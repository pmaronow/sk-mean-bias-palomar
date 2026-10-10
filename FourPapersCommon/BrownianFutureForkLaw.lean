module
public import FourPapersCommon.CanonicalBrownianFuture
public import FourPapersCommon.BrownianFork

@[expose] public section

/-! The exact joint law of an adapted split state and its two independent
future Wiener paths on the physical Brownian product space. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 900000

theorem brownianFutureFork_triple_law {A : Type*} [MeasurableSpace A]
    (a : ℝ≥0) (Y : Paper.BrownianSample→A)
    (hY : Measurable[canonicalBrownianFiltration a] Y) :
    brownianPairMeasure.map (fun w=>(Y w.1,
      (canonicalFutureBrownianPath a w.1,canonicalFutureBrownianPath a w.2)))=
      (canonicalBrownianMeasure.map Y).prod (canonicalWienerMeasure.prod canonicalWienerMeasure) := by
  have hYg:=hY.mono (canonicalBrownianFiltration.le a) le_rfl
  have hF:=measurable_canonicalFutureBrownianPath a
  have hpair:=hYg.prodMk hF
  calc
    _ = ((canonicalBrownianMeasure.map (fun w=>(Y w,canonicalFutureBrownianPath a w))).prod
        (canonicalBrownianMeasure.map (canonicalFutureBrownianPath a))).map
        MeasurableEquiv.prodAssoc := by
      rw [Measure.map_prod_map _ _ hpair hF,
        Measure.map_map MeasurableEquiv.prodAssoc.measurable (hpair.prodMap hF)]
      rfl
    _ = _ := by
      rw [canonicalFutureBrownianPath_joint_law a Y hY,canonicalFutureBrownianPath_law,
        Measure.prodAssoc_prod]

end FourPapersCommon
