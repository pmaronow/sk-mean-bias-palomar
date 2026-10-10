module
public import QuantitativeFollowup.AnisotropicBinaryFeatureLimits

@[expose] public section

/-! The actual finite Stieltjes identity on upward profile grids, pulled
back to the original profile measure through its genuine rounding map. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem anisotropicGrid_pair_second_stieltjes_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap) (j : ℕ)
    (e : AnisotropicCouplingIndex n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
    let qj:=Paper.parisiGridRound (vectorDyadicIndex j) q
    (∫p,Z p*anisotropicFiniteTailPairSecond D s qj
      (anisotropicFiniteProcessParameter D s qj (g,p.2)) e ∂vectorDisorderBrownianMeasure n)+
      Paper.parisiCDF (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) qj*
        anisotropicFinitePairSquareMoment D s g e Z qj+
      anisotropicGridFuturePairSquare D μ g q e Z j=
      ∫p,Z p ∂vectorDisorderBrownianMeasure n := by
  let N:=vectorDyadicIndex j
  let s:=Paper.parisiGridRSBScheme μ N
  let i:=anisotropicGridNodeIndex N q
  have hi : i ≤ (N+1)+2 := by have hh:=anisotropicGridNodeIndex_le N q;dsimp [i];omega
  have hZ' : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z :=
    hZ.mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono
      (anisotropicGridNode_after μ N q))) le_rfl
  have hnode : anisotropicSchemeNode s i hi=Paper.parisiGridRound N q :=
    anisotropicGridNode_eq_round μ N q
  have he:=anisotropicFinite_pair_second_node_stieltjes_pairing D s g i hi e Z hZ' hZi
  dsimp only at he
  rw [hnode,FRSB.parisiSchemeMeasure_grid_eq] at he
  have hm:=measurable_anisotropicFinitePairSquareMoment D s g e Z
    (hZ.mono ((vectorBrownianFiltration n).le _) le_rfl)
  have hf : Measurable (fun r : Paper.Overlap=>if Paper.parisiGridRound N q < r then
      anisotropicFinitePairSquareMoment D s g e Z r else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id) hm measurable_const
  have hfuture : (∫r : Paper.Overlap,if Paper.parisiGridRound N q < r then
      anisotropicFinitePairSquareMoment D s g e Z r else 0
        ∂(Paper.parisiGridMeasure μ N:Measure Paper.Overlap))=
      anisotropicGridFuturePairSquare D μ g q e Z j := by
    rw [Paper.parisiGridMeasure,ProbabilityMeasure.toMeasure_map,
      integral_map_of_stronglyMeasurable (Paper.measurable_parisiGridRound _) hf.stronglyMeasurable]
    rfl
  change _+_+ (∫r : Paper.Overlap,if Paper.parisiGridRound N q < r then
      anisotropicFinitePairSquareMoment D s g e Z r else 0
        ∂(Paper.parisiGridMeasure μ N:Measure Paper.Overlap))=_ at he
  rw [hfuture] at he
  exact he

end QuantitativeFollowup
