module
public import HexagonPaper.PathHeatBernsteinContraction
public import Paper.CanonicalBrownian
public import StochasticCalculus.ItoFormulaGeneral

@[expose] public section

/-! A genuinely measurable continuous path realization of the actual
natural Itô process for every predictable L² integrand. Bernstein samples
use the actual selected finite-time representatives; their true continuous
modification makes them converge in the supremum norm almost surely. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal BigOperators unitInterval
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem exists_scalarItoContinuousPath
    (V : PredictableProcessL2
      (Filtration.natural Paper.canonicalBrownian
        (fun t=>(Paper.measurable_canonicalBrownian t).stronglyMeasurable))
      Paper.canonicalBrownianMeasure) :
    ∃ L : Paper.BrownianSample→C(Paper.Overlap,ℝ), Measurable L ∧
      ∀q : Paper.Overlap,
        (naturalItoProcess Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
          (fun t=>(Paper.measurable_canonicalBrownian t).stronglyMeasurable) rfl V
            (q:ℝ).toNNReal : Paper.BrownianSample→ℝ)=ᵐ[Paper.canonicalBrownianMeasure]
          (fun sample=>L sample q) := by
  let hsm:=fun t=>(Paper.measurable_canonicalBrownian t).stronglyMeasurable
  let hB:=Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
  let R:=naturalItoProcessRepresentative hB hsm rfl V
  obtain ⟨Y,hY⟩:=exists_continuousModification_naturalItoProcess
    Paper.isBrownianReal_canonicalBrownian hsm V
  let Φ:ℕ→Paper.BrownianSample→C(Paper.Overlap,ℝ):=fun j sample=>
    pathHeatBernsteinSynthesis j (WithLp.toLp 2
      (fun i : Fin (j+1)=>R (bernstein.z i:ℝ).toNNReal sample))
  have hΦ (j : ℕ) : Measurable (Φ j) := by
    apply (pathHeatBernsteinSynthesis j).continuous.measurable.comp
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (j+1)=>ℝ)).measurable.comp
    apply Measurable.of_eval
    intro i
    exact ((stronglyMeasurable_naturalItoProcessRepresentative hB hsm rfl V
      (bernstein.z i:ℝ).toNNReal).mono
        ((Filtration.natural Paper.canonicalBrownian hsm).le _)).measurable
  have hgrid : ∀ᵐ sample ∂Paper.canonicalBrownianMeasure, ∀j : ℕ,∀i : Fin (j+1),
      R (bernstein.z i:ℝ).toNNReal sample=Y (bernstein.z i:ℝ).toNNReal sample := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro i
    exact hY.fixedTime_ae_eq _
  have happ (sample : Paper.BrownianSample)
      (hc : Continuous (fun t=>Y t sample))
      (hg : ∀j : ℕ,∀i : Fin (j+1),R (bernstein.z i:ℝ).toNNReal sample=
        Y (bernstein.z i:ℝ).toNNReal sample) :
      ∃Z : C(Paper.Overlap,ℝ),
        (∀q,Z q=Y (q:ℝ).toNNReal sample) ∧ Tendsto (fun j=>Φ j sample) atTop (𝓝 Z) := by
    let Z:C(Paper.Overlap,ℝ):=⟨fun q=>Y (q:ℝ).toNNReal sample,
      hc.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
    refine ⟨Z,fun _=>rfl,?_⟩
    have he (j : ℕ) : Φ j sample=bernsteinPathOperator j Z := by
      rw [←pathHeatBernsteinSynthesis_sample]
      dsimp only [Φ]
      congr 1
      ext i
      exact hg j i
    simpa only [he] using tendsto_bernsteinPathOperator Z
  have hlimit : ∀ᵐ sample ∂Paper.canonicalBrownianMeasure,
      ∃Z : C(Paper.Overlap,ℝ),Tendsto (fun j=>Φ j sample) atTop (𝓝 Z) := by
    filter_upwards [hY.continuous_paths,hgrid] with sample hc hg
    obtain ⟨Z,_,hz⟩:=happ sample hc hg
    exact ⟨Z,hz⟩
  obtain ⟨L,hL,hLt⟩:=measurable_limit_of_tendsto_metrizable_ae
    (fun j=>(hΦ j).aemeasurable) hlimit
  refine ⟨L,hL,?_⟩
  intro q
  filter_upwards [hY.continuous_paths,hgrid,hLt,hY.fixedTime_ae_eq (q:ℝ).toNNReal,
    naturalItoProcess_ae_eq_representative hB hsm rfl V (q:ℝ).toNNReal]
    with sample hc hg hl hq hr
  obtain ⟨Z,hZ,hz⟩:=happ sample hc hg
  have he : L sample=Z:=tendsto_nhds_unique hl hz
  rw [hr,hq,he,hZ]

end HexagonPaper
