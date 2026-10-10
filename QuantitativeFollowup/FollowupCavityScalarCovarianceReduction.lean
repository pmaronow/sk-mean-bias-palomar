module
public import QuantitativeFollowup.FollowupCavityFutureCovarianceReduction

@[expose] public section

/-! The scalar future-covariance factor in the source is obtained by genuine
full-past conditional projection under the actual Brownian law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem cavityScalarSquare_memLp_two (β : ℝ) (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    MemLp (fun ω=>M β μ p ω^2) 2 canonicalBrownianMeasure:=
  MemLp.of_bound ((measurable_M β μ p p.property).pow_const 2).aestronglyMeasurable 1
    (.of_forall fun ω=>by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (scalar_M_norm_le_one β μ p ω))

 theorem cavityScalarFutureSquare_memLp_two (β : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) :
    MemLp (cavityScalarFutureSquare β μ r p) 2 canonicalBrownianMeasure := by
  have hm : Measurable (cavityScalarFutureSquare β μ r p):=by
    have hmap : Measurable (fun ω : Paper.BrownianSample=>((r,p),ω)):=
      (measurable_const.prodMk measurable_const).prodMk measurable_id
    have hh:=(measurable_cavityScalarFutureSquare β μ).comp
      hmap
    exact hh
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  exact .of_forall fun ω=>by
    rw [Real.norm_of_nonneg (cavityScalarFutureSquare_mem_unit β μ r p ω).1]
    exact (cavityScalarFutureSquare_mem_unit β μ r p ω).2

 theorem cavityScalarFutureSquare_condExp (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (hrp : r≤p) :
    canonicalBrownianMeasure[(fun ω=>M β μ p ω^2)|
      canonicalBrownianFiltration (r:ℝ).toNNReal]=ᵐ[canonicalBrownianMeasure]
        cavityScalarFutureSquare β μ r p := by
  have he : scalarFutureSquareProcess β μ r p hrp=cavityScalarFutureSquare β μ r p:=by
    funext ω
    change scalarFutureSquare β μ r p hrp (parisiPhysicalSplitState β 0 μ r ω)=
      scalarFutureSquareExtended β μ r p (parisiPhysicalSplitState β 0 μ r ω)
    rw [scalarFutureSquareExtended_eq β μ r p hrp]
  rw [←he]
  exact condExp_scalarFutureSquareProcess β hβ μ r p hrp

 def cavityScalarProjectedCovariance (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r l : Paper.Overlap) : ℝ:=
  covariance (fun ω=>M β μ p ω^2) (cavityScalarFutureSquare β μ r l)
    canonicalBrownianMeasure

 theorem cavityScalarProjectedCovariance_eq_future (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (r p l : Paper.Overlap) (hrp : r≤p) (hrl : r≤l) :
    cavityScalarProjectedCovariance β μ p r l=cavityScalarConditionalCovariance β μ r p l := by
  exact covariance_conditional_projection_eq canonicalBrownianMeasure
    (canonicalBrownianFiltration (r:ℝ).toNNReal) (canonicalBrownianFiltration.le _)
    (cavityScalarSquare_memLp_two β μ p) (cavityScalarSquare_memLp_two β μ l)
    (cavityScalarFutureSquare_memLp_two β μ r p) (cavityScalarFutureSquare_memLp_two β μ r l)
    (cavityScalarFutureSquare_condExp β hβ μ r p hrp)
    (cavityScalarFutureSquare_condExp β hβ μ r l hrl)

 theorem cavityProjectedCovariance_product_eq_residual {n : ℕ} (D : AnisotropicSpinModel n)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (r p l : Paper.Overlap) (hrl : r<l) :
    cavityScalarProjectedCovariance β μ p r l*
      (cavityRestProjectedCovariance D μ a r l p-
        covariance (cavityRestSelfOverlap D μ l) (cavityRestSelfOverlap D μ p)
          (anisotropicMeasureSampleLaw D μ a))=
      -(cavityScalarFutureCovariance β μ r p l*cavityRestResidualCovariance D μ a r p l) := by
  by_cases hp : r<p
  · rw [cavityScalarProjectedCovariance_eq_future β hβ μ r p l hp.le hrl.le,
      cavityRestProjectedCovariance_sub_eq_residual D μ a r p l hp.le hrl.le,
      cavityScalarFutureCovariance_eq_mask,cavityRestResidualCovariance_eq_mask]
    simp only [hp,hrl,ite_eq_left,mul_neg]
  · rw [cavityRestProjectedCovariance_past D μ a r p l (le_of_not_gt hp) hrl.le,
      sub_self,mul_zero,cavityScalarFutureCovariance_eq_mask]
    simp [hp]

end QuantitativeFollowup
