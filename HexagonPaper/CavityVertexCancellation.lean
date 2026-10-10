module
public import QuantitativeFollowup.AnisotropicNodeB

@[expose] public section

/-! Literal right-CDF/strict-future variance cancellation under the actual
arbitrary-profile single-leaf law. Derivatives and conditional future squares
are native constructed objects, not conclusions supplied as assumptions. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal ENNReal Topology
namespace HexagonPaper
open QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem anisotropic_future_square_cancellation_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : Paper.Overlap) (i : Fin n) (p : AnisotropicDisorderBrownianSample n) :
    (q : ℝ)*(∫r : Paper.Overlap, if q < r then
      anisotropicPastSpinSquareKernel D μ a q r i p else 0 ∂parisiFreeMeasure μ a) +
    (∫r : Paper.Overlap, if q < r then ((r : ℝ)-(q : ℝ))*
      anisotropicPastSpinSquareKernel D μ a q r i p else 0 ∂parisiFreeMeasure μ a) =
    ∫r : Paper.Overlap, if q < r then (r : ℝ)*
      anisotropicPastSpinSquareKernel D μ a q r i p else 0 ∂parisiFreeMeasure μ a := by
  classical
  let K := fun r : Paper.Overlap => anisotropicPastSpinSquareKernel D μ a q r i p
  have hmap : @Measurable Paper.Overlap (Paper.Overlap×AnisotropicDisorderBrownianSample n)
      inferInstance ((inferInstance : MeasurableSpace Paper.Overlap).prod
        (anisotropicBrownianFiltration n (q : ℝ).toNNReal)) (fun r => (r,p)) :=
    measurable_id.prodMk measurable_const
  have hK : Measurable K := by
    simpa only [Function.comp_def,K] using
      (measurable_uncurry_anisotropicPastSpinSquareKernel D μ a q i).comp hmap
  have hset : MeasurableSet {r : Paper.Overlap | q < r} :=
    measurableSet_lt measurable_const measurable_id
  let f := fun r : Paper.Overlap => if q < r then K r else 0
  let g := fun r : Paper.Overlap => if q < r then ((r : ℝ)-(q : ℝ))*K r else 0
  have hf : Measurable f := Measurable.ite hset hK measurable_const
  have hg : Measurable g := Measurable.ite hset
    ((measurable_subtype_coe.sub_const _).mul hK) measurable_const
  have hfi : Integrable f (parisiFreeMeasure μ a) := (integrable_const (1 : ℝ)).mono'
    hf.aestronglyMeasurable (.of_forall fun r => by
      dsimp only [f]
      split_ifs
      · exact norm_anisotropicPastSpinSquareKernel_le D μ a q r i p
      · simp only [norm_zero,zero_le_one])
  have hgi : Integrable g (parisiFreeMeasure μ a) := (integrable_const (1 : ℝ)).mono'
    hg.aestronglyMeasurable (.of_forall fun r => by
      dsimp only [g]
      split_ifs
      · rw [norm_mul]
        have hnorm : ‖(r : ℝ)-(q : ℝ)‖ ≤ 1 := by
          rw [Real.norm_eq_abs,abs_le]
          constructor <;> linarith [r.property.1,r.property.2,q.property.1,q.property.2]
        exact (mul_le_mul hnorm (norm_anisotropicPastSpinSquareKernel_le D μ a q r i p)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      · simp only [norm_zero,zero_le_one])
  calc
    _ = (∫r, (q : ℝ)*f r+g r ∂parisiFreeMeasure μ a) := by
      rw [integral_add (hfi.const_mul _) hgi,integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun r => by
        dsimp only [f,g,K]
        split_ifs <;> ring

/-- All-profile local cancellation at every actual marked single-leaf node.
The conclusion explicitly uses the full-past conditional future-square
version and the actual spatial and variance derivatives. -/
 theorem anisotropic_vertex_variance_cancellation
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (q : Paper.Overlap) (i : Fin n) :
    ∀ᵐp : AnisotropicDisorderBrownianSample n×Configuration n
        ∂anisotropicMeasureSpinPathLaw D μ a,
      (q : ℝ)*anisotropicProcessSpinSecond D μ q i p.1 +
        2*deriv (fun b => anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q
          (anisotropicProcessParameter D μ q p.1)) (D.variance i) =
      1-(q : ℝ)*Paper.parisiCDF μ q*(anisotropicProcessSpinResponse D μ q i p.1)^2-
        ∫r : Paper.Overlap, if q < r then (r : ℝ)*
          anisotropicPastSpinSquareKernel D μ a q r i p.1 else 0 ∂parisiFreeMeasure μ a := by
  filter_upwards [anisotropic_marked_spin_second_nodeResponse D μ a ha hμ q i,
    anisotropic_marked_variance_nodeb D μ a ha hμ q i] with p hH hB
  rw [hH,hB.deriv]
  have hc := anisotropic_future_square_cancellation_integral D μ a q i p.1
  linarith

 theorem cavity_vertex_variance_cancellation (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : Paper.Overlap) :
    let D := followupCavitySpinModel n β ρ hβ hρ u hu
    ∀ᵐp : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)
        ∂anisotropicMeasureSpinPathLaw D μ a,
      (q : ℝ)*anisotropicProcessSpinSecond D μ q (Fin.last n) p.1 +
        2*deriv (fun b => anisotropicMeasureTailPotential
          (anisotropicReplaceVariance D (Fin.last n) b) μ q
          (anisotropicProcessParameter D μ q p.1)) (followupCavityB n β ρ u) =
      1-(q : ℝ)*Paper.parisiCDF μ q*(anisotropicProcessSpinResponse D μ q (Fin.last n) p.1)^2-
        ∫r : Paper.Overlap, if q < r then (r : ℝ)*
          anisotropicPastSpinSquareKernel D μ a q r (Fin.last n) p.1 else 0
          ∂parisiFreeMeasure μ a := by
  dsimp only
  simpa only [followupCavitySpinModel_variance_last] using
    anisotropic_vertex_variance_cancellation (followupCavitySpinModel n β ρ hβ hρ u hu)
      μ a ha hμ q (Fin.last n)

end HexagonPaper
