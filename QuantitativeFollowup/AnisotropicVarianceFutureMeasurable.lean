module
public import QuantitativeFollowup.AnisotropicVarianceClampedMeasure
public import QuantitativeFollowup.AnisotropicVarianceRestartNodeSquare

@[expose] public section

/-! Honest measurability and probability bounds for the finite future-square
observable in the diagonal-variance Stieltjes response. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem measurable_cavityFiniteFutureDepth (s : RSBScheme k) (J : ℕ) :
    Measurable (cavityFiniteFutureDepth s J) := by
  classical
  induction J with
  | zero => exact measurable_const
  | succ J ih =>
    change Measurable (fun r : Paper.Overlap=>
      if (r:ℝ) ≤ s.q (k+2-(J+1)) then J+1 else cavityFiniteFutureDepth s J r)
    exact Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
      measurable_const ih

theorem measurable_cavityFiniteConditionalCoordinateSquare (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (P : AnisotropicParameter n) (i : Fin n) :
    Measurable (cavityFiniteConditionalCoordinateSquare D s J P i) := by
  classical
  let f : ℕ→ℝ := fun d=>
    ∫y,(∫σ,Paper.spinSign (σ i) ∂finiteStateCascadeGibbsKernel
      (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d y)^2
      ∂OverlapPaper.sourceKernelLaw (fun l=>finiteStateGaussianCascadeKernel
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (gtStateLogPartition (fun _ : Configuration n=>0)) (d+l)) (J-d) (anisotropicEnergyMap D P)
  exact (measurable_of_countable f).comp (measurable_cavityFiniteFutureDepth s J)

theorem cavityFiniteConditionalCoordinateSquare_mem_Icc (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (P : AnisotropicParameter n) (i : Fin n) (r : Paper.Overlap) :
    cavityFiniteConditionalCoordinateSquare D s J P i r∈Icc (0:ℝ) 1 := by
  let d:=cavityFiniteFutureDepth s J r
  let Q:=fun l=>finiteStateGaussianCascadeKernel (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
    (gtStateLogPartition (fun _ : Configuration n=>0)) (d+l)
  let G:=fun y=>(∫σ,Paper.spinSign (σ i) ∂finiteStateCascadeGibbsKernel
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d y)^2
  have hQ l:=isMarkovKernel_finiteStateGaussianTerminalCascadeKernel
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) (d+l)
  letI:=OverlapPaper.isMarkovKernel_sourceKernelLaw Q hQ (J-d)
  have hb : ∀y,‖G y‖≤(1:ℝ) := by
    intro y
    letI:=isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) d
    have hspin : ∀σ : Configuration n,‖Paper.spinSign (σ i)‖≤(1:ℝ) := fun σ=>by
      simp only [Real.norm_eq_abs,Paper.abs_spinSign,le_refl]
    have hm:=norm_integral_le_of_norm_le_const (μ:=finiteStateCascadeGibbsKernel
      (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d y)
      (.of_forall hspin)
    simp only [probReal_univ,mul_one,Real.norm_eq_abs] at hm
    simpa only [G,Real.norm_eq_abs,abs_pow,one_pow] using pow_le_pow_left₀ (abs_nonneg _) hm 2
  constructor
  · exact integral_nonneg fun _=>sq_nonneg _
  · have hh:=norm_integral_le_of_norm_le_const (μ:=OverlapPaper.sourceKernelLaw Q (J-d)
      (anisotropicEnergyMap D P)) (.of_forall hb)
    simp only [probReal_univ,mul_one,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans hh

theorem anisotropicFiniteTailVarianceResponse_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicFiniteTailVarianceResponse D s q P i=
      (1/2 : ℝ)*(1-(q:ℝ)-∫r,
        max 0 ((r:ℝ)-(q:ℝ))*cavityFiniteConditionalCoordinateSquare D
          (vectorClampedScheme s q q.property) (k+2) P i r
        ∂(Paper.parisiSchemeMeasure (vectorClampedScheme s q q.property):Measure Paper.Overlap)) := by
  classical
  unfold anisotropicFiniteTailVarianceResponse
  rw [cavityFiniteNodeBResponse_stieltjes D (vectorClampedScheme s q q.property) (k+2) (by omega)
    (anisotropicEnergyMap D P) (cavityCoordinateFeature i) (cavityCoordinateFeature_binary i)]
  have hidx : k+1+2-(k+2)=1:=by omega
  rw [hidx,vectorClampedScheme_overlap_succ s q q.property 0,s.q_zero,max_eq_left q.property.1]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with r
  rw [←cavityFiniteConditionalCoordinateSquare_eq_futureSquare]
  have hnode : scalarSchemeTransportNode (vectorClampedScheme s q q.property) 1=q := by
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe _ _ (by omega),vectorClampedScheme_overlap_succ,
      s.q_zero,max_eq_left q.property.1]
  rw [hnode]
  split_ifs with hr
  · rw [max_eq_right (sub_nonneg.mpr (show (q:ℝ)≤(r:ℝ) from hr.le))]
  · rw [max_eq_left (sub_nonpos.mpr (show (r:ℝ)≤(q:ℝ) from le_of_not_gt hr)),zero_mul]

end QuantitativeFollowup
