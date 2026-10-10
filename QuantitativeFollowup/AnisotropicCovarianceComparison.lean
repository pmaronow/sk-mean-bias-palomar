module
public import QuantitativeFollowup.AnisotropicCovarianceMoments

@[expose] public section

/-! The actual full-profile field Hessian is between the right-CDF multiple
of the genuine posterior spin covariance and that covariance. The proof uses
the actual upward-grid suffix; every CDF atom is preserved. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def anisotropicFiniteTailCovarianceQuadratic (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (w : Field n) : ℝ :=
  ∑i : Fin n,∑j : Fin n,(anisotropicFiniteTailPairResponse D s q P (anisotropicOrderedCoupling i j)-
    anisotropicFiniteTailMagnetization D s q P i*anisotropicFiniteTailMagnetization D s q P j)*w i*w j

theorem tendsto_anisotropicFiniteTailCovarianceQuadratic_moving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) {qj : ℕ→Paper.Overlap} {q : Paper.Overlap}
    {Pj : ℕ→AnisotropicParameter n} {P : AnisotropicParameter n} {wj : ℕ→Field n} {w : Field n}
    (hq : Tendsto qj atTop (𝓝 q)) (hP : Tendsto Pj atTop (𝓝 P)) (hw : Tendsto wj atTop (𝓝 w)) :
    Tendsto (fun j=>anisotropicFiniteTailCovarianceQuadratic D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (qj j) (Pj j) (wj j)) atTop
        (𝓝 (anisotropicTailCovarianceQuadratic D μ q P w)) := by
  have hm := (tendstoUniformly_anisotropicFiniteDyadicTailMagnetization D μ).tendsto_comp
    (continuous_anisotropicMeasureTailMagnetization_joint D μ).continuousAt (hq.prodMk_nhds hP)
  unfold anisotropicFiniteTailCovarianceQuadratic anisotropicTailCovarianceQuadratic anisotropicTailSpinCovariance
  apply tendsto_finset_sum
  intro i _
  apply tendsto_finset_sum
  intro l _
  have hi := (EuclideanSpace.proj i).continuous.continuousAt.tendsto.comp hm
  have hl := (EuclideanSpace.proj l).continuous.continuousAt.tendsto.comp hm
  have hwi := (EuclideanSpace.proj i).continuous.continuousAt.tendsto.comp hw
  have hwl := (EuclideanSpace.proj l).continuous.continuousAt.tendsto.comp hw
  exact (((tendsto_anisotropicFiniteTailPairResponse_moving D μ (anisotropicOrderedCoupling i l) hq hP).sub
    (hi.mul hl)).mul hwi).mul hwl

theorem anisotropicCascadeDepthMass_node (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+2) :
    finiteStateCascadeDepthMass (anisotropicSchemeMass s) (k+2-i)=s.m (min i (k+1)) := by
  unfold finiteStateCascadeDepthMass
  by_cases hz : k+2-i=0
  · have he : i=k+2 := by omega
    rw [if_pos hz,he,Nat.min_eq_right (by omega : k+1 ≤ k+2)]
    exact s.m_top.symm
  · rw [if_neg hz,anisotropicSchemeMass,Nat.min_eq_left (by omega : i ≤ k+1)]
    congr 1
    omega

theorem anisotropicFiniteTail_covariance_bounds_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+2) (P : AnisotropicParameter n) (w : Field n) :
    s.m (min i (k+1))*anisotropicFiniteTailCovarianceQuadratic D s (anisotropicSchemeNode s i hi) P w ≤
      fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s (anisotropicSchemeNode s i hi))) P
        (anisotropicFieldInjection n w) (anisotropicFieldInjection n w) ∧
    fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s (anisotropicSchemeNode s i hi))) P
        (anisotropicFieldInjection n w) (anisotropicFieldInjection n w) ≤
          anisotropicFiniteTailCovarianceQuadratic D s (anisotropicSchemeNode s i hi) P w := by
  have h:=anisotropicFieldHessian_covariance_bounds D s (k+2-i) P w
  rw [anisotropicCascadeDepthMass_node s i hi,anisotropicFieldHessian_quadratic_eq_parameter,
    anisotropicSpinCovarianceEnergy_node_eq_pairExpansion D s i hi] at h
  rw [anisotropicFiniteTailPotential_node]
  exact h

theorem anisotropicMeasureTail_covariance_bounds (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (w : Field n) :
    Paper.parisiCDF μ q*anisotropicTailCovarianceQuadratic D μ q P w ≤
      fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P
        (anisotropicFieldInjection n w) (anisotropicFieldInjection n w) ∧
    fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P
        (anisotropicFieldInjection n w) (anisotropicFieldInjection n w) ≤
          anisotropicTailCovarianceQuadratic D μ q P w := by
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let ij:=fun j=>anisotropicGridNodeIndex (vectorDyadicIndex j) q
  let qj:=fun j=>Paper.parisiGridRound (vectorDyadicIndex j) q
  have hi (j : ℕ) : ij j ≤ (vectorDyadicIndex j+1)+2 := by
    have h:=anisotropicGridNodeIndex_le (vectorDyadicIndex j) q
    dsimp only [ij]
    omega
  have hn (j : ℕ) : anisotropicSchemeNode (sj j) (ij j) (hi j)=qj j :=
    anisotropicGridNode_eq_round μ (vectorDyadicIndex j) q
  have hq : Tendsto qj atTop (𝓝 q):=(Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex
  have hC:=tendsto_anisotropicFiniteTailCovarianceQuadratic_moving D μ hq
    (tendsto_const_nhds (x:=P)) (tendsto_const_nhds (x:=w))
  have hT := (tendstoUniformly_anisotropicDyadicTailSecondDifferential D μ).tendsto_comp
    (continuous_anisotropicMeasureTailSecondDifferential_joint D μ).continuousAt
      (hq.prodMk_nhds (tendsto_const_nhds (x:=P)))
  have hev : Continuous (fun T : AnisotropicParameter n→L[ℝ](AnisotropicParameter n→L[ℝ]ℝ)=>
      T (anisotropicFieldInjection n w) (anisotropicFieldInjection n w)) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  have hH:=hev.continuousAt.tendsto.comp hT
  have ha:=tendsto_anisotropicGridNode_mass μ q
  have hbound (j : ℕ) := anisotropicFiniteTail_covariance_bounds_node D (sj j) (ij j) (hi j) P w
  simp_rw [hn] at hbound
  have hcoeff (j : ℕ) : min (ij j) (vectorDyadicIndex j+1+1)=ij j := by
    apply Nat.min_eq_left
    have h:=anisotropicGridNodeIndex_le (vectorDyadicIndex j) q
    dsimp only [ij]
    omega
  simp only [sj,hcoeff] at hbound
  constructor
  · exact le_of_tendsto_of_tendsto (ha.mul hC) hH (.of_forall fun j=>(hbound j).1)
  · exact le_of_tendsto_of_tendsto hH hC (.of_forall fun j=>(hbound j).2)

end QuantitativeFollowup
