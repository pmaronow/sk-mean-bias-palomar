module
public import FourPapersCommon.GaussianSelectedSpatialHeatC2
public import FourPapersCommon.MovingMeanValueAtBoundary

@[expose] public section

/-! Genuine selected-heat response at variance zero for a moving C2 test.
The parameter requires joint Hessian continuity, with no derivative in it. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gaussianSelectedSpatialTrace (p : ι→Bool) (F : ℝ×EuclideanSpace ℝ ι→ℝ)
    (b : ℝ) (y : EuclideanSpace ℝ ι) : ℝ :=
  ∑i,if p i then fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y
    (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0

theorem continuous_gaussianSelectedSpatialTrace_slice (p : ι→Bool)
    (F : ℝ×EuclideanSpace ℝ ι→ℝ) (b : ℝ)
    (hF : ContDiff ℝ 2 (fun y=>F (b,y))) :
    Continuous (gaussianSelectedSpatialTrace p F b) := by
  have hc := (hF.fderiv_right (m:=1) (by norm_num)).continuous_fderiv (by norm_num)
  unfold gaussianSelectedSpatialTrace
  apply continuous_finsetSum
  intro i _
  by_cases hi : p i=true
  · simp only [hi,ite_true]
    exact (hc.clm_apply continuous_const).clm_apply continuous_const
  · simp only [if_neg hi]
    exact continuous_const

theorem gaussianSelectedSpatialTrace_bound (p : ι→Bool)
    (F : ℝ×EuclideanSpace ℝ ι→ℝ) (b B K : ℝ) (hB : 0 ≤ B)
    (h2 : ∀y,‖fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y‖ ≤ B*Real.exp (K*‖y‖))
    (y : EuclideanSpace ℝ ι) :
    ‖gaussianSelectedSpatialTrace p F b y‖ ≤ (Fintype.card ι:ℝ)*B*Real.exp (K*‖y‖) := by
  unfold gaussianSelectedSpatialTrace
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑_i:ι,B*Real.exp (K*‖y‖) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : p i=true
      · simp only [hi,ite_true]
        calc
          _ ≤ ‖fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y (EuclideanSpace.basisFun ι ℝ i)‖*
              ‖EuclideanSpace.basisFun ι ℝ i‖ :=
            (fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y (EuclideanSpace.basisFun ι ℝ i)).le_opNorm _
          _ ≤ B*Real.exp (K*‖y‖) := by
            rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one]
            exact ((fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y).le_opNorm
              (EuclideanSpace.basisFun ι ℝ i)).trans
              (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one];exact h2 y)
      · simp only [if_neg hi,norm_zero]
        positivity
    _ = _ := by simp [mul_assoc]

theorem continuousAt_gaussianSelectedSpatialTrace_integral (p : ι→Bool)
    (F : ℝ×EuclideanSpace ℝ ι→ℝ) (l r d B K : ℝ)
    (hd : d ∈ Ioo l r) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hF : ∀ b ∈ Ioo l r, ContDiff ℝ 2 (fun y=>F (b,y)))
    (hH : ∀ i, p i=true → ContinuousOn (fun z : ℝ×EuclideanSpace ℝ ι=>
      fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) z.2
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i))
      ((Ioo l r)×ˢ(univ : Set (EuclideanSpace ℝ ι))))
    (h2 : ∀ b ∈ Ioo l r, ∀y,
      ‖fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y‖ ≤ B*Real.exp (K*‖y‖)) :
    ContinuousAt (fun z : ℝ×ℝ=>∫w : EuclideanSpace ℝ ι,
      gaussianSelectedSpatialTrace p F z.1 (gaussianSelectedScale p z.2 w)
        ∂stdGaussian (EuclideanSpace ℝ ι)) (d,0) := by
  let A : ℝ := 2*(Fintype.card ι:ℝ)
  have hb : ∀ᶠ z : ℝ×ℝ in 𝓝 (d,0), z.1 ∈ Ioo l r :=
    continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hd)
  have hv : ∀ᶠ z : ℝ×ℝ in 𝓝 (d,0), z.2 < 1 :=
    continuous_snd.continuousAt.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  apply continuousAt_of_dominated
    (bound:=fun w : EuclideanSpace ℝ ι=>(Fintype.card ι:ℝ)*B*Real.exp ((K*A)*‖w‖))
  · filter_upwards [hb] with z hzb
    exact ((continuous_gaussianSelectedSpatialTrace_slice p F z.1 (hF z.1 hzb)).comp
      (gaussianSelectedScale p z.2).continuous).aestronglyMeasurable
  · filter_upwards [hb,hv] with z hzb hzv
    exact .of_forall fun w=>by
      apply (gaussianSelectedSpatialTrace_bound p F z.1 B K hB (h2 z.1 hzb) _).trans
      have hs : ‖gaussianSelectedScale p z.2 w‖ ≤ A*‖w‖ := by
        have hh := norm_gaussianSelectedScale_le p z.2 1 hzv.le w
        convert hh using 1 <;> simp only [Real.sqrt_one,A] <;> ring
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      exact (mul_le_mul_of_nonneg_left hs hK).trans_eq (by ring)
  · exact (integrable_exp_mul_norm_gaussian (stdGaussian (EuclideanSpace ℝ ι)) (K*A)).const_mul
      ((Fintype.card ι:ℝ)*B)
  · exact .of_forall fun w=>by
      have hs : ContinuousAt (fun z : ℝ×ℝ=>(z.1,gaussianSelectedScale p z.2 w)) (d,0) :=
        continuous_fst.continuousAt.prodMk
          ((continuous_gaussianSelectedScale_apply p w).comp continuous_snd).continuousAt
      let Q := fun (i : ι) (z : ℝ×ℝ)=>if p i then
        fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) (gaussianSelectedScale p z.2 w)
          (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0
      have hQ (i : ι) : ContinuousAt (Q i) (d,0) := by
        dsimp only [Q]
        by_cases hi : p i=true
        · simp only [hi,ite_true]
          exact ((hH i hi).continuousAt
            ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hd,mem_univ _⟩)).comp hs
        · simp only [if_neg hi]
          exact continuous_const.continuousAt
      have hsum (s : Finset ι) : ContinuousAt (fun z : ℝ×ℝ=>∑i∈s,Q i z) (d,0) := by
        induction s using Finset.induction_on with
        | empty => simpa only [Finset.sum_empty] using (continuous_const (y:=(0:ℝ))).continuousAt
        | @insert i s hi ih =>
          simp_rw [Finset.sum_insert hi]
          exact (hQ i).add ih
      exact hsum Finset.univ

theorem hasDerivWithinAt_gaussianSelected_moving_heat_zero (p : ι→Bool)
    (F : ℝ×EuclideanSpace ℝ ι→ℝ) (l r d alpha B K : ℝ)
    (hd : d ∈ Ioo l r) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hF : ∀ b ∈ Ioo l r, ContDiff ℝ 2 (fun y=>F (b,y)))
    (hH : ∀ i, p i=true → ContinuousOn (fun z : ℝ×EuclideanSpace ℝ ι=>
      fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) z.2
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i))
      ((Ioo l r)×ˢ(univ : Set (EuclideanSpace ℝ ι))))
    (h0 : ∀ b ∈ Ioo l r, ∀y, ‖F (b,y)‖ ≤ B*Real.exp (K*‖y‖))
    (h1 : ∀ b ∈ Ioo l r, ∀y, ‖fderiv ℝ (fun z=>F (b,z)) y‖ ≤ B*Real.exp (K*‖y‖))
    (h2 : ∀ b ∈ Ioo l r, ∀y,
      ‖fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y‖ ≤ B*Real.exp (K*‖y‖)) :
    HasDerivWithinAt (fun v=>∫z : EuclideanSpace ℝ ι,
        (F (d-alpha*v,gaussianSelectedScale p v z)-F (d-alpha*v,gaussianSelectedScale p 0 z))
        ∂stdGaussian (EuclideanSpace ℝ ι))
      ((1/2:ℝ)*∫z : EuclideanSpace ℝ ι,
        gaussianSelectedSpatialTrace p F d (gaussianSelectedScale p 0 z)
        ∂stdGaussian (EuclideanSpace ℝ ι)) (Ici (0:ℝ)) 0 := by
  let H : ℝ→ℝ→ℝ := fun b v=>gaussianSelectedSpatialHeat p (fun y=>F (b,y)) v
  let J : ℝ→ℝ→ℝ := fun b v=>(1/2:ℝ)*∫z : EuclideanSpace ℝ ι,
    gaussianSelectedSpatialTrace p F b (gaussianSelectedScale p v z) ∂stdGaussian (EuclideanSpace ℝ ι)
  have hcont (b : ℝ) (hb : b ∈ Ioo l r) : ContinuousOn (H b) (Icc (0:ℝ) 1) :=
    (continuous_gaussianSelectedSpatialHeat p (fun y=>F (b,y)) (hF b hb).continuous
      B K hB hK (h0 b hb)).continuousOn
  have hder (b : ℝ) (hb : b ∈ Ioo l r) (v : ℝ) (hv : v ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (H b) (J b v) v :=
    hasDerivAt_gaussianSelectedSpatialHeat p (fun y=>F (b,y)) (hF b hb)
      B K hB hK (h0 b hb) (h1 b hb) (h2 b hb) v hv.1
  have hJ : ContinuousAt (fun z : ℝ×ℝ=>J z.1 z.2) (d,0) :=
    continuous_const.continuousAt.mul
      (continuousAt_gaussianSelectedSpatialTrace_integral p F l r d B K hd hB hK hF hH h2)
  have hm := hasDerivWithinAt_moving_increment_zero H J (Ioo l r) d alpha
    (isOpen_Ioo.mem_nhds hd) hcont hder hJ
  have he : (fun v=>∫z : EuclideanSpace ℝ ι,
      (F (d-alpha*v,gaussianSelectedScale p v z)-F (d-alpha*v,gaussianSelectedScale p 0 z))
      ∂stdGaussian (EuclideanSpace ℝ ι))=ᶠ[𝓝 (0:ℝ)]
      (fun v=>H (d-alpha*v) v-H (d-alpha*v) 0) := by
    have hbcont : Continuous (fun v : ℝ=>d-alpha*v) := by fun_prop
    have hb : ∀ᶠ v : ℝ in 𝓝 (0:ℝ), d-alpha*v ∈ Ioo l r := by
      have ht : Tendsto (fun v : ℝ=>d-alpha*v) (𝓝 0) (𝓝 d) := by
        simpa only [mul_zero,sub_zero] using hbcont.continuousAt.tendsto (x:=0)
      exact ht.eventually (isOpen_Ioo.mem_nhds hd)
    filter_upwards [hb] with v hbv
    have hi (u : ℝ) : Integrable (fun z : EuclideanSpace ℝ ι=>F (d-alpha*v,gaussianSelectedScale p u z))
        (stdGaussian (EuclideanSpace ℝ ι)) := by
      apply integrable_gaussian_exponential_bound _ _
        (((hF (d-alpha*v) hbv).continuous.comp (gaussianSelectedScale p u).continuous).measurable)
        B (K*((Fintype.card ι:ℝ)*(1+Real.sqrt u))) hB
      intro z
      apply (h0 _ hbv _).trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
      exact (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p u u le_rfl z) hK).trans_eq (by ring)
    exact integral_sub (hi v) (hi 0)
  exact hm.congr_of_eventuallyEq_of_mem (he.filter_mono nhdsWithin_le_nhds) (by simp)

end FourPapersCommon
