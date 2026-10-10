module
public import QuantitativeFollowup.FourDescendantNativeLaw

@[expose] public section

/-! Literal spin-product moments under two and four genuine independent
conditional terminal draws, evaluated against the actual native process. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem cavityFreshTerminalPairLaw_selected_overlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (J : Finset (Fin n)) :
    (∫z,cavitySelectedSpinOverlap J z.2.1 z.2.2∂anisotropicFreshTerminalPairLaw D μ a q)=
      ∫sample,anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)
        ∂anisotropicMeasureSampleLaw D μ a := by
  let F:=fun z : Configuration n×Configuration n=>cavitySelectedSpinOverlap J z.1 z.2
  let B:=∑z : Configuration n×Configuration n,‖F z‖
  have hi : Integrable (fun z : (AnisotropicDisorderBrownianSample n×Configuration n)×
      (Configuration n×Configuration n)=>F z.2) (anisotropicFreshTerminalPairLaw D μ a q):=
    bounded_real_integrable _ ((measurable_of_finite F).comp measurable_snd) B
      (fun z=>Finset.single_le_sum (fun x _=>norm_nonneg (F x)) (Finset.mem_univ z.2))
  change (∫z,F z.2∂anisotropicFreshTerminalPairLaw D μ a q)=_
  rw [anisotropicFreshTerminalPairLaw,Measure.integral_compProd hi]
  simp only [Kernel.prod_apply]
  change (∫p,(∫z,cavitySelectedSpinOverlap J z.1 z.2
    ∂(anisotropicFreshTerminalSpinKernel D μ a q p).prod
      (anisotropicFreshTerminalSpinKernel D μ a q p))
    ∂anisotropicMeasureSpinPathLaw D μ a)=_
  simp_rw [integral_cavitySelectedSpinOverlap_product]
  have hk (i : Fin n):=
    (anisotropicFreshTerminalSpinKernel_conditional_mean D μ a q (fun σ=>Paper.spinSign (σ i))).symm.trans
      (anisotropicMeasureSpinPathLaw_spin_condExp D μ a q i)
  have hs : (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
      (∑i∈J,(∫σ,Paper.spinSign (σ i)∂anisotropicFreshTerminalSpinKernel D μ a q p)^2)/(J.card:ℝ))
      =ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q p.1):=by
    filter_upwards [ae_all_iff.mpr hk] with p hp
    unfold anisotropicSelectedMeanSquare
    congr 1
    exact Finset.sum_congr rfl fun i _=>congrArg (fun x : ℝ=>x^2) (hp i)
  rw [integral_congr_ae hs]
  exact integral_anisotropicMeasureSpinPathLaw_sample D μ a _
    ((continuous_anisotropicSelectedMeanSquare J).measurable.comp
      ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp
        (measurable_const.prodMk measurable_id)))

 theorem cavityFourDescendantLaw_spin_overlap_product (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n) (J : Finset (Fin n)) :
    (∫z,Paper.spinSign (z.2.1.1 i)*Paper.spinSign (z.2.1.2 i)*
      (cavitySelectedSpinOverlap J z.2.2.1 z.2.2.2-(q:ℝ))∂cavityFourDescendantLaw D μ a q)=
      ∫sample,(anisotropicProcessMagnetization D μ q sample i)^2*
        (anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q sample)-(q:ℝ))
        ∂anisotropicMeasureSampleLaw D μ a := by
  let F:=fun z : CavityFourTerminalSpins n=>Paper.spinSign (z.1.1 i)*Paper.spinSign (z.1.2 i)*
    (cavitySelectedSpinOverlap J z.2.1 z.2.2-(q:ℝ))
  let B:=∑z : CavityFourTerminalSpins n,‖F z‖
  have hi : Integrable (fun z : (AnisotropicDisorderBrownianSample n×Configuration n)×
      CavityFourTerminalSpins n=>F z.2) (cavityFourDescendantLaw D μ a q):=
    bounded_real_integrable _ ((measurable_of_finite F).comp measurable_snd) B
      (fun z=>Finset.single_le_sum (fun x _=>norm_nonneg (F x)) (Finset.mem_univ z.2))
  change (∫z,F z.2∂cavityFourDescendantLaw D μ a q)=_
  rw [cavityFourDescendantLaw,Measure.integral_compProd hi]
  have he (p : AnisotropicDisorderBrownianSample n×Configuration n) :
      (∫z,F z∂(((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ
        (anisotropicFreshTerminalSpinKernel D μ a q)) ×ₖ
        ((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ
          (anisotropicFreshTerminalSpinKernel D μ a q))) p)=
      (∫σ,Paper.spinSign (σ i)∂anisotropicFreshTerminalSpinKernel D μ a q p)^2*
        ((∑j∈J,(∫σ,Paper.spinSign (σ j)∂anisotropicFreshTerminalSpinKernel D μ a q p)^2)/
          (J.card:ℝ)-(q:ℝ)):=by
    simp only [Kernel.prod_apply]
    rw [integral_prod_mul (f:=fun z : Configuration n×Configuration n=>
      Paper.spinSign (z.1 i)*Paper.spinSign (z.2 i))
      (g:=fun z : Configuration n×Configuration n=>cavitySelectedSpinOverlap J z.1 z.2-(q:ℝ))]
    have hr : Integrable (fun z : Configuration n×Configuration n=>cavitySelectedSpinOverlap J z.1 z.2)
        ((anisotropicFreshTerminalSpinKernel D μ a q p).prod
          (anisotropicFreshTerminalSpinKernel D μ a q p)):=
      bounded_real_integrable _ (measurable_of_finite _) (∑z : Configuration n×Configuration n,
        ‖cavitySelectedSpinOverlap J z.1 z.2‖)
        (fun z=>Finset.single_le_sum (fun x _=>norm_nonneg (cavitySelectedSpinOverlap J x.1 x.2))
          (Finset.mem_univ z))
    have hspin := integral_prod_mul
      (f:=fun σ : Configuration n=>Paper.spinSign (σ i))
      (g:=fun σ : Configuration n=>Paper.spinSign (σ i))
      (μ:=anisotropicFreshTerminalSpinKernel D μ a q p)
      (ν:=anisotropicFreshTerminalSpinKernel D μ a q p)
    rw [hspin,integral_sub hr (integrable_const _),integral_const,
      probReal_univ,one_smul,integral_cavitySelectedSpinOverlap_product,pow_two]
  simp_rw [he]
  have hk (j : Fin n):=
    (anisotropicFreshTerminalSpinKernel_conditional_mean D μ a q (fun σ=>Paper.spinSign (σ j))).symm.trans
      (anisotropicMeasureSpinPathLaw_spin_condExp D μ a q j)
  have hs : (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
      (∫σ,Paper.spinSign (σ i)∂anisotropicFreshTerminalSpinKernel D μ a q p)^2*
        ((∑j∈J,(∫σ,Paper.spinSign (σ j)∂anisotropicFreshTerminalSpinKernel D μ a q p)^2)/
          (J.card:ℝ)-(q:ℝ)))=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>(anisotropicProcessMagnetization D μ q p.1 i)^2*
        (anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q p.1)-(q:ℝ)):=by
    filter_upwards [ae_all_iff.mpr hk] with p hp
    rw [hp i]
    simp only [anisotropicSelectedMeanSquare]
    congr 3
    exact Finset.sum_congr rfl fun j _=>congrArg (fun x : ℝ=>x^2) (hp j)
  rw [integral_congr_ae hs]
  have hm : Measurable (anisotropicProcessMagnetization D μ q) := by
    have hm0 := (measurable_uncurry_anisotropicProcessMagnetization D μ).comp
      ((measurable_const (a:=q)).prodMk measurable_id)
    simpa only [Function.comp_def,id_eq] using hm0
  exact integral_anisotropicMeasureSpinPathLaw_sample D μ a _
    (((EuclideanSpace.proj i).measurable.comp hm).pow_const 2 |>.mul
      (((continuous_anisotropicSelectedMeanSquare J).measurable.comp hm).sub measurable_const))

end QuantitativeFollowup
