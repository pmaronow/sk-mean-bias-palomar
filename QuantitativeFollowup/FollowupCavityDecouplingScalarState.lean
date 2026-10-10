module
public import QuantitativeFollowup.FollowupCavityDecouplingState
public import Paper.ParisiSelectedState

@[expose] public section

/-! The last selected coordinate is the actual scalar Parisi diffusion
driven by the last Wiener coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem cavityLastDrivenDrift_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (r : ℝ) (p : AnisotropicDisorderBrownianSample (n+1))
    (y : QuantitativePaper.Field (n+1)) :
    anisotropicDrivenDrift (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ p r y
      (Fin.last n)=
      followupCavityD n β ρ*Paper.parisiCDF μ r*
        Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ
          ((projIcc (0:ℝ) 1 zero_le_one r:ℝ), y (Fin.last n)+
            followupCavityScalarBeta n β ρ*Paper.canonicalBrownian r.toNNReal (p.2 (Fin.last n))) := by
  unfold anisotropicDrivenDrift anisotropicDrivenParameter
  rw [PiLp.smul_apply,anisotropicVarianceMap_apply,anisotropicDisorderInjection_apply,
    ←anisotropicParameterPoint_field,followupCavityMeasureGradient_last_zero]
  simp only [smul_eq_mul,PiLp.add_apply,anisotropicWienerNoise]
  rw [cavityLastNoise_zero,followupCavitySpinModel_variance_last,followupCavityB_zero]
  simp only [vectorBrownian_apply,followupCavityScalarBeta]
  ring

theorem cavityLastMeasureState_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (r : ℝ) (hr : r∈Icc (0:ℝ) 1)
    (p : AnisotropicDisorderBrownianSample (n+1)) :
    anisotropicMeasureState (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ r p
      (Fin.last n)=
      Paper.selectedParisiStateReal (followupCavityScalarBeta n β ρ) 0
        (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ (p.2 (Fin.last n)) r := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let β0:=followupCavityScalarBeta n β ρ
  let W:=fun s : ℝ=>Paper.canonicalBrownian s.toNNReal (p.2 (Fin.last n))
  let X:=fun s : ℝ=>anisotropicMeasureState D μ s p (Fin.last n)
  have hβ0 : β0≠0 := (followupCavityScalarBeta_pos n β ρ hβ hρ).ne'
  have hW : Continuous W := (Paper.continuous_canonicalBrownian _).comp continuous_real_toNNReal
  have hX : Continuous X := (EuclideanSpace.proj (Fin.last n)).continuous.comp
    (continuous_anisotropicMeasureState D μ p)
  have hXe (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      X t=0+β0*W t+∫s in 0..t,β0^2*Paper.parisiCDF μ s*Paper.parisiGradient β0 μ (s,X s) := by
    have hf:=isBounded_anisotropicDrivenDrift D μ p
    have hi : IntervalIntegrable (fun s=>anisotropicDrivenDrift D μ p s (anisotropicDriftCorrection D μ s p))
        volume 0 t := by
      apply (intervalIntegrable_const (c:=(anisotropicDriftBound D:ℝ))).mono_fun'
        (hf.measurable.comp (measurable_id.prodMk
          (ODE.FunSpace.continuous_compProj _).measurable)).aestronglyMeasurable
      exact .of_forall fun s=>hf.norm_le s _
    have hh:=congrArg (EuclideanSpace.proj (Fin.last n)) (anisotropicDriftCorrection_equation D μ p t ht)
    rw [←(EuclideanSpace.proj (Fin.last n)).intervalIntegral_comp_comm hi] at hh
    change anisotropicDriftCorrection D μ t p (Fin.last n)=
      ∫s in 0..t,anisotropicDrivenDrift D μ p s (anisotropicDriftCorrection D μ s p) (Fin.last n) at hh
    change anisotropicDriftCorrection D μ t p (Fin.last n)+anisotropicWienerNoise D t p (Fin.last n)=_
    rw [hh]
    have hn : anisotropicWienerNoise D t p (Fin.last n)=β0*W t := cavityLastNoise_zero n β ρ hβ hρ _
    rw [hn,zero_add]
    refine (add_comm (∫s in 0..t,anisotropicDrivenDrift D μ p s (anisotropicDriftCorrection D μ s p)
      (Fin.last n)) (β0*W t)).trans ?_
    apply congrArg (fun z : ℝ=>β0*W t+z)
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hs1 : s∈Icc (0:ℝ) 1:=⟨hs.1,hs.2.trans ht.2⟩
    dsimp only [D]
    rw [cavityLastDrivenDrift_zero,projIcc_of_mem zero_le_one hs1]
    have hb0 : β0^2=followupCavityD n β ρ:=Real.sq_sqrt (followupCavityD_pos n β ρ hβ hρ).le
    rw [hb0]
    congr 2
    change (s,anisotropicDriftCorrection D μ s p (Fin.last n)+β0*W s)=(s,X s)
    apply congrArg (fun z : ℝ=>(s,z))
    change anisotropicDriftCorrection D μ s p (Fin.last n)+β0*W s=X s
    dsimp only [X,anisotropicMeasureState]
    simp only [PiLp.add_apply]
    congr 1
    exact (cavityLastNoise_zero n β ρ hβ hρ (vectorBrownian s.toNNReal p.2)).symm
  have hv : Continuous (Function.uncurry (fun s x=>Paper.parisiGradient β0 μ (s,x))) :=
    Paper.continuous_parisiGradient β0 μ
  have hb := fun s x=>Paper.norm_parisiGradient_le_one β0 μ (s,x)
  have hl:=Paper.lipschitzWith_parisiGradient β0 hβ0 μ
  have hx:=Paper.parisiStateReal_unique β0 0 μ _ hv hb hl 1 zero_le_one W hW X hX hXe hr
  have hy:=Paper.parisiStateReal_unique β0 0 μ _ hv hb hl 1 zero_le_one W hW
    (Paper.selectedParisiStateReal β0 0 hβ0 μ (p.2 (Fin.last n)))
    (Paper.continuous_selectedParisiStateReal β0 0 hβ0 μ _) (fun t ht=>
      Paper.selectedParisiState_integral_equation β0 0 hβ0 μ _ ht) hr
  exact hx.trans hy.symm

end QuantitativeFollowup
