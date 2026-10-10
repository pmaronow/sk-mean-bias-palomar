module
public import QuantitativeFollowup.FollowupCavityDecouplingTail
public import QuantitativeFollowup.AnisotropicWhitening

@[expose] public section

/-! Derivatives of the actual separated profile, obtained by differentiating
the proved potential equality. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem followupCavityMeasureGradient_pairing_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x w : QuantitativePaper.Field (n+1)) :
    inner ℝ (anisotropicMeasureTailMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q
      (anisotropicParameterPoint g x)) w=
      inner ℝ (anisotropicMeasureTailMagnetization (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)))
        (cavityRestFieldProjection n w)+
      Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))*w (Fin.last n) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let P:=anisotropicParameterPoint g x
  let Pr:=anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)
  have hf:=hasDerivAt_affine_line_of_differentiable (anisotropicMeasureTailPotential D μ q)
    (anisotropicMeasureTailPotential_derivative_limit D μ q).2.differentiable_one
    P (anisotropicFieldInjection (n+1) w) 0
  have hr:=hasDerivAt_affine_line_of_differentiable (anisotropicMeasureTailPotential R μ q)
    (anisotropicMeasureTailPotential_derivative_limit R μ q).2.differentiable_one
    Pr (anisotropicFieldInjection n (cavityRestFieldProjection n w)) 0
  have hg : HasDerivAt (fun y=>Paper.parisiPotential (followupCavityScalarBeta n β ρ) μ (q,y))
      (Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n)))
      (x (Fin.last n)+id (0:ℝ)*w (Fin.last n)) := by
    simpa only [id_eq,zero_mul,add_zero] using Paper.hasDerivAt_parisiPotential_spatial_all
      (followupCavityScalarBeta n β ρ) μ q (x (Fin.last n)) q.property
  have hs:=hg.comp 0
      (((hasDerivAt_id (0:ℝ)).mul_const (w (Fin.last n))).const_add (x (Fin.last n)))
  have he : (fun z : ℝ=>anisotropicMeasureTailPotential D μ q
      (P+z • anisotropicFieldInjection (n+1) w))=
      fun z=>anisotropicMeasureTailPotential R μ q
        (Pr+z • anisotropicFieldInjection n (cavityRestFieldProjection n w))+
        (Real.log 2+Paper.parisiPotential (followupCavityScalarBeta n β ρ) μ
          (q,x (Fin.last n)+z*w (Fin.last n))) := by
    funext z
    rw [←map_smul,cavityAnisotropicPoint_add_field,
      followupCavityMeasureTailPotential_zero]
    simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    rw [←(anisotropicFieldInjection n).map_smul,cavityAnisotropicPoint_add_field]
  rw [he] at hf
  have hu:=hf.unique (hr.add (hs.const_add (Real.log 2)))
  simpa only [zero_smul,add_zero,zero_mul,fderiv_anisotropicMeasureTailPotential_field,
    add_zero,one_mul,D,R,P,Pr] using hu

theorem cavityRestFieldProjection_single {n : ℕ} (i : Fin n) :
    cavityRestFieldProjection n (EuclideanSpace.single i.castSucc (1:ℝ))=
      EuclideanSpace.single i (1:ℝ) := by
  ext j
  simp [cavityRestFieldProjection_apply, EuclideanSpace.single_apply]

theorem cavityRestFieldProjection_single_last (n : ℕ) :
    cavityRestFieldProjection n (EuclideanSpace.single (Fin.last n) (1:ℝ))=0 := by
  ext j
  simp [cavityRestFieldProjection_apply, EuclideanSpace.single_apply]

theorem followupCavityMeasureGradient_rest_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    cavityRestFieldProjection n (anisotropicMeasureTailMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q
      (anisotropicParameterPoint g x))=
      anisotropicMeasureTailMagnetization (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)) := by
  ext i
  have hh:=followupCavityMeasureGradient_pairing_zero μ n β ρ hβ hρ q g x
    (EuclideanSpace.single i.castSucc (1:ℝ))
  simpa [cavityRestFieldProjection_single, cavityRestFieldProjection_apply,
    EuclideanSpace.inner_single_right, EuclideanSpace.single_apply] using hh

theorem followupCavityMeasureGradient_last_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    anisotropicMeasureTailMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q
      (anisotropicParameterPoint g x) (Fin.last n)=
      Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n)) := by
  have hh:=followupCavityMeasureGradient_pairing_zero μ n β ρ hβ hρ q g x
    (EuclideanSpace.single (Fin.last n) (1:ℝ))
  simpa [cavityRestFieldProjection_single_last, EuclideanSpace.inner_single_right,
    EuclideanSpace.single_apply] using hh

end QuantitativeFollowup
