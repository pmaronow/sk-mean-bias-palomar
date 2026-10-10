module
public import QuantitativeFollowup.FollowupCavityCppFourDescendantMoments
public import QuantitativeFollowup.FollowupCavityCppDefinitions

@[expose] public section

/-! The literal native cavity covariance equals the four-descendant spin
moment minus the product of its two binary moments. All draws use the
actual regular conditional terminal-spin kernel given the entire past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem cavitySelectedMeanSquare_erased_last_projection (v : QuantitativePaper.Field (n+1)) :
    anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n)) v=
      anisotropicSelectedMeanSquare Finset.univ (cavityRestFieldProjection n v) := by
  unfold anisotropicSelectedMeanSquare
  simp only [Finset.card_erase_of_mem (Finset.mem_univ (Fin.last n)),Finset.card_univ,
    Fintype.card_fin,Nat.add_sub_cancel,cavityRestFieldProjection_apply]
  congr 1
  have h1:=Finset.sum_erase_add (Finset.univ:Finset (Fin (n+1)))
    (fun i=>v i^2) (Finset.mem_univ (Fin.last n))
  have h2:=Fin.sum_univ_castSucc (fun i:Fin (n+1)=>v i^2)
  linarith

 theorem cavityProcessSpinSelectedCovariance_eq_four_descendants (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n) (J : Finset (Fin n)) :
    covariance (fun ω=>anisotropicProcessMagnetization D μ q ω i^2)
      (fun ω=>anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q ω))
      (anisotropicMeasureSampleLaw D μ a)=
    (∫z,Paper.spinSign (z.2.1.1 i)*Paper.spinSign (z.2.1.2 i)*
      (cavitySelectedSpinOverlap J z.2.2.1 z.2.2.2-(q:ℝ))∂cavityFourDescendantLaw D μ a q)-
    (∫z,Paper.spinSign (z.2.1 i)*Paper.spinSign (z.2.2 i)
      ∂anisotropicFreshTerminalPairLaw D μ a q)*
    (∫z,cavitySelectedSpinOverlap J z.2.1 z.2.2-(q:ℝ)
      ∂anisotropicFreshTerminalPairLaw D μ a q) := by
  let P:=anisotropicMeasureSampleLaw D μ a
  let X:=fun ω : AnisotropicDisorderBrownianSample n=>anisotropicProcessMagnetization D μ q ω i^2
  let Y:=fun ω : AnisotropicDisorderBrownianSample n=>
    anisotropicSelectedMeanSquare J (anisotropicProcessMagnetization D μ q ω)
  have hm : Measurable (anisotropicProcessMagnetization D μ q):=by
    have hm0:=(measurable_uncurry_anisotropicProcessMagnetization D μ).comp
      ((measurable_const (a:=q)).prodMk measurable_id)
    simpa only [Function.comp_def,id_eq] using hm0
  have hx : MemLp X 2 P:=by
    apply MemLp.of_bound ((measurable_anisotropicProcessSpinResponse D μ q i).pow_const 2).aestronglyMeasurable 1
    exact .of_forall fun ω=>by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _)
        (anisotropicProcessSpinResponse_bound D μ q i ω) 2).trans_eq (by norm_num)
  have hy : MemLp Y 2 P:=MemLp.of_bound
    ((continuous_anisotropicSelectedMeanSquare J).measurable.comp hm).aestronglyMeasurable 1
    (.of_forall fun ω=>anisotropicSelectedMeanSquare_bound J _
      (fun j=>anisotropicProcessSpinResponse_bound D μ q j ω))
  have hpair :
      (∫z,cavitySelectedSpinOverlap J z.2.1 z.2.2-(q:ℝ)
        ∂anisotropicFreshTerminalPairLaw D μ a q)=(∫ω,Y ω∂P)-(q:ℝ):=by
    have hi : Integrable (fun z : (AnisotropicDisorderBrownianSample n×Configuration n)×
        (Configuration n×Configuration n)=>cavitySelectedSpinOverlap J z.2.1 z.2.2)
        (anisotropicFreshTerminalPairLaw D μ a q):=
      bounded_real_integrable _ ((measurable_of_finite
        (fun z : Configuration n×Configuration n=>cavitySelectedSpinOverlap J z.1 z.2)).comp
          measurable_snd) (∑z : Configuration n×Configuration n,
            ‖cavitySelectedSpinOverlap J z.1 z.2‖)
        (fun z=>Finset.single_le_sum (fun x _=>norm_nonneg (cavitySelectedSpinOverlap J x.1 x.2))
          (Finset.mem_univ z.2))
    rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul,
      cavityFreshTerminalPairLaw_selected_overlap]
  rw [cavityFourDescendantLaw_spin_overlap_product,
    anisotropicFreshTerminalPairLaw_spin_square,hpair,covariance_eq_sub hx hy]
  change (∫ω,X ω*Y ω∂P)-(∫ω,X ω∂P)*(∫ω,Y ω∂P)=
    (∫ω,X ω*(Y ω-(q:ℝ))∂P)-(∫ω,X ω∂P)*((∫ω,Y ω∂P)-(q:ℝ))
  have hf : (fun ω=>X ω*(Y ω-(q:ℝ)))=fun ω=>X ω*Y ω-X ω*(q:ℝ):=by
    funext ω;ring
  have hint : (∫ω,X ω*Y ω-X ω*(q:ℝ)∂P)=
      (∫ω,X ω*Y ω∂P)-(∫ω,X ω∂P)*(q:ℝ):=by
    change (∫ω,(X*Y) ω-(fun ω=>X ω*(q:ℝ)) ω∂P)=_
    rw [integral_sub (hx.integrable_mul hy) ((hx.integrable (by norm_num)).mul_const _)]
    simp only [Pi.mul_apply,integral_mul_const]
  rw [hf,hint]
  ring

 theorem followupCavityCpp_eq_four_descendants (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure)
    (a u : ℝ) (hu : u∈Icc (0:ℝ) 1) (p : Paper.Overlap) :
    followupCavityCpp n β ρ hβ hρ μ a u hu p=
    (∫z,Paper.spinSign (z.2.1.1 (Fin.last n))*Paper.spinSign (z.2.1.2 (Fin.last n))*
      (cavitySelectedSpinOverlap (Finset.univ.erase (Fin.last n)) z.2.2.1 z.2.2.2-(p:ℝ))
      ∂cavityFourDescendantLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p)-
    (∫z,Paper.spinSign (z.2.1 (Fin.last n))*Paper.spinSign (z.2.2 (Fin.last n))
      ∂anisotropicFreshTerminalPairLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p)*
    (∫z,cavitySelectedSpinOverlap (Finset.univ.erase (Fin.last n)) z.2.1 z.2.2-(p:ℝ)
      ∂anisotropicFreshTerminalPairLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p) := by
  unfold followupCavityCpp
  simp_rw [←cavitySelectedMeanSquare_erased_last_projection]
  exact cavityProcessSpinSelectedCovariance_eq_four_descendants _ _ _ _ _ _

end QuantitativeFollowup
