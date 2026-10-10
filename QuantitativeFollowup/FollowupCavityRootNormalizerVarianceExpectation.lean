module
public import QuantitativeFollowup.AnisotropicNodeB
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceDerivative

@[expose] public section

/-! Exact expected last-field root response. The future-square kernel is
integrated under the genuine native law, using actual conditional pairing
and bounded Fubini, including the root atom. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem anisotropic_root_variance_response_balance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (i : Fin n) :
    (∫p,anisotropicRootVarianceResponse D μ i p.1∂anisotropicMeasureSampleLaw D μ a)=
      (1/2:ℝ)*(1-∫r : Paper.Overlap,(r:ℝ)*
        (∫p,(anisotropicProcessSpinResponse D μ r i p)^2∂anisotropicMeasureSampleLaw D μ a)
          ∂parisiFreeMeasure μ a) := by
  let P:=anisotropicMeasureSampleLaw D μ a
  let Q:=parisiFreeMeasure μ a
  let K:=fun r p=>anisotropicPastSpinSquareKernel D μ a zeroOverlap r i p
  let F:=fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>(z.1:ℝ)*K z.1 z.2
  have hKm : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>K z.1 z.2) :=
    (measurable_uncurry_anisotropicPastSpinSquareKernel D μ a zeroOverlap i).mono
      (by
        dsimp only [MeasurableSpace.prod]
        exact sup_le_sup le_rfl (MeasurableSpace.comap_mono ((anisotropicBrownianFiltration n).le _))) le_rfl
  have hFm : Measurable F:=(measurable_subtype_coe.comp measurable_fst).mul hKm
  have hFb (z : Paper.Overlap×AnisotropicDisorderBrownianSample n) : ‖F z‖≤1 := by
    rw [norm_mul,Real.norm_of_nonneg z.1.property.1]
    exact (mul_le_mul_of_nonneg_left (norm_anisotropicPastSpinSquareKernel_le D μ a zeroOverlap z.1 i z.2)
      z.1.property.1).trans (by simpa only [mul_one] using z.1.property.2)
  have hFi : Integrable F (Q.prod P):=(integrable_const (1:ℝ)).mono' hFm.aestronglyMeasurable (.of_forall hFb)
  have hswap : (∫p,∫r,F (r,p)∂Q∂P)=∫r,∫p,F (r,p)∂P∂Q :=
    (integral_integral_swap (f:=fun r p=>F (r,p)) hFi).symm
  have hk (r : Paper.Overlap) : (∫p,K r p∂P)=∫p,(anisotropicProcessSpinResponse D μ r i p)^2∂P := by
    have hh:=anisotropicPastSpinSquareKernel_weighted_pairing D μ a zeroOverlap r i
      (fun _=>1) measurable_const 1 (fun _=>by norm_num)
    simpa only [one_mul] using hh
  have hR : (fun p=>anisotropicRootVarianceResponse D μ i p.1)=ᵐ[P]
      (fun p=>(1/2:ℝ)*(1-∫r,F (r,p)∂Q)) := by
    have hh:=anisotropicRestartVarianceResponse_eq_native D μ a zeroOverlap i
    filter_upwards [hh] with p hp
    have hstate : anisotropicMeasureState D μ zeroOverlap p=0:=anisotropicMeasureState_zero D μ p
    rw [hstate] at hp
    change anisotropicRootVarianceResponse D μ i p.1=anisotropicNativeVarianceResponse D μ a zeroOverlap i p at hp
    rw [hp,anisotropicNativeVarianceResponse_eq_free D μ a ha hμ zeroOverlap i p]
    simp only [zeroOverlap,sub_zero]
    congr 2
    apply integral_congr_ae
    exact .of_forall fun r=>by
      change (if zeroOverlap<r then (r:ℝ)*K r p else 0)=(r:ℝ)*K r p
      by_cases hr:zeroOverlap<r
      · simp only [hr,ite_true]
      · have he : r=zeroOverlap:=le_antisymm (le_of_not_gt hr) r.property.1
        simp [he,zeroOverlap]
  rw [integral_congr_ae hR,integral_const_mul,integral_sub (integrable_const 1) hFi.integral_prod_right,
    integral_const,probReal_univ,smul_eq_mul,mul_one,hswap]
  congr 2
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only [F]
    rw [integral_const_mul,hk]

end QuantitativeFollowup
