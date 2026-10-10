module
public import QuantitativeFollowup.AnisotropicBinaryFeatureProfile
public import QuantitativeFollowup.AnisotropicBinaryFeatureRegularity

@[expose] public section

/-! Exact mixing of the true arbitrary-profile pair-feature identity with
the actual initial exponential disorder tilt. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

private theorem integral_native_dummy_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (F G : AnisotropicDisorderBrownianSample n→ℝ)
    (hF : Integrable F (anisotropicMeasureSampleLaw D μ a))
    (hG : Integrable G (anisotropicMeasureSampleLaw D μ a))
    (he : ∀g,(∫p,F (g,p.2) ∂vectorDisorderBrownianMeasure n)=
      ∫p,G (g,p.2) ∂vectorDisorderBrownianMeasure n) :
    (∫p,F p ∂anisotropicMeasureSampleLaw D μ a)=∫p,G p ∂anisotropicMeasureSampleLaw D μ a := by
  rw [anisotropicMeasureSampleLaw,integral_prod _ hF,integral_prod _ hG]
  apply integral_congr_ae
  exact .of_forall fun g=>by
    have h1:=integral_fun_snd (μ:=completionLaw n) (ν:=vectorBrownianMeasure n)
      (fun w : VectorBrownianSample n=>F (g,w))
    have h2:=integral_fun_snd (μ:=completionLaw n) (ν:=vectorBrownianMeasure n)
      (fun w : VectorBrownianSample n=>G (g,w))
    simpa only [probReal_univ,one_smul] using h1.symm.trans ((he g).trans h2)

private theorem integrable_weighted {A : Type*} [MeasurableSpace A]
    (P : Measure A) (Z F : A→ℝ) (hZ : Integrable Z P) (hF : Measurable F)
    (C : ℝ) (hC : ∀p,‖F p‖ ≤ C) : Integrable (fun p=>Z p*F p) P :=
  (hZ.norm.const_mul C).mono' (hZ.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    (.of_forall fun p=>by rw [norm_mul];exact (mul_le_mul_of_nonneg_left (hC p) (norm_nonneg (Z p))).trans_eq (mul_comm _ _))

theorem anisotropic_native_pair_second_stieltjes_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n)
    (Z : AnisotropicDisorderBrownianSample n→ℝ)
    (hZ : Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal] Z)
    (B : ℝ≥0) (hB : ∀p,‖Z p‖ ≤ B) :
    (∫p,Z p*anisotropicProcessPairSecond D μ q e p ∂anisotropicMeasureSampleLaw D μ a)+
      Paper.parisiCDF μ q*(∫p,Z p*(anisotropicProcessPairResponse D μ q e p)^2
        ∂anisotropicMeasureSampleLaw D μ a)+
      (∫p,Z p*anisotropicRawFuturePairSquare D μ q e p ∂anisotropicMeasureSampleLaw D μ a)=
      ∫p,Z p ∂anisotropicMeasureSampleLaw D μ a := by
  let P:=anisotropicMeasureSampleLaw D μ a
  let H:=anisotropicProcessPairSecond D μ q e
  let M:=fun p=>(anisotropicProcessPairResponse D μ q e p)^2
  let F:=anisotropicRawFuturePairSquare D μ q e
  let E:=fun p=>Z p*H p+Paper.parisiCDF μ q*(Z p*M p)+Z p*F p
  have hZm:=hZ.mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hZi : Integrable Z P:=(integrable_const (B:ℝ)).mono' hZm.aestronglyMeasurable (.of_forall hB)
  have hHm:=(adapted_anisotropicProcessPairSecond D μ q e).mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hMm:=(measurable_anisotropicProcessPairResponse D μ q e).pow_const 2
  have hFm:=measurable_anisotropicRawFuturePairSquare D μ q e
  have hMb (p : AnisotropicDisorderBrownianSample n) : ‖M p‖ ≤ 1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessPairResponse_bound D μ q e p) 2).trans_eq (by norm_num)
  have hHi:=integrable_weighted P Z H hZi hHm (anisotropicPairSecondBound D e)
    (norm_anisotropicProcessPairSecond_le D μ q e)
  have hMi:=integrable_weighted P Z M hZi hMm 1 hMb
  have hFi:=integrable_weighted P Z F hZi hFm 1 (norm_anisotropicRawFuturePairSquare_le D μ q e)
  have hEi : Integrable E P:=(hHi.add (hMi.const_mul _)).add hFi
  have he : (∫p,E p ∂P)=∫p,Z p ∂P := by
    apply integral_native_dummy_pairing D μ a E Z hEi hZi
    intro g
    let zp:=fun p : VectorDisorderBrownianSample n=>Z (g,p.2)
    have hzp:=hZ.comp (measurable_anisotropicWienerInsertion_past g (q:ℝ).toNNReal)
    have hzpg:=hzp.mono ((vectorBrownianFiltration n).le _) le_rfl
    have hzpi : Integrable zp (vectorDisorderBrownianMeasure n):=
      (integrable_const (B:ℝ)).mono' hzpg.aestronglyMeasurable (.of_forall fun p=>hB (g,p.2))
    have hmap : Measurable (fun p : VectorDisorderBrownianSample n=>(g,p.2)) :=
      (measurable_const (a:=g)).prodMk measurable_snd
    have hpHi:=integrable_weighted (vectorDisorderBrownianMeasure n) zp (fun p=>H (g,p.2)) hzpi
      (hHm.comp hmap) (anisotropicPairSecondBound D e) (fun p=>norm_anisotropicProcessPairSecond_le D μ q e _)
    have hpMi:=integrable_weighted (vectorDisorderBrownianMeasure n) zp (fun p=>M (g,p.2)) hzpi
      (hMm.comp hmap) 1 (fun p=>hMb _)
    have hpFi:=integrable_weighted (vectorDisorderBrownianMeasure n) zp (fun p=>F (g,p.2)) hzpi
      (hFm.comp hmap) 1 (fun p=>norm_anisotropicRawFuturePairSquare_le D μ q e _)
    have hadd:=integral_add (hpHi.add (hpMi.const_mul (Paper.parisiCDF μ q))) hpFi
    have hadd2:=integral_add hpHi (hpMi.const_mul (Paper.parisiCDF μ q))
    simp only [Pi.add_apply] at hadd hadd2
    change (∫p,zp p*H (g,p.2)+Paper.parisiCDF μ q*(zp p*M (g,p.2))+zp p*F (g,p.2)
      ∂vectorDisorderBrownianMeasure n)=∫p,zp p ∂vectorDisorderBrownianMeasure n
    rw [hadd,hadd2,integral_const_mul]
    rw [anisotropicRawFuturePairSquare_fixed_disorder_pairing D μ g q e zp hzpg hzpi]
    exact anisotropic_pair_second_wholePast_stieltjes_pairing D μ g q e zp hzp hzpi
  have hadd:=integral_add (hHi.add (hMi.const_mul (Paper.parisiCDF μ q))) hFi
  have hadd2:=integral_add hHi (hMi.const_mul (Paper.parisiCDF μ q))
  simp only [Pi.add_apply] at hadd hadd2
  change (∫p,Z p*H p+Paper.parisiCDF μ q*(Z p*M p)+Z p*F p ∂P)=_ at he
  rw [hadd,hadd2,integral_const_mul] at he
  exact he

end QuantitativeFollowup
