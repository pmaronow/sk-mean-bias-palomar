module
public import QuantitativeFollowup.ScalarGradientTemperatureBound

@[expose] public section

/-! The actual Hessian comparison across temperatures retains the true
fourth-jet variance mismatch, bounded by the explicit checked jet estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def scalarHessianTemperatureSourceConstant (beta gamma : ℝ) : ℝ :=
  15+14*beta^2*scalarGradientTemperatureConstant beta+scalarFourthJetBound gamma/2

theorem scalarHessianTemperatureSourceConstant_pos (beta gamma : ℝ) :
    0< scalarHessianTemperatureSourceConstant beta gamma := by
  unfold scalarHessianTemperatureSourceConstant scalarGradientTemperatureConstant
  have h4 := scalarFourthJetBound_pos gamma
  positivity

theorem scalarHessianTemperatureSource_norm_le (beta gamma : ℝ)
    (hb : beta≠0) (hg : gamma≠0) (μ : Paper.ParisiMeasure)
    (a x : ℝ) (ha : a∈Icc (0 : ℝ) 1) (r : ℝ) (hr : r∈Icc (0 : ℝ) (1-a))
    (ω : Paper.BrownianSample) :
    ‖scalarDynkinSource (canonicalParisiRestartState beta x μ a ha.1)
        (canonicalParisiRestartDrift beta x μ a ha.1) gamma beta μ (MvPolynomial.X 1) a r ω-
      scalarDynkinSource (canonicalParisiRestartState beta x μ a ha.1)
        (canonicalParisiRestartDrift beta x μ a ha.1) beta beta μ (MvPolynomial.X 1) a r ω‖≤
      2*beta^2*‖parisiHessian beta μ (a+r,canonicalParisiRestartState beta x μ a ha.1 r.toNNReal ω)-
        parisiHessian gamma μ (a+r,canonicalParisiRestartState beta x μ a ha.1 r.toNNReal ω)‖+
      scalarHessianTemperatureSourceConstant beta gamma*|beta^2-gamma^2| := by
  let y := canonicalParisiRestartState beta x μ a ha.1 r.toNNReal ω
  let A := parisiCDF μ (a+r)
  let B := parisiGradient beta μ (a+r,y)
  let G := parisiGradient gamma μ (a+r,y)
  let H := parisiHessian beta μ (a+r,y)
  let K := parisiHessian gamma μ (a+r,y)
  have hat : a+r∈Icc (0 : ℝ) 1 := ⟨by linarith [ha.1,hr.1],by linarith [hr.2]⟩
  have hdr := canonicalParisiRestartDrift_eq beta x μ a ha.1 r.toNNReal
    (by rw [Real.coe_toNNReal _ hr.1];linarith [hr.2,ha.1]) ω
  rw [Real.coe_toNNReal _ hr.1] at hdr
  rw [scalarDynkinSource_hessian,scalarDynkinSource_hessian,hdr]
  simp only [parisiSpatialJet_one,parisiSpatialJet_two,sub_self,zero_div,zero_mul,add_zero]
  have he : -(gamma^2*A)*K^2+(beta^2*A*B-gamma^2*A*G)*parisiSpatialJet gamma μ 3 (a+r) y+
      ((beta^2-gamma^2)/2)*parisiSpatialJet gamma μ 4 (a+r) y-(-(beta^2*A)*H^2)=
      beta^2*A*(H^2-K^2)+(beta^2-gamma^2)*A*K^2+
      (beta^2*A*(B-G)+(beta^2-gamma^2)*(A*G))*parisiSpatialJet gamma μ 3 (a+r) y+
      ((beta^2-gamma^2)/2)*parisiSpatialJet gamma μ 4 (a+r) y := by ring
  change ‖-(gamma^2*A)*K^2+(beta^2*A*B-gamma^2*A*G)*parisiSpatialJet gamma μ 3 (a+r) y+
      ((beta^2-gamma^2)/2)*parisiSpatialJet gamma μ 4 (a+r) y-(-(beta^2*A)*H^2)‖≤_
  rw [he]
  have hA : ‖A‖≤1 := by rw [Real.norm_of_nonneg (parisiCDF_nonneg μ _)];exact parisiCDF_le_one μ _
  have hG : ‖G‖≤1 := norm_parisiGradient_le_one gamma μ _
  have hH : ‖H‖≤1 := norm_parisiHessian_le_one_all beta μ _
  have hK : ‖K‖≤1 := norm_parisiHessian_le_one_all gamma μ _
  have hKsq : ‖K‖^2≤1 := (pow_le_pow_left₀ (norm_nonneg _) hK 2).trans_eq (by norm_num)
  have hHK : ‖H^2-K^2‖≤2*‖H-K‖ := by
    rw [show H^2-K^2=(H-K)*(H+K) by ring,norm_mul]
    exact (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hCoef : beta^2*‖A‖≤ beta^2 :=
    (mul_le_mul_of_nonneg_left hA (sq_nonneg beta)).trans_eq (mul_one _)
  have hOne := mul_le_mul hCoef hHK (norm_nonneg _) (sq_nonneg beta)
  have hTwo : |beta^2-gamma^2| *‖A‖*‖K‖^2≤|beta^2-gamma^2| := by
    have hprod := mul_le_mul hA hKsq (sq_nonneg _) zero_le_one
    nlinarith only [mul_le_mul_of_nonneg_left hprod (abs_nonneg (beta^2-gamma^2))]
  have hGrad := parisiGradient_temperature_square_bound beta gamma hb hg μ (a+r) hat y
  change ‖B-G‖≤ scalarGradientTemperatureConstant beta*|beta^2-gamma^2| at hGrad
  have hAG : ‖A*G‖≤1 := by rw [norm_mul];exact (mul_le_mul hA hG (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hR : ‖beta^2*A*(B-G)+(beta^2-gamma^2)*(A*G)‖≤
      (beta^2*scalarGradientTemperatureConstant beta+1)*|beta^2-gamma^2| := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Real.norm_of_nonneg (sq_nonneg beta),Real.norm_eq_abs]
    rw [Real.norm_eq_abs] at hCoef hGrad
    simp only [norm_mul,Real.norm_eq_abs] at hAG
    have hx := mul_le_mul hCoef hGrad (abs_nonneg _) (sq_nonneg beta)
    have hy := mul_le_mul_of_nonneg_left hAG (abs_nonneg (beta^2-gamma^2))
    nlinarith only [hx,hy]
  have hR0 := (norm_nonneg _).trans hR
  have hThree := mul_le_mul hR (norm_parisiSpatialJet_three_le_fourteen gamma hg μ (a+r) y) (norm_nonneg _) hR0
  have hFour := mul_le_mul_of_nonneg_left (norm_parisiSpatialJet_four_le gamma hg μ (a+r) hat y)
    (abs_nonneg ((beta^2-gamma^2)/2))
  let P1 := beta^2*A*(H^2-K^2)
  let P2 := (beta^2-gamma^2)*A*K^2
  let P3 := (beta^2*A*(B-G)+(beta^2-gamma^2)*(A*G))*parisiSpatialJet gamma μ 3 (a+r) y
  let P4 := ((beta^2-gamma^2)/2)*parisiSpatialJet gamma μ 4 (a+r) y
  have hn : ‖P1+P2+P3+P4‖≤‖P1‖+‖P2‖+‖P3‖+‖P4‖ :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  dsimp only [P1,P2,P3,P4] at hn
  simp only [norm_mul,norm_pow,Real.norm_of_nonneg (sq_nonneg beta),Real.norm_eq_abs] at hn
  simp only [Real.norm_eq_abs] at hOne hTwo hThree hFour
  have hh := (hn.trans (add_le_add (add_le_add (add_le_add hOne hTwo) hThree) hFour))
  apply hh.trans_eq
  rw [abs_div]
  norm_num
  dsimp only [scalarHessianTemperatureSourceConstant,H,K,y]
  ring

end QuantitativeFollowup
