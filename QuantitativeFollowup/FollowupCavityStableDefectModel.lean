module
public import QuantitativeFollowup.FollowupCavityStableDefectArithmetic
public import QuantitativeFollowup.VectorCubicMoment
public import QuantitativeFollowup.SmallIntervalDecomposition
public import QuantitativePaper.FreeTraceCutoff

@[expose] public section

/-! Native stable-interval defect reduction. The only additional input is
the actual self-overlap contraction inequality; the cubic, thermal, and
mean-covariance bounds are proved for the genuine minimizing model. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem followupCavityStableDefect_of_contraction
    (n : ℕ) (hn : 2 ≤ n) (β C : ℝ) (hβ : 1 < β) (hC : 1 ≤ C)
    (μ : Paper.ParisiMeasure) (lam rho : ℝ)
    (hlam : lam ∈ Ioc (0:ℝ) (β/2)) (hrho : rho ∈ Ioc (0:ℝ) 1)
    (hNr : (n:ℝ)⁻¹ ≤ rho) (hμ : μ ∈ scalarFloor (lam/β))
    (hmin : ∀ν∈scalarFloor (lam/β),
      vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional n ν β (1-rho) (lam/β))
    (hcontract : (3*rho/4)*
        vectorIntegratedSelfOverlapVariance (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1]) ≤
      C*((n:ℝ)⁻¹+
        vectorInterpolationTraceError (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1])+
        vectorMeanDirectionCovarianceIntegral (n:=n) μ (lam/β) β (1-rho) (lam/β)
          (by linarith [hrho.1])+
        vectorIntegratedSelfOverlapCubic (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1]))) :
    β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1]) ≤
      followupCavityStableDefectConstant β C*(Real.log (2+(n:ℝ)))^2/
        ((n:ℝ)*lam*rho^2) := by
  have hn0 : 0<n := by omega
  have hN : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hNp : 0<(n:ℝ) := Nat.cast_pos.mpr hn0
  have hβp : 0<β := zero_lt_one.trans hβ
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlp : 0<lam := hlam.1
  have hrp : 0<rho := hrho.1
  have ht : 1-rho<1 := by linarith [hrho.1]
  have hs : lam/β ∈ Ioc (0:ℝ) (1/2) :=
    ⟨div_pos hlam.1 hβp,(div_le_iff₀ hβp).mpr (by linarith [hlam.2])⟩
  have hs' : lam/β ∈ Ioo (0:ℝ) 1 := ⟨hs.1,by linarith [hs.2]⟩
  let M := (n:ℝ)*(rho*β^2)
  let L := smallIntervalLogConstant β
  let K := followupCavityStableLogConstant C
  let ell := Real.log (2+(n:ℝ))
  let Q := ell^2/((n:ℝ)*lam*rho)
  let V := vectorIntegratedSelfOverlapVariance (n:=n) μ (lam/β) β (1-rho) ht.le
  let A := vectorInterpolationTraceError (n:=n) μ (lam/β) β (1-rho) ht.le
  let J := vectorMeanDirectionCovarianceIntegral (n:=n) μ (lam/β) β (1-rho) (lam/β) ht.le
  let H := vectorIntegratedSelfOverlapCubic (n:=n) μ (lam/β) β (1-rho) ht.le
  have hclock : (1-(1-rho))*β^2=rho*β^2 := by ring
  have hNr' : 1 ≤ (n:ℝ)*rho := by
    have hh : 1 ≤ rho*(n:ℝ) := (div_le_iff₀ hNp).mp (by simpa only [one_div] using hNr)
    simpa only [mul_comm] using hh
  have hM : 1 ≤ M := by
    dsimp only [M]
    have hβsq : 1 ≤ β^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hβsq (by positivity : 0 ≤ (n:ℝ)*rho)]
  have hMp : 0<M := zero_lt_one.trans_le hM
  have hMb : M ≤ β^2*(n:ℝ) := by
    dsimp only [M]
    nlinarith [mul_le_mul_of_nonneg_left hrho.2 (by positivity : 0 ≤ (n:ℝ)*β^2)]
  have hL : 0<L := smallIntervalLogConstant_pos β hβ
  have hK : 0<K := followupCavityStableLogConstant_pos C hC
  have hlog := smallInterval_log_bound (n:ℝ) β M hN hβ hMp hMb
  change 1+logPlus M ≤ L*ell at hlog
  have hlsq : (1+logPlus M)^2 ≤ L^2*ell^2 := by
    have hh := (sq_le_sq₀ (by linarith [logPlus_nonneg M])
      (by linarith only [hlog,logPlus_nonneg M])).mpr hlog
    nlinarith only [hh]
  have h1sq : 1 ≤ L^2*ell^2 := by
    nlinarith [hlsq,logPlus_nonneg M]
  have htwo := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ) ≤ 2+(n:ℝ))
  have hell : (1/2:ℝ) ≤ ell :=
    (lt_trans (by norm_num) Real.log_two_gt_d9).le.trans htwo
  have hellp : 0 < ell := by linarith
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  have hden : 0 < M*(lam/β) := mul_pos hMp hs.1
  have hnorm (B : ℝ) : β*(B/(M*(lam/β)))=B/((n:ℝ)*lam*rho) := by
    dsimp only [M]
    field_simp
    <;> ring
  have hA0 := vector_free_trace_floor_bound hn0 μ (lam/β) β (1-rho) hβp.ne' ht hs' hμ hmin
  rw [hclock] at hA0
  change A ≤ 1/(M*(lam/β)) at hA0
  have hA : β*A ≤ L^2*Q := by
    have hh := hA0.trans (div_le_div_of_nonneg_right h1sq hden.le)
    have hh' := mul_le_mul_of_nonneg_left hh hβp.le
    rw [hnorm] at hh'
    simpa only [Q,div_eq_mul_inv,mul_assoc] using hh'
  have hJ0 := vector_mean_direction_covariance_integral_bound hn0 μ (lam/β) β (1-rho)
    hβp.ne' ht hs' hμ hmin
  rw [hclock] at hJ0
  change J ≤ 456*(1+logPlus M)^2/(M*(lam/β)) at hJ0
  have hJ : β*J ≤ 456*L^2*Q := by
    have hh := hJ0.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlsq (by norm_num : (0:ℝ) ≤ 456)) hden.le)
    have hh' := mul_le_mul_of_nonneg_left hh hβp.le
    rw [hnorm] at hh'
    simpa only [Q,div_eq_mul_inv,mul_assoc] using hh'
  let kap := 1/(4*C)
  have hkap : kap ∈ Ioc (0:ℝ) (1/4) := by
    dsimp only [kap]
    exact ⟨by positivity,(div_le_iff₀ (by positivity : 0<4*C)).mpr (by linarith)⟩
  have hz : kap*rho ∈ Ioc (0:ℝ) (1/4) :=
    ⟨mul_pos hkap.1 hrho.1,(mul_le_mul_of_nonneg_left hrho.2 hkap.1.le).trans
      (by simpa only [mul_one] using hkap.2)⟩
  have hfirst : Real.log (2*M) ≤ L*ell := by
    have hh : Real.log (2*M) ≤ 1+logPlus M := by
      rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hMp.ne']
      have hm : Real.log M ≤ logPlus M := le_max_left _ _
      linarith [Real.log_two_lt_d9]
    exact hh.trans hlog
  have hsecond := followupCavityStable_log_reciprocal (n:ℝ) C rho hN hC hrho.1 hNr
  change Real.log (2/(kap*rho)) ≤ K*ell at hsecond
  have hfirst0 : 0 ≤ Real.log (2*M) := Real.log_nonneg (by linarith)
  have hsecond0 : 0 ≤ Real.log (2/(kap*rho)) :=
    Real.log_nonneg ((le_div_iff₀ hz.1).mpr (by linarith [hz.2]))
  have hlogs : Real.log (2*M)*Real.log (2/(kap*rho)) ≤ L*K*ell^2 := by
    have hh := mul_le_mul hfirst hsecond hsecond0 (by positivity : 0 ≤ L*ell)
    nlinarith only [hh]
  have hH0 := vector_cubic_self_overlap_moment hn0 μ (lam/β) β (1-rho) hβp.ne' ht hs hμ hmin
    (by simpa only [hclock] using hM) (kap*rho) hz
  rw [hclock] at hH0
  change H ≤ kap*rho*V+(425/(M*(lam/β)))*Real.log (2*M)*Real.log (2/(kap*rho)) at hH0
  have hH : H ≤ kap*rho*V+β⁻¹*(425*L*K*Q) := by
    have hh := mul_le_mul_of_nonneg_left hlogs
      (show (0:ℝ) ≤ 425/(M*(lam/β)) from div_nonneg (by norm_num) hden.le)
    have he : (425/(M*(lam/β)))*(L*K*ell^2)=β⁻¹*(425*L*K*Q) := by
      dsimp only [M,Q]
      field_simp
      <;> ring
    rw [he] at hh
    nlinarith only [hH0,hh]
  have hc : (3*rho/4)*V ≤ C*(β⁻¹*(β/(n:ℝ))+A+J+H) := by
    have he : β⁻¹*(β/(n:ℝ))=(n:ℝ)⁻¹ := by field_simp
    rw [he]
    exact hcontract
  have habs := followupCavityStable_thermal_absorption β C rho V A J H (β/(n:ℝ))
    (425*L*K*Q) hβp hC hrho.1 hc hH
  have hsmall : β/(n:ℝ) ≤ 2*β^2*Q := by
    apply (div_le_iff₀ hNp).mpr
    dsimp only [Q]
    have hh : β*(lam*rho) ≤ 2*β^2*ell^2 := by
      have hlr : lam*rho ≤ β/2 :=
        (mul_le_mul_of_nonneg_left hrho.2 hlam.1.le).trans (by simpa only [mul_one] using hlam.2)
      nlinarith [mul_le_mul_of_nonneg_left hlr hβp.le,sq_nonneg (ell-1/2)]
    have hp : 2*β^2*(ell^2/((n:ℝ)*lam*rho))*(n:ℝ)=2*β^2*ell^2/(lam*rho) := by
      field_simp
      <;> ring
    rw [hp]
    exact (le_div_iff₀ (mul_pos hlam.1 hrho.1)).mpr hh
  have hV : β*V ≤ 2*C*(2*β^2+457*L^2+425*L*K)*(Q/rho) := by
    have hh : rho*(β*V) ≤ 2*C*(2*β^2+457*L^2+425*L*K)*Q := by
      have hsum := add_le_add (add_le_add hsmall hA) hJ
      have hb := mul_le_mul_of_nonneg_left (add_le_add_right hsum (425*L*K*Q)) (by positivity : 0 ≤ 2*C)
      nlinarith only [habs,hb]
    rw [←mul_div_assoc]
    exact (le_div_iff₀ hrho.1).mpr (by nlinarith only [hh])
  rw [smallInterval_defect_decomposition hn0 μ (lam/β) β (1-rho) hβp.ne' ht hs' hμ hmin]
  change β*(A+2*J+V) ≤ _
  have hQr : Q ≤ Q/rho := (le_div_iff₀ hrho.1).mpr
    (mul_le_of_le_one_right hQ hrho.2)
  have hAJ : β*A+2*(β*J) ≤ 913*L^2*(Q/rho) := by
    have hh := mul_le_mul_of_nonneg_left hQr (by positivity : 0 ≤ 913*L^2)
    nlinarith only [hA,hJ,hh]
  have he : followupCavityStableDefectConstant β C*(Q/rho)=
      followupCavityStableDefectConstant β C*ell^2/((n:ℝ)*lam*rho^2) := by
    dsimp only [Q]
    field_simp
    <;> ring
  rw [←he]
  dsimp only [followupCavityStableDefectConstant,L,K] at hV hAJ ⊢
  nlinarith only [hV,hAJ]

end QuantitativeFollowup
