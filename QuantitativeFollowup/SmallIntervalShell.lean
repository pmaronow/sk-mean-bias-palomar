module
public import QuantitativeFollowup.RootProbabilityQuantile
public import QuantitativeFollowup.VectorQuantileIntervalVariance
public import QuantitativePaper.P2QuantileDiameter
public import Mathlib.Analysis.MeanInequalitiesPow
public import QuantitativeFollowup.QuantileWindowResidual

@[expose] public section

/-! Actual dyadic self-overlap shells under a localized minimizing quantile.
The localization premise here is discharged from the actual trial budget in
SmallIntervalModel. Partial free atoms are retained by the quantile interval. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def smallIntervalOmega (rho eta : ℝ) : ℝ := min 1 ((eta/rho)^((1:ℝ)/6))

def smallIntervalShellConstant (K : ℝ) : ℝ := 512*(1+(2*K)^(2/3:ℝ))

theorem smallIntervalOmega_nonneg (rho eta : ℝ) (hrho : 0 ≤ rho) (heta : 0 ≤ eta) :
    0 ≤ smallIntervalOmega rho eta := le_min zero_le_one (Real.rpow_nonneg (div_nonneg heta hrho) _)

theorem smallInterval_shell_diameter (μ : Paper.ParisiMeasure) (s K omega : ℝ)
    (hK : 0 ≤ K) (homega : 0 ≤ omega) (j : ℕ)
    (hpos : 0<volume.real (dyadicQuantileShell s s j))
    (hQ : ∀v∈Ioo (0:ℝ) (1-s),(parisiFreeQuantile μ s v:ℝ) ≤ K*(s+v+omega)) :
    parisiQuantileImageDiameter μ s (dyadicQuantileShell s s j)  ≤ 
      2*K*((2:ℝ)^j*s+omega) := by
  apply p2_quantile_diameter_le_of_upper μ s _
    (dyadicQuantileShell_ordConnected s s j).measurableSet hpos
  intro v hv
  have hh:=hQ v hv.1
  have hp : s+v<(2:ℝ)*((2:ℝ)^j*s) := by
    have hr:=hv.2.2
    rw [pow_succ] at hr
    linarith
  have hg:=mul_le_mul_of_nonneg_left (by linarith : s+v+omega ≤ 2*((2:ℝ)^j*s+omega)) hK
  exact hh.trans (by convert hg using 1 <;> ring)

theorem smallInterval_shell_power (M u omega : ℝ) (hM : 0<M) (hu : 0<u)
    (homega : 0 ≤ omega) :
    (1/(M*u))^(2/3:ℝ)*(u+omega)^(2/3:ℝ)*u^(1/3:ℝ)  ≤ 
      M^(-(2/3:ℝ))*(u^(1/3:ℝ)+u^(-(1/3:ℝ))*omega^(2/3:ℝ)) := by
  have hsplit:=Real.rpow_add_le_add_rpow hu.le homega (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (2/3:ℝ) ≤ 1)
  have hinv : (1/(M*u))^(2/3:ℝ)=M^(-(2/3:ℝ))*u^(-(2/3:ℝ)) := by
    rw [one_div,Real.inv_rpow (mul_nonneg hM.le hu.le),Real.mul_rpow hM.le hu.le,mul_inv_rev,
      ←Real.rpow_neg hM.le,←Real.rpow_neg hu.le]
    ring
  calc
    _ ≤ (1/(M*u))^(2/3:ℝ)*(u^(2/3:ℝ)+omega^(2/3:ℝ))*u^(1/3:ℝ):=by gcongr
    _=_:=by
      rw [hinv,mul_add,add_mul]
      have h1 : u^(-(2/3:ℝ))*u^(2/3:ℝ)*u^(1/3:ℝ)=u^(1/3:ℝ) := by
        rw [←Real.rpow_add hu];norm_num
      have h2 : u^(-(2/3:ℝ))*u^(1/3:ℝ)=u^(-(1/3:ℝ)) := by
        rw [←Real.rpow_add hu];norm_num
      calc
        _=M^(-(2/3:ℝ))*(u^(-(2/3:ℝ))*u^(2/3:ℝ)*u^(1/3:ℝ))+
          M^(-(2/3:ℝ))*(u^(-(2/3:ℝ))*u^(1/3:ℝ))*omega^(2/3:ℝ):=by ring
        _=_:=by rw [h1,h2];ring

theorem smallInterval_self_overlap_shell (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s)
    (K omega : ℝ) (hK : 0 ≤ K) (homega : 0 ≤ omega)
    (hQ : ∀v∈Ioo (0:ℝ) (1-s),(parisiFreeQuantile μ s v:ℝ) ≤ K*(s+v+omega)) (j : ℕ) :
    let M:=(n:ℝ)*((1-t)*β^2)
    let u:=(2:ℝ)^j*s
    (∫v in dyadicQuantileShell s s j,variance (vectorSelfOverlap (n:=n) μ β t ht.le
      (parisiFreeQuantile μ s v)) (vectorMeasureSpinPathLaw μ β t s ht.le))  ≤ 
      smallIntervalShellConstant K*((1+logPlus (M*u^2))/(M*u)+
        M^(-(2/3:ℝ))*(u^(1/3:ℝ)+u^(-(1/3:ℝ))*omega^(2/3:ℝ))) := by
  dsimp only
  let M:=(n:ℝ)*((1-t)*β^2)
  let u:=(2:ℝ)^j*s
  let J:=dyadicQuantileShell s s j
  let h:=volume.real J
  have hM : 0<M:=mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have hu : 0<u:=by dsimp only [u];positivity [hs.1]
  have hDom : J⊆Ioo (0:ℝ) (1-s):=dyadicQuantileShell_subset s s j
  by_cases hpos : 0<h
  · have hlen : h ≤ u:=dyadicQuantileShell_length_le s s hs.1.le j
    have hThreshold : ∀ᵐv∂volume.restrict J,u ≤ parisiCDF μ (parisiFreeQuantile μ s v) := by
      filter_upwards [ae_restrict_mem (dyadicQuantileShell_ordConnected s s j).measurableSet] with v hv
      have hh : u ≤ s+v:=by dsimp only [u];linarith [hv.2.1]
      exact hh.trans (parisiCDF_freeQuantile_lower μ s ⟨hs.1.le,hs.2.le⟩ (Ioo_subset_Ioc_self (hDom hv)))
    have hb:=vector_quantile_interval_variance hn μ s β t hβ ht hs hμ hmin J
      (dyadicQuantileShell_ordConnected s s j) hDom h u hpos rfl hu hThreshold
    have hell:=parisiQuantileImageDiameter_nonneg_of_positive_interval μ s J
      (dyadicQuantileShell_ordConnected s s j) hDom hpos
    have hd:=smallInterval_shell_diameter μ s K omega hK homega j hpos hQ
    let ε:=1/(M*u)
    have hε : 0<ε:=by dsimp only [ε];positivity
    have hlog : max (Real.log (h/ε)) 0 ≤ logPlus (M*u^2) := by
      change logPlus (h/ε) ≤ logPlus (M*u^2)
      apply logPlus_le_of_nonneg_le (div_nonneg hpos.le hε.le)
      apply (div_le_iff₀ hε).mpr
      dsimp only [ε]
      field_simp
      nlinarith
    have hfirst : min h (ε*(1+max (Real.log (h/ε)) 0)) ≤ (1+logPlus (M*u^2))/(M*u) := by
      apply (min_le_right _ _).trans
      convert mul_le_mul_of_nonneg_left (add_le_add_left hlog 1) hε.le using 1 <;> dsimp only [ε] <;> ring
    have hsecond : (ε*parisiQuantileImageDiameter μ s J)^(2/3:ℝ)*h^(1/3:ℝ) ≤ 
        (2*K)^(2/3:ℝ)*M^(-(2/3:ℝ))*(u^(1/3:ℝ)+u^(-(1/3:ℝ))*omega^(2/3:ℝ)) := by
      calc
        _ ≤ (ε*(2*K*(u+omega)))^(2/3:ℝ)*u^(1/3:ℝ):=by gcongr
        _=(2*K)^(2/3:ℝ)*((1/(M*u))^(2/3:ℝ)*(u+omega)^(2/3:ℝ)*u^(1/3:ℝ)):=by
          rw [Real.mul_rpow hε.le (by positivity),Real.mul_rpow (by positivity : 0 ≤ 2*K) (by positivity : 0 ≤ u+omega)]
          dsimp only [ε]
          ring
        _ ≤ _:=by
          convert mul_le_mul_of_nonneg_left (smallInterval_shell_power M u omega hM hu homega)
            (Real.rpow_nonneg (by positivity : 0 ≤ 2*K) _) using 1 <;> ring
    have hP : 0 ≤ (1+logPlus (M*u^2))/(M*u):=by positivity [logPlus_nonneg (M*u^2)]
    have hR : 0 ≤ M^(-(2/3:ℝ))*(u^(1/3:ℝ)+u^(-(1/3:ℝ))*omega^(2/3:ℝ)):=by positivity
    change (∫v in J,_) ≤ smallIntervalShellConstant K*((1+logPlus (M*u^2))/(M*u)+_)
    apply hb.trans
    change 512*(min h (ε*(1+max (Real.log (h/ε)) 0))+(ε*parisiQuantileImageDiameter μ s J)^(2/3:ℝ)*h^(1/3:ℝ)) ≤ _
    unfold smallIntervalShellConstant
    nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 2*K) (2/3:ℝ)]
  · have hfinite : volume J≠∞:=ne_of_lt ((measure_mono hDom).trans_lt (by rw [Real.volume_Ioo];exact ENNReal.ofReal_lt_top))
    have hzero : volume J=0:=by
      have hz : volume.real J=0:=le_antisymm (not_lt.mp hpos) measureReal_nonneg
      have he:=ofReal_measureReal (μ:=volume) (s:=J) hfinite
      rw [hz,ENNReal.ofReal_zero] at he
      exact he.symm
    rw [setIntegral_measure_zero _ hzero]
    unfold smallIntervalShellConstant
    positivity [logPlus_nonneg (M*u^2)]

end QuantitativeFollowup
