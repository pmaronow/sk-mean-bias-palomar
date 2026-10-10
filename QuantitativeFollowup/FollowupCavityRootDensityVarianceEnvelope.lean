module
public import QuantitativeFollowup.AnisotropicMeasureSpatialAllJets
public import QuantitativeFollowup.FollowupCavityRootDensityVarianceContinuity
public import QuantitativePaper.ExponentialJetBounds

@[expose] public section

/-! Common Gaussian envelopes for the actual density's spatial jets on a
positive variance cylinder. Constants are independent of profile depth;
all differentiability is supplied by the constructed spatial jet limits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n:ℕ}

theorem anisotropicRootDensity_positive_variance_jet_envelope
    (D:AnisotropicSpinModel n)(μ:Paper.ParisiMeasure)(a:ℝ)(i:Fin n)(d:ℝ)(hd:0<d):
    ∃B R:ℝ,0≤B ∧ 0≤R ∧ ∀b∈Ioo (d/2) (d+1),∀j:ℕ,j ≤ 3→∀x:AnisotropicDisorder n,
      ‖iteratedFDeriv ℝ j (anisotropicRootDensity (anisotropicReplaceVariance D i b) μ a) x‖≤
        B*Real.exp (R*‖x‖):=by
  let L:=anisotropicDisorderInjection n
  let U:=fun b=>anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ ∘ L
  let C:ℝ:=(‖anisotropicEnergyMap D‖₊*‖L‖₊:ℝ)
  let Q:Fin 3→ℝ:=fun j=>finiteStateSpatialJetBound (Configuration n) n (j.val+1)*C^(j.val+1)
  let K:ℝ:=1+∑j:Fin 3,Q j
  have hQ j:0≤Q j:=mul_nonneg (finiteStateSpatialJetBound_nonneg _ _ _) (by positivity)
  have hK:1≤K:=by dsimp only [K];exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _=>hQ j)
  have hC:0≤C:=by dsimp [C];positivity
  have hU b:ContDiff ℝ ∞ (U b):=(contDiff_anisotropicMeasurePotential _ μ).comp L.contDiff
  have hUi (b:ℝ)(j:ℕ)(hj:1≤j)(hj3:j ≤ 3)(x:AnisotropicDisorder n):
      ‖iteratedFDeriv ℝ j (U b) x‖≤K^j:=by
    let z:Fin 3:=⟨j-1,by omega⟩
    have hz:(z:ℕ)+1=j:=by dsimp [z];omega
    have hp:‖iteratedFDeriv ℝ j (U b) x‖≤Q z:=by
      rw [show U b=anisotropicMeasurePotential (anisotropicReplaceVariance D i b) μ ∘ L from rfl,
        L.iteratedFDeriv_comp_right (contDiff_anisotropicMeasurePotential _ μ) x (by simp)]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      have hh:=mul_le_mul_of_nonneg_right (norm_anisotropicMeasurePotential_jet_le_uniform
        (anisotropicReplaceVariance D i b) μ j hj (L x)) (show 0≤‖L‖^j by positivity)
      convert! hh using 1
      simp only [anisotropicSpatialJetBound,anisotropicReplaceVariance_energyMap,Q,hz,C,
        NNReal.coe_mul,coe_nnnorm,mul_pow,mul_assoc]
    have hQK:Q z≤K:=(Finset.single_le_sum (fun j _=>hQ j) (Finset.mem_univ z)).trans
      (by dsimp [K];linarith)
    exact hp.trans (hQK.trans (le_self_pow₀ hK (by omega)))
  let A:ℝ:=|U d 0|+(d+1)/2
  have hA:0≤A:=by dsimp [A];positivity
  have hUb b (hb:b∈Ioo (d/2) (d+1)):|U b 0|≤A:=by
    have hh:=anisotropicMeasureTailPotential_variance_abs_sub_le D μ ⟨0,by norm_num⟩
      (L 0) i b d (by linarith [hb.1]) hd
    simp only [anisotropicMeasureTailPotential_zero,sub_zero] at hh
    have hbd:|b-d|≤d+1:=by rw [abs_le];constructor <;> linarith [hb.1,hb.2]
    have ht:=abs_add_le (U b 0-U d 0) (U d 0)
    have hval:|U b 0-U d 0|≤(d+1)/2:=by
      exact hh.trans (by nlinarith)
    dsimp only [A]
    convert ht.trans (add_le_add hval le_rfl) using 1 <;> ring_nf
  have hLip b:LipschitzWith (‖anisotropicEnergyMap D‖₊*‖L‖₊) (U b):=by
    simpa only [anisotropicReplaceVariance_energyMap] using
      (anisotropicMeasurePotential_lipschitz (anisotropicReplaceVariance D i b) μ).comp L.lipschitz
  let M:ℝ:=∑j:Fin 4,(j.val.factorial:ℝ)*(max 1 |a|)^j.val*K^j.val
  let B:ℝ:=M*Real.exp (|a| *A)
  let R:ℝ:=|a| *C
  have hM:0≤M:=Finset.sum_nonneg fun j _=>by positivity
  refine ⟨B,R,by dsimp [B];positivity,by dsimp [R];positivity,?_⟩
  intro b hb j hj x
  have he:Real.exp (a*U b x)≤Real.exp (|a| *A)*Real.exp (R*‖x‖):=by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl:|U b x-U b 0|≤C*‖x‖:=by simpa only [Real.norm_eq_abs,sub_zero,C,NNReal.coe_mul] using (hLip b).norm_sub_le x 0
    have hv:=abs_add_le (U b x-U b 0) (U b 0)
    have hx:|U b x|≤C*‖x‖+A:=by
      convert hv.trans (add_le_add hl (hUb b hb)) using 1 <;> ring_nf
    have ha:=le_abs_self (a*U b x)
    rw [abs_mul] at ha
    have hm:=mul_le_mul_of_nonneg_left hx (abs_nonneg a)
    dsimp only [R]
    nlinarith only [ha,hm]
  have ht:=norm_iteratedFDeriv_exp_mul_le (U b) ((hU b).of_le (by simp):ContDiff ℝ 3 (U b))
    hj a K x (fun r hr hrj=>hUi b r hr (hrj.trans hj) x)
  have hcoef:(j.factorial:ℝ)*(max 1 |a|)^j*K^j≤M:=by
    exact Finset.single_le_sum
      (f:=fun z:Fin 4=>(z.val.factorial:ℝ)*(max 1 |a|)^z.val*K^z.val)
      (fun z _=>by positivity) (Finset.mem_univ (⟨j,by omega⟩:Fin 4))
  change ‖iteratedFDeriv ℝ j (fun y=>Real.exp (a*U b y)) x‖≤_
  calc
    _≤((j.factorial:ℝ)*(max 1 |a|)^j*K^j)*Real.exp (a*U b x):=by convert ht using 1 <;> ring
    _≤M*(Real.exp (|a| *A)*Real.exp (R*‖x‖)):=
      mul_le_mul hcoef he (Real.exp_pos _).le hM
    _=B*Real.exp (R*‖x‖):=by dsimp [B];ring

end QuantitativeFollowup
