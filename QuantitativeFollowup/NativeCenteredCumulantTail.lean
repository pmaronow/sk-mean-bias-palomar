module
public import FourPapersCommon.CenteredUpperTailCGF
public import QuantitativePaper.VarianceSensitiveTail
public import QuantitativePaper.NormalizedMoments

@[expose] public section

/-! The cited small-tilt centered cumulant estimate is derived from the
actual finite-SK variance-sensitive tail, with numerical constants. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000

def centeredEnergyCGF (n : ℕ) (β lam : ℝ) : ℝ :=
  cgf (fun g=>energyFreeEnergy n β g-(∫g,energyFreeEnergy n β g ∂couplingLaw n))
    (couplingLaw n) lam

def nativeCumulantTailRate : ℝ := Real.log 3/4
def nativeCumulantCoefficient : ℝ := 1024/nativeCumulantTailRate^2
def nativeCumulantRadius : ℝ := nativeCumulantTailRate/32

theorem nativeCumulantTailRate_pos_le : 0<nativeCumulantTailRate ∧
    nativeCumulantTailRate≤1 := by
  have hp : 0<Real.log (3:ℝ):=Real.log_pos (by norm_num)
  have hb:=Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  dsimp only [nativeCumulantTailRate]
  constructor <;> linarith

theorem nativeCumulantConstants : 0<nativeCumulantCoefficient ∧
    0<nativeCumulantRadius ∧ nativeCumulantCoefficient*nativeCumulantRadius^2=1 := by
  have hk:=nativeCumulantTailRate_pos_le.1
  refine ⟨by unfold nativeCumulantCoefficient;positivity,
    by unfold nativeCumulantRadius;positivity,?_⟩
  unfold nativeCumulantCoefficient nativeCumulantRadius
  field_simp
  norm_num

theorem native_centered_cumulant_tail_bound (n : ℕ) (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (lam : ℝ) (hlam : 0≤lam) (hSmall : lam*varianceTailScale n β≤nativeCumulantRadius) :
    centeredEnergyCGF n β lam ≤ nativeCumulantCoefficient*lam^2*
      (variance (energyFreeEnergy n β) (couplingLaw n)+β⁻¹^2) := by
  let P:=couplingLaw n
  let X:=energyFreeEnergy n β
  let Z : Couplings n → ℝ:=fun g=>X g-(∫g,X g ∂P)
  let D:=varianceTailScale n β
  let k:=nativeCumulantTailRate
  let a:=k/(2*D)
  have hD : 0<D:=varianceTailScale_pos n β hβ
  have hk : 0<k:=nativeCumulantTailRate_pos_le.1
  have hk1 : k≤1:=nativeCumulantTailRate_pos_le.2
  have ha : 0<a:=div_pos hk (mul_pos (by norm_num) hD)
  have hXm : Measurable X:=((continuous_logPartition n β).div_const β).measurable
  have hZm : Measurable Z:=hXm.sub measurable_const
  have hZi : Integrable Z P:=(integrable_energyFreeEnergy n β).sub (integrable_const _)
  have hZsq : Integrable (fun g=>Z g^2) P:=
    (memLp_two_iff_integrable_sq hZm.aestronglyMeasurable).mp
      ((memLp_two_energyFreeEnergy n β).sub (memLp_const _))
  have hCenter : (∫g,Z g ∂P)=0:=by
    rw [show Z=(fun g=>X g-(∫g,X g ∂P)) from rfl,
      integral_sub (integrable_energyFreeEnergy n β) (integrable_const _),integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul,X,P,sub_self]
  have hExp (s : ℝ) : Integrable (fun g=>Real.exp (s*Z g)) P:=by
    dsimp only [Z]
    simp_rw [mul_sub,Real.exp_sub,div_eq_mul_inv]
    exact (integrable_exp_energyFreeEnergy n β s).mul_const _
  have hPosExp : Integrable (fun g=>Real.exp (a*max (Z g) 0)) P:=by
    apply ((integrable_const 1).add (hExp a)).mono'
      ((hZm.max measurable_const).const_mul a).exp.aestronglyMeasurable
    filter_upwards [] with g
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    change Real.exp (a*max (Z g) 0)≤1+Real.exp (a*Z g)
    by_cases hz : 0≤Z g
    · rw [max_eq_left hz]
      linarith
    · rw [max_eq_right (le_of_not_ge hz),mul_zero,Real.exp_zero]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
  have hla : lam≤a/2:=by
    have hs : lam*D≤k/32:=hSmall
    change lam≤(k/(2*D))/2
    apply (le_div_iff₀ (by norm_num : 0<(2:ℝ))).mpr
    apply (le_div_iff₀ (mul_pos (by norm_num : 0<(2:ℝ)) hD)).mpr
    nlinarith
  have hTail : ∀u : ℝ,0<u → P.real {g | u≤Z g}≤3*Real.exp (-(2*a)*u):=by
    intro u hu
    have ht:=variance_sensitive_energy_tail n hn β hβ u hu.le
    convert ht using 1
    congr 2
    dsimp only [a,k,nativeCumulantTailRate,varianceTailRate,D]
    field_simp
    <;> ring
  have hCGF:=FourPapersCommon.centered_upper_tail_cgf_bound P Z hZm hZi hZsq hCenter
    a lam ha hlam hla (hExp lam) hPosExp hTail
  have hVeq : (∫g,Z g^2 ∂P)=variance X P:=
    (variance_eq_integral hXm.aemeasurable).symm
  rw [hVeq] at hCGF
  have hVs : variance X P≤D^2:=by
    rw [show D^2=variance X P+β⁻¹^2 from varianceTailScale_sq n β]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hk2 : k^2≤1:=by nlinarith
  have hVk : variance X P*k^2≤D^2:=
    (mul_le_mul_of_nonneg_left hk2 (variance_nonneg X P)).trans
      (by simpa only [mul_one] using hVs)
  have haeq : 32/a^2=128*D^2/k^2:=by
    dsimp only [a]
    field_simp
    <;> ring
  have hBracket : variance X P+32/a^2≤2048*D^2/k^2:=by
    rw [haeq]
    apply (le_div_iff₀ (sq_pos_of_pos hk)).mpr
    have he : (variance X P+128*D^2/k^2)*k^2=
        variance X P*k^2+128*D^2:=by field_simp <;> ring
    rw [he]
    nlinarith [sq_nonneg D]
  have hb:=mul_le_mul_of_nonneg_left hBracket (by positivity : 0≤lam^2/2)
  have he : lam^2/2*(2048*D^2/k^2)=nativeCumulantCoefficient*lam^2*
      (variance X P+β⁻¹^2):=by
    rw [←show D^2=variance X P+β⁻¹^2 from varianceTailScale_sq n β]
    dsimp only [nativeCumulantCoefficient,k]
    ring
  exact hCGF.trans (hb.trans_eq he)

end QuantitativeFollowup
