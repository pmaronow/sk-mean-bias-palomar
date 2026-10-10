module
public import QuantitativeFollowup.FiniteConcentratingPhysical
public import QuantitativeFollowup.SmoothLocalizationLayercake
public import QuantitativePaper.ResponseC1FamilyMidpoint

@[expose] public section

/-! Adaptive actual-model response for isolation. Every source input is
literal profile geometry or Stieltjes density. The response test and its
positive denominator bound are constructed, not assumed. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FourPapersCommon
open scoped ENNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 3200000

def smoothIsolationConstant (beta L : ℝ) : ℝ :=
  smoothLocalizationConstant beta L (responseCurvatureConstant beta)*
    localizationCaseConstant beta L/8192

theorem smoothIsolationConstant_pos (beta L : ℝ) (hb : 0<beta) (hL : 0<L) :
    0<smoothIsolationConstant beta L := by
  unfold smoothIsolationConstant
  exact div_pos (mul_pos (smoothLocalizationConstant_pos beta L _ hb hL
    (responseCurvatureConstant_pos beta)) (localizationCaseConstant_pos beta L hb hL)) (by norm_num)

theorem smooth_isolation_response_tests (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho theta q L h D : ℝ) (hbeta : 1≤beta) (hlam : 0≤lam)
    (hr : rho∈Ioc (0 : ℝ) 1) (hfloor : lam≤beta*parisiCDF (parisiMix μ ν theta) 0)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 1≤L) (hh : 0<h) (hD : 0<D)
    (hroot : beta*(parisiCDF ν 0-parisiCDF μ 0)≤0)
    (hslope : ∀z x : ℝ,0≤z→z≤x→x<q→
      beta*(parisiCDF ν x-parisiCDF μ x)-beta*(parisiCDF ν z-parisiCDF μ z)≤L*(x-z))
    (hanti : AntitoneOn (fun x=>beta*(parisiCDF ν x-parisiCDF μ x)) (Icc q 1))
    (hpost : ∀x∈Icc q 1,0≤beta*(parisiCDF ν x-parisiCDF μ x))
    (hbound : ∀x∈Icc (0 : ℝ) 1,|beta*(parisiCDF ν x-parisiCDF μ x)|≤beta)
    (hbudget : D/2≤∫x in (0 : ℝ)..1,|beta*(parisiCDF ν x-parisiCDF μ x)|)
    (hdensity : (ENNReal.ofReal beta • (parisiCDFPrimitive (parisiMix μ ν theta)).measure).restrict
      ({(0 : ℝ),q}ᶜ)≤ENNReal.ofReal (2*beta/h) • volume) :
    ∃w : ResponseC1Test,∃Y : ℝ,0<Y ∧
      responseC1EnergyDenominator (n:=n) μ ν beta (1-rho) lam theta (by linarith [hr.1]) w≤Y ∧
      (smoothIsolationConstant beta L*rho^2*min (rho*D^4) (h*D^2))*Y ≤
        rho^3*(responseC1Signal (n:=n) μ ν beta (1-rho) lam theta (by linarith [hr.1]) w)^2 := by
  have hb : 0<beta := zero_lt_one.trans_le hbeta
  have hLp : 0<L := zero_lt_one.trans_le hL
  let psi := fun x : ℝ=>beta*(parisiCDF ν x-parisiCDF μ x)
  let F := smoothIsolationConstant beta L*rho^2*min (rho*D^4) (h*D^2)
  have hF : 0<F := mul_pos (mul_pos (smoothIsolationConstant_pos beta L hb hLp)
    (sq_pos_of_pos hr.1)) (lt_min (mul_pos hr.1 (pow_pos hD 4))
      (mul_pos hh (pow_pos hD 2)))
  by_contra hNo
  have hFamilies : ∀A : ℝ,0<A→∀S : Finset ℕ,S.Nonempty→∀a : ℕ→ℝ,∀ell : ℝ,0<ell→
      (S:Set ℕ).PairwiseDisjoint (fun i=>Ioo (a i) (a i+ell))→
      (∀i∈S,Icc (a i) (a i+ell)⊆Ioo (0 : ℝ) q ∨ Icc (a i) (a i+ell)⊆Ioo q 1)→
      ∀sigma : ℝ,sigma^2=1→(∀i∈S,∀x∈Icc (a i) (a i+ell),A/2 ≤ sigma*psi x)→
        smoothFamilyCoefficient beta rho h (responseCurvatureConstant beta) A (S.card : ℝ) ell≤F := by
    intro A hA S hS a ell hell hdisj hinside sigma hsigma hSign
    have ha : ∀i∈S,0≤a i := by
      intro i hi
      have hx : a i∈Icc (a i) (a i+ell) := ⟨le_rfl,by linarith⟩
      rcases hinside i hi with hs|hs
      · exact (hs hx).1.le
      · exact hq.1.le.trans (hs hx).1.le
    have he : ∀i∈S,a i+ell≤1 := by
      intro i hi
      have hx : a i+ell∈Icc (a i) (a i+ell) := ⟨by linarith,le_rfl⟩
      rcases hinside i hi with hs|hs
      · exact (hs hx).2.le.trans hq.2.le
      · exact (hs hx).2.le
    have hz : finiteConcentratingBump S a ell q=0 := by
      apply finiteConcentratingBump_zero_outside S a ell hell
      intro hu
      obtain ⟨i,hi⟩ := mem_iUnion.mp hu
      obtain ⟨his,hxi⟩ := mem_iUnion.mp hi
      rcases hinside i his with hs|hs
      · exact lt_irrefl q (hs ⟨hxi.1.le,hxi.2.le⟩).2
      · exact lt_irrefl q (hs ⟨hxi.1.le,hxi.2.le⟩).1
    have hEn := finite_concentrating_response_envelope hn μ ν beta (1-rho) lam theta q
      (2*beta/h) A sigma hbeta ⟨by linarith [hr.2],by linarith [hr.1]⟩ hlam hfloor
      (by positivity) hA.le hsigma S hS a ell hell ha he hdisj hdensity hz hSign
    have hEn' :
        let w := finiteConcentratingResponseTest S a ell hell ha he
        let Y := beta*(S.card : ℝ)*512/(105*ell)+2*(2*beta/h)*
          finiteResponseDelta (n:=n) (parisiMix μ ν theta) beta (1-rho) lam (by linarith [hr.1]) S a ell
        0<Y ∧ responseC1EnergyDenominator (n:=n) μ ν beta (1-rho) lam theta (by linarith [hr.1]) w≤Y ∧
          smoothFamilyCoefficient beta rho h (responseCurvatureConstant beta) A (S.card : ℝ) ell*Y ≤
            rho^3*(responseC1Signal (n:=n) μ ν beta (1-rho) lam theta (by linarith [hr.1]) w)^2 := by
      simpa only [show 1-(1-rho)=rho by ring,smoothFamilyCoefficient] using hEn
    dsimp only at hEn'
    by_contra hlt
    have hle := le_of_not_ge hlt
    apply hNo
    refine ⟨_,_,hEn'.1,hEn'.2.1,?_⟩
    exact (mul_le_mul_of_nonneg_right hle hEn'.1.le).trans hEn'.2.2
  have hCoercivity := localization_coercivity_of_smooth_families psi
    (((parisiCDF_measurable ν).sub (parisiCDF_measurable μ)).const_mul beta)
    q beta L (responseCurvatureConstant beta) rho h D F hq hb hL
    (responseCurvatureConstant_pos beta) hr.1 hh hD.le hF.le hroot hslope hanti hpost hbound hbudget hFamilies
  have hDouble : 2*F≤F := by
    convert hCoercivity using 1
    dsimp only [F,smoothIsolationConstant]
    ring
  linarith only [hDouble,hF]

end QuantitativeFollowup
