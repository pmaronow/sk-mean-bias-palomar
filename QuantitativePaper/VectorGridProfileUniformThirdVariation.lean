module
public import QuantitativePaper.VectorGridProfileThirdCellBounds

@[expose] public section

/-! A genuine finite-grid telescope gives a depth-independent second
profile derivative bound at every restarted time and every field. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem norm_vectorGridProfileTailRecursion_third_profile_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ‖deriv (deriv (deriv (fun φ=>vectorProfileTailRecursion
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t q φ p
      (vectorDyadicIndex j+3) x))) θ‖≤vectorProfileThirdReactionBound n β t := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let N:=vectorDyadicIndex j+3
  let ρ:=Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)
  let X:=vectorRestartState (n:=n) ρ β t ht.le q p x
  let e : ℕ→ℝ:=fun i=>max 0 (s₀.q i-(q:ℝ))
  let F : ℝ→ℝ:=fun r=>∫sample : VectorDisorderBrownianSample n,
    deriv (deriv (deriv (fun φ=>vectorProfileTailRecursion s₀ s₁ β t ((q:ℝ)+r) φ p N
      (X r.toNNReal sample)))) θ ∂vectorDisorderBrownianMeasure n
  let M:=vectorProfileThirdReactionBound n β t
  have hM : 0≤M:=vectorProfileThirdReactionBound_nonneg n β t ht.le
  have he0 : e 0=0:=by
    dsimp only [e]
    rw [s₀.q_zero]
    exact max_eq_left (by linarith [q.property.1])
  have heN : e N=1-(q:ℝ):=by
    dsimp only [e,N]
    rw [s₀.q_top,max_eq_right (sub_nonneg.mpr q.property.2)]
  have hcell (i : ℕ) (hi : i∈Finset.range N) :
      |F (e (i+1))-F (e i)|≤M*(e (i+1)-e i) := by
    have hi' : i≤vectorDyadicIndex j+2:=by have hh:=Finset.mem_range.mp hi;dsimp only [N] at hh;omega
    have hmono : s₀.q i ≤ s₀.q (i+1):=s₀.q_mono i (by omega)
    have hab : e i≤e (i+1):=max_le_max le_rfl (sub_le_sub_right hmono (q:ℝ))
    by_cases hright : s₀.q (i+1)≤(q:ℝ)
    · have hea : e i=0:=max_eq_left (sub_nonpos.mpr (hmono.trans hright))
      have heb : e (i+1)=0:=max_eq_left (sub_nonpos.mpr hright)
      rw [hea,heb]
      simp
    · have hright' : (q:ℝ)<s₀.q (i+1):=lt_of_not_ge hright
      have hbEq : e (i+1)=s₀.q (i+1)-(q:ℝ):=
        max_eq_right (sub_nonneg.mpr hright'.le)
      have ha0 : 0≤e i:=le_max_left _ _
      have hb1 : e (i+1)≤1:=by
        have hnode : s₀.q (i+1)≤1:=s₀.q_le_one (by omega)
        rw [hbEq]
        linarith [q.property.1]
      have hleft : s₀.q i≤(q:ℝ)+e i:=by
        have hh:=le_max_right 0 (s₀.q i-(q:ℝ))
        change s₀.q i≤(q:ℝ)+max 0 (s₀.q i-(q:ℝ))
        linarith
      have hphysical (r : ℝ) (hr : r∈Icc (e i) (e (i+1))) :
          (q:ℝ)+r∈Icc (s₀.q i) (s₀.q (i+1)):=
        ⟨by linarith [hr.1],by rw [hbEq] at hr;linarith [hr.2]⟩
      have heF (r : ℝ) (hr : r∈Icc (e i) (e (i+1))) :
          F r=vectorGridProfileThirdRestartMoment μ ν j β t θ ht.le q p x i r := by
        apply integral_congr_ae
        exact .of_forall fun sample=>(vectorProfileCellPotentialThirdVariation_eq_tail
          s₀ s₁ β t i hi' ((q:ℝ)+r) (hphysical r hr) θ hθ p (X r.toNNReal sample)).symm
      rw [heF (e (i+1)) ⟨hab,le_rfl⟩,heF (e i) ⟨le_rfl,hab⟩]
      exact vectorGridProfile_third_restart_cell_bound μ ν j β t hβ ht θ hθ q p x i hi'
        (e i) (e (i+1)) ha0 hab hb1 hphysical
  have htotal : |F (e N)-F (e 0)|≤M*(1-(q:ℝ)) := by
    rw [←Finset.sum_range_sub (fun i=>F (e i)) N]
    calc
      _≤∑i∈Finset.range N,|F (e (i+1))-F (e i)|:=Finset.abs_sum_le_sum_abs _ _
      _≤∑i∈Finset.range N,M*(e (i+1)-e i):=Finset.sum_le_sum hcell
      _=_:=by rw [←Finset.mul_sum,Finset.sum_range_sub e N,heN,he0,sub_zero]
  have hterminal : F (e N)=0 := by
    rw [heN]
    have hphys : (q:ℝ)+(1-(q:ℝ))=1:=by ring
    simp only [F,hphys]
    have he : (fun sample : VectorDisorderBrownianSample n=>
        deriv (deriv (deriv (fun φ=>vectorProfileTailRecursion s₀ s₁ β t 1 φ p N
          (X (1-(q:ℝ)).toNNReal sample)))) θ)=(fun _=>0) := by
      funext sample
      exact vectorProfileTailRecursion_third_profile_terminal_zero s₀ s₁ β t θ hθ p _
    rw [he,integral_zero]
  have hinitial : F (e 0)=
      deriv (deriv (deriv (fun φ=>vectorProfileTailRecursion s₀ s₁ β t q φ p N x))) θ := by
    rw [he0]
    simp only [F,Real.toNNReal_zero,X,vectorRestartState_zero,add_zero]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  rw [hterminal,hinitial,zero_sub,abs_neg] at htotal
  rw [Real.norm_eq_abs]
  exact htotal.trans (mul_le_of_le_one_right hM (by linarith [q.property.1]))

end QuantitativePaper
