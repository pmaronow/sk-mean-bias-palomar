module
public import QuantitativeFollowup.FollowupCavityThreeEndpointMoments

@[expose] public section

/-! Literal physical u=1 three-descendant moment transport and the deleted
site thermal budget. Every terminal continuation remains conditionally
independent under the actual normalized model law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem standardSKOffDiagonalThreeDescendant_integral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (F : CavityThreeTerminalSpins n→ℝ) :
    (∫z,F z.2∂cavityThreeDescendantLaw (standardSKOffDiagonalModel n β t hβ ht) μ a q)=
      ∫z,F z.2∂cavityVectorThreeDescendantLaw μ β t a ht.le q := by
  have he:=congrArg (fun P:Measure (VectorMarkedSample n×CavityThreeTerminalSpins n)=>
    ∫z,F z.2∂P) (standardSKOffDiagonalThreeDescendantLaw μ β t a hβ ht q)
  rw [integral_map (f:=fun z:VectorMarkedSample n×CavityThreeTerminalSpins n=>F z.2)
      measurable_cavityThreeEndpointCompression.aemeasurable
      ((measurable_of_finite F).comp measurable_snd).aestronglyMeasurable,
    integral_map (f:=fun z:VectorMarkedSample n×CavityThreeTerminalSpins n=>F z.2)
      measurable_cavityVectorThreeRemoveDiagonal.aemeasurable
      ((measurable_of_finite F).comp measurable_snd).aestronglyMeasurable] at he
  exact he

theorem followup_cavity_one_three_descendant_integral (hn:0<n)
    (μ : Paper.ParisiMeasure) (β ρ a : ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (q : Paper.Overlap) (F:CavityThreeTerminalSpins (n+1)→ℝ) :
    (∫z,F z.2∂cavityThreeDescendantLaw
      (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a q)=
      ∫z,F z.2∂cavityVectorThreeDescendantLaw μ β (1-ρ) a (by linarith[hρ.1]) q := by
  rw [followupCavitySpinModel_one_eq_offDiagonal n hn β ρ hβ hρ]
  exact standardSKOffDiagonalThreeDescendant_integral μ β (1-ρ) a hβ.ne'
    (by linarith[hρ.1]) q F

theorem followup_cavity_one_deleted_three_square_le (hn:0<n)
    (μ : Paper.ParisiMeasure) (β ρ a : ℝ) (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1)
    (q : Paper.Overlap) :
    (∫z,(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2/(n:ℝ))^2
      ∂cavityThreeDescendantLaw
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a q)≤
      16*(foundationThermalTrace (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
        foundationMeanCovariance (n:=n+1) μ β (1-ρ) a (by linarith[hρ.1]) q+
        1/((n+1:ℕ):ℝ)^2) := by
  let ht : 1-ρ<1:=by linarith[hρ.1]
  let P:=cavityVectorThreeDescendantLaw (n:=n+1) μ β (1-ρ) a ht.le q
  let B:=foundationThermalTrace (n:=n+1) μ β (1-ρ) a ht.le q+
    foundationMeanCovariance (n:=n+1) μ β (1-ρ) a ht.le q
  let X:=∫z,(cavitySpinDifferencePairing Finset.univ z.2)^2∂P
  let Y:=∫z,(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2)^2∂P
  have hx : X/((n+1:ℕ):ℝ)^2=2*B := by
    have he:=cavityVectorThreeDescendantLaw_normalized_difference_square (n:=n+1)
      μ β (1-ρ) a hβ.ne' ht q
    simpa only [div_pow,integral_div] using he
  have hB : 0≤B := by
    have hX : 0≤X:=integral_nonneg (fun z=>sq_nonneg _)
    have hh:=div_nonneg hX (sq_nonneg (((n+1:ℕ):ℝ)))
    rw [hx] at hh
    linarith
  have hy : Y≤2*X+4:=cavityVectorThreeDescendant_deleted_difference_square_le
    (n:=n+1) μ β (1-ρ) a ht.le q (Fin.last n)
  have hnR : 1≤(n:ℝ):=by exact_mod_cast hn
  have hn2 : 0<(n:ℝ)^2:=sq_pos_of_pos (by linarith)
  have hN2 : 0<((n+1:ℕ):ℝ)^2:=sq_pos_of_pos (by positivity)
  have hscale : ((n+1:ℕ):ℝ)^2≤4*(n:ℝ)^2 := by
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  have hx' : X=2*B*((n+1:ℕ):ℝ)^2 := (div_eq_iff hN2.ne').mp hx
  have hpower:=mul_le_mul_of_nonneg_right hscale hB
  have hconst : 4≤16*(n:ℝ)^2/((n+1:ℕ):ℝ)^2 :=
    (le_div_iff₀ hN2).mpr (by nlinarith[hscale])
  have hb : Y/(n:ℝ)^2≤16*(B+1/((n+1:ℕ):ℝ)^2) := by
    apply (div_le_iff₀ hn2).mpr
    rw [hx'] at hy
    calc
      Y≤4*((n+1:ℕ):ℝ)^2*B+4 := by nlinarith[hy]
      _≤16*(n:ℝ)^2*B+16*(n:ℝ)^2/((n+1:ℕ):ℝ)^2 := by nlinarith[hpower,hconst]
      _=16*(B+1/((n+1:ℕ):ℝ)^2)*(n:ℝ)^2 := by ring
  have he:=followup_cavity_one_three_descendant_integral hn μ β ρ a hβ hρ q
    (fun σ=>(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) σ/(n:ℝ))^2)
  have he' : (∫z,(cavitySpinDifferencePairing (Finset.univ.erase (Fin.last n)) z.2/(n:ℝ))^2
      ∂cavityThreeDescendantLaw
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) μ a q)=Y/(n:ℝ)^2 := by
    simpa only [div_pow,integral_div] using he
  exact he'.trans_le hb

end QuantitativeFollowup
