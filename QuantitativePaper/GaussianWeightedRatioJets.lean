module
public import QuantitativePaper.GaussianWeightedJets
public import QuantitativePaper.GaussianDerivativeBounds
public import QuantitativePaper.FiniteJetBounds

@[expose] public section

/-! Genuine bounded spatial jets of normalized weighted Gaussian
expectations. The bounds are uniform in the variance/shift operator: relative
numerator jets cancel the positive partition denominator exactly. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

def gaussianWeightedShiftRatio {n : ℕ} (A : Field n →L[ℝ] E)
    (m : ℝ) (f g : E → ℝ) (x : E) : ℝ :=
  gaussianWeightedShiftMoment A m f g x/gaussianShiftPartition A m f x

def gaussianWeightedRatioJetCoefficient (m K D : ℝ) (G : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i∈Finset.range (j+1),(j.choose i : ℝ)*gaussianWeightedJetCoefficient m K G i*
    gaussianJetCoefficient 1 D (j-i)

theorem gaussianWeightedShiftRatio_uniform_jets {n : ℕ} (N : ℕ)
    (f g : E → ℝ) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    (L : ℝ≥0) (hlip : LipschitzWith L f) (m K : ℝ) (hK : 0 ≤ K)
    (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (hgJets : ∀ i,i ≤ N → ∀ x,‖iteratedFDeriv ℝ i g x‖ ≤ G i) :
    ∃ B : ℕ → ℝ,(∀ j,0 ≤ B j) ∧
      ∀ A : Field n →L[ℝ] E,ContDiff ℝ N (gaussianWeightedShiftRatio A m f g) ∧
        ∀ j,j ≤ N → ∀ x,‖iteratedFDeriv ℝ j (gaussianWeightedShiftRatio A m f g) x‖ ≤ B j := by
  let C : ℕ → ℝ := fun j=>(j.factorial : ℝ)*logJetCoefficient j*
    (gaussianDerivativePowerBound m K N)^j
  let D := finiteJetPowerBound C N
  have hD : 1 ≤ D := finiteJetPowerBound_ge_one C N
  let B := gaussianWeightedRatioJetCoefficient m K D G
  refine ⟨B,?_,?_⟩
  · intro j
    exact Finset.sum_nonneg (fun i _=>mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (gaussianWeightedJetCoefficient_nonneg m K hK G hG i))
      (gaussianJetCoefficient_nonneg 1 D (zero_le_one.trans hD) _))
  · intro A
    let Z := gaussianShiftPartition A m f
    let M := gaussianWeightedShiftMoment A m f g
    have hZ : ContDiff ℝ N Z := contDiff_gaussianShiftPartition N f hf L hlip K hK hjets A m
    have hpos : ∀ x,0 < Z x := gaussianShiftPartition_pos f L hlip A m
    have hM : ContDiff ℝ N M := contDiff_gaussianWeightedShiftMoment N f g hf hg L hlip m K hK G hG
      hjets hgJets A
    have hlog : ContDiff ℝ N (fun x=>Real.log (Z x)) := hZ.log (fun x=>(hpos x).ne')
    have hneg : ContDiff ℝ N (fun x=>-Real.log (Z x)) := hlog.neg
    have hnegJets (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) (x : E) :
        ‖iteratedFDeriv ℝ i (fun y=>-Real.log (Z y)) x‖ ≤ D^i := by
      change ‖iteratedFDeriv ℝ i (-(fun y=>Real.log (Z y))) x‖ ≤ _
      rw [iteratedFDeriv_neg_apply,norm_neg]
      exact (norm_iteratedFDeriv_log_gaussianShiftPartition_le N i f hf L hlip K hK hjets A m hi hiN x).trans
        (finite_jet_bound_le_power C N i hi hiN)
    let R : E → ℝ := fun x=>Real.exp (-Real.log (Z x))
    have hR : ContDiff ℝ N R := hneg.exp
    have hRB (i : ℕ) (hiN : i ≤ N) (x : E) :
        ‖iteratedFDeriv ℝ i R x‖ ≤ gaussianJetCoefficient 1 D i*(Z x)⁻¹ := by
      have hh := norm_iteratedFDeriv_exp_mul_le (fun y=>-Real.log (Z y)) hneg hiN 1 D x
        (fun l hl hli=>hnegJets l hl (hli.trans hiN) x)
      simpa only [R,one_mul,Real.exp_neg,Real.exp_log (hpos x),gaussianJetCoefficient,
        mul_assoc,mul_left_comm,mul_comm] using hh
    have he : gaussianWeightedShiftRatio A m f g=fun x=>M x*R x := by
      funext x
      simp only [gaussianWeightedShiftRatio,M,R,Real.exp_neg,Real.exp_log (hpos x),div_eq_mul_inv,Z]
    refine ⟨by rw [he];exact hM.mul hR,?_⟩
    intro j hj x
    rw [he]
    apply (norm_iteratedFDeriv_mul_le hM hR x (by exact_mod_cast hj)).trans
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hm := norm_iteratedFDeriv_gaussianWeightedShiftMoment_le N i f g hf hg L hlip m K hK
      G hG hjets hgJets A (hi'.trans hj) x
    have hr := hRB (j-i) ((Nat.sub_le j i).trans hj) x
    have hh := mul_le_mul hm hr (norm_nonneg _)
      (mul_nonneg (gaussianWeightedJetCoefficient_nonneg m K hK G hG i) (hpos x).le)
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (j.choose i))
    change (j.choose i : ℝ)*‖iteratedFDeriv ℝ i M x‖*‖iteratedFDeriv ℝ (j-i) R x‖ ≤ _
    calc
      _ ≤ (j.choose i : ℝ)*(gaussianWeightedJetCoefficient m K G i*Z x)*
          (gaussianJetCoefficient 1 D (j-i)*(Z x)⁻¹) := by
        simpa only [M,Z,mul_assoc] using hh'
      _ = _ := by field_simp [(hpos x).ne'] <;> ring

end QuantitativePaper
