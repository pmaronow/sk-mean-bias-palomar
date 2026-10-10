module
public import QuantitativePaper.VectorJointObservableRecursion

@[expose] public section

/-! Genuine smooth bounded tests with a fixed disorder parameter, lifted to the
retained product space used by the stochastic backward verification. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_snd_le (f : E→F) {N j : ℕ}
    (hf : ContDiff ℝ N f) (hj : j≤N) (p : A×E)
    (C : ℝ) (hC : 0≤C) (hb : ∀x,‖iteratedFDeriv ℝ j f x‖≤C) :
    ‖iteratedFDeriv ℝ j (fun z : A×E=>f z.2) p‖≤C := by
  let L : A×E→L[ℝ]E:=ContinuousLinearMap.snd ℝ A E
  have hL : ‖L‖≤1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖z.2‖ ≤ 1*max ‖z.1‖ ‖z.2‖
    simpa only [one_mul] using (le_max_right ‖z.1‖ ‖z.2‖)
  change ‖iteratedFDeriv ℝ j (f ∘ L) p‖≤C
  rw [L.iteratedFDeriv_comp_right hf p (by exact_mod_cast hj)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  calc
    _≤C*‖L‖^j:=mul_le_mul_of_nonneg_right (hb (L p)) (pow_nonneg (norm_nonneg _) _)
    _≤C*1:=by
      have hp : ‖L‖^j≤1:=by
        simpa only [one_pow] using (pow_le_pow_left₀ (norm_nonneg L) hL j)
      exact mul_le_mul_of_nonneg_left hp hC
    _=C:=mul_one C

variable {n : ℕ}

def VectorResponseTestData.fixedParameter {f g : Field n→ℝ}
    (d : VectorResponseTestData f g) :
    VectorJointResponseTestData (fun z=>f z.2) (fun z=>g z.2) where
  potentialRegularity := d.potentialRegularity.comp contDiff_snd
  observableRegularity := d.observableRegularity.comp contDiff_snd
  fieldLip := d.fieldLip
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have hp : dist z.2 w.2≤dist z w:=by
      simpa only [Prod.dist_eq] using (le_max_right (dist z.1 w.1) (dist z.2 w.2))
    exact (d.lipschitz.dist_le_mul z.2 w.2).trans
      (mul_le_mul_of_nonneg_left hp d.fieldLip.coe_nonneg)
  potentialPower := d.potentialPower
  potentialPower_ge_one := d.potentialPower_ge_one
  potentialJets j hj hjN z:=norm_iteratedFDeriv_snd_le f d.potentialRegularity hjN z
    _ (pow_nonneg d.potentialPower.coe_nonneg _) (d.potentialJets j hj hjN)
  observableBounds := d.observableBounds
  observableBounds_nonneg := d.observableBounds_nonneg
  observableJets j hjN z:=norm_iteratedFDeriv_snd_le g d.observableRegularity hjN z
    _ (d.observableBounds_nonneg j) (d.observableJets j hjN)

def VectorBoundedC3.fixedParameter {G : VectorParameter n→ℝ}
    (d : VectorBoundedC3 G) (p : Couplings n×ℝ) :
    VectorBoundedC3 (fun z : VectorParameter n=>G (p,z.2)) where
  regularity:=d.regularity.comp (contDiff_const.prodMk contDiff_snd)
  bounds:=d.bounds
  bounds_nonneg:=d.bounds_nonneg
  jets j hjN z:=norm_iteratedFDeriv_snd_le (fun x=>G (p,x))
    (d.regularity.comp (contDiff_const.prodMk contDiff_id)) hjN z
    _ (d.bounds_nonneg j) (fun x=>norm_iteratedFDeriv_fieldSlice_le
      G d.regularity hjN p x _ (d.bounds_nonneg j) (d.jets j hjN))

end QuantitativePaper
