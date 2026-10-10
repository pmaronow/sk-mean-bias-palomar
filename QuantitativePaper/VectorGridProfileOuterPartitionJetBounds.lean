module
public import QuantitativePaper.VectorGridProfileOuterJetBounds
public import QuantitativePaper.ScalarExponentialThirdJetBound
public import QuantitativePaper.VectorProfileOuterPartitionDerivatives

@[expose] public section

/-! Genuine Gaussian differentiation yields depth-independent bounds on
the first three literal outer partition jets, with the partition factor. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem norm_vectorGridProfileOuterPartition_jet_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (outer θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (r : ℕ) (hr : r∈Finset.Icc 1 3) :
    ‖iteratedDeriv r (vectorProfileOuterPartition (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t outer) θ‖≤
      scalarExponentialJetBound outer ((n:ℝ)*((1-t)*β^2)/2)
        (vectorProfileSecondReactionBound n β t) (vectorProfileThirdReactionBound n β t) r*
          vectorProfileOuterPartition (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
            (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t outer θ := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let a:=θ/2
  let b:=(θ+1)/2
  have ha : 0<a:=by dsimp [a];linarith [hθ.1]
  have hb : b<1:=by dsimp [b];linarith [hθ.2]
  have hx : θ∈Ioo a b:=by dsimp [a,b];constructor <;>linarith [hθ.1,hθ.2]
  have hr3 : r≤3:=(Finset.mem_Icc.mp hr).2
  let F:=fun φ (p : Couplings n×ℝ)=>vectorProfileRecursion s₀ s₁ β t φ p (vectorDyadicIndex j+3) 0
  let C:=scalarExponentialJetBound outer ((n:ℝ)*((1-t)*β^2)/2)
    (vectorProfileSecondReactionBound n β t) (vectorProfileThirdReactionBound n β t) r
  have hraw:=vectorProfileOuter_dominatedJets (n:=n) s₀ s₁ β t ht.le 3 (vectorDyadicIndex j+3) a b ha hb
  have hexp:=vectorProfileOuter_exponential_dominatedJets (n:=n) s₀ s₁ β t ht.le outer 3
    (vectorDyadicIndex j+3) a b ha hb
  have he:=hexp.iteratedDeriv_integral isOpen_Ioo hr3 hx
  have hi:=hexp.integrable_iteratedDeriv hr3 hx
  have hiexp : Integrable (fun p : Couplings n×ℝ=>Real.exp (outer*F θ p)) (completionLaw n):=by
    dsimp only [F]
    simp only [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ ⟨hθ.1.le,hθ.2.le⟩]
    exact integrable_exp_vectorRecursion _ β t outer (vectorDyadicIndex j+3) 0
  have hpoint (p : Couplings n×ℝ) :
      ‖iteratedDeriv r (fun φ=>Real.exp (outer*F φ p)) θ‖≤C*Real.exp (outer*F θ p):=by
    exact norm_iteratedDeriv_exp_three_jets_le (fun φ=>F φ p) outer (Ioo a b) isOpen_Ioo
      (hraw.smooth p) _ _ _ (by positivity)
      (vectorProfileSecondReactionBound_nonneg n β t ht.le)
      (vectorProfileThirdReactionBound_nonneg n β t ht.le) θ hx
      (by simpa only [vectorProfileOuterDerivative,iteratedDeriv_one,F,s₀,s₁] using
        abs_vectorGridProfileOuterDerivative_one_le μ ν j β t ht.le θ hθ p)
      (by simpa only [vectorProfileOuterDerivative,F,s₀,s₁] using
        abs_vectorGridProfileOuterDerivative_two_le μ ν j β t hβ ht θ hθ p)
      (by simpa only [vectorProfileOuterDerivative,F,s₀,s₁] using
        abs_vectorGridProfileOuterDerivative_three_le μ ν j β t hβ ht θ hθ p) r hr
  change ‖iteratedDeriv r (fun φ=>∫p,Real.exp (outer*F φ p)∂completionLaw n) θ‖≤_
  rw [he]
  apply (norm_integral_le_integral_norm _).trans
  have hbound:=integral_mono hi.norm (hiexp.const_mul C) hpoint
  rw [integral_const_mul] at hbound
  exact hbound

end QuantitativePaper
