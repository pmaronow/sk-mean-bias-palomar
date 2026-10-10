module
public import QuantitativePaper.VectorProfileExpectedVariationEndpoints
public import QuantitativePaper.VectorProfileClosedPositiveSource
public import FourPapersCommon.CellDifferenceTelescope

@[expose] public section

/-! The actual total nonnegative profile-response energy equals the
literal outer initial second derivative and is bounded by the true
finite energy-functional curvature for every nonnegative outer tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileSecondVariationCellEnergy
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Icc (0:ℝ) 1) (i : ℕ) : ℝ:=
  ∫q in (s₀.q i)..(s₀.q (i+1)),
    vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht hθ
      (vectorProfileFieldSecondVariationSource s₀ s₁ β t i) q.toNNReal

def vectorProfileSecondVariationTotalEnergy
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Icc (0:ℝ) 1) : ℝ:=
  ∑i∈Finset.range (k+2),vectorProfileSecondVariationCellEnergy (n:=n) s₀ s₁ β t outer θ ht hθ i

theorem vectorProfileSecondVariationTotalEnergy_eq_outer (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) :
    vectorProfileSecondVariationTotalEnergy (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩=
      (∫p : Couplings n×ℝ,vectorProfileOuterDerivative s₀ s₁ β t 2 θ p
        ∂vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer)/β := by
  let F : ℕ→ℝ→ℝ:=fun i=>vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileRetainedSecondVariation s₀ s₁ β t i)
  have hc : ∀i∈Finset.range (k+2),vectorProfileSecondVariationCellEnergy (n:=n) s₀ s₁ β t outer θ
      ht.le ⟨hθ.1.le,hθ.2.le⟩ i=F i (s₀.q (i+1))-F i (s₀.q i):=by
    intro i hi
    exact (vectorProfile_second_variation_closed_source hn s₀ s₁ β t outer θ hβ ht i
      (by have := Finset.mem_range.mp hi;omega) hθ).2.symm
  have hm : ∀i<k+1,F (i+1) (s₀.q (i+1))=F i (s₀.q (i+1)):=by
    intro i hi
    exact vectorProfile_retained_second_variation_expected_match s₀ s₁ β t outer θ ht.le hθ
      i (i+1) (by omega) (by omega) (s₀.q (i+1))
      ⟨s₀.q_mono i (by omega),le_rfl⟩ ⟨le_rfl,s₀.q_mono (i+1) (by omega)⟩
  unfold vectorProfileSecondVariationTotalEnergy
  rw [Finset.sum_congr rfl hc,sum_cell_differences_of_match F s₀.q (k+1) hm]
  simp only [F,s₀.q_top,s₀.q_zero]
  rw [vectorProfile_retained_second_variation_expected_terminal s₀ s₁ β t outer θ ht.le hθ,
    vectorProfile_retained_second_variation_expected_initial s₀ s₁ β t outer θ ht.le hθ]
  ring

theorem vectorProfileSecondVariationTotalEnergy_nonneg
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Icc (0:ℝ) 1) :
    0≤vectorProfileSecondVariationTotalEnergy (n:=n) s₀ s₁ β t outer θ ht hθ := by
  apply Finset.sum_nonneg
  intro i hi
  unfold vectorProfileSecondVariationCellEnergy
  rw [intervalIntegral.integral_of_le (s₀.q_mono i (by have := Finset.mem_range.mp hi;omega))]
  apply integral_nonneg
  intro q
  exact integral_nonneg (fun sample=>mul_nonneg (sub_nonneg.mpr ht)
    (responseMatrixFrobeniusSquare_nonneg _))

theorem vectorProfileFiniteEnergyFunctional_curvature_ge_total_energy
    (hn : 0<n) (s₀ s₁ : RSBScheme k) (β t lam θ : ℝ)
    (hβ : 0<β) (ht : t<1) (hlam : 0≤lam) (hθ : θ∈Ioo (0:ℝ) 1) :
    vectorProfileSecondVariationTotalEnergy (n:=n) s₀ s₁ β t (lam/β) θ ht.le ⟨hθ.1.le,hθ.2.le⟩/(n:ℝ)≤
      iteratedDeriv 2 (vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam) θ := by
  rw [vectorProfileSecondVariationTotalEnergy_eq_outer hn s₀ s₁ β t (lam/β) θ hβ ht hθ,
    vectorProfileFiniteEnergyFunctional_second_variation s₀ s₁ β t hβ.ne' ht.le hn lam θ hθ]
  have hn0 : (0:ℝ)<n:=by exact_mod_cast hn
  have hVar:=variance_nonneg (fun p : Couplings n×ℝ=>vectorProfileOuterDerivative s₀ s₁ β t 1 θ p/β)
    (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t (lam/β))
  have hv : 0≤(lam/(n:ℝ))*variance
      (fun p : Couplings n×ℝ=>vectorProfileOuterDerivative s₀ s₁ β t 1 θ p/β)
      (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t (lam/β)):=
    mul_nonneg (div_nonneg hlam hn0.le) hVar
  have hdiv (a : ℝ) : a/β/(n:ℝ)=a/((n:ℝ)*β):=by field_simp
  rw [hdiv]
  exact le_add_of_nonneg_right hv

end QuantitativePaper
