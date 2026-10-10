module
public import QuantitativePaper.VectorProfileCellExpectationIntegrable

@[expose] public section

/-! True expected-source interval laws, with endpoint integrability and
space-time Fubini discharged for actual exponential profile observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileCellExpectation (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ)
    (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (F : VectorProfileCellParameter n×Field n→ℝ) (q : ℝ≥0) : ℝ:=
  let s:=vectorProfileScheme s₀ s₁ θ hθ
  ∫sample : VectorDisorderBrownianSample n,F ((q,θ,sample.1),vectorFiniteState s β t ht q sample)
    ∂vectorFiniteDisorderTilt s β t outer

theorem vectorProfile_expected_source_interval
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (F H : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀l u A B : ℝ,s₀.q i≤l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (hEq : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,p) x=H ((q,θ,p),x))
    (a b : ℝ≥0) (hab : a≤b) (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    let E:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    IntegrableOn (E H) (Ioc a b) nonnegativeLebesgueMeasure ∧
      E F b-E F a=∫r in Ioc a b,E H r ∂nonnegativeLebesgueMeasure := by
  let l:=(s₀.q i+a)/2
  let u:=(b+s₀.q (i+1))/2
  let A:=θ/2
  let B:=(θ+1)/2
  have hl : s₀.q i≤l:=by dsimp [l];linarith
  have hu : u<s₀.q (i+1):=by dsimp [u];linarith
  have hA : 0<A:=by dsimp [A];linarith [hθ.1]
  have hB : B<1:=by dsimp [B];linarith [hθ.2]
  have hθAB : θ∈Ioo A B:=by dsimp [A,B];constructor <;>linarith [hθ.1,hθ.2]
  have hl0 : 0≤l:=(s₀.q_nonneg (by omega)).trans hl
  have hu1 : u≤1:=hu.le.trans (s₀.q_le_one (by omega))
  have haLU : (a:ℝ)∈Ioo l u:=by dsimp [l,u];constructor <;>linarith [hab]
  have hbLU : (b:ℝ)∈Ioo l u:=by dsimp [l,u];constructor <;>linarith [hab]
  let s:=vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩
  let X:=vectorFiniteState (n:=n) s β t ht.le
  let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t outer
  let S : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>H ((r,θ,sample.1),X r sample)
  obtain ⟨hInt,hId⟩:=vectorProfile_source_dynkin s₀ s₁ β t outer θ ht i hi hθ F H hGrowth hEq
    a b hab haq hbq
  have haF:=integrable_vectorProfile_cell_observable s₀ s₁ β t outer θ ht.le l u A B
    hl0 hu1 hA hB hθAB F (hGrowth l u A B hl hu hA hB) a haLU
  have hbF:=integrable_vectorProfile_cell_observable s₀ s₁ β t outer θ ht.le l u A B
    hl0 hu1 hA hB hθAB F (hGrowth l u A B hl hu hA hB) b hbLU
  rw [integral_sub hbF haF] at hId
  exact ⟨hInt.integral_prod_left,hId.trans (integral_integral_swap hInt).symm⟩

end QuantitativePaper
