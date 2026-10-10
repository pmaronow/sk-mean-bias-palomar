module
public import QuantitativeFollowup.OneSignCoercivity

@[expose] public section

/-! Native unit-interval and literal finite-union formulation of the
one-sign coercivity lemma. The global extension is obtained by the actual
unit-interval clamp; no smooth cutoff or positive-energy premise is added. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory Paper QuantitativePaper
open scoped NNReal ENNReal Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def oneSignUnitTestExtension (φ : Paper.Overlap→ℝ) (q : ℝ) : ℝ :=
  φ (projIcc 0 1 zero_le_one q)

theorem oneSignUnitTestExtension_lipschitz (φ : Paper.Overlap→ℝ) (K : ℝ≥0)
    (hφ : LipschitzWith K φ) : LipschitzWith K (oneSignUnitTestExtension φ) := by
  change LipschitzWith K (fun q=>φ (projIcc 0 1 zero_le_one q))
  simpa only [mul_one,Function.comp_def] using
    hφ.comp (LipschitzWith.projIcc zero_le_one)

theorem oneSignUnitTestExtension_off (φ : Paper.Overlap→ℝ) (I : Set ℝ)
    (hI : I⊆Ioo (0:ℝ) 1) (hoff : ∀q : Paper.Overlap,(q:ℝ)∉I→φ q=0) :
    ∀q∉I,oneSignUnitTestExtension φ q=0 := by
  intro q hq
  unfold oneSignUnitTestExtension
  apply hoff
  by_cases hq0 : q ≤ 0
  · rw [projIcc_of_le_left zero_le_one hq0]
    exact fun h=>lt_irrefl (0:ℝ) (hI h).1
  by_cases hq1 : 1 ≤ q
  · rw [projIcc_of_right_le zero_le_one hq1]
    exact fun h=>lt_irrefl (1:ℝ) (hI h).2
  · rw [projIcc_of_mem zero_le_one ⟨(lt_of_not_ge hq0).le,(lt_of_not_ge hq1).le⟩]
    exact hq

theorem oneSignFiniteIntervals_closure (S : Finset ℕ) (a b : ℕ→ℝ)
    (ha : ∀i∈S,0<a i) (hb : ∀i∈S,b i<1) :
    closure (⋃i∈S,Ioo (a i) (b i))⊆Ioo (0:ℝ) 1 := by
  have hsub : (⋃i∈S,Ioo (a i) (b i))⊆(⋃i∈S,Icc (a i) (b i)) := by
    intro q hq
    obtain ⟨i,hi,hqi⟩:=mem_iUnion₂.mp hq
    exact mem_iUnion₂.mpr ⟨i,hi,⟨hqi.1.le,hqi.2.le⟩⟩
  have hclosed : IsClosed (⋃i∈S,Icc (a i) (b i)):=isClosed_biUnion_finset (fun _ _=>isClosed_Icc)
  intro q hq
  obtain ⟨i,hi,hqi⟩:=mem_iUnion₂.mp ((closure_minimal hsub hclosed) hq)
  exact ⟨(ha i hi).trans_le hqi.1,hqi.2.trans_lt (hb i hi)⟩

/-- Follow-up Lemma5.3, for every native Lipschitz unit-interval test and
every finite union of interior open intervals. The zero-density branch is
the paper's extended-real convention, represented by its finite minimum. -/
theorem followup_one_sign_coercivity_finite_intervals (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (β lam rho θ : ℝ) (hβ : 0<β) (hlam : 0≤lam) (hrho : 0<rho)
    (hθ : θ∈Ioo (0:ℝ) 1) (S : Finset ℕ) (a b : ℕ→ℝ)
    (ha : ∀i∈S,0<a i) (hb : ∀i∈S,b i<1)
    (φ : Paper.Overlap→ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ)
    (hφ01 : ∀q,φ q∈Icc (0:ℝ) 1)
    (hoff : ∀q : Paper.Overlap,(q:ℝ)∉(⋃i∈S,Ioo (a i) (b i))→φ q=0)
    (hne : ∃q,φ q≠0) (A d σ : ℝ) (hA : 0<A) (hd : 0≤d) (hσ : |σ|=1)
    (hsign : ∀i∈S,∀q∈Ioo (a i) (b i),
      A/2≤σ*(responseProfile ν β q-responseProfile μ β q))
    (hdensity : (oneSignEnergyStieltjes (parisiMix μ ν θ) β).restrict
      (⋃i∈S,Ioo (a i) (b i))≤ENNReal.ofReal d • volume) :
    let ht : 1-rho≤1 := by linarith
    let f := fun y=>followupEnergyFunctional n β lam rho (parisiMix μ ν y)
    let ζ := responseAveragedCurvatureReal (n:=n) (parisiMix μ ν θ) β (1-rho) lam ht
    let Δ := rho*(∫q in (0:ℝ)..1,ζ q*oneSignUnitTestExtension φ q)
    let Y0 := ∫q in (0:ℝ)..1,(deriv (oneSignUnitTestExtension φ) q)^2
    0<Y0 ∧ (rho*A^2/72*oneSignCoercivityMinimum Δ (β*Y0) d ≤ iteratedDeriv 2 f θ) ∧
      ∀δ, 0≤δ → δ≤Δ → rho*A^2/72*oneSignCoercivityMinimum δ (β*Y0) d ≤ iteratedDeriv 2 f θ := by
  have hIc:=oneSignFiniteIntervals_closure S a b ha hb
  have hIo : (⋃i∈S,Ioo (a i) (b i))⊆Ioo (0:ℝ) 1:=subset_closure.trans hIc
  have hne' : ∃q∈Icc (0:ℝ) 1,oneSignUnitTestExtension φ q≠0 := by
    obtain ⟨q,hq⟩:=hne
    refine ⟨q,q.property,?_⟩
    simpa only [oneSignUnitTestExtension,projIcc_val] using hq
  have hs : ∀q∈(⋃i∈S,Ioo (a i) (b i)),
      A/2≤σ*(responseProfile ν β q-responseProfile μ β q) := by
    intro q hq
    obtain ⟨i,hi,hqi⟩:=mem_iUnion₂.mp hq
    exact hsign i hi q hqi
  have hbase:=followup_one_sign_coercivity hn μ ν β lam rho θ hβ hlam hrho hθ _ hIc
    (oneSignUnitTestExtension φ) K (oneSignUnitTestExtension_lipschitz φ K hφ)
    (fun q _=>hφ01 (projIcc 0 1 zero_le_one q))
    (oneSignUnitTestExtension_off φ _ hIo hoff) hne' A d σ hA hd hσ hs hdensity
  dsimp only at hbase ⊢
  refine ⟨hbase.1,hbase.2,?_⟩
  intro δ hδ hδΔ
  have hΔ : 0≤rho*(∫q in (0:ℝ)..1,
      responseAveragedCurvatureReal (n:=n) (parisiMix μ ν θ) β (1-rho) lam
        (by linarith) q*oneSignUnitTestExtension φ q) := by
    apply mul_nonneg hrho.le
    apply intervalIntegral.integral_nonneg zero_le_one
    intro q _
    exact mul_nonneg (responseAveragedCurvature_nonneg _ _ _ _ _ _)
      (hφ01 (projIcc 0 1 zero_le_one q)).1
  apply (mul_le_mul_of_nonneg_left
    (oneSignCoercivityMinimum_monotone _ d (mul_pos hβ hbase.1) hd hδ hΔ hδΔ)
    (by positivity : 0≤rho*A^2/72)).trans hbase.2

end QuantitativeFollowup
