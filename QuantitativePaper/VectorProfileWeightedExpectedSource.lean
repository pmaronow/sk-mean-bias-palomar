module
public import QuantitativePaper.VectorProfileWeightedGenerator
public import QuantitativePaper.VectorProfileActualExpectedSource

@[expose] public section

/-! Actual affine and squared-affine time testing of the finite profile
generator. These are the pieces of the tent tests in the response bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiffAt_vectorProfile_of_cell_growth
    (s₀ : RSBScheme k) (i : ℕ)
    (F : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀l u A B : ℝ,s₀.q i≤l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (a : VectorProfileCellParameter n) (x : Field n)
    (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ F (a,x) := by
  let u:=(a.1+s₀.q (i+1))/2
  let A:=a.2.1/2
  let B:=(a.2.1+1)/2
  apply (hGrowth (s₀.q i) u A B le_rfl (by dsimp [u];linarith [hq.2])
    (by dsimp [A];linarith [hθ.1]) (by dsimp [B];linarith [hθ.2])).smooth
  dsimp [vectorProfileJointCylinder,u,A,B]
  exact ⟨⟨hq.1,by linarith [hq.2]⟩,⟨by linarith [hθ.1],by linarith [hθ.2]⟩⟩

theorem vectorProfile_affine_expected_source_interval
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (F H : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀l u A B : ℝ,s₀.q i≤l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (hEq : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,p) x=H ((q,θ,p),x))
    (α δ : ℝ) (a b : ℝ≥0) (hab : a≤b)
    (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (fun z=>(α+δ*z.1.1)*F z)
      (fun z=>δ*F z+(α+δ*z.1.1)*H z) a b := by
  apply vectorProfile_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
  · intro l u A B hl hu hA hB
    exact exponentialSmoothOn_vectorProfile_affine_time_mul F l u A B α δ
      (hGrowth l u A B hl hu hA hB) ((s₀.q_nonneg (by omega)).trans hl)
      (hu.le.trans (s₀.q_le_one (by omega)))
  · intro q hq p x
    have hF:=(contDiffAt_vectorProfile_of_cell_growth s₀ i F hGrowth (q,θ,p) x hq hθ).of_le
      (show (2 : ℕ∞ω)≤∞ by simp)
    have hw : HasDerivAt (fun r : ℝ=>α+δ*r) δ q:=by
      exact (hasDerivAt_const_mul (x:=q) δ).const_add α
    rw [vectorProfileCellFieldGenerator_time_mul s₀ s₁ β t i F _ (q,θ,p) x
      hF hw.differentiableAt,hw.deriv,hEq q hq p x]
  · exact hab
  · exact haq
  · exact hbq

theorem exponentialSmoothOn_vectorProfile_squared_affine_time_mul
    (F : VectorProfileCellParameter n×Field n→ℝ) (l u A B α δ : ℝ)
    (hf : ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (hl : 0≤l) (hu : u≤1) :
    ExponentialSmoothOn (fun z=>(α+δ*z.1.1)^2*F z)
      (vectorProfileJointCylinder l u A B) := by
  have hq:=exponentialSmoothOn_vectorProfile_time_coordinate (n:=n) l u A B hl hu
  have hw:=(ExponentialSmoothOn.const α _).add (hq.compCLM (δ • ContinuousLinearMap.id ℝ ℝ))
  convert (hw.bilinear hw (ContinuousLinearMap.mul ℝ ℝ)).bilinear hf
    (ContinuousLinearMap.mul ℝ ℝ) using 1
  funext z
  simp only [pow_two,ContinuousLinearMap.mul_apply',ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,Function.comp_apply,smul_eq_mul,Pi.add_apply]

theorem vectorProfile_squared_affine_expected_source_interval
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (F H : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀l u A B : ℝ,s₀.q i≤l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (hEq : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,p) x=H ((q,θ,p),x))
    (α δ : ℝ) (a b : ℝ≥0) (hab : a≤b)
    (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (fun z=>(α+δ*z.1.1)^2*F z)
      (fun z=>2*δ*(α+δ*z.1.1)*F z+(α+δ*z.1.1)^2*H z) a b := by
  apply vectorProfile_expected_source_interval s₀ s₁ β t outer θ ht i hi hθ
  · intro l u A B hl hu hA hB
    exact exponentialSmoothOn_vectorProfile_squared_affine_time_mul F l u A B α δ
      (hGrowth l u A B hl hu hA hB) ((s₀.q_nonneg (by omega)).trans hl)
      (hu.le.trans (s₀.q_le_one (by omega)))
  · intro q hq p x
    have hF:=(contDiffAt_vectorProfile_of_cell_growth s₀ i F hGrowth (q,θ,p) x hq hθ).of_le
      (show (2 : ℕ∞ω)≤∞ by simp)
    have hw : HasDerivAt (fun r : ℝ=>(α+δ*r)^2) (2*δ*(α+δ*q)) q:=by
      convert ((hasDerivAt_const_mul (x:=q) δ).const_add α).pow 2 using 1 <;>ring
    rw [vectorProfileCellFieldGenerator_time_mul s₀ s₁ β t i F _ (q,θ,p) x
      hF hw.differentiableAt,hw.deriv,hEq q hq p x]
  · exact hab
  · exact haq
  · exact hbq

end QuantitativePaper
