module
public import QuantitativePaper.VectorProfileGeneratorExponential
public import QuantitativePaper.VectorProfileRetainedExpectedContinuity
public import QuantitativePaper.VectorProfileWeightedExpectedSource

@[expose] public section

/-! Genuine strict-cell continuity of expected generator sources under
the actual fractional diffusion law, using one Fernique path envelope. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem continuousOn_vectorProfileCellExpectation_cropped
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (l u A B a b : ℝ) (hl : 0≤l) (hu : u≤1) (hA : 0<A) (hB : B<1)
    (hθ : θ∈Ioo A B) (hla : l<a) (hbu : b<u)
    (F : VectorProfileCellParameter n×Field n→ℝ)
    (hF : ExponentialSmoothOn F (vectorProfileJointCylinder l u A B)) :
    ContinuousOn (fun q=>vectorProfileCellExpectation s₀ s₁ β t outer θ ht
      ⟨(hA.trans hθ.1).le,(hθ.2.trans hB).le⟩ F q.toNNReal) (Icc a b):=by
  obtain ⟨hSmooth,C,R,hC,hR,hjets,_⟩:=vectorProfileTestRestriction_exponential_bounds
    F l u A B θ hF hl hu hA hB hθ
  have hcont : ContinuousOn (vectorProfileTestRestriction θ F) (Icc a b×ˢuniv):=by
    apply hSmooth.continuousOn.mono
    intro z hz
    exact ⟨hla.trans_le hz.1.1,hz.1.2.trans_lt hbu⟩
  have hbnd (q : ℝ) (hq : q∈Icc a b) (p : Couplings n×ℝ) (x : Field n) :
      |vectorProfileTestRestriction θ F (q,p,x)|≤C*Real.exp (R*(‖p‖+‖x‖)):=by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
      hjets q ⟨hla.trans_le hq.1,hq.2.trans_lt hbu⟩ p x 0 (by norm_num)
  have hc:=continuousOn_vectorFinite_expected_exp_test
    (vectorProfileScheme s₀ s₁ θ ⟨(hA.trans hθ.1).le,(hθ.2.trans hB).le⟩)
    β t outer ht a b (hl.trans hla.le) (hbu.le.trans hu)
    (vectorProfileTestRestriction θ F) hcont C R hC hR hbnd
  apply hc.congr
  intro q hq
  have hq0 : 0≤q:=(hl.trans hla.le).trans hq.1
  simp only [vectorProfileCellExpectation,vectorProfileTestRestriction,
    Real.coe_toNNReal _ hq0]

theorem continuousAt_vectorProfileCellExpectation_of_growth
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (F : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀l u A B : ℝ,s₀.q i≤l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (q : ℝ) (hq : q∈Ioo (s₀.q i) (s₀.q (i+1))) :
    ContinuousAt (fun r=>vectorProfileCellExpectation s₀ s₁ β t outer θ ht
      ⟨hθ.1.le,hθ.2.le⟩ F r.toNNReal) q:=by
  let a:=(s₀.q i+q)/2
  let b:=(q+s₀.q (i+1))/2
  let u:=(b+s₀.q (i+1))/2
  have hc:=continuousOn_vectorProfileCellExpectation_cropped s₀ s₁ β t outer θ ht
    (s₀.q i) u (θ/2) ((θ+1)/2) a b (s₀.q_nonneg (by omega))
    (by dsimp [u,b];linarith [hq.2,s₀.q_le_one (by omega : i+1≤k+2)])
    (by linarith [hθ.1]) (by linarith [hθ.2])
    ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
    (by dsimp [a];linarith [hq.1]) (by dsimp [u,b];linarith [hq.2]) F
    (hGrowth _ _ _ _ le_rfl (by dsimp [u,b];linarith [hq.2])
      (by linarith [hθ.1]) (by linarith [hθ.2]))
  exact hc.continuousAt (Icc_mem_nhds (by dsimp [a];linarith [hq.1])
    (by dsimp [b];linarith [hq.2]))

theorem continuousAt_vectorProfileExpectedGeneratorSource
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (F H : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀l u A B : ℝ,s₀.q i≤l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (hEq : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,p) x=H ((q,θ,p),x))
    (q : ℝ) (hq : q∈Ioo (s₀.q i) (s₀.q (i+1))) :
    ContinuousAt (fun r=>vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le
      ⟨hθ.1.le,hθ.2.le⟩ H r.toNNReal) q:=by
  have hc:=continuousAt_vectorProfileCellExpectation_of_growth s₀ s₁ β t outer θ ht.le i hi hθ
    (fun z=>vectorProfileCellFieldGenerator s₀ s₁ β t i F z.1 z.2)
    (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldGenerator
      s₀ s₁ β t hβ ht i hi l u A B hu hA hB F (hGrowth l u A B hl hu hA hB)) q hq
  apply hc.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hq] with r hr
  have hr0 : 0≤r:=(s₀.q_nonneg (by omega)).trans hr.1.le
  unfold vectorProfileCellExpectation
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    simp only [Real.coe_toNNReal _ hr0]
    exact (hEq r hr sample.1 _).symm

end QuantitativePaper
