module
public import QuantitativePaper.VectorGridProfileRestartDrift
public import QuantitativePaper.VectorProfileRestartTestBounds
public import QuantitativePaper.VectorProfileRestartExpectedContinuity

@[expose] public section

/-! Actual cropped second-profile-variation identities along the genuine
restarted grid diffusion. The exact source is the bounded reaction term. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorGridProfileSecondRestartReaction
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t θ : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (i : ℕ)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ℝ:=
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let y:=vectorRestartState (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ)
    (vectorDyadicIndex j)) β t ht q p x r sample
  let G:=gradient (fun z=>vectorProfileCellJointPotential s₀ s₁ β t i (((q:ℝ)+r,θ,p),z)) y
  let P:=gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i ((q:ℝ)+r,θ,p)) y
  (-((1-t)*β^2)*(vectorProfileMass s₀ s₁ θ i*‖P‖^2+
    2*(s₁.m i-s₀.m i)*inner ℝ G P))

theorem vectorGridProfile_second_restart_cropped
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    (a b : ℝ≥0) (hab : a≤b) (hb1 : b≤1)
    (ha : (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i<(q:ℝ)+(a:ℝ))
    (hb : (q:ℝ)+(b:ℝ)<(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)) :
    let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
    let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
    let X:=vectorRestartState (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ)
      (vectorDyadicIndex j)) β t ht.le q p x
    let W:=vectorGridProfileSecondRestartReaction μ ν j β t θ ht.le q p x i
    Integrable (Function.uncurry W)
      ((nonnegativeLebesgueMeasure.restrict (Ioc a b)).prod (vectorDisorderBrownianMeasure n)) ∧
      (∫sample,vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+b,θ,p) (X b sample)-
        vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+a,θ,p) (X a sample)
        ∂vectorDisorderBrownianMeasure n)=
      ∫r in Ioc a b,(∫sample,W r sample∂vectorDisorderBrownianMeasure n)
        ∂nonnegativeLebesgueMeasure := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let l:=(s₀.q i+(q:ℝ)+(a:ℝ))/2
  let u:=((q:ℝ)+(b:ℝ)+s₀.q (i+1))/2
  have hl : s₀.q i≤l:=by dsimp only [l];linarith
  have hu : u<s₀.q (i+1):=by dsimp only [u];linarith
  have hla : l-(q:ℝ)<(a:ℝ):=by dsimp only [l];linarith
  have hbu : (b:ℝ)<u-(q:ℝ):=by dsimp only [u];linarith
  let f : ℝ×Field n→ℝ:=fun z=>
    vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+z.1,θ,p) z.2
  let ρ:=Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)
  let X:=vectorRestartState (n:=n) ρ β t ht.le q p x
  let d:=vectorAdditiveDrift (vectorRestartDriftData (n:=n) ρ β t ht.le q p)
    (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)
  let W:=vectorGridProfileSecondRestartReaction μ ν j β t θ ht.le q p x i
  let P:=vectorDisorderBrownianMeasure n
  let τ:=nonnegativeLebesgueMeasure.restrict (Ioc a b)
  obtain ⟨hf,B,K,hB,hK,hjets,htime⟩:=vectorProfile_second_restart_test_bounds s₀ s₁ β t hβ ht
    i hi l u hl hu θ hθ q p
  obtain ⟨hI,hD⟩:=vector_restart_fixed_parameter_cell_dynkin ρ β t ht.le q p x f
    (l-(q:ℝ)) (u-(q:ℝ)) hf B K hB hjets htime a b hab hb1 hla hbu
  have he (r : ℝ≥0) (hr : r∈Ioc a b) (sample : VectorDisorderBrownianSample n) :
      vectorRestartCellGenerator f X d ((1-t)*β^2) r sample=W r sample := by
    have hphysical : (q:ℝ)+(r:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1)):=
      ⟨by linarith [hr.1],by linarith [hr.2]⟩
    exact vectorGridProfile_restart_second_generator μ ν j β t hβ ht θ hθ q p x i hi r hphysical sample
  have hMem : ∀ᵐz ∂τ.prod P,z.1∈Ioc a b:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact .of_forall fun _=>hr
  have hW : Integrable (Function.uncurry W) (τ.prod P):=hI.congr (by
    filter_upwards [hMem] with z hz
    exact he z.1 hz z.2)
  have heI : (∫sample,(∫r in Ioc a b,
      vectorRestartCellGenerator f X d ((1-t)*β^2) r sample∂nonnegativeLebesgueMeasure)∂P)=
      ∫sample,(∫r in Ioc a b,W r sample∂nonnegativeLebesgueMeasure)∂P := by
    apply integral_congr_ae
    exact .of_forall fun sample=>setIntegral_congr_fun measurableSet_Ioc (fun r hr=>he r hr sample)
  rw [heI] at hD
  exact ⟨hW,hD.trans (integral_integral_swap hW).symm⟩

end QuantitativePaper
