module
public import QuantitativePaper.VectorGridProfileCellVariationBounds
public import QuantitativePaper.VectorRestartFiniteCellBackward
public import QuantitativePaper.VectorGridProfileMix
public import QuantitativePaper.VectorRestartCellDynkin

@[expose] public section

/-! Actual restarted grid-mixture drift and exact cancellation in the
twice-linearized profile equation. No drift or PDE identity is supplied. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorGridProfile_restart_cell_drift
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (ht : t≤1)
    (θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    (r : ℝ≥0) (hr : (q:ℝ)+(r:ℝ)∈Ioo
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)))
    (sample : VectorDisorderBrownianSample n) :
    let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
    let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
    let ρ:=Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)
    let X:=vectorRestartState ρ β t ht q p x
    vectorAdditiveDrift (vectorRestartDriftData ρ β t ht q p)
      (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q) r sample=
      (((1-t)*β^2)*vectorProfileMass s₀ s₁ θ i) •
        gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (((q:ℝ)+r,θ,p),y))
          (X r sample) := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  have hd:=vectorRestart_grid_cell_drift (Paper.parisiMix μ ν θ) j β t ht q p x i hi r hr sample
  rw [←vector_grid_profile_scheme_eq_mix μ ν (vectorDyadicIndex j) θ hθ] at hd
  have he : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (((q:ℝ)+r,θ,p),y))=
      vectorColeHopfStep (((1-t)*β^2)*(s₀.q (i+1)-((q:ℝ)+r)))
        (vectorProfileMass s₀ s₁ θ i)
        (vectorRecursion (vectorProfileScheme s₀ s₁ θ hθ) β t p (vectorDyadicIndex j+2-i)):=by
    funext y
    exact vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i ((q:ℝ)+r) θ hθ p y
  change vectorAdditiveDrift
      (vectorRestartDriftData (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t ht q p)
      (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q) r sample=
    (((1-t)*β^2)*vectorProfileMass s₀ s₁ θ i) •
      gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (((q:ℝ)+r,θ,p),y)) _
  rw [he]
  simpa only [smul_smul,vectorProfileScheme,s₀,s₁] using hd

theorem vectorGridProfile_restart_second_generator
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    (r : ℝ≥0) (hr : (q:ℝ)+(r:ℝ)∈Ioo
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)))
    (sample : VectorDisorderBrownianSample n) :
    let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
    let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
    let ρ:=Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)
    let X:=vectorRestartState ρ β t ht.le q p x
    let d:=vectorAdditiveDrift (vectorRestartDriftData ρ β t ht.le q p)
      (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)
    let f : ℝ×Field n→ℝ:=fun z=>
      vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+z.1,θ,p) z.2
    let y:=X r sample
    let G:=gradient (fun z=>vectorProfileCellJointPotential s₀ s₁ β t i (((q:ℝ)+r,θ,p),z)) y
    let P:=gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i ((q:ℝ)+r,θ,p)) y
    vectorRestartCellGenerator f X d ((1-t)*β^2) r sample=
      -((1-t)*β^2)*(vectorProfileMass s₀ s₁ θ i*‖P‖^2+
        2*(s₁.m i-s₀.m i)*inner ℝ G P) := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let ρ:=Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)
  let X:=vectorRestartState (n:=n) ρ β t ht.le q p x
  let d:=vectorAdditiveDrift (vectorRestartDriftData (n:=n) ρ β t ht.le q p)
    (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)
  let f : ℝ×Field n→ℝ:=fun z=>
    vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+z.1,θ,p) z.2
  let y:=X r sample
  have hf : ContDiffAt ℝ ∞ f (r,y):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>(((q:ℝ)+z.1,θ,p),z.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialSecondVariation s₀ s₁ β t i z.1 z.2) (r,y)
    (contDiffAt_vectorProfileCellPotentialSecondVariation s₀ s₁ β t hβ ht i hi
      ((q:ℝ)+r,θ,p) hr.2 hθ y) (by fun_prop)
  have htime:=(hasDerivAt_vectorProfileCellPotentialSecondVariation_time s₀ s₁ β t hβ ht i hi
    ((q:ℝ)+r,θ,p) hr.2 hθ y).comp (r:ℝ)
      ((hasDerivAt_const (r:ℝ) (q:ℝ)).add (hasDerivAt_id (r:ℝ)))
  have he:=(hasDerivAt_vectorRestartCell_time hf).unique htime
  simp only [zero_add,mul_one] at he
  have hd:=vectorGridProfile_restart_cell_drift μ ν j β t ht.le θ ⟨hθ.1.le,hθ.2.le⟩ q p x i hi r hr sample
  change d r sample=_ at hd
  change vectorRestartCellGenerator f X d ((1-t)*β^2) r sample=_
  unfold vectorRestartCellGenerator
  rw [hd,he,vectorBilinearTrace_hessian_eq_laplacian]
  simp only [map_smul,smul_eq_mul]
  rw [←inner_gradient_left]
  change ((1-t)*β^2*vectorProfileMass s₀ s₁ θ i)*
      inner ℝ (gradient (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+r,θ,p)) y)
        (gradient (fun z=>vectorProfileCellJointPotential s₀ s₁ β t i (((q:ℝ)+r,θ,p),z)) y)+_+_=_
  rw [real_inner_comm]
  ring

end QuantitativePaper
