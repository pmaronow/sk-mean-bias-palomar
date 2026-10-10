module
public import QuantitativePaper.UniformBoundaryBarrierValues
public import FourPapersCommon.WeightedParabolicJets

@[expose] public section

/-! Full source Lemma 5.1 with genuine one-sided time jets. Only the reaction
upper bound enters the proof; the resulting lower bound is independent of it. -/
noncomputable section
open Set Filter
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1800000

theorem uniform_boundary_strictness (τ ell ε : ℝ) (hτ : 0<τ)
    (hell : ell∈Ioc (0 : ℝ) 4) (hε : 0<ε)
    (W Wt W₁ W₂ B C : ℝ×ℝ→ℝ) (Cmax : ℝ)
    (hc : ContinuousOn W (Icc 0 τ×ˢIcc 0 ell))
    (hW : ∀p∈Icc 0 τ×ˢIcc 0 ell,0≤W p)
    (ht : ∀r∈Ioc (0 : ℝ) τ,∀x∈Ioo (0 : ℝ) ell,
      HasDerivWithinAt (fun s=>W (s,x)) (Wt (r,x)) (Icc 0 τ) r)
    (h1 : ∀r∈Ioc (0 : ℝ) τ,∀x∈Ioo (0 : ℝ) ell,
      HasDerivAt (fun y=>W (r,y)) (W₁ (r,x)) x)
    (h2 : ∀r∈Ioc (0 : ℝ) τ,∀x∈Ioo (0 : ℝ) ell,
      HasDerivAt (fun y=>W₁ (r,y)) (W₂ (r,x)) x)
    (hB : ∀r∈Ioc (0 : ℝ) τ,∀x∈Ioo (0 : ℝ) ell,0≤B (r,x))
    (hC : ∀r∈Ioc (0 : ℝ) τ,∀x∈Ioo (0 : ℝ) ell,0≤C (r,x) ∧ C (r,x)≤Cmax)
    (hPDE : ∀r∈Ioc (0 : ℝ) τ,∀x∈Ioo (0 : ℝ) ell,
      Wt (r,x)=(1/2 : ℝ)*W₂ (r,x)+B (r,x)*W₁ (r,x)+C (r,x)*W (r,x))
    (hright : ∀r∈Icc (0 : ℝ) τ,ε≤W (r,ell)) :
    ∀p∈Icc 0 τ×ˢIcc 0 ell,
      (1/4 : ℝ)*uniformBoundaryAlpha τ*ε*Real.exp (-uniformBoundaryAlpha τ)*
        (p.2-4*(τ-p.1)/τ)≤W p := by
  let V:=uniformBoundaryBarrier τ ell ε
  let K:=Cmax+1
  let Z:=weightedParabolicDifference K W V
  let Zt : ℝ×ℝ→ℝ:=fun p=>Real.exp (-K*p.1)*
    (Wt p-uniformBoundaryBarrierTime τ ell ε p-K*(W p-V p))
  let κ : ℝ×ℝ→ℝ:=fun p=>C p-K
  have hz : ContinuousOn Z (Icc 0 τ×ˢIcc 0 ell):=
    ((show Continuous (fun p : ℝ×ℝ=>Real.exp (-K*p.1)) from by fun_prop).continuousOn).mul
      (hc.sub (continuous_uniformBoundaryBarrier τ ell ε).continuousOn)
  have hzt (r : ℝ) (hr : r∈Ioc (0 : ℝ) τ) (x : ℝ) (hx : x∈Ioo (0 : ℝ) ell) :
      HasDerivWithinAt (fun s=>Z (s,x)) (Zt (r,x)) (Icc 0 τ) r:=
    hasDerivWithinAt_weightedParabolicDifference_time K W V τ r x _ _
      (ht r hr x hx) (hasDerivAt_uniformBoundaryBarrier_time τ ell ε r x).hasDerivWithinAt
  have hzx (r : ℝ) (hr : r∈Ioc (0 : ℝ) τ) (x : ℝ) (hx : x∈Ioo (0 : ℝ) ell) :
      HasDerivAt (fun y=>Z (r,y))
        (Real.exp (-K*r)*(W₁ (r,x)-uniformBoundaryBarrierFirst τ ell ε (r,x))) x:=
    hasDerivAt_weightedParabolicDifference_field K W V r x _ _
      (h1 r hr x hx) (hasDerivAt_uniformBoundaryBarrier_field τ ell ε r x)
  have hzxx (r : ℝ) (hr : r∈Ioc (0 : ℝ) τ) (x : ℝ) (hx : x∈Ioo (0 : ℝ) ell) :
      deriv (deriv (fun y=>Z (r,y))) x=
        Real.exp (-K*r)*(W₂ (r,x)-uniformBoundaryBarrierSecond τ ell ε (r,x)):=
    weightedParabolicDifference_second_deriv K W V W₁
      (uniformBoundaryBarrierFirst τ ell ε) r 0 ell x _ _ hx (h1 r hr)
      (fun y _=>hasDerivAt_uniformBoundaryBarrier_field τ ell ε r y)
      (h2 r hr x hx) (hasDerivAt_uniformBoundaryBarrier_first τ ell ε r x)
  have hcomparison : ∀p∈Icc 0 τ×ˢIcc 0 ell,0≤Z p:=by
    apply compact_negative_supersolution_nonneg τ 0 ell hτ.le hell.1 Z Zt B κ
      hz hzt (fun r hr x hx=>(hzx r hr x hx).differentiableAt)
    · intro r hr x hx
      dsimp only [κ,K]
      linarith [(hC r hr x hx).2]
    · intro r hr x hx hneg
      have hWV : W (r,x)<V (r,x):=by
        have hh : W (r,x)-V (r,x)<0:=neg_of_mul_neg_right hneg (Real.exp_pos _).le
        linarith
      have hVpos : 0≤V (r,x):=(hW (r,x) ⟨⟨hr.1.le,hr.2⟩,⟨hx.1.le,hx.2.le⟩⟩).trans hWV.le
      have hheat:=uniformBoundaryBarrier_heat_subsolution τ ell ε r x (B (r,x))
        hτ hell hε.le (hB r hr x hx)
      have hCV:=mul_nonneg (hC r hr x hx).1 hVpos
      calc
        _=Real.exp (-K*r)*((1/2 : ℝ)*uniformBoundaryBarrierSecond τ ell ε (r,x)+
            B (r,x)*uniformBoundaryBarrierFirst τ ell ε (r,x)-
            uniformBoundaryBarrierTime τ ell ε (r,x)+C (r,x)*V (r,x)):=by
          rw [(hzx r hr x hx).deriv,hzxx r hr x hx]
          dsimp only [Zt,Z,κ,weightedParabolicDifference]
          rw [hPDE r hr x hx]
          ring
        _≥0:=mul_nonneg (Real.exp_pos _).le (by linarith)
    · intro x hx
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr
        ((uniformBoundaryBarrier_initial_nonpos τ ell ε x hτ hell.1 hε.le hx.2).trans
          (hW (0,x) ⟨⟨le_rfl,hτ.le⟩,hx⟩)))
    · intro r hr
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr
        ((uniformBoundaryBarrier_left_nonpos τ ell ε r hτ hε.le hr.2).trans
          (hW (r,0) ⟨hr,⟨le_rfl,hell.1.le⟩⟩)))
    · intro r hr
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr
        ((uniformBoundaryBarrier_right_le τ ell ε r hτ hell.1 hε.le hr.2).trans (hright r hr)))
  intro p hp
  have hdiff : 0≤W p-V p:=nonneg_of_mul_nonneg_right (hcomparison p hp) (Real.exp_pos _)
  exact (uniformBoundaryBarrier_lower τ ell ε p.1 p.2 hτ hell hε.le hp.2.1).trans
    (sub_nonneg.mp hdiff)

end QuantitativePaper
