module
public import QuantitativePaper.VectorProfileCellLegendreCoordinates
public import QuantitativePaper.VectorProfileLegendrePotential

@[expose] public section

/-! Actual Legendre values jointly smooth on strict cells, with genuine
stationary time/profile differentiation. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileCellLegendrePotential (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  vectorProfileLegendrePotential s₀ s₁ β t (vectorProfileCellOverlap z.1.1) (k+2)
    z.1.2.1 z.1.2.2 z.2

def vectorProfileCellEnergyLegendrePotential (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  vectorProfileCellLegendrePotential s₀ s₁ β t i z/β

theorem vectorProfileCellLegendrePotential_eq_stationaryValue (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Icc (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Icc (0 : ℝ) 1)
    (m : Field n) :
    vectorProfileCellLegendrePotential s₀ s₁ β t i (a,m)=
      inner ℝ m (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))-
        vectorProfileCellJointPotential s₀ s₁ β t i
          (a,vectorProfileCellLegendreField s₀ s₁ β t i (a,m)) := by
  have he:=congrFun (vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a hq hθ)
    (vectorProfileCellLegendreField s₀ s₁ β t i (a,m))
  rw [he]
  rfl

theorem contDiffAt_vectorProfileCellLegendrePotential (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (vectorProfileCellLegendrePotential s₀ s₁ β t i) (a,m) := by
  let Y:=vectorProfileCellLegendreField (n:=n) s₀ s₁ β t i
  let U:=vectorProfileCellJointPotential (n:=n) s₀ s₁ β t i
  have hY : ContDiffAt ℝ ∞ Y (a,m):=
    contDiffAt_vectorProfileCellLegendreField s₀ s₁ β t hβ ht i hi a hq hθ m hm
  have hU : ContDiffAt ℝ ∞ U (a,Y (a,m)):=
    contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,Y (a,m)) hq.2 hθ
  have hPair : ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>(z.1,Y z)) (a,m):=
    contDiff_fst.contDiffAt.prodMk hY
  have hRaw : ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      inner ℝ z.2 (Y z)-U (z.1,Y z)) (a,m):=
    (contDiff_snd.contDiffAt.inner ℝ hY).sub (ContDiffAt.comp
      (f := fun z : VectorProfileCellParameter n×Field n=>(z.1,Y z)) (g := U) (a,m) hU hPair)
  apply hRaw.congr_of_eventuallyEq
  have hqNear := ((continuous_fst.comp continuous_fst).tendsto (a,m)).eventually
    (isOpen_Ioo.mem_nhds hq)
  have hθNear := ((continuous_fst.comp (continuous_snd.comp continuous_fst)).tendsto (a,m)).eventually
    (isOpen_Ioo.mem_nhds hθ)
  filter_upwards [hqNear,hθNear] with z hzq hzθ
  exact vectorProfileCellLegendrePotential_eq_stationaryValue s₀ s₁ β t i hi z.1
    ⟨hzq.1.le,hzq.2.le⟩ ⟨hzθ.1.le,hzθ.2.le⟩ z.2

theorem contDiffAt_vectorProfileCellEnergyLegendrePotential (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (vectorProfileCellEnergyLegendrePotential s₀ s₁ β t i) (a,m) :=
  (contDiffAt_vectorProfileCellLegendrePotential s₀ s₁ β t hβ ht i hi a hq hθ m hm).div_const β

theorem hasFDerivAt_vectorProfileCellLegendrePotential_parameter (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasFDerivAt (fun b : VectorProfileCellParameter n=>
      vectorProfileCellLegendrePotential s₀ s₁ β t i (b,m))
      (-((fderiv ℝ (vectorProfileCellJointPotential s₀ s₁ β t i)
        (a,vectorProfileCellLegendreField s₀ s₁ β t i (a,m))).comp
          (ContinuousLinearMap.inl ℝ (VectorProfileCellParameter n) (Field n)))) a := by
  let U:=vectorProfileCellJointPotential (n:=n) s₀ s₁ β t i
  let Y : VectorProfileCellParameter n→Field n:=fun b=>vectorProfileCellLegendreField s₀ s₁ β t i (b,m)
  have hU:=contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi (a,Y a) hq.2 hθ
  have hY : ContDiffAt ℝ ∞ Y a:=ContDiffAt.comp
    (f := fun b : VectorProfileCellParameter n=>(b,m))
    (g := vectorProfileCellLegendreField s₀ s₁ β t i) a
    (contDiffAt_vectorProfileCellLegendreField s₀ s₁ β t hβ ht i hi a hq hθ m hm) (by fun_prop)
  have hd : HasFDerivAt (fun y=>U (a,y))
      ((fderiv ℝ U (a,Y a)).comp (ContinuousLinearMap.inr ℝ (VectorProfileCellParameter n) (Field n)))
      (Y a):=by
    convert hU.differentiableAt (by simp) |>.hasFDerivAt.comp (Y a)
      ((hasFDerivAt_const a (Y a)).prodMk (hasFDerivAt_id (Y a))) using 1 <;>
      first | rfl | (ext w; simp)
  have hstationary : ∀ w : Field n,(fderiv ℝ U (a,Y a)) (0,w)=inner ℝ m w:=by
    intro w
    have he:=congrArg (fun L : Field n→L[ℝ]ℝ=>L w) hd.fderiv
    change fderiv ℝ (fun y=>U (a,y)) (Y a) w=(fderiv ℝ U (a,Y a)) (0,w) at he
    rw [←he,←inner_gradient_left]
    change inner ℝ (vectorProfileCellJointGradient s₀ s₁ β t i (a,Y a)) w=_
    rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩]
    have hx : vectorMagnetization
        (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1)
        β t a.2.2 (k+2) (Y a)=m:=
      vectorMagnetization_legendreField
        (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1)
        β t a.2.2 (k+2) m hm
    rw [hx]
  have hEnv:=hasFDerivAt_stationaryLegendre_value U Y a m (fderiv ℝ U (a,Y a))
    (fderiv ℝ Y a) (hU.differentiableAt (by simp)).hasFDerivAt
    (hY.differentiableAt (by simp)).hasFDerivAt hstationary
  apply hEnv.congr_of_eventuallyEq
  have hqNear := (continuous_fst.tendsto a).eventually (isOpen_Ioo.mem_nhds hq)
  have hθNear := ((continuous_fst.comp continuous_snd).tendsto a).eventually (isOpen_Ioo.mem_nhds hθ)
  filter_upwards [hqNear,hθNear] with b hbq hbθ
  exact vectorProfileCellLegendrePotential_eq_stationaryValue s₀ s₁ β t i hi b
    ⟨hbq.1.le,hbq.2.le⟩ ⟨hbθ.1.le,hbθ.2.le⟩ m

end QuantitativePaper
