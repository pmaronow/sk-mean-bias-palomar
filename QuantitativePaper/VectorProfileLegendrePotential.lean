module
public import QuantitativePaper.VectorProfileLegendreCoordinates
public import FourPapersCommon.StationaryEnvelope

@[expose] public section

/-! The actual affine-profile Legendre potential, jointly smooth in the
interior profile parameter, all disorder coordinates and magnetization.
Its parameter derivative is the genuine stationary envelope derivative. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileLegendrePotential (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n) : ℝ:=
  vectorLegendrePotential (vectorProfileInverseScheme s₀ s₁ q θ) β t p j m

def vectorProfileEnergyLegendrePotential (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n) : ℝ:=
  vectorProfileLegendrePotential s₀ s₁ β t q j θ p m/β

theorem vectorProfileLegendrePotential_eq_stationaryValue (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2) (θ : ℝ)
    (hθ : θ∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) (m : Field n) :
    vectorProfileLegendrePotential s₀ s₁ β t q j θ p m=
      inner ℝ m (vectorProfileLegendreField s₀ s₁ β t q j θ p m)-
        vectorProfileJointPotential s₀ s₁ β t q j
          ((θ,p),vectorProfileLegendreField s₀ s₁ β t q j θ p m) := by
  have he:=congrFun (vectorProfileJointPotential_eq_inverseScheme s₀ s₁ β t q j hj θ hθ p)
    (vectorProfileLegendreField s₀ s₁ β t q j θ p m)
  rw [he]
  rfl

theorem contDiffAt_vectorProfileLegendrePotential_joint (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (a : VectorProfileParameter n) (hθ : a.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileParameter n×Field n=>
      vectorProfileLegendrePotential s₀ s₁ β t q j z.1.1 z.1.2 z.2) (a,m) := by
  let Y : VectorProfileParameter n×Field n→Field n:=
    fun z=>vectorProfileLegendreField s₀ s₁ β t q j z.1.1 z.1.2 z.2
  have hY : ContDiffAt ℝ ∞ Y (a,m):=
    contDiffAt_vectorProfileLegendreField_joint s₀ s₁ β t ht q j hj a hθ m hm
  have hU : ContDiffAt ℝ ∞ (vectorProfileJointPotential s₀ s₁ β t q j) (a,Y (a,m)):=
    contDiffAt_vectorProfileJointPotential s₀ s₁ β t ht q j hj (a,Y (a,m)) hθ
  have hPair : ContDiffAt ℝ ∞ (fun z : VectorProfileParameter n×Field n=>(z.1,Y z)) (a,m):=
    contDiff_fst.contDiffAt.prodMk hY
  have hRaw : ContDiffAt ℝ ∞ (fun z : VectorProfileParameter n×Field n=>
      inner ℝ z.2 (Y z)-vectorProfileJointPotential s₀ s₁ β t q j (z.1,Y z)) (a,m):=
    (contDiff_snd.contDiffAt.inner ℝ hY).sub (ContDiffAt.comp (f := fun z : VectorProfileParameter n×Field n=>(z.1,Y z))
      (g := vectorProfileJointPotential s₀ s₁ β t q j) (a,m) hU hPair)
  apply hRaw.congr_of_eventuallyEq
  have hn:=((continuous_fst.comp continuous_fst).tendsto (a,m)).eventually
    (isOpen_Ioo.mem_nhds hθ)
  filter_upwards [hn] with z hz
  exact vectorProfileLegendrePotential_eq_stationaryValue s₀ s₁ β t q j hj z.1.1
    ⟨hz.1.le,hz.2.le⟩ z.1.2 z.2

theorem contDiffAt_vectorProfileEnergyLegendrePotential_joint (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (a : VectorProfileParameter n) (hθ : a.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileParameter n×Field n=>
      vectorProfileEnergyLegendrePotential s₀ s₁ β t q j z.1.1 z.1.2 z.2) (a,m):=
  (contDiffAt_vectorProfileLegendrePotential_joint s₀ s₁ β t ht q j hj a hθ m hm).div_const β

theorem hasFDerivAt_vectorProfileLegendrePotential_parameter (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (a : VectorProfileParameter n) (hθ : a.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    HasFDerivAt (fun b : VectorProfileParameter n=>
      vectorProfileLegendrePotential s₀ s₁ β t q j b.1 b.2 m)
      (-((fderiv ℝ (vectorProfileJointPotential s₀ s₁ β t q j)
        (a,vectorProfileLegendreField s₀ s₁ β t q j a.1 a.2 m)).comp
          (ContinuousLinearMap.inl ℝ (VectorProfileParameter n) (Field n)))) a := by
  let U:=vectorProfileJointPotential (n := n) s₀ s₁ β t q j
  let Y : VectorProfileParameter n→Field n:=
    fun b=>vectorProfileLegendreField s₀ s₁ β t q j b.1 b.2 m
  have hU:=contDiffAt_vectorProfileJointPotential s₀ s₁ β t ht q j hj (a,Y a) hθ
  have hPair : ContDiffAt ℝ ∞ (fun b : VectorProfileParameter n=>(b,m)) a:=
    contDiffAt_id.prodMk contDiffAt_const
  have hYfull : ContDiffAt ℝ ∞ (fun z : VectorProfileParameter n×Field n=>
      vectorProfileLegendreField s₀ s₁ β t q j z.1.1 z.1.2 z.2) (a,m):=
    contDiffAt_vectorProfileLegendreField_joint s₀ s₁ β t ht q j hj a hθ m hm
  have hY : ContDiffAt ℝ ∞ Y a:=
    ContDiffAt.comp (f := fun b : VectorProfileParameter n=>(b,m))
      (g := fun z : VectorProfileParameter n×Field n=>
        vectorProfileLegendreField s₀ s₁ β t q j z.1.1 z.1.2 z.2) a hYfull hPair
  have hd : HasFDerivAt (fun y=>U (a,y))
      ((fderiv ℝ U (a,Y a)).comp (ContinuousLinearMap.inr ℝ (VectorProfileParameter n) (Field n)))
      (Y a):=by
    convert hU.differentiableAt (by simp) |>.hasFDerivAt.comp (Y a)
      ((hasFDerivAt_const a (Y a)).prodMk (hasFDerivAt_id (Y a))) using 1 <;>
      first | rfl | (ext w; simp)
  have hstationary : ∀w : Field n,(fderiv ℝ U (a,Y a)) (0,w)=inner ℝ m w:=by
    intro w
    have he:=congrArg (fun L : Field n→L[ℝ]ℝ=>L w) hd.fderiv
    change fderiv ℝ (fun y=>U (a,y)) (Y a) w=(fderiv ℝ U (a,Y a)) (0,w) at he
    rw [←he,←inner_gradient_left]
    change inner ℝ (vectorProfileJointGradient s₀ s₁ β t q j (a,Y a)) w=_
    rw [vectorProfileJointGradient_legendreField s₀ s₁ β t q j hj a.1
      ⟨hθ.1.le,hθ.2.le⟩ a.2 m hm]
  have hEnv:=hasFDerivAt_stationaryLegendre_value U Y a m (fderiv ℝ U (a,Y a))
    (fderiv ℝ Y a) (hU.differentiableAt (by simp)).hasFDerivAt
    (hY.differentiableAt (by simp)).hasFDerivAt hstationary
  apply hEnv.congr_of_eventuallyEq
  have hn:=(continuous_fst.tendsto a).eventually (isOpen_Ioo.mem_nhds hθ)
  filter_upwards [hn] with b hb
  exact vectorProfileLegendrePotential_eq_stationaryValue s₀ s₁ β t q j hj b.1
    ⟨hb.1.le,hb.2.le⟩ b.2 m

end QuantitativePaper
