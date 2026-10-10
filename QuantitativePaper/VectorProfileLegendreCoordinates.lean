module
public import QuantitativePaper.VectorProfileInteriorSmooth
public import QuantitativePaper.VectorProfileInverseBounds
public import QuantitativePaper.VectorEnergyLegendre
public import FourPapersCommon.SmoothParameterInverse
public import FourPapersCommon.PartialGradientSmooth

@[expose] public section

/-! Genuine jointly smooth selected Legendre fields for the actual affine
profile family. The selector is the unique actual finite magnetization
preimage, and its regularity follows from the proved profile smoothness. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

abbrev VectorProfileParameter (n : ℕ):=ℝ×(Couplings n×ℝ)

def vectorProfileInverseScheme (s₀ s₁ : RSBScheme k) (q : Paper.Overlap) (θ : ℝ) :
    RSBScheme (k+1):=
  vectorProfileClampedScheme s₀ s₁ (projIcc (0 : ℝ) 1 zero_le_one θ,q)

def vectorProfileLegendreField (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (θ : ℝ) (p : Couplings n×ℝ) (m : Field n) : Field n:=
  vectorLegendreField (vectorProfileInverseScheme s₀ s₁ q θ) β t p j m

def vectorProfileJointPotential (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (z : VectorProfileParameter n×Field n) : ℝ:=
  vectorProfileTailRecursion s₀ s₁ β t q z.1.1 z.1.2 j z.2

def vectorProfileJointGradient (s₀ s₁ : RSBScheme k) (β t : ℝ) (q : Paper.Overlap)
    (j : ℕ) (z : VectorProfileParameter n×Field n) : Field n:=
  gradient (fun x=>vectorProfileJointPotential s₀ s₁ β t q j (z.1,x)) z.2

theorem vectorProfileJointPotential_eq_inverseScheme (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2) (θ : ℝ) (hθ : θ∈Icc (0 : ℝ) 1)
    (p : Couplings n×ℝ) :
    (fun x=>vectorProfileJointPotential s₀ s₁ β t q j ((θ,p),x))=
      vectorRecursion (vectorProfileInverseScheme s₀ s₁ q θ) β t p j := by
  change vectorProfileTailRecursion s₀ s₁ β t q θ p j=_
  rw [vectorProfileTailRecursion_eq_scheme s₀ s₁ β t q θ hθ p j,
    vectorTailRecursion_eq_clamped _ β t q q.property p hj]
  congr 2
  simp only [vectorProfileInverseScheme,vectorProfileClampedScheme,projIcc_of_mem zero_le_one hθ]

theorem vectorProfileJointGradient_eq_inverseScheme (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2) (θ : ℝ) (hθ : θ∈Icc (0 : ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    vectorProfileJointGradient s₀ s₁ β t q j ((θ,p),x)=
      vectorMagnetization (vectorProfileInverseScheme s₀ s₁ q θ) β t p j x := by
  unfold vectorProfileJointGradient
  rw [vectorProfileJointPotential_eq_inverseScheme s₀ s₁ β t q j hj θ hθ p]
  exact (vectorMagnetization_eq_gradient _ β t p j x).symm

theorem contDiffAt_vectorProfileJointPotential (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileJointPotential s₀ s₁ β t q j) z := by
  let L : (VectorProfileParameter n×Field n)→L[ℝ](ℝ×VectorParameter n):=
    ((ContinuousLinearMap.fst ℝ ℝ (Couplings n×ℝ)).comp
      (ContinuousLinearMap.fst ℝ (VectorProfileParameter n) (Field n))).prod
    (((ContinuousLinearMap.snd ℝ ℝ (Couplings n×ℝ)).comp
      (ContinuousLinearMap.fst ℝ (VectorProfileParameter n) (Field n))).prod
      (ContinuousLinearMap.snd ℝ (VectorProfileParameter n) (Field n)))
  exact (contDiffAt_vectorProfileTailRecursion_joint s₀ s₁ β t q ht q.property j hj
    (L z) hθ).comp z L.contDiff.contDiffAt

theorem contDiffAt_vectorProfileJointGradient (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileJointGradient s₀ s₁ β t q j) z :=
  contDiffAt_partial_gradient _ z (contDiffAt_vectorProfileJointPotential s₀ s₁ β t ht q j hj z hθ)

theorem vectorProfileJointGradient_legendreField (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2) (θ : ℝ) (hθ : θ∈Icc (0 : ℝ) 1)
    (p : Couplings n×ℝ) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    vectorProfileJointGradient s₀ s₁ β t q j
      ((θ,p),vectorProfileLegendreField s₀ s₁ β t q j θ p m)=m := by
  rw [vectorProfileJointGradient_eq_inverseScheme s₀ s₁ β t q j hj θ hθ]
  exact vectorMagnetization_legendreField _ β t p j m hm

theorem contDiffAt_vectorProfileLegendreField_joint (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (hj : j≤k+2)
    (a : VectorProfileParameter n) (hθ : a.1∈Ioo (0 : ℝ) 1)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileParameter n×Field n=>
      vectorProfileLegendreField s₀ s₁ β t q j z.1.1 z.1.2 z.2) (a,m) := by
  let F:=vectorProfileJointGradient (n := n) s₀ s₁ β t q j
  let Y : VectorProfileParameter n×Field n→Field n:=
    fun z=>vectorProfileLegendreField s₀ s₁ β t q j z.1.1 z.1.2 z.2
  let x:=Y (a,m)
  let S:=vectorProfileInverseScheme s₀ s₁ q a.1
  have hF : ContDiffAt ℝ ∞ F (a,x):=
    contDiffAt_vectorProfileJointGradient s₀ s₁ β t ht q j hj (a,x) hθ
  have hx:F (a,x)=m:=vectorProfileJointGradient_legendreField s₀ s₁ β t q j hj a.1
    ⟨hθ.1.le,hθ.2.le⟩ a.2 m hm
  have heq : (fun y=>F (a,y))=vectorMagnetization S β t a.2 j:=by
    funext y
    exact vectorProfileJointGradient_eq_inverseScheme s₀ s₁ β t q j hj a.1
      ⟨hθ.1.le,hθ.2.le⟩ a.2 y
  have hd : HasFDerivAt (fun y=>F (a,y))
      ((fderiv ℝ F (a,x)).comp (ContinuousLinearMap.inr ℝ (VectorProfileParameter n) (Field n))) x:=by
    convert hF.differentiableAt (by simp) |>.hasFDerivAt.comp x
      ((hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)) using 1 <;>
      first | rfl | (ext w; simp)
  rw [heq] at hd
  have hpartial : (fderiv ℝ F (a,x)).comp
      (ContinuousLinearMap.inr ℝ (VectorProfileParameter n) (Field n))=
      vectorFieldHessian S β t a.2 j x:=
    hd.unique (hasFDerivAt_vectorMagnetization S β t a.2 j x)
  have hInv : ((fderiv ℝ F (a,x)).comp
      (ContinuousLinearMap.inr ℝ (VectorProfileParameter n) (Field n))).IsInvertible:=by
    rw [hpartial,←vectorFieldHessianEquiv_coe S β t a.2 j x]
    exact ContinuousLinearMap.isInvertible_equiv
  have hθNear : ∀ᶠb : VectorProfileParameter n in 𝓝 a,b.1∈Ioo (0 : ℝ) 1:=
    (continuous_fst.tendsto a).eventually (isOpen_Ioo.mem_nhds hθ)
  have hinj : ∀ᶠb : VectorProfileParameter n in 𝓝 a,Function.Injective (fun y=>F (b,y)):=by
    filter_upwards [hθNear] with b hb
    have he : (fun y=>F (b,y))=vectorMagnetization
        (vectorProfileInverseScheme s₀ s₁ q b.1) β t b.2 j:=by
      funext y
      exact vectorProfileJointGradient_eq_inverseScheme s₀ s₁ β t q j hj b.1
        ⟨hb.1.le,hb.2.le⟩ b.2 y
    rw [he]
    exact vectorMagnetization_injective _ β t b.2 j
  have hY : ∀ᶠz : VectorProfileParameter n×Field n in 𝓝 (a,m),F (z.1,Y z)=z.2:=by
    have hnear := (continuous_fst.tendsto (a,m)).eventually hθNear
    have hmnear := (continuous_snd.tendsto (a,m)).eventually
      ((isOpen_vectorOpenSpinCube n).mem_nhds hm)
    filter_upwards [hnear,hmnear] with z hzθ hzm
    exact vectorProfileJointGradient_legendreField s₀ s₁ β t q j hj z.1.1
      ⟨hzθ.1.le,hzθ.2.le⟩ z.1.2 z.2 hzm
  exact contDiffAt_parameter_inverse F Y a m x hF hx hInv hinj hY

end QuantitativePaper
