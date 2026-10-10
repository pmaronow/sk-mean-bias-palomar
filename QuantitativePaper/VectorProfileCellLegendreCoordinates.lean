module
public import QuantitativePaper.VectorProfileCellSmooth
public import QuantitativePaper.VectorProfileCellPDE
public import QuantitativePaper.VectorProfileLegendreCoordinates

@[expose] public section

/-! Joint time/profile Legendre coordinates on every genuine strict cell. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

abbrev VectorProfileCellParameter (n : ℕ):=ℝ×VectorProfileParameter n

def vectorProfileCellOverlap (q : ℝ) : Paper.Overlap:=projIcc 0 1 zero_le_one q

def vectorProfileCellJointPotential (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : ℝ:=
  vectorProfilePhysicalCell s₀ s₁ β t i (z.1.1,z.1.2.1,z.1.2.2,z.2)

def vectorProfileCellJointGradient (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : Field n:=
  gradient (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (z.1,x)) z.2

def vectorProfileCellLegendreField (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorProfileCellParameter n×Field n) : Field n:=
  vectorProfileLegendreField s₀ s₁ β t (vectorProfileCellOverlap z.1.1) (k+2)
    z.1.2.1 z.1.2.2 z.2

theorem vectorProfileCellJointPotential_eq_scheme (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Icc (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Icc (0 : ℝ) 1) :
    (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x))=
      vectorRecursion (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1)
        β t a.2.2 (k+2) := by
  have hq01 : a.1∈Icc (0 : ℝ) 1:=⟨(s₀.q_nonneg (by omega)).trans hq.1,
    hq.2.trans (s₀.q_le_one (by omega))⟩
  rw [←vectorProfileJointPotential_eq_inverseScheme s₀ s₁ β t
    (vectorProfileCellOverlap a.1) (k+2) le_rfl a.2.1 hθ a.2.2]
  funext x
  change vectorProfilePhysicalCell s₀ s₁ β t i (a.1,a.2.1,a.2.2,x)=
    vectorProfileTailRecursion s₀ s₁ β t (vectorProfileCellOverlap a.1) a.2.1 a.2.2 (k+2) x
  simp only [vectorProfileCellOverlap,projIcc_of_mem zero_le_one hq01]
  exact vectorProfilePhysicalCell_eq_tail s₀ s₁ β t i hi a.1 a.2.1 hθ hq a.2.2 x

theorem vectorProfileCellJointGradient_eq_scheme (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1∈Icc (s₀.q i) (s₀.q (i+1))) (hθ : a.2.1∈Icc (0 : ℝ) 1) (x : Field n) :
    vectorProfileCellJointGradient s₀ s₁ β t i (a,x)=
      vectorMagnetization (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1)
        β t a.2.2 (k+2) x := by
  unfold vectorProfileCellJointGradient
  rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a hq hθ]
  exact (vectorMagnetization_eq_gradient _ β t a.2.2 (k+2) x).symm

theorem contDiffAt_vectorProfileCellJointPotential (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (z : VectorProfileCellParameter n×Field n) (hq : z.1.1<s₀.q (i+1))
    (hθ : z.1.2.1∈Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileCellJointPotential s₀ s₁ β t i) z := by
  have hc : 0<(1-t)*β^2:=mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hs:=contDiffAt_vectorProfileCellFunction s₀ s₁ β t ht.le ((1-t)*β^2)
    (s₀.q (i+1)) hc i (k+1-i) hi (z.1.1,z.1.2.1,z.1.2.2,z.2) hq hθ
  have hL : ContDiffAt ℝ ∞ (fun w : VectorProfileCellParameter n×Field n=>
      (w.1.1,w.1.2.1,w.1.2.2,w.2)) z:=by fun_prop
  exact ContDiffAt.comp (f := fun w : VectorProfileCellParameter n×Field n=>
      (w.1.1,w.1.2.1,w.1.2.2,w.2))
    (g := vectorProfileCellFunction s₀ s₁ β t ((1-t)*β^2) (s₀.q (i+1)) i (k+1-i)) z hs hL

theorem contDiffAt_vectorProfileCellJointGradient (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (z : VectorProfileCellParameter n×Field n) (hq : z.1.1<s₀.q (i+1))
    (hθ : z.1.2.1∈Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileCellJointGradient s₀ s₁ β t i) z :=
  contDiffAt_partial_gradient _ z
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi z hq hθ)

theorem contDiffAt_vectorProfileCellLegendreField (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β ≠ 0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (vectorProfileCellLegendreField s₀ s₁ β t i) (a,m) := by
  let F:=vectorProfileCellJointGradient (n:=n) s₀ s₁ β t i
  let Y:=vectorProfileCellLegendreField (n:=n) s₀ s₁ β t i
  let x:=Y (a,m)
  let S:=vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap a.1) a.2.1
  have he : (fun y=>F (a,y))=vectorMagnetization S β t a.2.2 (k+2):=by
    funext y
    exact vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi a
      ⟨hq.1.le,hq.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ y
  have hx : F (a,x)=m:=by
    exact (congrFun he x).trans (vectorMagnetization_legendreField S β t a.2.2 (k+2) m hm)
  have hF : ContDiffAt ℝ ∞ F (a,x):=
    contDiffAt_vectorProfileCellJointGradient s₀ s₁ β t hβ ht i hi (a,x) hq.2 hθ
  have hd : HasFDerivAt (fun y=>F (a,y))
      ((fderiv ℝ F (a,x)).comp (ContinuousLinearMap.inr ℝ (VectorProfileCellParameter n) (Field n))) x:=by
    convert hF.differentiableAt (by simp) |>.hasFDerivAt.comp x
      ((hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)) using 1 <;>
      first | rfl | (ext w; simp)
  rw [he] at hd
  have hpartial : (fderiv ℝ F (a,x)).comp
      (ContinuousLinearMap.inr ℝ (VectorProfileCellParameter n) (Field n))=
      vectorFieldHessian S β t a.2.2 (k+2) x:=
    hd.unique (hasFDerivAt_vectorMagnetization S β t a.2.2 (k+2) x)
  have hInv : ((fderiv ℝ F (a,x)).comp
      (ContinuousLinearMap.inr ℝ (VectorProfileCellParameter n) (Field n))).IsInvertible:=by
    rw [hpartial,←vectorFieldHessianEquiv_coe S β t a.2.2 (k+2) x]
    exact ContinuousLinearMap.isInvertible_equiv
  have hqNear : ∀ᶠ b : VectorProfileCellParameter n in 𝓝 a,
      b.1∈Ioo (s₀.q i) (s₀.q (i+1)):=
    (continuous_fst.tendsto a).eventually (isOpen_Ioo.mem_nhds hq)
  have hθNear : ∀ᶠ b : VectorProfileCellParameter n in 𝓝 a,b.2.1∈Ioo (0 : ℝ) 1:=
    ((continuous_fst.comp continuous_snd).tendsto a).eventually (isOpen_Ioo.mem_nhds hθ)
  have hinj : ∀ᶠ b : VectorProfileCellParameter n in 𝓝 a,Function.Injective (fun y=>F (b,y)):=by
    filter_upwards [hqNear,hθNear] with b hbq hbθ
    have he' : (fun y=>F (b,y))=vectorMagnetization
        (vectorProfileInverseScheme s₀ s₁ (vectorProfileCellOverlap b.1) b.2.1) β t b.2.2 (k+2):=by
      funext y
      exact vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi b
        ⟨hbq.1.le,hbq.2.le⟩ ⟨hbθ.1.le,hbθ.2.le⟩ y
    rw [he']
    exact vectorMagnetization_injective _ β t b.2.2 (k+2)
  have hY : ∀ᶠ z : VectorProfileCellParameter n×Field n in 𝓝 (a,m),F (z.1,Y z)=z.2:=by
    have hq' := (continuous_fst.tendsto (a,m)).eventually hqNear
    have hθ' := (continuous_fst.tendsto (a,m)).eventually hθNear
    have hm' := (continuous_snd.tendsto (a,m)).eventually
      ((isOpen_vectorOpenSpinCube n).mem_nhds hm)
    filter_upwards [hq',hθ',hm'] with z hzq hzθ hzm
    change vectorProfileCellJointGradient s₀ s₁ β t i (z.1,Y z)=z.2
    rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t i hi z.1
      ⟨hzq.1.le,hzq.2.le⟩ ⟨hzθ.1.le,hzθ.2.le⟩]
    exact vectorMagnetization_legendreField _ β t z.1.2.2 (k+2) z.2 hzm
  exact contDiffAt_parameter_inverse F Y a m x hF hx hInv hinj hY

end QuantitativePaper
