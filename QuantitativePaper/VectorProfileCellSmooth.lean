module
public import QuantitativePaper.VectorProfileCellRepresentation
public import QuantitativePaper.VectorProfileKernelEnvelopes
public import QuantitativePaper.VariableGaussianAverageSmooth
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! Genuine joint overlap/profile/disorder/field C∞ on every strict
finite Cole--Hopf cell. Zero-mass cells are actual Gaussian averages. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileCellCylinder (l u a b : ℝ) : Set (ℝ×(ℝ×VectorParameter n)):=
  {w|w.1∈Ioo l u ∧ w.2.1∈Ioo a b}

theorem isOpen_vectorProfileCellCylinder (l u a b : ℝ) :
    IsOpen (vectorProfileCellCylinder (n:=n) l u a b) :=
  (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_Ioo.preimage (continuous_fst.comp continuous_snd))

theorem vectorProfileCellGaussian_contDiffOn (N : ℕ) (f : ℝ×VectorParameter n→ℝ)
    (c Q l u a b : ℝ) (hc : 0<c) (hu : u<Q)
    (hf : ∀ y : ℝ×VectorParameter n,y.1∈Ioo a b → ContDiffAt ℝ ∞ f y)
    (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hjets : ∀ r,r ≤ N→∀ y : ℝ×VectorParameter n,y.1∈Ioo a b→
      ‖iteratedFDeriv ℝ r f y‖ ≤ K*Real.exp (D*‖y‖)) :
    ContDiffOn ℝ N (fun w : ℝ×(ℝ×VectorParameter n)=>
      ∫ z,f (vectorProfileCellEvaluation c Q z w) ∂fieldGaussian n)
      (vectorProfileCellCylinder l u a b) := by
  let U : Set (ℝ×VectorParameter n):={y|y.1∈Ioo a b}
  have hU : IsOpen U:=isOpen_Ioo.preimage continuous_fst
  have hv : Icc l u⊆Iio Q:=fun r hr=>hr.2.trans_lt hu
  have hLam : ∀ r∈Iio Q,ContDiffAt ℝ ∞ (fun q=>Real.sqrt (c*(Q-q))) r:=by
    intro r hr
    have hbase : ContDiffAt ℝ ∞ (fun q : ℝ=>c*(Q-q)) r:=by fun_prop
    exact hbase.sqrt (mul_pos hc (sub_pos.mpr hr)).ne'
  change ContDiffOn ℝ N (fun w : ℝ×(ℝ×VectorParameter n)=>
    ∫ z,f (variableGaussianEvaluation (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n))
      (vectorProfileJointShift n 1) (fun r=>Real.sqrt (c*(Q-r))) z w) ∂fieldGaussian n) _
  apply variableGaussianAverage_contDiffOn N f U hU hf
    (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n)) (vectorProfileJointShift n 1)
    (fun r=>Real.sqrt (c*(Q-r))) (Iio Q) isOpen_Iio hLam
    (vectorProfileCellCylinder l u a b) (isOpen_vectorProfileCellCylinder l u a b) l u hv
    (fun w hw=>⟨hw.1.1.le,hw.1.2.le⟩) ?_ K D hK hD hjets
  intro w hw z
  change (vectorProfileCellEvaluation c Q z w).1∈Ioo a b
  rw [vectorProfileCellEvaluation_eq]
  exact hw.2

theorem vectorProfileCellPartition_pos (s₀ s₁ : RSBScheme k) (β t c Q : ℝ) (i j : ℕ)
    (w : ℝ×(ℝ×VectorParameter n)) (hθ : w.2.1∈Icc (0 : ℝ) 1) :
    0<∫ z,Real.exp (vectorProfileCellExponent s₀ s₁ β t i j
      (vectorProfileCellEvaluation c Q z w)) ∂fieldGaussian n := by
  have hh:=vectorStepPartition_pos (vectorProfileRecursion s₀ s₁ β t w.2.1 w.2.2.1 j)
    (Real.sqrt (n:ℝ)).toNNReal (vectorProfileRecursion_lipschitz s₀ s₁ β t w.2.1 hθ w.2.2.1 j)
    (c*(Q-w.1)) (vectorProfileMass s₀ s₁ w.2.1 i) w.2.2.2
  simp_rw [vectorProfileCellEvaluation_eq]
  exact hh

theorem contDiffOn_vectorProfileCellFunction (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t ≤ 1)
    (c Q : ℝ) (hc : 0<c) (i j N : ℕ) (hi : i ≤ k+1)
    (l u a b : ℝ) (hu : u<Q) (ha : 0<a) (hb : b<1) :
    ContDiffOn ℝ N (vectorProfileCellFunction (n:=n) s₀ s₁ β t c Q i j)
      (vectorProfileCellCylinder l u a b) := by
  let W:=vectorProfileCellCylinder (n:=n) l u a b
  have hθ (w : ℝ×(ℝ×VectorParameter n)) (hw : w∈W) : w.2.1∈Ioo (0 : ℝ) 1:=
    ⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  rcases vectorProfileMass_zero_or_pos s₀ s₁ i hi with hm0|hmpos
  · obtain ⟨K,D,hK,hD,hj⟩:=exists_vectorProfileJointFunction_common_exp_jets
      (n:=n) s₀ s₁ β t ht N j a b ha hb
    have hAvg:=vectorProfileCellGaussian_contDiffOn N (vectorProfileJointFunction (n:=n) s₀ s₁ β t j)
      c Q l u a b hc hu (fun y hy=>contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht j y
        ⟨ha.trans hy.1,hy.2.trans hb⟩) K D (zero_le_one.trans hK) hD hj
    apply hAvg.congr
    intro w hw
    rw [vectorProfileCellFunction_eq_average_partition,if_pos (hm0 w.2.1)]
  · obtain ⟨K,D,hK,hD,hj⟩:=exists_vectorProfileCellExponent_exp_jets
      (n:=n) s₀ s₁ β t ht N i j hi a b ha hb
    have hPart:=vectorProfileCellGaussian_contDiffOn N
      (fun y : ℝ×VectorParameter n=>Real.exp (vectorProfileCellExponent s₀ s₁ β t i j y))
      c Q l u a b hc hu (fun y hy=>(contDiffAt_vectorProfileCellExponent s₀ s₁ β t ht i j y
        ⟨ha.trans hy.1,hy.2.trans hb⟩).exp) K D hK hD hj
    have hLog:=hPart.log (fun w hw=>(vectorProfileCellPartition_pos s₀ s₁ β t c Q i j w
      ⟨(hθ w hw).1.le,(hθ w hw).2.le⟩).ne')
    have hMass : ContDiffOn ℝ N (fun w : ℝ×(ℝ×VectorParameter n)=>
      vectorProfileMass s₀ s₁ w.2.1 i) W:=by
      have hm : ContDiff ℝ N (fun w : ℝ×(ℝ×VectorParameter n)=>
        vectorProfileMass s₀ s₁ w.2.1 i):=by unfold vectorProfileMass; fun_prop
      exact hm.contDiffOn
    have hInv:=hMass.inv (fun w hw=>(hmpos w.2.1 (hθ w hw)).ne')
    apply (hInv.mul hLog).congr
    intro w hw
    rw [vectorProfileCellFunction_eq_average_partition,if_neg (hmpos w.2.1 (hθ w hw)).ne']
    rfl

theorem contDiffAt_vectorProfileCellFunction (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t ≤ 1)
    (c Q : ℝ) (hc : 0<c) (i j : ℕ) (hi : i ≤ k+1)
    (w : ℝ×(ℝ×VectorParameter n)) (hq : w.1<Q) (hθ : w.2.1∈Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileCellFunction s₀ s₁ β t c Q i j) w := by
  apply contDiffAt_infty.mpr
  intro N
  let l:=w.1-1
  let u:=(w.1+Q)/2
  let a:=w.2.1/2
  let b:=(w.2.1+1)/2
  have hw : w∈vectorProfileCellCylinder l u a b:=by
    dsimp only [vectorProfileCellCylinder,l,u,a,b]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith [hθ.1],by linarith [hθ.2]⟩⟩
  have hh:=contDiffOn_vectorProfileCellFunction (n:=n) s₀ s₁ β t ht c Q hc i j N hi l u a b
    (by dsimp only [u]; linarith) (by dsimp only [a]; linarith [hθ.1])
    (by dsimp only [b]; linarith [hθ.2])
  exact (hh w hw).contDiffAt ((isOpen_vectorProfileCellCylinder l u a b).mem_nhds hw)

end QuantitativePaper
