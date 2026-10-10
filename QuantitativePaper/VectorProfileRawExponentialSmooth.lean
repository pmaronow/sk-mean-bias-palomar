module
public import QuantitativePaper.VectorProfileCellJetBounds
public import QuantitativePaper.VectorProfileTimePullbacks
public import FourPapersCommon.ExponentialPartialJets
public import FourPapersCommon.ExponentialLinearChange

@[expose] public section

/-! Actual raw affine-profile jets, including all chosen parameter and
spatial derivatives, have exponential growth on every cropped strict cell. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileJointCylinder (l u a b : ℝ) : Set (VectorProfileCellParameter n×Field n):=
  {z|z.1.1∈Ioo l u ∧ z.1.2.1∈Ioo a b}

theorem isOpen_vectorProfileJointCylinder (l u a b : ℝ) :
    IsOpen (vectorProfileJointCylinder (n:=n) l u a b) :=
  (isOpen_Ioo.preimage (continuous_fst.comp continuous_fst)).inter
    (isOpen_Ioo.preimage ((continuous_fst.comp continuous_snd).comp continuous_fst))

def vectorProfileJointReassociation :
    (VectorProfileCellParameter n×Field n)→L[ℝ](ℝ×(ℝ×VectorParameter n)) :=
  let A:=ContinuousLinearMap.fst ℝ (VectorProfileCellParameter n) (Field n)
  let X:=ContinuousLinearMap.snd ℝ (VectorProfileCellParameter n) (Field n)
  let Q:=(ContinuousLinearMap.fst ℝ ℝ (VectorProfileParameter n)).comp A
  let P:=(ContinuousLinearMap.snd ℝ ℝ (VectorProfileParameter n)).comp A
  let Theta:=(ContinuousLinearMap.fst ℝ ℝ (Couplings n×ℝ)).comp P
  let Disorder:=(ContinuousLinearMap.snd ℝ ℝ (Couplings n×ℝ)).comp P
  Q.prod (Theta.prod (Disorder.prod X))

theorem exponentialSmoothOn_vectorProfileCellJointPotential
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (vectorProfileCellJointPotential (n:=n) s₀ s₁ β t i)
      (vectorProfileJointCylinder l u a b) := by
  let c:=(1-t)*β^2
  let Q:=s₀.q (i+1)
  let U:=vectorProfileCellCylinder (n:=n) l u a b
  let f:=vectorProfileCellFunction (n:=n) s₀ s₁ β t c Q i (k+1-i)
  have hc : 0<c:=mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hf : ExponentialSmoothOn f U:=by
    refine ⟨fun w hw=>?_,fun r=>?_⟩
    · exact contDiffAt_vectorProfileCellFunction s₀ s₁ β t ht.le c Q hc i (k+1-i) hi w
        (hw.1.2.trans hu) ⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
    · obtain ⟨C,R,hC,hR,hj⟩:=exists_vectorProfileCellFunction_common_exp_jets
        (n:=n) s₀ s₁ β t ht.le c Q l u a b hc hu ha hb r i (k+1-i) hi
      exact ⟨C,R,zero_le_one.trans hC,hR,hj r le_rfl⟩
  have hmap : MapsTo (vectorProfileJointReassociation (n:=n))
      (vectorProfileJointCylinder l u a b) U:=fun _ hz=>hz
  exact hf.precompCLM vectorProfileJointReassociation hmap

end QuantitativePaper
