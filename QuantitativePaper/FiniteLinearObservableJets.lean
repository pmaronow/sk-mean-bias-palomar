module
public import QuantitativePaper.BoundedJets
public import QuantitativePaper.FiniteSoftmaxJets
public import QuantitativePaper.VectorConditionalMean
public import FourPapersCommon.AffineLineDerivatives

@[expose] public section

/-! Every observable of a genuine finite linear Gibbs family is globally
smooth with bounded jets of every order. The proof differentiates the actual
log partition after adding its terminal-spin offset coordinate. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [Nonempty ι]
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem boundedPositiveJets_finiteLinearSoftmax (l : ι→E→L[ℝ]ℝ) :
    BoundedPositiveJets (finiteLinearSoftmax l) := by
  refine ⟨?_,fun j hj=>?_⟩
  · exact (ContDiff.sum (fun i _=>(l i).contDiff.exp)).log
      (fun x=>(finiteLinearPartition_pos l x).ne')
  · let B:ℝ:=(j.factorial:ℝ)*logJetCoefficient j*(finitePartitionPowerBound l j)^j
    refine ⟨max 0 B,le_max_left _ _,fun x=>?_⟩
    exact (norm_iteratedFDeriv_finiteLinearSoftmax_le l j j hj le_rfl x).trans
      (le_max_right _ _)

variable {n : ℕ}

def finiteLinearObservable (l : Configuration n→E→L[ℝ]ℝ) (b : Configuration n→ℝ) (x:E) : ℝ:=
  terminalMean (fun i=>l i x) b

def finiteLinearOffset (l : Configuration n→E→L[ℝ]ℝ) (b : Configuration n→ℝ) (i:Configuration n) :
    ℝ×E→L[ℝ]ℝ:=
  (b i) • ContinuousLinearMap.fst ℝ ℝ E+
    (l i).comp (ContinuousLinearMap.snd ℝ ℝ E)

theorem finiteLinearObservable_eq_directional (l : Configuration n→E→L[ℝ]ℝ) (b : Configuration n→ℝ) (x:E) :
    finiteLinearObservable l b x=
      fderiv ℝ (finiteLinearSoftmax (finiteLinearOffset l b)) (0,x) (1,0) := by
  let f:=finiteLinearSoftmax (finiteLinearOffset l b)
  have hf:ContDiff ℝ 1 f:=(boundedPositiveJets_finiteLinearSoftmax (finiteLinearOffset l b)).1.of_le (by simp)
  have hd:=FourPapersCommon.hasDerivAt_affine_line f (hf.differentiable (by norm_num)) (0,x) (1,0) 0
  have he : (fun r:ℝ=>f ((0,x)+r • (1,0)))=
      (fun r=>terminalPotential (terminalTilt (fun i=>l i x) b r)):=by
    funext r
    unfold f finiteLinearSoftmax finiteLinearPartition terminalPotential terminalPartition
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [finiteLinearOffset,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
      zero_add,mul_one,smul_zero,add_zero,terminalTilt]
    ring
  rw [he] at hd
  have hh:=hd.unique (hasDerivAt_terminalPotential_tilt (fun i=>l i x) b 0)
  have hzero : terminalTilt (fun i=>l i x) b 0=(fun i=>l i x):=by
    funext i
    simp [terminalTilt]
  rw [hzero] at hh
  simpa only [zero_smul,add_zero,finiteLinearObservable,f] using hh.symm

theorem boundedJets_finiteLinearObservable (l : Configuration n→E→L[ℝ]ℝ) (b : Configuration n→ℝ) :
    BoundedJets (finiteLinearObservable l b) := by
  let f:=finiteLinearSoftmax (finiteLinearOffset l b)
  have hf:=boundedPositiveJets_finiteLinearSoftmax (finiteLinearOffset l b)
  have hg:BoundedJets (fun z:ℝ×E=>fderiv ℝ f z (1,0)):=hf.boundedJets_fderiv_apply (1,0)
  have hp:=hg.comp_linear (ContinuousLinearMap.inr ℝ ℝ E)
  have he : finiteLinearObservable l b=
      (fun z:ℝ×E=>fderiv ℝ f z (1,0)) ∘ ContinuousLinearMap.inr ℝ ℝ E:=by
    funext x
    exact finiteLinearObservable_eq_directional l b x
  rw [he]
  exact hp

end QuantitativePaper
