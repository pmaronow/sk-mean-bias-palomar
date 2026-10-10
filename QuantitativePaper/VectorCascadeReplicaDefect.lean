module
public import QuantitativePaper.VectorInterpolationPrefixExpectation
public import QuantitativePaper.VectorConditionalReplicaMoments
public import FourPapersCommon.FiniteStateCascadePairs

@[expose] public section

/-! Actual split-replica defect expectations at the genuine finite vector
diffusion nodes, including the grid-measure conditional law identification. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators Topology
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorRootCascadePairDefect (s : RSBScheme k) (β t a : ℝ) (p : ℕ)
    (q : Paper.Overlap) (H : FiniteStateField (Configuration n)) : ℝ :=
  ∫z,(overlap n z.1 z.2-(q:ℝ))^2∂
    (finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
      (vectorRootInterpolationScaledDirection (n:=n) s β t) p H).prod
    (finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
      (vectorRootInterpolationScaledDirection (n:=n) s β t) p H)

theorem measurable_vectorRootCascadePairDefect (s : RSBScheme k) (β t a : ℝ)
    (ha : 0 ≤ a) (p : ℕ) (q : Paper.Overlap) : Measurable (vectorRootCascadePairDefect (n:=n) s β t a p q) := by
  let K:=finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
    (vectorRootInterpolationScaledDirection (n:=n) s β t) p
  haveI:=isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha)
    (vectorRootInterpolationScaledDirection (n:=n) s β t) p
  have hd : Measurable (fun z : Configuration n×Configuration n=>(overlap n z.1 z.2-(q:ℝ))^2):=
    measurable_of_finite _
  change Measurable (fun H => ∫z,(overlap n z.1 z.2-(q:ℝ))^2∂(K H).prod (K H))
  simpa only [Kernel.prod_apply] using
    (hd.stronglyMeasurable.integral_kernel (κ:=K×ₖK)).measurable

theorem vectorRootCascadePairDefect_bound (hn : 0<n) (s : RSBScheme k) (β t a : ℝ)
    (ha : 0 ≤ a) (p : ℕ) (q : Paper.Overlap) (H : FiniteStateField (Configuration n)) :
    |vectorRootCascadePairDefect s β t a p q H|≤4 := by
  haveI:=isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha)
    (vectorRootInterpolationScaledDirection (n:=n) s β t) p
  unfold vectorRootCascadePairDefect
  rw [abs_of_nonneg (integral_nonneg fun z=>sq_nonneg _)]
  calc
    _≤∫_,(4:ℝ)∂_ := integral_mono Integrable.of_finite (integrable_const _) fun z=>by
      have ho:=abs_le.mp (abs_vectorOverlap_le_one hn z.1 z.2)
      nlinarith [q.property.1,q.property.2]
    _=4:=by simp

def vectorFiniteReplicaMatrixDefect (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (q : Paper.Overlap) (x : VectorState n) : ℝ :=
  (1/(n:ℝ))^2*∑l : Fin n,∑j : Fin n,
    (vectorBackwardMean s β t (fun σ=>Paper.spinSign (σ l)*Paper.spinSign (σ j)) i x)^2-
    2*(q:ℝ)*((1/(n:ℝ))*∑l : Fin n,
      (vectorBackwardMean s β t (fun σ=>Paper.spinSign (σ l)) i x)^2)+(q:ℝ)^2

theorem vectorRootCascadePairDefect_eq_finite_matrix (s : RSBScheme k) (β t a : ℝ)
    (ha : 0 ≤ a) (ht : t≤1) (p : ℕ) (hp : p≤k+1) (q : Paper.Overlap) (x : VectorState n) :
    vectorRootCascadePairDefect s β t a p q (vectorInterpolationStateMap β t x)=
      vectorFiniteReplicaMatrixDefect s β t (k+2-p) q x := by
  haveI:=isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha)
    (vectorRootInterpolationScaledDirection (n:=n) s β t) p
  unfold vectorRootCascadePairDefect
  rw [integral_overlap_defect_spin_product]
  simp_rw [vectorRootInterpolation_gibbs_mean s β t a ha ht _ p hp]
  rfl

theorem vectorRootCascadeSplitDefect_eq_finite (hn : 0<n) (s : RSBScheme k) (β t a : ℝ)
    (ha : 0 ≤ a) (hβ : β≠0) (ht : t<1) (hq : s.q 1=0) (p : ℕ) (hp : p≤k+1)
    (q : Paper.Overlap) :
    (∫z,(overlap n z.1 z.2-(q:ℝ))^2∂finiteStateCascadeSplitLaw
      (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
      (vectorRootInterpolationScaledDirection (n:=n) s β t) p (k+2-p) 0)=
      ∫sample : VectorDisorderBrownianSample n,vectorFiniteReplicaMatrixDefect s β t (k+2-p) q
        (vectorFiniteJointState s β t ht.le (s.q (k+2-p)).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
  let mass:=vectorRootInterpolationMass s a
  let L:=vectorRootInterpolationScaledDirection (n:=n) s β t
  have hm:=vectorRootInterpolationMass_nonneg s a ha
  haveI:=isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0) mass hm L p
  haveI:=isMarkovKernel_sourceKernelLaw
    (fun j=>finiteStateGaussianCascadeKernel mass L (gtStateLogPartition (fun _=>0)) (p+j))
    (fun j=>isMarkovKernel_finiteStateGaussianTerminalCascadeKernel _ mass hm L _) (k+2-p)
  have hd : Measurable (fun z : Configuration n×Configuration n=>(overlap n z.1 z.2-(q:ℝ))^2):=
    measurable_of_finite _
  have hb (z : Configuration n×Configuration n) : |(overlap n z.1 z.2-(q:ℝ))^2|≤4:=by
    rw [abs_of_nonneg (sq_nonneg _)]
    have ho:=abs_le.mp (abs_vectorOverlap_le_one hn z.1 z.2)
    nlinarith [q.property.1,q.property.2]
  rw [finiteStateCascadeSplitLaw,Measure.comp_eq_comp_const_apply,
    Kernel.integral_comp (source_bounded_integrable _ _ hd 4 hb)]
  simp only [Kernel.const_apply,Kernel.prod_apply]
  change (∫y,vectorRootCascadePairDefect s β t a p q y∂sourceKernelLaw
    (fun j=>finiteStateGaussianCascadeKernel mass L (gtStateLogPartition (fun _=>0)) (p+j))
      (k+2-p) 0)=_
  rw [←sourceKernelExpectation_eq_integral _
    (fun j=>isMarkovKernel_finiteStateGaussianTerminalCascadeKernel _ mass hm L _)
    _ (measurable_vectorRootCascadePairDefect s β t a ha p q) 4
    (vectorRootCascadePairDefect_bound hn s β t a ha p q)]
  rw [vectorRootInterpolation_expectation_eq_finite_node s β t a ha hβ ht hq p hp
    _ (measurable_vectorRootCascadePairDefect s β t a ha p q) 4 (by norm_num)
    (vectorRootCascadePairDefect_bound hn s β t a ha p q)]
  simp_rw [vectorRootCascadePairDefect_eq_finite_matrix s β t a ha ht.le p hp]

end QuantitativePaper
