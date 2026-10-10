module
public import QuantitativeFollowup.FollowupCavityPathCovariance
public import QuantitativeFollowup.FollowupCavityPathStieltjesGenerator

@[expose] public section

/-! The path-variance score is an observable of the actual retained fields
and terminal spins. This identifies the Gaussian-coordinate formula with
the physical recorded law, rather than assuming a law equivalence. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

abbrev CavityPathRecordSpace {j : ℕ} (T : FiniteTerminalGenealogy j) (n : ℕ) :=
  FiniteStateField (Configuration n)×Records (FiniteStateField (Configuration n)) (Configuration n) T

def cavityPathPhysicalRecord (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ)
    (p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) : CavityPathRecordSpace T n :=
  finiteCascadeTreeReferenceRootFlatRecord
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) T (anisotropicRootEnergyMap D) 0 p

def cavityPathRecordedLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) :=
  finiteCascadeTreeGaussianJointLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T (anisotropicRootEnergyMap D) 0

theorem cavityPathFlatLaw_physical_records_map (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) :
    (cavityPathFlatLaw D s a i T b).map (cavityPathPhysicalRecord D s i T b)=
      cavityPathRecordedLaw D s a i T b :=
  finiteCascadeTreeGaussianJointLaw_eq_flat_density _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

theorem cavityPathPhysicalRecord_eq_fixed_record (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (b : ℝ) (hb : 0<b) (p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) :
    cavityPathPhysicalRecord D s i T b p=
      cavityPathFixedRecord D s i T p.2 (gaussianSelectedScale (cavitySelectedRootPathMask i T) b p.1) := by
  unfold cavityPathPhysicalRecord cavityPathFixedRecord
  rw [cavityPathVariance_reference_record D s i b hb]
  rw [gaussianSelectedScale_eq_cavityPathDiagonal]

def cavityPathRecordMean (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (v : FiniteCascadeRecordVertex T)
    (p : CavityPathRecordSpace T n) : ℝ :=
  fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth)
      (v.field p.1 p.2) (cavityCoordinateFeature i)

def cavityPathRecordHessian (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (v : FiniteCascadeRecordVertex T)
    (p : CavityPathRecordSpace T n) : ℝ :=
  fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth))
      (v.field p.1 p.2) (cavityCoordinateFeature i) (cavityCoordinateFeature i)

def cavityPathRecordParameter (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (v : FiniteCascadeRecordVertex T)
    (p : CavityPathRecordSpace T n) : ℝ :=
  cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s v.depth (v.field p.1 p.2)
    (cavityCoordinateFeature i)

def cavityPathRecordSignedMarks (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (p : CavityPathRecordSpace T n) :=
  (finiteCascadeTerminalVertices T (finiteCascadeRecordTerminalSpins T p.2)).map
    (fun c=>(Paper.spinSign (c.2 i),c.1)) ++
    (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map
      (fun c=>(-c.1*cavityPathRecordMean D s i T b c.2 p,c.2))

def cavityPathRecordClockGram (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (p : CavityPathRecordSpace T n) : ℝ :=
  ((cavityPathRecordSignedMarks D s a i T b p).map (fun c=>
    ((cavityPathRecordSignedMarks D s a i T b p).map (fun d=>
      c.1*d.1*(cavityPhysicalCommonOverlap s T c.2 d.2-s.q (k+2-j)))).sum)).sum

def cavityPathRecordScore (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (p : CavityPathRecordSpace T n) : ℝ :=
  -((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map
    (fun c=>c.1*cavityPathRecordParameter D s i T b c.2 p)).sum+(1/2:ℝ)*
    (cavityPathRecordClockGram D s a i T b p-
      ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map (fun c=>
        c.1*(s.q (k+2-c.2.depth)-s.q (k+2-j))*cavityPathRecordHessian D s i T b c.2 p)).sum)

theorem cavityPathRecordMean_physical (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (b : ℝ) (hb : 0<b) (v : FiniteCascadeRecordVertex T)
    (p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) :
    cavityPathRecordMean D s i T b v (cavityPathPhysicalRecord D s i T b p)=
      cavityPathSelectedVertexMean D s i T b (gaussianSelectedScale (cavitySelectedRootPathMask i T) b p.1) v := by
  unfold cavityPathRecordMean cavityPathSelectedVertexMean
  rw [cavityPathPhysicalRecord_eq_fixed_record D s i T b hb p,cavityPathVertexField_eq_fixed_record]

theorem cavityPathRecordScore_physical (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (b : ℝ) (hb : 0<b) (p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) :
    cavityPathRecordScore D s a i T b (cavityPathPhysicalRecord D s i T b p)=
      cavityPathFlatScore D s a i T b p := by
  have hsp:=finiteCascadeRecordTerminalSpins_referenceRoot
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) T (anisotropicRootEnergyMap D)
      0 p.1 p.2
  have hmean (v : FiniteCascadeRecordVertex T):=cavityPathRecordMean_physical D s i T b hb v p
  have hH (v : FiniteCascadeRecordVertex T) :
      cavityPathRecordHessian D s i T b v (cavityPathPhysicalRecord D s i T b p)=
        cavityPathVertexBinaryHessian D s i T b (gaussianSelectedScale (cavitySelectedRootPathMask i T) b p.1) v := by
    unfold cavityPathRecordHessian cavityPathVertexBinaryHessian
    rw [cavityPathPhysicalRecord_eq_fixed_record D s i T b hb p,cavityPathVertexField_eq_fixed_record]
  have hB (v : FiniteCascadeRecordVertex T) :
      cavityPathRecordParameter D s i T b v (cavityPathPhysicalRecord D s i T b p)=
        cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s v.depth
          (cavityPathVertexField D s i T v (gaussianSelectedScale (cavitySelectedRootPathMask i T) b p.1))
          (cavityCoordinateFeature i) := by
    unfold cavityPathRecordParameter
    rw [cavityPathPhysicalRecord_eq_fixed_record D s i T b hb p,cavityPathVertexField_eq_fixed_record]
  unfold cavityPathFlatScore
  rw [cavityPathScoreGenerator_eq_shared_clock]
  unfold cavityPathRecordScore cavityPathRecordClockGram cavityPathRecordSignedMarks
    cavityPathSharedClockGram cavityPathSignedMarks cavityPathParameterCharge
  change finiteCascadeRecordTerminalSpins T (cavityPathPhysicalRecord D s i T b p).2=p.2 at hsp
  simp_rw [hsp,hmean,hH,hB]

theorem measurable_cavityPathRecordMean (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (v : FiniteCascadeRecordVertex T) :
    Measurable (cavityPathRecordMean D s i T b v) := by
  exact (((contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth).continuous_fderiv
        (by simp)).clm_apply continuous_const).measurable.comp v.measurable_field

theorem measurable_cavityPathRecordHessian (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) (v : FiniteCascadeRecordVertex T) :
    Measurable (cavityPathRecordHessian D s i T b v) := by
  have hd := (contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) v.depth).fderiv_right (m:=∞) (by simp)
  exact ((hd.continuous_fderiv (by simp)).clm_apply continuous_const |>.clm_apply continuous_const).measurable.comp
    v.measurable_field

theorem measurable_cavityPathRecordParameter (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2) (b : ℝ) (hb : 0<b)
    (v : FiniteCascadeRecordVertex T) : Measurable (cavityPathRecordParameter D s i T b v) := by
  let U : ℝ×FiniteStateField (Configuration n)→ℝ:=fun w=>finiteStateGaussianTerminalCascade
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i w.1) s) v.depth w.2
  have hs:=exponentialSmoothOn_cavityFinitePotential_variance D s i v.depth (v.depth_le.trans hj)
    (b/2) (3*b/2) (by linarith)
  have hU (H : FiniteStateField (Configuration n)) : ContDiffAt ℝ ∞ U (b,H):=
    hs.smooth _ ⟨⟨by linarith,by linarith⟩,mem_univ H⟩
  have he (H : FiniteStateField (Configuration n)) : fderiv ℝ U (b,H) (1,0)=
      cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s v.depth H (cavityCoordinateFeature i):=by
    have hd:=((hU H).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt b
      ((hasDerivAt_id b).prodMk (hasDerivAt_const b H))
    exact hd.unique (hasDerivAt_cavityFinitePotential_variance_field D s i b hb v.depth H)
  have hc : Continuous (fun H : FiniteStateField (Configuration n)=>fderiv ℝ U (b,H) (1,0)):=by
    apply continuous_iff_continuousAt.mpr
    intro H
    exact (((hU H).fderiv_right (m:=∞) (by simp)).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).clm_apply continuous_const.continuousAt
  have hf : cavityPathRecordParameter D s i T b v=
      fun p=>fderiv ℝ U (b,v.field p.1 p.2) (1,0):=by
    funext p
    exact (he _).symm
  rw [hf]
  exact hc.measurable.comp v.measurable_field

private theorem measurable_list_sum {Ω A : Type} [MeasurableSpace Ω]
    (cs : List A) (f : A→Ω→ℝ) (hf : ∀c∈cs,Measurable (f c)) :
    Measurable (fun p=>(cs.map (fun c=>f c p)).sum) := by
  induction cs with
  | nil => exact measurable_const
  | cons c cs ih =>
    convert! (hf c (by simp)).add (ih (fun d hd=>hf d (List.mem_cons_of_mem c hd))) using 1

private theorem measurable_list_gram {Ω A : Type} [MeasurableSpace Ω]
    (cs : List ((Ω→ℝ)×A)) (K : A→A→ℝ) (hf : ∀c∈cs,Measurable c.1) :
    Measurable (fun p=>(cs.map (fun c=>(cs.map (fun d=>c.1 p*d.1 p*K c.2 d.2)).sum)).sum) := by
  apply measurable_list_sum
  intro c hc
  apply measurable_list_sum
  intro d hd
  exact ((hf c hc).mul (hf d hd)).mul measurable_const

theorem measurable_cavityPathRecordClockGram (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (b : ℝ) :
    Measurable (cavityPathRecordClockGram D s a i T b) := by
  let g : CavityPathRecordSpace T n×TerminalSpins (Configuration n) T→ℝ:=fun w=>
    let ms:=(finiteCascadeTerminalVertices T w.2).map (fun c=>(Paper.spinSign (c.2 i),c.1)) ++
      (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map
        (fun c=>(-c.1*cavityPathRecordMean D s i T b c.2 w.1,c.2))
    (ms.map (fun c=>(ms.map (fun d=>
      c.1*d.1*(cavityPhysicalCommonOverlap s T c.2 d.2-s.q (k+2-j)))).sum)).sum
  have hg : Measurable g:=by
    apply measurable_from_prod_countable_left
    intro σ
    let cs : List ((CavityPathRecordSpace T n→ℝ)×FiniteCascadeRecordVertex T):=
      (finiteCascadeTerminalVertices T σ).map (fun c=>(fun _=>Paper.spinSign (c.2 i),c.1)) ++
        (finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map
          (fun c=>(fun p=>-c.1*cavityPathRecordMean D s i T b c.2 p,c.2))
    have hm : ∀c∈cs,Measurable c.1:=by
      intro c hc
      rcases List.mem_append.mp hc with hc|hc
      · obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
        exact measurable_const
      · obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
        exact measurable_const.mul (measurable_cavityPathRecordMean D s i T b d.2)
    convert measurable_list_gram cs
      (fun v w=>cavityPhysicalCommonOverlap s T v w-s.q (k+2-j)) hm using 1
    funext p
    simp only [g,cs,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  exact hg.comp (measurable_id.prodMk ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd))

theorem measurable_cavityPathRecordScore (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    (b : ℝ) (hb : 0<b) : Measurable (cavityPathRecordScore D s a i T b) := by
  apply Measurable.add
  · apply Measurable.neg
    apply measurable_list_sum
    intro c _
    exact measurable_const.mul (measurable_cavityPathRecordParameter D s i T hj b hb c.2)
  · apply Measurable.mul measurable_const
    apply (measurable_cavityPathRecordClockGram D s a i T b).sub
    apply measurable_list_sum
    intro c _
    exact measurable_const.mul (measurable_cavityPathRecordHessian D s i T b c.2)

theorem integral_cavityPathRecordedLaw_score_mul (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (b : ℝ) (hb : 0<b) :
    (∫p,F (finiteCascadeRecordTerminalSpins T p.2)*cavityPathRecordScore D s a i T b p
        ∂cavityPathRecordedLaw D s a i T b)=
      ∫p,F p.2*cavityPathFlatScore D s a i T b p∂cavityPathFlatLaw D s a i T b := by
  have hm:=measurable_finiteCascadeTreeReferenceRootFlatRecord
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) T (anisotropicRootEnergyMap D) 0
  change Measurable (cavityPathPhysicalRecord D s i T b) at hm
  have hf : Measurable (fun p : CavityPathRecordSpace T n=>
      F (finiteCascadeRecordTerminalSpins T p.2)*cavityPathRecordScore D s a i T b p):=
    ((measurable_of_countable F).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)).mul
      (measurable_cavityPathRecordScore D s a i T hj b hb)
  rw [←cavityPathFlatLaw_physical_records_map D s a i T b,integral_map hm.aemeasurable hf.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    dsimp only
    rw [cavityPathRecordScore_physical D s a i T b hb p]
    rw [show finiteCascadeRecordTerminalSpins T (cavityPathPhysicalRecord D s i T b p).2=p.2 from
      finiteCascadeRecordTerminalSpins_referenceRoot _ _ _ _ p.1 p.2]

theorem hasDerivAt_cavityPathMarkedExpectation_recorded_covariance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (b : ℝ) (hb : 0<b) :
    HasDerivAt (cavityPathMarkedExpectation D s a i T F)
      ((∫p,F (finiteCascadeRecordTerminalSpins T p.2)*cavityPathRecordScore D s a i T b p
          ∂cavityPathRecordedLaw D s a i T b)-
        cavityPathMarkedExpectation D s a i T F b*
          (∫p,cavityPathRecordScore D s a i T b p∂cavityPathRecordedLaw D s a i T b)) b := by
  have h1:=integral_cavityPathRecordedLaw_score_mul D s a i T hj (fun _=>1) b hb
  simp only [one_mul] at h1
  rw [integral_cavityPathRecordedLaw_score_mul D s a i T hj F b hb,h1]
  exact hasDerivAt_cavityPathMarkedExpectation_covariance D s a i T hj F b hb

end QuantitativeFollowup
