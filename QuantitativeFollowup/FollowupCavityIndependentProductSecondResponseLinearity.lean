module
public import QuantitativeFollowup.FollowupCavitySecondStreaming
public import QuantitativeFollowup.FollowupCavityOriginalGraftSecondResponse

@[expose] public section

/-! Genuine finite-terminal Six linearity. It permits the original-fresh
response to split under a bounded test without an old-pair assumption. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem independent_integrable_streaming_mul
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (G : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hG : Measurable G)
    (C : ℝ) (hC : 0≤C) (hGb : ∀r,|G r|≤C) :
    Integrable (fun r=>G r*cavityRecordedStreamingDefect n D s a T (D.variance (Fin.last n)) r)
      (anisotropicTrimmedRecordedTreeLaw D s a T) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := integrable_cavityRecordedFiveTerms_mul D s a ha has hq T
    (D.variance (Fin.last n)) G hG C hC hGb
  simp only [anisotropicReplaceVariance_self] at h1 h2 h3 h4 h5
  have hi := (((h1.sub (h2.const_mul 2)).add h3).add h4).add h5
  apply hi.congr
  exact .of_forall fun r=>by
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    rw [cavityRecordedStreamingDefect_five_terms D s a ha has hq T (D.variance (Fin.last n)) r]
    ring

private theorem independent_terminal_six_integral
    (D : AnisotropicSpinModel (n+1)) (hn : 0<n) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) :
    let G := fun r : CavityPathRecordSpace (trimRoot T) (n+1) =>
      F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
    let S := fun r => cavityRecordedStreamingDefect n D s a T (D.variance (Fin.last n)) r+
      a*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a
    Integrable (fun r=>G r*S r) (anisotropicTrimmedRecordedTreeLaw D s a T) ∧
      cavityMarkedSixExpectation D s a T G =
        ∫r,G r*S r∂anisotropicTrimmedRecordedTreeLaw D s a T := by
  dsimp only
  let G := fun r : CavityPathRecordSpace (trimRoot T) (n+1) =>
    F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
  let P := anisotropicTrimmedRecordedTreeLaw D s a T
  let S := fun r => cavityRecordedStreamingDefect n D s a T (D.variance (Fin.last n)) r
  let N := cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a
  let C := ∑τ,|F τ|
  have hC : 0≤C := Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hG : Measurable G := (measurable_of_finite F).comp
    ((measurable_finiteCascadeRecordTerminalSpins (trimRoot T)).comp measurable_snd)
  have hb (r) : |G r|≤C := by
    change |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)|≤∑τ,|F τ|
    exact Finset.single_le_sum (f:=fun τ=>|F τ|) (fun _ _=>abs_nonneg _) (Finset.mem_univ _)
  have hiG : Integrable G P := by
    apply (integrable_const (μ:=P) C).mono' hG.aestronglyMeasurable
    exact .of_forall fun r=>by simpa only [Real.norm_eq_abs] using hb r
  have hiS : Integrable (fun r=>G r*S r) P :=
    independent_integrable_streaming_mul D s a ha has hq T G hG C hC hb
  have hiN := hiG.mul_const (a*N)
  have hj : Integrable (fun r=>G r*(S r+a*N)) P := by
    convert! hiS.add hiN using 1
    funext r
    simp only [Pi.add_apply]
    ring
  refine ⟨hj,?_⟩
  change cavityMarkedSixExpectation D s a T G=∫r,G r*(S r+a*N)∂P
  have he : (fun r=>G r*(S r+a*N))=(fun r=>G r*S r+G r*(a*N)) := funext fun r=>by ring
  rw [he,integral_add hiS hiN,integral_mul_const,
    integral_cavityRecordedStreamingDefect_eq_markedFive D hn s a ha has hq T G hG C hC hb]
  unfold cavityMarkedSixExpectation
  dsimp only [N]
  ring

theorem cavityIndependent_six_terminal_list_sum {A : Type}
    (D : AnisotropicSpinModel (n+1)) (hn : 0<n) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (xs : List A) (F : A→TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) :
    cavityMarkedSixExpectation D s a T
      (fun r=>(xs.map (fun b=>F b (finiteCascadeRecordTerminalSpins (trimRoot T) r.2))).sum)=
      (xs.map (fun b=>cavityMarkedSixExpectation D s a T
        (fun r=>F b (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)))).sum := by
  rw [(independent_terminal_six_integral D hn s a ha has hq T (fun τ=>(xs.map (fun b=>F b τ)).sum)).2]
  simp_rw [←List.sum_map_mul_right]
  let P : Measure (CavityPathRecordSpace (trimRoot T) (n+1)) :=
    anisotropicTrimmedRecordedTreeLaw D s a T
  let H : A→CavityPathRecordSpace (trimRoot T) (n+1)→ℝ :=
    fun b r=>F b (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*
      (cavityRecordedStreamingDefect n D s a T (D.variance (Fin.last n)) r+
        a*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a)
  have hiH (b : A) : Integrable (H b) P :=
    (independent_terminal_six_integral D hn s a ha has hq T (F b)).1
  change (∫r,(xs.map (fun b=>H b r)).sum∂P)=_
  apply (FourPapersCommon.integral_list_map_sum_real P xs H hiH).trans
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  exact (independent_terminal_six_integral D hn s a ha has hq T (F b)).2.symm

theorem cavityIndependent_originalGraft_vertex_six_split
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ) :
    cavityMarkedSixExpectation D s a (.advance (finiteCascadeVertexGraft v))
      (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
        (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)))=
      ((observationLeaves (trimRoot T)).map (fun b=>cavityMarkedSixExpectation D s a
        (.advance (finiteCascadeVertexGraft v))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
          (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b))))).sum := by
  let U : FiniteTerminalGenealogy (k+2):=.advance (finiteCascadeVertexGraft v)
  let H:=fun b=>cavityFullTestToTerminal U
    (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b))
  have he : (followupCavityPhysicalRecordObservable n U
      (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)))=
      fun r : CavityPathRecordSpace (trimRoot U) (n+1)=>
        ((observationLeaves (trimRoot T)).map (fun b=>H b (finiteCascadeRecordTerminalSpins (trimRoot U) r.2))).sum:=by
    funext r
    change followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
      (cavitySingleGraftSampleObservable T v (cavityOriginalGraftPairObservable s T v F)) r=_
    rw [cavityOriginalGraftPairObservable_split_record]
    apply congrArg List.sum;apply List.map_congr_left;intro b _
    exact (cavityFullTestToTerminal_record U
      (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b)) r).symm
  rw [he,cavityIndependent_six_terminal_list_sum D hn s a ha has hq U (observationLeaves (trimRoot T)) H]
  apply congrArg List.sum;apply List.map_congr_left;intro b _
  apply congrArg (cavityMarkedSixExpectation D s a U)
  funext r
  exact cavityFullTestToTerminal_record U
    (cavitySingleGraftSampleObservable T v (cavityOriginalLeafGraftObservable s T v F b)) r

end QuantitativeFollowup
