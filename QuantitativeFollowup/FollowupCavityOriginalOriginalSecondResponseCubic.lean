module
public import QuantitativeFollowup.FollowupCavityOriginalOriginalGraftResponse
public import QuantitativeFollowup.FollowupCavityDominatedSixCubic

@[expose] public section

/-! The original-original second response is a sum of genuine same-tree
two-pair tests. Its cubic budget retains an arbitrary terminal spin factor
dominated by one old leaf-pair defect. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem oo_integrable_streaming_mul
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

private theorem oo_terminal_six_integral
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
    oo_integrable_streaming_mul D s a ha has hq T G hG C hC hb
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

private theorem oo_six_terminal_list_sum {A : Type}
    (D : AnisotropicSpinModel (n+1)) (hn : 0<n) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (xs : List A) (F : A→TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) :
    cavityMarkedSixExpectation D s a T
      (fun r=>(xs.map (fun b=>F b (finiteCascadeRecordTerminalSpins (trimRoot T) r.2))).sum)=
      (xs.map (fun b=>cavityMarkedSixExpectation D s a T
        (fun r=>F b (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)))).sum := by
  rw [(oo_terminal_six_integral D hn s a ha has hq T (fun τ=>(xs.map (fun b=>F b τ)).sum)).2]
  simp_rw [←List.sum_map_mul_right]
  let P : Measure (CavityPathRecordSpace (trimRoot T) (n+1)) :=
    anisotropicTrimmedRecordedTreeLaw D s a T
  let H : A→CavityPathRecordSpace (trimRoot T) (n+1)→ℝ :=
    fun b r=>F b (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*
      (cavityRecordedStreamingDefect n D s a T (D.variance (Fin.last n)) r+
        a*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a)
  have hiH (b : A) : Integrable (H b) P :=
    (oo_terminal_six_integral D hn s a ha has hq T (F b)).1
  change (∫r,(xs.map (fun b=>H b r)).sum∂P)=_
  apply (FourPapersCommon.integral_list_map_sum_real P xs H hiH).trans
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  exact (oo_terminal_six_integral D hn s a ha has hq T (F b)).2.symm

private theorem oo_sum_constant {A : Type*} (xs : List A) (C : ℝ) :
    (xs.map (fun _=>C)).sum=(xs.length:ℝ)*C := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.cast_add,Nat.cast_one]
      ring

def cavityOriginalOriginalSecondLeafTest (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (j h : ObservationLeaf (trimRoot T))
    (τ : TerminalSpins (Configuration (n+1)) (trimRoot T)) : ℝ :=
  F τ*cavitySpinOverlapDefect n (cavityProfileLevel s (observationCommonLevel (trimRoot T) j h))
    (observationTerminalSpin (trimRoot T) j τ) (observationTerminalSpin (trimRoot T) h τ)

theorem cavityOriginalOriginalSecondLeafTest_record (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (j h : ObservationLeaf (trimRoot T)) (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityOriginalOriginalSecondLeafTest s T F j h
      (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)=
      F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*
        cavityRecordedLeafPairDefect s (trimRoot T) j h r.2 := by
  simp only [cavityOriginalOriginalSecondLeafTest,observationTerminalSpin_record,cavityRecordedLeafPairDefect]

theorem cavityOriginalOriginalSecondResponse_six_split (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) :
    cavityMarkedSixExpectation D s a T
      (fun r=>F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*cavityOriginalDistinctLeafDefect n s T r)=
      ((observationLeaves (trimRoot T)).map (fun j=>((observationLeaves (trimRoot T)).map
        (fun h=>cavityMarkedSixExpectation D s a T
          (fun r=>cavityOriginalOriginalSecondLeafTest s T F j h
            (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)))).sum)).sum := by
  have he : (fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>
      F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*cavityOriginalDistinctLeafDefect n s T r)=
      fun r=>((observationLeaves (trimRoot T)).map (fun j=>((observationLeaves (trimRoot T)).map
        (fun h=>cavityOriginalOriginalSecondLeafTest s T F j h
          (finiteCascadeRecordTerminalSpins (trimRoot T) r.2))).sum)).sum := by
    funext r
    simp_rw [cavityOriginalOriginalSecondLeafTest_record]
    rw [cavityOriginalDistinctLeafDefect_eq_leaves hn D s T r,←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [←List.sum_map_mul_left]
  rw [he,oo_six_terminal_list_sum D hn s a ha has hq T (observationLeaves (trimRoot T))
    (fun j τ=>((observationLeaves (trimRoot T)).map
      (fun h=>cavityOriginalOriginalSecondLeafTest s T F j h τ)).sum)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  exact oo_six_terminal_list_sum D hn s a ha has hq T (observationLeaves (trimRoot T))
    (cavityOriginalOriginalSecondLeafTest s T F j)

theorem cavityOriginalOriginalSecondResponse_six_cubic_le (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot T))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)| ≤
        |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|) :
    let L : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |cavityMarkedSixExpectation D s a T
      (fun r=>F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*cavityOriginalDistinctLeafDefect n s T r)| ≤
      15*L^4*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum
          (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  rw [cavityOriginalOriginalSecondResponse_six_split hn D s a ha.1 has hq T F]
  let L : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let C := 15*L^2*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
    finiteCascadeUnweightedBranchSum
      (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T))
  have hb (j h : ObservationLeaf (trimRoot T)) :
      |cavityMarkedSixExpectation D s a T (fun r=>cavityOriginalOriginalSecondLeafTest s T F j h
        (finiteCascadeRecordTerminalSpins (trimRoot T) r.2))|≤C := by
    apply cavityMarkedSix_dominatedPair_cubic_le hn D s a ha has hq T ![i,j] ![l,h]
    · exact (measurable_of_finite (cavityOriginalOriginalSecondLeafTest s T F j h)).comp
        ((measurable_finiteCascadeRecordTerminalSpins (trimRoot T)).comp measurable_snd)
    · intro r
      rw [cavityOriginalOriginalSecondLeafTest_record,abs_mul]
      simp only [cavityRecordedPairProduct,Matrix.cons_val_zero,Matrix.cons_val_one,abs_mul]
      exact mul_le_mul_of_nonneg_right (hF r) (abs_nonneg _)
  have hs := abs_list_sum_le (observationLeaves (trimRoot T))
    (fun j=>((observationLeaves (trimRoot T)).map (fun h=>cavityMarkedSixExpectation D s a T
      (fun r=>cavityOriginalOriginalSecondLeafTest s T F j h
        (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)))).sum)
    (fun _=>((observationLeaves (trimRoot T)).map (fun _=>C)).sum)
    (fun j _=>abs_list_sum_le (observationLeaves (trimRoot T)) _ (fun _=>C) (fun h _=>hb j h))
  simp only [oo_sum_constant,observationLeaves_length,leafCount_trimRoot] at hs
  exact hs.trans_eq (by dsimp only [C,L];ring)

theorem followupCavityOriginalOriginalSecondDerivative_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot T))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)| ≤
        |cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D := followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |derivWithin (followupCavityOriginalOriginalGraftExpectation n β ρ hβ hρ s a T F)
      (Icc (0:ℝ) 1) u| ≤
      followupCavityAlpha n β ρ/2*(15*L^4)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  dsimp only
  rw [(hasDerivWithinAt_followupCavityOriginalOriginalGraftExpectation hn β ρ hβ hρ s a ha has hq
    T F u hu).derivWithin (uniqueDiffOn_Icc_zero_one u hu)]
  have hα := followupCavityAlpha_nonneg n β ρ hρ.2
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤followupCavityAlpha n β ρ/2)]
  exact (mul_le_mul_of_nonneg_left (cavityOriginalOriginalSecondResponse_six_cubic_le hn
    (followupCavitySpinModel n β ρ hβ hρ u hu) s a ha has hq T i l F hF)
      (by positivity)).trans_eq (by ring)

end QuantitativeFollowup
