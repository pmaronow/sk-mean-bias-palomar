module
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseBasic
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseNormalizer

@[expose] public section

/-! Multiplier bookkeeping keeps each first-response mark under its real
recorded graft law. The public applications below construct the multiplier
budgets from independent probability products. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private def independentPairMultiplier (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a Z K A : ℝ) : Prop :=
  ∀(U : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot U))
    (H : CavityPathRecordSpace (trimRoot U) (n+1)→ℝ), Measurable H→
      (∀r,|H r|≤|cavityRecordedLeafPairDefect s (trimRoot U) i l r.2|)→
        |(∫r,H r∂anisotropicTrimmedRecordedTreeLaw D s a U)*Z|≤
          K*(A+finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot U))

private theorem independent_single_multiplier
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a Z K A : ℝ)
    (hsource : independentPairMultiplier D s a Z K A)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (j : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hFb : ∀r,|F r|≤1) :
    |(∫r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1),F r.1*cavitySpinOverlapDefect n
        (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
        (observationLeafSpin (trimRoot T) j r.1.2) r.2∂anisotropicSingleVertexMarkedLaw D s a T v)*Z|≤
      K*(A+finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
        (finiteCascadeVertexGraft v)) := by
  let e:=fun r : CavityPathRecordSpace (finiteCascadeVertexGraft v) (n+1)=>
    ((r.1,(finiteCascadeGraftRecordExtract v r.2).1),(finiteCascadeGraftRecordExtract v r.2).2)
  have he : Measurable e :=
    (measurable_fst.prodMk ((measurable_finiteCascadeGraftRecordExtract v).fst.comp measurable_snd)).prodMk
      ((measurable_finiteCascadeGraftRecordExtract v).snd.comp measurable_snd)
  let H:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>F r.1*cavitySpinOverlapDefect n
    (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
    (observationLeafSpin (trimRoot T) j r.1.2) r.2
  have hσ : Measurable (fun r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>
      observationLeafSpin (trimRoot T) j r.1.2) :=
    (measurable_observationLeafSpin (E:=FiniteStateField (Configuration (n+1)))
      (S:=Configuration (n+1)) (trimRoot T) j).comp (measurable_snd.comp measurable_fst)
  let pair := fun r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>
    (observationLeafSpin (trimRoot T) j r.1.2,r.2)
  let d := fun p : Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n
    (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v)) p.1 p.2
  have hpair : Measurable pair := hσ.prodMk measurable_snd
  have hd : Measurable d := measurable_of_finite _
  have hdef : Measurable (d∘pair) := hd.comp hpair
  dsimp only [d,pair,Function.comp_def] at hdef
  have hH : Measurable H := (hF.comp measurable_fst).mul hdef
  have hm:=integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeVertexGraft v)))
    he.aemeasurable hH.aestronglyMeasurable
  have hmap : (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeVertexGraft v))).map e =
      anisotropicSingleVertexMarkedLaw D s a T v := anisotropicSingleVertexMarkedLaw_eq_graft D s a T v
  rw [hmap] at hm
  change |(∫r,H r∂anisotropicSingleVertexMarkedLaw D s a T v)*Z|≤_
  rw [hm]
  apply hsource (.advance (finiteCascadeVertexGraft v))
    (finiteCascadeVertexGraftOldLeaf v j) (finiteCascadeVertexGraftNewLeaf v) (H∘e) (hH.comp he)
  intro r
  dsimp only [H,e,Function.comp_def]
  simp only [cavityRecordedLeafPairDefect,
    finiteCascadeVertexGraftOldNewLeaf_commonLevel,
    finiteCascadeVertexGraftOldLeaf_spin,finiteCascadeVertexGraftNewLeaf_spin,abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (hFb (r.1,(finiteCascadeGraftRecordExtract v r.2).1)) (abs_nonneg _)

private theorem independent_cross_multiplier
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a Z K A : ℝ)
    (hsource : independentPairMultiplier D s a Z K A)
    (T : FiniteTerminalGenealogy (k+2)) (v w : FiniteCascadeRecordVertex (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hFb : ∀r,|F r|≤1) :
    |(∫r,F r.1*cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) r.2.1 r.2.2
        ∂anisotropicCrossVertexMarkedLaw D s a T v w)*Z|≤
      K*(A+finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
        (finiteCascadeCrossVertexGraft v w)) := by
  let e:=fun r : CavityPathRecordSpace (finiteCascadeCrossVertexGraft v w) (n+1)=>
    ((r.1,(finiteCascadeCrossGraftExtract v w r.2).1),(finiteCascadeCrossGraftExtract v w r.2).2)
  have he : Measurable e :=
    (measurable_fst.prodMk ((measurable_finiteCascadeCrossGraftExtract v w).fst.comp measurable_snd)).prodMk
      ((measurable_finiteCascadeCrossGraftExtract v w).snd.comp measurable_snd)
  let H:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)×(Configuration (n+1)×Configuration (n+1))=>
    F r.1*cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) r.2.1 r.2.2
  have hH : Measurable H := (hF.comp measurable_fst).mul
    ((measurable_of_finite (fun p : Configuration (n+1)×Configuration (n+1)=>
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) p.1 p.2)).comp measurable_snd)
  have hm:=integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeCrossVertexGraft v w)))
    he.aemeasurable hH.aestronglyMeasurable
  have hmap : (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeCrossVertexGraft v w))).map e =
      anisotropicCrossVertexMarkedLaw D s a T v w := anisotropicCrossVertexMarkedLaw_eq_graft D s a T v w
  rw [hmap] at hm
  change |(∫r,H r∂anisotropicCrossVertexMarkedLaw D s a T v w)*Z|≤_
  rw [hm]
  apply hsource (.advance (finiteCascadeCrossVertexGraft v w))
    (finiteCascadeCrossGraftFirstLeaf v w) (finiteCascadeCrossGraftSecondLeaf v w) (H∘e) (hH.comp he)
  intro r
  dsimp only [H,e,Function.comp_def]
  simp only [cavityRecordedLeafPairDefect,finiteCascadeCrossGraftFresh_commonLevel,
    finiteCascadeCrossGraftFirstLeaf_spin,finiteCascadeCrossGraftSecondLeaf_spin,abs_mul]
  rw [cavityPhysicalCommonOverlap_eq_profileLevel]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (hFb (r.1,(finiteCascadeCrossGraftExtract v w r.2).1)) (abs_nonneg _)

private theorem independent_future_multiplier
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a Z K A : ℝ)
    (hsource : independentPairMultiplier D s a Z K A)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) (hlevel : cavityProfileLevel s (cavityFiniteFutureDepth s v.depth q)=q)
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hFb : ∀r,|F r|≤1) :
    |(∫r,F r.1*cavitySpinOverlapDefect n q r.2.1 r.2.2
        ∂anisotropicFutureVertexMarkedLaw D s a T v q)*Z|≤
      K*(A+finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
        (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q))) := by
  let p:=cavityFiniteFutureDepth s v.depth q
  let e:=fun r : CavityPathRecordSpace (finiteCascadeFutureVertexGraft v p) (n+1)=>
    ((r.1,(finiteCascadeFutureGraftExtract v p r.2).1),(finiteCascadeFutureGraftExtract v p r.2).2)
  have he : Measurable e :=
    (measurable_fst.prodMk ((measurable_finiteCascadeFutureGraftExtract v p).fst.comp measurable_snd)).prodMk
      ((measurable_finiteCascadeFutureGraftExtract v p).snd.comp measurable_snd)
  let H:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)×(Configuration (n+1)×Configuration (n+1))=>
    F r.1*cavitySpinOverlapDefect n q r.2.1 r.2.2
  have hH : Measurable H := (hF.comp measurable_fst).mul
    ((measurable_of_finite (fun p : Configuration (n+1)×Configuration (n+1)=>
      cavitySpinOverlapDefect n q p.1 p.2)).comp measurable_snd)
  have hm:=integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeFutureVertexGraft v p)))
    he.aemeasurable hH.aestronglyMeasurable
  have hmap : (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeFutureVertexGraft v p))).map e =
      anisotropicFutureVertexMarkedLaw D s a T v q := anisotropicFutureVertexMarkedLaw_eq_graft D s a T v q
  rw [hmap] at hm
  change |(∫r,H r∂anisotropicFutureVertexMarkedLaw D s a T v q)*Z|≤_
  rw [hm]
  apply hsource (.advance (finiteCascadeFutureVertexGraft v p))
    (finiteCascadeContinuationNewLeaf (fun d=>(finiteCascadeFuturePairTree p d).tree) v
      (observationPairFirstLeaf (finiteCascadeFuturePairTree p v.depth)))
    (finiteCascadeContinuationNewLeaf (fun d=>(finiteCascadeFuturePairTree p d).tree) v
      (observationPairSecondLeaf (finiteCascadeFuturePairTree p v.depth))) (H∘e) (hH.comp he)
  intro r
  dsimp only [H,e,Function.comp_def]
  simp only [cavityRecordedLeafPairDefect,finiteCascadeContinuationNewLeaf_commonLevel,
    finiteCascadeContinuationNewLeaf_spin,observationPair_commonLevel,
    finiteCascadeFuturePairTree_split p v.depth (cavityFiniteFutureDepth_le s v.depth q),
    finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records,
    observationPair_spins_eq_leaf_pair,abs_mul]
  have hlevelp : cavityProfileLevel s p=q := hlevel
  rw [hlevelp]
  simpa only [one_mul,finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records] using
    mul_le_mul_of_nonneg_right (hFb (r.1,(finiteCascadeFutureGraftExtract v p r.2).1)) (abs_nonneg _)

private theorem independent_sum_constant {A : Type*} (xs : List A) (C : ℝ) :
    (xs.map (fun _=>C)).sum=(xs.length:ℝ)*C := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.cast_add,Nat.cast_one];ring

private theorem independent_weighted_affine {A : Type*} (xs : List (ℝ×A))
    (f : A→ℝ) (K C : ℝ) :
    (xs.map (fun c=>c.1*(K*(C+f c.2)))).sum=
      K*((xs.map Prod.fst).sum*C+(xs.map (fun c=>c.1*f c.2)).sum) := by
  have he : (fun c : ℝ×A=>c.1*(K*(C+f c.2)))=
    fun c=>K*(c.1*C+c.1*f c.2):=funext fun _=>by ring
  rw [he,List.sum_map_mul_left,List.sum_map_add,List.sum_map_mul_right]

private theorem independent_six_bounded_multiplier
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F) (hFb : ∀r,|F r|≤1)
    (Z K A RN : ℝ) (hK : 0≤K) (hA : 0≤A)
    (hsource : independentPairMultiplier D s a Z K A)
    (hNZ : |cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z|≤RN) :
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |cavityMarkedSixExpectation D s a T F*Z|≤
      14*K*L^2*(A+cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum
          (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T))+RN := by
  dsimp only
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let S:=A+M+B
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:=(cs.map Prod.fst).sum
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hS : 0≤S:=by dsimp only [S];positivity
  have hL : 1≤L:=by dsimp only [L];exact_mod_cast Nat.succ_le_of_lt (FiniteCascadeGenealogy.leafCount_pos (asGenealogy T))
  have hW : W=L-a:=by dsimp only [W,cs,L];rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hWL : W≤L:=by rw [hW];linarith [ha.1]
  have hW0 : 0≤W:=by
    apply List.sum_nonneg;intro z hz;obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hz
    exact anisotropicTrimmedVertexCharges_nonneg s a has T c hc
  have hiν (g : Paper.Overlap→ℝ) : Integrable g ν:=by
    dsimp only [ν];rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a g
  have hm : ν.real univ=1-a:=by
    change (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a univ).toReal=1-a
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
  have hOO : |(∫r,F r*cavityOriginalDistinctLeafDefect n s T r∂anisotropicTrimmedRecordedTreeLaw D s a T)*Z|≤K*L^2*S:=by
    let P:=anisotropicTrimmedRecordedTreeLaw D s a T
    let xs:=observationLeaves (trimRoot T)
    let H:=fun j h r=>F r*cavityRecordedLeafPairDefect s (trimRoot T) j h r.2
    have hi (j h : ObservationLeaf (trimRoot T)) : Integrable (H j h) P:=
      integrable_bounded_pair_mul_cavityDefect P F hF (fun r=>(hFb r).trans (by norm_num : (1:ℝ)≤4))
        _ _ ((measurable_observationLeafSpin _ j).comp measurable_snd) ((measurable_observationLeafSpin _ h).comp measurable_snd) _
    have he (r) : F r*cavityOriginalDistinctLeafDefect n s T r=(xs.map (fun j=>(xs.map (fun h=>H j h r)).sum)).sum:=by
      rw [cavityOriginalDistinctLeafDefect_eq_leaves hn D s T r,←List.sum_map_mul_left]
      apply congrArg List.sum;apply List.map_congr_left;intro j _;rw [←List.sum_map_mul_left]
    simp_rw [he]
    rw [integral_list_map_sum_real P xs _ (fun j=>integrable_list_map_sum_real P xs _ (hi j))]
    simp_rw [integral_list_map_sum_real P xs _ (hi _)]
    rw [←List.sum_map_mul_right]
    have hh:=abs_list_sum_le xs (fun j=>(xs.map (fun h=>∫r,H j h r∂P)).sum*Z)
      (fun _=>(xs.map (fun _=>K*(A+B))).sum) (fun j _=>by
        rw [←List.sum_map_mul_right];apply abs_list_sum_le;intro h _
        apply hsource T j h (H j h)
        · exact hF.mul ((measurable_cavityRecordedLeafPairDefect (n:=n)
            (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) j h).comp measurable_snd)
        · intro r;rw [abs_mul]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hFb r) (abs_nonneg _))
    simp only [independent_sum_constant,xs,observationLeaves_length,leafCount_trimRoot] at hh
    have heq : (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*(K*(A+B)))=K*L^2*(A+B):=by dsimp only [L];ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by dsimp only [S];linarith) (by positivity))
  have hOF : |cavityOriginalFreshExpectation D s a T F*Z|≤2*K*L^2*S:=by
    have hv (v : FiniteCascadeRecordVertex (trimRoot T)) :
        |(∫r,F r.1*cavityOriginalVertexOverlapSum n s T v (finiteCascadeRecordTerminalSpins (trimRoot T) r.1.2) r.2
          ∂anisotropicSingleVertexMarkedLaw D s a T v)*Z|≤L*(K*(A+finiteCascadeUnweightedBranchSum
            (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft v))) := by
      let P:=anisotropicSingleVertexMarkedLaw D s a T v
      let xs:=observationLeaves (trimRoot T)
      let H:=fun j (r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1))=>F r.1*cavitySpinOverlapDefect n
        (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
        (observationLeafSpin (trimRoot T) j r.1.2) r.2
      have hi (j : ObservationLeaf (trimRoot T)) : Integrable (H j) P:=
        integrable_bounded_pair_mul_cavityDefect P _ (hF.comp measurable_fst) (fun r=>(hFb r.1).trans (by norm_num : (1:ℝ)≤4))
          _ _ ((measurable_observationLeafSpin _ j).comp (measurable_snd.comp measurable_fst)) measurable_snd _
      have he (r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)) :
          F r.1*cavityOriginalVertexOverlapSum n s T v (finiteCascadeRecordTerminalSpins (trimRoot T) r.1.2) r.2=(xs.map (fun j=>H j r)).sum:=by
        rw [cavityOriginalVertexOverlapSum_eq_leaves,←List.sum_map_mul_left]
      simp_rw [he]
      rw [integral_list_map_sum_real P xs H hi,←List.sum_map_mul_right]
      have hh:=abs_list_sum_le xs _ (fun _=>K*(A+finiteCascadeUnweightedBranchSum
        (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft v)))
        (fun j _=>independent_single_multiplier D s a Z K A hsource T v j F hF hFb)
      simpa only [independent_sum_constant,xs,observationLeaves_length,leafCount_trimRoot,L] using hh
    have hh : |cavityOriginalFreshExpectation D s a T F*Z|≤
        (cs.map (fun c=>c.1*(L*(K*(A+finiteCascadeUnweightedBranchSum
          (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2)))))).sum:=by
      unfold cavityOriginalFreshExpectation;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro c hc
      rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
      exact mul_le_mul_of_nonneg_left (hv c.2) (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    have he : (cs.map (fun c=>c.1*(L*(K*(A+finiteCascadeUnweightedBranchSum
        (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2)))))).sum=
        L*K*(W*A+cavityChargedGraftBranchBudget s a T f):=by
      have ht (c : ℝ×FiniteCascadeRecordVertex (trimRoot T)) : c.1*(L*(K*(A+finiteCascadeUnweightedBranchSum
        (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2))))=
        c.1*((L*K)*(A+finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2))):=by ring
      simp_rw [ht]
      rw [independent_weighted_affine cs (fun v=>finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft v)) (L*K) A]
      rfl
    rw [he] at hh
    have hg:=cavityChargedGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    change _≤L*(M+2*B) at hg
    have hb : W*A+cavityChargedGraftBranchBudget s a T f≤2*L*S:=by
      dsimp only [S];nlinarith only [hg,mul_le_mul_of_nonneg_right hWL hA,mul_nonneg (show 0≤L by linarith) hA,mul_nonneg (show 0≤L by linarith) hM]
    exact hh.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring))
  have hFF : |cavityFreshFreshExpectation D s a T F*Z|≤3*K*L^2*S:=by
    have hh : |cavityFreshFreshExpectation D s a T F*Z|≤
        (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*(K*(A+finiteCascadeUnweightedBranchSum
          (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft c.2 d.2))))).sum)).sum:=by
      unfold cavityFreshFreshExpectation;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro c hc
      simp_rw [mul_assoc]
      rw [List.sum_map_mul_left,mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
      apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
      rw [←List.sum_map_mul_right];apply abs_list_sum_le;intro d hd
      rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)]
      exact mul_le_mul_of_nonneg_left (independent_cross_multiplier D s a Z K A hsource T c.2 d.2 F hF hFb)
        (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)
    have he : (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*(K*(A+finiteCascadeUnweightedBranchSum
          (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft c.2 d.2))))).sum)).sum=
        K*(W^2*A+cavityChargedCrossGraftBranchBudget s a T f):=by
      have hin (v : FiniteCascadeRecordVertex (trimRoot T)) := independent_weighted_affine cs (fun w=>finiteCascadeUnweightedBranchSum (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft v w)) K A
      simp_rw [hin]
      rw [independent_weighted_affine cs (fun v=>(cs.map (fun d=>d.1*finiteCascadeUnweightedBranchSum
        (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft v d.2))).sum) K (W*A)]
      change K*(W*(W*A)+cavityChargedCrossGraftBranchBudget s a T f)=_
      ring
    rw [he] at hh
    have hg:=cavityChargedCrossGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    change _≤L^2*(2*M+3*B) at hg
    have hw2 : W^2≤L^2:=(sq_le_sq₀ hW0 (by linarith)).mpr hWL
    have hb : W^2*A+cavityChargedCrossGraftBranchBudget s a T f≤3*L^2*S:=by
      dsimp only [S];nlinarith only [hg,mul_le_mul_of_nonneg_right hw2 hA,mul_nonneg (sq_nonneg L) hA,mul_nonneg (sq_nonneg L) hM]
    exact hh.trans ((mul_le_mul_of_nonneg_left hb hK).trans_eq (by ring))
  have hCF : |cavityCurrentFreshExpectation D s a T F*Z|≤3*K*L*S:=by
    have hh : |cavityCurrentFreshExpectation D s a T F*Z|≤
        (cs.map (fun c=>c.1*(K*(A+finiteCascadeUnweightedBranchSum
          (fun d=>f (cavityProfileLevel s d)) (finiteCascadeCrossVertexGraft c.2 c.2))))).sum:=by
      unfold cavityCurrentFreshExpectation;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro c hc
      have hc0:=anisotropicTrimmedVertexCharges_nonneg s a has T c hc
      have hlev : anisotropicVertexOverlap s c.2=cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2:=by
        rw [anisotropicVertexOverlap_eq_cross_self,cavityPhysicalCommonOverlap_eq_profileLevel]
      rw [hlev,mul_assoc,abs_mul,abs_of_nonneg (mul_nonneg hc0 (Paper.parisiCDF_nonneg _ _))]
      calc
        _≤c.1*1*|(_ : ℝ)*Z|:=by gcongr;exact Paper.parisiCDF_le_one _ _
        _≤_:=by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (independent_cross_multiplier D s a Z K A hsource T c.2 c.2 F hF hFb) hc0
    rw [independent_weighted_affine cs (fun v=>finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeCrossVertexGraft v v)) K A] at hh
    change _≤K*(W*A+cavityChargedCurrentGraftBranchBudget s a T f) at hh
    have hg:=cavityChargedCurrentGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    change _≤L*(2*M+3*B) at hg
    have hb : W*A+cavityChargedCurrentGraftBranchBudget s a T f≤3*L*S:=by
      dsimp only [S];nlinarith only [hg,mul_le_mul_of_nonneg_right hWL hA,mul_nonneg (show 0≤L by linarith) hA,mul_nonneg (show 0≤L by linarith) hM]
    exact hh.trans ((mul_le_mul_of_nonneg_left hb hK).trans_eq (by ring))
  have hFU : |cavityFutureFreshExpectation D s a T F*Z|≤3*K*L*S:=by
    let G:=fun (v : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap)=>finiteCascadeUnweightedBranchSum
      (fun d=>f (cavityProfileLevel s d)) (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q))
    let H:=fun v=>∫q : Paper.Overlap,if cavityProfileLevel s v.depth<q then G v q else 0∂ν
    have hv (v : FiniteCascadeRecordVertex (trimRoot T)) :
        |(∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
          (∫r,F r.1*cavitySpinOverlapDefect n q r.2.1 r.2.2∂anisotropicFutureVertexMarkedLaw D s a T v q)
          else 0∂ν)*Z|≤K*(A+H v):=by
      let R:=fun q : Paper.Overlap=>if anisotropicVertexOverlap s v<q then
        (∫r,F r.1*cavitySpinOverlapDefect n q r.2.1 r.2.2∂anisotropicFutureVertexMarkedLaw D s a T v q) else 0
      rw [←integral_mul_const]
      have hb : (∫q,|R q*Z|∂ν)≤∫q,K*(A+(if cavityProfileLevel s v.depth<q then G v q else 0))∂ν:=by
        apply integral_mono_ae (hiν _) (hiν _)
        filter_upwards [ae_cavityFiniteFutureDepth_level s a ha.1 has hq v.depth
          (v.depth_le.trans (by omega : k+1≤k+2))] with q hlev
        by_cases hvq : cavityProfileLevel s v.depth<q
        · dsimp only [R];rw [if_pos (show anisotropicVertexOverlap s v<q from hvq),if_pos hvq]
          exact independent_future_multiplier D s a Z K A hsource T v q (hlev hvq) F hF hFb
        · dsimp only [R];rw [if_neg (show ¬anisotropicVertexOverlap s v<q from hvq),if_neg hvq,zero_mul,abs_zero]
          positivity
      rw [integral_const_mul,integral_add (hiν _) (hiν _),integral_const,hm] at hb
      exact abs_integral_le_integral_abs.trans (hb.trans (by
        change K*((1-a)*A+H v)≤K*(A+H v)
        exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg ha.1 hA]) hK))
    have hh : |cavityFutureFreshExpectation D s a T F*Z|≤(cs.map (fun c=>c.1*(K*(A+H c.2)))).sum:=by
      unfold cavityFutureFreshExpectation;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro c hc
      rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
      exact mul_le_mul_of_nonneg_left (hv c.2) (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    rw [independent_weighted_affine cs H K A] at hh
    change _≤K*(W*A+cavityChargedFutureGraftBranchBudget s a T f) at hh
    have hg:=cavityChargedFutureGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    change _≤2*L*(M+B) at hg
    have hb : W*A+cavityChargedFutureGraftBranchBudget s a T f≤3*L*S:=by
      dsimp only [S];nlinarith only [hg,mul_le_mul_of_nonneg_right hWL hA,mul_nonneg (show 0≤L by linarith) hA,mul_nonneg (show 0≤L by linarith) hM,mul_nonneg (show 0≤L by linarith) hB]
    exact hh.trans ((mul_le_mul_of_nonneg_left hb hK).trans_eq (by ring))
  have hR : |a*(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z|≤RN:=by
    let E:=∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T
    have hE : |E|≤1:=by
      have he0 := norm_integral_le_of_norm_le_const
        (μ:=anisotropicTrimmedRecordedTreeLaw D s a T) (f:=F) (C:=1)
        (.of_forall fun r=>by simpa only [Real.norm_eq_abs] using hFb r)
      simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using he0
    have he : |a*E|≤1:=by
      rw [abs_mul,abs_of_nonneg ha.1]
      exact (mul_le_mul_of_nonneg_left hE ha.1).trans (by simpa only [mul_one] using ha.2)
    rw [show a*E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z=
      (a*E)*(cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z) by ring,abs_mul]
    calc
      _≤1*|cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _≤1*RN := mul_le_mul_of_nonneg_left hNZ (by norm_num)
      _=RN := one_mul _
  let OO:=(∫r,F r*cavityOriginalDistinctLeafDefect n s T r∂anisotropicTrimmedRecordedTreeLaw D s a T)*Z
  let OF:=cavityOriginalFreshExpectation D s a T F*Z
  let FF:=cavityFreshFreshExpectation D s a T F*Z
  let CF:=cavityCurrentFreshExpectation D s a T F*Z
  let FU:=cavityFutureFreshExpectation D s a T F*Z
  let R:=a*(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z
  have he : cavityMarkedSixExpectation D s a T F*Z=OO-2*OF+FF+CF+FU+R:=by
    unfold cavityMarkedSixExpectation cavityMarkedFiveExpectation;dsimp only [OO,OF,FF,CF,FU,R];ring
  rw [he]
  have h1:=abs_sub OO (2*OF)
  rw [abs_mul (2:ℝ) OF,show |(2:ℝ)|=2 by norm_num] at h1
  have h2:=abs_add_le (OO-2*OF) FF
  have h3:=abs_add_le (OO-2*OF+FF) CF
  have h4:=abs_add_le (OO-2*OF+FF+CF) FU
  have h5:=abs_add_le (OO-2*OF+FF+CF+FU) R
  have hLK : K*L*S≤K*L^2*S:=by
    have hl : L≤L^2:=by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hK) hS
  change |OO-2*OF+FF+CF+FU+R|≤14*K*L^2*S+RN
  nlinarith only [h1,h2,h3,h4,h5,hOO,hOF,hFF,hCF,hFU,hR,hLK]

/-- The two independently sampled trees can be different. Their original
branch budgets are both retained. No product law is replaced by one root. -/
theorem cavityIndependent_six_bounded_six_onePair_cubic_le
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T U : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F) (hFb : ∀r,|F r|≤1)
    (i l : ObservationLeaf (trimRoot U))
    (G : CavityPathRecordSpace (trimRoot U) (n+1)→ℝ) (hG : Measurable G)
    (hdomG : ∀r,|G r|≤|cavityRecordedLeafPairDefect s (trimRoot U) i l r.2|) :
    |cavityMarkedSixExpectation D s a T F*cavityMarkedSixExpectation D s a U G|≤
      1800*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot U)) := by
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let C:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot U)
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let J : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy U)
  let K:=60*J^2
  let Z:=cavityMarkedSixExpectation D s a U G
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hC : 0≤C:=finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hK : 0≤K:=by dsimp only [K];positivity
  have hsource : independentPairMultiplier D s a Z K (M+C):=by
    intro V j h H hH hdom
    have hh:=cavityIndependent_onePair_six_pairMean_cubic_le hn D s a ha has hq U V i l j h G hG hdomG H hH hdom
    rw [mul_comm (∫r,H r∂anisotropicTrimmedRecordedTreeLaw D s a V) Z]
    exact hh
  have hNZ : |cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z|≤2*K*(M+C):=by
    rw [mul_comm]
    have hh:=cavitySixth_six_mul_normalizer_cubic_le hn D s a ha has hq U i l G hG hdomG
    exact hh.trans_eq (by dsimp only [K,J,C,f,M];ring)
  have hh:=independent_six_bounded_multiplier hn D s a ha has hq T F hF hFb Z K (M+C) (2*K*(M+C))
    hK (add_nonneg hM hC) hsource hNZ
  dsimp only at hh
  have hL : 1≤L:=by dsimp only [L];exact_mod_cast Nat.succ_le_of_lt (FiniteCascadeGenealogy.leafCount_pos (asGenealogy T))
  have hc : 2*K*(M+C)≤2*K*L^2*(M+C):=by
    have he : M+C≤L^2*(M+C):=by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show 1≤L^2 by nlinarith) (add_nonneg hM hC)
    exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring)
  change |cavityMarkedSixExpectation D s a T F*Z|≤1800*L^2*J^2*(M+B+C)
  have hb :=mul_nonneg (mul_nonneg hK (sq_nonneg L)) hB
  have hcc:=mul_nonneg (mul_nonneg hK (sq_nonneg L)) hC
  calc
    _≤14*K*L^2*((M+C)+M+B)+2*K*(M+C):=hh
    _≤30*K*L^2*(M+B+C):=by nlinarith only [hc,hb,hcc]
    _=1800*L^2*J^2*(M+B+C):=by dsimp only [K];ring

/-- A bounded test contributes one inserted defect to Six; two external
independent pair means supply the remaining cubic factors. -/
theorem cavityIndependent_six_bounded_twoMeans_cubic_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F) (hFb : ∀r,|F r|≤1)
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (y : X→ℝ) (z : Y→ℝ) (hy : Measurable y) (hz : Measurable z)
    (hyb : ∀r,|y r|≤2) (hzb : ∀r,|z r|≤2) :
    |cavityMarkedSixExpectation D s a T F*(∫r,y r∂P)*(∫r,z r∂Q)|≤
      15*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
          (∫r,|y r|^3∂P)+(∫r,|z r|^3∂Q)) := by
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum
    (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  let C:=∫r,|y r|^3∂P
  let V:=∫r,|z r|^3∂Q
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let Z:=(∫r,y r∂P)*(∫r,z r∂Q)
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hC : 0≤C:=integral_nonneg fun _=>by positivity
  have hV : 0≤V:=integral_nonneg fun _=>by positivity
  have hsource : independentPairMultiplier D s a Z 1 (C+V):=by
    intro U i l G hG hdom
    have hh:=cavitySixth_independent_three_means hn D s a hq U i l G hG hdom P y hy hyb Q z hz hzb
    change |(∫r,G r∂anisotropicTrimmedRecordedTreeLaw D s a U)*Z|≤_
    simpa only [Z,one_mul,add_assoc,add_comm,add_left_comm,mul_assoc] using hh
  have hNZ : |cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z|≤M+C+V:=by
    simpa only [Z,mul_assoc,M,C,V] using
      cavityIndependent_normalizer_twoMeans_cubic_le D s a ha has hq P Q y z hy hz hyb hzb
  have hh:=independent_six_bounded_multiplier hn D s a ha has hq T F hF hFb Z 1 (C+V) (M+C+V)
    (by norm_num) (add_nonneg hC hV) hsource hNZ
  have hL : 1≤L:=by dsimp only [L];exact_mod_cast Nat.succ_le_of_lt (FiniteCascadeGenealogy.leafCount_pos (asGenealogy T))
  have hRN : M+C+V≤L^2*(M+B+C+V):=by
    have he:=mul_le_mul_of_nonneg_right (show 1≤L^2 by nlinarith) (show 0≤M+C+V by positivity)
    have hb:=mul_nonneg (sq_nonneg L) hB
    nlinarith only [he,hb]
  change |cavityMarkedSixExpectation D s a T F*(∫r,y r∂P)*(∫r,z r∂Q)|≤15*L^2*(M+B+C+V)
  rw [mul_assoc]
  exact hh.trans (by dsimp only [L] at *;nlinarith only [hRN])

end QuantitativeFollowup
