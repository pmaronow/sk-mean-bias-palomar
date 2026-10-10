module
public import QuantitativeFollowup.FollowupCavitySixthSecondResponseCubicIndependent
public import QuantitativeFollowup.FollowupCavityFutureGraftCubicBudget
public import QuantitativeFollowup.FollowupCavityCurrentGraftCubicBudget

@[expose] public section

/-! Actual marked streaming terms retain cubic order when multiplied by
one independently sampled bounded defect. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavitySixth_future_mark_independent_cubic {Ω : Type*} [MeasurableSpace Ω]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) (hlevel : cavityProfileLevel s (cavityFiniteFutureDepth s v.depth q)=q)
    (i l : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (z : Ω→ℝ) (hz : Measurable z) (hzb : ∀ω,|z ω|≤2) :
    |(∫r,F r.1*cavitySpinOverlapDefect n q r.2.1 r.2.2
        ∂anisotropicFutureVertexMarkedLaw D s a T v q)*(∫ω,z ω∂Q)|≤
      2*finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
        (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q))+(∫ω,|z ω|^3∂Q) := by
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
  rw [hm]
  apply cavitySixth_independent_pair_cubic hn D s a hq (.advance (finiteCascadeFutureVertexGraft v p))
    (cavityFutureSecondPairFirst T v p i) (cavityFutureSecondPairLast T v p l) (H∘e) (hH.comp he) _ Q z hz hzb
  intro r
  rw [cavityFutureSecondPairProduct_record s T v p (cavityFiniteFutureDepth_le s v.depth q),hlevel]
  dsimp only [H,e,Function.comp_def]
  rw [abs_mul,abs_mul]
  exact mul_le_mul_of_nonneg_right (hdom (r.1,(finiteCascadeFutureGraftExtract v p r.2).1)) (abs_nonneg _)

private theorem sixth_sum_constant {A : Type*} (xs : List A) (C : ℝ) :
    (xs.map (fun _=>C)).sum=(xs.length:ℝ)*C := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.cast_add,Nat.cast_one];ring

private theorem sixth_weighted_affine {A : Type*} (xs : List (ℝ×A)) (f : A→ℝ) (C : ℝ) :
    (xs.map (fun c=>c.1*(2*f c.2+C))).sum=
      2*(xs.map (fun c=>c.1*f c.2)).sum+(xs.map Prod.fst).sum*C := by
  simp_rw [mul_add]
  rw [List.sum_map_add,List.sum_map_mul_right]
  have he : (fun c : ℝ×A=>c.1*(2*f c.2))=fun c=>2*(c.1*f c.2):=funext fun _=>by ring
  rw [he,List.sum_map_mul_left]

/-- Every source in the literal Six operator is kept under its genuine
marked law, including the third independent normalizer mark. -/
theorem cavityMarkedSix_onePair_independent_cubic_le {Ω : Type*} [MeasurableSpace Ω]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (z : Ω→ℝ) (hz : Measurable z) (hzb : ∀ω,|z ω|≤2) :
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |cavityMarkedSixExpectation D s a T F*(∫ω,z ω∂Q)|≤
      60*L^2*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
        finiteCascadeUnweightedBranchSum
          (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)+
        (∫ω,|z ω|^3∂Q)) := by
  dsimp only
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let f:=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
  let M:=cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (trimRoot T)
  let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let C:=∫ω,|z ω|^3∂Q
  let Z:=∫ω,z ω∂Q
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:=(cs.map Prod.fst).sum
  have hM : 0≤M:=integral_nonneg fun q=>(cavityCubicPairMoment_bounds D _ a q).1
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) _
  have hC : 0≤C:=integral_nonneg fun ω=>by positivity
  have hL : 1≤L:=by dsimp only [L]; exact_mod_cast Nat.succ_le_of_lt (FiniteCascadeGenealogy.leafCount_pos (asGenealogy T))
  have hW : W=L-a:=by dsimp only [W,cs,L];rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hWL : W≤L:=by rw [hW];linarith [ha.1]
  have hW0 : 0≤W:=by rw [hW];linarith [ha.2]
  have hFb (r) : |F r|≤2:=(hdom r).trans (cavityRecordedLeafPairDefect_abs_le_two s (trimRoot T) i l r.2)
  have hiν (g : Paper.Overlap→ℝ) : Integrable g ν:=by
    dsimp only [ν];rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a g
  have hm : ν.real univ=1-a:=by
    change (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a univ).toReal=1-a
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
  have hOO : |(∫r,F r*cavityOriginalDistinctLeafDefect n s T r∂anisotropicTrimmedRecordedTreeLaw D s a T)*Z|≤L^2*(2*B+C) := by
    let P:=anisotropicTrimmedRecordedTreeLaw D s a T
    let xs:=observationLeaves (trimRoot T)
    let H:=fun j h r=>F r*cavityRecordedLeafPairDefect s (trimRoot T) j h r.2
    have hi (j h : ObservationLeaf (trimRoot T)) : Integrable (H j h) P:=
      integrable_bounded_pair_mul_cavityDefect P F hF (fun r=>(hFb r).trans (by norm_num : (2:ℝ)≤4))
        _ _ ((measurable_observationLeafSpin _ j).comp measurable_snd) ((measurable_observationLeafSpin _ h).comp measurable_snd) _
    have he (r) : F r*cavityOriginalDistinctLeafDefect n s T r=(xs.map (fun j=>(xs.map (fun h=>H j h r)).sum)).sum:=by
      rw [cavityOriginalDistinctLeafDefect_eq_leaves hn D s T r,←List.sum_map_mul_left]
      apply congrArg List.sum;apply List.map_congr_left;intro j _;rw [←List.sum_map_mul_left]
    simp_rw [he]
    rw [integral_list_map_sum_real P xs _ (fun j=>integrable_list_map_sum_real P xs _ (hi j))]
    simp_rw [integral_list_map_sum_real P xs _ (hi _)]
    rw [←List.sum_map_mul_right]
    have hh:=abs_list_sum_le xs
      (fun j=>(xs.map (fun h=>∫r,H j h r∂P)).sum*Z)
      (fun _=>(xs.map (fun _=>2*B+C)).sum) (fun j _=>by
      rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro h _
      apply cavitySixth_independent_pair_cubic hn D s a hq T ![i,j] ![l,h] (H j h)
      · exact hF.mul ((measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) j h).comp measurable_snd)
      · intro r;rw [abs_mul];simp only [cavityRecordedPairProduct,Matrix.cons_val_zero,Matrix.cons_val_one,abs_mul]
        exact mul_le_mul_of_nonneg_right (hdom r) (abs_nonneg _)
      · exact hz
      · exact hzb)
    simp only [sixth_sum_constant,xs,observationLeaves_length,leafCount_trimRoot] at hh
    exact hh.trans_eq (by dsimp only [L];ring)
  have hOF : |cavityOriginalFreshExpectation D s a T F*Z|≤2*L^2*(M+2*B)+L^2*C := by
    have hv (v : FiniteCascadeRecordVertex (trimRoot T)) :
        |(∫r,F r.1*cavityOriginalVertexOverlapSum n s T v (finiteCascadeRecordTerminalSpins (trimRoot T) r.1.2) r.2
          ∂anisotropicSingleVertexMarkedLaw D s a T v)*Z|≤L*(2*finiteCascadeUnweightedBranchSum
          (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft v)+C) := by
      let P:=anisotropicSingleVertexMarkedLaw D s a T v
      let xs:=observationLeaves (trimRoot T)
      let H:=fun j (r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1))=>
        F r.1*cavitySpinOverlapDefect n (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v)) (observationLeafSpin (trimRoot T) j r.1.2) r.2
      have hi (j : ObservationLeaf (trimRoot T)) : Integrable (H j) P:=
        integrable_bounded_pair_mul_cavityDefect P _ (hF.comp measurable_fst) (fun r=>(hFb r.1).trans (by norm_num : (2:ℝ)≤4))
          _ _ ((measurable_observationLeafSpin _ j).comp (measurable_snd.comp measurable_fst)) measurable_snd _
      have he (r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)) :
          F r.1*cavityOriginalVertexOverlapSum n s T v (finiteCascadeRecordTerminalSpins (trimRoot T) r.1.2) r.2=(xs.map (fun j=>H j r)).sum:=by
        rw [cavityOriginalVertexOverlapSum_eq_leaves,←List.sum_map_mul_left]
      simp_rw [he]
      rw [integral_list_map_sum_real P xs H hi,←List.sum_map_mul_right]
      have hh:=abs_list_sum_le xs _ (fun _=>2*finiteCascadeUnweightedBranchSum
        (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft v)+C)
        (fun j _=>cavitySixth_single_mark_independent_cubic hn D s a hq T v i l j F hF hdom Q z hz hzb)
      simpa only [sixth_sum_constant,xs,observationLeaves_length,leafCount_trimRoot,L] using hh
    have hh : |cavityOriginalFreshExpectation D s a T F*Z|≤
        (cs.map (fun c=>c.1*(L*(2*finiteCascadeUnweightedBranchSum
          (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2)+C)))).sum:=by
      unfold cavityOriginalFreshExpectation;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro c hc
      rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
      exact mul_le_mul_of_nonneg_left (hv c.2) (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    have he : (cs.map (fun c=>c.1*(L*(2*finiteCascadeUnweightedBranchSum
        (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2)+C)))).sum=
        L*(2*cavityChargedGraftBranchBudget s a T f+W*C):=by
      have hfun : (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>c.1*(L*(2*finiteCascadeUnweightedBranchSum
        (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2)+C)))=
        fun c=>L*(c.1*(2*finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft c.2)+C)):=funext fun _=>by ring
      rw [hfun,List.sum_map_mul_left,
        sixth_weighted_affine cs (fun v : FiniteCascadeRecordVertex (trimRoot T)=>
          finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeVertexGraft v)) C]
      rfl
    rw [he] at hh
    have hb:=cavityChargedGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    change _≤L*(M+2*B) at hb
    have hc:=mul_le_mul_of_nonneg_right hWL hC
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hb (show 0≤L by linarith),mul_le_mul_of_nonneg_left hc (show 0≤L by linarith)])
  have hFF : |cavityFreshFreshExpectation D s a T F*Z|≤2*L^2*(2*M+3*B)+L^2*C := by
    have hh : |cavityFreshFreshExpectation D s a T F*Z|≤
        (cs.map (fun c=>(cs.map (fun d=>c.1*d.1*(2*finiteCascadeUnweightedBranchSum
          (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft c.2 d.2)+C))).sum)).sum:=by
      unfold cavityFreshFreshExpectation;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro c hc;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro d hd
      rw [mul_assoc,abs_mul,abs_of_nonneg (mul_nonneg
        (anisotropicTrimmedVertexCharges_nonneg s a has T c hc) (anisotropicTrimmedVertexCharges_nonneg s a has T d hd))]
      exact mul_le_mul_of_nonneg_left (cavitySixth_cross_mark_independent_cubic hn D s a hq T c.2 d.2 i l F hF hdom Q z hz hzb)
        (mul_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc) (anisotropicTrimmedVertexCharges_nonneg s a has T d hd))
    have he : (cs.map (fun c=>(cs.map (fun d=>c.1*d.1*(2*finiteCascadeUnweightedBranchSum
          (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft c.2 d.2)+C))).sum)).sum=
        2*cavityChargedCrossGraftBranchBudget s a T f+W^2*C:=by
      simp_rw [mul_add,List.sum_map_add]
      have hp : (cs.map (fun c=>(cs.map (fun d=>c.1*d.1*(2*finiteCascadeUnweightedBranchSum
        (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft c.2 d.2)))).sum)).sum=
        2*cavityChargedCrossGraftBranchBudget s a T f:=by
        unfold cavityChargedCrossGraftBranchBudget
        simp_rw [←List.sum_map_mul_left]
        apply congrArg List.sum;apply List.map_congr_left;intro c _
        change (cs.map (fun d=>c.1*d.1*(2*finiteCascadeUnweightedBranchSum
          (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft c.2 d.2)))).sum=
          (cs.map (fun d=>2*(c.1*(d.1*finiteCascadeUnweightedBranchSum
            (fun h=>f (cavityProfileLevel s h)) (finiteCascadeCrossVertexGraft c.2 d.2))))).sum
        apply congrArg List.sum;apply List.map_congr_left;intro d _;ring
      rw [hp]
      have hc (c : ℝ×FiniteCascadeRecordVertex (trimRoot T)) : (cs.map (fun d=>c.1*d.1*C)).sum=c.1*(W*C):=by
        have heq : (fun d : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>c.1*d.1*C)=fun d=>d.1*(c.1*C):=funext fun _=>by ring
        rw [heq,List.sum_map_mul_right];dsimp only [W];ring
      simp_rw [hc];rw [List.sum_map_mul_right];dsimp only [W];ring
    rw [he] at hh
    have hb:=cavityChargedCrossGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    change _≤L^2*(2*M+3*B) at hb
    have hw2 : W^2≤L^2:=(sq_le_sq₀ hW0 (by linarith)).mpr hWL
    exact hh.trans (by nlinarith only [hb,mul_le_mul_of_nonneg_right hw2 hC])
  have hCF : |cavityCurrentFreshExpectation D s a T F*Z|≤2*L*(2*M+3*B)+L*C := by
    have hh : |cavityCurrentFreshExpectation D s a T F*Z|≤
        (cs.map (fun c=>c.1*(2*finiteCascadeUnweightedBranchSum
          (fun d=>f (cavityProfileLevel s d)) (finiteCascadeCrossVertexGraft c.2 c.2)+C))).sum:=by
      unfold cavityCurrentFreshExpectation;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro c hc
      have hc0:=anisotropicTrimmedVertexCharges_nonneg s a has T c hc
      have hlev : anisotropicVertexOverlap s c.2=cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2:=by
        rw [anisotropicVertexOverlap_eq_cross_self,cavityPhysicalCommonOverlap_eq_profileLevel]
      rw [hlev,mul_assoc,abs_mul,abs_of_nonneg (mul_nonneg hc0 (Paper.parisiCDF_nonneg _ _))]
      calc
        _≤c.1*1*|(_ : ℝ)*Z|:=by gcongr;exact Paper.parisiCDF_le_one _ _
        _≤_:=by
          simpa only [mul_one] using (mul_le_mul_of_nonneg_left
            (cavitySixth_cross_mark_independent_cubic hn D s a hq T c.2 c.2 i l F hF hdom Q z hz hzb) hc0)
    rw [sixth_weighted_affine cs (fun v : FiniteCascadeRecordVertex (trimRoot T)=>
      finiteCascadeUnweightedBranchSum (fun d=>f (cavityProfileLevel s d)) (finiteCascadeCrossVertexGraft v v)) C] at hh
    change _≤2*cavityChargedCurrentGraftBranchBudget s a T f+W*C at hh
    have hb:=cavityChargedCurrentGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    change _≤L*(2*M+3*B) at hb
    exact hh.trans (by nlinarith only [hb,mul_le_mul_of_nonneg_right hWL hC])
  have hFU : |cavityFutureFreshExpectation D s a T F*Z|≤4*L*(M+B)+L*C := by
    let G:=fun (v : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap)=>finiteCascadeUnweightedBranchSum
      (fun d=>f (cavityProfileLevel s d)) (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q))
    let H:=fun v=>∫q : Paper.Overlap,if cavityProfileLevel s v.depth<q then G v q else 0∂ν
    have hv (v : FiniteCascadeRecordVertex (trimRoot T)) :
        |(∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
          (∫r,F r.1*cavitySpinOverlapDefect n q r.2.1 r.2.2∂anisotropicFutureVertexMarkedLaw D s a T v q)
          else 0∂ν)*Z|≤2*H v+C := by
      let A:=fun q : Paper.Overlap=>if anisotropicVertexOverlap s v<q then
        (∫r,F r.1*cavitySpinOverlapDefect n q r.2.1 r.2.2∂anisotropicFutureVertexMarkedLaw D s a T v q) else 0
      rw [←integral_mul_const]
      have hb : (∫q,|A q*Z|∂ν)≤∫q,2*(if cavityProfileLevel s v.depth<q then G v q else 0)+C∂ν:=by
        apply integral_mono_ae (hiν _) (hiν _)
        filter_upwards [ae_cavityFiniteFutureDepth_level s a ha.1 has hq v.depth
          (v.depth_le.trans (by omega : k+1≤k+2))] with q hlev
        by_cases hvq : cavityProfileLevel s v.depth<q
        · dsimp only [A];rw [if_pos (show anisotropicVertexOverlap s v<q from hvq),if_pos hvq]
          exact cavitySixth_future_mark_independent_cubic hn D s a hq T v q (hlev hvq) i l F hF hdom Q z hz hzb
        · dsimp only [A];rw [if_neg (show ¬anisotropicVertexOverlap s v<q from hvq),if_neg hvq,zero_mul,abs_zero]
          simpa only [mul_zero,zero_add] using hC
      rw [integral_add (hiν _) (hiν _),integral_const_mul,integral_const,hm] at hb
      exact abs_integral_le_integral_abs.trans (hb.trans (by change 2*H v+(1-a)*C≤2*H v+C;nlinarith [mul_nonneg ha.1 hC]))
    have hh : |cavityFutureFreshExpectation D s a T F*Z|≤(cs.map (fun c=>c.1*(2*H c.2+C))).sum:=by
      unfold cavityFutureFreshExpectation;rw [←List.sum_map_mul_right]
      apply abs_list_sum_le;intro c hc
      rw [mul_assoc,abs_mul,abs_of_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)]
      exact mul_le_mul_of_nonneg_left (hv c.2) (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    rw [sixth_weighted_affine cs H C] at hh
    change _≤2*cavityChargedFutureGraftBranchBudget s a T f+W*C at hh
    have hb:=cavityChargedFutureGraftBranchBudget_le s a ha has hq T f (fun q=>(cavityCubicPairMoment_bounds D _ a q).1)
    change _≤2*L*(M+B) at hb
    exact hh.trans (by nlinarith only [hb,mul_le_mul_of_nonneg_right hWL hC])
  have hR : |a*(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z|≤B+M+C := by
    let E:=∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T
    let A:=fun q : Paper.Overlap=>E*(∫r,cavitySpinOverlapDefect n q r.2.1 r.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q)*Z
    have hbq (q) : |A q|≤B+f q+C:=by
      let P:=(anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q).snd
      let y:=fun r : Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n q r.1 r.2
      have hh:=cavitySixth_independent_three_means hn D s a hq T i l F hF hdom P y
        (measurable_of_finite _) (fun r=>cavitySpinOverlapDefect_abs_le_two n q q.property r.1 r.2) Q z hz hzb
      have he : (∫r,y r∂P)=∫r,cavitySpinOverlapDefect n q r.2.1 r.2.2∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q:=
        integral_map measurable_snd.aemeasurable (measurable_of_finite y).aestronglyMeasurable
      have hc : (∫r,|y r|^3∂P)=f q:=by
        dsimp only [f]
        rw [cavityCubicPairMoment_eq_fresh]
        simp only [P,y,cavitySpinOverlapDefect_abs_eq_rest]
      rw [he,hc] at hh;exact hh
    have hh:=abs_integral_le_integral_abs.trans (integral_mono (hiν _) (hiν _) hbq)
    have he : (∫q,A q∂ν)=E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z:=by
      dsimp only [A,cavityNormalizerFreshDefect,E];rw [integral_mul_const,integral_const_mul]
    rw [he,integral_add (hiν _) (hiν _),integral_add (hiν _) (hiν _),integral_const,integral_const,hm] at hh
    change |E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z|≤(1-a)*B+M+(1-a)*C at hh
    have hbudget : (1-a)*B+M+(1-a)*C≤B+M+C:=by nlinarith [mul_nonneg ha.1 hB,mul_nonneg ha.1 hC]
    have hwhole:=hh.trans hbudget
    rw [show a*E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z=
      a*(E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a*Z) by ring,abs_mul,abs_of_nonneg ha.1]
    exact (mul_le_mul_of_nonneg_left hwhole ha.1).trans (mul_le_of_le_one_left (by positivity) ha.2)
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
  have hLsq : L≤L^2:=by nlinarith
  have hLB : L*B≤L^2*B:=mul_le_mul_of_nonneg_right hLsq hB
  have hLM : L*M≤L^2*M:=mul_le_mul_of_nonneg_right hLsq hM
  have hLC : L*C≤L^2*C:=mul_le_mul_of_nonneg_right hLsq hC
  have hB2 : B≤L^2*B:=by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 1≤L^2 by nlinarith) hB
  have hM2 : M≤L^2*M:=by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 1≤L^2 by nlinarith) hM
  have hC2 : C≤L^2*C:=by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 1≤L^2 by nlinarith) hC
  change |OO-2*OF+FF+CF+FU+R|≤60*L^2*(M+B+C)
  nlinarith only [h1,h2,h3,h4,h5,hOO,hOF,hFF,hCF,hFU,hR,hLB,hLM,hLC,hB2,hM2,hC2,
    mul_nonneg (sq_nonneg L) hM,mul_nonneg (sq_nonneg L) hB,mul_nonneg (sq_nonneg L) hC]

end QuantitativeFollowup
