module
public import QuantitativeFollowup.FollowupCavitySixTermEndpoints
public import QuantitativeFollowup.FollowupCavityStreamingCoefficientBound

@[expose] public section

/-! Uniform actual spin-defect bounds and deletion bounds for genuine marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n k : ℕ}

theorem cavitySpinOverlapDefect_abs_le_two (n:ℕ)(q:ℝ)(hq:q∈Icc (0:ℝ) 1)
    (σ τ:Configuration (n+1)) : |cavitySpinOverlapDefect n q σ τ|≤2:=by
  rw [cavitySpinOverlapDefect_eq,abs_mul,abs_mul]
  have hs (x:Bool):|Paper.spinSign x|=1:=by cases x <;> norm_num [Paper.spinSign]
  rw [hs,hs,one_mul,one_mul]
  have hi:|∑l:Fin n,Paper.spinSign (σ l.castSucc)*Paper.spinSign (τ l.castSucc)|≤(n:ℝ):=by
    calc
      _≤∑l:Fin n,|Paper.spinSign (σ l.castSucc)*Paper.spinSign (τ l.castSucc)|:=Finset.abs_sum_le_sum_abs _ _
      _=(n:ℝ):=by simp only [abs_mul,hs,one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have ha:|(∑l:Fin n,Paper.spinSign (σ l.castSucc)*Paper.spinSign (τ l.castSucc))/(n:ℝ)|≤1:=by
    by_cases hn:n=0
    · subst n;simp
    · rw [abs_div,show |(n:ℝ)|=(n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
      exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr (by simpa only [one_mul] using hi)
  exact (abs_sub _ _).trans ((add_le_add ha (by simpa only [abs_of_nonneg hq.1] using hq.2)).trans_eq (by norm_num))

theorem cavityPhysicalCommonOverlap_mem_Icc (s:RSBScheme k){j:ℕ}(T:FiniteTerminalGenealogy j)
    (v w:FiniteCascadeRecordVertex T) : cavityPhysicalCommonOverlap s T v w∈Icc (0:ℝ) 1:=
  ⟨s.q_nonneg (Nat.sub_le _ _),s.q_le_one (Nat.sub_le _ _)⟩

theorem finiteCascadeTerminalVertices_length_eq_leafCount {S:Type}{j:ℕ}
    (T:FiniteTerminalGenealogy j)(σ:TerminalSpins S T):
    (finiteCascadeTerminalVertices T σ).length=FiniteCascadeGenealogy.leafCount (asGenealogy T):=by
  induction T with
  | leaf=>rfl
  | advance T ih=>simpa only [finiteCascadeTerminalVertices,List.length_map,asGenealogy,FiniteCascadeGenealogy.leafCount] using ih σ
  | fork T U ihT ihU=>
    simp only [finiteCascadeTerminalVertices,List.length_append,List.length_map,asGenealogy,FiniteCascadeGenealogy.leafCount]
    rw [ihT,ihU]

private theorem abs_list_map_sum_le_const {A:Type}(xs:List A)(f:A→ℝ)(B:ℝ)
    (hf:∀x∈xs,|f x|≤B):|(xs.map f).sum|≤(xs.length:ℝ)*B:=by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    exact (abs_add_le _ _).trans ((add_le_add (hf x (by simp)) (ih (fun y hy=>hf y (by simp [hy])))).trans_eq (by ring))

theorem cavityOriginalVertexOverlapSum_abs_le (n:ℕ)(s:RSBScheme k)
    (T:FiniteTerminalGenealogy (k+2))(v:FiniteCascadeRecordVertex (trimRoot T))
    (σ:TerminalSpins (Configuration (n+1)) (trimRoot T))(τ:Configuration (n+1)):
    |cavityOriginalVertexOverlapSum n s T v σ τ|≤2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ):=by
  have hh:=abs_list_map_sum_le_const (finiteCascadeTerminalVertices (trimRoot T) σ)
    (fun c=>cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.1 v) c.2 τ) 2
    (fun c _=>cavitySpinOverlapDefect_abs_le_two n _ (cavityPhysicalCommonOverlap_mem_Icc s _ _ _) _ _)
  rw [finiteCascadeTerminalVertices_length_eq_leafCount,leafCount_trimRoot] at hh
  exact hh.trans_eq (by ring)

theorem cavityOriginalDistinctLeafDefect_abs_le (n:ℕ)(s:RSBScheme k)
    (T:FiniteTerminalGenealogy (k+2))(r:CavityPathRecordSpace (trimRoot T) (n+1)):
    |cavityOriginalDistinctLeafDefect n s T r|≤2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2:=by
  classical
  let xs:=finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
  have hlen:xs.length=FiniteCascadeGenealogy.leafCount (asGenealogy T):=by
    dsimp only [xs];rw [finiteCascadeTerminalVertices_length_eq_leafCount,leafCount_trimRoot]
  have hi (c:FiniteCascadeRecordVertex (trimRoot T)×Configuration (n+1)):
      |(xs.map (fun d=>if c.1=d.1 then 0 else
        cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.1 d.1) c.2 d.2)).sum|≤(xs.length:ℝ)*2:=by
    apply abs_list_map_sum_le_const
    intro d _
    split_ifs
    · norm_num
    · exact cavitySpinOverlapDefect_abs_le_two n _ (cavityPhysicalCommonOverlap_mem_Icc s _ _ _) _ _
  have hx:=abs_list_map_sum_le_const xs _ ((xs.length:ℝ)*2) (fun c _=>hi c)
  change |cavityOriginalDistinctLeafDefect n s T r|≤_ at hx
  rw [hlen] at hx
  exact hx.trans_eq (by ring)

theorem integral_marked_defect_abs_le_of_fst {A B:Type}[MeasurableSpace A][MeasurableSpace B]
    (Q:Measure (A×B))[IsFiniteMeasure Q](P:Measure A)(hP:Q.fst=P)
    (F:A→ℝ)(hF:Measurable F)(CF:ℝ)(hCF:0≤CF)(hFb:∀x,|F x|≤CF)(hF0:∀x,0≤F x)
    (G:A×B→ℝ)(hG:Measurable G)(CG:ℝ)(hCG:0≤CG)(hGb:∀x,|G x|≤CG):
    |∫x,F x.1*G x∂Q|≤CG*(∫x,F x∂P):=by
  have hiF:Integrable (fun x:A×B=>F x.1) Q:=by
    apply (integrable_const CF).mono' (hF.comp measurable_fst).aestronglyMeasurable
    exact .of_forall fun x=>by
      change ‖F x.1‖≤CF
      simpa only [Real.norm_eq_abs] using hFb x.1
  have hi:Integrable (fun x=>F x.1*G x) Q:=by
    apply (integrable_const (CF*CG)).mono' ((hF.comp measurable_fst).mul hG).aestronglyMeasurable
    exact .of_forall fun x=>by
      change ‖F x.1*G x‖≤CF*CG
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hFb x.1) (hGb x) (abs_nonneg _) hCF
  calc
    _≤∫x,|F x.1*G x|∂Q:=by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f:=fun x=>F x.1*G x)
    _≤∫x,CG*F x.1∂Q:=by
      apply integral_mono hi.norm (hiF.const_mul CG)
      intro x
      change ‖F x.1*G x‖≤CG*F x.1
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hF0 x.1)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hGb x) (hF0 x.1)
    _=CG*(∫x,F x∂P):=by
      rw [integral_const_mul,←hP]
      exact congrArg (fun z:ℝ=>CG*z) (integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable).symm

end QuantitativeFollowup
