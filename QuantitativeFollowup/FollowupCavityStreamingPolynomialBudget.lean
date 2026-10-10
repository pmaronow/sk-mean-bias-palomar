module
public import QuantitativeFollowup.FollowupCavityStreamingPolynomial
public import QuantitativeFollowup.FollowupCavityStreamingCoefficientBound
public import FourPapersCommon.FiniteStreamingPolynomialsBudget

@[expose] public section

/-! Exact depth-independent complexity and absolute coefficient budgets
for the concrete six-branch physical cavity response polynomial. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem cavityStreamingBudget_sum_map_congr {I : Type} (xs : List I) (f g : I→ℝ)
    (h : ∀i∈xs,f i=g i) : (xs.map f).sum=(xs.map g).sum:=
  congrArg List.sum (List.map_congr_left h)

 theorem cavityStreamingPolynomialBudget_append (P Q : CavityStreamingPolynomial n k) :
    cavityStreamingPolynomialBudget (P++Q)=
      cavityStreamingPolynomialBudget P+cavityStreamingPolynomialBudget Q:=by
  simp only [cavityStreamingPolynomialBudget,List.map_append,List.sum_append]

 theorem cavityStreamingPolynomialBudget_flatMap {I : Type} (xs : List I)
    (P : I→CavityStreamingPolynomial n k) :
    cavityStreamingPolynomialBudget (xs.flatMap P)=
      (xs.map (fun i=>cavityStreamingPolynomialBudget (P i))).sum:=by
  induction xs with
  | nil=>simp [cavityStreamingPolynomialBudget]
  | cons i xs ih=>simp only [List.flatMap_cons,List.map_cons,List.sum_cons,
      cavityStreamingPolynomialBudget_append,ih]

 theorem cavityStreamingPolynomialBudget_scale (P : CavityStreamingPolynomial n k) (c : ℝ) :
    cavityStreamingPolynomialBudget (P.map (fun t=>(c*t.1,t.2)))=
      |c| * cavityStreamingPolynomialBudget P:=by
  simp only [cavityStreamingPolynomialBudget,List.map_map,Function.comp_def,abs_mul,mul_assoc]
  exact List.sum_map_mul_left _ _ _

 theorem cavityStreamingAtomResponse_cost (β ρ : ℝ) (s : RSBScheme k) (a : ℝ)
    (A : CavityStreamingAtom n k) (term : ℝ×List (CavityStreamingAtom n k))
    (ht : term∈cavityStreamingAtomResponse β ρ s a A) :
    cavityStreamingMonomialCost term.2 ≤ A.complexity+2 := by
  classical
  change term∈(cavityStreamingAtomResponseUnscaled s a A).map
    (fun c=>(followupCavityAlpha n β ρ/2*c.1,c.2)) at ht
  obtain ⟨t,hm,he⟩:=List.mem_map.mp ht
  have hs:=congrArg (fun z : ℝ×List (CavityStreamingAtom n k)=>z.2) he.symm
  change term.2=t.2 at hs
  rw [hs]
  simp only [cavityStreamingAtomResponseUnscaled,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,List.mem_map,List.mem_flatMap] at hm
  rcases hm with ((((ht|ht)|ht)|ht)|ht)|ht
  · rcases ht with rfl
    simp [cavityStreamingMonomialCost]
  · obtain ⟨c,_,rfl⟩:=ht
    simp [cavityStreamingMonomialCost]
  · obtain ⟨c,_,d,_,rfl⟩:=ht
    simp [cavityStreamingMonomialCost]
  · obtain ⟨c,_,rfl⟩:=ht
    simp [cavityStreamingMonomialCost]
  · obtain ⟨c,_,i,_,ht⟩:=ht
    split_ifs at ht with hi
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl
      simp [cavityStreamingMonomialCost]
    · simp only [List.not_mem_nil] at ht
  · obtain ⟨i,_,rfl⟩:=ht
    simp [cavityStreamingMonomialCost]

 private theorem budget_future_cell (s : RSBScheme k) (a : ℝ)
    (A : CavityStreamingAtom n k) (c : ℝ×FiniteCascadeRecordVertex (trimRoot A.tree))
    (i : vectorPosteriorFeatureIndex k) (hc : 0≤c.1) (has : a ≤ s.m 1) :
    cavityStreamingPolynomialBudget
      (if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then
        [(c.1*vectorPosteriorFeatureWeight s a i,[A.future s c.2 (vectorProfileAtom s i)])]
      else [])=
    (2*A.bound)*c.1*(vectorPosteriorFeatureWeight s a i*
      (if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then (1:ℝ) else 0)):=by
  split_ifs <;> simp only [cavityStreamingPolynomialBudget,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.prod_cons,List.prod_nil,CavityStreamingAtom.future,
    mul_one,add_zero,mul_zero,abs_of_nonneg
      (mul_nonneg hc (vectorPosteriorFeatureWeight_nonneg s a has i))] <;> ring

 theorem cavityStreamingAtomResponseUnscaled_budget_eq (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (A : CavityStreamingAtom n k) :
    cavityStreamingPolynomialBudget (cavityStreamingAtomResponseUnscaled s a A)=
      (2*A.bound)*cavityStreamingCoefficientEnvelope s a A.tree:=by
  classical
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot A.tree)
  let is:=(Finset.univ:Finset (vectorPosteriorFeatureIndex k)).toList
  let L:ℝ:=A.complexity
  let W:ℝ:=(cs.map Prod.fst).sum
  let C:ℝ:=A.bound
  have hc : ∀c∈cs,0≤c.1:=anisotropicTrimmedVertexCharges_nonneg s a has A.tree
  have hOF : cavityStreamingPolynomialBudget (cs.map (fun c=>(-2*c.1,[A.originalFresh s c.2])))=
      4*L*W*C:=by
    simp only [cavityStreamingPolynomialBudget,List.map_map,Function.comp_def,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,mul_one,CavityStreamingAtom.originalFresh]
    have he : (cs.map (fun c=>|-2*c.1| * (2*(A.complexity:ℝ)*A.bound))).sum=
        (cs.map (fun c=>c.1*(4*L*C))).sum:=by
      apply cavityStreamingBudget_sum_map_congr
      intro c hcc
      rw [abs_mul,abs_of_nonneg (hc c hcc)]
      norm_num
      dsimp only [L,C]
      ring
    rw [he,List.sum_map_mul_right]
    dsimp only [W]
    ring
  have hFF : cavityStreamingPolynomialBudget (cs.flatMap (fun c=>cs.map (fun d=>(c.1*d.1,
      [A.cross c.2 d.2 (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot A.tree) c.2 d.2))]))))=
      2*W^2*C:=by
    rw [cavityStreamingPolynomialBudget_flatMap]
    have he (c : ℝ×FiniteCascadeRecordVertex (trimRoot A.tree)) (hcc : c∈cs) :
        cavityStreamingPolynomialBudget (cs.map (fun d=>(c.1*d.1,
          [A.cross c.2 d.2 (cavityProfileLevel s
            (finiteCascadeCommonPathDepth (trimRoot A.tree) c.2 d.2))])))=c.1*W*(2*C):=by
      simp only [cavityStreamingPolynomialBudget,List.map_map,Function.comp_def,List.map_cons,
        List.map_nil,List.prod_cons,List.prod_nil,mul_one,CavityStreamingAtom.cross]
      have hh : (cs.map (fun d=>|c.1*d.1| * (2*A.bound))).sum=
          (cs.map (fun d=>d.1*(c.1*(2*C)))).sum:=by
        apply cavityStreamingBudget_sum_map_congr
        intro d hdd
        rw [abs_of_nonneg (mul_nonneg (hc c hcc) (hc d hdd))]
        dsimp only [C]
        ring
      rw [hh,List.sum_map_mul_right]
      dsimp only [W]
      ring
    have hh : (cs.map (fun c=>cavityStreamingPolynomialBudget (cs.map (fun d=>(c.1*d.1,
        [A.cross c.2 d.2 (cavityProfileLevel s
          (finiteCascadeCommonPathDepth (trimRoot A.tree) c.2 d.2))]))))).sum=
        (cs.map (fun c=>c.1*(W*(2*C)))).sum:=by
      apply cavityStreamingBudget_sum_map_congr
      intro c hcc
      rw [he c hcc]
      ring
    rw [hh,List.sum_map_mul_right]
    dsimp only [W]
    ring
  have hCurr : cavityStreamingPolynomialBudget (cs.map (fun c=>(c.1*
      Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2),
      [A.cross c.2 c.2 (anisotropicVertexOverlap s c.2)])))=
      (2*C)*(cs.map (fun c=>c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s)
        (anisotropicVertexOverlap s c.2))).sum:=by
    simp only [cavityStreamingPolynomialBudget,List.map_map,Function.comp_def,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,mul_one,CavityStreamingAtom.cross]
    rw [←List.sum_map_mul_left]
    apply cavityStreamingBudget_sum_map_congr
    intro c hcc
    rw [abs_of_nonneg (mul_nonneg (hc c hcc) (Paper.parisiCDF_nonneg _ _))]
    dsimp only [C]
    ring
  have hFut : cavityStreamingPolynomialBudget (cs.flatMap (fun c=>is.flatMap (fun i=>
      if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then
        [(c.1*vectorPosteriorFeatureWeight s a i,[A.future s c.2 (vectorProfileAtom s i)])]
      else [])))=
      (2*C)*(cs.map (fun c=>c.1*(∫q : Paper.Overlap,
        if anisotropicVertexOverlap s c.2<q then (1:ℝ) else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum:=by
    rw [cavityStreamingPolynomialBudget_flatMap,←List.sum_map_mul_left]
    apply cavityStreamingBudget_sum_map_congr
    intro c hcc
    rw [cavityStreamingPolynomialBudget_flatMap]
    have he : (is.map (fun i=>cavityStreamingPolynomialBudget
      (if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then
        [(c.1*vectorPosteriorFeatureWeight s a i,[A.future s c.2 (vectorProfileAtom s i)])]
      else []))).sum=
        (2*C)*c.1*(is.map (fun i=>vectorPosteriorFeatureWeight s a i*
          (if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then (1:ℝ) else 0))).sum:=by
      simp_rw [budget_future_cell s a A c _ (hc c hcc) has,List.sum_map_mul_left]
      rfl
    rw [he,←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq,
      integral_vectorProfileFreeMeasure s a has]
    simp only [is,Finset.sum_map_toList]
    dsimp only [C]
    ring
  have hSix : cavityStreamingPolynomialBudget (is.map (fun i=>(a*vectorPosteriorFeatureWeight s a i,
      [A,cavityStreamingNormalizerAtom n s i])))=
      (2*C)*a*(parisiFreeMeasure (Paper.parisiSchemeMeasure s) a).real univ:=by
    simp only [cavityStreamingPolynomialBudget,List.map_map,Function.comp_def,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,mul_one,cavityStreamingNormalizerAtom]
    have he : (is.map (fun i=>|a*vectorPosteriorFeatureWeight s a i| * (A.bound*2))).sum=
        (2*C)*a*(is.map (vectorPosteriorFeatureWeight s a)).sum:=by
      rw [←List.sum_map_mul_left]
      apply cavityStreamingBudget_sum_map_congr
      intro i _
      rw [abs_of_nonneg (mul_nonneg ha.1 (vectorPosteriorFeatureWeight_nonneg s a has i))]
      dsimp only [C]
      ring
    rw [he]
    have hmass : (is.map (vectorPosteriorFeatureWeight s a)).sum=
        (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a).real univ:=by
      have he:=integral_vectorProfileFreeMeasure s a has (fun _ : Paper.Overlap=>(1:ℝ))
      rw [vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq] at he
      simpa only [integral_const,smul_eq_mul,mul_one,is,Finset.sum_map_toList] using he.symm
    rw [hmass]
  unfold cavityStreamingAtomResponseUnscaled
  simp only [cavityStreamingPolynomialBudget_append]
  change cavityStreamingPolynomialBudget [(1,[A.originalOriginal s])]+_+_+_+_+_=_
  rw [hOF,hFF,hCurr,hFut,hSix]
  simp only [cavityStreamingPolynomialBudget,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.prod_cons,List.prod_nil,mul_one,one_mul,abs_one,add_zero,CavityStreamingAtom.originalOriginal]
  unfold cavityStreamingCoefficientEnvelope
  change 2*L^2*C+4*L*W*C+2*W^2*C+(2*C)*_+(2*C)*_+(2*C)*a*_= (2*C)*(L^2+2*L*W+W^2+_+_+a*_)
  ring

 theorem cavityStreamingAtomResponse_budget_le (β ρ : ℝ) (hρ : ρ∈Icc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1)
    (hq : s.q 1=0) (A : CavityStreamingAtom n k) :
    cavityStreamingPolynomialBudget (cavityStreamingAtomResponse β ρ s a A) ≤
      7*β^2*(A.complexity:ℝ)^2*A.bound:=by
  let L:ℝ:=A.complexity
  let C:ℝ:=A.bound
  let α:=followupCavityAlpha n β ρ
  let E:=cavityStreamingCoefficientEnvelope s a A.tree
  have hC : 0≤C:=A.bound_nonneg
  have hL : 1≤L:=by
    change (1:ℝ)≤(A.complexity:ℝ)
    exact_mod_cast (Nat.succ_le_iff.mpr A.complexity_pos)
  have hα0 : 0≤α:=followupCavityAlpha_nonneg n β ρ hρ.2
  have hα : α≤β^2:=by
    dsimp only [α,followupCavityAlpha]
    apply (div_le_iff₀ (by positivity : 0<(n:ℝ)+1)).mpr
    calc
      β^2*(1-ρ)*(n:ℝ) ≤ β^2*1*(n:ℝ):=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith [hρ.1] : 1-ρ≤1) (sq_nonneg β))
          (Nat.cast_nonneg n)
      _≤β^2*((n:ℝ)+1):=by nlinarith [sq_nonneg β]
  have hE : E≤7*L^2:=by
    have he:=(cavityStreamingCoefficientEnvelope_nonneg_le s a ha has A.tree).2
    change E≤4*L^2+2*L+1 at he
    have hLL : L≤L^2:=by nlinarith
    have h1 : 1≤L^2:=by nlinarith
    nlinarith
  rw [cavityStreamingAtomResponse,cavityStreamingPolynomialBudget_scale,
    abs_of_nonneg (div_nonneg hα0 (by norm_num)),
    cavityStreamingAtomResponseUnscaled_budget_eq s a ha has hq A]
  change α/2*((2*C)*E) ≤ 7*β^2*L^2*C
  calc
    α/2*((2*C)*E)=α*C*E:=by ring
    _≤α*C*(7*L^2):=mul_le_mul_of_nonneg_left hE (mul_nonneg hα0 hC)
    _≤β^2*C*(7*L^2):=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hα hC) (by positivity)
    _=7*β^2*L^2*C:=by ring

 theorem cavityStreamingMonomialCost_eq_finiteStreaming (xs : List (CavityStreamingAtom n k)) :
    cavityStreamingMonomialCost xs=
      FiniteStreamingPolynomials.monoCost CavityStreamingAtom.complexity xs:=rfl

 theorem cavityStreamingPolynomialBudget_eq_finiteStreaming (P : CavityStreamingPolynomial n k) :
    cavityStreamingPolynomialBudget P=
      FiniteStreamingPolynomials.budget CavityStreamingAtom.bound P:=rfl

 theorem cavityStreamingAtomResponse_costBound (β ρ : ℝ) (s : RSBScheme k) (a : ℝ)
    (A : CavityStreamingAtom n k) :
    FiniteStreamingPolynomials.costBound CavityStreamingAtom.complexity (A.complexity+2)
      (cavityStreamingAtomResponse β ρ s a A):=by
  intro term ht
  exact cavityStreamingAtomResponse_cost β ρ s a A term ht

 theorem cavityStreamingAtomResponse_finiteStreaming_budget_le (β ρ : ℝ)
    (hρ : ρ∈Icc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (A : CavityStreamingAtom n k) :
    FiniteStreamingPolynomials.budget CavityStreamingAtom.bound
      (cavityStreamingAtomResponse β ρ s a A) ≤ 7*β^2*(A.complexity:ℝ)^2*A.bound:=
  cavityStreamingAtomResponse_budget_le β ρ hρ s a ha has hq A

end QuantitativeFollowup
