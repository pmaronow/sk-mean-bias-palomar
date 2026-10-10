module
public import QuantitativeFollowup.FollowupCavityStreamingAtoms

@[expose] public section

/-! The actual first cavity streaming derivative is a finite polynomial
in fixed terminal-test expectations. All coefficient lists are the
literal physical vertex charges and free Stieltjes atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

abbrev CavityStreamingPolynomial (n k : ℕ) := List (ℝ×List (CavityStreamingAtom n k))

def cavityStreamingPolynomialEval (e : CavityStreamingAtom n k→ℝ)
    (P : CavityStreamingPolynomial n k) : ℝ :=
  (P.map (fun c=>c.1*(c.2.map e).prod)).sum

def cavityStreamingPolynomialBudget (P : CavityStreamingPolynomial n k) : ℝ :=
  (P.map (fun c=>|c.1| * (c.2.map CavityStreamingAtom.bound).prod)).sum

def cavityStreamingMonomialCost (xs : List (CavityStreamingAtom n k)) : ℕ :=
  (xs.map CavityStreamingAtom.complexity).sum

theorem cavityStreamingPolynomialEval_append (e : CavityStreamingAtom n k→ℝ)
    (P Q : CavityStreamingPolynomial n k) :
    cavityStreamingPolynomialEval e (P++Q)=
      cavityStreamingPolynomialEval e P+cavityStreamingPolynomialEval e Q := by
  simp only [cavityStreamingPolynomialEval,List.map_append,List.sum_append]

theorem cavityStreamingPolynomialEval_flatMap {I : Type} (e : CavityStreamingAtom n k→ℝ)
    (xs : List I) (P : I→CavityStreamingPolynomial n k) :
    cavityStreamingPolynomialEval e (xs.flatMap P)=
      (xs.map (fun i=>cavityStreamingPolynomialEval e (P i))).sum := by
  induction xs with
  | nil => simp [cavityStreamingPolynomialEval]
  | cons i xs ih =>
      simp only [List.flatMap_cons,List.map_cons,List.sum_cons,
        cavityStreamingPolynomialEval_append,ih]

theorem cavityStreamingPolynomialEval_scale (e : CavityStreamingAtom n k→ℝ)
    (P : CavityStreamingPolynomial n k) (c : ℝ) :
    cavityStreamingPolynomialEval e (P.map (fun t=>(c*t.1,t.2)))=
      c*cavityStreamingPolynomialEval e P := by
  simp only [cavityStreamingPolynomialEval,List.map_map,Function.comp_def]
  simp_rw [mul_assoc]
  exact List.sum_map_mul_left _ _ _

def cavityStreamingAtomResponseUnscaled (s : RSBScheme k) (a : ℝ)
    (A : CavityStreamingAtom n k) : CavityStreamingPolynomial n k := by
  classical
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot A.tree)
  let is:=(Finset.univ : Finset (vectorPosteriorFeatureIndex k)).toList
  exact [(1,[A.originalOriginal s])] ++
    cs.map (fun c=>(-2*c.1,[A.originalFresh s c.2])) ++
    cs.flatMap (fun c=>cs.map (fun d=>(c.1*d.1,[A.cross c.2 d.2
      (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot A.tree) c.2 d.2))]))) ++
    cs.map (fun c=>(c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2),
      [A.cross c.2 c.2 (anisotropicVertexOverlap s c.2)])) ++
    cs.flatMap (fun c=>is.flatMap (fun i=>
      if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then
        [(c.1*vectorPosteriorFeatureWeight s a i,[A.future s c.2 (vectorProfileAtom s i)])]
      else [])) ++
    is.map (fun i=>(a*vectorPosteriorFeatureWeight s a i,[A,cavityStreamingNormalizerAtom n s i]))

def cavityStreamingAtomResponse (β ρ : ℝ) (s : RSBScheme k) (a : ℝ)
    (A : CavityStreamingAtom n k) : CavityStreamingPolynomial n k :=
  (cavityStreamingAtomResponseUnscaled s a A).map
    (fun c=>(followupCavityAlpha n β ρ/2*c.1,c.2))

private theorem response_eval_future_cell (e : CavityStreamingAtom n k→ℝ)
    (s : RSBScheme k) (a : ℝ) (A : CavityStreamingAtom n k)
    (c : ℝ×FiniteCascadeRecordVertex (trimRoot A.tree))
    (i : vectorPosteriorFeatureIndex k) :
    cavityStreamingPolynomialEval e
      (if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then
        [(c.1*vectorPosteriorFeatureWeight s a i,[A.future s c.2 (vectorProfileAtom s i)])]
      else [])=
      c.1*(vectorPosteriorFeatureWeight s a i*
        (if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then
          e (A.future s c.2 (vectorProfileAtom s i)) else 0)) := by
  classical
  split_ifs <;> simp only [cavityStreamingPolynomialEval,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.prod_cons,List.prod_nil,mul_one,add_zero,mul_zero,mul_assoc]

theorem cavityStreamingAtomResponseUnscaled_eval
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (A : CavityStreamingAtom n k) (u : ℝ) :
    cavityStreamingPolynomialEval (fun B=>B.eval β ρ hβ hρ s a u)
      (cavityStreamingAtomResponseUnscaled s a A)=
      followupCavityStreamingBracket n β ρ hβ hρ s a A.tree A.test u := by
  classical
  let e:=fun B : CavityStreamingAtom n k=>B.eval β ρ hβ hρ s a u
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot A.tree)
  let is:=(Finset.univ : Finset (vectorPosteriorFeatureIndex k)).toList
  have hf : cavityStreamingPolynomialEval e (cs.flatMap (fun c=>is.flatMap (fun i=>
      if anisotropicVertexOverlap s c.2<vectorProfileAtom s i then
        [(c.1*vectorPosteriorFeatureWeight s a i,[A.future s c.2 (vectorProfileAtom s i)])]
      else [])))=
      followupCavityFutureGraftStreamingExpectation n β ρ hβ hρ s a A.tree
        (cavityFullTestToTerminal A.tree A.test) u := by
    rw [cavityStreamingPolynomialEval_flatMap]
    simp_rw [cavityStreamingPolynomialEval_flatMap,response_eval_future_cell,
      List.sum_map_mul_left]
    unfold followupCavityFutureGraftStreamingExpectation followupCavityFutureGraftStieltjesExpectation
    simp only [is,Finset.sum_map_toList]
    rfl
  have hn : cavityStreamingPolynomialEval e
      (is.map (fun i=>(a*vectorPosteriorFeatureWeight s a i,[A,cavityStreamingNormalizerAtom n s i])))=
      followupCavitySixthGraftExpectation n β ρ hβ hρ s a A.tree A.test u := by
    simp only [cavityStreamingPolynomialEval,List.map_map,Function.comp_def,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    change (is.map (fun i=>(a*vectorPosteriorFeatureWeight s a i)*
      (followupCavityPhysicalExpectation n β ρ hβ hρ s a A.tree A.test u*
        followupCavityNormalizerGraftPairExpectation n β ρ hβ hρ s a i u))).sum=_
    have he (i : vectorPosteriorFeatureIndex k) :
        (a*vectorPosteriorFeatureWeight s a i)*
          (followupCavityPhysicalExpectation n β ρ hβ hρ s a A.tree A.test u*
            followupCavityNormalizerGraftPairExpectation n β ρ hβ hρ s a i u)=
        (a*followupCavityPhysicalExpectation n β ρ hβ hρ s a A.tree A.test u)*
          (vectorPosteriorFeatureWeight s a i*followupCavityNormalizerGraftPairExpectation n β ρ hβ hρ s a i u) := by ring
    simp_rw [he,List.sum_map_mul_left]
    simp only [is,Finset.sum_map_toList]
    rfl
  have ho : cavityStreamingPolynomialEval e
      (cs.map (fun c=>(-2*c.1,[A.originalFresh s c.2])))=
      -2*followupCavityOriginalGraftFamily n β ρ hβ hρ s a A.tree
        (cavityFullTestToTrim A.tree A.test) u := by
    simp only [cavityStreamingPolynomialEval,List.map_map,Function.comp_def,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc,List.sum_map_mul_left]
    rfl
  have hc : cavityStreamingPolynomialEval e (cs.flatMap (fun c=>cs.map (fun d=>(c.1*d.1,
      [A.cross c.2 d.2 (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot A.tree) c.2 d.2))]))))=
      followupCavityCrossGraftFamily n β ρ hβ hρ s a A.tree
        (cavityFullTestToTrim A.tree A.test) u := by
    rw [cavityStreamingPolynomialEval_flatMap]
    simp only [cavityStreamingPolynomialEval,List.map_map,Function.comp_def,List.map_cons,
      List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc,List.sum_map_mul_left]
    rfl
  unfold cavityStreamingAtomResponseUnscaled
  simp only [cavityStreamingPolynomialEval_append]
  change cavityStreamingPolynomialEval e [(1,[A.originalOriginal s])]+_+_+_+_+_=_
  rw [hf,hn,ho,hc]
  simp only [cavityStreamingPolynomialEval,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,List.sum_cons,List.sum_nil,mul_one,one_mul,add_zero,List.map_map,Function.comp_def]
  change followupCavityOriginalOriginalSampleExpectation n β ρ hβ hρ s a A.tree
      (cavityFullTestToTrim A.tree A.test) u+
    -2*followupCavityOriginalGraftFamily n β ρ hβ hρ s a A.tree (cavityFullTestToTrim A.tree A.test) u+
    followupCavityCrossGraftFamily n β ρ hβ hρ s a A.tree (cavityFullTestToTrim A.tree A.test) u+
    followupCavityCurrentGraftFamily n β ρ hβ hρ s a A.tree (cavityFullTestToTrim A.tree A.test) u+
    followupCavityFutureGraftStreamingExpectation n β ρ hβ hρ s a A.tree (cavityFullTestToTerminal A.tree A.test) u+
    followupCavitySixthGraftExpectation n β ρ hβ hρ s a A.tree A.test u=_
  unfold followupCavityStreamingBracket
  ring

theorem hasDerivWithinAt_cavityStreamingAtom_eval
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (A : CavityStreamingAtom n k) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (A.eval β ρ hβ hρ s a)
      (cavityStreamingPolynomialEval (fun B=>B.eval β ρ hβ hρ s a u)
        (cavityStreamingAtomResponse β ρ s a A)) (Icc (0:ℝ) 1) u := by
  rw [cavityStreamingAtomResponse,cavityStreamingPolynomialEval_scale,
    cavityStreamingAtomResponseUnscaled_eval]
  exact hasDerivWithinAt_followupCavityPhysicalExpectation_streamingBracket hn β ρ hβ hρ s a ha has hq A.tree A.test u hu

end QuantitativeFollowup
