module
public import QuantitativeFollowup.FollowupCavityMarkedMomentBounds

@[expose] public section

/-! The literal six marked terms obey the source positive-observable
bound, using genuine deletion and actual nonnegative vertex charges. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n k : ℕ}

private theorem abs_weighted_list_sum_le {A:Type}(xs:List A)(w f:A→ℝ)(B:ℝ)
    (hw:∀c∈xs,0≤w c)(hf:∀c∈xs,|f c|≤B):
    |(xs.map (fun c=>w c*f c)).sum|≤(xs.map w).sum*B:=by
  induction xs with
  | nil=>simp
  | cons c xs ih=>
    simp only [List.map_cons,List.sum_cons]
    have hc:=hw c (by simp)
    have hfc:=hf c (by simp)
    have htail:=ih (fun d hd=>hw d (by simp [hd])) (fun d hd=>hf d (by simp [hd]))
    calc
      _≤|w c*f c|+|(xs.map (fun d=>w d*f d)).sum|:=abs_add_le _ _
      _≤w c*B+(xs.map w).sum*B:=by
        rw [abs_mul,abs_of_nonneg hc]
        exact add_le_add (mul_le_mul_of_nonneg_left hfc hc) htail
      _=_:=by ring

private theorem abs_integral_mul_nonnegative_le {A:Type}[MeasurableSpace A](P:Measure A)
    (F G:A→ℝ)(hF:Integrable F P)(hi:Integrable (fun r=>F r*G r) P)
    (hF0:∀r,0≤F r)(B:ℝ)(hG:∀r,|G r|≤B):
    |∫r,F r*G r∂P|≤B*(∫r,F r∂P):=by
  calc
    _≤∫r,‖F r*G r‖∂P:=by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f:=fun r=>F r*G r)
    _≤∫r,B*F r∂P:=by
      apply integral_mono hi.norm (hF.const_mul B)
      intro r
      change ‖F r*G r‖≤B*F r
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hF0 r)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hG r) (hF0 r)
    _=_:=integral_const_mul _ _

theorem cavityMarkedSixExpectation_abs_le
    (D:AnisotropicSpinModel (n+1))(hn:0<n)(s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)
    (has:a ≤ s.m 1)(hq:s.q 1=0)(T:FiniteTerminalGenealogy (k+2))
    (F:CavityPathRecordSpace (trimRoot T) (n+1)→ℝ)(hF:Measurable F)
    (C:ℝ)(hC:0≤C)(hFb:∀r,|F r|≤C)(hF0:∀r,0≤F r):
    |cavityMarkedSixExpectation D s a T F|≤
      2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
        2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1)*
          (∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T):=by
  let P:=anisotropicTrimmedRecordedTreeLaw D s a T
  let E:ℝ:=∫r,F r∂P
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:ℝ:=(cs.map Prod.fst).sum
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  have hE:0≤E:=integral_nonneg hF0
  have hL:0≤L:=Nat.cast_nonneg _
  have hw:∀c∈cs,0≤c.1:=anisotropicTrimmedVertexCharges_nonneg s a has T
  have hW:W=L-a:=by dsimp only [W,cs,L];rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hW0:0≤W:=List.sum_nonneg (by intro x hx;obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx;exact hw c hc)
  have hWL:W≤L:=by linarith [ha.1]
  have hiF:Integrable F P:=by
    apply (integrable_const C).mono' hF.aestronglyMeasurable
    exact .of_forall fun r=>by simpa only [Real.norm_eq_abs] using hFb r
  have hi0:Integrable (fun r=>F r*cavityOriginalDistinctLeafDefect n s T r) P:=by
    have hh:=(integrable_cavityRecordedFiveTerms_mul D s a ha.1 has hq T (D.variance (Fin.last n)) F hF C hC hFb).1
    simp_rw [anisotropicReplaceVariance_self,cavityRecordedOriginalOriginalDefect_eq_distinct_leaves D hn s T] at hh
    exact hh
  have hOO:|∫r,F r*cavityOriginalDistinctLeafDefect n s T r∂P|≤2*L^2*E:=
    abs_integral_mul_nonnegative_le P F _ hiF hi0 hF0 _ (cavityOriginalDistinctLeafDefect_abs_le n s T)
  have hOF:|cavityOriginalFreshExpectation D s a T F|≤2*L*W*E:=by
    have hx:=abs_weighted_list_sum_le cs Prod.fst
      (fun c=>∫z,F z.1*cavityOriginalVertexOverlapSum n s T c.2
        (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2∂anisotropicSingleVertexMarkedLaw D s a T c.2)
      (2*L*E) hw (fun c _=>integral_cavityOriginalVertexMarked_defect_abs_le D s a T c.2 F hF C hC hFb hF0)
    exact hx.trans_eq (by ring)
  have hpair (v w:FiniteCascadeRecordVertex (trimRoot T))(q:ℝ)(hq:q∈Icc (0:ℝ) 1):
      |∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2∂anisotropicCrossVertexMarkedLaw D s a T v w|≤2*E:=
    integral_cavityCrossVertexMarked_defect_abs_le D s a T v w q hq F hF C hC hFb hF0
  have hFF:|cavityFreshFreshExpectation D s a T F|≤2*W^2*E:=by
    let J:=fun c d:ℝ×FiniteCascadeRecordVertex (trimRoot T)=>
      ∫z,F z.1*cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) z.2.1 z.2.2
        ∂anisotropicCrossVertexMarkedLaw D s a T c.2 d.2
    have hh (c:ℝ×FiniteCascadeRecordVertex (trimRoot T)):
        |(cs.map (fun d=>d.1*J c d)).sum|≤W*(2*E):=
      abs_weighted_list_sum_le cs Prod.fst (J c) (2*E) hw
        (fun d _=>hpair c.2 d.2 _ (cavityPhysicalCommonOverlap_mem_Icc s _ _ _))
    have hx:=abs_weighted_list_sum_le cs Prod.fst (fun c=>(cs.map (fun d=>d.1*J c d)).sum) (W*(2*E)) hw (fun c _=>hh c)
    have he:cavityFreshFreshExpectation D s a T F=(cs.map (fun c=>c.1*(cs.map (fun d=>d.1*J c d)).sum)).sum:=by
      unfold cavityFreshFreshExpectation
      dsimp only [cs,J]
      simp_rw [←List.sum_map_mul_left]
      congr 2
      ext c
      congr 2
      ext d
      ring
    rw [he]
    exact hx.trans_eq (by ring)
  have hCF:|cavityCurrentFreshExpectation D s a T F|≤2*W*E:=by
    have hh (c:ℝ×FiniteCascadeRecordVertex (trimRoot T)):
        |Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2)*
          (∫z,F z.1*cavitySpinOverlapDefect n (anisotropicVertexOverlap s c.2) z.2.1 z.2.2
            ∂anisotropicCrossVertexMarkedLaw D s a T c.2 c.2)|≤2*E:=by
      rw [abs_mul,abs_of_nonneg (Paper.parisiCDF_nonneg _ _)]
      exact (mul_le_mul_of_nonneg_left (hpair c.2 c.2 _ (anisotropicVertexOverlap s c.2).property)
        (Paper.parisiCDF_nonneg _ _)).trans ((mul_le_mul_of_nonneg_right (Paper.parisiCDF_le_one _ _) (by positivity)).trans_eq (by ring))
    have hx:=abs_weighted_list_sum_le cs Prod.fst _ (2*E) hw (fun c _=>hh c)
    have he:|cavityCurrentFreshExpectation D s a T F|≤W*(2*E):=by
      simpa only [cavityCurrentFreshExpectation,cs,mul_assoc] using hx
    exact he.trans_eq (by ring)
  have hmass:ν.real univ≤1:=by
    dsimp only [ν,Measure.real]
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
    linarith [ha.1]
  have hFU:|cavityFutureFreshExpectation D s a T F|≤2*W*E:=by
    have hh (c:ℝ×FiniteCascadeRecordVertex (trimRoot T)):
        |∫q:Paper.Overlap,if anisotropicVertexOverlap s c.2<q then
          (∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2∂anisotropicFutureVertexMarkedLaw D s a T c.2 q)
            else 0∂ν|≤2*E:=by
      have hx:=norm_integral_le_of_norm_le_const (μ:=ν)
        (f:=fun q:Paper.Overlap=>if anisotropicVertexOverlap s c.2<q then
          (∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2∂anisotropicFutureVertexMarkedLaw D s a T c.2 q) else 0)
        (C:=2*E) (.of_forall fun q=>by
        split_ifs
        · simpa only [Real.norm_eq_abs] using integral_cavityFutureVertexMarked_defect_abs_le D s a T c.2 q F hF C hC hFb hF0
        · simpa using (show 0≤2*E by positivity))
      rw [Real.norm_eq_abs] at hx
      exact hx.trans
        ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring))
    have hx:=abs_weighted_list_sum_le cs Prod.fst _ (2*E) hw (fun c _=>hh c)
    exact hx.trans_eq (by ring)
  have hRoot:|a*E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a|≤2*E:=by
    rw [abs_mul,abs_mul,abs_of_nonneg ha.1,abs_of_nonneg hE]
    have hx:=mul_le_mul_of_nonneg_left
      (cavityNormalizerFreshDefect_abs_le D (Paper.parisiSchemeMeasure s) a ha)
      (mul_nonneg ha.1 hE)
    have hc:a*(1-a)≤1:=by nlinarith [ha.1,ha.2]
    calc
      a*E*|cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a|
          ≤a*E*(2*(1-a)):=hx
      _=2*E*(a*(1-a)):=by ring
      _≤2*E*1:=mul_le_mul_of_nonneg_left hc (by positivity)
      _=2*E:=by ring
  have hs:|cavityMarkedSixExpectation D s a T F|≤2*(L^2+2*L*W+W^2+2*W+1)*E:=by
    let OO:=∫r,F r*cavityOriginalDistinctLeafDefect n s T r∂P
    let OF:=cavityOriginalFreshExpectation D s a T F
    let FF:=cavityFreshFreshExpectation D s a T F
    let CF:=cavityCurrentFreshExpectation D s a T F
    let FU:=cavityFutureFreshExpectation D s a T F
    let R:=a*E*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a
    have h1:=abs_sub OO (2*OF)
    rw [abs_mul,show |(2:ℝ)|=2 by norm_num] at h1
    have h2:=abs_add_le (OO-2*OF) FF
    have h3:=abs_add_le (OO-2*OF+FF) CF
    have h4:=abs_add_le (OO-2*OF+FF+CF) FU
    have h5:=abs_add_le (OO-2*OF+FF+CF+FU) R
    change |OO-2*OF+FF+CF+FU+R|≤_
    nlinarith only [h1,h2,h3,h4,h5,hOO,hOF,hFF,hCF,hFU,hRoot]
  have hc:L^2+2*L*W+W^2+2*W+1≤4*L^2+2*L+1:=by
    have hm:=mul_le_mul_of_nonneg_left hWL hL
    have hw2:W^2≤L^2:=(sq_le_sq₀ hW0 hL).mpr hWL
    nlinarith
  exact hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) hE)

end QuantitativeFollowup
