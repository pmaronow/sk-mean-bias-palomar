module
public import FourPapersCommon.EndpointFixedL2Density

@[expose] public section

/-! Actual orthogonal endpoint compression in L² of an arbitrary overlap
measure. Endpoint atoms are removed from the output by a measurable
indicator, with operator norm at most one. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

def endpointInteriorIndicator (f : Paper.Overlap→ℝ) : Paper.Overlap→ℝ :=
  overlapEndpointSetᶜ.indicator f

theorem endpointInteriorIndicator_norm_le (f : Paper.Overlap→ℝ) (q : Paper.Overlap) :
    ‖endpointInteriorIndicator f q‖ ≤ ‖f q‖ := by
  by_cases hq : q∈overlapEndpointSetᶜ
  · simp [endpointInteriorIndicator,hq]
  · simp [endpointInteriorIndicator,hq]

theorem memLp_endpointInteriorIndicator (ν : Measure Paper.Overlap) (f : Lp ℝ 2 ν) :
    MemLp (endpointInteriorIndicator f) 2 ν :=
  (Lp.memLp f).indicator measurableSet_overlapEndpointSet.compl

def endpointInteriorLp (ν : Measure Paper.Overlap) (f : Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  (memLp_endpointInteriorIndicator ν f).toLp (endpointInteriorIndicator f)

theorem endpointInteriorLp_coeFn (ν : Measure Paper.Overlap) (f : Lp ℝ 2 ν) :
    endpointInteriorLp ν f=ᵐ[ν] endpointInteriorIndicator f :=
  (memLp_endpointInteriorIndicator ν f).coeFn_toLp

theorem endpointInteriorLp_mem (ν : Measure Paper.Overlap) (f : Lp ℝ 2 ν) :
    endpointInteriorLp ν f∈endpointFixedL2 ν := by
  rw [mem_endpointFixedL2_iff]
  filter_upwards [endpointInteriorLp_coeFn ν f] with q hq
  intro he
  rw [hq]
  apply indicator_of_notMem
  exact fun h=>h he

def endpointFixedL2Compression (ν : Measure Paper.Overlap) :
    Lp ℝ 2 ν→L[ℝ]endpointFixedL2 ν :=
  ({toFun:=fun f=>⟨endpointInteriorLp ν f,endpointInteriorLp_mem ν f⟩
    map_add':=by
      intro f g
      apply Subtype.ext
      change endpointInteriorLp ν (f+g)=endpointInteriorLp ν f+endpointInteriorLp ν g
      apply Lp.ext
      filter_upwards [endpointInteriorLp_coeFn ν (f+g),endpointInteriorLp_coeFn ν f,
        endpointInteriorLp_coeFn ν g,Lp.coeFn_add f g,
        Lp.coeFn_add (endpointInteriorLp ν f) (endpointInteriorLp ν g)] with q hfg hf hg hadd hout
      simp only [hfg,hout,Pi.add_apply,hf,hg,endpointInteriorIndicator]
      by_cases hq : q∈overlapEndpointSetᶜ
      · simp only [indicator_of_mem hq,hadd,Pi.add_apply]
      · simp only [indicator_of_notMem hq,zero_add]
    map_smul':=by
      intro c f
      apply Subtype.ext
      change endpointInteriorLp ν (c • f)=c • endpointInteriorLp ν f
      apply Lp.ext
      filter_upwards [endpointInteriorLp_coeFn ν (c • f),endpointInteriorLp_coeFn ν f,
        Lp.coeFn_smul c f,Lp.coeFn_smul c (endpointInteriorLp ν f)] with q hcf hf hin hout
      simp only [hcf,hout,Pi.smul_apply,hf,endpointInteriorIndicator]
      by_cases hq : q∈overlapEndpointSetᶜ
      · simp only [indicator_of_mem hq,hin,Pi.smul_apply]
      · simp only [indicator_of_notMem hq,smul_zero]
    } : Lp ℝ 2 ν→ₗ[ℝ]endpointFixedL2 ν).mkContinuous 1 (fun f=>by
      change ‖endpointInteriorLp ν f‖ ≤ 1*‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [endpointInteriorLp_coeFn ν f] with q hq
      rw [hq,one_mul]
      exact endpointInteriorIndicator_norm_le f q)

theorem endpointFixedL2Compression_coeFn (ν : Measure Paper.Overlap) (f : Lp ℝ 2 ν) :
    (endpointFixedL2Compression ν f : Lp ℝ 2 ν)=ᵐ[ν] endpointInteriorIndicator f :=
  endpointInteriorLp_coeFn ν f

theorem endpointFixedL2Compression_norm_le (ν : Measure Paper.Overlap) (f : Lp ℝ 2 ν) :
    ‖endpointFixedL2Compression ν f‖ ≤ ‖f‖ := by
  apply (show ‖endpointInteriorLp ν f‖ ≤ 1*‖f‖ from Lp.norm_le_mul_norm_of_ae_le_mul ?_).trans_eq (one_mul _)
  filter_upwards [endpointInteriorLp_coeFn ν f] with q hq
  rw [hq,one_mul]
  exact endpointInteriorIndicator_norm_le f q

theorem endpointFixedL2Compression_id (ν : Measure Paper.Overlap) (f : endpointFixedL2 ν) :
    endpointFixedL2Compression ν f.val=f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [endpointFixedL2Compression_coeFn ν f.val,
    (mem_endpointFixedL2_iff ν f.val).mp f.property] with q hq hf
  rw [hq]
  by_cases he : q∈overlapEndpointSet
  · rw [hf he]
    simp [endpointInteriorIndicator,he]
  · simp [endpointInteriorIndicator,he]

end FourPapersCommon
