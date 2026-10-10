module
public import QuantitativePaper.VectorBrownianFuture
public import Mathlib.Topology.ContinuousMap.Algebra

@[expose] public section

/-! Honest continuous splicing of an observed past with a fresh whole
Wiener path. It reconstructs the actual path from its true future increments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 600000
variable {n:ℕ}

def overlapElapsed (q t:Paper.Overlap):Paper.Overlap:=projIcc 0 1 zero_le_one ((t:ℝ)-q)

theorem continuous_overlapElapsed :Continuous (fun z:Paper.Overlap×Paper.Overlap=>overlapElapsed z.1 z.2):=by
  unfold overlapElapsed
  fun_prop

def scalarWienerSplice (q:Paper.Overlap) (W V:C(Paper.Overlap,ℝ)):C(Paper.Overlap,ℝ) where
  toFun t:=W (min t q)+V (overlapElapsed q t)-V 0
  continuous_toFun:=((W.continuous.comp (continuous_id.min continuous_const)).add
    (V.continuous.comp (continuous_overlapElapsed.comp (continuous_const.prodMk continuous_id)))).sub continuous_const

theorem continuous_scalarWienerSplice :
    Continuous (fun z:Paper.Overlap×(C(Paper.Overlap,ℝ)×C(Paper.Overlap,ℝ))=>
      scalarWienerSplice z.1 z.2.1 z.2.2):=by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z:(Paper.Overlap×(C(Paper.Overlap,ℝ)×C(Paper.Overlap,ℝ)))×Paper.Overlap=>
    z.1.2.1 (min z.2 z.1.1)+z.1.2.2 (overlapElapsed z.1.1 z.2)-z.1.2.2 0)
  have hW:Continuous (fun z:(Paper.Overlap×(C(Paper.Overlap,ℝ)×C(Paper.Overlap,ℝ)))×Paper.Overlap=>
      z.1.2.1 (min z.2 z.1.1)):=by fun_prop
  have hV:Continuous (fun z:(Paper.Overlap×(C(Paper.Overlap,ℝ)×C(Paper.Overlap,ℝ)))×Paper.Overlap=>
      z.1.2.2 (overlapElapsed z.1.1 z.2)):=
    continuous_eval.comp ((continuous_fst.snd.snd).prodMk
      (continuous_overlapElapsed.comp (continuous_fst.fst.prodMk continuous_snd)))
  have h0:Continuous (fun z:(Paper.Overlap×(C(Paper.Overlap,ℝ)×C(Paper.Overlap,ℝ)))×Paper.Overlap=>
      z.1.2.2 0):=by fun_prop
  exact (hW.add hV).sub h0

def vectorWienerSplice (q:Paper.Overlap) (W V:VectorWienerPath n):VectorWienerPath n:=
  fun i=>scalarWienerSplice q (W i) (V i)

theorem continuous_vectorWienerSplice :
    Continuous (fun z:Paper.Overlap×(VectorWienerPath n×VectorWienerPath n)=>vectorWienerSplice z.1 z.2.1 z.2.2):=by
  apply continuous_pi
  intro i
  have hm:Continuous (fun z:Paper.Overlap×(VectorWienerPath n×VectorWienerPath n)=>
      (z.1,(z.2.1 i,z.2.2 i))):=
    continuous_fst.prodMk (((continuous_apply i).comp continuous_snd.fst).prodMk
      ((continuous_apply i).comp continuous_snd.snd))
  exact continuous_scalarWienerSplice.comp hm

theorem scalarWienerSplice_actual (q:Paper.Overlap) (sample:Paper.BrownianSample):
    scalarWienerSplice q (Paper.canonicalBrownianPath sample)
      (canonicalFutureBrownianPath (q:ℝ).toNNReal sample)=Paper.canonicalBrownianPath sample:=by
  ext t
  change (Paper.canonicalBrownianPath sample) (min t q)+
    (canonicalFutureBrownianPath (q:ℝ).toNNReal sample) (overlapElapsed q t)-
      (canonicalFutureBrownianPath (q:ℝ).toNNReal sample) 0=(Paper.canonicalBrownianPath sample) t
  rw [canonicalFutureBrownianPath_zero,sub_zero]
  by_cases hqt:t≤q
  · have he:overlapElapsed q t=0:=by
      apply Subtype.ext
      simp only [overlapElapsed,projIcc_of_le_left (show (0:ℝ)≤1 from zero_le_one)
        (show (t:ℝ)-(q:ℝ)≤0 from sub_nonpos.mpr hqt)]
      rfl
    rw [min_eq_left hqt,he,canonicalFutureBrownianPath_zero,add_zero]
  · have hqtr:(q:ℝ)≤t:=le_of_lt (not_le.mp hqt)
    have he:((overlapElapsed q t:Paper.Overlap):ℝ)=(t:ℝ)-q:=by
      exact congrArg Subtype.val (projIcc_of_mem zero_le_one
        ⟨sub_nonneg.mpr hqtr,by linarith [q.property.1,t.property.2]⟩)
    rw [min_eq_right (not_le.mp hqt).le]
    change Paper.canonicalBrownian (q:ℝ).toNNReal sample+
      (Paper.canonicalBrownian ((q:ℝ).toNNReal+((overlapElapsed q t:Paper.Overlap):ℝ).toNNReal) sample-
        Paper.canonicalBrownian (q:ℝ).toNNReal sample)=Paper.canonicalBrownian (t:ℝ).toNNReal sample
    have ht: (q:ℝ).toNNReal+((overlapElapsed q t:Paper.Overlap):ℝ).toNNReal=(t:ℝ).toNNReal:=by
      apply NNReal.coe_injective
      rw [NNReal.coe_add,he,Real.coe_toNNReal _ q.property.1,
        Real.coe_toNNReal _ (sub_nonneg.mpr hqtr),Real.coe_toNNReal _ t.property.1]
      ring
    rw [ht]
    ring

theorem vectorWienerSplice_actual (q:Paper.Overlap) (sample:VectorDisorderBrownianSample n):
    vectorWienerSplice q (vectorCanonicalBrownianPath sample.2)
      (vectorFutureBrownianPath (q:ℝ).toNNReal sample)=vectorCanonicalBrownianPath sample.2:=by
  funext i
  exact scalarWienerSplice_actual q (sample.2 i)

def vectorStoppedBrownianPath (q:Paper.Overlap) (sample:VectorDisorderBrownianSample n):VectorWienerPath n:=
  fun i=>⟨fun t=>Paper.canonicalBrownian ((min t q:Paper.Overlap):ℝ).toNNReal (sample.2 i),
    (Paper.continuous_canonicalBrownian _).comp
      (continuous_real_toNNReal.comp (continuous_subtype_val.comp (continuous_id.min continuous_const)))⟩

theorem measurable_vectorStoppedBrownianPath_past (q:Paper.Overlap):
    Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] (vectorStoppedBrownianPath (n:=n) q):=by
  letI:MeasurableSpace (VectorDisorderBrownianSample n):=vectorBrownianFiltration n (q:ℝ).toNNReal
  apply Measurable.of_eval
  intro i
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  have hr:((min t q:Paper.Overlap):ℝ).toNNReal≤(q:ℝ).toNNReal:=Real.toNNReal_mono (min_le_right _ _)
  exact (EuclideanSpace.proj i).measurable.comp
    (((stronglyAdapted_disorderVectorBrownian n _).mono ((vectorBrownianFiltration n).mono hr)).measurable)

theorem vectorWienerSplice_stopped (q:Paper.Overlap) (sample:VectorDisorderBrownianSample n)
    (V:VectorWienerPath n):
    vectorWienerSplice q (vectorStoppedBrownianPath q sample) V=
      vectorWienerSplice q (vectorCanonicalBrownianPath sample.2) V:=by
  funext i
  ext t
  simp [vectorWienerSplice,scalarWienerSplice,vectorStoppedBrownianPath,
    vectorCanonicalBrownianPath,Paper.canonicalBrownianPath,min_assoc,min_self]

end QuantitativePaper
