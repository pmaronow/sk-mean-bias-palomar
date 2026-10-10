module
public import QuantitativePaper.VectorPrefixLogDensity
public import FourPapersCommon.GaussianCoordinateSplit

@[expose] public section

/-! The actual prefix Gaussian law in standard Euclidean coordinates, ready
for conditioning on incident-site coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

abbrev VectorPrefixGaussianIndex (n N:ℕ):=Option (Edge n)⊕(Fin N×Fin n)
abbrev VectorPrefixGaussianSpace (n N:ℕ):=EuclideanSpace ℝ (VectorPrefixGaussianIndex n N)

def prefixFlatFields (n N:ℕ) (z:Fin N×Fin n→ℝ):Fin N→Field n:=
  fun j=>WithLp.toLp 2 (fun i=>z (j,i))

theorem measurable_prefixFlatFields (n N:ℕ):Measurable (prefixFlatFields n N):=by
  unfold prefixFlatFields
  apply Measurable.of_eval
  intro j
  fun_prop

theorem prefixFlatFields_map (n N:ℕ):
    (Measure.pi (fun _:Fin N×Fin n=>gaussianReal 0 1)).map (prefixFlatFields n N)=
      Measure.pi (fun _:Fin N=>fieldGaussian n):=by
  have hc:(Measure.pi (fun _:Fin N×Fin n=>gaussianReal 0 1)).map
      (MeasurableEquiv.curry (Fin N) (Fin n) ℝ)=
        Measure.pi (fun _:Fin N=>Measure.pi (fun _:Fin n=>gaussianReal 0 1)):=by
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun _:Fin N=>fun _:Fin n=>gaussianReal 0 1)
  have hf:prefixFlatFields n N=
      (fun z:Fin N→(Fin n→ℝ)=>fun j=>WithLp.toLp 2 (z j))∘
        MeasurableEquiv.curry (Fin N) (Fin n) ℝ:=rfl
  rw [hf,←Measure.map_map (by fun_prop) (MeasurableEquiv.curry _ _ _).measurable,hc,
    Measure.pi_map_pi (fun _=>by fun_prop)]
  rfl

def prefixRawCoordinates (n N:ℕ) (z:VectorPrefixGaussianIndex n N→ℝ):
    VectorPrefixCoordinates n N:=
  (flatCompletionCoordinates n (fun i=>z (.inl i)),prefixFlatFields n N (fun i=>z (.inr i)))

theorem measurable_prefixRawCoordinates (n N:ℕ):Measurable (prefixRawCoordinates n N):=
  ((measurable_flatCompletionCoordinates n).comp (Measurable.of_eval fun _=>measurable_pi_apply _)).prodMk
    ((measurable_prefixFlatFields n N).comp (Measurable.of_eval fun _=>measurable_pi_apply _))

theorem prefixRawCoordinates_map (n N:ℕ):
    (Measure.pi (fun _:VectorPrefixGaussianIndex n N=>gaussianReal 0 1)).map
      (prefixRawCoordinates n N)=vectorPrefixCoordinateLaw n N:=by
  let e:=MeasurableEquiv.sumPiEquivProdPi (fun _:VectorPrefixGaussianIndex n N=>ℝ)
  have he:=(measurePreserving_sumPiEquivProdPi
    (fun _:VectorPrefixGaussianIndex n N=>gaussianReal 0 1)).map_eq
  have hf:prefixRawCoordinates n N=
      (Prod.map (flatCompletionCoordinates n) (prefixFlatFields n N))∘e:=rfl
  rw [hf,←Measure.map_map ((measurable_flatCompletionCoordinates n).prodMap
    (measurable_prefixFlatFields n N)) e.measurable,he,←Measure.map_prod_map _ _
      (measurable_flatCompletionCoordinates n) (measurable_prefixFlatFields n N),
    flatCompletionCoordinates_map,prefixFlatFields_map]
  rfl

def vectorPrefixEuclideanCoordinates (n N:ℕ):
    VectorPrefixGaussianSpace n N→L[ℝ]VectorPrefixCoordinates n N:=
  ((ContinuousLinearMap.pi fun e:Edge n=>EuclideanSpace.proj (.inl (some e))).prod
    (Real.sqrt (1/2:ℝ) • EuclideanSpace.proj (.inl none))).prod
    (ContinuousLinearMap.pi fun j:Fin N=>
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin n=>ℝ)).symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.pi fun i:Fin n=>EuclideanSpace.proj (.inr (j,i))))

theorem vectorPrefixEuclideanCoordinates_map (n N:ℕ):
    (SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N)).map
      (vectorPrefixEuclideanCoordinates n N)=vectorPrefixCoordinateLaw n N:=by
  unfold SYK.standardGaussianMeasureOnEuclidean
  rw [Measure.map_map (vectorPrefixEuclideanCoordinates n N).measurable (by fun_prop)]
  exact prefixRawCoordinates_map n N

def vectorPrefixEuclideanHistory {n k:ℕ} (s:RSBScheme k) (β t:ℝ) (N:ℕ):
    VectorPrefixGaussianSpace n N→L[ℝ](Fin (N+1)→VectorState n):=
  (independentHistoryLinear (vectorCoordinateUpdateLinear s β t) N).comp
    ((((ContinuousLinearMap.fst ℝ (Couplings n×ℝ) (Fin N→Field n)).prod
      (0:VectorPrefixCoordinates n N→L[ℝ]Field n)).prod
        (ContinuousLinearMap.snd ℝ (Couplings n×ℝ) (Fin N→Field n))).comp
          (vectorPrefixEuclideanCoordinates n N))

theorem vectorPrefixEuclideanHistory_apply {n k:ℕ} (s:RSBScheme k) (β t:ℝ)
    (N:ℕ) (z:VectorPrefixGaussianSpace n N):
    vectorPrefixEuclideanHistory s β t N z=
      vectorPrefixHistory s β t N (vectorPrefixEuclideanCoordinates n N z):=by
  unfold vectorPrefixEuclideanHistory
  rw [ContinuousLinearMap.comp_apply,independentHistoryLinear_apply]
  simp_rw [vectorCoordinateUpdateLinear_apply]
  rfl

def vectorPrefixEuclideanLaw {n k:ℕ} (s:RSBScheme k) (β t a:ℝ) (N:ℕ):
    Measure (VectorPrefixGaussianSpace n N):=
  (SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N)).withDensity
    (fun z=>vectorPrefixHistoryDensity s β t a N (vectorPrefixEuclideanHistory s β t N z))

theorem vectorPrefixEuclideanLaw_map {n k:ℕ} (s:RSBScheme k) (β t a:ℝ) (N:ℕ):
    (vectorPrefixEuclideanLaw (n:=n) s β t a N).map (vectorPrefixEuclideanCoordinates n N)=
      vectorPrefixGaussianLaw s β t a N:=by
  unfold vectorPrefixEuclideanLaw
  simp_rw [vectorPrefixEuclideanHistory_apply]
  have hm:=map_withDensity_pullback
    (SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N))
    (vectorPrefixEuclideanCoordinates n N) (vectorPrefixEuclideanCoordinates n N).measurable
    (fun p=>vectorPrefixHistoryDensity s β t a N (vectorPrefixHistory s β t N p))
    ((measurable_vectorPrefixHistoryDensity s β t a N).comp
      (measurable_vectorPrefixHistory s β t N))
  rw [vectorPrefixEuclideanCoordinates_map] at hm
  exact hm

end QuantitativePaper
