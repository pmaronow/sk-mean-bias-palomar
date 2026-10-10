module
public import QuantitativePaper.VectorHistoryLinear
public import FourPapersCommon.HistoryBackwardPrefix

@[expose] public section

/-! Actual Gaussian reference coordinates and normalized density for every
chronological prefix of the vector path. Future fields have been integrated
out by the Markov law, rather than included in a terminal-spin tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1600000

abbrev VectorPrefixCoordinates (n N:ℕ):=(Couplings n×ℝ)×(Fin N→Field n)

def vectorPrefixHistory {n k:ℕ} (s:RSBScheme k) (β t:ℝ) (N:ℕ)
    (p:VectorPrefixCoordinates n N):FiniteHistory (VectorState n) N:=
  independentHistory (vectorCoordinateUpdate s β t) N ((p.1,0),p.2)

theorem measurable_vectorPrefixHistory {n k:ℕ} (s:RSBScheme k) (β t:ℝ) (N:ℕ):
    Measurable (vectorPrefixHistory (n:=n) s β t N):=
  (measurable_independentHistory _ (measurable_vectorCoordinateUpdate s β t) N).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

def vectorPrefixCoordinateLaw (n N:ℕ):Measure (VectorPrefixCoordinates n N):=
  (completionLaw n).prod (Measure.pi (fun _:Fin N=>fieldGaussian n))

instance vectorPrefixCoordinateLaw_probability (n N:ℕ):
    IsProbabilityMeasure (vectorPrefixCoordinateLaw n N):=by
  unfold vectorPrefixCoordinateLaw;infer_instance

theorem vectorPrefixHistory_map {n k:ℕ} (s:RSBScheme k) (β t:ℝ) (N:ℕ):
    (vectorPrefixCoordinateLaw n N).map (vectorPrefixHistory s β t N)=
      finiteHistoryLaw (vectorBaseInitialLaw n) (vectorProfileBaseKernel s β t) N:=by
  have h:=independentHistory_law (vectorBaseInitialLaw n) (fieldGaussian n)
    (vectorCoordinateUpdate s β t) (measurable_vectorCoordinateUpdate s β t)
    (vectorProfileBaseKernel s β t) (vectorProfileBaseKernel_markov s β t)
    (vectorProfileBaseKernel_eq_coordinateUpdate s β t) N
  have he:(vectorBaseInitialLaw n).prod (Measure.pi (fun _:Fin N=>fieldGaussian n))=
      (vectorPrefixCoordinateLaw n N).map (fun p=>((p.1,0),p.2)):=by
    unfold vectorBaseInitialLaw vectorPrefixCoordinateLaw
    conv_lhs=>rhs;rw [←Measure.map_id (μ:=Measure.pi (fun _:Fin N=>fieldGaussian n))]
    rw [Measure.map_prod_map _ _ (by fun_prop) measurable_id]
    rfl
  rw [he,Measure.map_map (measurable_independentHistory _
    (measurable_vectorCoordinateUpdate s β t) N)
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)] at h
  exact h

def vectorPrefixHistoryDensity {n k:ℕ} (s:RSBScheme k) (β t a:ℝ) (N:ℕ)
    (h:FiniteHistory (VectorState n) N):ℝ≥0∞:=
  vectorInitialStateWeight s β t a (h 0)*finiteHistoryDensity (vectorProfileWeight s β t) N h

theorem measurable_vectorPrefixHistoryDensity {n k:ℕ} (s:RSBScheme k) (β t a:ℝ) (N:ℕ):
    Measurable (vectorPrefixHistoryDensity (n:=n) s β t a N):=by
  unfold vectorPrefixHistoryDensity
  exact ((measurable_vectorInitialStateWeight (n:=n) s β t a).comp
    (measurable_pi_apply (0:Fin (N+1)))).mul
    (measurable_finiteHistoryDensity _ (measurable_vectorProfileWeight s β t) N)

theorem vectorPrefixHistoryLaw_eq_density {n k:ℕ} (s:RSBScheme k) (β t a:ℝ) (N:ℕ):
    finiteHistoryLaw (vectorInitialLaw (n:=n) s β t a) (vectorProfileKernel s β t) N=
      (finiteHistoryLaw (vectorBaseInitialLaw n) (vectorProfileBaseKernel s β t) N).withDensity
        (vectorPrefixHistoryDensity s β t a N):=by
  letI:=vectorOuterLaw_probability (n:=n) s β t a
  letI:IsProbabilityMeasure (vectorInitialLaw (n:=n) s β t a):=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  exact finiteHistoryLaw_withDensity_initial_and_transitions _ _ _ _
    (vectorProfileBaseKernel_markov s β t) (vectorProfileKernel_markov s β t)
    _ (measurable_vectorInitialStateWeight s β t a) (vectorInitialLaw_eq_withDensity s β t a)
    _ (measurable_vectorProfileWeight s β t) (vectorProfileKernel_eq_withDensity s β t) N

def vectorPrefixGaussianLaw {n k:ℕ} (s:RSBScheme k) (β t a:ℝ) (N:ℕ):
    Measure (VectorPrefixCoordinates n N):=
  (vectorPrefixCoordinateLaw n N).withDensity
    (fun p=>vectorPrefixHistoryDensity s β t a N (vectorPrefixHistory s β t N p))

theorem vectorPrefixGaussianLaw_map {n k:ℕ} (s:RSBScheme k) (β t a:ℝ) (N:ℕ):
    (vectorPrefixGaussianLaw (n:=n) s β t a N).map (vectorPrefixHistory s β t N)=
      finiteHistoryLaw (vectorInitialLaw s β t a) (vectorProfileKernel s β t) N:=by
  unfold vectorPrefixGaussianLaw
  rw [map_withDensity_pullback _ _ (measurable_vectorPrefixHistory s β t N) _
    (measurable_vectorPrefixHistoryDensity s β t a N),vectorPrefixHistory_map,
    vectorPrefixHistoryLaw_eq_density]

theorem vectorPrefixGaussianLaw_probability {n k:ℕ} (s:RSBScheme k) (β t a:ℝ) (N:ℕ):
    IsProbabilityMeasure (vectorPrefixGaussianLaw (n:=n) s β t a N):=by
  letI:=vectorOuterLaw_probability (n:=n) s β t a
  letI:IsProbabilityMeasure (vectorInitialLaw (n:=n) s β t a):=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  letI:=isProbabilityMeasure_finiteHistoryLaw (vectorInitialLaw (n:=n) s β t a)
    (vectorProfileKernel s β t) (vectorProfileKernel_markov s β t) N
  rw [←Measure.isProbabilityMeasure_map_iff (measurable_vectorPrefixHistory s β t N).aemeasurable,
    vectorPrefixGaussianLaw_map]
  infer_instance

private theorem integral_history_observation_reduce {State:Type*} [MeasurableSpace State]
    (ν:Measure State) [IsProbabilityMeasure ν] (κ:ℕ→Kernel State State)
    (hκ:∀j,IsMarkovKernel (κ j)) (N i:ℕ) (hi:i≤N)
    (f:State→ℝ) (hf:Measurable f) (K:ℝ) (hK:∀x,|f x|≤K):
    (∫h,f (historyObservation N i h) ∂finiteHistoryLaw ν κ N)=
      ∫h,f (h (Fin.last i)) ∂finiteHistoryLaw ν κ i:=by
  induction N with
  | zero =>
    have he:i=0:=by omega
    subst i
    simp
  | succ N ih =>
    by_cases he:i=N+1
    · subst i;simp
    · have hi':i≤N:=by omega
      exact (integral_history_observation_prefix ν κ hκ N i hi' f hf K hK).trans (ih hi')

/-- A bounded actual observable at level `N` may be averaged under its
normalized Gaussian prefix instead of the full disorder/field history. -/
theorem integral_vectorPrefixGaussianLaw_terminal {n k:ℕ} (s:RSBScheme k)
    (β t a:ℝ) (N:ℕ) (hN:N≤k+2) (f:VectorState n→ℝ)
    (hf:Measurable f) (K:ℝ) (hK:∀x,|f x|≤K):
    (∫h,f (historyObservation (k+2) N h) ∂vectorFieldHistoryLaw s β t a)=
      ∫p,f (vectorPrefixHistory s β t N p (Fin.last N)) ∂vectorPrefixGaussianLaw s β t a N:=by
  letI:=vectorOuterLaw_probability (n:=n) s β t a
  letI:IsProbabilityMeasure (vectorInitialLaw (n:=n) s β t a):=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have hh:=integral_history_observation_reduce (vectorInitialLaw (n:=n) s β t a)
    (vectorProfileKernel s β t) (vectorProfileKernel_markov s β t) (k+2) N hN f hf K hK
  rw [←vectorPrefixGaussianLaw_map s β t a N] at hh
  rw [integral_map (f:=fun h:FiniteHistory (VectorState n) N=>f (h (Fin.last N)))
    (measurable_vectorPrefixHistory s β t N).aemeasurable
    (hf.comp (measurable_pi_apply (Fin.last N))).aestronglyMeasurable] at hh
  exact hh

end QuantitativePaper
