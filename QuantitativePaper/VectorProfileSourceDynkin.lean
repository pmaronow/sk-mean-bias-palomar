module
public import QuantitativePaper.VectorProfileCellDynkin
public import QuantitativePaper.VectorProfileFieldSourceValues

@[expose] public section

/-! Actual unbounded profile-source Dynkin identities on strict cells.
The generic adapter isolates deterministic equation and envelope inputs;
the three concrete model instances below discharge them. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfile_source_dynkin
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (F H : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀l u A B : ℝ,s₀.q i≤l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (hEq : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,p) x=H ((q,θ,p),x))
    (a b : ℝ≥0) (hab : a≤b) (haq : s₀.q i<(a:ℝ)) (hbq : (b:ℝ)<s₀.q (i+1)) :
    let s:=vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩
    let X:=vectorFiniteState (n:=n) s β t ht.le
    let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t outer
    let S : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>H ((r,θ,sample.1),X r sample)
    Integrable (Function.uncurry S) ((nonnegativeLebesgueMeasure.restrict (Ioc a b)).prod P) ∧
      (∫sample,F ((b,θ,sample.1),X b sample)-F ((a,θ,sample.1),X a sample) ∂P)=
        ∫sample,(∫r in Ioc a b,S r sample ∂nonnegativeLebesgueMeasure) ∂P := by
  let l:=(s₀.q i+a)/2
  let u:=(b+s₀.q (i+1))/2
  let A:=θ/2
  let B:=(θ+1)/2
  have hl : s₀.q i≤l:=by dsimp [l];linarith
  have hu : u<s₀.q (i+1):=by dsimp [u];linarith
  have hA : 0<A:=by dsimp [A];linarith [hθ.1]
  have hB : B<1:=by dsimp [B];linarith [hθ.2]
  have hθAB : θ∈Ioo A B:=by dsimp [A,B];constructor <;>linarith [hθ.1,hθ.2]
  have hla : l<(a:ℝ):=by dsimp [l];linarith
  have hbu : (b:ℝ)<u:=by dsimp [u];linarith
  have hb : b≤1:=by exact_mod_cast hbq.le.trans (s₀.q_le_one (by omega))
  let s:=vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩
  let X:=vectorFiniteState (n:=n) s β t ht.le
  let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t outer
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc a b)
  let G : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    vectorProfileCellFieldGenerator s₀ s₁ β t i F (r,θ,sample.1) (X r sample)
  let S : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>H ((r,θ,sample.1),X r sample)
  obtain ⟨hInt,hId⟩:=vectorProfile_cell_dynkin_of_exponentialSmooth s₀ s₁ β t outer θ ht i hi
    l u A B hl hu hA hB hθAB F (hGrowth l u A B hl hu hA hB) a b hab hb hla hbu
  have hGS (r : ℝ≥0) (hr : r∈Ioc a b) (sample : VectorDisorderBrownianSample n) : G r sample=S r sample:=
    hEq r ⟨haq.trans hr.1,lt_of_le_of_lt hr.2 hbq⟩ sample.1 (X r sample)
  have hMem : ∀ᵐz ∂ν.prod P,z.1∈Ioc a b:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact .of_forall fun _=>hr
  have hIntS : Integrable (Function.uncurry S) (ν.prod P):=hInt.congr (by
    filter_upwards [hMem] with z hz
    exact hGS z.1 hz z.2)
  have he : (∫sample,(∫r in Ioc a b,G r sample ∂nonnegativeLebesgueMeasure) ∂P)=
      ∫sample,(∫r in Ioc a b,S r sample ∂nonnegativeLebesgueMeasure) ∂P:=by
    apply integral_congr_ae
    exact .of_forall fun sample=>setIntegral_congr_fun measurableSet_Ioc
      (fun r hr=>hGS r hr sample)
  exact ⟨hIntS,hId.trans he⟩

end QuantitativePaper
