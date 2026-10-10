module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOrigin
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingBranchMass

@[expose] public section

/-! The genuine Stieltjes weight of attachment origins, before contracting
equal-time edges.  An upper endpoint atom belongs to its incoming edge;
forks carry only inherited right-CDF weights.  The incoming mass is kept
explicit, so the prescribed root atom is removed exactly once. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

@[reducible] def nativeStreamingOriginChild {j : ℕ} {T : FiniteTerminalGenealogy j} :
    NativeStreamingOrigin T → NativeStreamingOrigin T.advance
  | .vertex v => .vertex (.child v)
  | .edge e r => .edge (.child e) r

@[reducible] def nativeStreamingOriginLeft {j : ℕ} {T U : FiniteTerminalGenealogy j} :
    NativeStreamingOrigin T → NativeStreamingOrigin (.fork T U)
  | .vertex v => .vertex (.left v)
  | .edge e r => .edge (.left e) r

@[reducible] def nativeStreamingOriginRight {j : ℕ} {T U : FiniteTerminalGenealogy j} :
    NativeStreamingOrigin U → NativeStreamingOrigin (.fork T U)
  | .vertex v => .vertex (.right v)
  | .edge e r => .edge (.right e) r

@[reducible] def nativeStreamingOriginWeightIntegral
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → ℝ →
      (NativeStreamingOrigin T → ℝ) → ℝ
  | _, .leaf, s, Φ => (1-s)*Φ (.vertex (.root .leaf))
  | _, @FiniteTerminalGenealogy.advance j T, s, Φ =>
      nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginChild o)) +
      (∫r in Ioc (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a) +
      (Paper.parisiCDF μ (q (j+1))-s)*Φ (.vertex (.root T.advance))
  | j, .fork T U, s, Φ =>
      nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginLeft o)) +
      nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginRight o)) +
      (2*Paper.parisiCDF μ (q j)-s)*Φ (.vertex (.root (.fork T U)))

theorem nativeStreaming_free_real_Ioc (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (lo hi : Paper.Overlap) (hle : lo≤hi) :
    (parisiFreeMeasure μ a).real (Ioc lo hi) =
      Paper.parisiCDF μ hi-Paper.parisiCDF μ lo := by
  have hz : (zeroOverlap : Paper.Overlap)∉Ioc lo hi := by
    intro h
    have hh : (lo:ℝ)<0 := h.1
    exact (not_lt_of_ge lo.property.1) hh
  have he := congrArg (fun m : Measure Paper.Overlap => m (Ioc lo hi))
    (root_add_parisiFreeMeasure μ a ha hμ)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Ioc, Set.indicator_of_notMem hz,
    mul_zero, zero_add] at he
  change ((parisiFreeMeasure μ a) (Ioc lo hi)).toReal = _
  rw [he]
  change (μ:Measure Paper.Overlap).real (Ioc lo hi) =
    (μ:Measure Paper.Overlap).real (Iic hi)-(μ:Measure Paper.Overlap).real (Iic lo)
  have hset : Iic hi \ Iic lo = Ioc lo hi := by
    ext x
    simp only [mem_sdiff, mem_Iic, mem_Ioc, not_le, and_comm]
  rw [←hset]
  exact measureReal_sdiff (Iic_subset_Iic.mpr hle) measurableSet_Iic

theorem nativeStreamingOriginWeightIntegral_const
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s C : ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T s (fun _ => C) =
      ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C := by
  induction T generalizing s with
  | leaf => simp only [nativeStreamingOriginWeightIntegral, asGenealogy,
      FiniteCascadeGenealogy.leafCount, Nat.cast_one]
  | @advance j T ih =>
      change nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun _ => C) + (∫_ in Ioc (q (j+1)) (q j), C ∂parisiFreeMeasure μ a) +
        (Paper.parisiCDF μ (q (j+1))-s)*C = _
      rw [ih, setIntegral_const, nativeStreaming_free_real_Ioc μ a ha hμ _ _
        (hq (Nat.le_succ j))]
      simp only [smul_eq_mul]
      change _ = ((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C
      ring
  | @fork j T U ihT ihU =>
      change nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun _ => C) + nativeStreamingOriginWeightIntegral μ a q U
        (Paper.parisiCDF μ (q j)) (fun _ => C) +
        (2*Paper.parisiCDF μ (q j)-s)*C = _
      rw [ihT, ihU]
      change _ = (((FiniteCascadeGenealogy.leafCount (asGenealogy T)+
        FiniteCascadeGenealogy.leafCount (asGenealogy U):ℕ):ℝ)-s)*C
      rw [Nat.cast_add]
      ring

theorem nativeStreamingOriginWeightIntegral_zeroEdge
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (Φ : NativeStreamingOrigin T.advance → ℝ) (hq : q (j+1)=q j) :
    nativeStreamingOriginWeightIntegral μ a q T.advance s Φ =
      nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginChild o)) +
      (Paper.parisiCDF μ (q j)-s)*Φ (.vertex (.root T.advance)) := by
  simp only [nativeStreamingOriginWeightIntegral, hq, Ioc_self,
    Measure.restrict_empty, integral_zero_measure, add_zero]

theorem nativeStreamingOriginWeightIntegral_abs_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (hs : s≤Paper.parisiCDF μ (q j)) (C : ℝ) (hC : 0≤C)
    (Φ : NativeStreamingOrigin T → ℝ) (hΦ : ∀o, |Φ o|≤C) :
    |nativeStreamingOriginWeightIntegral μ a q T s Φ| ≤
      C*((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s) := by
  induction T generalizing s with
  | leaf =>
      have hs1 : s≤1 := hs.trans (Paper.parisiCDF_le_one μ (q 0))
      simp only [nativeStreamingOriginWeightIntegral, asGenealogy,
        FiniteCascadeGenealogy.leafCount, Nat.cast_one]
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs1), mul_comm C]
      exact mul_le_mul_of_nonneg_left (hΦ _) (sub_nonneg.mpr hs1)
  | @advance j T ih =>
      have hT := ih (Paper.parisiCDF μ (q j)) le_rfl
        (fun o => Φ (nativeStreamingOriginChild o)) (fun o => hΦ _)
      have he : |∫r in Ioc (q (j+1)) (q j),
          Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a| ≤
          C*(Paper.parisiCDF μ (q j)-Paper.parisiCDF μ (q (j+1))) := by
        have H := norm_setIntegral_le_of_norm_le_const
          (μ := parisiFreeMeasure μ a) (s := Ioc (q (j+1)) (q j))
          (f := fun r => Φ (.edge (.here T) r)) (C := C)
          (measure_lt_top _ _) (fun r _ => by
            simpa only [Real.norm_eq_abs] using hΦ (.edge (.here T) r))
        simpa only [Real.norm_eq_abs, nativeStreaming_free_real_Ioc μ a ha hμ _ _
          (hq (Nat.le_succ j))] using H
      have hr : |(Paper.parisiCDF μ (q (j+1))-s)*Φ (.vertex (.root T.advance))| ≤
          C*(Paper.parisiCDF μ (q (j+1))-s) := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs), mul_comm C]
        exact mul_le_mul_of_nonneg_left (hΦ _) (sub_nonneg.mpr hs)
      change |(_+_)+_|≤C*((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)
      have ht := (abs_add_le
        (nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
          (fun o => Φ (nativeStreamingOriginChild o)))
        (∫r in Ioc (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a))
      have hall := abs_add_le
        (nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
          (fun o => Φ (nativeStreamingOriginChild o)) +
          (∫r in Ioc (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a))
        ((Paper.parisiCDF μ (q (j+1))-s)*Φ (.vertex (.root T.advance)))
      nlinarith only [hT, he, hr, ht, hall]
  | @fork j T U ihT ihU =>
      have hT := ihT (Paper.parisiCDF μ (q j)) le_rfl
        (fun o => Φ (nativeStreamingOriginLeft o)) (fun o => hΦ _)
      have hU := ihU (Paper.parisiCDF μ (q j)) le_rfl
        (fun o => Φ (nativeStreamingOriginRight o)) (fun o => hΦ _)
      have hc : 0≤2*Paper.parisiCDF μ (q j)-s := by
        linarith [Paper.parisiCDF_nonneg μ (q j)]
      have hr : |(2*Paper.parisiCDF μ (q j)-s)*Φ (.vertex (.root (.fork T U)))| ≤
          C*(2*Paper.parisiCDF μ (q j)-s) := by
        rw [abs_mul, abs_of_nonneg hc, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hΦ _) hc
      change |(_+_)+_|≤C*(((FiniteCascadeGenealogy.leafCount (asGenealogy T)+
        FiniteCascadeGenealogy.leafCount (asGenealogy U):ℕ):ℝ)-s)
      rw [Nat.cast_add]
      have ht := abs_add_le
        (nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
          (fun o => Φ (nativeStreamingOriginLeft o)))
        (nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
          (fun o => Φ (nativeStreamingOriginRight o)))
      have hall := abs_add_le
        (nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
          (fun o => Φ (nativeStreamingOriginLeft o))+
          nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
            (fun o => Φ (nativeStreamingOriginRight o)))
        ((2*Paper.parisiCDF μ (q j)-s)*Φ (.vertex (.root (.fork T U))))
      nlinarith only [hT, hU, hr, ht, hall]

end QuantitativeFollowup
