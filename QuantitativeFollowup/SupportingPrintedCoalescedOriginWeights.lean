module
public import QuantitativeFollowup.SupportingPrintedCoalescedClusterCharge

@[expose] public section

/-! Exact contraction of the genuine origin weight. Each physical root
component has its actual exit multiplicity; edges are open at both ends.
The hypotheses below are callback regularity and same-state coherence;
native moment consumers discharge them from their actual recorded laws. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeCoalescedOriginCoherent
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → (NativeStreamingOrigin T → ℝ) → Prop
  | _, .leaf, _ => True
  | _, @FiniteTerminalGenealogy.advance j T, Φ =>
      (if q (j+1) = q j then
        Φ (.vertex (.child (.root T))) = Φ (.vertex (.root T.advance))
      else Φ (.edge (.here T) (q j)) = Φ (.vertex (.child (.root T)))) ∧
      IntegrableOn (fun r => Φ (.edge (.here T) r)) (Ioc (q (j+1)) (q j))
        (parisiFreeMeasure μ a) ∧
      nativeCoalescedOriginCoherent μ a q T (fun o => Φ (nativeStreamingOriginChild o))
  | _, .fork T U, Φ =>
      Φ (.vertex (.left (.root T))) = Φ (.vertex (.root (.fork T U))) ∧
      Φ (.vertex (.right (.root U))) = Φ (.vertex (.root (.fork T U))) ∧
      nativeCoalescedOriginCoherent μ a q T (fun o => Φ (nativeStreamingOriginLeft o)) ∧
      nativeCoalescedOriginCoherent μ a q U (fun o => Φ (nativeStreamingOriginRight o))

@[reducible] def nativeCoalescedOriginResidual
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → (NativeStreamingOrigin T → ℝ) → ℝ
  | _, .leaf, _ => 0
  | _, @FiniteTerminalGenealogy.advance j T, Φ =>
      nativeCoalescedOriginResidual μ a q T (fun o => Φ (nativeStreamingOriginChild o)) +
      if q (j+1) = q j then 0 else
        ((parisiFreeMeasure μ a).real {q j} +
          ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j)) *
            Φ (.vertex (.child (.root T))) +
        ∫ r in Ioo (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a
  | _, .fork T U, Φ =>
      nativeCoalescedOriginResidual μ a q T (fun o => Φ (nativeStreamingOriginLeft o)) +
      nativeCoalescedOriginResidual μ a q U (fun o => Φ (nativeStreamingOriginRight o))

theorem nativeOrigin_integral_Ioc_split_atom (μ : Paper.ParisiMeasure) (a : ℝ)
    (lo hi : Paper.Overlap) (h : lo < hi) (f : Paper.Overlap → ℝ)
    (hf : IntegrableOn f (Ioc lo hi) (parisiFreeMeasure μ a)) :
    (∫ r in Ioc lo hi, f r ∂parisiFreeMeasure μ a) =
      (∫ r in Ioo lo hi, f r ∂parisiFreeMeasure μ a) +
      (parisiFreeMeasure μ a).real {hi} * f hi := by
  have hs : Ioc lo hi = Ioo lo hi ∪ {hi} := by
    ext x
    simp only [mem_Ioc, mem_Ioo, mem_union, mem_singleton_iff]
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx.2 with ht | he
      · exact Or.inl ⟨hx.1, ht⟩
      · exact Or.inr he
    · rintro (hx | rfl)
      · exact ⟨hx.1, hx.2.le⟩
      · exact ⟨h, le_rfl⟩
  have hd : Disjoint (Ioo lo hi) {hi} := by
    apply disjoint_left.mpr
    intro x hx he
    subst x
    exact lt_irrefl hi hx.2
  have hsub : Ioo lo hi ⊆ Ioc lo hi := fun x hx => ⟨hx.1, hx.2.le⟩
  have hat : {hi} ⊆ Ioc lo hi := by
    rintro x hx
    rw [mem_singleton_iff] at hx
    subst x
    exact ⟨h, le_rfl⟩
  rw [hs, setIntegral_union hd (measurableSet_singleton hi) (hf.mono_set hsub)
    (hf.mono_set hat), integral_singleton, smul_eq_mul]

theorem nativeOriginWeightIntegral_eq_coalesced_residual
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hq0 : q 0 = 1) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (s : ℝ) (Φ : NativeStreamingOrigin T → ℝ)
    (hΦ : nativeCoalescedOriginCoherent μ a q T Φ) :
    nativeStreamingOriginWeightIntegral μ a q T s Φ =
      nativeCoalescedOriginResidual μ a q T Φ +
      ((nativeRootClusterExits q T : ℝ)*Paper.parisiCDF μ (q j)-s)*
        Φ (.vertex (.root T)) := by
  induction T generalizing s with
  | leaf =>
      simp only [nativeStreamingOriginWeightIntegral, nativeCoalescedOriginResidual,
        nativeRootClusterExits, Nat.cast_one, one_mul, zero_add, hq0]
      rw [Paper.parisiCDF_eq_one_of_one_le μ (by norm_num)]
  | @advance j T ih =>
      obtain ⟨hc, hi, ht⟩ := hΦ
      have hh := ih (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginChild o)) ht
      by_cases hz : q (j+1) = q j
      · simp only [if_pos hz] at hc
        simp only [nativeStreamingOriginWeightIntegral, nativeCoalescedOriginResidual,
          nativeRootClusterExits, if_pos hz, hz, ite_true, Ioc_self, Measure.restrict_empty,
          integral_zero_measure, add_zero]
        rw [hh]
        change _ + _ * Φ (.vertex (.root T.advance)) = _
        rw [hc]
        ring
      · simp only [if_neg hz] at hc
        have hlt : q (j+1) < q j := lt_of_le_of_ne (hq (Nat.le_succ j)) hz
        simp only [nativeStreamingOriginWeightIntegral, nativeCoalescedOriginResidual,
          nativeRootClusterExits, if_neg hz, Nat.cast_one, one_mul]
        rw [hh, nativeOrigin_integral_Ioc_split_atom μ a _ _ hlt _ hi, hc]
        ring
  | @fork j T U ihT ihU =>
      obtain ⟨hl, hr, ht, hu⟩ := hΦ
      have ht' := ihT (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginLeft o)) ht
      have hu' := ihU (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginRight o)) hu
      simp only [nativeStreamingOriginWeightIntegral, nativeCoalescedOriginResidual,
        nativeRootClusterExits, Nat.cast_add]
      rw [ht', hu']
      change _ = _
      rw [hl, hr]
      ring

theorem nativeOriginWeightIntegral_eq_printed_coalesced
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hq0 : q 0 = 1) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (Φ : NativeStreamingOrigin T → ℝ)
    (hΦ : nativeCoalescedOriginCoherent μ a q T Φ) :
    nativeStreamingOriginWeightIntegral μ a q T (nativeCoalescedIncomingMass μ a (q j)) Φ =
      nativeCoalescedOriginResidual μ a q T Φ +
      ((parisiFreeMeasure μ a).real {q j} +
        ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j))*
          Φ (.vertex (.root T)) := by
  rw [nativeOriginWeightIntegral_eq_coalesced_residual μ a q hq hq0 T _ Φ hΦ]
  have he := nativeCoalescedIncomingMass_atom μ a ha hμ (q j)
  have hc : (nativeRootClusterExits q T : ℝ)*Paper.parisiCDF μ (q j) -
      nativeCoalescedIncomingMass μ a (q j) = (parisiFreeMeasure μ a).real {q j} +
      ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j) := by
    linear_combination he
  rw [hc]

theorem nativeCoalescedIncomingMass_zero (μ : Paper.ParisiMeasure) (a : ℝ) :
    nativeCoalescedIncomingMass μ a zeroOverlap = a := by
  have he : Iio zeroOverlap = (∅ : Set Paper.Overlap) := by
    ext x
    simp only [mem_Iio, mem_empty_iff_false, iff_false]
    exact not_lt_of_ge x.property.1
  simp only [nativeCoalescedIncomingMass, he, measureReal_empty, add_zero]

theorem nativeOriginWeightIntegral_initial_eq_printed_coalesced
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hq0 : q 0 = 1) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (hqj : q j = zeroOverlap)
    (Φ : NativeStreamingOrigin T → ℝ)
    (hΦ : nativeCoalescedOriginCoherent μ a q T Φ) :
    nativeStreamingOriginWeightIntegral μ a q T a Φ =
      nativeCoalescedOriginResidual μ a q T Φ +
      ((parisiFreeMeasure μ a).real {q j} +
        ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j))*
          Φ (.vertex (.root T)) := by
  have he := nativeOriginWeightIntegral_eq_printed_coalesced μ a ha hμ q hq hq0 T Φ hΦ
  have hs : nativeCoalescedIncomingMass μ a (q j) = a := by
    rw [hqj, nativeCoalescedIncomingMass_zero]
  simpa only [hs] using he

theorem nativeRootCluster_printed_weight_nonneg
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    0 ≤ (parisiFreeMeasure μ a).real {q j} +
      ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j) := by
  have hc : 1 ≤ nativeRootClusterExits q T := by
    rw [nativeRootCluster_exits_eq_forks_add_one]
    omega
  have hr : (1 : ℝ) ≤ nativeRootClusterExits q T := by exact_mod_cast hc
  exact add_nonneg (measureReal_nonneg) (mul_nonneg (sub_nonneg.mpr hr)
    (Paper.parisiCDF_nonneg μ (q j)))

theorem nativeRootCluster_exits_le_leaves (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    nativeRootClusterExits q T ≤ FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction T with
  | leaf => exact le_rfl
  | advance T ih =>
      simp only [nativeRootClusterExits, asGenealogy, FiniteCascadeGenealogy.leafCount]
      split
      · exact ih
      · exact FiniteCascadeGenealogy.leafCount_pos (asGenealogy T)
  | fork T U ihT ihU =>
      simp only [nativeRootClusterExits, asGenealogy, FiniteCascadeGenealogy.leafCount]
      exact Nat.add_le_add ihT ihU

theorem nativeRootCluster_printed_weight_le_atom_add_leaves
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (parisiFreeMeasure μ a).real {q j} +
      ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j) ≤
      (parisiFreeMeasure μ a).real {q j} +
        (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ) := by
  have hl : (nativeRootClusterExits q T : ℝ) ≤
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
    exact_mod_cast nativeRootCluster_exits_le_leaves q T
  have hc : 1 ≤ nativeRootClusterExits q T := by
    rw [nativeRootCluster_exits_eq_forks_add_one]
    omega
  have hr : (1 : ℝ) ≤ nativeRootClusterExits q T := by exact_mod_cast hc
  have hp := mul_le_mul_of_nonneg_left (Paper.parisiCDF_le_one μ (q j))
    (sub_nonneg.mpr hr)
  simp only [mul_one] at hp
  linarith

end QuantitativeFollowup
