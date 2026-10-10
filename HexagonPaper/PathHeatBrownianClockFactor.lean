module
public import HexagonPaper.PathHeatBrownianClockReindex
public import HexagonPaper.PathHeatClockPrefix

@[expose] public section

/-! Identification of actual finite independent canonical Wiener clocks
with the explicit independent-increment Gaussian factor. The coefficients
are the true clock increments and fixed cumulative-coordinate masks. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
namespace HexagonPaper
open Paper FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {j n : ℕ}

def pathHeatBrownianClockVariance
    (c : ℝ → Fin j → Fin (n+1) → Paper.Overlap) (z : ℝ) (α : Fin (j*n)) : ℝ :=
  (c z (finProdFinEquiv.symm α).1 (finProdFinEquiv.symm α).2.succ : ℝ)-
    (c z (finProdFinEquiv.symm α).1 (finProdFinEquiv.symm α).2.castSucc : ℝ)

def pathHeatBrownianClockMask (α : Fin (j*n)) : QuantitativePaper.Field (j*(n+1)) :=
  WithLp.toLp 2 (fun p =>
    if (finProdFinEquiv.symm α).1=(finProdFinEquiv.symm p).1 ∧
      (finProdFinEquiv.symm α).2.val<(finProdFinEquiv.symm p).2.val then 1 else 0)

@[simp] theorem pathHeatBrownianClockVariance_pair
    (c : ℝ → Fin j → Fin (n+1) → Paper.Overlap) (z : ℝ) (a : Fin j) (i : Fin n) :
    pathHeatBrownianClockVariance c z (finProdFinEquiv (a,i)) =
      (c z a i.succ : ℝ)-(c z a i.castSucc : ℝ) := by
  simp [pathHeatBrownianClockVariance]

@[simp] theorem pathHeatBrownianClockMask_pair (a k : Fin j) (i : Fin n)
    (l : Fin (n+1)) :
    pathHeatBrownianClockMask (finProdFinEquiv (a,i)) (finProdFinEquiv (k,l)) =
      if a=k ∧ i.val<l.val then 1 else 0 := by
  change (if (finProdFinEquiv.symm (finProdFinEquiv (a,i))).1 =
    (finProdFinEquiv.symm (finProdFinEquiv (k,l))).1 ∧
    (finProdFinEquiv.symm (finProdFinEquiv (a,i))).2.val <
    (finProdFinEquiv.symm (finProdFinEquiv (k,l))).2.val then (1 : ℝ) else 0) = _
  simp only [Equiv.symm_apply_apply]

theorem pathHeatBrownianClockVariance_nonnegative
    (c : ℝ → Fin j → Fin (n+1) → Paper.Overlap) (z : ℝ)
    (hc : ∀ a, Monotone (c z a)) (α : Fin (j*n)) :
    0 ≤ pathHeatBrownianClockVariance c z α := by
  unfold pathHeatBrownianClockVariance
  apply sub_nonneg.mpr
  exact hc _ (by simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ];omega)

theorem pathHeatBrownianClock_covariance_pair
    (c : ℝ → Fin j → Fin (n+1) → Paper.Overlap) (z : ℝ)
    (hc : ∀ a, Monotone (c z a)) (h0 : ∀ a, (c z a 0 : ℝ)=0)
    (a b : Fin j) (l r : Fin (n+1)) :
    pathHeatVarianceCovariance (pathHeatBrownianClockVariance c)
      pathHeatBrownianClockMask z (finProdFinEquiv (a,l)) (finProdFinEquiv (b,r)) =
      if a=b then min (c z a l : ℝ) (c z b r : ℝ) else 0 := by
  unfold pathHeatVarianceCovariance
  rw [←finProdFinEquiv.sum_comp,Fintype.sum_prod_type]
  simp only [pathHeatBrownianClockVariance_pair,pathHeatBrownianClockMask_pair]
  by_cases hab : a=b
  · subst b
    rw [if_pos rfl]
    have hcollapse :
        (∑ k : Fin j, ∑ i : Fin n, ((c z k i.succ : ℝ)-(c z k i.castSucc : ℝ))*
          (if k=a ∧ i.val<l.val then 1 else 0)*
          (if k=a ∧ i.val<r.val then 1 else 0)) =
        ∑ i : Fin n, ((c z a i.succ : ℝ)-(c z a i.castSucc : ℝ))*
          (if i.val<l.val then 1 else 0)*(if i.val<r.val then 1 else 0) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro k _ hka
        simp [hka]
      · simp
    rw [hcollapse]
    exact clock_prefix_covariance (fun i => (c z a i : ℝ))
      (fun _ _ hi => hc a hi) (h0 a) l r
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro i _
    by_cases hka : k=a
    · have hkb : k≠b := by simpa only [hka] using hab
      simp [hkb]
    · simp [hka]

theorem pathHeatBrownianClock_covariance
    (c : ℝ → Fin j → Fin (n+1) → Paper.Overlap) (z : ℝ)
    (hc : ∀ a, Monotone (c z a)) (h0 : ∀ a, (c z a 0 : ℝ)=0)
    (p q : Fin (j*(n+1))) :
    pathHeatVarianceCovariance (pathHeatBrownianClockVariance c)
      pathHeatBrownianClockMask z p q =
      if (finProdFinEquiv.symm p).1=(finProdFinEquiv.symm q).1 then
        min (c z (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℝ)
          (c z (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 : ℝ) else 0 := by
  obtain ⟨⟨a,l⟩,rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨b,r⟩,rfl⟩ := finProdFinEquiv.surjective q
  simpa only [Equiv.symm_apply_apply] using
    pathHeatBrownianClock_covariance_pair c z hc h0 a b l r

/-- A law identity for the actual product of canonical continuous Wiener
paths, after its canonical finite coordinate reindexing. -/
theorem pathHeatWienerMesh_eq_varianceLaw
    (c : ℝ → Fin j → Fin (n+1) → Paper.Overlap) (z : ℝ)
    (hc : ∀ a, Monotone (c z a)) (h0 : ∀ a, (c z a 0 : ℝ)=0) :
    pathHeatWienerMeshReindexedLaw (c z) =
      pathHeatVarianceLaw (pathHeatBrownianClockVariance c) pathHeatBrownianClockMask z := by
  apply pathHeatVarianceLaw_unique
    (pathHeatBrownianClockVariance c) pathHeatBrownianClockMask z
    (pathHeatBrownianClockVariance_nonnegative c z hc)
  · exact pathHeatWienerMeshReindexedLaw_centered (c z)
  · intro p q
    rw [pathHeatWienerMeshReindexedLaw_covariance,pathHeatBrownianClock_covariance c z hc h0]

end HexagonPaper
