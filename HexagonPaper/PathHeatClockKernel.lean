module
public import HexagonPaper.PathHeatTreeBernsteinMixedFlatten
public import HexagonPaper.PathHeatBrownianClockFactor

@[expose] public section

/-! Actual continuous kernels of independent time-changed Wiener edges and
the exact finite clock-factor covariance derivative. Derivative clocks need
not be monotone: their signed increment telescope is proved directly. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pathHeatClockProfile {L : ℕ} (c : Fin L → C(I,ℝ)) : C(Fin L × I,ℝ) :=
  ⟨fun x => c x.1 x.2, continuous_prod_of_discrete_left.mpr (fun l => (c l).continuous)⟩

def pathHeatClockEdgeIndicator {L : ℕ} : C(Fin L × Fin L,ℝ) :=
  ⟨fun x => if x.1=x.2 then 1 else 0, continuous_of_discreteTopology⟩

def pathHeatClockMinMap (L : ℕ) : C((Fin L × I) × (Fin L × I),Fin L × I) :=
  ⟨fun x => (x.1.1,min x.1.2 x.2.2),
    continuous_fst.fst.prodMk (continuous_fst.snd.min continuous_snd.snd)⟩

def pathHeatClockRawKernel {L : ℕ} (c : Fin L → C(I,ℝ)) :
    C(Fin L × I,C(Fin L × I,ℝ)) :=
  ((pathHeatClockEdgeIndicator.comp
    ⟨fun x : (Fin L × I) × (Fin L × I) => (x.1.1,x.2.1),
      continuous_fst.fst.prodMk continuous_snd.fst⟩) *
        ((pathHeatClockProfile c).comp (pathHeatClockMinMap L))).curry

@[simp] theorem pathHeatClockRawKernel_apply {L : ℕ} (c : Fin L → C(I,ℝ))
    (x y : Fin L × I) : pathHeatClockRawKernel c x y =
      if x.1=y.1 then c x.1 (min x.2 y.2) else 0 := by
  simp [pathHeatClockRawKernel,pathHeatClockEdgeIndicator,pathHeatClockProfile,
    pathHeatClockMinMap,ite_mul]

theorem norm_pathHeatClockRawKernel_le {L : ℕ} (c : Fin L → C(I,ℝ)) :
    ‖pathHeatClockRawKernel c‖ ≤ ‖pathHeatClockProfile c‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro y
  rw [pathHeatClockRawKernel_apply]
  split_ifs
  · exact (pathHeatClockProfile c).norm_coe_le_norm (x.1,min x.2 y.2)
  · simpa using norm_nonneg (pathHeatClockProfile c)

def pathHeatClockReal {L : ℕ} (c : Fin L → C(I,I)) : Fin L → C(I,ℝ) :=
  fun l => ⟨fun t => (c l t : ℝ), continuous_subtype_val.comp (c l).continuous⟩

@[simp] theorem pathHeatClockReal_apply {L : ℕ} (c : Fin L → C(I,I))
    (l : Fin L) (t : I) : pathHeatClockReal c l t = (c l t : ℝ) := rfl

theorem bernstein_z_monotone (n : ℕ) : Monotone (@bernstein.z n) := by
  intro i j hij
  change (i : ℝ)/(n:ℝ) ≤ (j : ℝ)/(n:ℝ)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg n)

theorem bernstein_z_min (n : ℕ) (i j : Fin (n+1)) :
    bernstein.z (min i j) = min (bernstein.z i) (bernstein.z j) :=
  (bernstein_z_monotone n).map_min

theorem clock_prefix_covariance_signed {n : ℕ} (c : Fin (n+1) → ℝ)
    (h0 : c 0=0) (l r : Fin (n+1)) :
    (∑i : Fin n,(c i.succ-c i.castSucc)*(if i.val<l.val then 1 else 0)*
      (if i.val<r.val then 1 else 0)) = c (min l r) := by
  rcases le_total l r with hlr | hrl
  · rw [min_eq_left hlr]
    have he (i : Fin n) :
        (c i.succ-c i.castSucc)*(if i.val<l.val then 1 else 0)*
          (if i.val<r.val then 1 else 0) =
        (c i.succ-c i.castSucc)*(if i.val<l.val then 1 else 0) := by
      by_cases hi : i.val<l.val
      · have hir : i.val<r.val := lt_of_lt_of_le hi hlr
        simp [hi,hir]
      · simp [hi]
    simp_rw [he]
    rw [clock_prefix_sum,h0,sub_zero]
  · rw [min_eq_right hrl]
    have he (i : Fin n) :
        (c i.succ-c i.castSucc)*(if i.val<l.val then 1 else 0)*
          (if i.val<r.val then 1 else 0) =
        (c i.succ-c i.castSucc)*(if i.val<r.val then 1 else 0) := by
      by_cases hi : i.val<r.val
      · have hil : i.val<l.val := lt_of_lt_of_le hi hrl
        simp [hi,hil]
      · simp [hi]
    simp_rw [he]
    rw [clock_prefix_sum,h0,sub_zero]

def pathHeatClockMesh (n : ℕ) {L : ℕ} (c : ℝ → Fin L → C(I,I)) :
    ℝ → Fin L → Fin (n+1) → Paper.Overlap :=
  fun z l i => c z l (bernstein.z i)

def pathHeatClockMeshDerivative (n : ℕ) {L : ℕ} (dc : ℝ → Fin L → C(I,ℝ)) :
    ℝ → Fin (L*n) → ℝ :=
  fun z α => dc z (finProdFinEquiv.symm α).1 (bernstein.z (finProdFinEquiv.symm α).2.succ) -
    dc z (finProdFinEquiv.symm α).1 (bernstein.z (finProdFinEquiv.symm α).2.castSucc)

@[simp] theorem pathHeatClockMeshDerivative_pair (n : ℕ) {L : ℕ}
    (dc : ℝ → Fin L → C(I,ℝ)) (z : ℝ) (a : Fin L) (i : Fin n) :
    pathHeatClockMeshDerivative n dc z (finProdFinEquiv (a,i)) =
      dc z a (bernstein.z i.succ)-dc z a (bernstein.z i.castSucc) := by
  simp [pathHeatClockMeshDerivative]

theorem pathHeatClockMesh_covarianceDerivative_pair (n : ℕ) {L : ℕ}
    (dc : ℝ → Fin L → C(I,ℝ)) (z : ℝ) (h0 : ∀a, dc z a 0=0)
    (a b : Fin L) (l r : Fin (n+1)) :
    pathHeatVarianceCovarianceDerivative (pathHeatClockMeshDerivative n dc)
      pathHeatBrownianClockMask z (finProdFinEquiv (a,l)) (finProdFinEquiv (b,r)) =
        if a=b then dc z a (min (bernstein.z l) (bernstein.z r)) else 0 := by
  unfold pathHeatVarianceCovarianceDerivative
  rw [←finProdFinEquiv.sum_comp,Fintype.sum_prod_type]
  simp only [pathHeatClockMeshDerivative_pair,pathHeatBrownianClockMask_pair]
  by_cases hab : a=b
  · subst b
    rw [if_pos rfl]
    have hcollapse :
        (∑ k : Fin L, ∑ i : Fin n,
          (dc z k (bernstein.z i.succ)-dc z k (bernstein.z i.castSucc))*
            (if k=a ∧ i.val<l.val then 1 else 0)*(if k=a ∧ i.val<r.val then 1 else 0)) =
        ∑ i : Fin n, (dc z a (bernstein.z i.succ)-dc z a (bernstein.z i.castSucc))*
          (if i.val<l.val then 1 else 0)*(if i.val<r.val then 1 else 0) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro k _ hka; simp [hka]
      · simp
    rw [hcollapse]
    have ht := clock_prefix_covariance_signed (fun i => dc z a (bernstein.z i))
      (by simpa only [bernstein.z_zero] using h0 a) l r
    simpa only [bernstein_z_min] using ht
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro i _
    by_cases hka : k=a
    · have hkb : k≠b := by simpa only [hka] using hab
      simp [hkb]
    · simp [hka]

theorem pathHeatClockMesh_covarianceDerivative (n : ℕ) {L : ℕ}
    (dc : ℝ → Fin L → C(I,ℝ)) (z : ℝ) (h0 : ∀a, dc z a 0=0)
    (p q : Fin (L*(n+1))) :
    pathHeatVarianceCovarianceDerivative (pathHeatClockMeshDerivative n dc)
      pathHeatBrownianClockMask z p q =
        pathHeatClockRawKernel (dc z)
          ((finProdFinEquiv.symm p).1,bernstein.z (finProdFinEquiv.symm p).2)
          ((finProdFinEquiv.symm q).1,bernstein.z (finProdFinEquiv.symm q).2) := by
  obtain ⟨⟨a,l⟩,rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨b,r⟩,rfl⟩ := finProdFinEquiv.surjective q
  simpa only [Equiv.symm_apply_apply,pathHeatClockRawKernel_apply] using
    pathHeatClockMesh_covarianceDerivative_pair n dc z h0 a b l r

theorem pathHeatClockMeshVariance_hasDerivAt (n : ℕ) {L : ℕ}
    (c : ℝ → Fin L → C(I,I)) (dc : ℝ → Fin L → C(I,ℝ)) (z : ℝ)
    (hdc : ∀a t, HasDerivAt (fun w => (c w a t : ℝ)) (dc z a t) z)
    (α : Fin (L*n)) :
    HasDerivAt (fun w => pathHeatBrownianClockVariance (pathHeatClockMesh n c) w α)
      (pathHeatClockMeshDerivative n dc z α) z :=
  (hdc _ _).sub (hdc _ _)

theorem pathHeatClockDerivative_root_zero {L : ℕ}
    (c : ℝ → Fin L → C(I,I)) (dc : ℝ → Fin L → C(I,ℝ)) (z : ℝ)
    (hdc : ∀a t, HasDerivAt (fun w => (c w a t : ℝ)) (dc z a t) z)
    (hroot : ∀w a, c w a 0=0) (a : Fin L) : dc z a 0=0 := by
  have he : (fun w => (c w a 0 : ℝ)) = fun _ => (0:ℝ) := by
    funext w; rw [hroot]; rfl
  have hd := hdc a 0
  rw [he] at hd
  exact hd.unique (hasDerivAt_const z (0:ℝ))

end HexagonPaper
