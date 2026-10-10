module
public import FourPapersCommon.FiniteCascadeTreeCoordinateScaling
public import FourPapersCommon.FiniteCascadeConditionalMarks

@[expose] public section

/-! The common-path covariance of the independent, retained Gaussian edge
coordinates. Forks use disjoint coordinate sets; repeated levels contribute
zero when their actual increment coefficient vanishes. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {I : Type} [Fintype I] [DecidableEq I]

@[reducible] def finiteCascadePathCoefficient (d : ℕ → ℝ) (i : I) :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} →
      FiniteCascadeRecordVertex T → GaussianCoordinateIndex I T → ℝ
  | _, _, .root _ => fun _ => 0
  | _, @FiniteTerminalGenealogy.advance j _, .child v =>
      Sum.elim (fun l => if l=i then d j else 0) (finiteCascadePathCoefficient d i v)
  | _, _, .left v => Sum.elim (finiteCascadePathCoefficient d i v) (fun _ => 0)
  | _, _, .right v => Sum.elim (fun _ => 0) (finiteCascadePathCoefficient d i v)

@[reducible] def finiteCascadeCommonPathQuadratic (d : ℕ → ℝ) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      FiniteCascadeRecordVertex T → FiniteCascadeRecordVertex T → ℝ
  | _, .leaf => fun _ _ => 0
  | _, @FiniteTerminalGenealogy.advance j T => fun v w => match v,w with
      | .root _, _ => 0
      | _, .root _ => 0
      | .child v, .child w => (d j)^2+finiteCascadeCommonPathQuadratic d T v w
  | _, .fork T U => fun v w => match v,w with
      | .root _, _ => 0
      | _, .root _ => 0
      | .left v, .left w => finiteCascadeCommonPathQuadratic d T v w
      | .right v, .right w => finiteCascadeCommonPathQuadratic d U v w
      | .left _, .right _ => 0
      | .right _, .left _ => 0

theorem finiteCascadePathCoefficient_covariance (d : ℕ → ℝ) (i : I)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (v w : FiniteCascadeRecordVertex T) :
    (∑e : GaussianCoordinateIndex I T,
      finiteCascadePathCoefficient d i v e*finiteCascadePathCoefficient d i w e) =
        finiteCascadeCommonPathQuadratic d T v w := by
  classical
  induction T with
  | leaf => cases v; cases w; simp [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic]
  | @advance j T ih =>
      cases v with
      | root => simp [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic]
      | child v =>
        cases w with
        | root => simp [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic]
        | child w =>
          simp only [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic,Fintype.sum_sum_type,
            Sum.elim_inl,Sum.elim_inr]
          rw [ih v w]
          congr 1
          rw [Finset.sum_eq_single i]
          · simp; ring
          · intro l _ hli; simp [hli]
          · simp
  | fork T U ihT ihU =>
      cases v with
      | root => simp [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic]
      | left v =>
        cases w with
        | root => simp [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic]
        | left w => simpa [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic,Fintype.sum_sum_type]
            using ihT v w
        | right w => simp [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic,Fintype.sum_sum_type]
      | right v =>
        cases w with
        | root => simp [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic]
        | left w => simp [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic,Fintype.sum_sum_type]
        | right w => simpa [finiteCascadePathCoefficient,finiteCascadeCommonPathQuadratic,Fintype.sum_sum_type]
            using ihU v w

@[reducible] def finiteCascadeCommonPathDepth :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      FiniteCascadeRecordVertex T → FiniteCascadeRecordVertex T → ℕ
  | _, .leaf => fun _ _ => 0
  | _, @FiniteTerminalGenealogy.advance j T => fun v w => match v,w with
      | .root _, _ => j+1
      | _, .root _ => j+1
      | .child v, .child w => finiteCascadeCommonPathDepth T v w
  | j, .fork T U => fun v w => match v,w with
      | .root _, _ => j
      | _, .root _ => j
      | .left v, .left w => finiteCascadeCommonPathDepth T v w
      | .right v, .right w => finiteCascadeCommonPathDepth U v w
      | .left _, .right _ => j
      | .right _, .left _ => j

theorem finiteCascadeCommonPathDepth_le {j : ℕ} (T : FiniteTerminalGenealogy j)
    (v w : FiniteCascadeRecordVertex T) : finiteCascadeCommonPathDepth T v w ≤ j := by
  induction T with
  | leaf => cases v; cases w; exact le_rfl
  | advance T ih =>
      cases v with
      | root => exact le_rfl
      | child v => cases w with
        | root => exact le_rfl
        | child w => exact (ih v w).trans (Nat.le_succ _)
  | fork T U ihT ihU =>
      cases v with
      | root => exact le_rfl
      | left v => cases w with
        | root => exact le_rfl
        | left w => exact ihT v w
        | right w => exact le_rfl
      | right v => cases w with
        | root => exact le_rfl
        | left w => exact le_rfl
        | right w => exact ihU v w

theorem finiteCascadeCommonPathQuadratic_eq_clock (d q : ℕ → ℝ)
    (hd : ∀j,(d j)^2=q j-q (j+1)) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathQuadratic d T v w = q (finiteCascadeCommonPathDepth T v w)-q j := by
  induction T with
  | leaf => cases v; cases w; simp [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
  | @advance j T ih =>
      cases v with
      | root => simp [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
      | child v => cases w with
        | root => simp [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
        | child w =>
          simp only [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
          rw [hd,ih v w]
          ring
  | fork T U ihT ihU =>
      cases v with
      | root => simp [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
      | left v => cases w with
        | root => simp [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
        | left w => exact ihT v w
        | right w => simp [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
      | right v => cases w with
        | root => simp [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
        | left w => simp [finiteCascadeCommonPathQuadratic,finiteCascadeCommonPathDepth]
        | right w => exact ihU v w

end FourPapersCommon
