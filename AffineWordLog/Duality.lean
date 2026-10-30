import Mathlib
import AffineWordLog.Definitions
set_option autoImplicit false

lemma awd_summable_words (r : Bool → ℝ) (hr : ∀ b, 0 ≤ r b)
    (hr1 : r false + r true < 1) :
    Summable (fun w : List Bool => (w.map r).prod) := by
  apply (List.equivSigmaTuple.symm.summable_iff).mp
  change Summable (fun p : (n : ℕ) × (Fin n → Bool) =>
    ((List.ofFn p.2).map r).prod)
  simp_rw [List.map_ofFn, List.prod_ofFn]
  apply (summable_sigma_of_nonneg (fun p : (n : ℕ) × (Fin n → Bool) =>
    Finset.prod_nonneg (fun i _ => hr (p.2 i)))).mpr
  constructor
  · intro n
    exact (hasSum_fintype _).summable
  · simp_rw [tsum_fintype, ← Fintype.sum_pow, Fintype.sum_bool]
    exact summable_geometric_of_lt_one (add_nonneg (hr true) (hr false)) (by linarith)

lemma awd_J_bound (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |AffineWordLog.J x| ≤ 2 * |x| := by
  by_cases hx0 : x = 0
  · simp [hx0, AffineWordLog.J]
  have hp : 0 < |x| := abs_pos.mpr hx0
  have hd : 0 < 1 - |x| := by linarith
  have hh := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by linarith) 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one] at hh
  have he : AffineWordLog.J x = -(x + Real.log (1 - x)) / x := by
    rw [AffineWordLog.J, if_neg hx0]
    field_simp
    <;> ring
  rw [he, abs_div, abs_neg]
  calc
    |x + Real.log (1 - x)| / |x| ≤ (|x| ^ 2 / (1 - |x|)) / |x| :=
      div_le_div_of_nonneg_right hh hp.le
    _ = |x| / (1 - |x|) := by field_simp
    _ ≤ 2 * |x| := (div_le_iff₀ hd).mpr (by
      nlinarith [mul_nonneg (abs_nonneg x) (show 0 ≤ 1 - 2 * |x| by linarith)])

lemma awd_summable_J {ι : Type*} (f : ι → ℝ) (hf : Summable f) :
    Summable (fun i => AffineWordLog.J (f i)) := by
  apply (hf.abs.mul_left 2).of_norm_bounded_eventually
  have he := (Metric.tendsto_nhds.mp hf.tendsto_cofinite_zero) (1 / 2) (by norm_num)
  filter_upwards [he] with i hi
  rw [Real.dist_eq, sub_zero] at hi
  simpa only [Real.norm_eq_abs] using awd_J_bound (f i) hi.le

noncomputable def awdK (a x : ℝ) : ℝ :=
  x + (x - a) * AffineWordLog.J (x / (1 + a))

lemma awd_summable_K {ι : Type*} (a : ℝ) (f : ι → ℝ) (hf : Summable f) :
    Summable (fun i => awdK a (f i)) := by
  have hj : Summable (fun i => AffineWordLog.J (f i / (1 + a))) :=
    awd_summable_J _ (by simpa only [div_eq_mul_inv] using hf.mul_right (1 + a)⁻¹)
  have hm : Summable (fun i => f i * AffineWordLog.J (f i / (1 + a))) := by
    have hh := summable_mul_of_summable_norm hf.norm hj.norm
    exact hh.comp_injective (i := fun i => (i, i)) (fun i j h => congrArg Prod.fst h)
  apply (hf.add (hm.sub (hj.mul_left a))).congr
  intro i
  dsimp [awdK]
  ring

lemma awd_parameters (a : ℝ) (ha : 0 < a)
    (hb : a < (Real.sqrt 5 - 1) / 2) :
    a < 1 ∧ a + a / (1 + a) < 1 := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have ht : 0 < (Real.sqrt 5 - (2 * a + 1)) * (Real.sqrt 5 + (2 * a + 1)) := by
    apply mul_pos
    · linarith
    · positivity
  have hquad : a ^ 2 + a < 1 := by nlinarith
  have hsp : 0 < 1 + a := by linarith
  have hq : a / (1 + a) < 1 - a := (div_lt_iff₀ hsp).mpr (by nlinarith)
  constructor <;> nlinarith [sq_nonneg a]

lemma awd_coeff_bounds (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (w : List Bool) :
    0 ≤ (AffineWordLog.coeff a w).1 ∧ (AffineWordLog.coeff a w).1 ≤ 1 ∧
    0 ≤ (AffineWordLog.coeff a w).1 + (AffineWordLog.coeff a w).2 ∧
    (AffineWordLog.coeff a w).1 + (AffineWordLog.coeff a w).2 ≤ 1 := by
  have hq0 : 0 ≤ a / (1 + a) := by positivity
  have hq1 : a / (1 + a) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  induction w with
  | nil => norm_num [AffineWordLog.coeff]
  | cons b w ih =>
    rcases ih with ⟨hc0, hc1, he0, he1⟩
    cases b
    · dsimp [AffineWordLog.coeff]
      have h1 := mul_nonneg ha.le hc0
      have h2 := mul_le_mul_of_nonneg_left hc1 ha.le
      have h3 := mul_nonneg ha.le he0
      have h4 := mul_le_mul_of_nonneg_left he1 ha.le
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor <;> nlinarith
    · dsimp [AffineWordLog.coeff]
      have h1 := mul_nonneg hq0 hc0
      have h2 := mul_le_mul_of_nonneg_left hc1 hq0
      have h3 := mul_nonneg hq0 he0
      have h4 := mul_le_mul_of_nonneg_left he1 hq0
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor <;> nlinarith

lemma awd_coeff_abs (a : ℝ) (w : List Bool) :
    |(AffineWordLog.coeff a w).2| =
      (w.map (fun b => if b then |a / (1 + a)| else |a|)).prod := by
  induction w with
  | nil => simp [AffineWordLog.coeff]
  | cons b w ih => cases b <;> simp [AffineWordLog.coeff, abs_mul, ih]

noncomputable def awdX (a : ℝ) (w : List Bool) : ℝ :=
  a * (AffineWordLog.coeff a w).2 / (1 - a * (AffineWordLog.coeff a w).1)

lemma awd_denom_pos (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (w : List Bool) :
    0 < 1 - a * (AffineWordLog.coeff a w).1 := by
  have hc := (awd_coeff_bounds a ha ha1 w).2.1
  have := mul_le_mul_of_nonneg_left hc ha.le
  linarith

lemma awd_X_lt_one (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (w : List Bool) :
    awdX a w < 1 := by
  unfold awdX
  apply (div_lt_one (awd_denom_pos a ha ha1 w)).mpr
  have he := (awd_coeff_bounds a ha ha1 w).2.2.2
  have := mul_le_mul_of_nonneg_left he ha.le
  nlinarith

lemma awd_coeff_append (a : ℝ) (u v : List Bool) :
    AffineWordLog.coeff a (u ++ v) =
      ((AffineWordLog.coeff a u).1 + (AffineWordLog.coeff a u).2 *
        (AffineWordLog.coeff a v).1,
       (AffineWordLog.coeff a u).2 * (AffineWordLog.coeff a v).2) := by
  induction u with
  | nil => simp [AffineWordLog.coeff]
  | cons b u ih =>
    cases b <;> simp [AffineWordLog.coeff, ih] <;> constructor <;> ring

lemma awd_X_append_false (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (w : List Bool) :
    awdX a (w ++ [false]) = -a * awdX a w / (1 - awdX a w) := by
  have hd := ne_of_gt (awd_denom_pos a ha ha1 w)
  have hd' := ne_of_gt (awd_denom_pos a ha ha1 (w ++ [false]))
  have hx := ne_of_gt (sub_pos.mpr (awd_X_lt_one a ha ha1 w))
  apply (eq_div_iff hx).mpr
  simp only [awd_coeff_append, AffineWordLog.coeff] at hd'
  simp only [awdX, awd_coeff_append, AffineWordLog.coeff]
  field_simp [hd, hd']
  <;> ring

lemma awd_X_append_true (a : ℝ) (w : List Bool) :
    awdX a (w ++ [true]) = a / (1 + a) * awdX a w := by
  simp only [awdX, awd_coeff_append, AffineWordLog.coeff]
  ring

lemma awd_summable_X (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (har : a + a / (1 + a) < 1) : Summable (awdX a) := by
  have hq : 0 < a / (1 + a) := by positivity
  have hw : Summable (fun w : List Bool => |(AffineWordLog.coeff a w).2|) := by
    have h := awd_summable_words (fun b => if b then |a / (1 + a)| else |a|)
      (by intro b; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity)
      (by simpa only [Bool.false_eq_true, ↓reduceIte, abs_of_pos ha, abs_of_pos hq] using har)
    exact h.congr (fun w => (awd_coeff_abs a w).symm)
  apply (hw.mul_left (a / (1 - a))).of_norm_bounded
  intro w
  rw [Real.norm_eq_abs, awdX, abs_div, abs_mul,
    abs_of_pos ha, abs_of_pos (awd_denom_pos a ha ha1 w)]
  have hd : 1 - a ≤ 1 - a * (AffineWordLog.coeff a w).1 := by
    have := mul_le_mul_of_nonneg_left (awd_coeff_bounds a ha ha1 w).2.1 ha.le
    linarith
  calc
    a * |(AffineWordLog.coeff a w).2| / (1 - a * (AffineWordLog.coeff a w).1) ≤
        a * |(AffineWordLog.coeff a w).2| / (1 - a) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hd
    _ = a / (1 - a) * |(AffineWordLog.coeff a w).2| := by ring

lemma awd_coeff_dual (a : ℝ) (ha : 0 < a) (w : List Bool) :
    AffineWordLog.coeff (-a / (1 + a)) (w.map Bool.not) =
      ((1 + a) - (1 + a)^2 * (AffineWordLog.coeff a w).1 -
        (1 + a) * (AffineWordLog.coeff a w).2, (AffineWordLog.coeff a w).2) := by
  have hs : 1 + a ≠ 0 := ne_of_gt (by linarith)
  have hb : 1 + -a / (1 + a) = 1 / (1 + a) := by field_simp; ring
  have hq : (-a / (1 + a)) / (1 + -a / (1 + a)) = -a := by
    rw [hb]
    field_simp
  induction w with
  | nil => simp [AffineWordLog.coeff]
  | cons b w ih =>
    cases b <;> apply Prod.ext <;>
      simp [AffineWordLog.coeff, ih, hq] <;> field_simp <;> ring

lemma awd_X_dual (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (w : List Bool) :
    awdX (-a / (1 + a)) (w.map Bool.not) =
      -awdX a w / ((1 + a) * (1 + a - awdX a w)) := by
  have hs : 1 + a ≠ 0 := ne_of_gt (by linarith)
  have hd := ne_of_gt (awd_denom_pos a ha ha1 w)
  have hx : 1 + a - awdX a w ≠ 0 := ne_of_gt (by
    have := awd_X_lt_one a ha ha1 w
    linarith)
  have he : 1 - (-a / (1 + a)) * ((1 + a) -
        (1 + a)^2 * (AffineWordLog.coeff a w).1 -
        (1 + a) * (AffineWordLog.coeff a w).2) =
      (1 - a * (AffineWordLog.coeff a w).1) * (1 + a - awdX a w) := by
    dsimp [awdX]
    field_simp
    <;> ring
  have hy : awdX a w * (1 - a * (AffineWordLog.coeff a w).1) =
      a * (AffineWordLog.coeff a w).2 := by
    dsimp [awdX]
    field_simp
  apply (eq_div_iff (mul_ne_zero hs hx)).mpr
  rw [awdX, awd_coeff_dual a ha]
  change (-a / (1 + a)) * (AffineWordLog.coeff a w).2 /
      (1 - (-a / (1 + a)) * ((1 + a) -
        (1 + a)^2 * (AffineWordLog.coeff a w).1 -
        (1 + a) * (AffineWordLog.coeff a w).2)) *
      ((1 + a) * (1 + a - awdX a w)) = -awdX a w
  rw [he]
  field_simp [hd, hx, hs]
  nlinarith [hy]

lemma awdK_log (a x : ℝ) (hs : 1 + a ≠ 0) (hx : x ≠ 0) :
    awdK a x = (1 + a) * (a / x - 1) * Real.log (1 - x / (1 + a)) + a := by
  simp only [awdK, AffineWordLog.J, if_neg (div_ne_zero hx hs)]
  field_simp
  <;> ring

lemma awd_cocycle (a x : ℝ) (ha : 0 < a) (hx1 : x < 1) :
    (1 + a) * AffineWordLog.J x -
        AffineWordLog.J (-x / ((1 + a) * (1 + a - x))) =
      awdK a x - awdK a (-a * x / (1 - x)) - awdK a (a / (1 + a) * x) := by
  by_cases hx : x = 0
  · subst x
    simp [awdK, AffineWordLog.J]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hs0 : 0 < 1 + a := by linarith
  have hs : 1 + a ≠ 0 := ne_of_gt hs0
  have ht0 : 0 < 1 - x := by linarith
  have ht : 1 - x ≠ 0 := ne_of_gt ht0
  have hu0 : 0 < 1 + a - x := by linarith
  have hu : 1 + a - x ≠ 0 := ne_of_gt hu0
  have hv0 : 0 < 1 - x / (1 + a) := by
    apply sub_pos.mpr
    apply (div_lt_one hs0).mpr
    linarith
  have hv : 1 - x / (1 + a) ≠ 0 := ne_of_gt hv0
  have hp : 0 < (1 + a)^2 - a * x := by
    nlinarith [mul_pos ha ht0, sq_nonneg a]
  have hz : 1 - (a / (1 + a) * x) / (1 + a) ≠ 0 := by
    have he : 1 - (a / (1 + a) * x) / (1 + a) =
        ((1 + a)^2 - a * x) / (1 + a)^2 := by field_simp <;> ring
    rw [he]
    exact div_ne_zero (ne_of_gt hp) (pow_ne_zero 2 hs)
  have hlog0 : Real.log (1 - (-a * x / (1 - x)) / (1 + a)) =
      Real.log (1 - x / (1 + a)) - Real.log (1 - x) := by
    have he : 1 - (-a * x / (1 - x)) / (1 + a) =
        (1 - x / (1 + a)) / (1 - x) := by field_simp <;> ring
    rw [he, Real.log_div hv ht]
  have hlog1 : Real.log (1 - (-x / ((1 + a) * (1 + a - x)))) =
      Real.log (1 - (a / (1 + a) * x) / (1 + a)) -
        Real.log (1 - x / (1 + a)) := by
    have he : 1 - (-x / ((1 + a) * (1 + a - x))) =
        (1 - (a / (1 + a) * x) / (1 + a)) / (1 - x / (1 + a)) := by
      apply (eq_div_iff hv).mpr
      field_simp
      <;> ring
    rw [he, Real.log_div hz hv]
  have hx0 : -a * x / (1 - x) ≠ 0 :=
    div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha0) hx) ht
  have hx2 : a / (1 + a) * x ≠ 0 := mul_ne_zero (div_ne_zero ha0 hs) hx
  have hxh : -x / ((1 + a) * (1 + a - x)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hx) (mul_ne_zero hs hu)
  rw [awdK_log a x hs hx, awdK_log a _ hs hx0, awdK_log a _ hs hx2]
  simp only [AffineWordLog.J, if_neg hx, if_neg hxh]
  rw [hlog0, hlog1]
  field_simp
  <;> ring

lemma awd_tsum_cons (f : List Bool → ℝ) (hf : Summable f) :
    (∑' w, f w) = f [] + (∑' w, f (false :: w)) + (∑' w, f (true :: w)) := by
  let e : Unit ⊕ (Bool × List Bool) ≃ List Bool :=
    { toFun := fun s => match s with
        | Sum.inl _ => []
        | Sum.inr (b, w) => b :: w
      invFun := fun w => match w with
        | [] => Sum.inl ()
        | b :: v => Sum.inr (b, v)
      left_inv := by rintro (u | ⟨b, w⟩); cases u <;> rfl; rfl
      right_inv := by intro w; cases w <;> rfl }
  have hp : Summable (fun p : Bool × List Bool => f (p.1 :: p.2)) := by
    apply hf.comp_injective
    rintro ⟨b, w⟩ ⟨c, v⟩ h
    simpa only [List.cons.injEq, Prod.mk.injEq] using h
  have hn : Summable (fun _ : Unit => f []) := (hasSum_fintype _).summable
  calc
    (∑' w, f w) = ∑' s, f (e s) := (e.tsum_eq f).symm
    _ = (∑' _ : Unit, f []) + (∑' p : Bool × List Bool, f (p.1 :: p.2)) :=
      Summable.tsum_sum hn hp
    _ = _ := by rw [hp.tsum_prod, tsum_bool]; simp [add_assoc]

lemma awd_tsum_append (f : List Bool → ℝ) (hf : Summable f) :
    (∑' w, f w) = f [] + (∑' w, f (w ++ [false])) + (∑' w, f (w ++ [true])) := by
  let e : List Bool ≃ List Bool :=
    Function.Involutive.toPerm List.reverse List.reverse_reverse
  have h := awd_tsum_cons (fun w => f w.reverse) (hf.comp_injective List.reverse_injective)
  simp only [List.reverse_nil, List.reverse_cons] at h
  have h0 : (∑' w : List Bool, f w.reverse) = ∑' w, f w := e.tsum_eq f
  have h1 : (∑' w : List Bool, f (w.reverse ++ [false])) = ∑' w, f (w ++ [false]) :=
    e.tsum_eq (fun w => f (w ++ [false]))
  have h2 : (∑' w : List Bool, f (w.reverse ++ [true])) = ∑' w, f (w ++ [true]) :=
    e.tsum_eq (fun w => f (w ++ [true]))
  rwa [h0, h1, h2] at h

theorem AffineWordLog.realIntervalDuality (a : ℝ) (ha_pos : 0 < a)
    (ha_bound : a < (Real.sqrt 5 - 1) / 2) :
    AffineWordLog.I (-a / (1 + a)) = (1 + a) * AffineWordLog.I a - a := by
  obtain ⟨ha1, har⟩ := awd_parameters a ha_pos ha_bound
  have hx := awd_summable_X a ha_pos ha1 har
  have hj := awd_summable_J (awdX a) hx
  have hk := awd_summable_K a (awdX a) hx
  have hk0 : Summable (fun w => awdK a (awdX a (w ++ [false]))) :=
    hk.comp_injective (List.append_left_injective [false])
  have hk1 : Summable (fun w => awdK a (awdX a (w ++ [true]))) :=
    hk.comp_injective (List.append_left_injective [true])
  have he (w : List Bool) :
      AffineWordLog.J (awdX (-a / (1 + a)) (w.map Bool.not)) =
        (1 + a) * AffineWordLog.J (awdX a w) - awdK a (awdX a w) +
          awdK a (awdX a (w ++ [false])) + awdK a (awdX a (w ++ [true])) := by
    rw [awd_X_dual a ha_pos ha1 w]
    have h := awd_cocycle a (awdX a w) ha_pos (awd_X_lt_one a ha_pos ha1 w)
    rw [← awd_X_append_false a ha_pos ha1 w, ← awd_X_append_true a w] at h
    linarith
  have ht := awd_tsum_append (fun w => awdK a (awdX a w)) hk
  have hr : awdK a (awdX a []) = a := by simp [awdX, AffineWordLog.coeff, awdK]
  rw [hr] at ht
  let e : List Bool ≃ List Bool := Equiv.listEquivOfEquiv Equiv.boolNot
  change (∑' w, AffineWordLog.J (awdX (-a / (1 + a)) w)) =
    (1 + a) * (∑' w, AffineWordLog.J (awdX a w)) - a
  rw [← e.tsum_eq (fun w => AffineWordLog.J (awdX (-a / (1 + a)) w))]
  change (∑' w : List Bool, AffineWordLog.J (awdX (-a / (1 + a)) (w.map Bool.not))) = _
  simp_rw [he]
  rw [(((hj.mul_left (1 + a)).sub hk).add hk0).tsum_add hk1,
    ((hj.mul_left (1 + a)).sub hk).tsum_add hk0,
    (hj.mul_left (1 + a)).tsum_sub hk, tsum_mul_left]
  linarith
