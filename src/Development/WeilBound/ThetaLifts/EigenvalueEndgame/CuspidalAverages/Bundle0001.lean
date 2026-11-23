module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KeyThree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ExistsCond
section
noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp.Key

open scoped Matrix
open Filter Topology ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil

theorem exists_compl {K : Type} [Field K] {d j : ℕ} (u : Matrix (Fin d) (Fin j) K) (p : Matrix (Fin j) (Fin d) K) (h : p * u = 1) :
    ∃ (e : Fin j → Fin d) (c : GL (Fin d) K), Function.Injective e ∧ (∀ a i, c.1 a (e i) = u a i) ∧
      p * c.1 = (1 : Matrix (Fin d) (Fin d) K).submatrix e id := by
  let N := LinearMap.ker p.mulVecLin
  let b := Module.finBasis K N
  have hs : Function.Surjective p.mulVecLin := fun y => ⟨u *ᵥ y, by simp [h]⟩
  have hd : j + Module.finrank K N = d := by
    have := p.mulVecLin.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hs] at this
    simpa using this
  let q : Fin j ⊕ Fin (Module.finrank K N) ≃ Fin d := finSumFinEquiv.trans (finCongr hd)
  let w : Matrix (Fin d) (Fin (Module.finrank K N)) K := Matrix.of fun a i => (b i).1 a
  have hw : p * w = 0 := Matrix.ext fun a i => congrFun (b i).2 a
  let c : Matrix (Fin d) (Fin d) K := (Matrix.fromCols u w).submatrix id q.symm
  have hc : IsUnit c := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    refine (injective_iff_map_eq_zero c.mulVecLin).2 fun x hx => ?_
    have h1 : u *ᵥ (fun i => x (q (.inl i))) + w *ᵥ (fun i => x (q (.inr i))) = 0 := by
      rw [← hx]
      funext a
      simp [c, Matrix.mulVec, dotProduct, ← q.sum_comp]
    have h2 : (fun i => x (q (.inl i))) = 0 := by
      have := congrArg (p *ᵥ ·) h1
      simpa [Matrix.mulVec_add, h, hw] using this
    rw [h2, Matrix.mulVec_zero, zero_add] at h1
    have h3 : ∀ i, x (q (.inr i)) = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent _ (Subtype.ext (by
      funext a
      simpa [w, Matrix.mulVec, dotProduct, mul_comm] using congrFun h1 a))
    funext a
    obtain ⟨i | i, rfl⟩ := q.surjective a
    exacts [congrFun h2 i, h3 i]
  refine ⟨fun i => q (.inl i), hc.unit, fun _ _ h => Sum.inl_injective (q.injective h), fun a i => by simp [c], ?_⟩
  ext a b'
  obtain ⟨i | i, rfl⟩ := q.surjective b'
  · have := congrFun (congrFun h a) i
    simpa [c, Matrix.mul_apply, Matrix.one_apply] using this
  · have := congrFun (congrFun hw a) i
    simpa [c, Matrix.mul_apply, Matrix.one_apply] using this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

theorem unif_lt {ϖ : kˣ} (hϖ : IsUnif ϖ) : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one

theorem exists_cond {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k ℂ} (hc : Continuous ψ) (h1 : ψ ≠ 1) : ∃ c : ℤ,
    (∀ x, valuation k x ≤ valuation k ((ϖ ^ c : kˣ) : k) → ψ x = 1) ∧
      ∃ x, valuation k x ≤ valuation k ((ϖ ^ (c - 1) : kˣ) : k) ∧ ψ x ≠ 1 := by
  have hl := unif_lt hϖ
  have h0 : 0 < valuation k (ϖ : k) := by rw [pos_iff_ne_zero]; simp
  let P : ℤ → Prop := fun c => ∀ x, valuation k x ≤ valuation k ((ϖ ^ c : kˣ) : k) → ψ x = 1
  have ex : ∃ c, P c := by
    have : {x | ‖ψ x - 1‖ < 1 / 2} ∈ 𝓝 (0 : k) := (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
    obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_zero_iff _ |>.1 this
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hl γ
    refine ⟨m, fun x hx => ?_⟩
    have hb : ∀ i : ℕ, ‖ψ x ^ i - 1‖ < 1 / 2 := fun i => by
      rw [← AddChar.map_nsmul_eq_pow]
      refine hγ (lt_of_le_of_lt ?_ hm)
      have : valuation k (i • x) ≤ valuation k x := by
        rw [nsmul_eq_mul, map_mul]
        exact mul_le_of_le_one_left' (natCast_mem (valuation k).integer i)
      simpa using this.trans hx
    have hg : ∀ i : ℕ, (3 / 2 : ℝ) ^ i * ‖ψ x - 1‖ ≤ ‖ψ x ^ 2 ^ i - 1‖ := fun i => by
      induction i with
      | zero => simp
      | succ i ih =>
        have e : ψ x ^ 2 ^ (i + 1) - 1 = (ψ x ^ 2 ^ i - 1) * (2 + (ψ x ^ 2 ^ i - 1)) := by rw [pow_succ, pow_mul]; ring
        have a := norm_sub_norm_le (2 : ℂ) (-(ψ x ^ 2 ^ i - 1))
        rw [sub_neg_eq_add, norm_neg, Complex.norm_two] at a
        have b := hb (2 ^ i)
        rw [e, norm_mul, pow_succ]
        nlinarith [norm_nonneg (ψ x ^ 2 ^ i - 1)]
    by_contra hne
    have hp : 0 < ‖ψ x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (1 / ‖ψ x - 1‖) (show (1 : ℝ) < 3 / 2 by norm_num)
    rw [div_lt_iff₀ hp] at hi
    linarith [hg i, hb (2 ^ i)]
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra hn
    push Not at hn
    exact h1 (AddChar.ext _ _ hn)
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hv : 0 < valuation k x := by rw [pos_iff_ne_zero]; simpa
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hl (Units.mk0 (valuation k x)⁻¹ (inv_ne_zero hv.ne'))
  obtain ⟨c, hc1, hc2⟩ := Int.exists_least_of_bdd (P := P) ⟨-m, fun z hz => by
    by_contra hn
    refine hx (hz x ?_)
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    refine le_trans ?_ (zpow_le_zpow_right_of_le_one₀ h0 hl.le (not_le.1 hn).le)
    rw [zpow_neg, zpow_natCast]
    exact (le_inv_comm₀ (pow_pos h0 _) hv).1 (by simpa using hm.le)⟩ ex
  refine ⟨c, hc1, ?_⟩
  by_contra hn
  push Not at hn
  have := hc2 (c - 1) hn
  omega

def IntM {a b : Type} (Y : Matrix a b k) : Prop := ∀ i j, valuation k (Y i j) ≤ 1

theorem IntM.mul {a b c : Type} [Fintype b] {Y : Matrix a b k} {Z : Matrix b c k} (h : IntM Y) (h' : IntM Z) : IntM (Y * Z) :=
  fun i j => show (Y * Z) i j ∈ (valuation k).integer from
    Subring.sum_mem _ fun l _ => Subring.mul_mem _ (h i l) (h' l j)

theorem oneO_mul {g : GL (Fin d) k} (h : IntM g.1) (h' : IntM (g⁻¹).1) (Y : Matrix (Fin n) (Fin d) k) :
    oneO k n d (Y * g.1) = oneO k n d Y := by
  have : IntM (Y * g.1) ↔ IntM Y := ⟨fun a => by simpa [Matrix.mul_assoc] using a.mul h', fun a => a.mul h⟩
  by_cases hY : IntM Y
  · rw [oneO, Set.indicator_of_mem (this.2 hY), Set.indicator_of_mem hY]; rfl
  · rw [oneO, Set.indicator_of_notMem (mt this.1 hY), Set.indicator_of_notMem hY]

theorem isOpen_int : IsOpen {x : k | valuation k x ≤ 1} := (valuation k).isOpen_integer

theorem apow_unif {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℕ) : apow ϖ (((2 * m : ℕ) : ℂ) / 2) = ((resCard k : ℂ) ^ m)⁻¹ := by
  rw [show ((2 * m : ℕ) : ℂ) / 2 = m by push_cast; ring, apow, nabs_uniformiser hϖ.irreducible (x := ϖ) rfl, Complex.cpow_natCast]
  simp

def yy (q r : ℂ) (c : ℤ) (m : ℕ) : ℂ := (q * r) ^ (-(m : ℤ)) * ∑ i ∈ Finset.range (2 * m - c + 1).toNat, r ^ i

theorem yy_inv (q : ℂ) {r : ℂ} (hr : r ≠ 0) (c : ℤ) (m : ℕ) : yy q r⁻¹ c m = r ^ c * yy q r c m := by
  unfold yy
  rcases le_or_gt (2 * m - c + 1) 0 with h | h
  · simp [Int.toNat_eq_zero.2 h]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * m - c = N := ⟨(2 * m - c).toNat, by omega⟩
  have e : (2 * m - c + 1).toNat = N + 1 := by omega
  have s : ∑ i ∈ Finset.range (N + 1), r⁻¹ ^ i = (r ^ N)⁻¹ * ∑ i ∈ Finset.range (N + 1), r ^ i := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    rw [show i + l + 1 - 1 - i = l by omega, pow_add, inv_pow]
    field_simp
  rw [e, s, show c = (m : ℤ) + m - N by omega, zpow_sub₀ hr, zpow_add₀ hr]
  simp only [zpow_neg, zpow_natCast, inv_pow, mul_pow]
  field_simp

theorem yy_tendsto {q : ℝ} (hq : 1 < q) {r : ℂ} (hr : q < ‖r‖) (c : ℤ) : Tendsto (fun m => ‖yy q r c m‖) atTop atTop := by
  set R := ‖r‖ with hR
  have hR1 : 1 < R := hq.trans hr
  have h1 : Tendsto (fun m : ℕ => (R ^ (1 - c) * (R / q) ^ m - 1) / (R + 1)) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-1) ((tendsto_pow_atTop_atTop_of_one_lt
      ((one_lt_div (by linarith)).2 hr)).const_mul_atTop (by positivity))).atTop_div_const (by linarith)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop c.toNat] with m hm
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * m - c + 1 = N := ⟨(2 * m - c + 1).toNat, by omega⟩
  have a : R ^ N - 1 ≤ ‖∑ i ∈ Finset.range N, r ^ i‖ * (R + 1) := by
    have b := norm_sub_norm_le (r ^ N) 1
    rw [← geom_sum_mul, norm_mul, norm_pow, norm_one] at b
    exact b.trans (mul_le_mul_of_nonneg_left (by simpa using norm_sub_le r 1) (norm_nonneg _))
  have hQ : 1 ≤ (q * R) ^ m := one_le_pow₀ (by nlinarith)
  have e : R ^ (1 - c) * (R / q) ^ m = ((q * R) ^ m)⁻¹ * R ^ N := by
    rw [← zpow_natCast R N, ← hN, show 2 * (m : ℤ) - c + 1 = m + m + (1 - c) by ring, zpow_add₀ (by linarith), zpow_add₀ (by linarith),
      zpow_natCast, div_pow, mul_pow]
    field_simp
  rw [yy, hN, Int.toNat_natCast, norm_mul, norm_zpow, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), zpow_neg,
    zpow_natCast, div_le_iff₀ (by linarith), e, mul_assoc]
  have i1 : ((q * R) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ
  have i0 : 0 ≤ ((q * R) ^ m)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left a i0]

end PositivityTheory.ThKEnd.Cusp.Key

end
end

-- bundled from Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.LeSuccIff
section
noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp.LocB

open ValuativeRel GlobalTheory.WeilM GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {ϖ : kˣ}

def Le (ϖ : kˣ) (e : ℤ) (x : k) : Prop := valuation k x ≤ valuation k (ϖ : k) ^ e

theorem u_pos (ϖ : kˣ) : 0 < valuation k (ϖ : k) := by
  rw [Valuation.pos_iff]; exact ϖ.ne_zero

theorem u_lt (h : IsUnif ϖ) : valuation k (ϖ : k) < 1 := by rw [h]; exact uniformizer_lt_one

theorem Le.mono (h : IsUnif ϖ) {e e' : ℤ} {x : k} (hx : Le ϖ e x) (he : e' ≤ e) : Le ϖ e' x :=
  le_trans hx (zpow_le_zpow_right_of_le_one₀ (u_pos ϖ) (u_lt h).le he)

theorem Le.add {e : ℤ} {x y : k} (hx : Le ϖ e x) (hy : Le ϖ e y) : Le ϖ e (x + y) := (valuation k).map_add_le hx hy

theorem Le.sub {e : ℤ} {x y : k} (hx : Le ϖ e x) (hy : Le ϖ e y) : Le ϖ e (x - y) := (valuation k).map_sub_le hx hy

theorem Le.zero (e : ℤ) : Le ϖ e 0 := by simp [Le]

theorem Le.mul {e f : ℤ} {x y : k} (hx : Le ϖ e x) (hy : Le ϖ f y) : Le ϖ (e + f) (x * y) := by
  unfold Le at *
  rw [map_mul, zpow_add₀ (u_pos ϖ).ne']
  exact mul_le_mul' hx hy

theorem le_mul_iff {e f : ℤ} {x y : k} (hy : valuation k y = valuation k (ϖ : k) ^ f) : Le ϖ (e + f) (x * y) ↔ Le ϖ e x := by
  unfold Le
  rw [map_mul, zpow_add₀ (u_pos ϖ).ne', hy]
  exact mul_le_mul_iff_left₀ (zpow_pos (u_pos ϖ) f)

theorem le_one_iff (h : IsUnif ϖ) {x : k} : Le ϖ 1 x ↔ valuation k x < 1 := by
  unfold Le; rw [zpow_one, h, le_uniformizer_iff]

theorem le_zero_iff {x : k} : Le ϖ 0 x ↔ valuation k x ≤ 1 := by unfold Le; rw [zpow_zero]

theorem val_zpow (e : ℤ) : valuation k ((ϖ : k) ^ e) = valuation k (ϖ : k) ^ e := map_zpow₀ _ _ _

theorem le_succ_iff (h : IsUnif ϖ) {e : ℤ} {x : k} : Le ϖ (e + 1) x ↔ Le ϖ e x ∧ valuation k x ≠ valuation k (ϖ : k) ^ e := by
  have h0 : (ϖ : k) ^ e ≠ 0 := zpow_ne_zero _ ϖ.ne_zero
  have hx : x = x / (ϖ : k) ^ e * (ϖ : k) ^ e := (div_mul_cancel₀ _ h0).symm
  have hp := zpow_pos (u_pos ϖ) e
  rw [hx, add_comm, le_mul_iff (val_zpow e), le_one_iff h]
  unfold Le
  rw [← lt_iff_le_and_ne, map_mul, val_zpow]
  exact (mul_lt_iff_lt_one_left hp).symm

theorem exists_reps (h : IsUnif ϖ) : ∃ R : Finset k, R.card = GlobalTheory.SplitWeil.resCard k ∧ (∀ ρ ∈ R, Le ϖ 0 ρ) ∧
    ∀ x, Le ϖ 0 x → ∃ ρ ∈ R, Le ϖ 1 (x - ρ) ∧ ∀ ρ' ∈ R, Le ϖ 1 (x - ρ') → ρ' = ρ := by
  classical
  have : Fintype 𝓀[k] := Fintype.ofFinite _
  obtain ⟨s, hs⟩ := (IsLocalRing.residue_surjective (R := 𝒪[k])).hasRightInverse
  have key : ∀ (x : 𝒪[k]) (z : 𝓀[k]), Le ϖ 1 ((x : k) - (s z : k)) ↔ IsLocalRing.residue _ x = z := by
    intro x z
    rw [le_one_iff h, ← hs z, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hs z,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    rfl
  refine ⟨Finset.univ.image fun z => (s z : k), ?_, ?_, fun x hx => ?_⟩
  · rw [Finset.card_image_of_injective (f := fun z => (s z : k)) _ (Subtype.val_injective.comp hs.injective), Finset.card_univ,
      GlobalTheory.SplitWeil.resCard, Nat.card_eq_fintype_card]
  · intro ρ hρ
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hρ
    exact le_zero_iff.2 (s z).2
  · let x' : 𝒪[k] := ⟨x, le_zero_iff.1 hx⟩
    refine ⟨s (IsLocalRing.residue _ x'), Finset.mem_image_of_mem _ (Finset.mem_univ _), (key x' _).2 rfl, fun ρ' hρ' h' => ?_⟩
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hρ'
    rw [(key x' z).1 h']

theorem count (h : IsUnif ϖ) {M : Type} (l : (M → ℂ) →ₗ[ℂ] ℂ) (S S' : Set M) (f : M → k) (s : k → M → M)
    (h1 : ∀ Y ∈ S', Le ϖ 0 (f Y)) (h2 : ∀ ρ, Le ϖ 0 ρ → ∀ Y, s ρ Y ∈ S ↔ Y ∈ S' ∧ Le ϖ 1 (f Y - ρ))
    (h3 : ∀ ρ, Le ϖ 0 ρ → l (fun Y => S.indicator 1 (s ρ Y)) = l (S.indicator 1)) :
    l (S'.indicator 1) = (GlobalTheory.SplitWeil.resCard k : ℂ) * l (S.indicator 1) := by
  classical
  obtain ⟨R, hc, hR, hx⟩ := exists_reps h
  have : S'.indicator (1 : M → ℂ) = ∑ ρ ∈ R, fun Y => S.indicator (1 : M → ℂ) (s ρ Y) := by
    funext Y
    rw [Finset.sum_apply]
    by_cases hY : Y ∈ S'
    · obtain ⟨ρ, hρ, h4, h5⟩ := hx _ (h1 Y hY)
      rw [Finset.sum_eq_single_of_mem ρ hρ, Set.indicator_of_mem hY, Set.indicator_of_mem ((h2 ρ (hR ρ hρ) Y).2 ⟨hY, h4⟩)]
      · rfl
      · intro ρ' hρ' hne
        exact Set.indicator_of_notMem (fun hm => hne (h5 ρ' hρ' ((h2 ρ' (hR ρ' hρ') Y).1 hm).2)) _
    · rw [Set.indicator_of_notMem hY, Finset.sum_eq_zero]
      intro ρ hρ
      exact Set.indicator_of_notMem (fun hm => hY ((h2 ρ (hR ρ hρ) Y).1 hm).1) _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_sum, Finset.sum_congr rfl fun ρ hρ => h3 ρ (hR ρ hρ), Finset.sum_const, hc, nsmul_eq_mul]

def Box (ϖ : kˣ) (e : Fin n → Fin d → ℤ) : Set (Matrix (Fin n) (Fin d) k) := {Y | ∀ x y, Le ϖ (e x y) (Y x y)}

def Piv (ϖ : kˣ) (a : Fin n) (i : Fin d) (e : Fin n → Fin d → ℤ) : Set (Matrix (Fin n) (Fin d) k) :=
  {Y | Y ∈ Box ϖ e ∧ valuation k (Y a i) = valuation k (ϖ : k) ^ e a i}

theorem box_SB (ϖ : kˣ) (e : Fin n → Fin d → ℤ) : (Box ϖ e).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact (Box ϖ e) := by
    have h : IsCompact (Set.pi Set.univ fun x : Fin n => Set.pi Set.univ fun y : Fin d =>
        {z : k | valuation k z ≤ valuation k (ϖ : k) ^ e x y}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _
    have e' : Box ϖ e = (Set.pi Set.univ fun x : Fin n => Set.pi Set.univ fun y : Fin d =>
        {z : k | valuation k z ≤ valuation k (ϖ : k) ^ e x y}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e']; exact h
  have ho : IsOpen (Box ϖ e) := by
    simp only [Box, Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    convert GlobalTheory.SplitWeil.Model.isOpen_int.preimage
      (f := fun A : Matrix (Fin n) (Fin d) k => A i j * (ϖ : k) ^ (-e i j)) (by fun_prop) using 1
    ext A
    have := le_mul_iff (ϖ := ϖ) (e := e i j) (x := A i j) (val_zpow (-e i j))
    rw [add_neg_cancel, le_zero_iff] at this
    exact this.symm
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hc.isClosed, ho⟩).isLocallyConstant

theorem piv_eq (h : IsUnif ϖ) (a : Fin n) (i : Fin d) (e e' : Fin n → Fin d → ℤ)
    (he : ∀ x y, e' x y = e x y + if x = a ∧ y = i then 1 else 0) :
    (Piv ϖ a i e).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) = (Box ϖ e).indicator 1 - (Box ϖ e').indicator 1 := by
  have key : ∀ Y, Y ∈ Box ϖ e' ↔ Y ∈ Box ϖ e ∧ valuation k (Y a i) ≠ valuation k (ϖ : k) ^ e a i := by
    intro Y
    constructor
    · intro hY
      refine ⟨fun x y => (hY x y).mono h (by rw [he]; split_ifs <;> omega), ?_⟩
      have := hY a i
      rw [he, if_pos ⟨rfl, rfl⟩] at this
      exact ((le_succ_iff h).1 this).2
    · rintro ⟨hY, hn⟩ x y
      rw [he]
      split_ifs with hxy
      · obtain ⟨rfl, rfl⟩ := hxy
        exact (le_succ_iff h).2 ⟨hY _ _, hn⟩
      · simpa using hY x y
  funext Y
  by_cases h1 : Y ∈ Box ϖ e <;> by_cases h2 : valuation k (Y a i) = valuation k (ϖ : k) ^ e a i <;>
    simp [Set.indicator, Piv, key, h1, h2]

theorem piv_SB (h : IsUnif ϖ) (a : Fin n) (i : Fin d) (e : Fin n → Fin d → ℤ) :
    (Piv ϖ a i e).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ SB (Matrix (Fin n) (Fin d) k) := by
  rw [piv_eq h a i e (fun x y => e x y + if x = a ∧ y = i then 1 else 0) fun _ _ => rfl]
  exact Submodule.sub_mem _ (box_SB _ _) (box_SB _ _)

theorem move (h : IsUnif ϖ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) (a : Fin n) (i : Fin d) (e e' : Fin n → Fin d → ℤ)
    (x₀ : Fin n) (y₀ : Fin d) (hne : ¬ (a = x₀ ∧ i = y₀)) (he : ∀ x y, e x y = e' x y + if x = x₀ ∧ y = y₀ then 1 else 0)
    (δ : Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k) (h0 : ∀ Y, δ Y x₀ y₀ = Y a i) (h1 : ∀ Y, δ Y a i = 0)
    (h2 : ∀ (t : k) Y, δ (Y + t • δ Y) = δ Y)
    (h3 : ∀ Y ∈ Box ϖ e', ∀ x y, Le ϖ (e' x y - (e' x₀ y₀ - e' a i)) (δ Y x y))
    (h4 : ∀ t : k, Le ϖ (e' x₀ y₀ - e' a i) t →
      l (fun Y => (Piv ϖ a i e).indicator 1 (Y + t • δ Y)) = l ((Piv ϖ a i e).indicator 1)) :
    l ((Piv ϖ a i e').indicator 1) = (GlobalTheory.SplitWeil.resCard k : ℂ) * l ((Piv ϖ a i e).indicator 1) := by
  set w := e' x₀ y₀ - e' a i with hw
  have hai : e a i = e' a i := by rw [he, if_neg hne, add_zero]
  have ht : ∀ ρ, Le ϖ 0 ρ → Le ϖ w (-(ρ * (ϖ : k) ^ w)) := fun ρ hρ => by
    have := (le_mul_iff (val_zpow w)).2 hρ
    rw [zero_add] at this
    simpa using (Le.zero w).sub this
  have hd : ∀ z : k, valuation k z = valuation k (ϖ : k) ^ e' a i →
      valuation k ((ϖ : k) ^ w * z) = valuation k (ϖ : k) ^ e' x₀ y₀ ∧ (ϖ : k) ^ w * z ≠ 0 := fun z hz => by
    have : valuation k ((ϖ : k) ^ w * z) = valuation k (ϖ : k) ^ e' x₀ y₀ := by
      rw [map_mul, val_zpow, hz, ← zpow_add₀ (u_pos ϖ).ne', hw, sub_add_cancel]
    refine ⟨this, fun h0 => ?_⟩
    rw [h0, map_zero] at this
    exact (zpow_pos (u_pos ϖ) _).ne this
  have hb : ∀ t, Le ϖ w t → ∀ Y ∈ Box ϖ e', Y + t • δ Y ∈ Box ϖ e' := fun t ht Y hY x y => by
    have := ht.mul (h3 Y hY x y)
    rw [add_sub_cancel] at this
    exact (hY x y).add this
  refine count h l _ _ (fun Y => Y x₀ y₀ / ((ϖ : k) ^ w * Y a i)) (fun ρ Y => Y + (-(ρ * (ϖ : k) ^ w)) • δ Y) ?_ ?_
    fun ρ hρ => h4 _ (ht ρ hρ)
  · rintro Y ⟨hY, hp⟩
    obtain ⟨h5, h6⟩ := hd _ hp
    rw [← le_mul_iff h5, div_mul_cancel₀ _ h6, zero_add]
    exact hY _ _
  · intro ρ hρ Y
    have hpiv : (Y + (-(ρ * (ϖ : k) ^ w)) • δ Y) a i = Y a i := by simp [h1]
    have hent : ∀ h6 : (ϖ : k) ^ w * Y a i ≠ 0, (Y x₀ y₀ / ((ϖ : k) ^ w * Y a i) - ρ) * ((ϖ : k) ^ w * Y a i) =
        (Y + (-(ρ * (ϖ : k) ^ w)) • δ Y) x₀ y₀ := fun h6 => by
      rw [sub_mul, div_mul_cancel₀ _ h6]; simp [h0]; ring
    constructor
    · rintro ⟨hZ, hp⟩
      rw [hpiv, hai] at hp
      obtain ⟨h5, h6⟩ := hd _ hp
      have hZ' : Y + (-(ρ * (ϖ : k) ^ w)) • δ Y ∈ Box ϖ e' := fun x y =>
        (hZ x y).mono h (by rw [he]; split_ifs <;> omega)
      have := hb (-(-(ρ * (ϖ : k) ^ w))) (by simpa using (Le.zero w).sub (ht ρ hρ)) _ hZ'
      rw [h2, neg_smul (-(ρ * (ϖ : k) ^ w)), add_neg_cancel_right] at this
      refine ⟨⟨this, hp⟩, ?_⟩
      rw [← le_mul_iff h5, hent h6, add_comm 1]
      have := hZ x₀ y₀
      rwa [he, if_pos ⟨rfl, rfl⟩] at this
    · rintro ⟨⟨hY, hp⟩, h7⟩
      obtain ⟨h5, h6⟩ := hd _ hp
      rw [← le_mul_iff h5, hent h6, add_comm 1] at h7
      refine ⟨fun x y => ?_, by rw [hpiv, hai]; exact hp⟩
      rw [he]
      split_ifs with hxy
      · obtain ⟨rfl, rfl⟩ := hxy
        exact h7
      · rw [add_zero]; exact hb _ (ht ρ hρ) Y hY x y

end PositivityTheory.ThKEnd.Cusp.LocB

end
end

-- bundled from Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.PlaContinuous
section
noncomputable section

namespace PositivityTheory.ThKEnd.Cusp

open scoped TensorProduct
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem pla_le_one_iff {v : Pl F} (x : Fv F v) :
    ValuativeRel.valuation (Fv F v) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v)) Valued.v).le_one_iff_le_one

theorem pla_continuous (v : Pl F) (t : E →ₐ[F] Fv F v) : Continuous (piW t) :=
  (continuous_splitProj t).comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap
    (fun a b => map_mul (evFin F v) a b) ((RestrictedProduct.continuous_eval v).comp continuous_snd))

theorem pla_int (z : AE F E) : ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, piW t z ∈ v.adicCompletionIntegers F := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v t => by rw [map_zero]; exact zero_mem _
  | add y z hy hz => filter_upwards [hy, hz] with v h h' t using by rw [map_add]; exact add_mem (h t) (h' t)
  | tmul a e =>
    have : Algebra.IsAlgebraic ℤ E := IsFractionRing.comap_isAlgebraic_iff.2 (inferInstance : Algebra.IsAlgebraic ℚ E)
    obtain ⟨d, hd, hi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) e).exists_integral_multiple
    have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
    have h1 : ∀ᶠ v : Pl F in cofinite, algebraMap F (Fv F v) (d : F)⁻¹ ∈ v.adicCompletionIntegers F :=
      (algebraMap F (Af F) (d : F)⁻¹).2
    have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F := a.2.2
    filter_upwards [h1, h2] with v hv hv' t
    have h3 : t (d • e) ∈ v.adicCompletionIntegers F := apply_coe_mem t (⟨d • e, hi⟩ : 𝓞 E)
    have h4 : t e = algebraMap F (Fv F v) (d : F)⁻¹ * t (d • e) := by
      rw [← Int.cast_smul_eq_zsmul F, map_smul, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul]
    show evFin F v a * t e ∈ _
    rw [h4]
    exact mul_mem hv' (mul_mem hv h3)

theorem places : Places := by
  intro F E _ _ _ _ _ σ h
  refine ⟨pla_continuous, fun z => (pla_int z).mono fun v hv t => (pla_le_one_iff _).2 (hv t), fun χ T hχ v hv t x hx => ?_,
    fun hf => ?_⟩
  · refine hχ (splitPrime t) (fun hm => hv (splitPrime_under t ▸ hm)) _ ?_
    have h1 : Valued.v (complMap (splitPrime_under t) (x : Fv F v)) ≤ 1 := complMap_mem _ ((pla_le_one_iff _).1 hx.le)
    have h2 : Valued.v (complMap (splitPrime_under t) ((x : Fv F v)⁻¹)) ≤ 1 :=
      complMap_mem _ ((pla_le_one_iff _).1 (by rw [map_inv₀, hx, inv_one]))
    have h3 : Valued.v (complMap (splitPrime_under t) (x : Fv F v)) ≠ 0 := by simp
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h3)] at h2
    exact le_antisymm h1 h2
  · obtain ⟨v, hv, hn⟩ := GlobalTheory.Orb.exists_split_place_notMem h hf.toFinset
    exact hv (hf.mem_toFinset.2 hn)

end PositivityTheory.ThKEnd.Cusp

end
end

