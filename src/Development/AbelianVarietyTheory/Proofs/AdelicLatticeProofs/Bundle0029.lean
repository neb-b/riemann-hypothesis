module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowImageUnitsCongruentOneModOfIsAdicComp
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem deep_smod_iff {O : Type} [CommRing O] (π a b : O) (n : ℕ) :
    a ≡ b [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule O O)] ↔ π ^ n ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem deep_exists_solution {O : Type} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (h : O[X]) (y : O) :
    ∃ x : O, x + π * h.eval x = y := by
  let T : O → O := fun x => y - π * h.eval x
  have hT : ∀ (n : ℕ) (a b : O), π ^ n ∣ a - b → π ^ (n + 1) ∣ T a - T b := by
    intro n a b hab
    have h1 : π ^ n ∣ h.eval a - h.eval b := hab.trans (Polynomial.sub_dvd_eval_sub a b h)
    obtain ⟨c, hc⟩ := h1
    refine ⟨-c, ?_⟩
    simp only [T]
    linear_combination (-π) * hc
  let s : ℕ → O := fun n => T^[n] 0
  have hs : ∀ n, s (n + 1) = T (s n) := fun n => Function.iterate_succ_apply' T n 0
  have h1 : ∀ n, π ^ n ∣ s n - s (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hT n _ _ ih
      rwa [← hs, ← hs] at this
  have h2 : ∀ m n, m ≤ n → π ^ m ∣ s m - s n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := dvd_add ih ((pow_dvd_pow π hmn).trans (h1 n))
      simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {π}) (M := O) inferInstance (f := s)
    (fun {m n} hmn => (deep_smod_iff π _ _ m).2 (h2 m n hmn))
  have hL' : ∀ n, π ^ n ∣ s n - L := fun n => (deep_smod_iff π _ _ n).1 (hL n)
  have h0 : L - T L = 0 := by
    refine IsHausdorff.haus (I := Ideal.span {π}) (M := O) inferInstance _ (fun n => ?_)
    rw [deep_smod_iff]
    have a1 := hT n _ _ (hL' n)
    rw [← hs] at a1
    have a2 := dvd_sub a1 (hL' (n + 1))
    have a3 := (pow_dvd_pow π (Nat.le_succ n)).trans a2
    convert a3 using 1
    ring
  refine ⟨L, ?_⟩
  simp only [T] at h0
  linear_combination h0

theorem deep_binomial {O : Type} [CommRing O] (t : O) (n : ℕ) :
    ∃ g : O[X], ∀ x : O, (1 + t * x) ^ n = 1 + n * t * x + t ^ 2 * x ^ 2 * g.eval x := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨g * (1 + C t * X) + C (n : O), fun x => ?_⟩
    rw [pow_succ, hg]
    simp only [eval_add, eval_mul, eval_one, eval_C, eval_X, Nat.cast_succ]
    ring

theorem deep_mem_oneUnits {O : Type} [CommRing O] (t : O) (u : Oˣ) :
    u ∈ oneUnits t ↔ ∃ x : O, (u : O) = 1 + t * x := by
  rw [oneUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]
  have : ((Ideal.Quotient.mk (Ideal.span {t}) : O →* O ⧸ Ideal.span {t}) (u : O) = 1) ↔
      Ideal.Quotient.mk (Ideal.span {t}) (u : O) = Ideal.Quotient.mk (Ideal.span {t}) 1 := Iff.rfl
  rw [this, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by linear_combination hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by linear_combination hx⟩

theorem deep_isUnit {O : Type} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (x : O) : IsUnit (1 + π * x) := by
  have h : π ∈ (⊥ : Ideal O).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {π}) (Ideal.mem_span_singleton_self π)
  have := Ideal.mem_jacobson_bot.1 h x
  rwa [add_comm] at this

theorem deep_units_pows :
    ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 →
      IsAdicComplete (Ideal.span {π}) O →
      pows p (oneUnits ((p : O) * π)) = oneUnits ((p : O) ^ 2 * π) ∧
        pTor p (oneUnits ((p : O) * π)) = 1 := by
  intro p O _ _ _ π hp hπ hc
  obtain ⟨g, hg⟩ := deep_binomial ((p : O) * π) p
  have key : ∀ x : O, (1 + (p : O) * π * x) ^ p =
      1 + (p : O) ^ 2 * π * (x + π * (X ^ 2 * g).eval x) := by
    intro x
    rw [hg]
    simp only [eval_mul, eval_pow, eval_X]
    ring
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  constructor
  · ext u
    rw [pows, Subgroup.mem_map, deep_mem_oneUnits]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, hx⟩ := (deep_mem_oneUnits _ _).1 hv
      exact ⟨_, by rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, hx, key]⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := deep_exists_solution π (X ^ 2 * g) y
      obtain ⟨v, hv⟩ := deep_isUnit π ((p : O) * x)
      have hv' : (v : O) = 1 + (p : O) * π * x := by rw [hv]; ring
      refine ⟨v, (deep_mem_oneUnits _ _).2 ⟨x, hv'⟩, Units.ext ?_⟩
      rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, hv', key, hx, hy]
  · rw [pTor, Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, one_mem _, one_pow _⟩, ?_⟩
    rintro ⟨u, hu, hu1⟩
    obtain ⟨x, hx⟩ := (deep_mem_oneUnits _ _).1 hu
    have h1 : (u : O) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hu1, Units.val_one]
    rw [hx, key] at h1
    have h2 : (p : O) ^ 2 * π * (x * (1 + π * (x * g.eval x))) = 0 := by
      simp only [eval_mul, eval_pow, eval_X] at h1
      linear_combination h1
    have h3 : x = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h (mul_ne_zero (pow_ne_zero _ hp0) hπ)
      · exact (mul_eq_zero.1 h).resolve_right (deep_isUnit π _).ne_zero
    refine Subtype.ext (Units.ext ?_)
    simp [hx, h3]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexTopOfGroupFg
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem card_quot_range_nsmul_eq_pow_finrank_mul_card_ker (M : Type) [AddCommGroup M]
    [AddGroup.FG M] (p : ℕ) (hp : 0 < p) :
    Nat.card (nsmulAddMonoidHom (α := M) p).ker ≠ 0 ∧
      (nsmulAddMonoidHom (α := M) p).range.index =
        p ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) p).ker := by
  obtain ⟨n, ι, _, q, hq, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (q i ^ e i)) :=
    Finite.of_equiv _ (DirectSum.linearEquivFunOnFintype ℤ ι _).toEquiv.symm
  set D := DirectSum ι fun i => ZMod (q i ^ e i)
  set P := Fin n →₀ ℤ
  have hker : Nat.card (nsmulAddMonoidHom (α := M) p).ker =
      Nat.card (nsmulAddMonoidHom (α := D) p).ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(φ x).2, ?_⟩
        invFun := fun y => ⟨φ.symm (0, y), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := congrArg φ x.2
      rw [nsmulAddMonoidHom_apply, map_nsmul, map_zero] at h
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
      exact congrArg Prod.snd h
    · have h := y.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h ⊢
      rw [← map_nsmul, Prod.smul_mk, smul_zero, h, Prod.mk_zero_zero, map_zero]
    · intro x
      apply Subtype.ext
      apply φ.injective
      have h := congrArg φ x.2
      rw [nsmulAddMonoidHom_apply, map_nsmul, map_zero] at h
      have h1 : p • (φ x).1 = 0 := congrArg Prod.fst h
      have h2 : (φ x).1 = 0 := (smul_eq_zero.mp h1).resolve_left hp.ne'
      simp only [AddEquiv.apply_symm_apply]
      exact Prod.ext h2.symm rfl
    · intro y
      apply Subtype.ext
      simp
  have hrange : (nsmulAddMonoidHom (α := M) p).range =
      AddSubgroup.comap φ.toAddMonoidHom
        ((nsmulAddMonoidHom (α := P) p).range.prod (nsmulAddMonoidHom (α := D) p).range) := by
    ext x
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_comap,
      AddSubgroup.mem_prod, AddEquiv.coe_toAddMonoidHom]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨(φ y).1, by rw [map_nsmul]; rfl⟩, ⟨(φ y).2, by rw [map_nsmul]; rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨φ.symm (a, b), φ.injective ?_⟩
      rw [map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_mk, ha, hb]
  have hindexD : (nsmulAddMonoidHom (α := D) p).range.index =
      Nat.card (nsmulAddMonoidHom (α := D) p).ker := by
    haveI : (nsmulAddMonoidHom (α := D) p).ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite
    exact AddSubgroup.index_range
  have hrank : Module.finrank ℤ M = n := by
    rw [φ.toIntLinearEquiv.finrank_eq]
    have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ P D)
    rw [LinearMap.range_eq_top.mpr fun x => ⟨(x, 0), rfl⟩, LinearMap.ker_fst, rank_top] at h
    have h0 : Module.rank ℤ (LinearMap.inr ℤ P D).range = 0 := by
      rw [rank_eq_zero_iff]
      rintro ⟨x, y, rfl⟩
      refine ⟨(Nat.card D : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
      apply Subtype.ext
      simp only [SetLike.val_smul, LinearMap.coe_inr, Submodule.coe_zero, natCast_zsmul]
      ext
      · simp
      · simpa using card_nsmul_eq_zero' (x := y)
    rw [h0, add_zero, rank_finsupp_self, Cardinal.mk_fin, Cardinal.lift_natCast] at h
    change Module.finrank ℤ (P × D) = n
    rw [Module.finrank, ← h]
    simp
  refine ⟨?_, ?_⟩
  · rw [hker]
    exact Nat.card_pos.ne'
  · rw [hrange, AddSubgroup.index_comap_of_surjective _ φ.surjective, AddSubgroup.index_prod,
      AddSubgroup.index_range_nsmul, Module.finrank_finsupp_self, Fintype.card_fin, hrank,
      hindexD, hker]


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.pIdx_top_of_fg : ∀ (p : ℕ) (G : Type) [CommGroup G] [Group.FG G],
    0 < p →
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) ≠ 0 ∧
      _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
        p ^ Module.finrank ℤ (Additive G) * _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) := by
  intro p G _ _ hp
  obtain ⟨h1, h2⟩ := card_quot_range_nsmul_eq_pow_finrank_mul_card_ker (Additive G) p hp
  have htor : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) =
      Nat.card (nsmulAddMonoidHom (α := Additive G) p).ker := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.ofMul x.1, ?_⟩
        invFun := fun y => ⟨y.1.toMul, Subgroup.mem_top _, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, ← ofMul_pow, x.2.2, ofMul_one]
    · have h := y.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h
      rw [← toMul_nsmul, h, toMul_zero]
  have hidx : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
      (nsmulAddMonoidHom (α := Additive G) p).range.index := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right, ← Subgroup.index_toAddSubgroup]
    congr 1
    ext x
    change Additive.toMul x ∈ Subgroup.map (powMonoidHom p) ⊤ ↔ _
    rw [Subgroup.mem_map, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨Additive.ofMul y, by
        rw [nsmulAddMonoidHom_apply, ← ofMul_pow, ← powMonoidHom_apply, hy, ofMul_toMul]⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.toMul y, Subgroup.mem_top _, by
        rw [powMonoidHom_apply, ← toMul_nsmul, ← nsmulAddMonoidHom_apply, hy]⟩
  exact ⟨htor ▸ h1, by rw [hidx, htor]; exact h2⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorPowerSumRightActionNormAndContinuity
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.ActNorm

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma tpow_apply_eq_prod {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ)
    (a b : Fin n → ι) : _root_.GlobalTheory.ClassFin.tpow n y a b = ∏ k, y (a k) (b k) := by
  simp [_root_.GlobalTheory.ClassFin.tpow]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma tpow_conjTranspose {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ) :
    (_root_.GlobalTheory.ClassFin.tpow n y)ᴴ = _root_.GlobalTheory.ClassFin.tpow n yᴴ := by
  ext a b
  simp [tpow_apply_eq_prod, conjTranspose_apply, star_prod]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma nsq_eq_sum_sum_norm_sq_components {ι : Type} [Fintype ι] {m : ℕ} (d : Fin m → ℕ)
    (x : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) :
    _root_.GlobalTheory.ClassFin.nsq x = ∑ i, ∑ a : Fin (d i) → ι, ‖x ⟨i, a⟩‖ ^ 2 := by
  unfold _root_.GlobalTheory.ClassFin.nsq _root_.GlobalTheory.ClassFin.TIdx at *
  exact Fintype.sum_sigma _

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma act_apply_eq_vecMul_tpow {ι : Type} [Fintype ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (y : Matrix ι ι ℂ) (i : Fin m)
    (a : Fin (d i) → ι) :
    _root_.GlobalTheory.ClassFin.act d v y ⟨i, a⟩ =
      ((fun b => v ⟨i, b⟩) ᵥ* _root_.GlobalTheory.ClassFin.tpow (d i) y) a := rfl

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma sum_norm_sq_vecMul_eq_of_mul_conjTranspose_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] (w : κ → ℂ)
    (M : Matrix κ κ ℂ) (hM : M * Mᴴ = 1) : ∑ c, ‖(w ᵥ* M) c‖ ^ 2 = ∑ a, ‖w a‖ ^ 2 := by
  have key : ∀ x : κ → ℂ, ((∑ c, ‖x c‖ ^ 2 : ℝ) : ℂ) = x ⬝ᵥ star x := by
    intro x
    push_cast
    simp [dotProduct, Complex.mul_conj']
  apply Complex.ofReal_injective
  rw [key, key, star_vecMul, dotProduct_mulVec, vecMul_vecMul, hM, vecMul_one]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma sum_norm_sq_vecMul_le_card_sq_mul_bound_sq {κ : Type} [Fintype κ] (w : κ → ℂ) (M : Matrix κ κ ℂ)
    (K : ℝ) (hK : ∀ a c, ‖M a c‖ ≤ K) :
    ∑ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ (Fintype.card κ : ℝ) ^ 2 * K ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
  have hc : ∀ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ (Fintype.card κ : ℝ) * K ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
    intro c
    have h1 : ‖(w ᵥ* M) c‖ ≤ ∑ a, ‖w a‖ * K := by
      simp only [vecMul, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hK a c) (norm_nonneg _)
    calc ‖(w ᵥ* M) c‖ ^ 2 ≤ (∑ a, ‖w a‖ * K) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = K ^ 2 * (∑ a, ‖w a‖) ^ 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ K ^ 2 * ((Fintype.card κ : ℝ) * ∑ a, ‖w a‖ ^ 2) := by
          gcongr
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖w a‖)
      _ = _ := by ring
  calc ∑ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ ∑ _c : κ, (Fintype.card κ : ℝ) * K ^ 2 * ∑ a, ‖w a‖ ^ 2 :=
        Finset.sum_le_sum fun c _ => hc c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma norm_tpow_apply_le_pow_of_forall_norm_le {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ) (B : ℝ)
    (hy : ∀ i j, ‖y i j‖ ≤ B) (a b : Fin n → ι) : ‖_root_.GlobalTheory.ClassFin.tpow n y a b‖ ≤ B ^ n := by
  rw [tpow_apply_eq_prod, norm_prod]
  calc ∏ k, ‖y (a k) (b k)‖ ≤ ∏ _k : Fin n, B :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hy _ _
    _ = B ^ n := by simp


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ), (∀ (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (U : Matrix ι ι ℂ), U * Uᴴ = 1 → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v U) = _root_.GlobalTheory.ClassFin.nsq v) ∧ (∀ C : ℝ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (y : Matrix ι ι ℂ), (∀ i j, ‖y i j‖ ≤ C) → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v y) ≤ C' * _root_.GlobalTheory.ClassFin.nsq v) ∧ ∀ v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ, Continuous (_root_.GlobalTheory.ClassFin.act d v) := by
  intro ι _ _ m d
  refine ⟨fun v U hU => ?_, fun C => ?_, fun v => ?_⟩
  · have hK : ∀ n, _root_.GlobalTheory.ClassFin.tpow n U * (_root_.GlobalTheory.ClassFin.tpow n U)ᴴ = 1 := by
      intro n
      have h := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).1 n
      rw [tpow_conjTranspose, ← h.2.1, hU, h.1]
    rw [nsq_eq_sum_sum_norm_sq_components, nsq_eq_sum_sum_norm_sq_components]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [act_apply_eq_vecMul_tpow]
    exact sum_norm_sq_vecMul_eq_of_mul_conjTranspose_eq_one _ _ (hK _)
  · set B := max C 0
    refine ⟨∑ i, (Fintype.card (Fin (d i) → ι) : ℝ) ^ 2 * (B ^ d i) ^ 2,
      Finset.sum_nonneg fun _ _ => by positivity, fun v y hy => ?_⟩
    have hyB : ∀ i j, ‖y i j‖ ≤ B := fun i j => (hy i j).trans (le_max_left _ _)
    rw [nsq_eq_sum_sum_norm_sq_components, nsq_eq_sum_sum_norm_sq_components, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [act_apply_eq_vecMul_tpow]
    refine (sum_norm_sq_vecMul_le_card_sq_mul_bound_sq _ _ _ (norm_tpow_apply_le_pow_of_forall_norm_le _ y B hyB)).trans ?_
    gcongr
    exact Finset.single_le_sum
      (f := fun i => (Fintype.card (Fin (d i) → ι) : ℝ) ^ 2 * (B ^ d i) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  · unfold _root_.GlobalTheory.ClassFin.act
    simp only [vecMul, dotProduct, tpow_apply_eq_prod]
    fun_prop

end GlobalTheory.ClassFin.ActNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealMulAbsNormCpowEqExpTsum
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem tsum_ideal_mul_absNorm_cpow_eq_exp_tsum :
    ∀ (K : Type) [Field K] [NumberField K] (X : Ideal (𝓞 K) → ℂ), X ⊥ = 0 → X ⊤ = 1 → (∀ I J, X (I * J) = X I * X J) → (∀ I, ‖X I‖ ≤ 1) → ∀ s : ℂ, 1 < s.re → ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  intro K _ _ X hbot htop hmul hle s hs
  have hnorm : ∀ P : HeightOneSpectrum (𝓞 K), 1 < Ideal.absNorm P.asIdeal := by
    intro P
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
    have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    omega
  refine GlobalTheory.Mem.tsum_eq_exp_tsum_neg_log_of_primes (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal)
    (fun P => P.prime) ?_ (fun I => X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ?_ ?_ ?_ ?_ ?_
  ·
    intro P Q h
    rw [Ideal.dvd_iff_le] at h
    exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h).symm
  · intro I J
    rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  · simp [Ideal.one_eq_top, htop]
  · intro I hI hfI
    have hbot' : I ≠ ⊥ := by
      rintro rfl; exact hfI (by simp [hbot])
    have htop' : I ≠ ⊤ := by rwa [← Ideal.one_eq_top]
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop'
    have hMbot : M ≠ ⊥ := fun h => hbot' (le_bot_iff.mp (h ▸ hIM))
    exact ⟨⟨M, hM.isPrime, hMbot⟩, (Ideal.dvd_iff_le).mpr hIM⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_)
      (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hle I)
  · intro P hP
    have hlt : ‖X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
      have hn := hnorm P
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hr : ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by simp; linarith)
      calc ‖X P.asIdeal‖ * ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re
          ≤ 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re :=
            mul_le_mul_of_nonneg_right (hle _) (by positivity)
        _ < 1 := by rw [one_mul]; exact hr
    rw [sub_eq_zero] at hP
    rw [← hP, norm_one] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory
end

