module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Lemmata.GeneralBFactRest.Imports
public import Lemmata.GeneralBFactSide.Imports

@[expose] public section

-- bundled from ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.AssDim
section
namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem exists_assoc_step {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) :
    ∃ q ∈ associatedPrimes R (QuotSMulTop x M), p < q ∧ x ∈ q ∧ x ∉ p := by
  first | exact Bl.general_b_fact_rest.goal1 .. | (apply Bl.general_b_fact_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_rest.goal1 <;> assumption)

theorem length_le_of_isRegular_of_mem_associatedPrimes : ∀ (rs : List R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M],
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsRegular M rs → ∀ {p : Ideal R},
    p ∈ associatedPrimes R M → (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
  | [], M, _, _, _, _, _, p, hp => by
    have : p.IsPrime := hp.isPrime
    have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr this.ne_top
    simpa using ringKrullDim_nonneg_of_nontrivial
  | x :: rs', M, _, _, _, hm, reg, p, hp => by
    obtain ⟨hreg, hreg'⟩ := (isRegular_cons_iff M x rs').mp reg
    have hx : x ∈ maximalIdeal R := hm x List.mem_cons_self
    obtain ⟨q, hq, hpq, hxq, hxnp⟩ := exists_assoc_step hp hx hreg
    have ih := length_le_of_isRegular_of_mem_associatedPrimes rs'
      (fun r hr => hm r (List.mem_cons_of_mem _ hr)) hreg' hq
    have hpp : p.IsPrime := hp.isPrime
    have hxp : Ideal.Quotient.mk p x ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact hxnp
    have hdim : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) :=
      ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
        (Ideal.Quotient.factor_surjective hpq.le) (mem_nonZeroDivisors_of_ne_zero hxp)
        (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq)
    calc ((x :: rs').length : WithBot ℕ∞) = (rs'.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ q) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ p) := hdim

variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem ModDepthGE.le_ringKrullDim_quotient_of_mem_associatedPrimes {n : ℕ}
    (h : ModDepthGE R M n) {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  subst hlen
  exact length_le_of_isRegular_of_mem_associatedPrimes rs hmem hreg hp

end ReciprocityTheory.CA
end

-- bundled from ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
section
namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem isCM_iff_isCMMod : IsCM R ↔ IsCMMod R R := by
  have hd : Module.supportDim R R = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
  constructor
  · rintro ⟨h1, n, hn, h2⟩
    exact ⟨h1, Module.Finite.self R, n, hd.trans hn, h2⟩
  · rintro ⟨h1, -, n, hn, h2⟩
    exact ⟨h1, n, hd.symm.trans hn, h2⟩

theorem modDepthGE_congr {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ) : ModDepthGE R M n ↔ ModDepthGE R N n := by
  constructor
  · rintro ⟨rs, h1, h2, h3⟩
    exact ⟨rs, h1, h2, (e.isRegular_congr rs).mp h3⟩
  · rintro ⟨rs, h1, h2, h3⟩
    exact ⟨rs, h1, h2, (e.isRegular_congr rs).mpr h3⟩

theorem isCMMod_congr {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : IsCMMod R M ↔ IsCMMod R N := by
  have hs : Module.support R M = Module.support R N :=
    (Module.support_subset_of_injective e.toLinearMap e.injective).antisymm
      (Module.support_subset_of_surjective e.toLinearMap e.surjective)
  have hd : Module.supportDim R M = Module.supportDim R N := by
    unfold Module.supportDim
    rw [hs]
  constructor
  · rintro ⟨h1, h2, n, hn, h3⟩
    exact ⟨h1, Module.Finite.equiv e, n, hd.symm.trans hn, (modDepthGE_congr e n).mp h3⟩
  · rintro ⟨h1, h2, n, hn, h3⟩
    exact ⟨h1, Module.Finite.equiv e.symm, n, hd.trans hn, (modDepthGE_congr e n).mpr h3⟩

lemma isRegular_map_algebraMap_iff' {S M : Type*} [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] (rs : List R) :
    IsRegular M (rs.map (algebraMap R S)) ↔ IsRegular M rs := by
  open Pointwise in
  have key : ∀ l : List R,
      ((Ideal.ofList (l.map (algebraMap R S))) • (⊤ : Submodule S M)).restrictScalars R
        = Ideal.ofList l • (⊤ : Submodule R M) := by
    intro l
    induction l with
    | nil => simp
    | cons r l ih =>
      have ih' : ∀ y : M, y ∈ (Ideal.ofList (l.map (algebraMap R S))) • (⊤ : Submodule S M) ↔
          y ∈ Ideal.ofList l • (⊤ : Submodule R M) :=
        fun y => by rw [← ih, Submodule.restrictScalars_mem]
      have hr : ∀ y : M, y ∈ (algebraMap R S r) • (⊤ : Submodule S M) ↔
          y ∈ r • (⊤ : Submodule R M) := fun y => by
        simp [Submodule.mem_smul_pointwise_iff_exists, algebraMap_smul]
      ext m
      simp only [List.map_cons, Ideal.ofList_cons, Submodule.sup_smul,
        Submodule.ideal_span_singleton_smul, Submodule.restrictScalars_mem, Submodule.mem_sup, ih', hr]
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isRegular_iff,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h h'
    apply h
    apply Submodule.restrictScalars_injective R S M
    rw [key, Submodule.restrictScalars_top]
    exact h'
  · intro h h'
    apply h
    rw [← key, ← h', Submodule.restrictScalars_top]

lemma mk_mem_maximalIdeal_quot (I : Ideal R) [IsLocalRing (R ⧸ I)] {r : R}
    (hr : r ∈ maximalIdeal R) : Ideal.Quotient.mk I r ∈ maximalIdeal (R ⧸ I) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective v
  have h1 : r * s - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
  have h2 : r * s - 1 ∉ maximalIdeal R := by
    intro h
    have h' : r * s - (r * s - 1) ∈ maximalIdeal R :=
      (maximalIdeal R).sub_mem ((maximalIdeal R).mul_mem_right s hr) h
    rw [sub_sub_cancel] at h'
    exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top inferInstance) h'
  have h3 : IsUnit (r * s - 1) := by
    by_contra h
    exact h2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have h4 : IsUnit (Ideal.Quotient.mk I (r * s - 1)) := h3.map _
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr h1] at h4
  exact not_isUnit_zero h4

theorem depthGE_quotient_iff (I : Ideal R) [IsLocalRing (R ⧸ I)] (n : ℕ) :
    DepthGE (R ⧸ I) n ↔ ModDepthGE R (R ⧸ I) n := by
  have key : ∀ rs : List R, RingTheory.Sequence.IsRegular (R ⧸ I) (rs.map (Ideal.Quotient.mk I)) ↔
      RingTheory.Sequence.IsRegular (R ⧸ I) rs := fun rs => by
    have := isRegular_map_algebraMap_iff' (S := R ⧸ I) (M := R ⧸ I) rs
    rwa [Ideal.Quotient.algebraMap_eq] at this
  have hs : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  constructor
  · rintro ⟨rs, hlen, hmem, hreg⟩
    refine ⟨rs.map (Function.surjInv hs), by simp [hlen], ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hy' := hmem y hy
      rw [← Function.surjInv_eq hs y] at hy'
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy' ⊢
      exact fun hu => hy' (hu.map _)
    · have hl : (rs.map (Function.surjInv hs)).map (Ideal.Quotient.mk I) = rs := by
        simp [Function.comp_def, Function.surjInv_eq hs]
      rw [← key, hl]
      exact hreg
  · rintro ⟨rs, hlen, hmem, hreg⟩
    refine ⟨rs.map (Ideal.Quotient.mk I), by simp [hlen], ?_, (key rs).mpr hreg⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact mk_mem_maximalIdeal_quot I (hmem y hy)

theorem isCM_quotient_iff [IsNoetherianRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    IsCM (R ⧸ I) ↔ IsCMMod R (R ⧸ I) := by
  have hfin : Module.Finite R (R ⧸ I) :=
    Module.Finite.of_surjective (Submodule.mkQ I) (Submodule.mkQ_surjective I)
  have hd : Module.supportDim R (R ⧸ I) = ringKrullDim (R ⧸ I) := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient]
  constructor
  · rintro ⟨-, n, hn, h⟩
    exact ⟨inferInstance, hfin, n, hd.trans hn, (depthGE_quotient_iff I n).mp h⟩
  · rintro ⟨-, -, n, hn, h⟩
    exact ⟨inferInstance, n, hd.symm.trans hn, (depthGE_quotient_iff I n).mpr h⟩

theorem DepthGE.of_ringEquiv {S : Type*} [CommRing S] [IsLocalRing S] (e : R ≃+* S) {n : ℕ}
    (h : DepthGE R n) : DepthGE S n := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨rs.map (e : R →+* S), by simp [hlen], ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hy' := hmem y hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy' ⊢
    intro hu
    apply hy'
    simpa using hu.map (e.symm : S →+* R)
  · haveI h1 : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := ⟨by ext; simp, by ext; simp⟩
    have h2 : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := ⟨by ext; simp, by ext; simp⟩
    exact (LinearEquiv.isRegular_congr' (σ' := (e.symm : S →+* R)) e.toSemilinearEquiv rs).mp hreg

theorem IsCM.of_ringEquiv {S : Type*} [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    (h : IsCM R) : IsCM S := by
  obtain ⟨hN, n, hn, hd⟩ := h
  exact ⟨isNoetherianRing_of_ringEquiv R e, n, (ringKrullDim_eq_of_ringEquiv e).symm.trans hn,
    hd.of_ringEquiv e⟩

end ReciprocityTheory.CA
end

-- bundled from ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
section
namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem ModDepthGE.mono {m n : ℕ} (hmn : m ≤ n) (h : ModDepthGE R M n) : ModDepthGE R M m := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨rs.take m, by simp [hlen, hmn], fun r hr => hmem r (List.mem_of_mem_take hr), ?_⟩
  have hw : IsWeaklyRegular M (rs.take m) := by
    have := hreg.toIsWeaklyRegular
    rw [← List.take_append_drop m rs, isWeaklyRegular_append_iff] at this
    exact this.1
  refine ⟨hw, fun htop => hreg.top_ne_smul ?_⟩
  refine le_antisymm (htop.le.trans (Submodule.smul_mono_left ?_)) le_top
  exact Ideal.span_mono fun r hr => List.mem_of_mem_take hr

theorem ModDepthGE.of_quotSMulTop {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R (QuotSMulTop x M) n) : ModDepthGE R M (n + 1) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨x :: rs, by simp [hlen], ?_, (isRegular_cons_iff M x rs).mpr ⟨reg, hreg⟩⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hx
  · exact hmem r hr

theorem exch_socle {x y : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) {a : M} (ha : a ∉ x • (⊤ : Submodule R M))
    (hma : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M)) :
    ∃ b : M, b ∉ y • (⊤ : Submodule R M) ∧
      ∀ z ∈ maximalIdeal R, z • b ∈ y • (⊤ : Submodule R M) := by
  obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma y hy)
  refine ⟨b, ?_, ?_⟩
  · intro hby
    obtain ⟨b', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hby
    apply ha
    have : y • a = y • (x • b') := by rw [← hb, smul_comm]
    rw [ry this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · intro z hz
    obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma z hz)
    have : x • (z • b) = x • (y • c) := by
      rw [smul_comm x z, hb, smul_comm x y, hc, smul_comm]
    rw [rx this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

section Noeth

variable [IsNoetherianRing R]

theorem socle_of_max_mem_ass {N : Type*} [AddCommGroup N] [Module R N]
    (h : maximalIdeal R ∈ associatedPrimes R N) :
    ∃ a : N, a ≠ 0 ∧ ∀ z ∈ maximalIdeal R, z • a = 0 := by
  obtain ⟨-, a, ha⟩ := Submodule.isAssociatedPrime_iff.mp h
  refine ⟨a, ?_, fun z hz => ?_⟩
  · rintro rfl
    apply (maximalIdeal.isMaximal R).ne_top
    rw [ha, eq_top_iff]
    intro r _
    exact Submodule.mem_colon_singleton.mpr (by simp)
  · rw [ha] at hz
    simpa using Submodule.mem_colon_singleton.mp hz

theorem max_not_mem_ass_of_reg {N : Type*} [AddCommGroup N] [Module R N] {w : R}
    (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular N w) :
    maximalIdeal R ∉ associatedPrimes R N := by
  intro h
  obtain ⟨a, ha, hz⟩ := socle_of_max_mem_ass h
  exact ha (rw (show w • a = w • (0 : N) by rw [hz w hw, smul_zero]))

theorem max_not_mem_ass_swap {x y w : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular (QuotSMulTop y M) w) :
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x M) := by
  intro h
  obtain ⟨a, ha, hz⟩ := socle_of_max_mem_ass h
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have ha' : a ∉ x • (⊤ : Submodule R M) := fun h' => ha ((Submodule.Quotient.mk_eq_zero _).mpr h')
  have hz' : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M) := fun z hz0 =>
    (Submodule.Quotient.mk_eq_zero _).mp (by rw [Submodule.Quotient.mk_smul]; exact hz z hz0)
  obtain ⟨b, hb, hzb⟩ := exch_socle hy rx ry ha' hz'
  have hb0 : (Submodule.Quotient.mk b : QuotSMulTop y M) ≠ 0 :=
    fun h' => hb ((Submodule.Quotient.mk_eq_zero _).mp h')
  apply hb0
  apply rw
  show w • _ = w • (0 : QuotSMulTop y M)
  rw [smul_zero, ← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hzb w hw)

theorem exists_reg_both {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
    (h₁ : maximalIdeal R ∉ associatedPrimes R N₁) (h₂ : maximalIdeal R ∉ associatedPrimes R N₂) :
    ∃ z ∈ maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  first | exact Bl.general_b_fact_side.goal1 .. | (apply Bl.general_b_fact_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_side.goal1 <;> assumption)

end Noeth

section Main

variable [IsNoetherianRing R]

universe u in
theorem exists_regular_sequence_cons (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] {x : R},
      x ∈ maximalIdeal R → IsSMulRegular N x → ModDepthGE R N (n + 1) →
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular N (x :: rs) := by
  induction n with
  | zero =>
    intro N _ _ _ x hx reg h
    obtain ⟨rs, -, -, hreg⟩ := h
    have := hreg.nontrivial
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    exact ⟨[], rfl, by simp, (isRegular_cons_iff N x []).mpr ⟨reg, IsRegular.nil R _⟩⟩
  | succ n ih =>
    intro N _ _ _ x hx reg h
    obtain ⟨ys0, hlen, hmem, hreg⟩ := h
    rcases ys0 with _ | ⟨y, ys⟩
    · simp at hlen
    rcases ys with _ | ⟨y', ys'⟩
    · simp at hlen
    have hy : y ∈ maximalIdeal R := hmem y (by simp)
    have hy' : y' ∈ maximalIdeal R := hmem y' (by simp)
    have := hreg.nontrivial
    obtain ⟨ry, hys⟩ := (isRegular_cons_iff N y _).mp hreg
    have ry' : IsSMulRegular (QuotSMulTop y N) y' := ((isRegular_cons_iff _ _ _).mp hys).1
    have hAy := max_not_mem_ass_of_reg hy' ry'
    have hAx := max_not_mem_ass_swap hy reg ry hy' ry'
    obtain ⟨z, hz, rzx, rzy⟩ := exists_reg_both hAx hAy
    have hdy : ModDepthGE R (QuotSMulTop y N) (n + 1) :=
      ⟨y' :: ys', by simpa using hlen, fun r hr => hmem r (List.mem_cons_of_mem _ hr), hys⟩
    obtain ⟨zs, hzs, hzsm, hzreg⟩ := ih (QuotSMulTop y N) hz rzy hdy
    have h1 : IsRegular N (y :: z :: zs) := (isRegular_cons_iff N y _).mpr ⟨ry, hzreg⟩
    have h2 : IsRegular N (z :: y :: zs) := IsLocalRing.isRegular_of_perm h1 (List.Perm.swap z y zs)
    obtain ⟨rz, hyz⟩ := (isRegular_cons_iff N z _).mp h2
    have : Nontrivial (QuotSMulTop x N) := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    have : Nontrivial (QuotSMulTop z (QuotSMulTop x N)) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal _ hz
    have h3 : IsRegular N [x, z] :=
      (isRegular_cons_iff N x _).mpr ⟨reg, (isRegular_cons_iff _ z _).mpr ⟨rzx, IsRegular.nil R _⟩⟩
    have h4 : IsRegular N [z, x] := IsLocalRing.isRegular_of_perm h3 (List.Perm.swap z x [])
    have rxz : IsSMulRegular (QuotSMulTop z N) x :=
      ((isRegular_cons_iff _ x _).mp ((isRegular_cons_iff N z _).mp h4).2).1
    have hdz : ModDepthGE R (QuotSMulTop z N) (n + 1) := by
      refine ⟨y :: zs, by simp [hzs], fun r hr => ?_, hyz⟩
      rcases List.mem_cons.mp hr with rfl | hr
      exacts [hy, hzsm r hr]
    obtain ⟨ws, hws, hwsm, hwreg⟩ := ih (QuotSMulTop z N) hx rxz hdz
    have h5 : IsRegular N (z :: x :: ws) := (isRegular_cons_iff N z _).mpr ⟨rz, hwreg⟩
    have h6 : IsRegular N (x :: z :: ws) := IsLocalRing.isRegular_of_perm h5 (List.Perm.swap x z ws)
    refine ⟨z :: ws, by simp [hws], fun r hr => ?_, h6⟩
    rcases List.mem_cons.mp hr with rfl | hr
    exacts [hz, hwsm r hr]

end Main

variable [IsNoetherianRing R] [Module.Finite R M]

theorem exists_isRegular_cons_of_modDepthGE {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) {n : ℕ} (h : ModDepthGE R M (n + 1)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M (x :: rs) :=
  exists_regular_sequence_cons n M hx reg h

theorem ModDepthGE.quotSMulTop {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R M (n + 1)) : ModDepthGE R (QuotSMulTop x M) n := by
  obtain ⟨rs, hl, hm, hr⟩ := exists_isRegular_cons_of_modDepthGE hx reg h
  exact ⟨rs, hl, hm, ((isRegular_cons_iff M x rs).mp hr).2⟩

end ReciprocityTheory.CA
end

-- bundled from ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.IsCMOfIsRegularLocalRing
section
namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

theorem isCM_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsCM R := by
  have hd : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  refine ⟨inferInstance, (maximalIdeal R).spanFinrank, hd, ?_⟩
  obtain ⟨rs, hlen, reg, hm⟩ := ReciprocityTheory.CA.RegGens.exists_regular_gens R _ hd
  refine ⟨rs, hlen, fun r hr => ?_, reg⟩
  rw [← hm]
  exact Ideal.subset_span hr

end ReciprocityTheory.CA
end

