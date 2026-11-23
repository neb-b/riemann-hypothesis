module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubOneMulSumEq
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.TateInv

theorem sub_one_mul_sum {R : Type*} [CommRing R] (ω : R) (n : ℕ) :
    (ω - 1) * ∑ s ∈ Finset.range n, (s : R) * ω ^ s = n * ω ^ n - ω * ∑ s ∈ Finset.range n, ω ^ s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem sub_one_mul_sum_eq {Ω : Type*} [Field Ω] (ω : Ω) (p : ℕ) (h1 : ω ≠ 1) (hp : ω ^ p = 1) :
    (ω - 1) * ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s = p := by
  rw [sub_one_mul_sum, hp, geom_sum_eq h1, hp, sub_self, zero_div, mul_zero, sub_zero, mul_one]

theorem pow_apply_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t i : ℕ) : (γ ^ t) (ζ ^ i) = ζ ^ (i * a ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hγ, ← pow_mul, pow_succ]
    congr 1; ring

theorem pow_apply_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t : ℕ) {x : Ω} (hx : x ∈ Subring.closure {ζ}) : (γ ^ t) x ∈ Subring.closure {ζ} := by
  have h : Subring.closure {ζ} ≤ (Subring.closure {ζ}).comap ((γ ^ t : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω) := by
    rw [Subring.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy, SetLike.mem_coe, Subring.mem_comap]
    have := pow_apply_pow γ ζ a hγ t 1
    simp only [pow_one, one_mul] at this
    show (γ ^ t) ζ ∈ _
    rw [this]
    exact Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  exact h hx

theorem mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m)) (i : ℕ)
    (hi : ¬ p ^ (L - m) ∣ i) :
    ∃ H ∈ Subring.closure {ζ}, (p : Ω) * ζ ^ i = γ H - H := by
  have hp : p.Prime := hpf.out
  obtain ⟨hmL, K, d, u, hd, hu, he, -⟩ := GlobalTheory.K5.MonX.exists_pow_eq hp2 hm1 hi
  have hpL : p ^ L = p ^ (L - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hpm : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  set ω := ζ ^ (u * d * p ^ (L - 1)) with hω
  have hω1 : ω ≠ 1 := by
    rw [hω, Ne, hζ.pow_eq_one_iff_dvd, hpL]
    intro h
    have h' : p ^ (L - 1) * p ∣ p ^ (L - 1) * (u * d) := by rwa [mul_comm (p ^ (L - 1)) (u * d)]
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h'
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact hu h
    · exact hd h
  have hωp : ω ^ p = 1 := by
    rw [hω, ← pow_mul, hζ.pow_eq_one_iff_dvd]
    exact ⟨u * d, by rw [hpL]; ring⟩
  have hγω : γ ω = ω := by
    rw [hω, map_pow, hγ, ← pow_mul]
    have e : (1 + p ^ m) * (u * d * p ^ (L - 1)) = u * d * p ^ (L - 1) + p ^ L * (u * d * p ^ (m - 1)) := by
      rw [hpL, hpm]; ring
    rw [e, pow_add, pow_mul ζ (p ^ L), hζ.pow_eq_one, one_pow, mul_one]
  have hγtω : ∀ t : ℕ, (γ ^ t) ω = ω := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hγω]
  set S : Ω := ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s with hS
  have hγtS : ∀ t : ℕ, (γ ^ t) S = S := by
    intro t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_mul, map_natCast, map_pow, hγtω]
  have hK : (γ ^ K) (ζ ^ i) = ω * ζ ^ i := by
    rw [pow_apply_pow γ ζ _ hγ, he, pow_add, hω, mul_comm]
  have hωmem : ω ∈ Subring.closure {ζ} := Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  have hSmem : S ∈ Subring.closure {ζ} :=
    Subring.sum_mem _ fun s _ => Subring.mul_mem _ (natCast_mem _ s) (Subring.pow_mem _ hωmem _)
  have hH0 : S * ζ ^ i ∈ Subring.closure {ζ} :=
    Subring.mul_mem _ hSmem (Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _)
  refine ⟨∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i),
    Subring.sum_mem _ fun t _ => pow_apply_mem γ ζ _ hγ t hH0, ?_⟩
  have hγH : γ (∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i)) = ∑ t ∈ Finset.range K, (γ ^ (t + 1)) (S * ζ ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [pow_succ', AlgEquiv.mul_apply]
  rw [hγH, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (γ ^ t) (S * ζ ^ i)), pow_zero,
    AlgEquiv.one_apply, map_mul, hγtS, hK]
  have := sub_one_mul_sum_eq ω p hω1 hωp
  rw [← hS] at this
  linear_combination (-(ζ ^ i)) * this


open Classical in
theorem trace_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * (if p ^ (L - m) ∣ i then ζ ^ i else 0) := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := GlobalTheory.NTr.sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  split_ifs with hd
  · have h1 : (ζ ^ p ^ m) ^ i = 1 := by
      obtain ⟨j, hj⟩ := hd
      rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]


open Classical in
theorem key_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (ζ ^ i - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  rw [trace_mono p L m hm1 hm ζ hζ τ hτ i]
  split_ifs with hd
  · exact ⟨0, Subring.zero_mem _, ζ ^ i, by simp, rfl⟩
  · obtain ⟨H, hH, e⟩ := mono p hp2 L m hm1 ζ hζ γ hγ i hd
    exact ⟨H, hH, 0, by rw [sub_zero, e], rfl⟩


open Classical in
theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val)
    (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (y - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact key_mono p hp2 L m hm1 hm ζ hζ γ hγ τ hτ (Multiplicative.toAdd i)
  | zero => exact ⟨0, Subring.zero_mem _, 0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    obtain ⟨H2, h2, z2, e2, f2⟩ := hy
    exact ⟨H1 + H2, Subring.add_mem _ h1 h2, z1 + z2, by rw [map_add (f := _)]; linear_combination e1 + e2,
      by simp only [map_add (f := _), Finset.sum_add_distrib, f1, f2]; ring⟩
  | neg x _ hx =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    exact ⟨-H1, Subring.neg_mem _ h1, -z1, by rw [map_neg]; linear_combination -e1,
      by simp only [map_neg, Finset.sum_neg_distrib, f1]; ring⟩

theorem tate_inv : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F F' : Ω, InZl ε p L F → IsNT ε p L m F F' →
  ∀ γ : Ω ≃ₐ[ℚ] Ω, γ (zt ε p L) = zt ε p L ^ (1 + p ^ m) → ∃ H : Ω, InZl ε p L H ∧ (p : Ω) ^ c * (F - F') = γ H - H := by
  intro p hpf hp2
  refine ⟨1, ?_⟩
  intro Ω _ _ _ ε L m hm1 hmL F F' hF hNT γ hγ
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := GlobalTheory.NTr.zt_prim ε p L hp.pos
  obtain ⟨D, hD, hDF⟩ := hF
  obtain ⟨τ, hτ, hT⟩ := hNT
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨H, hH, z, e1, e2⟩ := key p hp2 L m hm1 hmL (zt ε p L) hζ γ hγ τ hτ _ hDF
  have hz : z = D * F' := by
    apply mul_left_cancel₀ hpN
    rw [← e2]
    simp only [map_mul, map_natCast, ← Finset.mul_sum]
    rw [← hT]; ring
  refine ⟨H / D, ⟨D, hD, by rwa [mul_div_cancel₀ _ hD0]⟩, ?_⟩
  rw [map_div₀, map_natCast, pow_one, ← sub_div, ← e1, hz, eq_div_iff hD0]
  ring

end GlobalTheory.TateInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotientStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
  GlobalTheory.K5.IsInt (p := p) (a / b) → a / b ∈ Lev T m := by
  intro p _ Ω _ _ hΩ T m hm a ha b hb hb0 hint
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T m
  obtain ⟨-, hrange⟩ := _root_.GlobalTheory.K5.LevEmb.emb_inj_range p Ω hΩ T m hm ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
  rw [← hrange] at ha hb ⊢
  obtain ⟨a', rfl⟩ := (AlgHom.mem_range ι).1 ha
  obtain ⟨b', rfl⟩ := (AlgHom.mem_range ι).1 hb
  rcases ValuationRing.dvd_total b' a' with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine (AlgHom.mem_range ι).2 ⟨c, ?_⟩
    rw [hc, map_mul, mul_div_cancel_left₀ _ hb0]
  · have ha0 : ι a' ≠ 0 := by
      intro h
      apply hb0
      rw [hc, map_mul, h, zero_mul]
    have hz0 : ι a' / ι b' ≠ 0 := div_ne_zero ha0 hb0
    have hzi : (ι a' / ι b')⁻¹ = ι c := by
      rw [inv_div, hc, map_mul, mul_div_cancel_left₀ _ ha0]
    have hmem := GlobalTheory.K5.LevClosed.mem_adjoin_inv_of_isIntegral (R := O0 p) hz0 hint
    rw [hzi] at hmem
    have hle : Algebra.adjoin (O0 p) {ι c} ≤ ι.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨c, rfl⟩)
    exact hle hmem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformPoleOrder
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem uniform_pole_order : ∀ (E : Subring ℂ) (M : ℕ) (f : ℍ → ℂ), 0 < M →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ) →
    (∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * f (γ • τ)) → ∃ w : ℕ, Lv E M w f := by
  intro E M f hM hinv hw
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  choose w hw using hw
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let lift : SL(2, ZMod M) → SL(2, ℤ) := fun g => if h : ∃ γ, red γ = g then h.choose else 1
  let W : ℕ := Finset.univ.sup fun g => w (lift g)
  refine ⟨W, hinv, fun γ => ?_⟩
  have hex : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
  have hl : lift (red γ) = hex.choose := dif_pos hex
  set γ' := lift (red γ) with hγ'
  have hred : red γ' = red γ := by rw [hl]; exact hex.choose_spec
  have hmem : γ * γ'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem']
    show red (γ * γ'⁻¹) = 1
    rw [map_mul, map_inv, hred, mul_inv_cancel]
  have hf : ∀ τ : ℍ, f (γ • τ) = f (γ' • τ) := fun τ => by
    have := hinv _ hmem (γ' • τ)
    rw [← this, ← mul_smul, inv_mul_cancel_right]
  have hle : w γ' ≤ W := Finset.le_sup (f := fun g => w (lift g)) (Finset.mem_univ (red γ))
  have hD : QAll (· ∈ E) M fun τ => DD τ ^ (W - w γ') :=
    QAllSubring.pow _ (eis_qAll M hM DD (Or.inr (Or.inr rfl)) E)
  have := QAllSubring.mul hD (hw γ')
  convert this using 2 with τ
  rw [hf τ, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringGaloisStableOfKummer
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory

theorem isPGroup_coatom_normal_index_eq {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (K : Subgroup P) (hK : IsCoatom K) :
    K.Normal ∧ K.index = p := by
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K Group.normalizerCondition_of_isNilpotent hK
  have hQ : IsPGroup p (P ⧸ K) := hP.to_quotient K
  have hidx : K.index ≠ 1 := fun h => hK.1 (Subgroup.index_eq_one.1 h)
  have hdvd : p ∣ Nat.card (P ⧸ K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hidx (by rw [Subgroup.index_eq_card, hn, pow_zero])
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have htop : (Subgroup.zpowers x).comap (QuotientGroup.mk' K) = ⊤ := by
    apply hK.2
    refine lt_of_le_of_ne ?_ ?_
    · intro k hk
      have : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      rw [Subgroup.mem_comap, this]
      exact one_mem _
    · intro h
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K x
      have : y ∈ K := by
        rw [h, Subgroup.mem_comap]
        exact Subgroup.mem_zpowers _
      exact hx1 ((QuotientGroup.eq_one_iff y).2 this)
  have hz : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K z
    have : y ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
      rw [htop]; exact Subgroup.mem_top _
    exact this
  have hcard : Nat.card (P ⧸ K) = p := by
    rw [← hx, ← Nat.card_zpowers, hz, Subgroup.card_top]
  exact ⟨hN, by rw [Subgroup.index_eq_card, hcard]⟩

theorem valuationSubring_galois_stable_of_kummer : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  intro l hl F L _ _ _ _ _ hP hζ W hW
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  let D : Subgroup (L ≃ₐ[F] L) :=
    { carrier := {σ | ∀ x, σ x ∈ W ↔ x ∈ W}
      mul_mem' := by
        intro a b ha hb x
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AlgEquiv.mul_apply, ha, hb]
      one_mem' := by intro x; simp
      inv_mem' := by
        intro a ha x
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (a⁻¹ x)]
        simp }
  suffices hD : D = ⊤ by
    intro τ x
    have hτ : τ ∈ D := hD ▸ Subgroup.mem_top τ
    exact hτ x
  by_contra hD
  obtain ⟨H, hH, hDH⟩ := (eq_top_or_exists_le_coatom D).resolve_left hD
  obtain ⟨hHn, hHi⟩ := isPGroup_coatom_normal_index_eq hP H hH
  haveI : IsGalois F (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
  have hfr : Module.finrank F (IntermediateField.fixedField H) = l := by
    have h1 := (letI : Module.Free (IntermediateField.fixedField H) L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank F (IntermediateField.fixedField H) L)
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F L,
      ← H.card_mul_index, hHi, mul_comm (Nat.card H)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  haveI : IsCyclic (IntermediateField.fixedField H ≃ₐ[F] IntermediateField.fixedField H) :=
    isCyclic_of_prime_card (p := l) (by rw [IsGalois.card_aut_eq_finrank, hfr])
  obtain ⟨ζ, hζ⟩ := hζ
  have hK : (primitiveRoots (Module.finrank F (IntermediateField.fixedField H)) F).Nonempty :=
    ⟨ζ, by rw [hfr, mem_primitiveRoots hl.pos]; exact hζ⟩
  obtain ⟨α, ⟨δ, hδ⟩, hα⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic F (IntermediateField.fixedField H) hK
  rw [hfr] at hδ
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h1 : (⊤ : IntermediateField F (IntermediateField.fixedField H)) = ⊥ := by
      rw [← hα]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 (zero_mem _)
    have h2 := congrArg
      (fun E : IntermediateField F (IntermediateField.fixedField H) => Module.finrank F E) h1
    simp only [IntermediateField.finrank_top', IntermediateField.finrank_bot] at h2
    exact hl.one_lt.ne' (hfr ▸ h2)
  have hθ0 : (α : L) ≠ 0 := fun h => hα0 (Subtype.ext h)
  have hθl : (α : L) ^ l ∈ (algebraMap F L).range := by
    refine ⟨δ, ?_⟩
    have := congrArg (fun y : IntermediateField.fixedField H => (y : L)) hδ
    simpa using this
  have hKθ : ∀ x ∈ IntermediateField.fixedField H, x ∈ IntermediateField.adjoin F {(α : L)} := by
    intro x hx
    have hm : x ∈ (IntermediateField.adjoin F {α}).map (IntermediateField.fixedField H).val :=
      ⟨⟨x, hx⟩, by rw [hα]; trivial, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at hm
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∉ H := by
    by_contra h
    exact hH.1 (eq_top_iff.2 fun g _ => by_contra fun hg => h ⟨g, hg⟩)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace (IntermediateField.fixedField H) L W (W.comap (τ : L →+* L))
    (fun a => (hW α hθ0 hθl τ a (hKθ a a.2)).symm)
  have hη : σ.restrictScalars F ∈ H := by
    refine (IntermediateField.fixingSubgroup_fixedField H).le ?_
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  have hτη : τ * σ.restrictScalars F ∈ D := fun x => hσ x
  exact hτ ((H.mul_mem_cancel_right hη).1 (hDH hτη))

end GlobalTheory
end

