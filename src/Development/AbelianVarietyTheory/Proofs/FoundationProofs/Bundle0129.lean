module

public import Mathlib
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Formalism.JacquetSubsetSums.JacquetSubsetSum
public import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTorsionFreeOfCardQuotientPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem padicInt_torsionFree_of_card_quotient_pow (l : ℕ) [Fact l.Prime] (C : Type)
    [AddCommGroup C] [Module ℤ_[l] C] [Module.Finite ℤ_[l] C]
    (h : ∀ r : ℕ, 0 < r →
      Nat.card (C ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))) = l ^ r) :
    ∀ (r : ℕ) (c : C), (l : ℤ_[l]) ^ r • c = 0 → c = 0 := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let N : ℕ → AddSubgroup C := fun r =>
    (LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))).toAddSubgroup
  have hmem : ∀ r (x : C), x ∈ N r ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x := fun r x => Iff.rfl
  have hidx : ∀ r, 0 < r → (N r).index = l ^ r := fun r hr => h r hr
  let f : C →+ C := (LinearMap.lsmul ℤ_[l] C (l : ℤ_[l])).toAddMonoidHom
  have hf : ∀ x, f x = (l : ℤ_[l]) • x := fun x => rfl
  have hrange : f.range = N 1 := by
    ext x
    rw [hmem]
    simp only [AddMonoidHom.mem_range, hf, pow_one]
  have key : ∀ c : C, (l : ℤ_[l]) • c = 0 → ∀ k, 0 < k → c ∈ N k := by
    intro c hc k hk
    have h1 : N (k + 1) ≤ N 1 := by
      intro x hx
      obtain ⟨y, rfl⟩ := (hmem _ _).1 hx
      exact (hmem _ _).2 ⟨(l : ℤ_[l]) ^ k • y, by rw [smul_smul, ← pow_add, add_comm]⟩
    have h2 := AddSubgroup.relIndex_mul_index h1
    rw [hidx 1 one_pos, hidx (k + 1) k.succ_pos, pow_one, pow_succ] at h2
    have h3 : ((N (k + 1)).comap f).index = l ^ k := by
      rw [AddSubgroup.index_comap, hrange]
      exact Nat.eq_of_mul_eq_mul_right hl h2
    have h4 : N k ≤ (N (k + 1)).comap f := by
      intro x hx
      obtain ⟨y, rfl⟩ := (hmem _ _).1 hx
      exact (hmem _ _).2 ⟨y, by rw [hf, smul_smul, pow_succ']⟩
    have h5 := AddSubgroup.relIndex_mul_index h4
    rw [h3, hidx k hk] at h5
    have h6 : (N k).relIndex ((N (k + 1)).comap f) = 1 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hl k) (by rw [h5, one_mul])
    apply AddSubgroup.relIndex_eq_one.1 h6
    show f c ∈ N (k + 1)
    rw [hf, hc]
    exact zero_mem _
  have one : ∀ c : C, (l : ℤ_[l]) • c = 0 → c = 0 := by
    intro c hc
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := C)
      (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    rw [← Submodule.mem_bot ℤ_[l], ← hK, Submodule.mem_iInf]
    intro i
    obtain ⟨y, hy⟩ := (hmem _ _).1 (key c hc (i + 1) i.succ_pos)
    rw [← hy, pow_succ, mul_smul]
    refine Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ i) Submodule.mem_top
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  intro r
  induction r with
  | zero => intro c hc; simpa using hc
  | succ r ih =>
    intro c hc
    rw [pow_succ, mul_smul] at hc
    exact one c (ih _ hc)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceTUnitSetMuModelSmoothedSb
section
open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.LambdaValuationPowers

theorem pieceT_unitSet_muModel_smoothedSb : ∀ (p : ℕ) [Fact p.Prime] (N m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d a b t : ℤ) (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ m) → 0 < N → ¬ p ∣ N → 1 ≤ m → 3 ≤ k → ψ.IsPrimitive → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → Integral (p ^ m) (pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m)) ∧ ∀ r : ℕ, toQ (p ^ m) (pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m)) r = -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (N : K) ^ ((2 : ℤ) - k) * up (p ^ m) (GlobalTheory.LambdaValuationPowers.coPtSb N p m k ψ c d a b) r := by
  intro p _ N m k K _ _ ψ c d a b t ζ hp2 hζ hN hpN hm hk hψ hc hd ht
  have hS : ∀ r : ℕ, pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m) r = _ := fun r =>
    GlobalTheory.TameSmoothing.pieceT_unitSet_eq_four_pieceTRaw p N m m k K ψ c d (a * t, 0) (b * t, 0) ζ hζ hN hpN hm le_rfl hk hc hd r
  have e1 : ((c * (a * t), c * 0) : ℤ × ℤ) = (c * a * t, 0) := by ext <;> simp [mul_assoc]
  have e2 : ((d * (b * t), d * 0) : ℤ × ℤ) = (d * b * t, 0) := by ext <;> simp [mul_assoc]
  simp only [e1, e2] at hS
  obtain ⟨I1, T1⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ a b t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I2, T2⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ (c * a) b t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I3, T3⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ a (d * b) t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I4, T4⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ (c * a) (d * b) t ζ hp2 hζ hN hpN hm hk hψ ht
  refine ⟨fun n hn => ?_, fun r => ?_⟩
  · rw [hS n, I1 n hn, I2 n hn, I3 n hn, I4 n hn]; ring
  · simp only [toQ, up] at T1 T2 T3 T4 ⊢
    rw [hS, T1, T2, T3, T4]
    simp only [coPtSb]
    ring

end GlobalTheory.LambdaValuationPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsRangeOfMonicRoot
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem qAll_isBoundedAtImInfty {p : ℂ → Prop} {N : ℕ} {f : ℍ → ℂ} (hN : 0 < N) (h : QAll p N f) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  obtain ⟨a, ha, -⟩ := h
  exact (GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN ha).2

theorem isBoundedAtImInfty_of_monic_root {n : ℕ} {h : ℍ → ℂ} {s : Fin n → ℍ → ℂ}
    (hs : ∀ j, UpperHalfPlane.IsBoundedAtImInfty (s j))
    (hrel : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) : UpperHalfPlane.IsBoundedAtImInfty h := by
  have hb : ∀ τ, ‖h τ‖ ≤ 1 + ∑ j, ‖s j τ‖ := fun τ => _root_.GlobalTheory.monic_root_norm_le_one_add_sum n (fun j => s j τ) (h τ) (hrel τ)
  have hsum : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
    refine Asymptotics.IsBigO.add (Asymptotics.isBigO_refl _ _) ?_
    convert Asymptotics.IsBigO.sum (A := fun j τ => ‖s j τ‖) (s := Finset.univ) (fun j _ => (hs j).norm_left) using 1
    ext τ; simp [Finset.sum_apply]
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_of_le _ fun τ => ?_) hsum
  refine (hb τ).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

end GlobalTheory.FN

namespace GlobalTheory.FN

theorem qAll_range_of_monic_root : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (N n : ℕ) (h : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ) → (∀ j, QAll (· ∈ ε.range) N (s j)) → (∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) → QAll (· ∈ ε.range) N h := by
  intro Ω _ _ ε N n h s hN hh hper hs hrel
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.FN.hasQ_of_periodic_bounded N h hN hh hper
    (isBoundedAtImInfty_of_monic_root (fun j => qAll_isBoundedAtImInfty hN (hs j)) hrel)
  choose a ha hain using hs
  let p : ℕ → ℍ → ℂ := fun i => if hi : i < n then s ⟨i, hi⟩ else fun _ => 1
  let c : ℕ → ℕ → ℂ := fun i => if hi : i < n then a ⟨i, hi⟩ else fun k => if k = 0 then 1 else 0
  have hp : ∀ i, HasQ N (p i) (c i) := by
    intro i
    by_cases hi : i < n
    · simpa [p, c, hi] using ha ⟨i, hi⟩
    · simpa [p, c, hi] using HasQ.const N 1
  have hrel' : ∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * h τ ^ i = 0 := by
    intro τ
    rw [Finset.sum_range_succ, Finset.sum_range, add_comm, ← hrel τ]
    simp [p]
  have hQ := _root_.GlobalTheory.QFam.polyRel_qSeries N n h b p c hN hb hp hrel'
  set Q := ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i)) with hQdef
  have hcoeff : ∀ i, Q.coeff i = if i < n + 1 then PowerSeries.mk (c i) else 0 := by
    intro i
    rw [hQdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i (fun j => PowerSeries.mk (c j))]
    simp
  have hcn : PowerSeries.mk (c n) = 1 := by
    ext k
    simp [c, PowerSeries.coeff_one]
  have hQ0 : Q ≠ 0 := by
    intro h0
    have := hcoeff n
    rw [h0, if_pos (Nat.lt_succ_self n), hcn] at this
    simp at this
  have hcr : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range := by
    intro i k
    rw [hcoeff i]
    split_ifs with hi
    · rw [PowerSeries.coeff_mk]
      by_cases hin : i < n
      · simpa [c, hin] using hain ⟨i, hin⟩ k
      · simp only [c, hin, dite_false]
        split_ifs
        · exact ⟨1, map_one ε⟩
        · exact ⟨0, map_zero ε⟩
    · simp only [map_zero]
      exact ⟨0, map_zero ε⟩
  have key := _root_.GlobalTheory.PsRoot.coeff_mem_range_of_isRoot Ω ε (PowerSeries.mk b) Q hQ0 hcr hQ
  exact ⟨b, hb, fun k => by simpa using key k⟩

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbedding
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

section

variable (l : ℕ) [Fact l.Prime]

private theorem qzTor_smul_mk (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzTor_mk_eq_zero (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzTor_mk_surj (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

private theorem qzTor_key (r : ℕ) (x : ℤ_[l]) :
    x • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 ↔ PadicInt.toZModPow r x = 0 := by
  have hl : ((l : ℚ_[l]) ^ r) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  rw [qzTor_smul_mk, qzTor_mk_eq_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    have : ((z * (l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) = (z : ℚ_[l]) * (l : ℚ_[l]) ^ r := by
      push_cast; rfl
    rw [this, hz]
    field_simp
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    push_cast
    field_simp

end

theorem qz_torsion_zmod_embedding (l : ℕ) [Fact l.Prime] :
    (∀ a : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) ∧
    ∀ r : ℕ, ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧
      (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧
      ∀ (x : ℤ_[l]) (y : ZMod (l ^ r)), ι (PadicInt.toZModPow r x * y) = x • ι y := by
  have hp : l.Prime := Fact.out
  refine ⟨fun a => ?_, fun r => ?_⟩
  · obtain ⟨q, rfl⟩ := qzTor_mk_surj l a
    have hlt : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have hpos : (0 : ℝ) < (‖q‖ + 1)⁻¹ := by positivity
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hpos hlt
    refine ⟨r, ?_⟩
    rw [qzTor_smul_mk, qzTor_mk_eq_zero]
    have hle : ‖(l : ℚ_[l]) ^ r * q‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      calc ‖(l : ℚ_[l])‖ ^ r * ‖q‖ ≤ (‖q‖ + 1)⁻¹ * (‖q‖ + 1) :=
            mul_le_mul hr.le (by linarith) (norm_nonneg _) hpos.le
        _ = 1 := inv_mul_cancel₀ (by positivity)
    refine ⟨⟨_, hle⟩, ?_⟩
    push_cast
    rfl
  · have hl : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    set e : QZ l := QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) with he
    have hs : Function.Surjective (PadicInt.toZModPow (p := l) r) := by
      haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
      exact ZMod.ringHom_surjective _
    have hwd : ∀ x x' : ℤ_[l], PadicInt.toZModPow r x = PadicInt.toZModPow r x' →
        x • e = x' • e := by
      intro x x' h
      rw [← sub_eq_zero, ← sub_smul, he, qzTor_key, map_sub, h, sub_self]
    have hinv := Function.surjInv_eq hs
    let ι : ZMod (l ^ r) →+ QZ l := AddMonoidHom.mk' (fun y => Function.surjInv hs y • e) (by
      intro y y'
      rw [← add_smul]
      apply hwd
      rw [map_add (f := _), hinv, hinv, hinv])
    have hι : ∀ x : ℤ_[l], ι (PadicInt.toZModPow r x) = x • e := fun x =>
      hwd _ _ (hinv _)
    refine ⟨ι, ?_, fun a => ⟨fun ha => ?_, ?_⟩, fun x y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, he, qzTor_key] at hy
      exact hy
    · obtain ⟨q, rfl⟩ := qzTor_mk_surj l a
      rw [qzTor_smul_mk, qzTor_mk_eq_zero] at ha
      obtain ⟨z, hz⟩ := ha
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      rw [hι, he, qzTor_smul_mk, hz]
      congr 1
      push_cast
      field_simp
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, smul_smul, he, qzTor_key, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · obtain ⟨x', rfl⟩ := hs y
      rw [← map_mul, hι, hι, mul_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueTowerPowersLinearIndependentStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_tower_powers_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt (p := p) y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt (p := p) (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (d j ^ m / (p : Ω)) := by
  intro p hp Ω _ _ h E hE hq T N d hd hs
  classical
  have := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have mem_rad_iff (x : integralClosure (O0 p) Ω) :
      x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
        ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := by
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
      refine ⟨n + 1, n.succ_pos, ?_⟩
      have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
      have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
        rw [pow_succ, ← h1]; push_cast; field_simp
      rw [h2]
      exact (z * x).2
    · rintro ⟨m, -, hm⟩
      refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
      push_cast
      field_simp
  have isInt_inv (x : Ω) (hx0 : x ≠ 0)
      (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (x ^ m / (p : Ω))) :
      IsInt (p := p) x⁻¹ := by
    obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) :=
      hmax ▸ o0_isAdicComplete_span_p p
    have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
    let : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
    have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
      FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
    have : Algebra.IsAlgebraic (O0 p) Ω := h.alg
    have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
      Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
    obtain ⟨a, b, hb, h1, h2⟩ :=
      exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p) hirr x hx0
    rw [map_natCast] at h1 h2
    have hpi : IsIntegral (O0 p) (p : Ω) := by
      exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    by_cases ha : 0 < a
    · exfalso
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ) := ⟨(a - 1).toNat, by push_cast; omega⟩
      refine hx ⟨b, hb, ?_⟩
      have : x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n := by
        rw [zpow_natCast]; field_simp; ring
      rw [this]
      exact h1.mul (hpi.pow n)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
      refine IsIntegral.of_pow hb ?_
      have : x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n := by
        rw [zpow_neg, zpow_natCast, inv_pow]; field_simp
      rw [this]
      exact h2.mul (hpi.pow n)
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff]
  have : M.IsMaximal := ResidueIndep.rad_isMaximal h
  let : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  have : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · have h1 : (y : Ω) ≠ 0 := by
            intro hy0
            have : y = 0 := Subtype.ext hy0
            exact h0 (by rw [this, map_zero])
          have h2 := isInt_inv (y : Ω) h1 (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω := fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = d j := fun j hj => by simp only [d', dite_eq_left hj]
  have key := ResidueIndep.field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hE ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have hz : Ideal.Quotient.mk M (y ^ p - t ^ p ^ N) = 0 := by
        rw [RingHom.map_sub, RingHom.map_pow, RingHom.map_pow, hb, sub_self]
      have := (hmem (y ^ p - t ^ p ^ N)).1 hz
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact (hd j hj).1, rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hs)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_mul, map_pow] using this)
  intro j hj
  rw [← hd' j hj]
  exact (hmem _).1 (key j hj)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignEven
section
namespace GlobalTheory

theorem signEven : Formalism.PacketSums.SignEven := by
  intro p q h
  apply Even.neg_one_pow
  rw [Nat.even_mul]
  rcases Nat.even_or_odd p with hp | hp
  · exact Or.inl hp
  · right
    rcases Nat.even_or_odd q with hq | hq
    · exact hq
    · exact absurd (hp.add_odd hq) (Nat.not_even_iff_odd.mpr h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRepSubgroupEqZero
section
noncomputable section

namespace GlobalTheory.NoFixedCharSum

theorem sum_rep_subgroup_eq_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N]
    (h : ∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) : ∑ n : N, τ (n : G) = 0 := by
  ext v
  simp only [LinearMap.sum_apply, LinearMap.zero_apply]
  apply h
  intro m hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨m, hm⟩ : N)) _ _ ?_
  intro n
  simp [map_mul]

theorem noFixedSum : Formalism.PacketSums.NoFixedSum := by
  intro G V _ _ _ _ τ N _ h x y
  have h0 := sum_rep_subgroup_eq_zero τ N h
  have : ∑ n : N, τ (x * (n : G) * y) = τ x * (∑ n : N, τ (n : G)) * τ y := by
    simp [Finset.mul_sum, Finset.sum_mul, map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, this, h0]
  simp

end GlobalTheory.NoFixedCharSum
end
end

