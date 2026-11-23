module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PinsOfClosedSubgroupPadicCharacterInv
section
noncomputable def UpperTheory.Reformulated.B.Qe19.LiftEquiv :
    Prop :=
    ∀ (Γ X : Type) [inst : Group Γ] [inst_1 : MulAction Γ X],
      (∀ (x : X), Finite ↥(MulAction.stabilizer Γ x)) →
        ∀ (A B : Rep.{0, 0, 0} ℂ Γ) (f : A ⟶ B),
          Function.Surjective (⇑(Rep.Hom.hom f) : (↑A : Type) → (↑B : Type)) →
            ∀ (φ : X → (↑B : Type)),
              (∀ (g : Γ) (x : X),
                  φ (g • x) = ((B.ρ : Γ → (↑B : Type) →ₗ[ℂ] (↑B : Type)) g : (↑B : Type) → (↑B : Type)) (φ x)) →
                ∃ (ψ : X → (↑A : Type)),
                  (∀ (g : Γ) (x : X),
                      ψ (g • x) = ((A.ρ : Γ → (↑A : Type) →ₗ[ℂ] (↑A : Type)) g : (↑A : Type) → (↑A : Type)) (ψ x)) ∧
                    ∀ (x : X), (Rep.Hom.hom f : (↑A : Type) → (↑B : Type)) (ψ x) = φ x

private theorem UpperTheory.Reformulated.B.Qe19.fixed_lift {Γ : Type} [Group Γ] (H : Subgroup Γ) [Finite H]
    (A B : Rep.{0, 0, 0} ℂ Γ) (f : A ⟶ B) (hf : Function.Surjective (Rep.Hom.hom f))
    (b : B) (hb : ∀ h ∈ H, B.ρ h b = b) :
    ∃ a : A, (∀ h ∈ H, A.ρ h a = a) ∧ (Rep.Hom.hom f) a = b := by
  classical
  haveI := Fintype.ofFinite H
  obtain ⟨a, ha⟩ := hf b
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ k : H, A.ρ k a, ?_, ?_⟩
  · intro h hh
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : H)) _ _ ?_
    intro k
    simp [map_mul]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    have h1 : ∀ k : H, (Rep.Hom.hom f) (A.ρ k a) = b := by
      intro k
      rw [Rep.hom_comm_apply, ha, hb k k.2]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem UpperTheory.Reformulated.B.Qe19.pins_of_closed_subgroup_padic_character_inv :
    UpperTheory.Reformulated.B.Qe19.LiftEquiv := by
  intro Γ X _ _ hfin A B f hf φ hφ
  have h1 : ∀ x : X, ∃ a : A, (∀ h ∈ MulAction.stabilizer Γ x, A.ρ h a = a) ∧
      (Rep.Hom.hom f) a = φ x := by
    intro x
    haveI := hfin x
    refine UpperTheory.Reformulated.B.Qe19.fixed_lift _ A B f hf (φ x) ?_
    intro h hh
    rw [← hφ, MulAction.mem_stabilizer_iff.mp hh]
  choose a ha hfa using h1
  have h2 : ∃ r : X → X, (∀ (g : Γ) (x : X), r (g • x) = r x) ∧ ∀ x, ∃ g : Γ, g • r x = x := by
    refine ⟨fun x => (Quotient.mk (MulAction.orbitRel Γ X) x).out, ?_, ?_⟩
    · intro g x
      have : Quotient.mk (MulAction.orbitRel Γ X) (g • x) = Quotient.mk (MulAction.orbitRel Γ X) x :=
        Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g))
      simp only [this]
    · intro x
      have h := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ X) x)).symm
      exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  obtain ⟨r, hr, hg⟩ := h2
  choose s hs using hg
  refine ⟨fun x => A.ρ (s x) (a (r x)), ?_, ?_⟩
  · intro g x
    have hm : (s (g • x))⁻¹ * (g * s x) ∈ MulAction.stabilizer Γ (r x) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hs x, inv_smul_eq_iff, ← hr g x, hs]
    have h3 := congrArg (A.ρ (s (g • x))) (ha (r x) _ hm)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
    simp only [hr g x]
    exact h3.symm
  · intro x
    show (Rep.Hom.hom f) (A.ρ (s x) (a (r x))) = φ x
    rw [Rep.hom_comm_apply, hfa, ← hφ, hs]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PointFinitePower
section
theorem UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow :
    ∀ {O S : Type} [inst : CommRing O] [inst_1 : CommRing S]
    [inst_2 : Algebra O S] [IsNoetherianRing S] (m : Ideal S),
    (∀ (x : S), ∃ (a : O), x - (Algebra.algebraMap O S : O → S) a ∈ m) →
      ∀ (n : ℕ), ∃ (N : Submodule O S), N.FG ∧ ∀ (x : S), ∃ y ∈ N, x - y ∈ m ^ n := by
  intro O S _ _ _ _ m hm n
  induction n with
  | zero =>
    refine ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z : S, z ∈ Submodule.span S (s : Set S) →
        ∃ w ∈ Submodule.span O (s : Set S), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        exact ⟨z, Submodule.subset_span hz, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | zero =>
        exact ⟨0, Submodule.zero_mem _, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | add z z' _ _ h h' =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨w', hw', h'⟩ := h'
        refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
        have e : z + z' - (w + w') = (z - w) + (z' - w') := by ring
        rw [e]
        exact Submodule.add_mem _ h h'
      | smul c z hz h =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨a, ha⟩ := hm c
        refine ⟨a • w, Submodule.smul_mem _ a hw, ?_⟩
        have hz' : z ∈ m ^ n := by
          rw [← hs]
          exact hz
        have e : c • z - a • w
            = algebraMap O S a * (z - w) + z * (c - algebraMap O S a) := by
          rw [Algebra.smul_def a w, smul_eq_mul]
          ring
        rw [e]
        refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ h) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' ha
    refine ⟨N ⊔ Submodule.span O (s : Set S), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, h⟩ := key (x - y) hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rw [← sub_sub]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowCong
section
theorem UpperTheory.Reformulated.B.Qh11.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hb n)) hab
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowEig
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp8.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

theorem UpperTheory.Reformulated.B.Qp8.pow_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp8.Mat C N) (l : C) (w : Fin N → C),
      Matrix.mulVec y w = l • w → ∀ (m : ℕ), Matrix.mulVec (y ^ m) w = l ^ m • w := by
  intro C _ N y l w h m
  induction m with
  | zero => rw [pow_zero, pow_zero, one_smul, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowSubMem
section
theorem UpperTheory.Reformulated.B.Qk67.pow_sub_mem :
    ∀ {E : Type} [inst : Field E]
    [inst_1 : NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (x : NumberField.RingOfIntegers E),
    x ^ (Ideal.absNorm : Ideal (NumberField.RingOfIntegers E) → ℕ) w.asIdeal - x ∈ w.asIdeal := by
  intro E _ _ w x
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Ideal.absNorm w.asIdeal
      = Fintype.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← Ideal.Quotient.eq, map_pow, hcard]
  exact FiniteField.pow_card _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowSubOneMem
section
theorem UpperTheory.Reformulated.B.Qf4.pow_sub_one_mem :
    ∀ {S : Type} [inst : CommRing S] (J : Ideal S) (p : ℕ),
    Nat.Prime p → (↑p : S) ∈ J → ∀ (x : S), x - (1 : S) ∈ J → ∀ (j : ℕ), x ^ p ^ j - (1 : S) ∈ J ^ (j + (1 : ℕ)) := by
  intro S _ J p _ hp x hx j
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have h1 : x ^ p ^ j - 1 ∈ J := Ideal.pow_le_self (Nat.succ_ne_zero j) ih
    have h2 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i) ∈ J := by
      have h3 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i)
          = (∑ i ∈ Finset.range p, ((x ^ p ^ j) ^ i - 1)) + (p : S) := by
        simp [Finset.sum_sub_distrib]
      rw [h3]
      refine J.add_mem (J.sum_mem fun i _ => ?_) hp
      exact J.mem_of_dvd (sub_one_dvd_pow_sub_one _ i) h1
    rw [pow_succ p j, pow_mul, ← mul_geom_sum, pow_succ J (j + 1)]
    exact Ideal.mul_mem_mul ih h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrecompleteOfFinite
section
open TensorProduct in
private theorem precomplete_of_finite {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨c, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨c • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) c (AdicCompletion.of I M x)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

open Polynomial in
private theorem lift_idem {T : Type} [CommRing T] (I : Ideal T) [HenselianRing T I]
    (f : T ⧸ I) (hf : IsIdempotentElem f) :
    ∃ e : T, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = f := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  have hm : (X ^ 2 - X : T[X]).Monic := by
    nontriviality T
    apply monic_X_pow_sub
    simp
  have hf' : Ideal.Quotient.mk I a * Ideal.Quotient.mk I a = Ideal.Quotient.mk I a := hf
  obtain ⟨e, he, hea⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - X : T[X]) hm a
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [eval_sub, eval_pow, eval_X, map_sub, pow_two, map_mul, eval_mul]
      rw [hf', sub_self])
    (by
      have h : eval a (derivative (X ^ 2 - X : T[X])) = 2 * a - 1 := by
        simp
        ring
      rw [h, map_sub, map_mul, map_one, map_ofNat]
      refine IsUnit.of_mul_eq_one (2 * Ideal.Quotient.mk I a - 1) ?_
      linear_combination 4 * hf')
  refine ⟨e, ?_, Ideal.Quotient.eq.mpr hea⟩
  have : e ^ 2 - e = 0 := by simpa using he
  show e * e = e
  linear_combination this

private theorem artin_idem {A : Type} [CommRing A] [IsArtinianRing A] (J : Ideal A) :
    ∃ (e : A) (n : ℕ), IsIdempotentElem e ∧ 1 - e ∈ J ∧ ∀ x ∈ J, x ^ n * e = 0 := by
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun n => OrderDual.toDual (J ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  have h1 : J ^ n = J ^ (n + 1) := hn (n + 1) (by omega)
  have h2 : J ^ n = J ^ (n + n) := hn (n + n) (by omega)
  have hid : IsIdempotentElem (J ^ n) := by
    show J ^ n * J ^ n = J ^ n
    rw [← pow_add, ← h2]
  obtain ⟨f, hf, hJ⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp hid
  refine ⟨1 - f, n, hf.one_sub, ?_, ?_⟩
  · have : f ∈ J ^ (n + 1) := by
      rw [← h1, hJ]
      exact Submodule.mem_span_singleton_self f
    simpa using Ideal.pow_le_self (by omega) this
  · intro x hx
    have : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
    rw [hJ] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    have hf' : f * f = f := hf
    rw [← hc, smul_eq_mul]
    linear_combination (-c) * hf'

private theorem exists_scalar {Λ T : Type} [CommRing Λ] [CommRing T] [Algebra Λ T]
    {ι : Type} (t : ι → T) (a : ι → Λ) (h : Algebra.adjoin Λ (Set.range t) = ⊤) (J : Ideal T)
    (hJ : ∀ i, t i - algebraMap Λ T (a i) ∈ J) (s : T) :
    ∃ c : Λ, s - algebraMap Λ T c ∈ J := by
  have hs : s ∈ Algebra.adjoin Λ (Set.range t) := h ▸ Algebra.mem_top
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i, hJ i⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, ?_⟩
    have := J.add_mem hc hd
    convert this using 1
    rw [map_add (f := _)]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c * d, ?_⟩
    have := J.add_mem (J.mul_mem_right y hc) (J.mul_mem_left (algebraMap Λ T c) hd)
    convert this using 1
    rw [map_mul]; ring

private theorem maximal_of_scalar {Λ T : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing T]
    [Algebra Λ T] (J : Ideal T) (hne : J ≠ ⊤)
    (hm : Ideal.map (algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ≤ J)
    (hs : ∀ s : T, ∃ c : Λ, s - algebraMap Λ T c ∈ J) : J.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hne ((Ideal.eq_top_iff_one J).mpr h), fun K x hJK hxJ hxK => ?_⟩
  obtain ⟨c, hc⟩ := hs x
  by_cases hu : IsUnit c
  · have h1 : algebraMap Λ T c ∈ K := by
      have := K.sub_mem hxK (hJK hc)
      simpa using this
    exact (Ideal.eq_top_iff_one K).mp (K.eq_top_of_isUnit_mem h1 (hu.map _))
  · exfalso
    have h1 : algebraMap Λ T c ∈ J := hm (Ideal.mem_map_of_mem _ hu)
    have := J.add_mem hc h1
    exact hxJ (by simpa using this)

theorem UpperTheory.Reformulated.B.Qe2.locAbs :
    ∀ (Λ T : Type) [inst : CommRing Λ] [inst_1 : IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] [inst_4 : CommRing T] [inst_5 : Algebra Λ T] [Module.Finite Λ T]
    (ι : Type) (t : ι → T) (a : ι → Λ),
    Algebra.adjoin Λ (Set.range t) = ⊤ →
      ∃ (e : T),
        IsIdempotentElem e ∧
          (∀ (i : ι),
              ∃ (n : ℕ),
                (t i - (Algebra.algebraMap Λ T : Λ → T) (a i)) ^ n * e ∈
                  Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ)) ∧
            (1 : T) - e ∈
                Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                  Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i)) ∧
              (∀ (s : T),
                  ∃ (c : Λ),
                    s - (Algebra.algebraMap Λ T : Λ → T) c ∈
                      Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                        Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i))) ∧
                (e ≠ (0 : T) →
                  (Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                      Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i))).IsMaximal) := by
  intro Λ T _ _ _ _ _ _ _ ι t a h
  set I : Ideal T := Ideal.map (algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) with hI
  set J : Ideal T := I ⊔ Ideal.span (Set.range fun i : ι ↦ t i - algebraMap Λ T (a i)) with hJ
  have hmem : ∀ i, t i - algebraMap Λ T (a i) ∈ J := fun i =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hs := exists_scalar t a h J hmem
  by_cases htop : J = ⊤
  · exact ⟨0, IsIdempotentElem.zero, fun i => ⟨0, by simp⟩, by simp [htop], hs,
      fun h0 => absurd rfl h0⟩
  have hmax : J.IsMaximal := maximal_of_scalar J htop le_sup_left hs
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal Λ) T := precomplete_of_finite _ T
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal Λ) T := {}
  haveI : IsAdicComplete I T := (IsAdicComplete.map_algebraMap_iff _ _).mpr this
  haveI : IsArtinianRing (T ⧸ I) := by
    letI : Field (Λ ⧸ IsLocalRing.maximalIdeal Λ) := Ideal.Quotient.field _
    haveI : Module.Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) (T ⧸ I) :=
      Module.Finite.of_restrictScalars_finite Λ _ _
    exact IsArtinianRing.of_finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) (T ⧸ I)
  obtain ⟨f, n, hf, hfJ, hfn⟩ := artin_idem (J.map (Ideal.Quotient.mk I))
  obtain ⟨e, he, rfl⟩ := lift_idem I f hf
  refine ⟨e, he, fun i => ⟨n, ?_⟩, ?_, hs, fun _ => hmax⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
    exact hfn _ (Ideal.mem_map_of_mem _ (hmem i))
  · have h1 : Ideal.Quotient.mk I (1 - e) ∈ J.map (Ideal.Quotient.mk I) := by
      rwa [map_sub, map_one]
    have h2 := Ideal.mem_quotient_iff_mem (I := I) (J := J) le_sup_left (x := 1 - e)
    exact h2.mp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrecompleteOfPowLe
section
theorem UpperTheory.Reformulated.B.Qk41.precomplete_of_pow_le :
    ∀ {A : Type} [inst : CommRing A]
    {I J : Ideal A}, J ≤ I → ∀ {e : ℕ}, I ^ e ≤ J → ∀ [IsPrecomplete J A], IsPrecomplete I A := by
  intro A _ I J hJI e he hJ
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    SModEq.mono (Submodule.smul_mono_left (h1 m)) (hf (Nat.mul_le_mul_left _ hmn)))
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos e))).trans
    (SModEq.mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)) (hL n))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PreservedCoefficient
section
private theorem coeff_mem_of_mem_maximalIdeal {O σ : Type} [CommRing O] [IsLocalRing O]
    {g : MvPowerSeries σ O} (hg : g ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O))
    (b : σ →₀ ℕ) :
    MvPowerSeries.coeff b g ∈ IsLocalRing.maximalIdeal O ^ (1 - Finsupp.degree b) := by
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, Nat.sub_zero, pow_one, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← MvPowerSeries.isUnit_iff_constantCoeff]
    exact hg
  · have h1 : Finsupp.degree b ≠ 0 := fun h => hb ((Finsupp.degree_eq_zero_iff b).1 h)
    have h2 : 1 - Finsupp.degree b = 0 := by omega
    rw [h2, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem UpperTheory.Reformulated.B.PreservedCoefficient.pres_new_coeff :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    (N : ℕ),
    ∀ h ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ N,
      ∀ (a : σ →₀ ℕ),
        (MvPowerSeries.coeff a : MvPowerSeries σ O → O) h ∈
          IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (σ →₀ ℕ) → ℕ) a) := by
  intro O σ _ _ N
  classical
  induction N with
  | zero =>
    intro h _ a
    rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ N ih =>
    intro h hh
    rw [pow_succ] at hh
    refine Submodule.mul_induction_on hh ?_ ?_
    · intro f hf g hg a
      rw [MvPowerSeries.coeff_mul]
      refine Submodule.sum_mem _ fun p hp => ?_
      have hsum : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree a := by
        rw [← map_add (f := _), Finset.HasAntidiagonal.mem_antidiagonal.1 hp]
      have hmul := Ideal.mul_mem_mul (ih f hf p.1) (coeff_mem_of_mem_maximalIdeal hg p.2)
      rw [← pow_add] at hmul
      exact Ideal.pow_le_pow_right (by omega) hmul
    · intro f g hf hg a
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hf a) (hg a)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdE
section
noncomputable def UpperTheory.Reformulated.B.DaGva8.prodE :
    {G₁ G₂ : Type} →
      [inst : Group G₁] →
        [inst_1 : TopologicalSpace G₁] →
          [inst_2 : Group G₂] →
            [inst_3 : TopologicalSpace G₂] → (T₁ : Subgroup G₁) → (T₂ : Subgroup G₂) → ↥T₁ × ↥T₂ ≃ₜ* ↥(T₁.prod T₂) :=
  fun {_ _} _ _ _ _ T₁ T₂ =>
    { toFun := fun x => ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
      invFun := fun y => (⟨y.1.1, y.2.1⟩, ⟨y.1.2, y.2.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      continuous_invFun :=
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }
end

