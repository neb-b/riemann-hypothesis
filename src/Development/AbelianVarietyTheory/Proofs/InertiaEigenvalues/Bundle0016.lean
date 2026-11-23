module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantMatrixLiftOfAdicComplete
section
namespace GlobalTheory.InvariantLift

variable {G : Type} [Group G] {A : Type} [CommRing A] {r : ℕ}

theorem average_step (σ : G → A →+* A) (hσ : ∀ g h a, σ (g * h) a = σ g (σ h a))
    (M : G →* Matrix (Fin r) (Fin r) A) (hM : ∀ g h i j, σ g (M h i j) = M h i j)
    (N : Subgroup G) [hN : N.Normal] [Finite (G ⧸ N)] (τ : A) (hτ : ∀ g ∈ N, σ g τ = τ)
    (hτ1 : ∑ᶠ x : G ⧸ N, σ x.out τ = 1) (c d : A) (hd : ∀ g ∈ N, ∀ i j, d ∣ (M g - 1) i j)
    (W : Matrix (Fin r) (Fin r) A) (hW : ∀ g ∈ N, W.map (σ g) = W)
    (hc : ∀ g i j, c ∣ (M g * W.map (σ g) - W) i j) :
    ∃ W' : Matrix (Fin r) (Fin r) A, (∀ i j, c ∣ (W - W') i j) ∧ (∀ g ∈ N, W'.map (σ g) = W') ∧
      ∀ g i j, d ∣ (M g * W'.map (σ g) - W') i j := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _

  have dl : ∀ (e : A) (X : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ X i j) →
      ∀ (Y : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e X hX Y i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hX i k).mul_right _
  have dr : ∀ (e : A) (Y : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ Y i j) →
      ∀ (X : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e Y hY X i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hY k j).mul_left _

  have hfix : ∀ a : A, (∀ m ∈ N, σ m a = a) → ∀ g, ∀ n ∈ N, σ n (σ g a) = σ g a := by
    intro a ha g n hn
    have hm : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
    rw [← hσ, show n * g = g * (g⁻¹ * n * g) by group, hσ, ha _ hm]
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) (Fin r) A, U = τ • W := ⟨_, rfl⟩
  have hUfix : ∀ m ∈ N, ∀ k l, σ m (U k l) = U k l := by
    intro m hm k l
    have hWe : σ m (W k l) = W k l := congrFun (congrFun (hW m hm) k) l
    rw [hU, Matrix.smul_apply, smul_eq_mul, map_mul, hτ m hm, hWe]
  have hUl : ∀ g, ∀ n ∈ N, U.map (σ (n * g)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ]
    exact hfix _ (fun m hm => hUfix m hm k l) g n hn
  have hUr : ∀ g, ∀ n ∈ N, U.map (σ (g * n)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ, hUfix n hn]
  have hMfix : ∀ g h, (M h).map (σ g) = M h := by
    intro g h
    ext i j
    exact hM g h i j
  have hUmap : ∀ g h, (U.map (σ h)).map (σ g) = U.map (σ (g * h)) := by
    intro g h
    ext i j
    simp [hσ]
  have hsum : ∀ (f : A →+* A) (X : G ⧸ N → Matrix (Fin r) (Fin r) A),
      (∑ x, X x).map f = ∑ x, (X x).map f := by
    intro f X
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.sum_apply, map_sum]

  refine ⟨∑ x : G ⧸ N, M x.out * U.map (σ x.out), ?_, ?_, ?_⟩
  · intro i j
    have h1 : ∑ x : G ⧸ N, σ x.out τ = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact hτ1
    have hent : ∀ x : G ⧸ N, (M x.out * U.map (σ x.out)) i j =
        σ x.out τ * (M x.out * W.map (σ x.out)) i j := by
      intro x
      simp only [hU, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsplit : (W - ∑ x : G ⧸ N, M x.out * U.map (σ x.out)) i j =
        ∑ x : G ⧸ N, σ x.out τ * (W i j - (M x.out * W.map (σ x.out)) i j) := by
      rw [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_congr rfl (fun x _ => hent x)]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rw [hsplit]
    refine Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right ?_ _
    exact dvd_sub_comm.mp (by simpa only [Matrix.sub_apply] using hc x.out i j)
  · intro n hn
    rw [hsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.map_mul, hMfix, hUmap, hUl _ n hn]
  · intro g i j
    have hmul : M g * (∑ x : G ⧸ N, M x.out * U.map (σ x.out)).map (σ g) =
        ∑ x : G ⧸ N, M (g * x.out) * U.map (σ (g * x.out)) := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.map_mul, hMfix, hUmap, map_mul, mul_assoc]
    have hre : ∑ x : G ⧸ N, M x.out * U.map (σ x.out) =
        ∑ x : G ⧸ N, M (g • x).out * U.map (σ (g • x).out) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun y : G ⧸ N => M y.out * U.map (σ y.out))).symm
    rw [hmul, hre, ← Finset.sum_sub_distrib, Matrix.sum_apply]
    refine Finset.dvd_sum fun x _ => ?_
    obtain ⟨n, hn, hgx⟩ : ∃ n ∈ N, g * x.out = (g • x).out * n := by
      refine ⟨((g • x).out)⁻¹ * (g * x.out), ?_, (mul_inv_cancel_left _ _).symm⟩
      rw [← QuotientGroup.eq]
      simp only [QuotientGroup.out_eq']
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      simp only [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.mk_mul, QuotientGroup.out_eq',
        Quotient.out_eq]
    rw [hgx, map_mul, hUr _ n hn]
    have hfac : M (g • x).out * M n * U.map (σ (g • x).out) - M (g • x).out * U.map (σ (g • x).out)
        = M (g • x).out * ((M n - 1) * U.map (σ (g • x).out)) := by
      noncomm_ring
    rw [hfac]
    exact dr d _ (dl d _ (fun i' j' => by simpa [Matrix.sub_apply] using hd n hn i' j') _) _ i j

theorem exists_invariant_lift : ∀ (G : Type) [Group G] (A : Type) [CommRing A] (π : A), IsAdicComplete (Ideal.span {π}) A → ∀ (σ : G → A →+* A), (∀ g h a, σ (g * h) a = σ g (σ h a)) → (∀ g, σ g π = π) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) A), (∀ g h i j, σ g (M h i j) = M h i j) → ∀ (S : Set (Subgroup G)), (∀ N ∈ S, N.Normal ∧ Finite (G ⧸ N) ∧ ∃ τ : A, (∀ g ∈ N, σ g τ = τ) ∧ ∑ᶠ x : G ⧸ N, σ x.out τ = 1) → (∀ N ∈ S, ∀ k : ℕ, ∃ N' ∈ S, N' ≤ N ∧ ∀ g ∈ N', ∀ i j, π ^ k ∣ (M g - 1) i j) → ∀ (W₀ : Matrix (Fin r) (Fin r) A), (∃ N ∈ S, ∀ g ∈ N, W₀.map (σ g) = W₀) → (∀ g i j, π ∣ (M g * W₀.map (σ g) - W₀) i j) → ∃ W : Matrix (Fin r) (Fin r) A, (∀ i j, π ∣ (W - W₀) i j) ∧ ∀ g, M g * W.map (σ g) = W := by
  intro G _ A _ π hA σ hσ hσπ r M hM S hS hSk W₀ hW₀ hW₀c
  classical

  have hstep : ∀ (k : ℕ) (N : Subgroup G) (W : Matrix (Fin r) (Fin r) A), N ∈ S →
      (∀ g ∈ N, W.map (σ g) = W) → (∀ g i j, π ^ (k + 1) ∣ (M g * W.map (σ g) - W) i j) →
      ∃ (N' : Subgroup G) (W' : Matrix (Fin r) (Fin r) A), N' ∈ S ∧ (∀ g ∈ N', W'.map (σ g) = W') ∧
        (∀ g i j, π ^ (k + 1 + 1) ∣ (M g * W'.map (σ g) - W') i j) ∧
        ∀ i j, π ^ (k + 1) ∣ (W - W') i j := by
    intro k N W hNS hWN hWc
    obtain ⟨N', hN'S, hN'N, hN'd⟩ := hSk N hNS (k + 1 + 1)
    obtain ⟨hN'n, hN'f, τ, hτ, hτ1⟩ := hS N' hN'S
    haveI := hN'n
    haveI := hN'f
    obtain ⟨W', h1, h2, h3⟩ := GlobalTheory.InvariantLift.average_step σ hσ M hM N' τ hτ hτ1
      (π ^ (k + 1)) (π ^ (k + 1 + 1)) hN'd W (fun g hg => hWN g (hN'N hg)) hWc
    exact ⟨N', W', hN'S, h2, h3, h1⟩
  choose! Nf Wf hNf hWf hcf hdf using hstep
  obtain ⟨N₀, hN₀S, hN₀W⟩ := hW₀
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → Subgroup G × Matrix (Fin r) (Fin r) A,
      seq 0 = (N₀, W₀) ∧ ∀ k, seq (k + 1) = (Nf k (seq k).1 (seq k).2, Wf k (seq k).1 (seq k).2) :=
    ⟨fun k => Nat.rec (N₀, W₀) (fun k q => (Nf k q.1 q.2, Wf k q.1 q.2)) k, rfl, fun _ => rfl⟩
  have hP : ∀ k, (seq k).1 ∈ S ∧ (∀ g ∈ (seq k).1, (seq k).2.map (σ g) = (seq k).2) ∧
      ∀ g i j, π ^ (k + 1) ∣ (M g * (seq k).2.map (σ g) - (seq k).2) i j := by
    intro k
    induction k with
    | zero => exact ⟨by simp [hseq0, hN₀S], by simpa [hseq0] using hN₀W,
        by simpa [hseq0] using hW₀c⟩
    | succ k ih =>
      rw [hseqs]
      exact ⟨hNf k _ _ ih.1 ih.2.1 ih.2.2, hWf k _ _ ih.1 ih.2.1 ih.2.2, hcf k _ _ ih.1 ih.2.1 ih.2.2⟩
  have hd : ∀ k i j, π ^ (k + 1) ∣ (seq k).2 i j - (seq (k + 1)).2 i j := by
    intro k i j
    have := hdf k _ _ (hP k).1 (hP k).2.1 (hP k).2.2 i j
    rw [hseqs]
    simpa [Matrix.sub_apply] using this
  have hcauchy : ∀ m n, m ≤ n → ∀ i j, π ^ m ∣ (seq m).2 i j - (seq n).2 i j := by
    intro m n hmn i j
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : (seq m).2 i j - (seq (n + 1)).2 i j =
          ((seq m).2 i j - (seq n).2 i j) + ((seq n).2 i j - (seq (n + 1)).2 i j) := by ring
      rw [e]
      exact dvd_add ih ((pow_dvd_pow π (by omega)).trans (hd n i j))

  have hmod : ∀ (n : ℕ) (x y : A),
      x ≡ y [SMOD ((Ideal.span {π}) ^ n • (⊤ : Submodule A A))] ↔ π ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hlim : ∀ i j, ∃ L : A, ∀ n, π ^ n ∣ (seq n).2 i j - L := by
    intro i j
    obtain ⟨L, hL⟩ := hA.toIsPrecomplete.prec (f := fun n => (seq n).2 i j)
      (fun {m n} hmn => (hmod m _ _).mpr (hcauchy m n hmn i j))
    exact ⟨L, fun n => (hmod n _ _).mp (hL n)⟩
  choose L hL using hlim
  refine ⟨Matrix.of L, ?_, ?_⟩
  · intro i j
    have a := hd 0 i j
    have b := hL i j 1
    rw [hseq0] at a
    simp only [zero_add, pow_one] at a b
    have c : π ∣ W₀ i j - L i j := by
      have e : W₀ i j - L i j = (W₀ i j - (seq 1).2 i j) + ((seq 1).2 i j - L i j) := by ring
      rw [e]
      exact dvd_add a b
    simpa [Matrix.sub_apply] using dvd_sub_comm.mp c
  · intro g
    ext i j
    apply sub_eq_zero.mp
    rw [← Matrix.sub_apply]
    apply hA.toIsHausdorff.haus
    intro n
    rw [hmod, sub_zero]
    have key : (M g * (Matrix.of L).map (σ g) - Matrix.of L) i j =
        (∑ k, M g i k * σ g (L k j - (seq n).2 k j)) +
          (M g * (seq n).2.map (σ g) - (seq n).2) i j + ((seq n).2 i j - L i j) := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, map_sub,
        mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
    refine dvd_add (dvd_add (Finset.dvd_sum fun k _ => ?_) ?_) (hL i j n)
    · obtain ⟨e, he⟩ := dvd_sub_comm.mp (hL k j n)
      refine dvd_mul_of_dvd_right ⟨σ g e, ?_⟩ _
      rw [he, map_mul, map_pow, hσπ]
    · exact (pow_dvd_pow π (Nat.le_succ n)).trans ((hP n).2.2 g i j)

end GlobalTheory.InvariantLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrimitiveRootSubIsUnitOfDvdSubOne
section
open PowerSeries

namespace GlobalTheory


open IsLocalRing Polynomial in
theorem exists_isPrimitiveRoot_sub_isUnit_of_dvd_sub_one {l : ℕ} {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hl : l.Prime) (hu : ¬ IsUnit (l : O)) (e : ℕ) (he : e ∣ l - 1) :
    ∃ ω : O, IsPrimitiveRoot ω e ∧
      ∀ i j : ℕ, i < e → j < e → i ≠ j → IsUnit (ω ^ i - ω ^ j) := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  have he0 : e ≠ 0 := by rintro rfl; exact hl1 (zero_dvd_iff.1 he)
  have hel : e < l := by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hl1) he; omega

  have hlk : ((l : ℕ) : ResidueField O) = 0 := by
    have h : residue O (l : O) = 0 := (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hu)
    simpa using h
  have : CharP (ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl).2 hlk

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hg' : IsPrimitiveRoot g (l - 1) := by
    have h := IsPrimitiveRoot.orderOf g
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units] at h
  have hd : (l - 1) / e ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hl1) he) (Nat.pos_of_ne_zero he0)).ne'
  have hζ : IsPrimitiveRoot ((g ^ ((l - 1) / e) : (ZMod l)ˣ) : ZMod l) e := by
    have h := hg'.pow_of_dvd hd (Nat.div_dvd_of_dvd he)
    rw [Nat.div_div_self he hl1] at h
    exact IsPrimitiveRoot.coe_units_iff.2 h
  have hζk := hζ.map_of_injective (f := ZMod.castHom (dvd_refl l) (ResidueField O))
    (RingHom.injective _)
  obtain ⟨ω₀, hω₀⟩ := residue_surjective
    (ZMod.castHom (dvd_refl l) (ResidueField O) ((g ^ ((l - 1) / e) : (ZMod l)ˣ) : ZMod l))
  rw [← hω₀] at hζk

  have heu : IsUnit (e : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) ((CharP.cast_eq_zero_iff _ l e).1 h)
    omega
  have hω₀u : IsUnit ω₀ := (residue_ne_zero_iff_isUnit _).1 (hζk.ne_zero he0)
  obtain ⟨ω, hroot, hsub⟩ := HenselianRing.is_henselian (I := maximalIdeal O)
    (Polynomial.X ^ e - Polynomial.C 1 : O[X]) (monic_X_pow_sub_C 1 he0) ω₀
    (by
      rw [← residue_eq_zero_iff]
      simp [hζk.pow_eq_one])
    (by
      have h : IsUnit ((e : O) * ω₀ ^ (e - 1)) := heu.mul (hω₀u.pow _)
      simpa [Polynomial.derivative_X_pow] using h.map (Ideal.Quotient.mk (maximalIdeal O)))
  have hres : residue O ω = residue O ω₀ := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsub
  have hωe : ω ^ e = 1 := by
    have h := hroot.eq_zero
    simpa [sub_eq_zero] using h
  refine ⟨ω, ⟨hωe, fun k hk => hζk.dvd_of_pow_eq_one k ?_⟩, fun i j hi hj hij => ?_⟩
  · rw [← hres, ← map_pow, hk, map_one]
  · rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_pow, hres, sub_ne_zero]
    exact fun h => hij (hζk.pow_inj hi hj h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitMatrixOfPowSmulSpanInvert
section
namespace GlobalTheory

def powDenomSubring {S EE : Type} [CommRing S] [CommRing EE] (a : S →+* EE) (Q : S) :
    Subring EE where
  carrier := {e | ∃ (n : ℕ) (t : S), a Q ^ n * e = a t}
  mul_mem' := by
    rintro e f ⟨n, t, ht⟩ ⟨m, r, hr⟩
    refine ⟨n + m, t * r, ?_⟩
    rw [map_mul, ← ht, ← hr]; ring
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro e f ⟨n, t, ht⟩ ⟨m, r, hr⟩
    refine ⟨n + m, Q ^ m * t + Q ^ n * r, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← ht, ← hr]; ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro e ⟨n, t, ht⟩
    refine ⟨n, -t, ?_⟩
    rw [map_neg, ← ht]; ring

theorem eq_zero_of_sum_smul_eq_zero_of_powDenom {S EE W RW Y : Type} [CommRing S] [CommRing EE]
    [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW)
    (c : W →+* RW) (ψ : S →+* W) (Q : S) (hι : Function.Injective ι)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y)
    (hx : ∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) (E : Fin q → EE)
    (hE : ∀ m, E m ∈ powDenomSubring a Q) (h0 : ∑ m, ι (E m) • x m = 0) (m : Fin q) :
    E m = 0 := by
  choose n t ht using hE
  set N := ∑ m, n m with hN
  have hle : ∀ m, n m ≤ N := fun m =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  have h1 : ∀ m, a Q ^ N * E m = a (Q ^ (N - n m) * t m) := by
    intro m
    rw [map_mul, map_pow, ← ht, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle m)]
  have h2 := hx (fun m => ψ (Q ^ (N - n m) * t m)) (by
    have : ∀ m, c (ψ (Q ^ (N - n m) * t m)) • x m = ι (a Q ^ N) • (ι (E m) • x m) := by
      intro m
      rw [← hc, ← h1, map_mul, mul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h0, smul_zero])
  have h3 : ψ (Q ^ (N - n m) * t m) = 0 := congrFun h2 m
  have h4 : a Q ^ N * E m = 0 := by
    apply hι
    rw [h1, hc, h3, map_zero, map_zero]
  exact ((hQ.pow N).mul_right_eq_zero).1 h4

theorem exists_coeff_powDenom {S EE W RW Y : Type} [CommRing S] [CommRing EE]
    [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW)
    (c : W →+* RW) (ψ : S →+* W) (Q : S)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y) (y : Y)
    (hy : ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • y = ∑ i, c (ψ (s i)) • x i) :
    ∃ E : Fin q → EE, (∀ i, E i ∈ powDenomSubring a Q) ∧ y = ∑ i, ι (E i) • x i := by
  obtain ⟨k, s, hs⟩ := hy
  obtain ⟨v, hv⟩ := (hQ.pow k).exists_left_inv
  refine ⟨fun i => v * a (s i), fun i => ⟨k, s i, ?_⟩, ?_⟩
  · rw [← mul_assoc, mul_comm _ v, hv, one_mul]
  · have : ∀ i, ι (v * a (s i)) • x i = ι v • (c (ψ (s i)) • x i) := by
      intro i
      rw [map_mul, mul_smul, hc]
    simp only [this]
    rw [← Finset.smul_sum, ← hs, ← hc, ← map_pow, ← mul_smul, ← map_mul, hv, map_one, one_smul]

theorem exists_isUnit_matrix_of_pow_smul_span : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by
  intro S EE W RW Y _ _ _ _ _ _ a ι c ψ Q hι hc hQ q x z hx hz hx'
  choose A hAm hA using fun j => exists_coeff_powDenom a ι c ψ Q hc hQ x (z j) (hz j)
  choose B hBm hB using fun i => exists_coeff_powDenom a ι c ψ Q hc hQ z (x i) (hx' i)
  refine ⟨Matrix.of fun i j => A j i, ?_, fun j => by simpa using hA j⟩
  have hAB : (Matrix.of fun i j => A j i) * (Matrix.of fun j i => B i j)
      = (1 : Matrix (Fin q) (Fin q) EE) := by
    ext m i
    rw [← sub_eq_zero]
    refine eq_zero_of_sum_smul_eq_zero_of_powDenom a ι c ψ Q hι hc hQ x hx
      (fun m => ((Matrix.of fun i j => A j i) * (Matrix.of fun j i => B i j)) m i
        - (1 : Matrix (Fin q) (Fin q) EE) m i) ?_ ?_ m
    · intro m
      refine sub_mem ?_ ?_
      · rw [Matrix.mul_apply]
        exact sum_mem fun j _ => mul_mem (hAm j m) (hBm i j)
      · rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have h1 : ∑ m, ι ((1 : Matrix (Fin q) (Fin q) EE) m i) • x m = x i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro m _ hm
          simp [Matrix.one_apply_ne hm]
        · simp
      rw [h1]
      conv_rhs => rw [hB i]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hA j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, mul_comm, mul_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hAB)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLengthEqAndCardEqPowOfIsFiniteLength
section
namespace GlobalTheory

private lemma card_eq_card_residueField_of_isSimpleModule' (O : Type) [CommRing O]
    [IsLocalRing O] (S : Type) [AddCommGroup S] [Module O S] [IsSimpleModule O S] :
    Nat.card S = Nat.card (IsLocalRing.ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := O) (M := S)).mp ‹_›
  have hI' : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  subst hI'
  exact Nat.card_congr e.toEquiv

theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] (h : IsFiniteLength O M) :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨0, ?_, ?_⟩
    · simpa using (Module.length_eq_zero_iff (R := O) (M := M)).mpr ‹_›
    · simp [Nat.card_of_subsingleton (0 : M)]
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨n, hl, hc⟩ := ih
    refine ⟨n + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hl, Module.length_eq_one_iff.mpr ‹_›]
      push_cast
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      change Nat.card (M ⧸ N) * Nat.card N = _
      rw [card_eq_card_residueField_of_isSimpleModule' O (M ⧸ N), hc, pow_succ, mul_comm]

theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Finite M] :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength O M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitOfPowDvdSub
section
namespace GlobalTheory.LimitOfDivisibility

theorem exists_limit_of_pow_dvd_sub {R : Type} [inst : CommRing R] (p : ℕ)
    [IsAdicComplete (Ideal.span {(↑p : R)}) R] (f : ℕ → R)
    (h : ∀ (n : ℕ), (↑p : R) ^ n ∣ f (n + (1 : ℕ)) - f n) :
    ∃ (L : R), ∀ (n : ℕ), (↑p : R) ^ n ∣ L - f n := by
  have key : ∀ (n : ℕ) (x y : R),
      x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • ⊤ : Submodule R R)] ↔ (p : R) ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hc : ∀ m k : ℕ, (p : R) ^ m ∣ f (m + k) - f m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (p : R) ^ m ∣ f (m + k + 1) - f (m + k) :=
        (pow_dvd_pow _ (Nat.le_add_right m k)).trans (h (m + k))
      have h2 := dvd_add h1 ih
      have e : f (m + k + 1) - f (m + k) + (f (m + k) - f m) = f (m + (k + 1)) - f m := by
        rw [← Nat.add_assoc]; ring
      rwa [e] at h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R)}) (M := R) inferInstance (f := f) (by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [key, dvd_sub_comm]
    exact hc m k)
  refine ⟨L, fun n => ?_⟩
  rw [dvd_sub_comm]
  exact (key n _ _).1 (hL n)

end GlobalTheory.LimitOfDivisibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntOfCompatibleZmodPow
section
namespace GlobalTheory

theorem exists_padicInt_of_compatible_zmod_pow :
    ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)),
      (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) →
      ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  intro p _ c hc
  let f : ∀ n : ℕ, Polynomial ℤ →+* ZMod (p ^ n) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) (c n)
  have hf : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply Polynomial.ringHom_ext
    · intro a
      simp [f]
    · simpa [f] using hc k₁ k₂ hk
  refine ⟨PadicInt.lift hf Polynomial.X, fun n => ?_⟩
  have h := congrArg (fun g : Polynomial ℤ →+* ZMod (p ^ n) => g Polynomial.X)
    (PadicInt.lift_spec hf n)
  simpa [f] using h

end GlobalTheory
end

