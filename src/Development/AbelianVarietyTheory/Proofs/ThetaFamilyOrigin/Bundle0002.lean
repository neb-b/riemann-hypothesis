module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelOfPairing

section Abstract

variable {G U : Type} [Group G] [CommGroup U] {R : G → G → U → Prop} {M : ℕ}

theorem prod_pow_eq_one (cm : ∀ a b : G, Commute a b) {n : ℕ} (y : Fin n → G) (hy : ∀ i, y i ^ M = 1)
    (a : Fin n → ℕ) : (List.ofFn fun i => y i ^ a i).prod ^ M = 1 := by
  refine List.prod_induction (fun y => y ^ M = 1) (fun x y hx hy => ?_) (one_pow _) fun z hz => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hz
    rw [← pow_mul, Nat.mul_comm, pow_mul, hy, one_pow]

theorem rel_one (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {y : G} (hy : y ^ M = 1) :
    R 1 y 1 := by
  obtain ⟨c, hc, hc'⟩ := hu 1 y (one_pow _) hy
  have h := hm _ _ _ _ _ hc hc
  rw [_root_.mul_one] at h
  have e : c * c = c := hc' _ h
  have : c = 1 := by simpa using e
  exact this ▸ hc

theorem rel_pow (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {x y : G} {c : U}
    (h₁ : R 1 y 1) (h : R x y c) (a : ℕ) : R (x ^ a) y (c ^ a) := by
  induction a with
  | zero => simpa using h₁
  | succ a ih => rw [pow_succ, pow_succ]; exact hm _ _ _ _ _ ih h

theorem rel_prod (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {y : G}
    (h₁ : R 1 y 1) : ∀ {n : ℕ} (x : Fin n → G) (c : Fin n → U), (∀ i, R (x i) y (c i)) →
      R (List.ofFn x).prod y (∏ i, c i)
  | 0, _, _, _ => by simpa using h₁
  | n + 1, x, c, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact hm _ _ _ _ _ (h 0) (rel_prod hm h₁ _ _ fun i => h i.succ)

theorem exists_column (g : ℕ) (i : Fin (2 * g)) :
    ∃ j : Fin (2 * g), (stdSymp g i j = 1 ∨ stdSymp g i j = -1) ∧ ∀ i', i' ≠ i → stdSymp g i' j = 0 := by
  have hi := i.2
  by_cases h : (i : ℕ) < g
  · refine ⟨⟨i + g, by omega⟩, Or.inl (by simp [stdSymp, h]), fun i' hi' => ?_⟩
    have : (i' : ℕ) ≠ i := fun e => hi' (Fin.ext e)
    have := i'.2
    unfold stdSymp
    rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
  · refine ⟨⟨i - g, by omega⟩, Or.inr ?_, fun i' hi' => ?_⟩
    · unfold stdSymp
      rw [if_neg (by simp only; omega), if_pos (by simp only; omega)]
    · have : (i' : ℕ) ≠ i := fun e => hi' (Fin.ext e)
      have := i'.2
      unfold stdSymp
      rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]

theorem injective_comb (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {ζ : U} (hζ : IsPrimitiveRoot ζ M)
    {g : ℕ} (y : Fin (2 * g) → G) (hy : ∀ i, y i ^ M = 1) (hp : ∀ i j, R (y i) (y j) (ζ ^ stdSymp g i j))
    (c c' : Fin (2 * g) → Fin M)
    (e : (List.ofFn fun i => y i ^ (c i : ℕ)).prod = (List.ofFn fun i => y i ^ (c' i : ℕ)).prod) : c = c' := by
  funext i
  obtain ⟨j, hj, hj'⟩ := exists_column g i
  have h₁ := rel_one hu hm (hy j)
  have key : ∀ a : Fin (2 * g) → Fin M,
      R (List.ofFn fun i => y i ^ (a i : ℕ)).prod (y j) ((ζ ^ stdSymp g i j) ^ (a i : ℕ)) := fun a => by
    have h := rel_prod hm h₁ (fun i => y i ^ (a i : ℕ)) (fun i => (ζ ^ stdSymp g i j) ^ (a i : ℕ))
      fun i => rel_pow hm h₁ (hp i j) _
    rwa [Finset.prod_eq_single i (fun b _ hb => by rw [hj' b hb, zpow_zero, one_pow])
      (fun h => absurd (Finset.mem_univ _) h)] at h
  have k₁ := key c
  rw [e] at k₁
  have q := (hu _ _ (prod_pow_eq_one cm y hy _) (hy j)).unique k₁ (key c')
  have hζ' : IsPrimitiveRoot (ζ ^ stdSymp g i j) M := by
    rcases hj with hj | hj
    · rwa [hj, zpow_one]
    · rw [hj, zpow_neg, zpow_one]; exact hζ.inv
  exact Fin.ext (hζ'.pow_inj (c i).2 (c' i).2 q)

theorem surjective_comb (cm : ∀ a b : G, Commute a b) (hM : M ≠ 0) {n : ℕ} (y : Fin n → G)
    (hy : ∀ i, y i ^ M = 1) (hcard : Nat.card {x : G // x ^ M = 1} = M ^ n)
    (hinj : ∀ c c' : Fin n → Fin M,
      (List.ofFn fun i => y i ^ (c i : ℕ)).prod = (List.ofFn fun i => y i ^ (c' i : ℕ)).prod → c = c')
    (z : G) (hz : z ^ M = 1) : ∃ c : Fin n → Fin M, (List.ofFn fun i => y i ^ (c i : ℕ)).prod = z := by
  let f : (Fin n → Fin M) → {x : G // x ^ M = 1} := fun c => ⟨_, prod_pow_eq_one cm y hy fun i => (c i : ℕ)⟩
  have : Finite {x : G // x ^ M = 1} := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hM)
  have hb : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨fun c c' h => hinj c c' (congrArg Subtype.val h), by rw [hcard]; simp⟩
  obtain ⟨c, hc⟩ := hb.2 ⟨z, hz⟩
  exact ⟨c, congrArg Subtype.val hc⟩

end Abstract

end GlobalTheory.LevelOfPairing

namespace GlobalTheory


open LevelOfPairing in
theorem exists_level_of_pairing : GlobalFnsSt → WeilSt → MulNSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), IsPrimitiveRoot ze M → (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S), (M : K) ≠ 0 ∧ IsPrimitiveRoot (Units.map s.appTop.hom.toMonoidHom ze) M) → ∀ x : Fin (2 * P.g) → (baseOver S ⟶ P.A), (∀ i, x i ^ M = 1) → (∀ i j, WeilIs P.A P.L M (x i) (x j) (ze ^ stdSymp P.g i j)) → ∃ lev : Level P M ze, lev.pt = x := by
  intro hG hW hN S _ P M ze hze hK x hx hp
  have := P.isAb.comm
  have cm : ∀ (T : Over S) (a b : T ⟶ P.A), Commute a b := fun T a b => _root_.mul_comm a b
  have tor : ∀ (T : Over S) (h : T ⟶ baseOver S) (i), (h ≫ x i) ^ M = 1 := fun T h i => by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have ind : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (c c' : Fin (2 * P.g) → Fin M),
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ x i) (fun i => (c i : ℕ)) =
        linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ x i) (fun i => (c' i : ℕ)) →
      c = c' := by
    intro K _ s c c' e
    obtain ⟨hu, hm, -⟩ := hW S P M (Over.mk s)
    refine LevelOfPairing.injective_comb (R := fun a b u => WeilIs P.A P.L M a b u) (cm _) hu hm (hK K s).2 _
      (tor _ _) (fun i j => ?_) c c' e
    have h := CommPairing.weilIs_pull hG P.isAb P.isLB
      (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) (hp i j)
    exact (map_zpow (Units.map s.appTop.hom.toMonoidHom) ze _) ▸ h
  refine ⟨⟨x, hze, hx, fun K _ _ s => ind K s, fun K _ _ s z hz => ?_, hp⟩, rfl⟩
  have hM : M ≠ 0 := fun e => (hK K s).1 (by rw [e, Nat.cast_zero])
  exact LevelOfPairing.surjective_comb (cm _) hM _ (tor _ _)
    ((hN S P M (Nat.one_le_iff_ne_zero.2 hM)).2.2.2.2 K s (hK K s).1) (ind K s) z hz

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStdSympZmod
section
set_option autoImplicit false

namespace GlobalTheory.SympMod

theorem card_torsion_zmod {M d : ℕ} [NeZero M] (hd : d ∣ M) :
    Nat.card {a : ZMod M // d • a = 0} = d := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod M) d
  rw [Nat.card_zmod, Nat.gcd_eq_right hd] at h
  exact h

theorem exists_pair_eq_one {M g : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (N : Submodule (ZMod M) V)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // x ∈ N ∧ d • x = 0} = d ^ (2 * (g + 1))) :
    ∃ e ∈ N, ∃ f ∈ N, B e f = 1 := by
  have : IsPrincipalIdealRing (ZMod M) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod M)) (ZMod.ringHom_surjective _)
  obtain ⟨e, he, f, hf, h₁, h₂, h₃⟩ := exists_pair_dvd_of_bilinForm B N
  have hall : ∀ x ∈ N, ∀ y ∈ N, B e f ∣ B x y := by
    intro x hx y hy
    obtain ⟨b, hb⟩ := h₁ y hy
    obtain ⟨a, ha⟩ := h₂ x hx
    have k₁ : B (x - a • e) f = 0 := by simp [ha, mul_comm]
    have k := h₃ (x - a • e) (N.sub_mem hx (N.smul_mem _ he)) (y - b • f)
      (N.sub_mem hy (N.smul_mem _ hf)) (by simp [hb, mul_comm]) k₁
    rw [map_sub, map_smul, k₁, smul_zero, sub_zero] at k
    have : B x y = B (x - a • e) y + a * B e y := by simp
    rw [this]
    exact dvd_add k (Dvd.dvd.mul_left (h₁ y hy) a)
  have hu : IsUnit (B e f) := by
    by_contra hnu
    obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective (B e f)
    rw [← hm, ZMod.isUnit_iff_coprime, Nat.Prime.not_coprime_iff_dvd] at hnu
    obtain ⟨p, hp, ⟨c, rfl⟩, ⟨q, hq⟩⟩ := hnu
    have hkill : ∀ x ∈ N, q • x = 0 := by
      intro x hx
      refine hN _ (N.toAddSubgroup.nsmul_mem hx q) fun y hy => ?_
      obtain ⟨r, hr⟩ := hall x hx y hy
      rw [map_nsmul, LinearMap.smul_apply, hr, ← hm, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, ← mul_assoc,
        mul_comm q p, ← hq, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
    have hM : ∀ x : V, M • x = 0 := fun x => by
      rw [← Nat.cast_smul_eq_nsmul (ZMod M), ZMod.natCast_self, zero_smul]
    have k₁ := hc q ⟨p, by rw [hq, mul_comm]⟩
    have k₂ := hc M dvd_rfl
    have k₃ : Nat.card {x : V // x ∈ N ∧ q • x = 0} = Nat.card {x : V // x ∈ N ∧ M • x = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        ⟨fun h => ⟨h.1, hM x⟩, fun h => ⟨h.1, hkill x h.1⟩⟩)
    rw [k₁, k₂] at k₃
    have k₄ : q = M := Nat.pow_left_injective (by omega) k₃
    have k₅ := NeZero.pos M
    have := hp.two_le
    nlinarith
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  exact ⟨e, he, u • f, N.smul_mem _ hf, by simpa using hu⟩

theorem exists_isSymplecticFamily {M : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (hB : B.IsAlt) (g : ℕ) (N : Submodule (ZMod M) V)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // x ∈ N ∧ d • x = 0} = d ^ (2 * g)) :
    ∃ e f : Fin g → V, IsSymplecticFamily B e f (fun _ => 1) ∧ (∀ i, e i ∈ N) ∧ ∀ i, f i ∈ N := by
  induction g generalizing N with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0⟩
  | succ g ih =>
  obtain ⟨e, he, f, hf, hd⟩ := exists_pair_eq_one N hN hc
  have hd' : B f e = -1 := by rw [← hB.neg_eq, hd]
  let N' : Submodule (ZMod M) V := N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
  have hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0 := fun y => Iff.rfl
  have hpr : ∀ y ∈ N, y - B y f • e - B e y • f ∈ N' := fun y hy =>
    (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he)) (N.smul_mem _ hf),
      by simp [hd, hB.self_eq_zero], by simp [← hB.neg_eq y f, hd', hB.self_eq_zero]⟩
  have hdec : ∀ y ∈ N, ∃ a b : ZMod M, ∃ y' ∈ N', y = a • e + b • f + y' := fun y hy =>
    ⟨B y f, B e y, _, hpr y hy, by abel⟩
  obtain ⟨e', f', hs, he', hf'⟩ := ih N' (by
    intro x hx hx0
    refine hN x hx.1 fun y hy => ?_
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
    simp [hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2]) (by
    intro d hdM
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdM (NeZero.pos M)
    let F : {a : ZMod M // d • a = 0} × {a : ZMod M // d • a = 0} × {x : V // x ∈ N' ∧ d • x = 0} →
        {x : V // x ∈ N ∧ d • x = 0} := fun t =>
      ⟨t.1.1 • e + t.2.1.1 • f + t.2.2.1,
        N.add_mem (N.add_mem (N.smul_mem _ he) (N.smul_mem _ hf)) t.2.2.2.1.1, by
          rw [smul_add, smul_add, ← smul_assoc, ← smul_assoc, t.1.2, t.2.1.2, t.2.2.2.2]
          simp⟩
    have hF : Function.Bijective F := by
      constructor
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨y, hy, hy'⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨z, hz, hz'⟩⟩ h
        have h : a • e + b • f + y = a' • e + b' • f + z := congrArg Subtype.val h
        obtain rfl : b = b' := by
          simpa [hd, hB.self_eq_zero, ((hmem _).1 hy).2.1, ((hmem _).1 hz).2.1] using congrArg (B e) h
        obtain rfl : a = a' := by
          simpa [hd', hB.self_eq_zero, ((hmem _).1 hy).2.2, ((hmem _).1 hz).2.2] using congrArg (B f) h
        obtain rfl : y = z := add_left_cancel h
        rfl
      · rintro ⟨x, hx, hx'⟩
        have k₁ : d • B x f = 0 := by rw [← LinearMap.smul_apply, ← map_nsmul, hx']; simp
        have k₂ : d • B e x = 0 := by rw [← map_nsmul, hx', map_zero]
        refine ⟨⟨⟨B x f, k₁⟩, ⟨B e x, k₂⟩, ⟨_, hpr x hx, ?_⟩⟩, Subtype.ext ?_⟩
        · rw [smul_sub, smul_sub, ← smul_assoc, ← smul_assoc, k₁, k₂, hx']
          simp
        · show B x f • e + B e x • f + (x - B x f • e - B e x • f) = x
          abel
    have h := Nat.card_eq_of_bijective F hF
    rw [hc d hdM, Nat.card_prod, Nat.card_prod, card_torsion_zmod hdM,
      show d ^ (2 * (g + 1)) = d * (d * d ^ (2 * g)) by ring] at h
    exact Nat.eq_of_mul_eq_mul_left hd0 (Nat.eq_of_mul_eq_mul_left hd0 h))
  refine ⟨Fin.cons e e', Fin.cons f f', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (he' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.1]
    · simp [hs.left_left]
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (hf' _)).2.2]
    · simp [hB.eq_iff.1 ((hmem _).1 (hf' _)).2.2]
    · simp [hs.right_right]
  · intro i
    cases i using Fin.cases
    · simp [hd]
    · simp [hs.left_right_self]
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact absurd rfl hij
    · simp [((hmem _).1 (hf' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]
    · simpa using hs.left_right_ne _ _ fun a => hij (congrArg _ a)
  · intro i
    cases i using Fin.cases
    · exact he
    · exact (he' _).1
  · intro i
    cases i using Fin.cases
    · exact hf
    · exact (hf' _).1


open ReciprocityTheory.ChartRestriction.G.Out in
theorem exists_stdSymp_zmod {M g : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (hB : B.IsAlt) (hN : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // d • x = 0} = d ^ (2 * g)) :
    ∃ v : Fin (2 * g) → V, ∀ i k, B (v i) (v k) = (stdSymp g i k : ℤ) := by
  obtain ⟨e, f, hs, -, -⟩ := exists_isSymplecticFamily hB g ⊤ (fun x _ h => hN x fun y => h y trivial)
    (fun d hd => by simpa using hc d hd)
  let σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm
  refine ⟨Sum.elim e f ∘ σ, fun i k => ?_⟩
  obtain ⟨a, rfl⟩ := σ.symm.surjective i
  obtain ⟨b, rfl⟩ := σ.symm.surjective k
  simp only [Function.comp, Equiv.apply_symm_apply, stdSymp]
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g + a := fun _ => rfl
  rcases a with a | a <;> rcases b with b | b <;> have := a.2 <;> have := b.2 <;>
    simp only [l, r, Sum.elim_inl, Sum.elim_inr, hs.left_left, hs.right_right, hs.left_right, hs.right_left hB,
      Fin.ext_iff] <;> split_ifs <;> first | omega | simp

end GlobalTheory.SympMod

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Out in
theorem exists_stdSymp_of_alternating_pairing :
    ∀ (M g : ℕ) (G : Type) [CommGroup G] (R : Type) [CommRing R] [IsDomain R] (ζ : Rˣ), 0 < M →
    IsPrimitiveRoot ζ M → (∀ x : G, x ^ M = 1) →
    (∀ d : ℕ, d ∣ M → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) →
    ∀ e : G →* G →* Rˣ, (∀ x, e x x = 1) → (∀ x, (∀ y, e x y = 1) → x = 1) →
    ∃ x : Fin (2 * g) → G, ∀ i j, e (x i) (x j) = ζ ^ stdSymp g i j := by
  intro M g G _ R _ _ ze hM hz hG hc w halt hnd
  have : NeZero M := ⟨hM.ne'⟩
  have wm : ∀ x y, w x y ∈ Subgroup.zpowers ze := fun x y => by
    rw [hz.zpowers_eq, mem_rootsOfUnity, ← map_pow, hG, map_one]
  have hT : ∀ x : Additive G, M • x = 0 := fun x => hG x.toMul
  let _ : Module (ZMod M) (Additive G) := AddCommGroup.zmodModule hT
  let β : Additive G → Additive G → ZMod M := fun x y =>
    hz.zmodEquivZPowers.symm (Additive.ofMul ⟨w x.toMul y.toMul, wm _ _⟩)
  have βl : ∀ x x' y, β (x + x') y = β x y + β x' y := fun x x' y => by
    simp only [β, ← map_add (f := _)]
    exact congrArg _ (Subtype.ext (by
      show w (x.toMul * x'.toMul) y.toMul = w x.toMul y.toMul * w x'.toMul y.toMul
      rw [map_mul, MonoidHom.mul_apply]))
  have βr : ∀ x y y', β x (y + y') = β x y + β x y' := fun x y y' => by
    simp only [β, ← map_add (f := _)]
    exact congrArg _ (Subtype.ext (map_mul (w x.toMul) y.toMul y'.toMul))
  have βw : ∀ x y (n : ℤ), β x y = n ↔ w x.toMul y.toMul = ze ^ n := fun x y n => by
    simp only [β]
    rw [AddEquiv.symm_apply_eq, hz.zmodEquivZPowers_apply_coe_int]
    exact Subtype.ext_iff
  let B : LinearMap.BilinForm (ZMod M) (Additive G) := LinearMap.mk₂ _ β βl
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β · y) fun x x' => βl x x' y) c x) βr
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β x) (βr x)) c y)
  obtain ⟨v, hv⟩ := SympMod.exists_stdSymp_zmod (V := Additive G) (g := g) (B := B)
    (fun x => ((βw x x 0).2 (by simpa using halt _)).trans Int.cast_zero)
    (fun x hx => hnd x.toMul fun y => by
      have h := (βw x (Additive.ofMul y) 0).1 ((hx _).trans Int.cast_zero.symm)
      rwa [zpow_zero] at h) (fun d hd => hc d hd)
  exact ⟨fun i => (v i).toMul, fun i k => (βw _ _ _).1 (hv i k)⟩

end GlobalTheory
end

