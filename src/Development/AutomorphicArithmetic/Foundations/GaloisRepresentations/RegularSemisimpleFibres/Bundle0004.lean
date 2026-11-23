module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftBlocks
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma geo_mul (x l : ℕ) (hx : 1 ≤ x) :
    (∑ i ∈ Finset.range l, x ^ i) * (x - 1) = x ^ l - 1 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have := geom_sum_mul_add y l
  simp only [Nat.add_sub_cancel]
  omega

private lemma div_id (N a b S : ℕ) (ha : 0 < a) (hS : S * a = b) (hb : b ∣ N) (hb0 : 0 < b) :
    S * (N / b) = N / a := by
  obtain ⟨c, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left c hb0]
  subst hS
  rw [show S * a * c = a * (S * c) by ring, Nat.mul_div_cancel_left _ ha]

private lemma sub_one_dvd (x e : ℕ) : x - 1 ∣ x ^ e - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow x 1 e

private lemma ms_sum {α : Type*} (n : ℕ) (g : ℕ → α) :
    (Multiset.range n).map g = ∑ j ∈ Finset.range n, ({g j} : Multiset α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ih, add_comm,
      Multiset.singleton_add]

private lemma list_sum {α : Type*} (l : ℕ) (F : ℕ → Multiset α) :
    ((List.range l).map F).sum = ∑ i ∈ Finset.range l, F i := by
  induction l with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private lemma block_mul {α : Type*} (l m' : ℕ) (g : ℕ → α) :
    ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m', ({g (i + l * j)} : Multiset α) =
      ∑ n ∈ Finset.range (l * m'), ({g n} : Multiset α) := by
  induction m' with
  | zero => simp
  | succ m ih =>
    calc ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range (m + 1), ({g (i + l * j)} : Multiset α)
        = ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            {g (i + l * m)}) := Finset.sum_congr rfl fun i _ => Finset.sum_range_succ _ m
      _ = ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            ∑ i ∈ Finset.range l, ({g (i + l * m)} : Multiset α) := Finset.sum_add_distrib
      _ = ∑ n ∈ Finset.range (l * (m + 1)), ({g n} : Multiset α) := by
          rw [ih, Nat.mul_succ, Finset.sum_range_add]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

private lemma perm_map {α : Type*} (l m : ℕ) (hc : Nat.Coprime l m) (hm : 0 < m) (G : ℕ → α)
    (hG : ∀ n, G (n + m) = G n) :
    (Multiset.range m).map (fun j => G (l * j)) = (Multiset.range m).map G := by
  have hper : Function.Periodic G m := hG
  have hinj : Set.InjOn (fun j => l * j % m) (Finset.range m : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < m := by simpa using hx
    have hy' : y < m := by simpa using hy
    have h1 : l * x ≡ l * y [MOD m] := hxy
    have h2 : x ≡ y [MOD m] := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hx' hy'
  have himg : (Finset.range m).image (fun j => l * j % m) = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hm)
    · rw [Finset.card_image_of_injOn hinj]
  rw [ms_sum, ms_sum]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun j _ => by rw [hper.map_mod_nat]

private def lbk (Q q : ℕ) (p : ℕ × ℕ) : Multiset (ℕ × ZMod (Q - 1)) :=
  (Multiset.range p.1).map fun j =>
    ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))

private lemma lbk_dvd (Q q l m' k : ℕ) :
    ((List.range l).map fun i => lbk Q (q ^ l) (m', k * q ^ i)).sum = lbk Q q (l * m', k) := by
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j =>
    ((1 : ℕ), ((k * q ^ j * ((Q - 1) / (q ^ (l * m') - 1)) : ℕ) : ZMod (Q - 1))) with hGdef
  have h1 : ∀ i, lbk Q (q ^ l) (m', k * q ^ i) =
      ∑ j ∈ Finset.range m', ({G (i + l * j)} : Multiset _) := by
    intro i
    rw [← ms_sum (n := m') (g := fun j => G (i + l * j))]
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef, ← pow_mul, pow_add, mul_assoc]
  have h2 : lbk Q q (l * m', k) = (Multiset.range (l * m')).map G := rfl
  rw [list_sum, h2, ms_sum, ← block_mul]
  exact Finset.sum_congr rfl fun i _ => h1 i

private lemma lbk_ndvd (Q q l f m k : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f)
    (hm : 0 < m) (hmf : m ∣ f) (hnd : ¬ l ∣ m) :
    lbk Q (q ^ l) (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) = lbk Q q (m, k) := by
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hql : 1 < (q ^ l) ^ m := Nat.one_lt_pow hm.ne' (Nat.one_lt_pow hl.ne_zero (by omega))
  have hT : (∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ m - 1) = (q ^ l) ^ m - 1 := by
    have := geo_mul (q ^ m) l hqm.le
    simp only [← pow_mul] at this ⊢
    rw [this, Nat.mul_comm l m]
  have hd1 : (q ^ l) ^ m - 1 ∣ Q - 1 := by
    obtain ⟨e, rfl⟩ := hmf
    rw [hQ, pow_mul]
    exact sub_one_dvd _ e
  have hd2 : q ^ m - 1 ∣ Q - 1 := (Dvd.intro_left _ hT).trans hd1
  have hC := div_id (Q - 1) (q ^ m - 1) ((q ^ l) ^ m - 1) _ (by omega) hT hd1 (by omega)
  have hC2 : (Q - 1) / (q ^ m - 1) * (q ^ m - 1) = Q - 1 := Nat.div_mul_cancel hd2
  set C := (Q - 1) / (q ^ m - 1) with hCdef
  set T := ∑ i ∈ Finset.range l, q ^ (m * i) with hTdef
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j => ((1 : ℕ), ((k * q ^ j * C : ℕ) : ZMod (Q - 1))) with hGdef
  have hG : ∀ n, G (n + m) = G n := by
    intro n
    obtain ⟨u, hu⟩ : ∃ u, q ^ m = u + 1 := ⟨q ^ m - 1, by omega⟩
    have hCu : C * u = Q - 1 := by rw [hu] at hC2; simpa using hC2
    have : k * q ^ (n + m) * C = k * q ^ n * C + k * q ^ n * (Q - 1) := by
      rw [pow_add, hu, ← hCu]; ring
    simp only [hGdef, this]
    push_cast [ZMod.natCast_self]
    simp [ZMod.natCast_self]
  have hL : lbk Q (q ^ l) (m, k * T) = (Multiset.range m).map fun j => G (l * j) := by
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef]
    rw [← hC, pow_mul]
    congr 2
    ring
  rw [hL, perm_map l m ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd) hm G hG]
  rfl

private lemma lbkL (Q q l f : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1) → (∀ p ∈ liftAll q l L, p.1 ∣ f) →
      ((liftAll q l L).map (lbk Q (q ^ l))).sum = (L.map (lbk Q q)).sum := by
  intro L
  induction L with
  | nil => intro _ _; simp [liftAll]
  | cons p L ih =>
    intro h0 hd
    obtain ⟨m, k⟩ := p
    have hsplit : liftAll q l ((m, k) :: L) = (if l ∣ m then liftL q l [(m, k)] else
        [(m, k * ∑ i ∈ Finset.range l, q ^ (m * i))]) ++ liftAll q l L := by
      simp [liftAll]
    rw [hsplit] at hd ⊢
    have hdL : ∀ p ∈ liftAll q l L, p.1 ∣ f := fun p hp => hd p (List.mem_append_right _ hp)
    rw [List.map_append, List.sum_append, ih (fun p hp => h0 p (List.mem_cons_of_mem _ hp)) hdL,
      List.map_cons, List.sum_cons]
    congr 1
    by_cases hlm : l ∣ m
    · obtain ⟨m', rfl⟩ := hlm
      have : liftL q l [(l * m', k)] = (List.range l).map fun i => (m', k * q ^ i) := by
        simp [liftL, Nat.mul_div_cancel_left _ hl.pos]
      rw [if_pos (dvd_mul_right _ _), this, List.map_map]
      exact lbk_dvd Q q l m' k
    · rw [if_neg hlm] at hd ⊢
      have hmf : m ∣ f := hd (m, _) (List.mem_append_left _ (List.mem_singleton.2 rfl))
      simpa using lbk_ndvd Q q l f m k hq hl hQ (h0 (m, k) List.mem_cons_self) hmf hlm

private lemma splitsL (q l f : ℕ) (hl : l.Prime) (L : List (ℕ × ℕ))
    (hd : ∀ p ∈ liftAll q l L, p.1 ∣ f) : ∀ p ∈ L, p.1 ∣ l * f := by
  rintro ⟨m, k⟩ hp
  by_cases hlm : l ∣ m
  · have h1 : (m / l, k * q ^ 0) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp only [if_pos hlm, liftL]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.mem_map.2 ⟨0, List.mem_range.2 hl.pos, rfl⟩
    have h2 := hd _ h1
    obtain ⟨m', rfl⟩ := hlm
    rw [Nat.mul_div_cancel_left _ hl.pos] at h2
    exact Nat.mul_dvd_mul_left l h2
  · have h1 : (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp [if_neg hlm]
    exact (hd _ h1).mul_left l

theorem UpperTheory.Gal.InertialTypesAlt.liftBlocks :
    LiftBlocks := by
  intro a l Q hl ha hs
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq, hD, hL⟩ := ha
  obtain ⟨f, hf, hQ, hdiv⟩ := hs
  have hq' : 2 ≤ q := hq
  have hQ' : Q = (q ^ l) ^ f := hQ
  have hdiv' : ∀ p ∈ liftAll q l L, p.1 ∣ f := hdiv
  have hL0 : ∀ p ∈ L, 0 < p.1 := fun p hp => (hL p hp).1
  refine ⟨⟨l * f, Nat.mul_pos hl.pos hf, by rw [hQ', pow_mul], splitsL q l f hl L hdiv'⟩, ?_⟩
  have hS := geo_mul q l (by omega)
  have hql : 1 < q ^ l := Nat.one_lt_pow hl.ne_zero (by omega)
  have hDid : (∑ i ∈ Finset.range l, q ^ i) * ((Q - 1) / (q ^ l - 1)) = (Q - 1) / (q - 1) :=
    div_id (Q - 1) (q - 1) (q ^ l - 1) _ (by omega) hS (by rw [hQ']; exact sub_one_dvd _ f) (by omega)
  have hDpart : ((⟨q, D, L⟩ : Lbl).lift l).D.map (fun p =>
        (p.1, ((p.2 * ((Q - 1) / (((⟨q, D, L⟩ : Lbl).lift l).q - 1)) : ℕ) : ZMod (Q - 1)))) =
      D.map (fun p => (p.1, ((p.2 * ((Q - 1) / (q - 1)) : ℕ) : ZMod (Q - 1)))) := by
    show (D.map _).map _ = _
    rw [List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp]
    rw [← hDid, mul_assoc]
    rfl
  have hLpart := lbkL Q q l f hq' hl hQ' L hL0 hdiv'
  unfold Lbl.blocks
  rw [hDpart]
  congr 1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftOk
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Gal.InertialTypesAlt.coprime_pow_sub_one_self {q m : ℕ} (hm : 0 < m) (hq : 2 ≤ q) : Nat.Coprime (q ^ m - 1) q := by
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have e : q ^ m - 1 + 1 = q ^ m := by omega
  have a := Nat.gcd_dvd_left (q ^ m - 1) q
  have b := Nat.gcd_dvd_right (q ^ m - 1) q
  have c : Nat.gcd (q ^ m - 1) q ∣ q ^ m - 1 + 1 := by
    rw [e]
    exact b.trans (dvd_pow_self q hm.ne')
  exact Nat.dvd_one.1 ((Nat.dvd_add_right a).1 c)

private theorem UpperTheory.Gal.InertialTypesAlt.reg_dvd {q l m k : ℕ} (i : ℕ) (hq : 2 ≤ q) (hl : 0 < l) (hm : 0 < m) (hd : l ∣ m)
    (h : GlobalTheory.Shin.Reg q m k) : GlobalTheory.Shin.Reg (q ^ l) (m / l) (k * q ^ i) := by
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left c hl]
  intro j hj hjc hmod
  have hcop : Nat.gcd (q ^ (l * c) - 1) (q ^ i) = 1 :=
    Nat.Coprime.pow_right i (UpperTheory.Gal.InertialTypesAlt.coprime_pow_sub_one_self hm hq)
  refine h (l * j) (Nat.mul_pos hl hj) (Nat.mul_lt_mul_of_pos_left hjc hl) ?_
  rw [← pow_mul] at hmod
  apply Nat.ModEq.cancel_right_of_coprime hcop
  have e : k * q ^ (l * j) * q ^ i = k * q ^ i * (q ^ l) ^ j := by
    rw [← pow_mul]; ring
  rw [e]
  exact hmod

private theorem UpperTheory.Gal.InertialTypesAlt.reg_ndvd {q l m k : ℕ} (hq : 2 ≤ q) (hl : l.Prime) (hm : 0 < m) (hd : ¬ l ∣ m)
    (h : GlobalTheory.Shin.Reg q m k) : GlobalTheory.Shin.Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) := by
  intro j hj hjm hmod
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have hgt : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hx : q ^ m - 1 + 1 = q ^ m := by omega
  have hgeo := geom_sum_mul_add (q ^ m - 1) l
  rw [hx] at hgeo
  have hS : (∑ i ∈ Finset.range l, q ^ (m * i)) = ∑ i ∈ Finset.range l, (q ^ m) ^ i :=
    Finset.sum_congr rfl fun i _ => pow_mul q m i
  rw [← hS] at hgeo
  set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef
  have hbig : 1 < (q ^ m) ^ l := Nat.one_lt_pow hl.ne_zero hgt
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0] at hgeo
    omega
  have hmodulus : (q ^ l) ^ m - 1 = (q ^ m - 1) * S := by
    have : (q ^ l) ^ m = (q ^ m) ^ l := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [this, ← hgeo, Nat.mul_comm]
    simp
  rw [hmodulus] at hmod
  have e1 : k * (q ^ l) ^ j ≡ k [MOD q ^ m - 1] := by
    apply Nat.ModEq.mul_right_cancel' hS0
    have e : k * (q ^ l) ^ j * S = k * S * (q ^ l) ^ j := by ring
    rw [e]
    exact hmod
  have hone : q ^ m ≡ 1 [MOD q ^ m - 1] := by
    have : (q ^ m - 1) + 1 ≡ 0 + 1 [MOD q ^ m - 1] :=
      Nat.ModEq.add_right 1 (by simp [Nat.ModEq])
    rwa [hx] at this
  have hcop : Nat.Coprime m l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
  have hr0 : (l * j) % m ≠ 0 := by
    intro h0
    have h1 : m ∣ l * j := Nat.dvd_of_mod_eq_zero h0
    have h2 : m ∣ j := hcop.dvd_of_dvd_mul_left h1
    have := Nat.le_of_dvd hj h2
    omega
  have hrm : (l * j) % m < m := Nat.mod_lt _ hm
  have hpow : q ^ (l * j) ≡ q ^ ((l * j) % m) [MOD q ^ m - 1] := by
    have hsplit : q ^ (l * j) = (q ^ m) ^ ((l * j) / m) * q ^ ((l * j) % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hsplit]
    have := (hone.pow ((l * j) / m)).mul_right (q ^ ((l * j) % m))
    simpa using this
  refine h _ (Nat.pos_of_ne_zero hr0) hrm ?_
  have e2 : k * q ^ ((l * j) % m) ≡ k * q ^ (l * j) [MOD q ^ m - 1] := (hpow.mul_left k).symm
  refine e2.trans ?_
  rw [pow_mul]
  exact e1

private theorem UpperTheory.Gal.InertialTypesAlt.deg_append (A B : List (ℕ × ℕ)) :
    GlobalTheory.Shin.deg (A ++ B) = GlobalTheory.Shin.deg A + GlobalTheory.Shin.deg B := by
  simp [GlobalTheory.Shin.deg]

private theorem UpperTheory.Gal.InertialTypesAlt.block_dvd (q l : ℕ) (p : ℕ × ℕ) (hd : l ∣ p.1) :
    GlobalTheory.Shin.deg (GlobalTheory.Shin.liftL q l [p]) = p.1 := by
  have h : ((List.range l).map fun i => (p.1 / l, p.2 * q ^ i)).map Prod.fst = List.replicate l (p.1 / l) := by
    rw [List.map_map]
    apply List.eq_replicate_iff.2
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    rfl
  have h2 : GlobalTheory.Shin.deg (GlobalTheory.Shin.liftL q l [p]) = (List.replicate l (p.1 / l)).sum := by
    rw [← h]
    simp [GlobalTheory.Shin.deg, GlobalTheory.Shin.liftL]
  rw [h2, List.sum_replicate, smul_eq_mul]
  exact Nat.mul_div_cancel' hd

private theorem UpperTheory.Gal.InertialTypesAlt.liftAll_spec (q l : ℕ) (L : List (ℕ × ℕ)) (hq : 2 ≤ q) (hl : l.Prime)
    (h : ∀ p ∈ L, 0 < p.1 ∧ GlobalTheory.Shin.Reg q p.1 p.2) :
    GlobalTheory.Shin.deg (GlobalTheory.Shin.liftAll q l L) = GlobalTheory.Shin.deg L ∧
      ∀ p ∈ GlobalTheory.Shin.liftAll q l L, 0 < p.1 ∧ GlobalTheory.Shin.Reg (q ^ l) p.1 p.2 := by
  induction L with
  | nil => simp [GlobalTheory.Shin.liftAll, GlobalTheory.Shin.deg]
  | cons p L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hp0, hpR⟩ := h p List.mem_cons_self
    have hsplit : GlobalTheory.Shin.liftAll q l (p :: L) =
        (if l ∣ p.1 then GlobalTheory.Shin.liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++
          GlobalTheory.Shin.liftAll q l L := by
      simp only [GlobalTheory.Shin.liftAll, List.flatMap_cons]
    have hdegp : GlobalTheory.Shin.deg (p :: L) = p.1 + GlobalTheory.Shin.deg L := by simp [GlobalTheory.Shin.deg]
    rw [hsplit, UpperTheory.Gal.InertialTypesAlt.deg_append, ih1, hdegp]
    by_cases hd : l ∣ p.1
    · rw [if_pos hd]
      refine ⟨by rw [UpperTheory.Gal.InertialTypesAlt.block_dvd q l p hd], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · simp only [GlobalTheory.Shin.liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        exact ⟨Nat.div_pos (Nat.le_of_dvd hp0 hd) hl.pos, UpperTheory.Gal.InertialTypesAlt.reg_dvd i hq hl.pos hp0 hd hpR⟩
      · exact ih2 x hx
    · rw [if_neg hd]
      refine ⟨by simp [GlobalTheory.Shin.deg], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hp0, UpperTheory.Gal.InertialTypesAlt.reg_ndvd hq hl hp0 hd hpR⟩
      · exact ih2 x hx

theorem UpperTheory.Gal.InertialTypesAlt.liftOk :
    LiftOk := by
  intro a l hl hok
  obtain ⟨hq, hD, hL⟩ := hok
  obtain ⟨h1, h2⟩ := UpperTheory.Gal.InertialTypesAlt.liftAll_spec a.q l a.L hq hl hL
  have hD' : GlobalTheory.Shin.deg (a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i)) = GlobalTheory.Shin.deg a.D := by
    simp [GlobalTheory.Shin.deg, List.map_map, Function.comp_def]
  refine ⟨⟨?_, ?_, h2⟩, ?_⟩
  · show 2 ≤ a.q ^ l
    calc 2 ≤ a.q := hq
      _ ≤ a.q ^ l := Nat.le_self_pow hl.ne_zero a.q
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
    exact hD r hr
  · show GlobalTheory.Shin.deg (a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i)) + GlobalTheory.Shin.deg (GlobalTheory.Shin.liftAll a.q l a.L) =
      GlobalTheory.Shin.deg a.D + GlobalTheory.Shin.deg a.L
    rw [hD', h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PMeetsIff
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sum_ne_iff {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (κ : Representation ℂ H W) :
    (∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0) ↔
      ∃ f : W →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (κ g x) = ρ g (f x) := by
  classical
  haveI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank κ ρ
  have hsum : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g * κ.character g⁻¹ :=
    Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hc : (Nat.card H : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hsum]
  constructor
  · intro h
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at key
      exact h ((mul_eq_zero.mp key).resolve_left hc)
    haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hpos)
    obtain ⟨φ, hφ⟩ := exists_ne (0 : Representation.IntertwiningMap κ ρ)
    refine ⟨φ.toLinearMap, ?_, fun g x => Representation.IntertwiningMap.isIntertwining κ ρ φ g x⟩
    intro h0
    exact hφ (Representation.IntertwiningMap.ext (by simpa using h0))
  · rintro ⟨f, hf0, hf⟩
    let φ := f.intertwiningMap_of_isIntertwiningMap κ ρ hf
    have hφ : φ ≠ 0 := by
      intro h0
      apply hf0
      ext x
      have := congrArg (fun ψ : Representation.IntertwiningMap κ ρ => ψ x) h0
      simpa [φ] using this
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      rw [← (Representation.invariantsEquivIntertwiningMap κ ρ).finrank_eq]
      apply Nat.pos_iff_ne_zero.mp
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨(Representation.invariantsEquivIntertwiningMap κ ρ).symm φ, ?_⟩
      simpa using hφ
    intro hs
    rw [hs, mul_zero] at key
    exact hpos (by exact_mod_cast key.symm)

theorem UpperTheory.Gal.InertialTypesAlt.meetsIff :
    MeetsIff := by
  intro H V W _ _ _ _ _ _ _ _ ρ κ
  classical
  haveI := Fintype.ofFinite H
  have hstar : ∀ g : H, star (LinearMap.trace ℂ W (κ g)) = κ.character g⁻¹ := by
    intro g
    have hmem : (fun g => algebraMap ℂ ℂ (κ.character g)) ∈ GlobalTheory.BI.Virt ℂ ℂ H :=
      AddSubgroup.subset_closure (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ H W κ).1
    have := _root_.GlobalTheory.CuspGL.star_virt_eq_inv H _ hmem g
    change star (κ.character g) = _
    simpa using this
  have hM : Meets ρ (fun g => LinearMap.trace ℂ W (κ g)) ↔
      ∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0 := by
    unfold Meets
    rw [finsum_eq_sum_of_fintype]
    simp only [hstar]
    rfl
  have hswap : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g⁻¹ * κ.character g :=
    Fintype.sum_equiv (Equiv.inv H) _ _ fun g => by simp [mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hM, hswap]
    exact sum_ne_iff κ ρ
  · rw [hM]
    exact sum_ne_iff ρ κ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPolBot
section
noncomputable section

open Polynomial

namespace UpperTheory.Gal.InertialTypesAlt

private theorem polBot_block (Q : ℕ) (x : ℂ) (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (c : ℕ → ℕ) (m : ℕ) :
    (((Multiset.range m).map fun j => ((1 : ℕ), ((c j : ℕ) : ZMod (Q - 1)))).map
      fun b => (X - C (x ^ b.2.val)) ^ b.1).prod = ∏ j ∈ Finset.range m, (X - C (x ^ c j)) := by
  haveI : NeZero (Q - 1) := ⟨by omega⟩
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod, Finset.range_val]
  congr 1
  apply Multiset.map_congr rfl
  intro j _
  simp only [Function.comp, pow_one, ZMod.val_natCast]
  rw [← pow_eq_pow_mod _ hx]

private theorem polBot_list (q Q : ℕ) (x : ℂ) (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (L : List (ℕ × ℕ)) :
    (((L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))).sum).map
        fun b => (X - C (x ^ b.2.val)) ^ b.1).prod =
      (L.map fun p => ∏ j ∈ Finset.range p.1, (X - C (x ^ (p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)))))).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, Multiset.map_add (f := _), Multiset.prod_add, ih, List.map_cons, List.prod_cons,
      polBot_block Q x hQ hx (fun j => p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1))) p.1]

theorem polBot : PolBot := by
  intro q Q L x hQ hx
  have h := polBot_list q Q x hQ hx L
  simpa [Lbl.pol, Lbl.blocks] using h

end UpperTheory.Gal.InertialTypesAlt
end
end

