module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.IdealForm
section
open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem ideal_form (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : ℕ) (I : E → Prop) (hI1 : I 1)
    (hIm : ∀ t x, IntAt P t → I x → I (t * x)) (hIb : ∀ x, I x → IntAt P (qE P ^ j * x)) :
    ∃ K, K ≤ j ∧ I (qE P ^ K)⁻¹ ∧ ∀ x, I x → IntAt P (qE P ^ K * x) := by
  classical
  have hq0 := qE_ne_zero P hp
  refine ⟨Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j, Nat.findGreatest_le j,
    Nat.findGreatest_spec (P := fun k => I (qE P ^ k)⁻¹) (Nat.zero_le j) (by simpa using hI1), ?_⟩
  intro x hx
  by_contra hxK
  have hx0 : x ≠ 0 := by rintro rfl; exact hxK (by simpa using intAt_zero P)
  have hex : ∃ k, IntAt P (qE P ^ k * x) := ⟨j, hIb x hx⟩
  have hk0 : IntAt P (qE P ^ Nat.find hex * x) := Nat.find_spec hex
  have hk0j : Nat.find hex ≤ j := Nat.find_min' hex (hIb x hx)
  have hKk0 : Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j < Nat.find hex := by
    by_contra hle; rw [not_lt] at hle
    apply hxK
    have : qE P ^ Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j * x =
        qE P ^ (Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j - Nat.find hex) * (qE P ^ Nat.find hex * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]; exact intAt_mul P (intAt_pow P (intAt_natCast P _) _) hk0
  obtain ⟨k1, hk1⟩ : ∃ k1, Nat.find hex = k1 + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnot : ¬ IntAt P (qE P ^ Nat.find hex * x / qE P) := by
    have : qE P ^ Nat.find hex * x / qE P = qE P ^ k1 * x := by rw [hk1, pow_succ]; field_simp
    rw [this]; exact Nat.find_min hex (by omega)
  have hu := unit_of_not_div P hp hq hk0 hnot
  have hI := hIm _ _ hu hx
  have e : (qE P ^ Nat.find hex * x)⁻¹ * x = (qE P ^ Nat.find hex)⁻¹ := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  rw [e] at hI
  exact Nat.findGreatest_is_greatest hKk0 hk0j hI

section M

variable {n : ℕ} (Mm : (Fin n → E) → Prop) (Madd : ∀ u v, Mm u → Mm v → Mm (u + v))
  (Msmul : ∀ t v, IntAt P t → Mm v → Mm (t • v)) (Mlam : ∀ v, (∀ l, IntAt P (v l)) → Mm v)

include Madd Msmul Mlam in
theorem comb_mem (b : Fin n → Fin n → E) (hbM : ∀ l, Mm (b l)) (w : Fin n → E) (hw : ∀ l, IntAt P (w l)) :
    Mm (∑ l, w l • b l) := by
  classical
  have h0 : Mm 0 := Mlam 0 (fun l => by
    first
    | exact ⟨0, 1, (fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)), by simp⟩
    | (unfold IntAt; done))
  exact Finset.sum_induction _ Mm (fun a b ha hb => Madd a b ha hb) h0
    (fun l _ => Msmul _ _ (hw l) (hbM l))

include Madd Msmul Mlam in

include Madd Msmul Mlam in
theorem herm (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : ℕ)
    (Mbd : ∀ v, Mm v → ∀ l, IntAt P (qE P ^ j * v l)) :
    ∃ (K : Fin n → ℕ) (b : Fin n → Fin n → E), (∀ l, K l ≤ j) ∧ (∀ l, Mm (b l)) ∧
      (∀ l, b l l = (qE P ^ K l)⁻¹) ∧ UT b ∧
      ∀ v, Mm v → ∃ w : Fin n → E, (∀ l, IntAt P (w l)) ∧ v = ∑ l, w l • b l := by
  classical
  have hIl : ∀ l : Fin n, ∃ K, K ≤ j ∧ (∃ v, Mm v ∧ v l = (qE P ^ K)⁻¹ ∧ ∀ k, l < k → v k = 0) ∧
      ∀ x, (∃ v, Mm v ∧ v l = x ∧ ∀ k, l < k → v k = 0) → IntAt P (qE P ^ K * x) := by
    intro l
    apply ideal_form P hp hq j (fun x => ∃ v, Mm v ∧ v l = x ∧ ∀ k, l < k → v k = 0)
    · refine ⟨Pi.single l 1, Mlam _ fun k => ?_, by simp, fun k hk => by simp [Pi.single_apply, hk.ne']⟩
      by_cases hk : k = l
      · rw [hk]; simpa using intAt_one P
      · simpa [Pi.single_apply, hk] using intAt_zero P
    · rintro t x ht ⟨v, hv, rfl, hz⟩
      exact ⟨t • v, Msmul t v ht hv, by simp, fun k hk => by simp [hz k hk]⟩
    · rintro x ⟨v, hv, rfl, -⟩; exact Mbd v hv l
  choose K hKj hKb hKall using hIl
  choose b hbM hbl hbz using hKb
  refine ⟨K, b, hKj, hbM, hbl, fun l k hlk => hbz l k hlk, ?_⟩
  have hq0 := qE_ne_zero P hp
  have main : ∀ k, k ≤ n → ∀ v, Mm v → Zab k v →
      ∃ w : Fin n → E, (∀ l, IntAt P (w l)) ∧ v = ∑ l, w l • b l := by
    intro k
    induction k with
    | zero =>
      intro _ v _ hz
      refine ⟨0, fun _ => intAt_zero P, ?_⟩
      funext l; simp [hz l (Nat.zero_le _)]
    | succ k ih =>
      intro hk v hv hz
      have ht : IntAt P (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩) :=
        hKall ⟨k, by omega⟩ _ ⟨v, hv, rfl, fun k' hk' => hz k' (by rw [Fin.lt_def] at hk'; simp at hk'; omega)⟩
      have hv' := Madd _ _ hv (Msmul _ _ (intAt_neg P ht) (hbM ⟨k, by omega⟩))
      have hz' : Zab k (v + (-(qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)) • b ⟨k, by omega⟩) := by
        intro l hl
        rcases Nat.lt_or_eq_of_le hl with hlt | heq
        · rw [Pi.add_apply, hz l hlt, Pi.smul_apply, hbz _ l (by rw [Fin.lt_def]; simpa using hlt)]; simp
        · have : l = ⟨k, by omega⟩ := Fin.ext heq.symm
          rw [this, Pi.add_apply, Pi.smul_apply, hbl, smul_eq_mul]
          field_simp; ring
      obtain ⟨w', hw', e'⟩ := ih (by omega) _ hv' hz'
      refine ⟨w' + Pi.single ⟨k, by omega⟩ (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩), fun l => ?_, ?_⟩
      · rw [Pi.add_apply]
        refine intAt_add P (hw' l) ?_
        by_cases hl : l = ⟨k, by omega⟩
        · rw [hl]; simpa using ht
        · simpa [Pi.single_apply, hl] using intAt_zero P
      · have : v = (v + (-(qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)) • b ⟨k, by omega⟩) +
            (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩) • b ⟨k, by omega⟩ := by rw [neg_smul]; abel
        conv_lhs => rw [this]
        rw [e']
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single ⟨k, by omega⟩]
        · simp
        · intro i _ hi; simp [Pi.single_apply, hi]
        · simp
  exact fun v hv => main n le_rfl v hv (fun l hl => absurd l.2 (by omega))

end M

end PI.TwNormLat.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.PrXLeOfNf
section
open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

def Crit (N c : ℕ) (n : ℕ → ℤ) (z : Sp E N) (v : Sp E (N + c)) : Prop :=
  (∀ l : Fin N, IntAt P (v (Fin.castAdd _ l) - Loc.atN v N * z l)) ∧
    ∀ i : Fin c, IntAt P ((((Ideal.absNorm P.asIdeal : ℕ) : E) ^ n i.1)⁻¹ * v (Fin.natAdd _ i))

theorem fin_split {N c : ℕ} (l : Fin (N + c)) :
    (∃ l' : Fin N, l = Fin.castAdd c l') ∨ ∃ i : Fin c, l = Fin.natAdd N i := by
  by_cases h : l.1 < N
  · exact Or.inl ⟨⟨l.1, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨l.1 - N, by omega⟩, Fin.ext (by simp; omega)⟩

theorem intAt_zpow (m : ℤ) (hm : 0 ≤ m) : IntAt P (qE P ^ m) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]; exact intAt_pow P (intAt_natCast P _) _

theorem intAt_scale (hp : (Ideal.absNorm P.asIdeal).Prime) {j : ℕ} {m : ℤ} (hm : -(j : ℤ) ≤ m) {a : E}
    (ha : IntAt P ((qE P ^ m)⁻¹ * a)) : IntAt P (qE P ^ j * a) := by
  have hq0 := qE_ne_zero P hp
  have h1 : qE P ^ m ≠ 0 := zpow_ne_zero m hq0
  have : qE P ^ j * a = qE P ^ ((j : ℤ) + m) * ((qE P ^ m)⁻¹ * a) := by
    rw [zpow_add₀ hq0, zpow_natCast, mul_assoc (qE P ^ j), ← mul_assoc (qE P ^ m), mul_inv_cancel₀ h1, one_mul]
  rw [this]; exact intAt_mul P (intAt_zpow P _ (by omega)) ha

theorem bdd_of_nf (hp : (Ideal.absNorm P.asIdeal).Prime) {N c j : ℕ} (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c))
    (n : ℕ → ℤ) (z : Sp E N) (hn : ∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0) (hz : z ∈ stdAt E N P)
    (hc : ∀ v, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ Crit P N c n z v) : Bdd P N c j h := by
  rw [mem_stdAt] at hz
  intro x hx
  rw [mem_lam] at hx
  constructor
  · rw [hc]
    refine ⟨fun l => intAt_sub P (hx _) (intAt_mul P ?_ (hz l)), fun i => intAt_mul P ?_ (hx _)⟩
    · unfold Loc.atN; split_ifs
      · exact hx _
      · exact intAt_zero P
    · rw [← zpow_neg]; exact intAt_zpow P _ (by have := (hn i.1).2; omega)
  · have hv : Crit P N c n z (h x) := by
      rw [← hc]; rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, mem_lam]; exact hx
    have hN : IntAt P (qE P ^ j * Loc.atN (h x) N) := by
      unfold Loc.atN; split_ifs with hN
      · have := hv.2 ⟨0, by omega⟩
        exact intAt_scale P hp (hn 0).1 this
      · simpa using intAt_zero P
    rw [mem_lam]
    intro l
    rw [Pi.smul_apply, smul_eq_mul]
    rcases fin_split l with ⟨l', rfl⟩ | ⟨i, rfl⟩
    · have e : qE P ^ j * h x (Fin.castAdd c l') = qE P ^ j * (h x (Fin.castAdd c l') - Loc.atN (h x) N * z l') +
          qE P ^ j * Loc.atN (h x) N * z l' := by ring
      rw [e]
      exact intAt_add P (intAt_mul P (intAt_pow P (intAt_natCast P _) _) (hv.1 l')) (intAt_mul P hN (hz l'))
    · exact intAt_scale P hp (hn i.1).1 (hv.2 i)

theorem prX_le_of_nf {N c : ℕ} (kj : ℕ) (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) (n : ℕ → ℤ) (z : Sp E N)
    (hc : ∀ v, h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ Crit P N c n z v) :
    Loc.prX (Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h) ≤ GLint E N P := by
  rintro g ⟨r, hr, hg⟩
  have hJ := (Subgroup.mem_comap.1 hr.2).1
  have lamEq : ∀ w, w ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ w ∈ stdAt E (N + c) P := by
    intro w; rw [mem_lam, mem_stdAt]
  have hstab : ∀ v, h⁻¹ (r v) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔
      h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 := by
    intro v
    have := hJ (h⁻¹ v)
    rw [lamEq, lamEq, ← this]
    simp [MulAut.conj_apply, LinearEquiv.mul_apply]
  have hX : ∀ x : Sp E N, h⁻¹ (Loc.inX E N c x) ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ x ∈ stdAt E N P := by
    intro x
    rw [hc, mem_stdAt]
    have h1 : ∀ l : Fin N, Loc.inX E N c x (Fin.castAdd c l) = x l := fun l => by simp [Loc.inX]
    have h2 : ∀ i : Fin c, Loc.inX E N c x (Fin.natAdd N i) = 0 := fun i => by simp [Loc.inX]
    have h3 : Loc.atN (Loc.inX E N c x) N = 0 := by simp [Loc.atN, Loc.inX]
    simp only [Crit, h1, h2, h3, zero_mul, sub_zero, mul_zero]
    exact ⟨fun H => H.1, fun H => ⟨H, fun _ => intAt_zero P⟩⟩
  show ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P
  intro x
  rw [← hX, ← hX, ← hg x, hstab]

end PI.TwNormLat.W
end
end

