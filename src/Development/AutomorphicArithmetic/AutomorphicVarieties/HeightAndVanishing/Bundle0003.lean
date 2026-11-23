module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem orderOf_pow_coprime_parts {Γ : Type} [Group Γ] (x : Γ) (P C e : ℕ) (hn : orderOf x = P * C)
    (hP : 0 < P) (hC : 0 < C) (hco : P.Coprime C) (h1 : C ∣ e) (h2 : e ≡ 1 [MOD P]) :
    orderOf (x ^ e) = P ∧ orderOf (x * (x ^ e)⁻¹) = C := by
  have hcx : Commute (x ^ e) x := (Commute.refl x).pow_left e
  have hcomm : Commute (x ^ e) (x * (x ^ e)⁻¹) := hcx.mul_right (Commute.refl _).inv_right
  have hyz : x ^ e * (x * (x ^ e)⁻¹) = x := by
    rw [← mul_assoc, hcx.eq, mul_inv_cancel_right]
  have hoy : orderOf (x ^ e) ∣ P := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, orderOf_dvd_iff_pow_eq_one.mp]
    rw [hn, mul_comm P C]
    exact Nat.mul_dvd_mul_right h1 P
  have hoz : orderOf (x * (x ^ e)⁻¹) ∣ C := by
    apply orderOf_dvd_of_pow_eq_one
    rw [(hcx.symm.inv_right).mul_pow, inv_pow, ← pow_mul]
    have : x ^ (e * C) = x ^ C := by
      rw [pow_eq_pow_iff_modEq, hn]
      have := Nat.ModEq.mul_right' C h2
      simpa using this
    rw [this, mul_inv_cancel]
  have hco' : (orderOf (x ^ e)).Coprime (orderOf (x * (x ^ e)⁻¹)) := Nat.Coprime.of_dvd hoy hoz hco
  have hprod : orderOf (x ^ e) * orderOf (x * (x ^ e)⁻¹) = P * C := by
    rw [← hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco', hyz, hn]
  obtain ⟨a, ha⟩ := hoy
  obtain ⟨b, hb⟩ := hoz
  have hab : a * b = 1 := by
    have : P * C * (a * b) = P * C * 1 := by
      calc P * C * (a * b)
          = (orderOf (x ^ e) * orderOf (x * (x ^ e)⁻¹)) * (a * b) := by rw [hprod]
        _ = (orderOf (x ^ e) * a) * (orderOf (x * (x ^ e)⁻¹) * b) := by ring
        _ = P * C * 1 := by rw [← ha, ← hb, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hP hC) this
  have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_right hab
  have hb1 : b = 1 := Nat.eq_one_of_mul_eq_one_left hab
  refine ⟨?_, ?_⟩
  · rw [ha, ha1, mul_one]
  · rw [hb, hb1, mul_one]

theorem UpperTheory.V.HV.partOrd :
    ∀ (Γ : Type) [Group Γ] (l : ℕ), l.Prime → ∀ x : Γ, 0 < orderOf x →
      orderOf (lPart l x) = ordProj[l] (orderOf x) ∧ orderOf (lPrime l x) = ordCompl[l] (orderOf x) ∧ ¬ l ∣ orderOf (lPrime l x) ∧
      lPart l x ∈ Subgroup.zpowers x ∧ lPrime l x ∈ Subgroup.zpowers x ∧ (¬ l ∣ orderOf x → lPart l x = 1 ∧ lPrime l x = x) ∧
      ∀ a b : Γ, Commute a b → a * b = x → ¬ l ∣ orderOf a → (∃ s, b ^ l ^ s = 1) → lPrime l x = a ∧ lPart l x = b := by
  intro Γ _ l hl x hx
  have hn0 : orderOf x ≠ 0 := hx.ne'
  obtain ⟨P, hPd⟩ : ∃ P, P = ordProj[l] (orderOf x) := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = ordCompl[l] (orderOf x) := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e, e = C ^ Nat.totient P := ⟨_, rfl⟩
  have hPC : P * C = orderOf x := by rw [hPd, hCd]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hP : 0 < P := by rw [hPd]; exact pow_pos hl.pos _
  have hC : 0 < C := by rw [hCd]; exact Nat.ordCompl_pos l hn0
  have hlC : ¬ l ∣ C := by rw [hCd]; exact Nat.not_dvd_ordCompl hl hn0
  have hcoC : l.Coprime C := (Nat.Prime.coprime_iff_not_dvd hl).2 hlC
  have hco : P.Coprime C := by rw [hPd]; exact hcoC.pow_left _
  have hlp : lPart l x = x ^ e := by rw [hed, hPd, hCd]; rfl
  have hlpr : lPrime l x = x * (lPart l x)⁻¹ := rfl
  have h1 : C ∣ e := by rw [hed]; exact dvd_pow_self _ (Nat.totient_pos.2 hP).ne'
  have h2 : e ≡ 1 [MOD P] := by rw [hed]; exact Nat.ModEq.pow_totient hco.symm
  obtain ⟨hA, hB⟩ := orderOf_pow_coprime_parts x P C e hPC.symm hP hC hco h1 h2
  rw [← hlp] at hA hB
  rw [← hlpr] at hB
  rw [← hCd, ← hPd]
  refine ⟨hA, hB, hB ▸ hlC, ?_, ?_, ?_, ?_⟩
  · rw [hlp]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  · rw [hlpr, hlp]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
  · intro hnd
    have hf : (orderOf x).factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    have ho : orderOf (lPart l x) = 1 := by rw [hA, hPd, hf, pow_zero]
    have h1' := orderOf_eq_one_iff.mp ho
    exact ⟨h1', by rw [hlpr, h1', inv_one, mul_one]⟩
  · rintro a b hab habx hna ⟨s, hs⟩
    have hcoa : (orderOf a).Coprime l := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hna)
    have hob : orderOf b ∣ l ^ s := orderOf_dvd_of_pow_eq_one hs
    have hab' : (orderOf a).Coprime (orderOf b) := Nat.Coprime.coprime_dvd_right hob (hcoa.pow_right s)
    have hx' : orderOf x = orderOf a * orderOf b := by
      rw [← habx]; exact hab.orderOf_mul_eq_mul_orderOf_of_coprime hab'
    have hoaC : orderOf a ∣ C := by
      have hd : orderOf a ∣ P * C := by rw [hPC, hx']; exact dvd_mul_right _ _
      have hcP : (orderOf a).Coprime P := by rw [hPd]; exact hcoa.pow_right _
      exact hcP.dvd_of_dvd_mul_left hd
    have hobP : orderOf b ∣ P := by
      have hd : orderOf b ∣ P * C := by rw [hPC, hx']; exact dvd_mul_left _ _
      have hcC : (orderOf b).Coprime C := Nat.Coprime.coprime_dvd_left hob (hcoC.pow_left s)
      exact hcC.dvd_of_dvd_mul_right hd
    have hae : a ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp (hoaC.trans h1)
    have hbe : b ^ e = b := by
      have := (pow_eq_pow_iff_modEq (x := b) (n := e) (m := 1)).2 (h2.of_dvd hobP)
      simpa using this
    have hpart : lPart l x = b := by
      calc lPart l x = x ^ e := hlp
        _ = (a * b) ^ e := by rw [habx]
        _ = b := by rw [hab.mul_pow, hae, hbe, one_mul]
    refine ⟨?_, hpart⟩
    rw [hlpr, hpart, ← habx, mul_inv_cancel_right]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PointArith
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem point_arith (x B : ℝ) (hx : 2 ≤ x) (hB : 0 ≤ B) (k K D C0 : ℕ) (hk : k ≤ K) :
    (k : ℝ) * (x ^ D + D * B) + x ^ C0 ≤ x ^ (C0 + D + K + K * D) + ((C0 + D + K + K * D : ℕ) : ℝ) * B := by
  have hx1 : (1:ℝ) ≤ x := by linarith
  have h1 := one_add_mul_le_pow (show (-2:ℝ) ≤ x - 1 by linarith) K
  rw [show (1:ℝ) + (x - 1) = x by ring] at h1
  have hKr : (k:ℝ) ≤ K := by exact_mod_cast hk
  have hK0 : (0:ℝ) ≤ K := by positivity
  have hD0 : (0:ℝ) ≤ D := by positivity
  have hC0 : (0:ℝ) ≤ C0 := by positivity
  have hc : (K:ℝ) + 1 ≤ x ^ K := by nlinarith
  have ha : 1 ≤ x ^ C0 := one_le_pow₀ hx1
  have hb : 1 ≤ x ^ D := one_le_pow₀ hx1
  have he : 1 ≤ x ^ (K * D) := one_le_pow₀ hx1
  have hpow : x ^ (C0 + D + K + K * D) = x ^ C0 * x ^ D * x ^ K * x ^ (K * D) := by
    rw [pow_add, pow_add, pow_add]
  have hM : (k:ℝ) * D ≤ ((C0 + D + K + K * D : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hMB : (k:ℝ) * D * B ≤ ((C0 + D + K + K * D : ℕ) : ℝ) * B :=
    mul_le_mul_of_nonneg_right hM hB
  have hab : x ^ C0 ≤ x ^ C0 * x ^ D := le_mul_of_one_le_right (by positivity) hb
  have habc : x ^ C0 * x ^ D * ((K:ℝ) + 1) ≤ x ^ C0 * x ^ D * x ^ K :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have hq : x ^ C0 * x ^ D * x ^ K ≤ x ^ C0 * x ^ D * x ^ K * x ^ (K * D) :=
    le_mul_of_one_le_right (by positivity) he
  have hkb : (k:ℝ) * x ^ D ≤ K * x ^ D := mul_le_mul_of_nonneg_right hKr (by positivity)
  have hKb : (K:ℝ) * x ^ D ≤ K * (x ^ C0 * x ^ D) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) ha) hK0
  rw [hpow]
  nlinarith

theorem UpperTheory.V.HV.point :
    SumIn → SumOut → PointHV := by
  intro hin hout χ j
  classical
  obtain ⟨C0, r₁, r₂, hr₁, hr₂, hO⟩ := hout χ
  obtain ⟨Cl, hCl⟩ : ∃ Cl : ℕ → ℕ, ∀ (l : Nat.Primes) (hl : (l:ℕ) ∈ Bchi χ),
      Cl l = Classical.choose (hin χ l (j l) hl) :=
    ⟨fun n => if hn : n.Prime ∧ n ∈ Bchi χ then Classical.choose (hin χ ⟨n, hn.1⟩ (j n) hn.2) else 0,
      fun l hl => dif_pos (show (l:ℕ).Prime ∧ (l:ℕ) ∈ Bchi χ from ⟨l.2, hl⟩)⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ l ∈ Bchi χ, Cl l ≤ D :=
    ⟨∑ l ∈ Bchi χ, Cl l, fun l hl => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hl⟩
  refine ⟨C0 + D + (Bchi χ).card + (Bchi χ).card * D, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ h1 h2 h3 h4 t ht hbig B hB hlay E _ _ _ hE Ω _ _ _ ld
  have hIn : ∀ l : Nat.Primes, (l:ℕ) ∈ Bchi χ →
      PlusLe ld {l} t (((h.N:ℝ) * t) ^ (Cl l) + (Cl l : ℝ) * B) := by
    intro l hl
    rw [hCl l hl]
    exact Classical.choose_spec (hin χ l (j l) hl) h hχ t ht hbig B hB (hlay l hl) E hE Ω ld
  have hOut : ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l:ℕ) ≠ 2 ∧ (l:ℕ) ∉ Bchi χ) →
      PlusLe ld S t (((h.N:ℝ) * t) ^ C0) :=
    fun S hS => hO h hχ h1 h2 h3 h4 t ht hbig E hE Ω ld S hS
  have hx2 : (2:ℝ) ≤ (h.N:ℝ) * t := by
    have hN : (1:ℝ) ≤ h.N := by exact_mod_cast h.N_pos
    have ht' : (2:ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  refine ⟨?_, ?_⟩
  · intro p hpf e hp2 he1 he2
    by_cases hb : p ∈ Bchi χ
    · exact (hIn ⟨p, hpf.out⟩ hb).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
    · refine (hOut {⟨p, hpf.out⟩} ?_).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
      intro l hl
      obtain rfl := Finset.mem_singleton.mp hl
      exact ⟨hp2, hb⟩
  · intro S hS2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)]
    have hout2 := (hOut (S.filter (fun l : Nat.Primes => (l:ℕ) ∉ Bchi χ)) (by
      intro l hl
      rw [Finset.mem_filter] at hl
      exact ⟨hS2 l hl.1, hl.2⟩)).2
    have hin2 : ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ),
        Real.log ((l:ℕ):ℝ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ)
        ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ), (((h.N:ℝ) * t) ^ D + (D:ℝ) * B) := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_filter] at hl
      have h0 := (hIn l hl.2).2
      rw [Finset.sum_singleton] at h0
      have hle := hD l hl.2
      have hp1 : ((h.N:ℝ) * t) ^ (Cl l) ≤ ((h.N:ℝ) * t) ^ D := pow_le_pow_right₀ (by linarith) hle
      have hp2 : (Cl l : ℝ) * B ≤ (D:ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hB
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at hin2
    have hcard : (S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)).card ≤ (Bchi χ).card :=
      Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l:ℕ))
        (fun l hl => (Finset.mem_filter.mp hl).2) Subtype.coe_injective.injOn
    have key := point_arith ((h.N:ℝ) * t) B hx2 hB _ (Bchi χ).card D C0 hcard
    linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem projA {N : ℕ} (r d : ℕ) (h : d ∣ N) (hd : d ∣ ordProj[r] N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h (proj r N u) = ZMod.unitsMap h u := by
  have h1 : ZMod.castHom h (ZMod d) (idem r N) = 1 := by
    unfold idem
    rw [map_natCast, ← Nat.cast_one (R := ZMod d), ZMod.natCast_eq_natCast_iff]
    exact (Nat.ModEq.pow_totient (coprime_ordProj_ordCompl r N).symm).of_dvd hd
  apply Units.ext
  show ZMod.castHom h (ZMod d) (idem r N * u + (1 - idem r N)) = ZMod.castHom h (ZMod d) u
  rw [map_add (f := _), map_mul, map_sub, h1, map_one]
  ring

private theorem projB {N : ℕ} (r d : ℕ) (hr : r.Prime) (h : d ∣ N) (hd : d ∣ ordCompl[r] N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h (proj r N u) = 1 := by
  have h1 : ZMod.castHom h (ZMod d) (idem r N) = 0 := by
    unfold idem
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_pow hd (Nat.totient_pos.2 (pow_pos hr.pos _)).ne'
  apply Units.ext
  show ZMod.castHom h (ZMod d) (idem r N * u + (1 - idem r N)) = 1
  rw [map_add (f := _), map_mul, map_sub, h1, map_one]
  ring

private theorem crtExt {N : ℕ} [NeZero N] (r : ℕ) {u v : (ZMod N)ˣ}
    (h1 : ZMod.unitsMap (Nat.ordProj_dvd N r) u = ZMod.unitsMap (Nat.ordProj_dvd N r) v)
    (h2 : ZMod.unitsMap (Nat.ordCompl_dvd N r) u = ZMod.unitsMap (Nat.ordCompl_dvd N r) v) : u = v := by
  have key : ∀ (d : ℕ) (h : d ∣ N), ZMod.unitsMap h u = ZMod.unitsMap h v →
      (u : ZMod N).val ≡ (v : ZMod N).val [MOD d] := by
    intro d h e
    have e' : ZMod.castHom h (ZMod d) (u : ZMod N) = ZMod.castHom h (ZMod d) (v : ZMod N) := congrArg Units.val e
    rw [← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (v : ZMod N), map_natCast, map_natCast] at e'
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 e'
  have h3 := (Nat.modEq_and_modEq_iff_modEq_mul (coprime_ordProj_ordCompl r N)).1 ⟨key _ _ h1, key _ _ h2⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h3
  apply Units.ext
  rw [← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (v : ZMod N)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

private theorem dvdCompl {N : ℕ} [NeZero N] {r d : ℕ} (hr : r.Prime) (h : d ∣ N) (hd : ¬ r ∣ d) : d ∣ ordCompl[r] N := by
  have hc : d.Coprime (ordProj[r] N) := (((Nat.Prime.coprime_iff_not_dvd hr).2 hd).symm).pow_right _
  apply hc.dvd_of_dvd_mul_left
  rwa [Nat.ordProj_mul_ordCompl_eq_self]

private theorem mapMap {N M d : ℕ} (h1 : d ∣ M) (h2 : M ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 u) = ZMod.unitsMap (h1.trans h2) u := by
  rw [← ZMod.unitsMap_comp h1 h2]; rfl

theorem UpperTheory.V.HV.projFacts :
    ∀ (N : ℕ) [NeZero N] (r : ℕ), r.Prime →
      (∀ u, ZMod.unitsMap (Nat.ordProj_dvd N r) (proj r N u) = ZMod.unitsMap (Nat.ordProj_dvd N r) u) ∧
      (∀ u, ZMod.unitsMap (Nat.ordCompl_dvd N r) (proj r N u) = 1) ∧ (∀ u, proj r N (proj r N u) = proj r N u) ∧
      (∀ r', r'.Prime → r' ≠ r → ∀ u, proj r N (proj r' N u) = 1) ∧ (¬ r ∣ N → ∀ u, proj r N u = 1) ∧
      (proj r N).range = (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker ∧ (proj r N).ker = (ZMod.unitsMap (Nat.ordProj_dvd N r)).ker ∧
      (∀ (M : ℕ) (h : M ∣ N), ¬ r ∣ M → ∀ u, ZMod.unitsMap h (proj r N u) = 1) ∧
      ∀ (M : ℕ) (h : M ∣ N) u, ZMod.unitsMap h (proj r N u) = proj r M (ZMod.unitsMap h u) := by
  intro N _ r hr
  have hA := projA r _ (Nat.ordProj_dvd N r) dvd_rfl
  have hB := projB r _ hr (Nat.ordCompl_dvd N r) dvd_rfl
  have hM : ∀ (r : ℕ), r.Prime → ∀ (M : ℕ) (h : M ∣ N), ¬ r ∣ M → ∀ u, ZMod.unitsMap h (proj r N u) = 1 :=
    fun r hr M h hM u => projB r M hr h (dvdCompl hr h hM) u
  refine ⟨hA, hB, fun u => crtExt r (hA _) (by rw [hB, hB]), fun r' hr' hne u => ?_, fun hN u => ?_, ?_, ?_,
    hM r hr, fun M h u => ?_⟩
  · refine crtExt r ?_ (by rw [hB, map_one])
    rw [hA, map_one]
    exact hM r' hr' _ _ (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hr' hr).1 (hr'.dvd_of_dvd_pow hd))) u
  · have := hM r hr N dvd_rfl hN u
    rwa [ZMod.unitsMap_self] at this
  · ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact hB v
    · intro hu
      exact ⟨u, crtExt r (hA u) ((hB u).trans (MonoidHom.mem_ker.1 hu).symm)⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hu
      rw [← hA, hu, map_one]
    · intro hu
      exact crtExt r (by rw [hA, hu, map_one]) (by rw [hB, map_one])
  · haveI : NeZero M := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) h⟩
    refine crtExt r ?_ ?_
    · rw [projA r _ _ dvd_rfl, mapMap, mapMap]
      exact projA r _ _ (Nat.ordProj_dvd_ordProj_of_dvd (NeZero.ne N) h r) u
    · rw [projB r _ hr _ dvd_rfl, mapMap]
      exact projB r _ hr _ (Nat.ordCompl_dvd_ordCompl_of_dvd h r) u
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

open Polynomial in
private theorem splitting_field_iso_quadratic (p : ℕ) (hp : 0 < p) (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (δ : K) (hδ : δ ^ 2 = -(p : K)) (L : Type) [Field L] [NumberField L]
    [hL : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Nonempty (L ≃ₐ[ℚ] K) := by
  classical
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hsK : (f.map (algebraMap ℚ K)).Splits := by
    have hfac : f.map (algebraMap ℚ K) = (X + C δ) * (X + C (-δ)) := by
      have hpK : (p : K) = -(δ ^ 2) := by rw [hδ]; ring
      rw [hf, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        map_natCast, hpK]
      simp only [map_neg, map_pow]
      ring
    rw [hfac]
    exact (Splits.X_add_C _).mul (Splits.X_add_C _)
  let φ := IsSplittingField.lift L f hsK
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hLK : Module.finrank ℚ L ≤ 2 :=
    hK ▸ LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj
  have hL1 : Module.finrank ℚ L ≠ 1 := by
    intro h1
    have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one (F := ℚ) (E := L) h1
    have hsL := IsSplittingField.splits L f
    have hdeg : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
      rw [Polynomial.degree_map, hf, Polynomial.degree_X_pow_add_C (by norm_num)]
      norm_num
    obtain ⟨r, hr⟩ := hsL.exists_eval_eq_zero hdeg
    have hrm : r ∈ (⊥ : Subalgebra ℚ L) := hbt ▸ Algebra.mem_top
    obtain ⟨q, rfl⟩ := Algebra.mem_bot.mp hrm
    have hq : algebraMap ℚ L (q ^ 2 + p) = 0 := by
      simpa [hf, Polynomial.eval_map] using hr
    have hq0 : q ^ 2 + (p : ℚ) = 0 := (algebraMap ℚ L).injective (by rw [hq, map_zero])
    have hpq : (0 : ℚ) < q ^ 2 + p := by
      have : (0 : ℚ) < p := by exact_mod_cast hp
      positivity
    linarith
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have h2 : Module.finrank ℚ L = 2 := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (h2.trans hK.symm)).1 hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem UpperTheory.V.HV.kstar :
    ∀ p : ℕ, p.Prime → p % 4 = 3 → discr (Kstar p) = -(p : ℤ) ∧ IsTotallyComplex (Kstar p) ∧ Module.finrank ℚ (Kstar p) = 2 ∧ ∃ s : Kstar p, s ^ 2 = -(p : Kstar p) := by
  intro p hp h3
  obtain ⟨K, _, _, hK2, hd⟩ := KStar.Consta.exists_quadField hp h3
  obtain ⟨⟨δ, hδ⟩, -⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hK2 hp.ne_zero hd
  haveI : Polynomial.IsSplittingField ℚ (Kstar p) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
    have h := Polynomial.IsSplittingField.splittingField (K := ℚ) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))
    have h' : Polynomial.IsSplittingField ℚ (Polynomial.SplittingField (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)))
        (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
      convert h
    exact h'
  obtain ⟨e⟩ := splitting_field_iso_quadratic p hp.pos K hK2 δ hδ (Kstar p)
  have hfr : Module.finrank ℚ (Kstar p) = 2 := e.toLinearEquiv.finrank_eq.trans hK2
  have hdisc : discr (Kstar p) = -(p : ℤ) := by
    rw [NumberField.discr_eq_discr_of_algEquiv (Kstar p) e, hd]
  obtain ⟨hs, htc⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hfr hp.ne_zero hdisc
  exact ⟨hdisc, htc, hfr, hs⟩
end

