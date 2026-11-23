module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem pow_mod_eq_pow_of_pow_eq_one' {F : Type} [Field F] {z : F} {m : ℕ} (h : z ^ m = 1) (k : ℕ) :
    z ^ (k % m) = z ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k m, pow_add, pow_mul, h, one_pow, mul_one]

private theorem rt_add {F : Type} [Field F] {ζ : F} {m : ℕ} (hm : 0 < m) (h : IsPrimitiveRoot ζ m) (i j : ZMod m) :
    ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [ZMod.val_add, pow_mod_eq_pow_of_pow_eq_one' h.pow_eq_one, pow_add]

private theorem rt_mul {F : Type} [Field F] {z : F} {m : ℕ} (h : z ^ m = 1) (i j : ZMod m) :
    z ^ (i * j).val = (z ^ i.val) ^ j.val := by
  rw [ZMod.val_mul, pow_mod_eq_pow_of_pow_eq_one' h, pow_mul]

private theorem rt_inj {F : Type} [Field F] {ζ : F} {m : ℕ} (hm : 0 < m) (h : IsPrimitiveRoot ζ m) {i j : ZMod m}
    (e : ζ ^ i.val = ζ ^ j.val) : i = j := by
  haveI : NeZero m := ⟨hm.ne'⟩
  exact ZMod.val_injective m (h.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) e)

private theorem rt_ex {F : Type} [Field F] {ζ : F} {m : ℕ} (hm : 0 < m) (h : IsPrimitiveRoot ζ m) {z : F}
    (hz : z ^ m = 1) : ∃ i : ZMod m, z = ζ ^ i.val := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨k, hk, hk'⟩ := h.eq_pow_of_pow_eq_one hz
  refine ⟨(k : ZMod m), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk, hk']

private theorem cyc_spec {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ζ : Ω} {m : ℕ} (hm : 0 < m) (h : IsPrimitiveRoot ζ m)
    (s : Ω ≃ₐ[ℚ] Ω) : ∀ z : Ω, z ^ m = 1 → s z = z ^ (cyc m s).val := by
  have hsm : (s ζ) ^ m = 1 := by rw [← map_pow, h.pow_eq_one, map_one]
  obtain ⟨k, hk⟩ := rt_ex hm h hsm
  have hex : ∃ y : ZMod m, ∀ z : Ω, z ^ m = 1 → s z = z ^ y.val := by
    refine ⟨k, fun z hz => ?_⟩
    obtain ⟨i, hi⟩ := rt_ex hm h hz
    rw [hi, map_pow, hk, ← pow_mul, ← pow_mul, mul_comm]
  unfold cyc
  exact Classical.epsilon_spec hex

theorem UpperTheory.V.Z.Kato.Sym.lgB :
    UpperTheory.V.Z.Kato.Sym.LgB := by
  intro Ω _ _ _ ε X m hm
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hζΩ : IsPrimitiveRoot (eOm ε (1 / (m : ℚ))) m := isPrimitiveRoot_eOm ε hm.ne'
  have hz : IsPrimitiveRoot (zt X m) m :=
    hζΩ.map_of_injective (f := (io X).comp (algebraMap Ω X.K)) (RingHom.injective _)
  have hspec : ∀ a b : Kb X, b ≠ 0 → a ^ m = b ^ m → a = zt X m ^ (lg X m a b).val * b := by
    intro a b hb hab
    have h1 : (a / b) ^ m = 1 := by rw [div_pow, hab, div_self (pow_ne_zero _ hb)]
    obtain ⟨i, hi⟩ := rt_ex hm hz h1
    have hex : ∃ i : ZMod m, a = zt X m ^ i.val * b := ⟨i, by rw [← hi, div_mul_cancel₀ a hb]⟩
    unfold lg
    exact Classical.epsilon_spec hex
  have huniq : ∀ (a b : Kb X) (i : ZMod m), b ≠ 0 → a = zt X m ^ i.val * b → lg X m a b = i := by
    intro a b i hb hai
    have hab : a ^ m = b ^ m := by
      rw [hai, mul_pow, ← pow_mul, mul_comm i.val m, pow_mul, hz.pow_eq_one, one_pow, one_mul]
    have h2 := hspec a b hb hab
    apply rt_inj hm hz
    apply mul_right_cancel₀ hb
    rw [← h2, ← hai]
  have hne : ∀ b c : Kb X, c ≠ 0 → b ^ m = c ^ m → b ≠ 0 := by
    intro b c hc hbc h0
    have : c ^ m ≠ 0 := pow_ne_zero _ hc
    rw [← hbc, h0, zero_pow hm.ne'] at this
    exact this rfl
  refine ⟨hz, hspec, huniq, ?_, ?_, ?_, ?_⟩
  · intro a b c hc hab hbc
    have hb := hne b c hc hbc
    apply huniq a c _ hc
    rw [rt_add hm hz, mul_assoc, ← hspec b c hc hbc, ← hspec a b hb hab]
  · intro a b a' b' hb hb' hab hab'
    apply huniq _ _ _ (mul_ne_zero hb hb')
    rw [rt_add hm hz]
    conv_lhs => rw [hspec a b hb hab, hspec a' b' hb' hab']
    ring
  · intro σ τ s hadm hl a b hb hab
    have hσb : σ b ≠ 0 := (map_ne_zero σ).2 hb
    have hσz : σ (zt X m) = zt X m ^ (cyc m s).val := by
      show σ ((io X) ((algebraMap Ω X.K) (eOm ε (1 / (m : ℚ))))) =
        ((io X) ((algebraMap Ω X.K) (eOm ε (1 / (m : ℚ))))) ^ (cyc m s).val
      rw [hl, hadm.1, cyc_spec hm hζΩ s _ hζΩ.pow_eq_one, map_pow, map_pow]
    apply huniq _ _ _ hσb
    rw [rt_mul hz.pow_eq_one, ← hσz, ← map_pow, ← map_mul, ← hspec a b hb hab]
  · intro s t
    refine ⟨?_, ?_, cyc_spec hm hζΩ s⟩
    · apply rt_inj hm hζΩ
      rw [← cyc_spec hm hζΩ (s * t) _ hζΩ.pow_eq_one, rt_mul hζΩ.pow_eq_one,
        ← cyc_spec hm hζΩ s _ hζΩ.pow_eq_one, ← map_pow, ← cyc_spec hm hζΩ t _ hζΩ.pow_eq_one]
      rfl
    · apply rt_inj hm hζΩ
      rw [← cyc_spec hm hζΩ 1 _ hζΩ.pow_eq_one, AlgEquiv.one_apply, ZMod.val_one_eq_one_mod,
        pow_mod_eq_pow_of_pow_eq_one' hζΩ.pow_eq_one, pow_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.EOmZero
section
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem dg_mat (k : ℕ) (hk : 0 < k) :
    (((dg k : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (!![(k : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  have hdet : 0 < (!![(k : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two_of]
    exact_mod_cast hk
  simp only [dg, toGQ, dif_pos hdet]
  rfl

private theorem ofSL_mat (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := rfl

private theorem eOm_zero' {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  have h : Complex.exp (2 * Real.pi * Complex.I * ((0 : ℚ) : ℂ)) = ε 1 := by simp
  unfold eOm
  rw [h]
  exact Function.leftInverse_invFun ε.injective 1

theorem galDg : GalDg := by
  intro Ω _ _ _ ε X k hk
  have hinj : Function.Injective X.exp := X.exp.toRingHom.injective
  have hD : ∀ (f : X.K) (q : ℚ), (X.exp (X.sl (dg k) f)).coeff q = (X.exp f).coeff (q / k) := by
    intro f q
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    have h := X.exp_upper (dg k) (by simp [ent, dg_mat k hk]) f (q / k)
    have e00 : ent (dg k) 0 0 = k := by simp [ent, dg_mat k hk]
    have e01 : ent (dg k) 0 1 = 0 := by simp [ent, dg_mat k hk]
    have e11 : ent (dg k) 1 1 = 1 := by simp [ent, dg_mat k hk]
    rw [e00, e01, e11] at h
    simpa [hkq, eOm_zero'] using h
  refine ⟨fun s f => hinj ?_, fun γ γ' h f => ?_, ?_⟩
  · ext q
    rw [X.gal_exp, hD, hD, X.gal_exp]
  · have hm : dg k * ofSL γ = ofSL γ' * dg k := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [dg_mat k hk, ofSL_mat, ofSL_mat, ← Matrix.map_mul, ← Matrix.map_mul, h]
    rw [← X.sl_mul, ← X.sl_mul, hm]
  · intro M γ
    induction γ using Matrix.SpecialLinearGroup.fin_two_induction with
    | _ a b c d hdet => ?_
    intro hγ
    obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
    change ((a : ℤ) : ZMod (k * M)) = 1 at h00
    change ((b : ℤ) : ZMod (k * M)) = 0 at h01
    change ((c : ℤ) : ZMod (k * M)) = 0 at h10
    change ((d : ℤ) : ZMod (k * M)) = 1 at h11
    have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd b _).mp h01
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd c _).mp h10
    have ha := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 a (k * M)).mp (by rw [Int.cast_one]; exact h00.symm)
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 d (k * M)).mp (by rw [Int.cast_one]; exact h11.symm)
    push_cast at ha hb hc hd
    have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    obtain ⟨c', rfl⟩ : (k : ℤ) ∣ c := dvd_trans (dvd_mul_right _ _) hc
    have hc' : (M : ℤ) ∣ c' := (mul_dvd_mul_iff_left hkz).mp hc
    have hdet' : a * d - (k * b) * c' = 1 := by rw [← hdet]; ring
    refine ⟨⟨!![a, k * b; c', d], by rw [Matrix.det_fin_two_of]; exact hdet'⟩, ?_, ?_⟩
    · refine CongruenceSubgroup.Gamma_mem.mpr ⟨?_, ?_, ?_, ?_⟩
      · change ((a : ℤ) : ZMod M) = 1
        rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact dvd_sub_comm.mp (dvd_trans (dvd_mul_left _ _) ha)
      · change ((k * b : ℤ) : ZMod M) = 0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact (dvd_trans (dvd_mul_left _ _) hb).mul_left _
      · change ((c' : ℤ) : ZMod M) = 0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hc'
      · change ((d : ℤ) : ZMod M) = 1
        rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact dvd_sub_comm.mp (dvd_trans (dvd_mul_left _ _) hd)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end UpperTheory.V.Z.Kato.Sym

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Recip
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.recip :
    UpperTheory.V.Z.Kato.Sym.Recip := by
  classical
  intro Ω _ _ _ ε X s γ S
  choose L hL hLf using X.level
  set M : ℕ := ∏ f ∈ S, L f with hMdef
  have hM : 0 < M := Finset.prod_pos fun f _ => hL f
  have hfix : ∀ f ∈ S, ∀ δ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL δ) f = f := by
    intro f hf δ hδ
    apply hLf f δ
    have hd : L f ∣ M := Finset.dvd_prod_of_mem _ hf
    rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hδ
    have c1 := congrArg (ZMod.castHom hd (ZMod (L f))) h1
    have c2 := congrArg (ZMod.castHom hd (ZMod (L f))) h2
    have c3 := congrArg (ZMod.castHom hd (ZMod (L f))) h3
    have c4 := congrArg (ZMod.castHom hd (ZMod (L f))) h4
    rw [map_intCast] at c1 c2 c3 c4
    rw [map_one] at c1 c4
    rw [map_zero] at c2 c3
    exact ⟨c1, c2, c3, c4⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hex : ∀ t : Ω ≃ₐ[ℚ] Ω, ∃ d : ℕ, t ζ = ζ ^ d := fun t => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := t ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  obtain ⟨d, hd⟩ := hex s
  obtain ⟨e, he⟩ := hex s.symm
  have hde : (d : ZMod M) * e = 1 := by
    have h1 : ζ ^ (d * e) = ζ ^ 1 := by
      rw [pow_mul, ← hd, ← map_pow, ← he]; simp
    have h2 := (hζ.isOfFinOrder hM.ne').pow_eq_pow_iff_modEq.mp h1
    rw [← hζ.eq_orderOf] at h2
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    simpa using this
  have hdet : ((en γ 0 0 : ℤ) : ZMod M) * en γ 1 1 - (en γ 0 1 : ℤ) * (en γ 1 0 : ℤ) = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod M) h
    simpa [en] using this
  let A : SL(2, ZMod M) := ⟨!![(en γ 0 0 : ℤ), e * (en γ 0 1 : ℤ); d * (en γ 1 0 : ℤ), (en γ 1 1 : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet - ((en γ 0 1 : ℤ) : ZMod M) * (en γ 1 0 : ℤ) * hde⟩
  obtain ⟨γ', hγ'⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M A
  have hent : ∀ i j, ((en γ' i j : ℤ) : ZMod M) = A.1 i j := fun i j => by
    rw [← hγ']; rfl
  refine ⟨γ', fun f hf => (X.recip M f hM (hfix f hf) ζ hζ s d (by rw [hd, zpow_natCast]) γ' γ ?_).symm⟩
  rw [hent, hent, hent, hent]
  refine ⟨by simp [A], ?_, by simp [A], by simp [A]⟩
  have : A.1 0 1 = e * (en γ 0 1 : ℤ) := by simp [A]
  rw [this]
  push_cast
  linear_combination -((en γ 0 1 : ℤ) : ZMod M) * hde
end

