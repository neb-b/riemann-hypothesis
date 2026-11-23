module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.EvalSmulCong
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelPowPrimeFourthPowerDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.MemGamIff
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem gam_mono {M M' : ℕ} (h : M ∣ M') : CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨a, b, c, d⟩ := hγ
  have e := fun (x : ℤ) (y : ZMod M') (hh : (x : ZMod M') = y) => congrArg (ZMod.castHom h (ZMod M)) hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_intCast, map_one] using e _ _ a
  · simpa only [map_intCast, map_zero] using e _ _ b
  · simpa only [map_intCast, map_zero] using e _ _ c
  · simpa only [map_intCast, map_one] using e _ _ d

private theorem gam_le {M N l : ℕ} (hN : N ∣ M) (hl : l ∣ M) : CongruenceSubgroup.Gamma M ≤ Gam N l := by
  intro γ hγ
  have h1 := gam_mono hN hγ
  have h2 := gam_mono hl hγ
  rw [CongruenceSubgroup.Gamma_mem] at h1 h2
  refine ⟨?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma1_mem _ _).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩
  · exact CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1

private theorem mem_gam_iff (M : ℕ) (a b : SL(2, ℤ)) : a * b⁻¹ ∈ CongruenceSubgroup.Gamma M ↔
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) a = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) b := by
  rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, mul_inv_eq_one]

private theorem map_liftSL (M : ℕ) (γ : SL(2, ZMod M)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ :=
  Classical.epsilon_spec (GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M γ)

private theorem isTr_img {M N l : ℕ} [NeZero M] (hN : N ∣ M) (hl : l ∣ M) :
    IsTr (CongruenceSubgroup.Gamma M) (Gam N l) (fun γ : {γ // γ ∈ img (Gam N l) M} => liftSL M γ.1) := by
  refine ⟨fun γ => ?_, fun δ hδ => ?_⟩
  · obtain ⟨δ, hδ, e⟩ := (Finset.mem_filter.1 γ.2).2
    have h1 : liftSL M γ.1 * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [mem_gam_iff, map_liftSL, e]
    have h2 := mul_mem (gam_le hN hl h1) hδ
    simpa using h2
  · refine ⟨⟨Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, δ, hδ, rfl⟩⟩, ?_, fun γ hγ => ?_⟩
    · show _ ∈ _
      rw [mem_gam_iff, map_liftSL]
    · have h1 : δ * (liftSL M γ.1)⁻¹ ∈ CongruenceSubgroup.Gamma M := hγ
      rw [mem_gam_iff, map_liftSL] at h1
      exact Subtype.ext h1.symm

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem recip_mod [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {σ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M)
    (f : X.K) (h : SL(2, ℤ)) : ∃ δ ∈ CongruenceSubgroup.Gamma M,
      X.gal σ (X.sl (ofSL (δ * h)) f) = X.sl (ofSL h) (X.gal σ f) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨M0, hM0, hf⟩ := X.level f
  have hM' : M0 * M ≠ 0 := mul_ne_zero hM0.ne' hM
  haveI : NeZero (M0 * M) := ⟨hM'⟩
  have hζ := isPrimitiveRoot_eOm ε hM'
  set ζ := eOm ε (1 / ((M0 * M : ℕ) : ℚ)) with hζd
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ⁻¹ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hmod : ∀ a b : ℕ, ζ ^ a = ζ ^ b → a ≡ b [MOD M0 * M] := fun a b hab => by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hM').pow_eq_pow_iff_modEq.1 hab
  have hij : (i : ZMod (M0 * M)) * j = 1 := by
    have : ζ ^ (i * j) = ζ ^ 1 := by
      rw [pow_mul, hi, ← map_pow, hj, pow_one, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hmod _ _ this)
    simpa using h2
  have hi1 : (i : ZMod M) = 1 := by
    have h1 : σ (ζ ^ M0) = ζ ^ M0 := (mem_fixMu_iff σ).1 hσ _ (by rw [← pow_mul, hζ.pow_eq_one])
    have : ζ ^ (M0 * i) = ζ ^ (M0 * 1) := by
      rw [mul_one, mul_comm, pow_mul, hi, ← map_pow, h1]
    have h2 := Nat.ModEq.mul_left_cancel' hM0.ne' (hmod _ _ this)
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  let φ := ZMod.castHom (dvd_mul_left M M0) (ZMod M)
  have hj1 : (j : ZMod M) = 1 := by
    have := congrArg φ hij
    rwa [map_mul, map_natCast, map_natCast, map_one, hi1, one_mul] at this
  have hdet : en h 0 0 * en h 1 1 - en h 0 1 * en h 1 0 = 1 := by
    have := h.2
    rwa [Matrix.det_fin_two] at this
  have hdet' : (en h 0 0 : ZMod (M0 * M)) * en h 1 1 - en h 0 1 * en h 1 0 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod (M0 * M)) hdet
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) (M0 * M)
    ⟨!![(en h 0 0 : ZMod (M0 * M)), j * en h 0 1; i * en h 1 0, en h 1 1], by
      rw [Matrix.det_fin_two_of]; linear_combination hdet' - (en h 0 1 : ZMod (M0 * M)) * (en h 1 0) * hij⟩
  have e : ∀ a b, (en γ a b : ZMod (M0 * M)) =
      !![(en h 0 0 : ZMod (M0 * M)), j * en h 0 1; i * en h 1 0, en h 1 1] a b := fun a b =>
    congrArg (fun m : SL(2, ZMod (M0 * M)) => m.1 a b) hγ
  have e00 : (en γ 0 0 : ZMod (M0 * M)) = en h 0 0 := e 0 0
  have e01 : (en γ 0 1 : ZMod (M0 * M)) = j * en h 0 1 := e 0 1
  have e10 : (en γ 1 0 : ZMod (M0 * M)) = i * en h 1 0 := e 1 0
  have e11 : (en γ 1 1 : ZMod (M0 * M)) = en h 1 1 := e 1 1
  refine ⟨γ * h⁻¹, ?_, ?_⟩
  · rw [mem_gam_iff]
    have f00 := congrArg φ e00
    have f01 := congrArg φ e01
    have f10 := congrArg φ e10
    have f11 := congrArg φ e11
    simp only [map_mul, map_intCast, map_natCast, hi1, hj1, one_mul] at f00 f01 f10 f11
    ext a b
    fin_cases a <;> fin_cases b
    exacts [f00, f01, f10, f11]
  · rw [inv_mul_cancel_right]
    refine X.recip (M0 * M) f (Nat.pos_of_ne_zero hM') (fun δ hδ => hf δ (gam_mono (dvd_mul_right _ _) hδ)) ζ hζ σ i
      (by rw [zpow_natCast, hi]) γ h ⟨e00.symm, ?_, ?_, e11.symm⟩
    · rw [e01, Int.cast_natCast, ← mul_assoc, hij, one_mul]
    · rw [e10, Int.cast_natCast]

private theorem trM_eq [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (x : X.Khat l) :
    trM X l N M w g x = trH X l w (fun γ : {γ // γ ∈ img (Gam N l) M} => liftSL M γ.1) ![en g 0 0, en g 0 1]
      (X.kmap l (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv x) := by
  unfold trM trH
  rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Tower.act_act Ω ε X l _ _ (by simp) (by simp)]
  congr 1
  funext u
  simp [Tower.act, sec, mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sTrM :
    UpperTheory.V.Z.Kato.Nb.STrM := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW a ha hI
  have hlp : l.Prime := Fact.out
  have hNM : N ∣ M := hL.eq ▸ dvd_mul_right _ _
  have hnM : l ^ n ∣ M := hL.eq ▸ hL.dl.mul_left _
  have hlM : l ∣ M := (dvd_pow_self l (by have := hL.pos; omega)).trans hnM
  obtain ⟨hE, hAdd, -, hSum, hDv, -⟩ := sApi Ω ε X l n
  obtain ⟨hR, -, -, hCg, hMap, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, hTo, -, hUn, -, -, hCy⟩ := sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))
  refine ⟨?_, fun σ hσ => ?_⟩
  · have hle : CongruenceSubgroup.Gamma M ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) :=
      le_inf (gam_le hNM hlM) (gam_mono hnM)
    have hT := isTr_img (l := l) hNM hlM
    have hRep : Rep X l n (slU X (ofSL g) a)
        (X.kmap l (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (a : X.K))) := by
      rw [hTo]; exact hMap _ _ _ (hR a)
    have hU := hUn _ (ofSL g) a ha
    have hH : InvH X (CongruenceSubgroup.Gamma M) (l ^ n) (slU X (ofSL g) a) := by
      intro γ hγ
      obtain ⟨k, hk⟩ := hI _ ((CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ g)
      refine ⟨slU X (ofSL g) k, ?_⟩
      show X.sl (ofSL γ) (X.sl (ofSL g) a) = X.sl (ofSL g) a * (X.sl (ofSL g) k) ^ l ^ n
      rw [← map_pow, ← map_mul, ← hk, ← X.sl_mul, ← X.sl_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
    obtain ⟨h1, h2, -⟩ := trc ε X l N w n _ hle _ _ hT ![en g 0 0, en g 0 1] _ _ hRep
    rw [trM_eq]
    exact ⟨⟨_, h1 hU, hE.refl _⟩, h2 hH, hW n _ M (Nat.pos_of_ne_zero (NeZero.ne M)) le_rfl hle _ _ hT _ _ _ hU hH hRep⟩
  · haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow (by have := hL.pos; omega) hlp.one_lt⟩
    have hσ' : σ ∈ fixMu Ω (l ^ n) := by
      rw [mem_fixMu_iff] at hσ ⊢
      intro z hz
      obtain ⟨c, hc⟩ := hnM
      exact hσ z (by rw [hc, pow_mul, hz, one_pow])
    have hχ := (sCycZ Ω l n σ).2
    rw [(hCy (l ^ n) σ).2.2.2.1.1 hσ', Units.val_one, ZMod.val_one, Nat.cast_one] at hχ
    unfold trM
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine hSum _ _ _ _ fun γ _ u => ?_
    generalize g * liftSL M γ = h
    obtain ⟨δ, hδ, e⟩ := recip_mod X (NeZero.ne M) hσ (a : X.K) h
    obtain ⟨k, hk⟩ := hI δ hδ
    set A := X.kmap l (X.gal σ) (X.kmap l (X.sl (ofSL h)).toRingEquiv (clsK X l n (a : X.K))) with hA
    set B := X.kmap l (X.sl (ofSL h)).toRingEquiv (clsK X l n (X.gal σ a)) with hB
    have rA : Rep X l n (galU X σ (slU X (ofSL h) a)) A := hMap _ _ _ (hMap _ _ _ (hR a))
    have rB : Rep X l n (slU X (ofSL h) (galU X σ a)) B := hMap _ _ _ (hR (galU X σ a))
    have hBA := hCg _ _ _ _ rB rA ⟨galU X σ (slU X (ofSL h) k), Units.ext (by
      show X.sl (ofSL h) (X.gal σ a) = X.gal σ (X.sl (ofSL h) a) * (X.gal σ (X.sl (ofSL h) k)) ^ l ^ n
      rw [← e, map_mul, X.sl_mul, hk, map_mul, map_pow, map_mul, map_pow])⟩
    set c := (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) * u 1]) 0 with hc
    set c' := (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 with hc'
    have hcc : (l : ℤ_[l]) ^ n ∣ c ^ w - c' ^ w := by
      refine Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow c c' w)
      obtain ⟨t, ht⟩ := hχ
      refine ⟨mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * t * u 1, ?_⟩
      simp only [hc, hc', Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * u 1) * ht
    have h3 := hDv _ _ A hcc
    show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal σ) (X.kmap l (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (c ^ w • clsK X l n (a : X.K))) - X.kmap l (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (c' ^ w • clsK X l n (X.gal σ a))) = 0
    rw [hTo, map_smul, map_smul, map_smul, ← hA, ← hB]
    have : c ^ w • A - c' ^ w • B = (c ^ w • A - c' ^ w • A) - c' ^ w • (B - A) := by
      rw [smul_sub]; abel
    rw [this, map_sub, h3, map_smul, hBA, smul_zero, sub_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OfDesc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups

theorem UpperTheory.V.Z.Kato.Nb.sEsLev : UpperTheory.V.Z.Kato.Nb.SEsLev := by
  unfold SEsLev
  intro Ω _ _ _ ε X l _ N w hN b hb n
  have hl : Nat.Prime l := Fact.out
  obtain ⟨⟨c, hcA, hbu⟩, hinv⟩ := hb
  have api := sApi Ω ε X l n
  have cls := sCls Ω ε X l n
  have ev := _root_.GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hsub : ∀ (x y x' y' : ℤ_[l]) (a e : ℕ), (l : ℤ_[l]) ^ n ∣ x - x' → (l : ℤ_[l]) ^ n ∣ y - y' →
      (l : ℤ_[l]) ^ n ∣ x ^ a * y ^ e - x' ^ a * y' ^ e := by
    intro x y x' y' a e hx hy
    have h : x ^ a * y ^ e - x' ^ a * y' ^ e = (x ^ a - x' ^ a) * y ^ e + x' ^ a * (y ^ e - y' ^ e) := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left (hx.trans (sub_dvd_pow_sub_pow x x' a)) _)
      (dvd_mul_of_dvd_right (hy.trans (sub_dvd_pow_sub_pow y y' e)) _)
  have cong : ∀ u u' : Fin 2 → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ u i - u' i) →
      (AdicCompletion.eval (idl l) (X.Kl l) n) (b u - b u') = 0 := by
    intro u u' h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hbu u, hbu u', ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact api.2.2.2.2.1 _ _ _ (hsub _ _ _ _ _ _ (h 0) (h 1))
  refine ⟨cong, ?_, ?_⟩
  · intro t u
    rw [hbu, hbu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    have hi : (i : ℕ) + (w - i) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.2)
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [show t ^ w = t ^ (i : ℕ) * t ^ (w - i) by rw [← pow_add, hi]]
    ring
  · intro u
    have hbA : b u ∈ X.A l := by
      rw [hbu]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcA i)
    obtain ⟨φ0, hφ, hd⟩ := X.j_hol
    obtain ⟨f, hfU, hf⟩ := _root_.GlobalTheory.KZ.ES.exists_un_eval_eq_cls ε X ⟨φ0, hd, hφ⟩ l n (b u) hbA
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 6 * l * N * l ^ n := ⟨_, rfl⟩
    have hMpos : 0 < M := by
      rw [hM]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hl.pos) hN) (pow_pos hl.pos n)
    have hMd : 6 * l ∣ M := ⟨N * l ^ n, by rw [hM]; ring⟩
    have hNM : (N : ℤ) ∣ (M : ℤ) := ⟨6 * l * l ^ n, by rw [hM]; push_cast; ring⟩
    have hlM : (l : ℤ) ∣ (M : ℤ) := ⟨6 * N * l ^ n, by rw [hM]; push_cast; ring⟩
    have hlnM : (l : ℤ) ^ n ∣ (M : ℤ) := ⟨6 * l * N, by rw [hM]; push_cast; ring⟩
    have key : ∀ (d : ℕ) (x y : ℤ), (d : ℤ) ∣ y - x → ((x : ZMod d) = (y : ZMod d)) :=
      fun d x y h => (ZMod.intCast_eq_intCast_iff_dvd_sub x y d).mpr h
    have hdl : ∀ x : ℤ, (M : ℤ) ∣ x → (l : ℤ_[l]) ^ n ∣ (x : ℤ_[l]) := by
      intro x hx
      obtain ⟨e, he⟩ := hlnM.trans hx
      exact ⟨(e : ℤ_[l]), by rw [he]; push_cast; ring⟩
    have hγ : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ,
        (X.sl (ofSL γ)) (f : X.K) = (f : X.K) * (g : X.K) ^ l ^ n := by
      intro γ hγM
      rw [CongruenceSubgroup.Gamma_mem] at hγM
      obtain ⟨h00, h01, h10, h11⟩ := hγM
      have d00 : (M : ℤ) ∣ 1 - γ 0 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h00)
      have d01 : (M : ℤ) ∣ 0 - γ 0 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h01)
      have d10 : (M : ℤ) ∣ 0 - γ 1 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h10)
      have d11 : (M : ℤ) ∣ 1 - γ 1 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h11)
      have hG : γ ∈ Gam N l := by
        show γ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
        refine Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N γ).mpr ⟨?_, ?_, ?_⟩,
          CongruenceSubgroup.Gamma0_mem.mpr ?_⟩
        · simpa using key N _ _ (hNM.trans d00)
        · simpa using key N _ _ (hNM.trans d11)
        · simpa using key N _ _ (hNM.trans d10)
        · simpa using key l _ _ (hlM.trans d10)
      have hact := congrFun (hinv γ hG) u
      simp only [GlobalTheory.KZ.Tower.act, LinearMap.coe_mk, AddHom.coe_mk] at hact
      rw [Betti.toGQ_sl] at hact
      have hcu : ∀ i, (l : ℤ_[l]) ^ n ∣ (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) i - u i := by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 - u 0
              = ((γ 0 0 - 1 : ℤ) : ℤ_[l]) * u 0 + ((γ 0 1 : ℤ) : ℤ_[l]) * u 1 := by
            simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring
          rw [e]
          exact dvd_add (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d00)) _)
            (dvd_mul_of_dvd_left (hdl _ (by simpa using d01)) _)
        · have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 - u 1
              = ((γ 1 0 : ℤ) : ℤ_[l]) * u 0 + ((γ 1 1 - 1 : ℤ) : ℤ_[l]) * u 1 := by
            simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring
          rw [e]
          exact dvd_add (dvd_mul_of_dvd_left (hdl _ (by simpa using d10)) _)
            (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d11)) _)
      have heq : (AdicCompletion.eval (idl l) (X.Kl l) n) (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
          = X.cls l n f := by
        rw [← hf, ← sub_eq_zero, ← map_sub]
        exact cong _ u hcu
      have h2 := KmapA.eval_kmap X l (X.sl (ofSL γ)).toRingEquiv n _ f heq
      rw [hact, hf] at h2
      obtain ⟨g, hg⟩ := (ev.2.1 _ _).mp h2.symm
      refine ⟨g, ?_⟩
      have := congrArg Units.val hg
      simpa using this
    obtain ⟨k', h, hlev⟩ := _root_.GlobalTheory.KZ.ES.desc_pow_four ε X l n M hl hMpos hMd f hγ
    refine ⟨n + k', f ^ 4 * h ^ l ^ n, Nat.le_add_right _ _, ?_, ?_, ?_⟩
    · intro W hW
      obtain ⟨g, hg⟩ := hfU W hW
      refine ⟨g ^ 4 * h, ?_⟩
      have hg0 : (g : X.K) ≠ 0 := g.ne_zero
      have hh0 : (h : X.K) ≠ 0 := h.ne_zero
      have e : ((f ^ 4 * h ^ l ^ n : X.Kˣ) : X.K) / ((g ^ 4 * h : X.Kˣ) : X.K) ^ l ^ n
          = ((f : X.K) / (g : X.K) ^ l ^ n) ^ 4 := by
        push_cast
        field_simp
        ring
      rw [e, map_pow, hg, one_pow]
    · have e : M * l ^ k' = 6 * l * N * l ^ (n + k') := by rw [hM, pow_add]; ring
      rw [← e]
      push_cast
      exact hlev
    · have r1 : UpperTheory.Kd.K4.Rep X l n f (b u) := hf
      have r2 := cls.2.2.1 f (b u) 4 r1
      have r3 : UpperTheory.Kd.K4.Rep X l n (h ^ l ^ n) 0 := by
        show _ = _
        rw [map_zero]
        have h3 := (ev.2.1 (h ^ l ^ n) 1).mpr ⟨h, by simp⟩
        rw [h3, ev.2.2.2.1]
      have h4 := (cls.2.1 _ _ _ _ r2 r3).1
      simpa using h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.PushPsi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.PushforwardPsi

private theorem exF {Γ A C : Type} [Group Γ] [CommGroup A] [CommGroup C] (c : Γ →* A) (ψ : Γ →* C)
    (h : ∀ s, c s = 1 → ψ s = 1) : ∃ f : A → C, ∀ a s, f (a * (c s)⁻¹) = f a * ψ s := by
  have h1 : ∀ a : A, ∃ s, c s = a⁻¹ * (QuotientGroup.mk a : A ⧸ c.range).out := fun a =>
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk a : A ⧸ c.range)).symm
  choose σ hσ using h1
  refine ⟨fun a => ψ (σ a), fun a s => ?_⟩
  have e : (QuotientGroup.mk (a * (c s)⁻¹) : A ⧸ c.range) = QuotientGroup.mk a :=
    QuotientGroup.eq.2 ⟨s, by simp⟩
  have h2 := h ((σ (a * (c s)⁻¹))⁻¹ * (σ a * s)) (by
    rw [map_mul, map_mul, map_inv, hσ, hσ, e, inv_mul_eq_one, mul_inv, inv_inv, mul_right_comm])
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul] at h2
  exact h2

private theorem exC (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] :
    ∃ c : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ, ∀ s, cycM M s = c s ∧ ∀ z : Ω, z ^ M = 1 → s z = z ^ (c s : ZMod M).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨hζ.autToPow ℚ, fun s => ?_⟩
  have hs : ∀ z : Ω, z ^ M = 1 → s z = z ^ (hζ.autToPow ℚ s : ZMod M).val := fun w hw => by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
    rw [map_pow, ← hζ.autToPow_spec ℚ s, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨?_, hs⟩
  have hM := cycM_spec M s ⟨_, hs⟩
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((hM ζ hζ.pow_eq_one).symm.trans (hs ζ hζ.pow_eq_one))

private theorem push_prod {Γ A B B' V : Type} [Group Γ] [AddCommMonoid V] [Fintype A] [Fintype B'] [DecidableEq B]
    {i1 : Fintype (A × B')} {i2 : DecidableEq (A × B)} (g : B' → B) (Z : Γ → A × B' → V) (s : Γ) (a : A) (y : B) :
    @push Γ (A × B) (A × B') i1 i2 V _ (Prod.map id g) Z s (a, y) = ∑ y', if g y' = y then Z s (a, y') else 0 := by
  obtain rfl : i1 = instFintypeProd A B' := Subsingleton.elim _ _
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun y' _ => ?_
  by_cases h : g y' = y <;> simp [h]

end UpperTheory.V.Z.Kato.Nb.PushforwardPsi

open UpperTheory.V.Z.Kato.Nb.PushforwardPsi in
theorem UpperTheory.V.Z.Kato.Nb.sPushPsi :
    UpperTheory.V.Z.Kato.Nb.SPushPsi := by
  intro l _ Ω _ _ _ cf ρ p n _ ψw hψ Y hc hp hcont hO
  obtain ⟨c, hcs⟩ := exC Ω p
  obtain ⟨f, hf⟩ := exF c ψw fun s hs => hψ s fun z hz => by
    rw [(hcs s).2 z hz, hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  refine ⟨fun r s x => ∑ t, if f t = x.1 then Y r s (t, x.2) else 0, fun r s s' x => ?_, fun r x i => ?_,
    fun r s x i => ?_, fun r s => ?_, fun r s y => ?_⟩
  · have e : ∑ t, (if f t = (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).1 then
        Y r s' (t, (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).2) else 0) =
        ∑ t, if f t = x.1 then Y r s' ((t, x.2) * cycT l r p s) else 0 := by
      symm
      refine Fintype.sum_equiv (Equiv.mulRight (c s)⁻¹) _ _ fun t => ?_
      simp [hf, cycT, (hcs s).1]
    beta_reduce
    rw [e, Matrix.mulVec_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · exact hc r s s' _
    · simp
  · simp only [Finset.sum_apply]
    refine continuous_finsetSum _ fun t _ => ?_
    split_ifs
    · exact hcont r _ i
    · exact continuous_const
  · simp only [Finset.sum_apply]
    refine sum_mem fun t _ => ?_
    split_ifs
    · exact hO r s _ i
    · exact zero_mem _
  · funext ⟨a, y⟩
    rw [push_prod]
    have e : ∀ t, Y r s (t, y) = ∑ y', if redL l r y' = y then Y (r + 1) s (t, y') else 0 := fun t => by
      rw [hp r, push_prod]
    simp only [e]
    have e2 : ∀ (P : Prop) [Decidable P] {ι : Type} [Fintype ι] (v : ι → Fin 2 → Qbar l),
        (if P then ∑ j, v j else 0) = ∑ j, if P then v j else 0 := fun P _ _ _ v => by split_ifs <;> simp
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun t _ => ?_
    change (if f t = a then if redL l r y' = y then _ else 0 else 0) = if redL l r y' = y then if f t = a then _ else 0 else 0
    split_ifs <;> rfl
  · rw [Finset.sum_comm]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SRel0
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

theorem UpperTheory.V.Z.Kato.Nb.sRel0 :
    UpperTheory.V.Z.Kato.Nb.SRel0 := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he c₀ Y hY r n
  obtain ⟨bB, hL, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, heq, -⟩ := hA
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h2 : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  rw [h2] at hL
  obtain ⟨-, -, -, -, -, -, -, hcy⟩ := sSlD Ω ε X N hN
  have hfix : ∀ (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (topM l n r (N * N)))ˣ),
      (repM (topM l n r (N * N)) y)⁻¹ * s * repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹) ∈
        fixMu Ω (topMu l n r N) := by
    intro s y
    have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l n r (N * N)) (s * t) = cycM (topM l n r (N * N)) s * cycM (topM l n r (N * N)) t :=
      fun s t => (hcy (topM l n r (N * N)) s).2.1 t
    have hr := (hcy (topM l n r (N * N)) s).2.2.1
    refine (hcy (topM l n r (N * N)) _).2.2.2.1.2 ?_
    have h1 : y * cycM (topM l n r (N * N)) ((repM (topM l n r (N * N)) y)⁻¹ * s) = cycM (topM l n r (N * N)) s := by
      conv_lhs => rw [← hr y]
      rw [← hm, hr, mul_inv_cancel_left]
    rw [hm, hr, eq_inv_mul_of_mul_eq h1]
    simp [mul_comm, mul_left_comm]
  have hB := sBStab Ω ε X l N (2 * e - 1) hN
  obtain ⟨-, -, -, hsum, -, -, hgal, -⟩ := sApi Ω ε X l n
  let P : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hadd
  refine ⟨GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB), b, fun s y => ⟨?_, ?_⟩, hb, fun s y => ?_⟩
  · exact Submodule.sum_mem _ fun y' _ => (hB _ (hL _ (hfix s y')).1).1 _
  · have h1 := hsum _ (Finset.univ.filter fun y' => redM l n r (N * N) y' = y) _ _
      (fun y' _ => hgal (repM (topM l n r (N * N)) y') _ (((l : ℤ_[l]) ^ c₀) • _) (hL _ (hfix s y')).2)
    have h3 : (∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y) =
        ∑ y' ∈ Finset.univ.filter (fun y' => redM l n r (N * N) y' = y),
          shB X l (topM l n r (N * N)) (clsBmu X l n r N x c d (2 * e + 1) gm) s y' := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Y0, GlobalTheory.KA.push, shB, clsBmu_eq, h2, map_sum]
      exact Finset.sum_comm
    simp only [map_smul, ← Finset.smul_sum] at h1
    beta_reduce
    rw [h3]
    exact h1
  · have h4 : pr (GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y) = YfB X l pr W e ψ n r N bB s y := by
      refine (map_sum P _ _).trans (Finset.sum_congr rfl fun y' _ => ?_)
      exact heq _ _ (hL _ (hfix s y')).1
    rw [h4]
    exact hC s y
end

