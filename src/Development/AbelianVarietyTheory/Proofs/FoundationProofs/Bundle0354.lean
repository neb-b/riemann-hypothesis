module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformNormCoeffPrimeLeOfNotDvdLevel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActCommGamma0CapGamma0LevelShimuraReciprocit
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GammaZeroComm

theorem act_eq_self_of_mem_B {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w) {h : SL(2, ℤ)} (hh : h ∈ Gam N l) :
    X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 h hh
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem eval_kmap_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ : X.K ≃+* X.K) (n : ℕ) {x y : X.Khat l} (h : x - y ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine Submodule.smul_induction_on h (fun r hr m _ => ?_) (fun a b ha hb => ?_)
  · rw [map_smul, map_smul]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ m))
    rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add (f := _), map_add (f := _), ha, hb, add_zero]

theorem exists_twist (M : ℕ) (e e' : ℤ) (he : (e : ZMod M) * e' = 1) (γ : SL(2, ℤ)) :
    ∃ γ₁ : SL(2, ℤ), (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1 := by
  have hdet : (en γ 0 0 : ZMod M) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    have h2 := congrArg (Int.cast : ℤ → ZMod M) this
    push_cast at h2
    exact h2
  obtain ⟨γ₁, hγ₁⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M
    ⟨!![(en γ 0 0 : ZMod M), e' * en γ 0 1; e * en γ 1 0, en γ 1 1], by
      rw [Matrix.det_fin_two_of]; linear_combination hdet - (en γ 0 1 : ZMod M) * en γ 1 0 * he⟩
  have hent : ∀ i j, (en γ₁ i j : ZMod M) =
      (!![(en γ 0 0 : ZMod M), e' * en γ 0 1; e * en γ 1 0, en γ 1 1] : Matrix (Fin 2) (Fin 2) (ZMod M)) i j :=
    fun i j => congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod M) => g.1 i j) hγ₁
  refine ⟨γ₁, ?_, ?_, ?_, ?_⟩
  · rw [hent]; rfl
  · rw [hent]
    show _ = (e : ZMod M) * (e' * en γ 0 1)
    rw [← mul_assoc, he, one_mul]
  · rw [hent]; rfl
  · rw [hent]; rfl

theorem cong_of_dvd {M K : ℕ} (hK : K ∣ M) {e : ℤ} {γ γ₁ : SL(2, ℤ)}
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) :
    (en γ 0 0 : ZMod K) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod K) = e * en γ₁ 0 1 ∧
      (e : ZMod K) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod K) = en γ₁ 1 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := h
  have e00 := congrArg (ZMod.castHom hK (ZMod K)) h00
  have e01 := congrArg (ZMod.castHom hK (ZMod K)) h01
  have e10 := congrArg (ZMod.castHom hK (ZMod K)) h10
  have e11 := congrArg (ZMod.castHom hK (ZMod K)) h11
  simp only [map_mul, map_intCast] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

theorem twist_mul_inv_mem {N l M : ℕ} (hN : N ∣ M) (hl : l ∣ M) {e : ℤ} {γ γ₁ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) :
    γ₁ * γ⁻¹ ∈ Gam N l := by
  obtain ⟨a00, -, a10, a11⟩ := cong_of_dvd hN h
  obtain ⟨-, -, b10, -⟩ := cong_of_dvd hl h
  have cN : (en γ 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ.1
  have cl : (en γ 1 0 : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ.2
  have hdet : (en γ 0 0 : ZMod N) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    have h2 := congrArg (Int.cast : ℤ → ZMod N) this
    push_cast at h2
    exact h2
  have m00 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 0 0 = en γ₁ 0 0 * en γ 1 1 - en γ₁ 0 1 * en γ 1 0 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have m10 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 1 0 = en γ₁ 1 0 * en γ 1 1 - en γ₁ 1 1 * en γ 1 0 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have m11 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 1 1 = en γ₁ 1 1 * en γ 0 0 - en γ₁ 1 0 * en γ 0 1 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  rw [cN] at a10 hdet
  rw [cl] at b10
  refine ⟨(CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, CongruenceSubgroup.Gamma0_mem.2 ?_⟩
  · rw [m00]; push_cast; rw [← a00, cN]; linear_combination hdet
  · rw [m11]; push_cast; rw [← a11, ← a10]; linear_combination hdet
  · rw [m10]; push_cast; rw [← a10, cN]; ring
  · rw [m10]; push_cast; rw [← b10, cl]; ring

theorem twist_vec {l n M : ℕ} [Fact l.Prime] (hM : l ^ n ∣ M) {e : ℤ} {χ : ℤ_[l]} (hχ : (e : ℤ_[l]) - χ ∈ (idl l) ^ n)
    {γ γ₁ : SL(2, ℤ)}
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) (u : Fin 2 → ℤ_[l]) (i : Fin 2) :
    (![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1] :
      Fin 2 → ℤ_[l]) i - (mZl l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1]) i ∈ (idl l) ^ n := by
  obtain ⟨e00, e01, e10, e11⟩ := cong_of_dvd hM h
  rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hχ ⊢
  rw [map_intCast] at hχ
  simp only [en] at e00 e01 e10 e11
  rw [hχ] at e01 e10
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add (f := _), map_mul, map_intCast]
  · rw [← e00, e01]; ring
  · rw [← e10, ← e11]; ring

theorem galB_act_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b) = X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) := by
  intro Ω _ _ _ ε X _ _ N l w _ _ hN _ _ γ hγ s b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl : l.Prime := Fact.out
  funext u
  apply AdicCompletion.ext
  intro n
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  obtain ⟨M0, hM0, hlev⟩ := X.eval_kmap_levelRed l
    (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]) n
  obtain ⟨M, hM, hNM, hlM, hlnM, hM0M⟩ : ∃ M : ℕ, 0 < M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M ∧ M0 ∣ M :=
    ⟨N * l * l ^ n * M0, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hl.pos) (pow_pos hl.pos n)) hM0,
      ⟨l * l ^ n * M0, by ring⟩, ⟨N * l ^ n * M0, by ring⟩, ⟨N * l * M0, by ring⟩, ⟨N * l * l ^ n, by ring⟩⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  obtain ⟨e, he, heχ⟩ := exists_int_exponent_cyclotomic l s n M hM hlnM
  obtain ⟨e', he', -⟩ := exists_int_exponent_cyclotomic l s.symm n M hM hlnM
  have hee : (e : ZMod M) * e' = 1 := by
    have h1 : ζ ^ (e * e') = ζ := by
      rw [_root_.zpow_mul, ← he ζ hζ, ← map_zpow₀, ← he' ζ hζ, AlgEquiv.apply_symm_apply]
    have h0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
    have h2 : ζ ^ (e * e' - 1) = 1 := by rw [zpow_sub_one₀ h0, h1, mul_inv_cancel₀ h0]
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (e * e') M).2 ((hζ.zpow_eq_one_iff_dvd _).1 h2)
    push_cast at h3
    exact h3.symm
  obtain ⟨γ₁, hc⟩ := exists_twist M e e' hee γ
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hact : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) b := by
    conv_lhs => rw [← act_eq_self_of_mem_B X N l w hb (twist_mul_inv_mem hNM hlM hγ hc)]
    rw [Tower.act_act Ω ε X l _ _ (hpos _) (hpos _), ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  rw [hact]
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s)
      (X.kmap l (X.sl (toGQ (γ₁ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
        (b (mZl l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1])))) =
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.gal s)
        (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1])))
  rw [Tower.kmap_kmap, Tower.kmap_kmap, Betti.toGQ_sl, Betti.toGQ_sl,
    ← eval_kmap_congr X l _ n (X.B_sub_mem N l w b hb n _ _ (twist_vec hlnM heχ hc u))]
  refine hlev _ _ fun f hf => ?_
  exact X.recip M f hM (fun g hg => hf g (LevelRed.gamma_le_of_dvd hM0M hg)) ζ hζ s e (he ζ hζ) γ₁ γ hc

end GlobalTheory.KZ.GammaZeroComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionUpperTriangularHeckeReindexOnB
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GalUpper

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem map_eq_zpow_of_pow_eq_one (s : Ω ≃ₐ[ℚ] Ω) {L : ℕ} (hL : 0 < L) {e : ℤ}
    (he : ∀ ζ : Ω, IsPrimitiveRoot ζ L → s ζ = ζ ^ e) {ω : Ω} (hω : ω ^ L = 1) : s ω = ω ^ e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hω
  rw [map_pow, he ξ hξ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]

theorem eOm_mul_int (ε : Ω →+* ℂ) (x : ℚ) (k : ℤ) : eOm ε (x * k) = eOm ε x ^ k := by
  apply ε.injective
  rw [map_zpow₀, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_int_mul]
  congr 1; push_cast; ring

theorem gal_sl_upper (ε : Ω →+* ℂ) (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M q : ℕ) (hq : 0 < q) (e : ℤ)
    (he : ∀ ω : Ω, ω ^ (M * q) = 1 → s ω = ω ^ e) (j : ℤ) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    X.gal s (X.sl (toGQ !![1, j; 0, (q : ℤ)]) f) = X.sl (toGQ !![1, j * e; 0, (q : ℤ)]) (X.gal s f) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have key : ∀ (a : ℤ) (g : X.K) (t : ℚ), (X.exp (X.sl (toGQ !![1, a; 0, (q : ℤ)]) g)).coeff t =
      eOm ε (t * a) * (X.exp g).coeff (t * q) := by
    intro a g t
    have h := Tower.exp_upper_int ε X 1 a q one_pos (by exact_mod_cast hq) g (t * q)
    have e1 : t * q * ((1 : ℤ) : ℚ) / ((q : ℤ) : ℚ) = t := by push_cast; field_simp
    have e2 : t * q * (a : ℚ) / ((q : ℤ) : ℚ) = t * a := by push_cast; field_simp
    rwa [e1, e2] at h
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext t
  change (X.exp (X.gal s _)).coeff t = (X.exp (X.sl _ _)).coeff t
  rw [X.gal_exp, key, key, X.gal_exp, map_mul]
  by_cases h0 : (X.exp f).coeff (t * q) = 0
  · rw [h0, map_zero, mul_zero, mul_zero]
  · congr 1
    have h1 := GlobalTheory.KroneckerCongruence.eOm_level X M f hf _ h0
    have h2 : eOm ε (t * j) ^ (M * q) = 1 := by
      rw [← zpow_natCast, ← eOm_mul_int,
        show t * j * (((M * q : ℕ) : ℤ) : ℚ) = t * q * M * j by push_cast; ring, eOm_mul_int, h1, _root_.one_zpow]
    rw [he _ h2, ← eOm_mul_int]
    congr 1; push_cast; ring


omit [IsAlgClosure ℚ Ω] in
theorem eval_eq_zero_of_mem {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K)
    {x : X.Khat l} (hx : x ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [map_smul, map_smul]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y))
    rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]


omit [IsAlgClosure ℚ Ω] in
theorem act_upper_add {ε : Ω →+* ℂ} (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    (q : ℕ) (hq : 0 < q) (a t : ℤ) :
    X.act l !![1, a + t * q; 0, (q : ℤ)] b = X.act l !![1, a; 0, (q : ℤ)] b := by
  let γ : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ Gam N l := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]; simp [γ]
    · rw [CongruenceSubgroup.Gamma0_mem]; simp [γ]
  have hinv : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
    induction hb using Submodule.span_induction with
    | mem x hx => exact hx.2 γ hγ
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hm : (!![1, a + t * q; 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, a; 0, (q : ℤ)] := by
    simp [γ]
  rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [γ.det_coe]; exact one_pos)
    (by simp [Matrix.det_fin_two]; exact hq), hinv]

theorem galB_act_upper : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ) (e : ℤ), 0 < q → (∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e) → ∀ (j : ℤ), ∀ b ∈ X.B N l w, X.galB l s (X.act l !![1, j; 0, (q : ℤ)] b) = X.act l !![1, j * e; 0, (q : ℤ)] (X.galB l s b) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw s q e hq he j b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero q := ⟨hq.ne'⟩
  have hlp : l.Prime := Fact.out
  have hb' := _root_.GlobalTheory.KZ.StabGal.galB_mem_B ε X hε hj N l w hl hN hNl hw s b hb
  funext u
  apply AdicCompletion.ext
  intro n
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  set v : Fin 2 → ℤ_[l] := mZl l !![1, j; 0, (q : ℤ)] *ᵥ ![u 0, χ * u 1] with hv
  obtain ⟨M, hM, hred⟩ := _root_.GlobalTheory.KZ.Tower.eval_kmap_levelRed X l (b v) n
  have hL : 0 < M * q * l ^ n := Nat.mul_pos (Nat.mul_pos hM hq) (pow_pos hlp.pos n)
  obtain ⟨d, hd, hdχ⟩ := GlobalTheory.T.exists_int_exponent_congr_cyclotomicCharacter l s n (M * q * l ^ n) hL (dvd_mul_left _ _)
  have hd' : ∀ ω : Ω, ω ^ (M * q) = 1 → s ω = ω ^ d := fun ω hω =>
    map_eq_zpow_of_pow_eq_one s hL hd (by rw [pow_mul, hω, one_pow])
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hq.ne'
  have hde : (q : ℤ) ∣ d - e := by
    rw [← hξ.zpow_eq_one_iff_dvd, zpow_sub₀ hξ0, ← he ξ hξ,
      ← hd' ξ (by rw [mul_comm, pow_mul, hξ.pow_eq_one, one_pow])]
    exact div_self ((map_ne_zero s).2 hξ0)
  obtain ⟨t, ht⟩ := hde
  have hjd : j * d = j * e + (j * t) * q := by linear_combination j * ht
  rw [← act_upper_add X hb' q hq (j * e) (j * t), ← hjd]
  set v' : Fin 2 → ℤ_[l] := mZl l !![1, j * d; 0, (q : ℤ)] *ᵥ u with hv'
  change AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.gal s) (X.kmap l (X.sl (toGQ !![1, j; 0, (q : ℤ)])).toRingEquiv (b v))) =
    AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ !![1, j * d; 0, (q : ℤ)])).toRingEquiv (X.kmap l (X.gal s) (b ![v' 0, χ * v' 1])))
  rw [Tower.kmap_kmap, Tower.kmap_kmap,
    hred _ ((X.gal s).trans (X.sl (toGQ !![1, j * d; 0, (q : ℤ)])).toRingEquiv)
      (fun f hf => gal_sl_upper ε X s M q hq d hd' j f hf), ← sub_eq_zero, ← map_sub, ← map_sub]
  apply eval_eq_zero_of_mem
  refine GlobalTheory.T.bettiFunction_sub_mem_of_columns_congr X N l w b hb n _ _ ?_
  intro i
  fin_cases i
  · have h := Ideal.mul_mem_left _ (-((j : ℤ_[l]) * u 1)) hdχ
    convert h using 1
    simp [hv, hv', mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · convert Ideal.zero_mem _
    simp [hv, hv', mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

end GlobalTheory.KZ.GalUpper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeAction
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.GamComm

theorem intCast_eq_of_dvd {K M : ℕ} (hK : K ∣ M) {x y : ℤ} (h : (x : ZMod M) = y) : (x : ZMod K) = y := by
  simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h

theorem gamma_le_of_dvd {K M : ℕ} (hK : K ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  refine CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩
  · simpa using intCast_eq_of_dvd hK (y := 1) (by simpa using h1)
  · simpa using intCast_eq_of_dvd hK (y := 0) (by simpa using h2)
  · simpa using intCast_eq_of_dvd hK (y := 0) (by simpa using h3)
  · simpa using intCast_eq_of_dvd hK (y := 1) (by simpa using h4)

theorem mul_inv_mem_Gam (N l : ℕ) (g δ : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (h00 : (en δ 0 0 : ZMod N) = en g 0 0) (h11 : (en δ 1 1 : ZMod N) = en g 1 1) : g * δ⁻¹ ∈ Gam N l := by
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (Subgroup.mem_inf.1 hg).2 (inv_mem (Subgroup.mem_inf.1 hδ).2)⟩
  have a1 : (en g 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hg).1
  have a2 : (en δ 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hδ).1
  have hdet : (en δ 0 0 : ZMod N) * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod N) h
    simpa [en] using this
  have e00 : en (g * δ⁻¹) 0 0 = en g 0 0 * en δ 1 1 - en g 0 1 * en δ 1 0 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e10 : en (g * δ⁻¹) 1 0 = en g 1 0 * en δ 1 1 - en g 1 1 * en δ 1 0 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e11 : en (g * δ⁻¹) 1 1 = en g 1 1 * en δ 0 0 - en g 1 0 * en δ 0 1 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩
  · change ((en (g * δ⁻¹) 0 0 : ℤ) : ZMod N) = 1
    rw [e00]; push_cast
    linear_combination hdet - (en δ 1 1 : ZMod N) * h00 + ((en δ 0 1 : ZMod N) - en g 0 1) * a2
  · change ((en (g * δ⁻¹) 1 1 : ℤ) : ZMod N) = 1
    rw [e11]; push_cast
    linear_combination hdet - (en δ 0 0 : ZMod N) * h11 + (en δ 0 1 : ZMod N) * a2 - (en δ 0 1 : ZMod N) * a1
  · change ((en (g * δ⁻¹) 1 0 : ℤ) : ZMod N) = 0
    rw [e10]; push_cast
    rw [a1, a2]; ring

theorem act_galB_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ _ ε X N l w _ hN b hb δ hδ s
  funext u
  refine AdicCompletion.ext fun n => ?_
  have hcls := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hF := hcls.2.2.2.2.2.1
  obtain ⟨f, hf⟩ := hcls.1 (AdicCompletion.eval (idl l) (X.Kl l) n
    (b ![(mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))
  obtain ⟨M₀, hM₀, hlev⟩ := X.level (f : X.K)
  have hlp : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨M, hM, hM0, hMN, hMl, hMn⟩ : ∃ M : ℕ, 0 < M ∧ M₀ ∣ M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M :=
    ⟨M₀ * N * l * l ^ n, by positivity, ⟨N * l * l ^ n, by ring⟩, ⟨M₀ * l * l ^ n, by ring⟩,
      ⟨M₀ * N * l ^ n, by ring⟩, ⟨M₀ * N * l, by ring⟩⟩
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hMn s
  obtain ⟨g, h00, h01, h10, h11⟩ := GlobalTheory.exists_sl2_conj_diag_zmod M i hi δ
  have hc : (en δ 0 0 : ZMod M) = en g 0 0 ∧ (en δ 0 1 : ZMod M) = ((i : ℤ) : ZMod M) * en g 0 1 ∧
      ((i : ℤ) : ZMod M) * en δ 1 0 = en g 1 0 ∧ (en δ 1 1 : ZMod M) = en g 1 1 :=
    ⟨h00, by simpa only [Int.cast_natCast] using h01, by simpa only [Int.cast_natCast] using h10, h11⟩
  have hrec := X.recip M f hM (fun γ hγ => hlev γ (gamma_le_of_dvd hM0 hγ)) ζ hζ s i
    (by rw [zpow_natCast, hs]) g δ hc
  have h10' : (((i : ℤ) * en δ 1 0 : ℤ) : ZMod M) = en g 1 0 := by push_cast; exact h10
  have hg0 : ∀ K : ℕ, K ∣ M → δ ∈ CongruenceSubgroup.Gamma0 K → g ∈ CongruenceSubgroup.Gamma0 K := fun K hK h => by
    have a : (en δ 1 0 : ZMod K) = 0 := CongruenceSubgroup.Gamma0_mem.1 h
    refine CongruenceSubgroup.Gamma0_mem.2 ((intCast_eq_of_dvd hK h10').symm.trans ?_)
    rw [Int.cast_mul, a, mul_zero]
  have hgam : g * δ⁻¹ ∈ Gam N l :=
    mul_inv_mem_Gam N l g δ
      (Subgroup.mem_inf.2 ⟨hg0 N hMN (Subgroup.mem_inf.1 hδ).1, hg0 l hMl (Subgroup.mem_inf.1 hδ).2⟩) hδ
      (intCast_eq_of_dvd hMN h00) (intCast_eq_of_dvd hMN h11)
  have hact : X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b := by
    have e : (g : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [e, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos), hb.2 _ hgam]
  have hpol := StabGal.eval_Pol_congr X l w b hb.1 n _ _
    (StabGal.twist_congr l n M hMn δ g i (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) hc
      (by simpa only [Int.cast_natCast] using hχ) u)
  rw [hact]
  have hL := hF (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hF (X.gal s) _ _ hf.symm)
  have hR := hF (X.gal s) _ _ (hF (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hpol.symm.trans hf.symm))
  refine hL.trans (Eq.trans ?_ hR.symm)
  congr 1
  apply Units.ext
  change X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ)) (X.gal s f) = X.gal s (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ)) f)
  rw [StabGal.toGQ_SL, StabGal.toGQ_SL, hrec]

end GlobalTheory.KZ.GamComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualUpperTriangularDecomposiStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeBoundMain
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices

theorem hecke_bound_lt (k q : ℕ) (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) < 1 + (q : ℝ) ^ (k - 1) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set x : ℝ := (q : ℝ) ^ ((k : ℝ) / 2) with hx
  set y : ℝ := (q : ℝ) ^ ((k : ℝ) / 2 - 1) with hy
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : 1 < x := Real.one_lt_rpow hq1 (by linarith)
  have hy1 : 1 < y := Real.one_lt_rpow hq1 (by linarith)
  have hxy : x * y = (q : ℝ) ^ (k - 1) := by
    rw [hx, hy, ← Real.rpow_add hq0, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  nlinarith [mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1)]

theorem hecke_bound_ne (k : ℕ) (g : UpperTheory.V.Af.Newform k) (q : ℕ) (hk : 3 ≤ k) (hq : q.Prime)
    (hqM : ¬ q ∣ g.M) :
    ‖g.a q‖ ≤ (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) ∧
      g.a q ≠ 1 + (q : ℂ) ^ (k - 1) := by
  have hb := GlobalTheory.HeckeBd.norm_a_le k g q hq hqM
  refine ⟨hb, fun h => ?_⟩
  have hlt := hecke_bound_lt k q hk hq.two_le
  have hn : ‖(1 : ℂ) + (q : ℂ) ^ (k - 1)‖ = 1 + (q : ℝ) ^ (k - 1) := by
    have : (1 : ℂ) + (q : ℂ) ^ (k - 1) = (((1 : ℝ) + (q : ℝ) ^ (k - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h, hn] at hb
  linarith

theorem hecke_bound_main : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (q : ℕ), 3 ≤ k → q.Prime → ¬ q ∣ g.M →
    ‖g.a q‖ ≤ (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) ∧ g.a q ≠ 1 + (q : ℂ) ^ (k - 1) :=
  fun k g q hk hq hqM => hecke_bound_ne k g q hk hq hqM

end GlobalTheory.HeckeFamilyMatrices
end
end

