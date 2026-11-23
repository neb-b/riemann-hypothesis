module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia.FrobConjIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.TraceHeckeCongruenceVanish
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsFrob
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsFrob : UpperTheory.V.Z.Kato.Nb.SEsFrob := by
  intro Ω _ _ _ l _ v B σ hq hql hB hF
  obtain ⟨hσ, hfr⟩ := hF
  have hmem : ∀ g : Gal(Ω/ℚ), g ∈ ValuationSubring.decompositionSubgroup ℚ B → ∀ y ∈ B, g y ∈ B :=
    fun g hg y hy => (B.subMulAction ℚ).smul_mem' ⟨g, hg⟩ hy
  refine ⟨⟨?_, fun y hy => ⟨hmem σ hσ y hy, hmem σ⁻¹ (inv_mem hσ) y hy,
    hfr y ((B.valuation_le_one_iff y).mpr hy)⟩⟩, ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    have h := (hB ((normV v : ℕ) : 𝓞 ℚ)).mpr ((UpperTheory.V.Z.Kato.Nb.mem_place_iff v _).mpr dvd_rfl)
    simpa using h
  · have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [UpperTheory.V.Z.Kato.Nb.mem_place_iff]
      intro hd
      exact hql ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd)
    exact cycZ_of_isFrob hl hB ⟨hσ, hfr⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.GalAct
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.GalAct

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem act_sl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (g h : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
    (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos) b

private theorem gam_le (N l : ℕ) : Gam N l ≤ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l :=
  inf_le_inf_right _ (CongruenceSubgroup.Gamma1_in_Gamma0 N)

private theorem conj_mem (N l : ℕ) (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gam N l)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) : δ * γ * δ⁻¹ ∈ Gam N l := by
  obtain ⟨a1, a2, a3⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 (Subgroup.mem_inf.1 hγ).1
  have a4 : ((δ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hδ).1
  refine GamComm.mul_inv_mem_Gam N l _ δ (mul_mem hδ (gam_le N l hγ)) hδ ?_ ?_
  · simp [en, Matrix.mul_apply, Fin.sum_univ_two, a1, a3]
  · simp [en, Matrix.mul_apply, Fin.sum_univ_two, a2, a4]

private theorem act_act_conj (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (γ δ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l ((δ * γ * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  rw [act_sl, act_sl, inv_mul_cancel_right]

private theorem galB_mem [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (hN : 0 < N)
    (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.B N l w) : X.galB l s b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  have hA := (kmap_A_stable ε X ε.injective ⟨φ, h2, h1⟩ l).2 s
  have himg : X.galB l s '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨StabGal.galB_mem_Pol X l w s hA c hc.1, fun γ hγ => StabGal.inv_galB X N l w hN s c hc γ hγ⟩
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.galB l s) hb)

private theorem act_mem [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (δ : SL(2, ℤ))
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  have hA := (kmap_A_stable ε X ε.injective ⟨φ, h2, h1⟩ l).1 (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))
  have himg : X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ hA c hc.1, fun γ hγ => ?_⟩
    rw [act_act_conj, hc.2 _ (conj_mem N l γ δ hγ hδ)]
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.act l _) hb)

private theorem eval_congr (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (a t : X.Fn l) (ht : PolMod X l w n t)
    (hat : CgF X l n a t) (u v : Fin 2 → ℤ_[l]) (huv : ∀ i, PadicInt.toZModPow n (u i) = PadicInt.toZModPow n (v i)) :
    AdicCompletion.eval (idl l) (X.Kl l) n (a u) = AdicCompletion.eval (idl l) (X.Kl l) n (a v) := by
  obtain ⟨c, -, hc⟩ := ht
  have e : ∀ x, AdicCompletion.eval (idl l) (X.Kl l) n (a x) = AdicCompletion.eval (idl l) (X.Kl l) n (t x) := fun x => by
    rw [← sub_eq_zero, ← map_sub]; exact hat x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, e, ← sub_eq_zero, ← map_sub, hc, hc, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← sub_smul, map_smul]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  simp [huv]

private theorem comm [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) (hN : 0 < N)
    (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : InvM X l N w n b) (δ : SL(2, ℤ))
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) :
    CgF X l n (X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b))
      (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b)) := by
  obtain ⟨⟨t, ht, hbt⟩, hinv, -⟩ := hb
  obtain ⟨hE, -, -, -, -, hact, hgal, -⟩ := sApi Ω ε X l n
  intro u
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
  have hrec := X.recip M f hM (fun γ hγ => hlev γ (GamComm.gamma_le_of_dvd hM0 hγ)) ζ hζ s i
    (by rw [zpow_natCast, hs]) g δ hc
  have h10' : (((i : ℤ) * en δ 1 0 : ℤ) : ZMod M) = en g 1 0 := by push_cast; exact h10
  have hg0 : ∀ K : ℕ, K ∣ M → δ ∈ CongruenceSubgroup.Gamma0 K → g ∈ CongruenceSubgroup.Gamma0 K := fun K hK h => by
    have a : (en δ 1 0 : ZMod K) = 0 := CongruenceSubgroup.Gamma0_mem.1 h
    refine CongruenceSubgroup.Gamma0_mem.2 ((GamComm.intCast_eq_of_dvd hK h10').symm.trans ?_)
    rw [Int.cast_mul, a, mul_zero]
  have hgam : g * δ⁻¹ ∈ Gam N l :=
    GamComm.mul_inv_mem_Gam N l g δ
      (Subgroup.mem_inf.2 ⟨hg0 N hMN (Subgroup.mem_inf.1 hδ).1, hg0 l hMl (Subgroup.mem_inf.1 hδ).2⟩) hδ
      (GamComm.intCast_eq_of_dvd hMN h00) (GamComm.intCast_eq_of_dvd hMN h11)
  have hdg : CgF X l n (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b) := by
    have h := hact (δ : Matrix (Fin 2) (Fin 2) ℤ) _ _ (hinv _ hgam)
    rw [act_sl, inv_mul_cancel_right] at h
    exact hE.symm h
  have h1 := hgal s _ _ hdg u
  rw [map_sub, sub_eq_zero] at h1 ⊢
  rw [h1]
  have hpol := eval_congr X l w n b t ht hbt _ _
    (StabGal.twist_congr l n M hMn δ g i (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) hc
      (by simpa only [Int.cast_natCast] using hχ) u)
  have hL := hF (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hF (X.gal s) _ _ hf.symm)
  have hR := hF (X.gal s) _ _ (hF (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hpol.symm.trans hf.symm))
  refine hR.trans (Eq.trans ?_ hL.symm)
  congr 1
  apply Units.ext
  change X.gal s (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ)) f) = X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ)) (X.gal s f)
  rw [StabGal.toGQ_SL, StabGal.toGQ_SL, hrec]

private theorem polMod_galB [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ)
    (s : Ω ≃ₐ[ℚ] Ω) (t : X.Fn l) (ht : PolMod X l w n t) : PolMod X l w n (X.galB l s t) := by
  obtain ⟨c, hcU, hc⟩ := ht
  obtain ⟨-, -, -, -, hmap, -, hpow⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, -, hgU, hU, -⟩ := sSlD Ω ε X 1 one_pos
  refine ⟨fun i => ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i),
    fun i => ?_, fun u => ?_⟩
  · obtain ⟨f, hf, hr⟩ := hcU i
    obtain ⟨j, hj⟩ := hpow _ ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) _ (hmap (X.gal s) f _ hr)
    refine ⟨_, ?_, hj⟩
    have h0 : Units.map (X.gal s : X.K →* X.K) f ∈ X.Un (l ^ n) := hgU _ s f hf
    clear hj
    induction j with
    | zero => rw [pow_zero]; exact (hU _).1
    | succ k ih => rw [pow_succ]; exact ((hU _).2 _ ih _ h0).1
  · show X.kmap l (X.gal s) (t ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
    rw [hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

end UpperTheory.V.Z.Kato.Nb.GalAct

open UpperTheory.V.Z.Kato.Nb.GalAct in
theorem UpperTheory.V.Z.Kato.Nb.sGalAct :
    UpperTheory.V.Z.Kato.Nb.SGalAct := by
  intro Ω _ _ _ ε X l _ N w n hN s a ha
  have hcomm := comm X l N w n hN s a ha
  obtain ⟨⟨t, ht, hat⟩, hinv, b, hb, hba⟩ := ha
  obtain ⟨hE, -, -, -, -, hact, hgal, -⟩ := sApi Ω ε X l n
  have hba' : CgF X l n b (((l : ℤ_[l]) ^ cL X l N w) • a) := hba
  refine ⟨⟨⟨_, polMod_galB X l w n s t ht, hgal s _ _ hat⟩, fun γ hγ => ?_, X.galB l s b, galB_mem X l N w hN s b hb, ?_⟩,
    fun δ hδ => ⟨⟨⟨_, (sInvApi Ω ε X l N w n).2.2.2.2.2.2.2 _ t
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos) ht, hact _ _ _ hat⟩, fun γ hγ => ?_,
      X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b, act_mem X l N w δ hδ b hb, ?_⟩, hcomm δ hδ⟩⟩
  · exact hE.trans (hE.symm (hcomm γ (gam_le N l hγ))) (hgal s _ _ (hinv γ hγ))
  · have h := hgal s _ _ hba'
    rw [map_smul] at h
    exact h
  · rw [act_act_conj]
    exact hact _ _ _ (hinv _ (conj_mem N l γ δ hγ hδ))
  · have h := hact (δ : Matrix (Fin 2) (Fin 2) ℤ) _ _ hba'
    rw [map_smul] at h
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.HeckeInv
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem hi_perm (N l p : ℕ) (hl : l.Prime) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    ∃ π : Equiv.Perm (Fin (p + 1)), ∀ i, ∃ γ' ∈ Gam N l,
      GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) * GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i) := by
  have hpl : ¬ p ∣ N * l := by
    intro h
    have := Nat.Coprime.coprime_dvd_right h (by rw [mul_comm]; exact hc)
    exact hp.one_lt.ne' ((Nat.coprime_self p).1 this)
  have hpN : p.Coprime N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N l) hc
  have hpNl : p.Coprime (N * l) := by rw [mul_comm]; exact hc
  have hD := Betti.isDiam_sgD (N := N) (l := l) (d := p) hN.ne' hl.ne_zero hpN
  have hD' := Betti.isDiam_sgD (N := N * l) (l := l) (d := p) (Nat.mul_ne_zero hN.ne' hl.ne_zero) hl.ne_zero hpNl
  set σ := sgD N l p with hσ
  set σ' := sgD (N * l) l p with hσ'
  have hdia : GlobalTheory.Hk.IsDia N l p σ' := by
    refine ⟨CongruenceSubgroup.Gamma0_mem.1 hD'.1.1, ?_⟩
    have h2 := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hD'.2
    simpa [GlobalTheory.KZ.en] using h2
  have hδ : σ * σ'⁻¹ ∈ Gam N l := by
    refine ⟨?_, Subgroup.mul_mem _ hD.1.2 (Subgroup.inv_mem _ hD'.1.2)⟩
    have h0 := CongruenceSubgroup.Gamma0_mem.1 hD.1.1
    have h1 := hD.2
    have h0' : (((σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := by
      have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) (CongruenceSubgroup.Gamma0_mem.1 hD'.1.1)
      simpa using this
    have h1' : (((σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = p := by
      have h2 := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hD'.2
      simpa [GlobalTheory.KZ.en] using h2
    simp only [GlobalTheory.KZ.en] at h1
    have hdet := σ.det_coe
    have hdet' := σ'.det_coe
    rw [Matrix.det_fin_two] at hdet hdet'
    have e1 := congrArg (Int.cast : ℤ → ZMod N) hdet
    have e2 := congrArg (Int.cast : ℤ → ZMod N) hdet'
    push_cast at e1 e2
    rw [h0, h1] at e1
    rw [h0', h1'] at e2
    show σ * σ'⁻¹ ∈ CongruenceSubgroup.Gamma1 N
    rw [CongruenceSubgroup.Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast
    rw [h0, h1, h0', h1']
    refine ⟨?_, ?_, ?_⟩
    all_goals first | linear_combination e1 | linear_combination e2 | ring
  obtain ⟨π, hπ⟩ := GlobalTheory.HkInv.perm N l p σ' γ hp hpl hdia hγ
  let D : Fin (p + 1) → SL(2, ℤ) := fun i => if (i : ℕ) < p then 1 else σ * σ'⁻¹
  have hDm : ∀ i, D i ∈ Gam N l := by
    intro i
    simp only [D]
    split_ifs
    · exact one_mem _
    · exact hδ
  have hT : ∀ i, GlobalTheory.HeckeFamilyMatrices.tqFam p σ i = (D i : Matrix (Fin 2) (Fin 2) ℤ) * GlobalTheory.HeckeFamilyMatrices.tqFam p σ' i := by
    intro i
    simp only [GlobalTheory.HeckeFamilyMatrices.tqFam, D]
    split_ifs
    · simp
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((σ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ),
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  refine ⟨π, fun i => ?_⟩
  obtain ⟨γ', hγ', he⟩ := hπ i
  refine ⟨D i * γ' * (D (π i))⁻¹, mul_mem (mul_mem (hDm i) hγ') (inv_mem (hDm _)), ?_⟩
  rw [hT i, hT (π i), Matrix.mul_assoc]
  erw [he]
  rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_assoc (D i * γ'), inv_mul_cancel, mul_one]

private theorem hi_det (p : ℕ) (hp : 0 < p) (σ : SL(2, ℤ)) (i : Fin (p + 1)) : 0 < (GlobalTheory.HeckeFamilyMatrices.tqFam p σ i).det := by
  unfold GlobalTheory.HeckeFamilyMatrices.tqFam
  split_ifs
  · simp [Matrix.det_fin_two]
    exact_mod_cast hp
  · rw [Matrix.det_mul, GlobalTheory.HeckeFamilyMatrices.mat, σ.det_coe, one_mul]
    simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two]
    exact_mod_cast hp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

private theorem hi_sum (N p : ℕ) (a : X.Fn l) :
    X.heckeT N l p a = ∑ i : Fin (p + 1), X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) a := by
  rw [Fin.sum_univ_castSucc]
  simp only [GlobalTheory.KZ.Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun j => (X.act l !![1, (j : ℤ); 0, (p : ℤ)]) a)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [GlobalTheory.HeckeFamilyMatrices.tqFam]
  · simp [GlobalTheory.HeckeFamilyMatrices.tqFam, GlobalTheory.HeckeFamilyMatrices.dg]

private theorem hi_act (N p : ℕ) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    ∃ (π : Equiv.Perm (Fin (p + 1))) (g : Fin (p + 1) → SL(2, ℤ)), (∀ i, g i ∈ Gam N l) ∧ ∀ a : X.Fn l,
      X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l p a) =
        ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) (X.act l (g i : Matrix (Fin 2) (Fin 2) ℤ) a) := by
  obtain ⟨π, hπ⟩ := hi_perm N l p (Fact.out) hN hp hc γ hγ
  choose g hg he using hπ
  refine ⟨π, g, hg, fun a => ?_⟩
  have hd1 : ∀ δ : SL(2, ℤ), 0 < (δ : Matrix (Fin 2) (Fin 2) ℤ).det := fun δ => by rw [δ.det_coe]; exact one_pos
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hi_sum X l N p a, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hi_det p hp.pos _ i) (hd1 γ), GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hd1 (g i)) (hi_det p hp.pos _ (π i)), he i]

private theorem hi_pol_sum (w : ℕ) {ι : Type} (S : Finset ι) (t : ι → X.Fn l) (h : ∀ i, t i ∈ X.Pol l w) :
    ∑ i ∈ S, t i ∈ X.Pol l w := by
  choose c hcA hcu using h
  refine ⟨fun k => ∑ i ∈ S, c i k, fun k => Submodule.sum_mem _ fun i _ => hcA i k, fun u => ?_⟩
  simp only [Finset.sum_apply, hcu, Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem hi_rep_sum (n : ℕ) {ι : Type} (S : Finset ι) (c : ι → X.Khat l)
    (h : ∀ i, ∃ f ∈ X.Un (l ^ n), UpperTheory.Kd.K4.Rep X l n f (c i)) : ∃ f ∈ X.Un (l ^ n), UpperTheory.Kd.K4.Rep X l n f (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun W _ => ⟨1, by simp⟩, ?_⟩
    simp [UpperTheory.Kd.K4.Rep, GlobalTheory.KZ.Tower.cls]
  | insert i S hi ih =>
    obtain ⟨f, hf, hr⟩ := ih
    obtain ⟨f', hf', hr'⟩ := h i
    refine ⟨f' * f, fun W hW => ?_, ?_⟩
    · obtain ⟨g, hg⟩ := hf W hW
      obtain ⟨g', hg'⟩ := hf' W hW
      refine ⟨g' * g, ?_⟩
      have : ((f' * f : X.Kˣ) : X.K) / ((g' * g : X.Kˣ) : X.K) ^ (l ^ n) = ((f' : X.K) / (g' : X.K) ^ (l ^ n)) * ((f : X.K) / (g : X.K) ^ (l ^ n)) := by
        rw [Units.val_mul, Units.val_mul, mul_pow, div_mul_div_comm]
      rw [this, map_mul, hg, hg', one_mul]
    · unfold UpperTheory.Kd.K4.Rep at *
      rw [Finset.sum_insert hi, map_add (f := _), hr, hr']
      simp only [GlobalTheory.KZ.Tower.cls, ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

private theorem hi_polMod_sum (w n : ℕ) {ι : Type} (S : Finset ι) (t : ι → X.Fn l) (h : ∀ i, PolMod X l w n (t i)) :
    PolMod X l w n (∑ i ∈ S, t i) := by
  choose c hc hcu using h
  refine ⟨fun k => ∑ i ∈ S, c i k, fun k => hi_rep_sum X l n S (fun i => c i k) (fun i => hc i k), fun u => ?_⟩
  simp only [Finset.sum_apply, hcu, Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem hi_B [IsAlgClosure ℚ Ω] (N w p : ℕ) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (b : X.Fn l) (hb : b ∈ X.B N l w) : X.heckeT N l p b ∈ X.B N l w := by
  have hA := (GlobalTheory.KZ.kmap_A_stable ε X ε.injective (by obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩) l).1
  have key : ∀ x ∈ X.BSet N l w, X.heckeT N l p x ∈ X.BSet N l w := by
    rintro x ⟨hxP, hxI⟩
    refine ⟨?_, fun γ hγ => ?_⟩
    · rw [hi_sum X l N p x]
      exact hi_pol_sum X l w Finset.univ _ (fun i => GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ (fun a ha => hA _ a ha) x hxP)
    · obtain ⟨π, g, hg, he⟩ := hi_act X l N p hN hp hc γ hγ
      rw [he x, hi_sum X l N p x]
      calc _ = ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) x :=
            Finset.sum_congr rfl fun i _ => by rw [hxI _ (hg i)]
        _ = _ := Equiv.sum_comp π (fun i => X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) x)
  have hle : X.B N l w ≤ (X.B N l w).comap (X.heckeT N l p) :=
    Submodule.span_le.2 (fun x hx => Submodule.subset_span (key x hx))
  exact hle hb

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sHeckeInv :
    UpperTheory.V.Z.Kato.Nb.SHeckeInv := by
  intro Ω _ _ _ ε X l _ N w n p hN hp hc a ha
  obtain ⟨⟨t, hPt, hCt⟩, hinv, b, hbB, hbL⟩ := ha
  obtain ⟨hEq, -, -, hSum, -, hAct, -⟩ := sApi Ω ε X l n
  have hPolAct := (sInvApi Ω ε X l N w n).2.2.2.2.2.2.2
  have hH : ∀ x y, CgF X l n x y → CgF X l n (X.heckeT N l p x) (X.heckeT N l p y) := by
    intro x y hxy
    rw [hi_sum X l N p x, hi_sum X l N p y]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ hxy)
  refine ⟨⟨∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) t, ?_, ?_⟩, fun γ hγ => ?_, X.heckeT N l p b, hi_B X l N w p hN hp hc b hbB, fun u => ?_⟩
  · exact hi_polMod_sum X l w n Finset.univ _ (fun i => hPolAct _ t (hi_det p hp.pos _ i) hPt)
  · rw [hi_sum X l N p a]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ hCt)
  · obtain ⟨π, g, hg, he⟩ := hi_act X l N p hN hp hc γ hγ
    rw [he a]
    have h2 : X.heckeT N l p a = ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) a := by
      rw [hi_sum X l N p a]
      exact (Equiv.sum_comp π (fun i => X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) a)).symm
    rw [h2]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ (hinv (g i) (hg i)))
  · have hba : CgF X l n b ((l : ℤ_[l]) ^ cL X l N w • a) := fun u => by simpa using hbL u
    have := hH _ _ hba u
    simpa [map_smul] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LiftOk
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sLiftOk :
    UpperTheory.V.Z.Kato.Nb.SLiftOk := by
  intro Ω _ _ _ ε X l _ N w _ hl hc hw
  have h : ∃ c, LiftsWith X l N w c :=
    UpperTheory.Kd.K4.liftH ε X l N w hl (Nat.pos_of_ne_zero (NeZero.ne N)) hc hw
  exact Classical.epsilon_spec h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

attribute [local instance] algMdl

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem trM_add (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (a b : X.Khat l) :
    trM X l N M w g (a + b) = trM X l N M w g a + trM X l N M w g b := by
  unfold trM
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← map_add (f := _)]
  congr 1
  funext u
  simp [smul_add]

private theorem trM_sub (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (a b : X.Khat l) :
    trM X l N M w g (a - b) = trM X l N M w g a - trM X l N M w g b := by
  rw [eq_sub_iff_add_eq, ← trM_add, sub_add_cancel]

private theorem trM_cg [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M w : ℕ) [NeZero M] (g : SL(2, ℤ))
    (a b : X.Khat l) (h : AdicCompletion.eval (idl l) (X.Kl l) n (a - b) = 0) :
    CgF X l n (trM X l N M w g a) (trM X l N M w g b) := by
  obtain ⟨-, -, -, hsum, -, hact, -⟩ := sApi Ω ε X l n
  refine hsum _ _ _ _ fun γ _ => hact _ _ _ fun u => ?_
  rw [← smul_sub, map_smul, h, smul_zero]

end

theorem UpperTheory.V.Z.Kato.Nb.sTopRel :
    UpperTheory.V.Z.Kato.Nb.STopRel := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW c d ws hws hLv x y hxy x' y' hx hy
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  obtain ⟨a, ha, hinv, hs⟩ := hws.top n N M₀ M hLv hN hM (hL.eq ▸ dvd_rfl) (hL.eq ▸ hL.dl.mul_left N) x y hxy x' y' hx hy
  obtain ⟨hI, hG⟩ := sTrM Ω ε X l n N M₀ M w g hL hW a ha fun γ hγ => by
    obtain ⟨k, hk⟩ := hinv γ hγ
    exact ⟨k, by simpa [slU] using congrArg Units.val hk⟩
  obtain ⟨h0, hadd, -⟩ := sInvApi Ω ε X l N w n
  obtain ⟨heq, hpm, -⟩ := sApi Ω ε X l n
  obtain ⟨hcls, hmul, -, hcg, -⟩ := sCls Ω ε X l n
  refine ⟨0 - trM X l N M w g (clsK X l n (a : X.K)), (hadd _ _ h0 hI).2, fun σ hσ => ?_⟩
  obtain ⟨h, hh⟩ := hs σ hσ
  have hW0 : wGen X M l n (slD X N (siegel X c x')) (slD X N (siegel X d y')) σ ≠ 0 :=
    fun e => TopW.topW_ne_zero _ (Subtype.ext e)
  have h1 := sXiOne Ω ε X l n N M₀ M w g hL x y hxy (ws n M₀ σ) ((hws.coc n M₀ hLv).eqv σ)
  have h2 := hcg _ _ _ _ (hcls (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (ws n M₀ σ x y)))
    (hmul _ _ _ _ (hcls (Units.mk0 _ hW0)) (hmul _ _ _ _ (hcls (galU X σ a)) (hcls a)).2).1
    ⟨h, Units.ext (by
      rw [Units.val_mul, Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      exact hh)⟩
  have h3 := trM_cg X l n N M w g _ _ h2
  rw [trM_add, trM_sub] at h3
  have h4 := heq.trans (heq.symm h3) h1
  have h5 := (hpm _ _ _ _ h4 (hpm _ _ _ _ (heq.symm (hG σ hσ)) (heq.refl (trM X l N M w g (clsK X l n (a : X.K))))).2).2
  convert h5 using 1
  · exact (add_sub_cancel_right _ _).symm
  · rw [map_sub, map_zero]; abel
end

