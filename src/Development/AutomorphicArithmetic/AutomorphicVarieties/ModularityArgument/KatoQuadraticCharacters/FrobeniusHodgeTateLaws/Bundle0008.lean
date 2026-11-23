module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0024

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AdmissibleFunctionalOfProjection
section
open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

private theorem norm_l_lt (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends (p := l) ((l : ℕ) : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

private theorem sq_ne {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (α c : ℂ) (hα : ‖ι.symm α‖ = 1) (hc : c = 1 ∨ c = -1)
    (n : ℕ) (hn : n ≠ 0) : α ^ 2 ≠ c * (l : ℂ) ^ n := by
  intro h
  have h1 := congrArg (fun z => ‖ι.symm z‖) h
  have h2 : ‖ι.symm c‖ = 1 := by rcases hc with rfl | rfl <;> simp
  simp only [map_pow, map_mul, map_natCast, norm_pow, norm_mul, hα, h2, one_pow, one_mul] at h1
  have h3 := pow_lt_one₀ (norm_nonneg _) (norm_l_lt l) hn
  rw [← h1] at h3
  exact lt_irrefl _ h3

private theorem alg_eq {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) :
    algebraMap ℤ_[l] (Qbar l) z = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) :=
  IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) z

private theorem norm_alg {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) z‖ = ‖z‖ := by
  rw [alg_eq]
  exact PadicAlgCl.norm_extends (p := l) (z : ℚ_[l])

private theorem tmul_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) : ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) ∈ X.VB N l w (Qbar l) :=
  ⟨(1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : X.B N l w), by simp⟩

theorem UpperTheory.V.Z.Kato.Joint.admissibleFunctional_of_projection :
    UpperTheory.V.Z.Kato.Joint.AdmOf2 := by
  classical
  intro hAdm hK3 hRho _ hFrob hUnif hForm hFin hUb hLin hOp hStab hThP hEig hQuad hInt
  intro l _ Ω _ _ _ ι e S A W g hNf χg ψ₀ hlM hal hK hAtt hIne hψ j hj ε X N _ χ α B cc c₀ hN hMN hlN hχ hα hαe hE
  have hp : l.Prime := Fact.out
  have he := hNf.e_pos
  have hl2 := hNf.l_odd
  obtain ⟨ρ, hρ, hρc, hρ10, hρ11, F, hρ00⟩ := hRho l Ω ι e S A W g ψ₀ hNf ⟨hlM, hal, χg, hK, hAtt, hIne⟩ ⟨χg, hK, hIne, hψ⟩
  have hρ' : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = (eps l s ^ e * (χg s : Qbar l)⁻¹) • mat W s := by
    intro s
    rw [hρ, hψ s, rhoK, thK, mul_inv, inv_inv]
    rfl
  obtain ⟨⟨S0, hS0⟩, hirr⟩ := hFrob l Ω ι e S A W g χg hNf hK hAtt ρ hρ'
  have hq := hQuad l Ω ι e S A W g χg hNf hK hlM hAtt
  have hcop : ∀ d : ℕ, d.Coprime N → d.Coprime g.M := fun d hd => Nat.Coprime.coprime_dvd_right hMN hd
  have hlcN : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hlN
  have hjl : (l : Ω) ∈ A.nonunits := (‹JEx› l Ω A hNf.atL).1
  have hjA : ∀ x ∈ A, ‖j x‖ ≤ 1 := fun x hx => (hj x).1 hx
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  let lamC : Letter → ℂ := fun T => match T with
    | Letter.T q => g.a q
    | Letter.U => α
    | Letter.D d => g.χ (d : ZMod g.M)
  have hcm : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := Units.continuous_val.comp hρc
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hw1 : 2 * e - 1 + 1 = 2 * e := by omega
  have hw2 : 2 * e - 1 + 2 = 2 * e + 1 := by omega
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have h3 := hK3 ε X ε.injective ⟨φ, hφ2, hφ1⟩ (2 * e + 1) g N l hl2 hMN hN hlcN.symm ⟨e, rfl⟩ (by omega) α
    (by rw [← hχ l hlcN]; exact hαe) (sq_ne ι α _ hα (hq l (hcop l hlcN)) _ (by omega))
    (sq_ne ι α _ hα (hq l (hcop l hlcN)) _ (by omega)) lamC (fun _ _ _ => rfl) rfl (fun _ _ => rfl) (E := Qbar l) norm_alg ι
  simp only [hw] at h3
  obtain ⟨m, π, σ, P, hP, hP1, -, hσ, hπg, hσg, hσT, hπT, hπσ, hPx⟩ := h3 ρ S0
    (hUnif l Ω _ hcm.matrix_trace) (hUnif l Ω _ hcm.matrix_det)
    (fun q hq hS s hs => by rw [hw1]; exact hS0 q hq hS s hs) hirr
  let χd : ℕ → ℤ_[l] := fun d => if g.χ (d : ZMod g.M) = 1 then 1 else -1
  have hχd : ∀ d : ℕ, d.Coprime N → ι.symm (g.χ (d : ZMod g.M)) = ((χd d : ℤ_[l]) : Qbar l) := by
    intro d hd
    by_cases h : g.χ (d : ZMod g.M) = 1
    · simp [χd, h]
    · have h' := (hq d (hcop d hd)).resolve_left h
      simp only [χd, if_neg h]
      rw [h']
      simp
  have hχd' : ∀ d : ℕ, d.Coprime N → ι ((χd d : ℤ_[l]) : Qbar l) = χ d := by
    intro d hd
    rw [← hχd d hd, RingEquiv.apply_symm_apply, hχ d hd]
  obtain ⟨lam₀, lam, c, hc, hf0, hf, hfix, hl0, hl⟩ := hFin hUb l ι (2 * e + 1) N B cc (fun d => ((χd d : ℤ_[l]) : Qbar l)) c₀ P hP
  have hev : ∃ k : ℕ, ∀ T, GlobalTheory.KZ.admitted N l T → ‖ι.symm (lamC T)‖ ≤ (l : ℝ) ^ k := by
    obtain ⟨k, hk⟩ := hInt l Ω ι e S A W g χg hNf hK hAtt
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
    refine ⟨k, ?_⟩
    rintro (q | _ | d) hT
    · exact hk q hT.1
    · exact hα.le.trans h1
    · rcases hq d (hcop d hT) with h | h <;> simpa [lamC, h] using h1
  have heig := hEig hLin hOp hStab hThP l Ω ε X A N (2 * e - 1) j χd (fun T => ι.symm (lamC T))
    ⟨hjl, hl2, hlN, hN, hodd, hjA⟩ hev P hP
    (fun T hT b hb => by
      have hb' := _root_.GlobalTheory.KZ.B_stable_op ε X ε.injective ⟨φ, hφ2, hφ1⟩ N l (2 * e - 1) hl2 hN hlcN.symm hodd T hT b hb
      rw [hPx _ (tmul_mem X N l _ _ hb'), hPx _ (tmul_mem X N l _ _ hb), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_smul, ← hπT i T hT _ (tmul_mem X N l _ _ hb)]
      rfl)
    lam₀ lam hf0 (by rw [hw2]; exact hl)
  obtain ⟨pr, a, cf, hcf, -, hadd, hsm, hint, hgal, hT, hD, hU, hlam⟩ :=
    hAdm ε X A N l e S W ψ₀ ι g j hNf he ⟨φ, hφ1, hφ2⟩ hjl hl2 hlN hN hjA (fun T => ι.symm (lamC T)) ρ F hρ hρ10 hρ11
      (by rw [hw1]; exact hρ00) (fun _ _ _ => rfl) χd hχd m π σ P hP hP1 hσ hπg hσg hσT hπT hπσ hPx c lam hf hfix heig
  refine ⟨pr, cf, χd, (((l : ℕ) : Qbar l) ^ a) • lam, ((l : ℕ) : Qbar l) ^ a, hc.trans hcf,
    pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero), hadd, hsm, hint, hgal,
    ⟨fun q => ((χd q : ℤ_[l]) : Qbar l), fun q hq hql b hb => ⟨hT q hq hql b hb,
      hD q ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hql (h.mul_left l)) b hb⟩⟩, hU, hχd',
    fun b hb d hd => hD d hd b hb, hlam, fun s hs => ?_⟩
  have hF := hForm l ι (2 * e + 1) N χ (fun q => g.a q) α B cc (fun d => ((χd d : ℤ_[l]) : Qbar l)) (fun T => ι.symm (lamC T))
    (by omega) hE hχd' (fun _ _ _ => ι.apply_symm_apply _) (ι.apply_symm_apply _) hχd P hP s hs
  rw [LinearMap.smul_apply, smul_eq_mul, hl, hl0, hF, hP1, map_one, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AqBdPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open UpperTheory.V.Z.Kato.Joint
open scoped Pointwise

private theorem aqBd_place {q : ℕ} (hq : q.Prime) : ∃ w : Pl, ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  have hn : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) = q := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hne : Ideal.span {((q : ℕ) : 𝓞 ℚ)} ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hn
    exact hq.one_lt.ne hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((q : ℕ) : 𝓞 ℚ) ∈ M := (Ideal.span_singleton_le_iff_mem M).1 hle
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hq.ne_zero (Nat.cast_eq_zero.1 hmem)

private theorem aqBd_frob (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {q : ℕ} (hq : q.Prime) :
    ∃ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s := by
  obtain ⟨w, hw⟩ := aqBd_place hq
  obtain ⟨V, hV⟩ := exists_isPlaceOver (F := ℚ) Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hV
  rw [GlobalTheory.RhoAdm.normV_ratPrime hq w hw] at hσ
  refine ⟨σ, V, ?_, fun x hx => ⟨?_, hσ.2 x ((V.valuation_le_one_iff x).2 hx)⟩⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    simpa using (hV _).2 hw
  · have h : σ • V = V := MulAction.mem_stabilizer_iff.1 hσ.1
    rw [← h]
    exact ValuationSubring.smul_mem_pointwise_smul σ x V hx

theorem UpperTheory.V.Z.Kato.Joint.aqBd :
    UpperTheory.V.Z.Kato.Joint.AqBd := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hχ hatt
  obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
  have hc := (Continuous.matrix_trace
    (Units.continuous_val.comp (GlobalTheory.RhoAdm.untw_cont e W χ hN.cont hχ))).norm
  haveI : CompactSpace (Ω ≃ₐ[ℚ] Ω) := inferInstance
  obtain ⟨C, hC⟩ := (isCompact_range hc).bddAbove
  obtain ⟨k, hk⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l (max C (∑ q ∈ S0, ‖ι.symm (g.a q)‖))
  refine ⟨k, fun q hq => le_trans ?_ hk⟩
  by_cases hqS : q ∈ S0
  · exact le_max_of_le_right
      (Finset.single_le_sum (f := fun q => ‖ι.symm (g.a q)‖) (fun _ _ => norm_nonneg _) hqS)
  · obtain ⟨s, hs⟩ := aqBd_frob Ω hq
    rw [← (hS0 q hq hqS s hs).1]
    exact le_max_of_le_left (hC ⟨s, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiFix
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers

namespace UpperTheory.V.Z.Kato.Joint

theorem chiFix : ChiFix := by
  intro l _ ι N χ χd hχ
  have hinj : ∀ x y : ℤ_[l], ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) =
      ι (algebraMap ℚ_[l] (Qbar l) (y : ℚ_[l])) → x = y := by
    intro x y h
    exact PadicInt.ext ((algebraMap ℚ_[l] (Qbar l)).injective (ι.injective h))
  have hF1 : ι (algebraMap ℚ_[l] (Qbar l) ((1 : ℤ_[l]) : ℚ_[l])) = 1 := by simp
  have hFm : ∀ x y : ℤ_[l], ι (algebraMap ℚ_[l] (Qbar l) ((x * y : ℤ_[l]) : ℚ_[l])) =
      ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) * ι (algebraMap ℚ_[l] (Qbar l) (y : ℚ_[l])) := by
    intro x y
    simp
  have hFp : ∀ (x : ℤ_[l]) (k : ℕ), ι (algebraMap ℚ_[l] (Qbar l) ((x ^ k : ℤ_[l]) : ℚ_[l])) =
      ι (algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) ^ k := by
    intro x k
    simp
  have hcop : ∀ a : ℕ, a.Coprime N ↔ (a % N).Coprime N := by
    intro a
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm a N, Nat.gcd_rec]
  refine ⟨fun d => if d.Coprime N then χd d else 0, ?_, ?_, ?_, ?_⟩
  · intro d hd
    dsimp only
    rw [if_pos hd]
  · intro d hd
    dsimp only
    rw [if_pos hd]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hd1 : d = 1 := Nat.coprime_zero_right d |>.1 hd
      subst hd1
      have h1 : χd 1 = 1 := hinj _ _ (by rw [hχ 1 hd, hF1]; simp)
      rw [h1]
      exact isUnit_one
    · have hk : (χd d) ^ Nat.totient N = 1 := by
        apply hinj
        rw [hFp, hχ d hd, hF1, ← map_pow, ← Nat.cast_pow,
          (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.pow_totient hd), Nat.cast_one, map_one]
      exact IsUnit.of_pow_eq_one hk (Nat.totient_pos.2 hN).ne'
  · intro a b
    dsimp only
    by_cases ha : a.Coprime N
    · by_cases hb : b.Coprime N
      · have hab : (a * b).Coprime N := Nat.Coprime.mul_left ha hb
        rw [if_pos hab, if_pos ha, if_pos hb]
        apply hinj
        rw [hFm, hχ _ hab, hχ _ ha, hχ _ hb, Nat.cast_mul, map_mul]
      · have hab : ¬ (a * b).Coprime N := fun h => hb (Nat.Coprime.coprime_mul_left h)
        rw [if_neg hab, if_neg hb, mul_zero]
    · have hab : ¬ (a * b).Coprime N := fun h => ha (Nat.Coprime.coprime_mul_right h)
      rw [if_neg hab, if_neg ha, zero_mul]
  · intro a b hab
    dsimp only
    have hiff : a.Coprime N ↔ b.Coprime N := by rw [hcop a, hcop b, hab]
    by_cases ha : a.Coprime N
    · have hb : b.Coprime N := hiff.1 ha
      rw [if_pos ha, if_pos hb]
      apply hinj
      rw [hχ _ ha, hχ _ hb, (ZMod.natCast_eq_natCast_iff' a b N).2 hab]
    · have hb : ¬ b.Coprime N := fun h => ha (hiff.2 h)
      rw [if_neg ha, if_neg hb]

end UpperTheory.V.Z.Kato.Joint

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmNormNat
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix

namespace UpperTheory.V.Z.Kato.Joint

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem sm_sys {W : R2 Ω l} {c : Coef l} {y : G ℚ Ω → Fin 2 → Qbar l} {S' : Finset Pl} (h : Sys W c y S')
    {a : Qbar l} (ha : a ∈ c.O) : Sys W c (fun s => a • y s) S' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, Submodule.smul_mem _ a h2, fun s i => c.O.mul_mem ha (h3 s i), fun w hw => ?_, fun n hn w hw hd ψ hk hs => ?_⟩
  · obtain ⟨B, hB, x, hx⟩ := h4 w hw
    refine ⟨B, hB, a • x, fun s hs => ?_⟩
    simp only [hx s hs, Matrix.mulVec_smul, smul_sub]
  · obtain ⟨Y, P, u, b, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := h5 n hn w hw hd ψ hk hs
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    refine ⟨fun s x => a • Y s x, P, u, a • b, ?_, fun s x i => c.O.mul_mem ha (k2 s x i), k3, k4,
      fun i => c.O.mul_mem ha (k5 i), fun s t x => ?_, fun s => ?_, k8, fun q hq hl => ?_⟩
    · exact k1.const_smul a
    · simp only [k6, Matrix.mulVec_smul, smul_add]
    · have := k7 s
      rw [finsum_eq_sum_of_fintype] at this ⊢
      rw [← Finset.smul_sum, this]
      simp only [Matrix.mulVec_smul, smul_add, smul_sub, smul_comm a P]
    · obtain ⟨B, hB, t, ht, ht'⟩ := k9 q hq hl
      refine ⟨B, hB, fun x => a • t x, fun x i => c.O.mul_mem ha (ht x i), fun s hs x => ?_⟩
      simp only [ht' s hs, Matrix.mulVec_smul, smul_sub]

private theorem sm_iw {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (h : IwSys2 c A ν Z) (d : ℕ) (hd : Nat.Coprime d l) :
    IwSys2 c A ν (smZ d hd Z) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun r => ⟨fun s x => ?_, fun s hs t ht x => ?_⟩, fun r s x => ?_⟩
  · exact c.O.sub_mem ((h2 r).1 _ _) (c.O.mul_mem (natCast_mem c.O d) ((h2 r).1 _ _))
  · unfold smZ
    rw [(h2 r).2 s hs t ht, (h2 r).2 s hs t ht, mul_right_comm x]
    ring
  · unfold smZ
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← h3 r s x, h3 r s (x * _)]
    congr 2
    have hu : Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom
        (ZMod.unitOfCoprime d (Nat.Coprime.pow_right (r + 1) hd)) = ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd) := by
      ext
      simp only [Units.coe_map, ZMod.coe_unitOfCoprime, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_natCast]
    symm
    refine Finset.sum_equiv (Equiv.mulRight (ZMod.unitOfCoprime d (Nat.Coprime.pow_right (r + 1) hd))) (fun i => ?_)
      (fun i _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight, map_mul, hu, mul_left_inj]

private theorem sm_norm_nat {a : ℕ} (h : Nat.Coprime a l) : ‖(a : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 h.symm

private theorem sm_eta {r n : ℕ} (hr : 1 ≤ r) (hn : n ≤ r) (e : ℕ) (ψ : ZMod l → Qbar l) (hψ : ∀ x, ‖ψ x‖ ≤ 1)
    (d : ℕ) (hd : Nat.Coprime d l) (hd1 : (d : ZMod l) = 1) (x : (ZMod (l ^ r))ˣ) :
    ‖((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x - (d : Qbar l) ^ e *
      ((((((x * ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ *
        chiK l ψ r (x * ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd)))‖ ≤ ‖(l : Qbar l) ^ n‖ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  unfold chiK
  set z := x * ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd) with hz
  have hmod : (z : ZMod (l ^ r)).val ≡ (x : ZMod (l ^ r)).val * d [MOD l ^ r] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hz, Units.val_mul,
      ZMod.coe_unitOfCoprime]
  have hl : l ∣ l ^ r := dvd_pow_self l (by omega)
  have ha := sm_norm_nat (Nat.Coprime.coprime_dvd_right hl (ZMod.val_coe_unit_coprime x))
  have hb := sm_norm_nat (Nat.Coprime.coprime_dvd_right hl (ZMod.val_coe_unit_coprime z))
  generalize (z : ZMod (l ^ r)).val = b at *
  generalize (x : ZMod (l ^ r)).val = a at *
  have hψe : ((b : ℕ) : ZMod l) = ((a : ℕ) : ZMod l) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 (hmod.of_dvd hl), Nat.cast_mul, hd1, mul_one]
  obtain ⟨k, hk⟩ := ((hmod.of_dvd (pow_dvd_pow l hn)).pow e).symm.dvd
  have hk' : (b : Qbar l) ^ e - ((a : Qbar l) * d) ^ e = (l : Qbar l) ^ n * k := by exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) hk
  have ha0 : (a : Qbar l) ≠ 0 := by rw [← norm_ne_zero_iff, ha]; exact one_ne_zero
  have hb0 : (b : Qbar l) ≠ 0 := by rw [← norm_ne_zero_iff, hb]; exact one_ne_zero
  have key : ((a : Qbar l) ^ e)⁻¹ * ψ a - (d : Qbar l) ^ e * (((b : Qbar l) ^ e)⁻¹ * ψ b) =
      (l : Qbar l) ^ n * (k * ψ a) * (((a : Qbar l) ^ e)⁻¹ * ((b : Qbar l) ^ e)⁻¹) := by
    rw [hψe, ← mul_assoc ((l : Qbar l) ^ n), ← hk', mul_pow]
    field_simp
  rw [key, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, norm_pow (a : Qbar l), norm_pow (b : Qbar l), ha, hb]
  simp only [one_pow, inv_one, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ k) (norm_nonneg _) (hψ _))

private theorem sm_sp {c : Coef l} {A : ValuationSubring Ω}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hZ : ∀ r s x, Z r s x ∈ c.O) (e : ℕ) (ψ : ZMod l → Qbar l)
    (hψ : ∀ x, ‖ψ x‖ ≤ 1) (d : ℕ) (hd : Nat.Coprime d l) (hd1 : (d : ZMod l) = 1) {y : G ℚ Ω → Fin 2 → Qbar l}
    (h : SpLink A e (chiK l ψ) Z y) :
    SpLink A e (chiK l ψ) (smZ d hd Z) fun s => (1 - (d : Qbar l) ^ (e + 1)) • y s := by
  intro n
  obtain ⟨r₀, hr₀⟩ := h n
  refine ⟨max r₀ (max n 1), fun r hr s hs hc => ?_⟩
  have h0 := hr₀ r (by omega) s hs hc
  have h1 := sm_eta (r := r) (n := n) (by omega) (by omega) e ψ hψ d hd hd1
  unfold Cg at h0 ⊢
  set η : (ZMod (l ^ r))ˣ → Qbar l := fun x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x with hη
  set u := ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd) with hu
  have h2 : ∀ x, ‖η x - (d : Qbar l) ^ e * η (x * u)‖ ≤ ‖(l : Qbar l) ^ n‖ := h1
  have hsp : sp η (Z r) s = ∑ x, η (x * u) * Z r s (x * u) :=
    (Fintype.sum_equiv (Equiv.mulRight u) _ _ fun x => rfl).symm
  have hsm : sp η (smZ d hd Z r) s = sp η (Z r) s - d * ∑ x, η x * Z r s (x * u) := by
    unfold sp smZ
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [← hu]; ring
  have hD : ∑ x, (η x - (d : Qbar l) ^ e * η (x * u)) * Z r s (x * u) =
      ∑ x, η x * Z r s (x * u) - (d : Qbar l) ^ e * sp η (Z r) s := by
    rw [hsp, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have key : ((1 - (d : Qbar l) ^ (e + 1)) • y s) 1 - sp η (smZ d hd Z r) s =
      (1 - (d : Qbar l) ^ (e + 1)) * (y s 1 - sp η (Z r) s) +
        d * ∑ x, (η x - (d : Qbar l) ^ e * η (x * u)) * Z r s (x * u) := by
    rw [hD, hsm, Pi.smul_apply, smul_eq_mul]
    ring
  have hc1 : ‖(1 - (d : Qbar l) ^ (e + 1))‖ ≤ 1 :=
    GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c.O.sub_mem c.O.one_mem (c.O.pow_mem (natCast_mem c.O d) _))
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans h0
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (sm_norm_nat hd).le).trans ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hZ _ _ _))).trans (h2 x)

end UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.smSys : UpperTheory.V.Z.Kato.Joint.SmSys := by
  intro l _ Ω _ _ W c y S' A ν Z e ψ d hd hd1 hψ h1 h2 h3
  exact ⟨sm_sys h1 (c.O.sub_mem c.O.one_mem (c.O.pow_mem (natCast_mem c.O d) _)), sm_iw h2 d hd,
    sm_sp (fun r => (h2.2.1 r).1) e ψ hψ d hd hd1 h3⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmoothedZetaClassHodgeTateLawStatement
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def KatoEulerSystemIwasawaClassStatement : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
    ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
      (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
      (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e →
      (∃ x, cw x ≠ 0) → AdmWn ι e g A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
      ∃ (c₀ m : ℕ) (cf' : Coef l) (S' : Finset Pl) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
        (y : G ℚ Ω → Fin 2 → Qbar l),
        IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
        (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧
        (∀ r y i, Continuous fun s => Y r s y i) ∧
        (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) ∧ (∀ r s y i, Y r s y i ∈ cf.O) ∧ (∀ z, z ∈ cf.O → z ∈ cf'.O) ∧
        (∀ r s, Cv r (y s) (GlobalTheory.KA.spec (fun u : (ZMod (l ^ r))ˣ => ((((u : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r u) (Y r) s)) ∧
        Sys W cf' (fun s => ((l : Qbar l) ^ m) • y s) S' ∧
        IwSys2 cf' A (nuD W e ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) ∧
        SpLink A e (chiK l ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) (fun s => ((l : Qbar l) ^ m) • y s)

def SmoothedZetaClassHodgeTateLawStatement : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
      (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
    ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
      (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
      AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
    ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
    ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
      IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
      (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
      (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
      (∀ r s y, Y r s y 1 ∈ cf.O) →
    ∀ (χd : ℕ → ℤ_[l]), (∀ δ : ℕ, Nat.Coprime δ N → IsUnit (χd δ)) → (∀ a b : ℕ, χd (a * b) = χd a * χd b) →
      (∀ a b : ℕ, a % N = b % N → χd a = χd b) → ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χd j pr cf lam →
    ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
    ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
      HTLawCsOfCoef A cf (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) j m₀ c₁
        (fun m ψ z => (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (GlobalTheory.KummerEisensteinGalois.up (l ^ m) (fun i => ∑ x : ZMod N, cw x *
            GlobalTheory.LambdaValuationPowers.chiProj N l m (2 * e + 1) ψ (fun n => ((χd n : ℤ_[l]) : Qbar l)) (c : ℤ) (d : ℤ) (x.val : ℤ) i)))

def AdmTop2 : Prop :=
  ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
    [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
    (j : Ω →+* Qbar l),
    Nf e S A W → 1 ≤ e →
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
    (∀ x ∈ A, ‖j x‖ ≤ 1) →
    ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
    (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
    ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
    ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
      (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
    P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
    (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
    (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
    (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
    (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
    (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
    (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
    ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
    (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
      Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
    ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
      c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
      (∀ b b', pr (b + b') = pr b + pr b') ∧
      (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
      (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
      (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
      (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
      IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam)

def Glue2 : Prop :=
  KatoEulerSystemIwasawaClassStatement → SmoothedZetaClassHodgeTateLawStatement → AdmFR → TowerEx → GlobalTheory.EisM.CuspidalUnitaryTwistsClaim → Meas3 → JEx → CoefUb → Mono → PsiEx → FrobU → DetIne → HatW → PinOf → SmNz →
    GmEx → ExplSmul → AvgEq → AvgMF → RhsEq → SmSys → ChiFix → ExistsZetaEulerSystemIwasawaData Pin7

end UpperTheory.V.Z.Kato.Joint

end
end

