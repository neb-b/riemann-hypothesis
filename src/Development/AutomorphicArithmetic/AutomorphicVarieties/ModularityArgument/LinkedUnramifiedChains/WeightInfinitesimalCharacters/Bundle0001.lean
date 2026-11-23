module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.Temper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Formalism.PrimeAboveExistence.LenEqPlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.FreeFlagU
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.J.freeFlagU :
    Af.HypothesesH → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
        ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → Af.IsAutCsd ι r →
        ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ),
          W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ → StrictAnti m → 0 < k →
          (∀ i (g : Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (ψ i g * cycBar F Ω l g ^ (-m i)) ^ k = 1) →
          (∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) →
          ∃ g : Dec (F := F) A, cycZ F Ω l g = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  intro PH F Ω _ _ _ _ _ _ l _ hl ι n hn r hr ⟨π, hreg, hcsd, hatt⟩ A hA ψ m k hflag hm hk hine hgen
  have P := PH.toClassicalTheorems
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar F ^ n) :=
    ⟨fun v => by
      have e : (quadChar F ^ n).locInf v (-1) = (quadChar F).locInf v (-1) ^ n := rfl
      rw [e, quadChar_locInf],
     by rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hcsd⟩
  obtain ⟨w, h, hw⟩ := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A l).2 hA
  obtain ⟨⟨σ, hσ⟩, -⟩ := locCompC P F n π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  have hc := (compatCsd PH F Ω l ι n hn r π hr hreg hcsd hatt w σ hσ A h rc hrc).2
  exact purLocS P F Ω l hl ι n r hr w A h hw (rc (algNorm σ))
    (fun O _ _ _ Bw hj => ⟨(hc O Bw hj).1, by first | exact Lev.SsCmp.of_eq (hc O Bw hj).2 | exact (hc O Bw hj).2⟩)
    (temper P F Ω n hn π hreg ⟨_, hpol⟩ w A h rc hrc σ hσ) ψ m k hflag hm hk hine
    (Or.inl hgen)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.PropGKU
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Z.J

private theorem isCM (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) (h' : IsTotallyComplex K) :
    IsCMField K := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := h }
  exact IsCMField.ofCMExtension ℚ K

private theorem exists_w (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal := by
  have h1 : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro h
    have := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at this
    rcases Nat.pow_eq_one.1 this with h | h
    · exact hp.ne_one h
    · exact Module.finrank_pos.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h1
  have hm : (p : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hm⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))

private theorem cop_norm {K : Type} [Field K] [NumberField K] {p N : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) : (normV w).Coprime N := by
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [Ideal.absNorm_span_natCast] at h
  rw [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact Nat.Coprime.coprime_dvd_left h (((Nat.Prime.coprime_iff_not_dvd hp).2 hN).pow_left _)

private theorem frob_val {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [hl : Fact l.Prime] {p N : ℕ} [NeZero N] (hp : p.Prime) (hN : ¬ p ∣ N) (hlp : l ≠ p)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) {B : ValuationSubring Ω} (hB : IsPlaceOver B w)
    {σ : G K Ω} (hσ : IsFrob B (normV w) σ) :
    ((Chr.cls ℚ Ω N (galEmb ℚ K Ω σ) : (ZMod N)ˣ) : ZMod N) = normV w ∧
      ((cycZ ℚ Ω l (galEmb ℚ K Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = normV w := by
  obtain ⟨-, -, -, hcop, -, -, hpow, -⟩ := ML.placeBasic Ω
  have hp' : ML.Over B p := by
    have := (hB p).2 hw
    simpa only [map_natCast] using this
  constructor
  · have hφ : IsFrob (F := ℚ) B (normV w) (galEmb ℚ K Ω σ) :=
      ⟨Subgroup.mem_comap.1 (((galEmbFam ℚ K Ω l).1 B).1.ge hσ.1), hσ.2⟩
    have h := hpow B _ N _ hφ (hcop B p N ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) hp')
    rw [(Chr.clsFacts ℚ Ω N).2.2.1 _ (ZMod.unitOfCoprime _ (cop_norm hp hN hw)) fun ζ hζ => ?_, ZMod.coe_unitOfCoprime]
    rw [h ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  · refine cycZ_of_isFrob (F := K) (fun h => ?_) hB hσ
    refine hcop B p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hp' ?_
    have := (hB l).2 h
    simpa only [map_natCast] using this

private theorem vl_bound {l : ℕ} [hl : Fact l.Prime] {ι : Type} {κ : Type} [Fintype ι] (X : ι → Finset κ)
    (f : ι → κ → PadicAlgCl l) (NN : ℤ) (h0 : NN ≠ 0) (hf : ∀ o, ∀ ρ ∈ X o, f o ρ ≠ 0)
    (h : ‖((NN : ℤ) : PadicAlgCl l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖f o ρ‖) :
    ∑ o, ∑ ρ ∈ X o, vl l (f o ρ) ≤ padicValInt l NN := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have e1 : ‖((NN : ℤ) : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l NN : ℝ)) := by
    rw [← map_intCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends,
      Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0), Padic.valuation_intCast, ← Real.rpow_intCast]
    simp
  have h2 := Real.logb_le_logb_of_le hl1 (by rw [e1]; positivity) h
  rw [e1, Real.logb_rpow (by positivity) hl1.ne', Real.logb_prod _ _ fun o _ =>
    Finset.prod_ne_zero_iff.2 fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ),
    Finset.sum_congr rfl fun o _ => Real.logb_prod _ _ fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ)] at h2
  simp only [vl, Finset.sum_neg_distrib]
  linarith

private theorem ker_comp {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    (ψ : DirichletCharacter O N) : (ψ.ringHomComp f).toUnitHom.ker = ψ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, Units.val_one]
  exact map_eq_one_iff f hf

private theorem card_orb {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    Nat.card {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} ≤ Nat.totient H.index := by
  by_cases h : ∃ χ : DirichletCharacter ℂ N, χ.toUnitHom.ker = H
  · obtain ⟨χ, rfl⟩ := h
    obtain ⟨h1, -, -, h2⟩ := orbFacts ℂ N χ
    rw [h1, ← h2]
    exact le_rfl
  · haveI : IsEmpty {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} := ⟨fun x => h ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

private theorem t_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e q : ℕ) (ψ : DirichletCharacter c.O N) (ι : Qbar l ≃+* ℂ) (g : G ℚ Ω)
    (h1 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = q) (h2 : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = q) :
    ι.symm (Af.eis3 q e (ι (algebraMap c.O (PadicAlgCl l) (ψ q)))⁻¹) =
      algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹ : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹)⁻¹ : c.Oˣ) : c.O)) := by
  have e1 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.Oˣ) : c.O) = (q : c.O) ^ e * ψ q := by
    simp [Chr.Psi, Chr.dirG, chiO, h1, h2]
  rw [map_inv (Chr.Psi l e (Chr.dirG ℚ Ω ψ)), inv_inv, map_add (f := _), map_add (f := _), map_one, map_units_inv, e1]
  simp [Af.eis3, mul_comm]

private theorem comp_inj {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    {ψ ψ' : DirichletCharacter O N} (h : ψ.ringHomComp f = ψ'.ringHomComp f) : ψ = ψ' :=
  MulChar.ext' fun a => hf (by rw [← MulChar.ringHomComp_apply, h, MulChar.ringHomComp_apply])

private theorem orb_equiv {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) (f : c.O →+* ℂ)
    (hf : Function.Injective f) {ψ₀ : DirichletCharacter c.O N} (h₀ : ψ₀ ∈ orb c H) :
    ∃ E : orb c H ≃ {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H}, ∀ ψ, (E ψ).1 = ψ.1.ringHomComp f := by
  refine ⟨Equiv.ofBijective (fun ψ => ⟨ψ.1.ringHomComp f, (ker_comp f hf _).trans ((mem_orb c).1 ψ.2)⟩) ⟨?_, ?_⟩,
    fun _ => rfl⟩
  · intro a b h
    exact Subtype.ext (comp_inj f hf (congrArg Subtype.val h))
  · rintro ⟨χ, hχ⟩
    have h1 := (ker_comp f hf ψ₀).trans ((mem_orb c).1 h₀)
    obtain ⟨j, -, hj⟩ := ((orbFacts ℂ N (ψ₀.ringHomComp f)).2.2.1 χ).1 (hχ.trans h1.symm)
    rw [MulChar.ringHomComp_pow] at hj
    refine ⟨⟨ψ₀ ^ j, (mem_orb c).2 ?_⟩, Subtype.ext hj.symm⟩
    rw [← ker_comp f hf, ← hj, hχ]
end

