module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import ReciprocityTheory.DualLattices.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CMVal GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.ChiGrid

namespace GlobalTheory.SqTop.FieldDatPf

theorem good_prime {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (hs : GlobalTheory.Mem.Chr.SplitsC H.E p) :
    ¬ (p : ℤ) ∣ discr H.E ∧ ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal →
      Ideal.absNorm P.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below P) := by
  refine ⟨GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp _ ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver hp).symm.trans hs),
    fun P hP => ?_⟩
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs P hP
  exact ⟨h1, GlobalTheory.ToricDenom.splits_below H h3⟩

theorem splitsC_of_mod {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (h : p % (H.QS * H.q * H.d) = 1) :
    GlobalTheory.Mem.Chr.SplitsC H.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod R H p hp h).1

theorem exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), GlobalTheory.ToricDenom.below P = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, hv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  exact ⟨⟨Q, hQ.isPrime, hne⟩, HeightOneSpectrum.ext hv.over.symm⟩

theorem natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  show algebraMap (OF E) (𝓞 E) _ ∈ P.asIdeal ↔ _
  rw [map_natCast]

variable {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T}


open Classical in
theorem expIn_condF' (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    expIn (condF P) v = if v ∈ P.S0 then condExp P v else 0 := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), v ∉ S →
      ¬ v.asIdeal ∣ ∏ u ∈ S, u.asIdeal ^ condExp P u := fun S hS h => by
    induction S using Finset.induction_on with
    | empty => exact v.prime.not_dvd_one (by simpa using h)
    | @insert u S hu ih =>
      rw [Finset.prod_insert hu] at h
      rcases v.prime.dvd_mul.mp h with h | h
      · have h2 := v.prime.dvd_of_dvd_pow h
        have : v = u := HeightOneSpectrum.ext (associated_iff_eq.1 (v.irreducible.associated_of_dvd u.irreducible h2))
        exact hS (this ▸ Finset.mem_insert_self u S)
      · exact ih (fun hv => hS (Finset.mem_insert_of_mem hv)) h
  show multiplicity v.asIdeal (∏ u ∈ P.S0, u.asIdeal ^ condExp P u) = _
  split_ifs with h
  · rw [← Finset.mul_prod_erase _ _ h]
    refine multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) fun h' => ?_
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ v.ne_bot)] at h'
    exact key _ (Finset.notMem_erase _ _) h'
  · exact multiplicity_eq_zero_of_not_dvd (key _ h)

theorem isBaseCond_condF (P : Places L) (hg : ∀ i, D.host.g i % LevelStarExponents.condE D = 1)
    (hpde : ((Ideal.span {(D.host.pde : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
      ((Ideal.span {(D.host.pde' : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E) :
    IsBaseCond (condF P) := by
  classical
  have hE : 1 < LevelStarExponents.condE D := by
    have := D.host.qd_big
    unfold LevelStarExponents.condE
    have h1 : 1 ≤ D.host.QS := D.host.QS_pos
    have h2 : 1 < D.host.q := by omega
    have h3 : 1 ≤ D.host.d := by omega
    calc 1 < 1 * D.host.q * 1 := by omega
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr

  have hgood : ∀ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) →
      p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
        (p : 𝓞 D.host.E) ∈ Q.asIdeal → Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
    have ofMod : ∀ p : ℕ, p.Prime → p % LevelStarExponents.condE D = 1 → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
        ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
          Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
      intro p hp hm
      have h4 : p % 4 = 1 := by
        have : (4 : ℕ) ∣ LevelStarExponents.condE D := ((dvd_trans (by norm_num) (UpperTheory.Ram.Rd.sixteen_dvd_QS D.host)).mul_right _).mul_right _
        rw [← Nat.mod_mod_of_dvd p this, hm]
      refine ⟨hp, by omega, good_prime D.host hp (splitsC_of_mod D.host hp hm)⟩
    have ofSplit : ∀ p : ℕ, p.Prime → p % 15 = 1 →
        ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E →
        p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
        ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ Q.asIdeal →
          Ideal.absNorm Q.asIdeal = p ∧ Splits (GlobalTheory.ToricDenom.below Q) := by
      intro p hp h15 hs
      have hs' : GlobalTheory.Mem.Chr.SplitsC D.host.E p := by
        have e := GlobalTheory.HostSplit.ncard_placesOver D.host.E hp
        rw [hs] at e
        exact e
      exact ⟨hp, by omega, good_prime D.host hp hs'⟩
    rintro p (rfl | rfl | rfl | rfl | rfl)
    · exact ofMod _ (D.host.g_prime 0) (hg 0)
    · exact ofMod _ (D.host.g_prime 1) (hg 1)
    · exact ofSplit _ D.host.pde_prime D.host.pde_mod.1 hpde.1
    · exact ofSplit _ D.host.pde'_prime D.host.pde_mod.2 hpde.2
    · obtain ⟨hq, hqm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
      refine ofMod _ hq ?_
      rw [← Nat.mod_mod_of_dvd _ (dvd_mul_left (LevelStarExponents.condE D) (Formalism.MainNotions.rPrAv D)), hqm]
      exact Nat.mod_eq_of_lt hE
  have hexp : ∀ v : HeightOneSpectrum (OF D.host.E), v.asIdeal ∣ condF P → v ∈ P.S0 := by
    intro v hv
    by_contra h
    have e := expIn_condF' P v
    rw [if_neg h] at e
    have hne : condF P ≠ 0 := Finset.prod_ne_zero_iff.2 fun u _ => pow_ne_zero _ u.ne_bot
    have := (multiplicity_eq_zero (FiniteMultiplicity.of_prime_left v.prime hne)).1 e
    exact this hv
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot
  · intro e
    have h0 : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
    have e1 := expIn_condF' P P.v0
    rw [if_pos h0, condExp, if_pos rfl] at e1
    have e2 : expIn (condF P) P.v0 = 0 := by
      rw [e]; exact multiplicity_eq_zero_of_not_dvd fun h => P.v0.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
    omega
  · have hS := hexp v hv
    have hle : expIn (condF P) v ≤ 2 := by
      rw [expIn_condF', if_pos hS, condExp]; split_ifs <;> omega
    obtain ⟨p, hp, hpv⟩ : ∃ p : ℕ, (p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' ∨ p = q0 D) ∧
        (p : OF D.host.E) ∈ v.asIdeal := by
      rcases P.mem_S0_of_sum_eq.1 hS with h | h
      · exact ⟨q0 D, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h ▸ P.basePlace_over_qZero⟩
      · rcases (S1_mem_OmF D).1 h with h | h | h | h
        · exact ⟨_, Or.inl rfl, h⟩
        · exact ⟨_, Or.inr (Or.inl rfl), h⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩
    obtain ⟨h1, h2, h3, h4⟩ := hgood p hp
    obtain ⟨Q, rfl⟩ := exists_above v
    exact ⟨(h4 Q ((natCast_mem_below Q p).1 hpv)).2, hle, p, h1, h2, hpv, h3, fun Q' hQ' => (h4 Q' hQ').1⟩

theorem isCMType_cmPhi (D : D7) : IsCMType (cmPhi D) ∧ ∀ τ τ', cmPhi D τ D.host.sqrtMinusD = cmPhi D τ' D.host.sqrtMinusD := by
  obtain ⟨hcm, hsq⟩ := GlobalTheory.LamTie.CMType.phi_cmType D.R D.host
  have e : ∀ τ, cmPhi D τ = GlobalTheory.LamTie.phi D.host (D.eTau τ) := fun _ => rfl
  refine ⟨fun σ => ?_, fun τ τ' => by rw [e, e]; exact hsq _ _⟩
  obtain ⟨g, hg, hu⟩ := hcm σ
  refine ⟨D.eTau.symm g, ?_, fun τ hτ => ?_⟩
  · simp only [e, Equiv.apply_symm_apply]
    exact hg
  · have hτ' : σ = GlobalTheory.LamTie.phi D.host (D.eTau τ) ∨ σ = ComplexEmbedding.conjugate (GlobalTheory.LamTie.phi D.host (D.eTau τ)) := by
      simpa only [e] using hτ
    rw [← hu _ hτ', Equiv.symm_apply_apply]

end GlobalTheory.SqTop.FieldDatPf

namespace GlobalTheory.SqTop

theorem fieldDat : FieldDat := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ _ G => ?_⟩⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  obtain ⟨hcm, hsq⟩ := FieldDatPf.isCMType_cmPhi D
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  exact ⟨D.host.isCMField_hostE, GlobalTheory.ToricDenomBridge.host_isAbelianGalois D.host,
    GlobalTheory.ToricDenomBridge.isFieldData_host D.host hcm hsq, FieldDatPf.isBaseCond_condF G.pl Pm.g_mod Pm.pde_split,
    GlobalTheory.ToricDenom.ringPair D.host.d hd,
    GlobalTheory.ToricDenomBridge.isIntLattice_of D.host.hyp.2.1 (by have := D.host.hyp.2.2.2.1; omega) rfl rfl⟩

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeight
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.FlatDiag

theorem norm_diagChar_flatWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  classical
  intro E _ _ _ H Dw l c σ τ t
  set e := exOf Dw (flatWt Dw τ) 0 with he_def
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have hE : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      e (some ⟨ρ, i⟩) = if ρ = τ.1 then -1 else if ρ = conjEmb τ.1 then 1 else 0 := by
    intro ρ i
    obtain ⟨n, hi⟩ := i
    simp only [he_def, exOf, exZ, wtOf, flatWt, parWt, Datum.mult] at hi ⊢
    by_cases h : ρ (H.rt : E) = H.rt0
    · rw [if_pos h] at hi
      rw [dite_eq_left h, dite_eq_left hi]
      have h2 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      by_cases h1 : ρ = τ.1
      · subst h1
        simp
      · have h3 : (⟨ρ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [h1, h2, h3]
    · rw [if_neg h] at hi
      rw [dite_eq_right h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      by_cases h' : conjEmb ρ (H.rt : E) = H.rt0
      · rw [dite_eq_left h', dite_eq_left hi]
        by_cases h2 : ρ = conjEmb τ.1
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) = τ := Subtype.ext (show conjEmb ρ = τ.1 by rw [h2, conjEmb_conjEmb])
          rw [if_pos h3, if_neg h1, if_pos h2]
          norm_num
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) ≠ τ := fun e => h2 (by
            rw [← congrArg Subtype.val e, conjEmb_conjEmb])
          rw [if_neg h3, if_neg h1, if_neg h2]
          norm_num
      · rw [dite_eq_right h']
        have h2 : ρ ≠ conjEmb τ.1 := fun e => h' (by rw [e, conjEmb_conjEmb]; exact τ.2)
        simp [h1, h2]
  have e0 : e none = 0 := by simp [he_def, exOf, exZ, wtOf_snd]
  let f : (CAt σ)ˣ →* ℂˣ := Units.map (MonoidHom.id ℂ)
  have hf : ∀ u : (CAt σ)ˣ, ((f u : ℂˣ) : ℂ) = toC (u : CAt σ) := fun _ => rfl
  have e₁ : GlobalTheory.CompHS.diagChar e t = ((∏ ix, f (t ix) ^ e ix : ℂˣ) : ℂ) := by
    have : (∏ ix, f (t ix) ^ e ix) = f (∏ ix, t ix ^ e ix) := by simp only [map_prod, map_zpow]
    rw [this, hf]
    rfl
  let g : (E →+* ℂ) → ℝ := fun ρ => ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt σ))‖ ^ e (some ⟨ρ, i⟩)
  have e₂ : ‖GlobalTheory.CompHS.diagChar e t‖ = ∏ ρ, g ρ := by
    rw [e₁, Units.coe_prod, norm_prod, Fintype.prod_option, e0, zpow_zero, Units.val_one, norm_one, one_mul,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun ρ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hf]
  have e₃ : ∏ ρ, g ρ = g τ.1 * g (conjEmb τ.1) := by
    rw [← Finset.prod_pair hne]
    refine (Finset.prod_subset (Finset.subset_univ _) fun ρ _ hρ => ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
    exact Finset.prod_eq_one fun i _ => by rw [hE, if_neg hρ.1, if_neg hρ.2, zpow_zero]
  have gτ : g τ.1 = (∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [hE, if_pos rfl, zpow_neg_one]
  have gc : g (conjEmb τ.1) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖ :=
    Finset.prod_congr rfl fun i _ => by rw [hE, if_neg hne.symm, if_pos rfl, zpow_one]
  rw [e₂, e₃, gτ, gc, div_eq_mul_inv, mul_comm]

end GlobalTheory.CompHS.FlatDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSigmaStableUnitNeighborhood
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.IdeleCongr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAE_mul {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  first
  | exact @_root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem
  | exact _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem
  | (apply _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAdeleProducts.intAE_mul_mem ..)

theorem intAE_one : (1 : FiniteAdeleRing (𝓞 F) F ⊗[F] E) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  refine AddSubgroup.subset_closure ⟨1, fun v => ?_, 1, ?_⟩
  · rw [map_one]; exact one_mem _
  · rw [Algebra.TensorProduct.one_def]; simp

theorem intAE_nat (m : ℕ) : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [← nsmul_one]; exact nsmul_mem intAE_one m

theorem sigR_intAE (σ : E →ₐ[F] E) {z : FiniteAdeleRing (𝓞 F) F ⊗[F] E} (h : z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, RingOfIntegers.mapRingHom (σ : E →+* E) x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_cA (σ : E →ₐ[F] E) (y : AdeleRing (𝓞 F) F ⊗[F] E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.cA σ y) = HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ (HeckeCharacterZeroLocus.ThmBIn.finPart F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

end GlobalTheory.IdeleCongr

namespace GlobalTheory.IdeleCongr

theorem exists_open_congruence_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (m : ℕ), 0 < m → ∃ U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, IsOpen (U : Set (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) ∧
      (∀ x ∈ U, Units.map (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ).toRingHom.toMonoidHom x ∈ U) ∧
      ∀ x ∈ U, ∃ s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E,
        HeckeCharacterZeroLocus.ThmBIn.finPart F E (x : AdeleRing (𝓞 F) F ⊗[F] E) = 1 + (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * s := by
  intro F E _ _ _ _ _ σ m hm
  haveI : IsModuleTopology (HeckeCharacterZeroLocus.ThmBIn.AF F) (HeckeCharacterZeroLocus.ThmBIn.AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (HeckeCharacterZeroLocus.ThmBIn.AE F E) := IsModuleTopology.isTopologicalRing (HeckeCharacterZeroLocus.ThmBIn.AF F) _
  obtain ⟨Φ, hΦc, -, hint⟩ := GlobalTheory.HeckeInhabitant.exists_fin (F := F) (E := E)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  let c : FiniteAdeleRing (𝓞 F) F ⊗[F] E := HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹)
  have hmc : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * c = 1 := by
    have : (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) = HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)) := by
      rw [map_natCast, map_natCast]
    rw [this, ← map_mul, ← map_mul, mul_inv_cancel₀ hm0, map_one, map_one]
  let C : AdeleRing (𝓞 F) F ⊗[F] E → Prop := fun y =>
    (HeckeCharacterZeroLocus.ThmBIn.finPart F E y - 1) * c ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E
  have hdec : ∀ z : FiniteAdeleRing (𝓞 F) F ⊗[F] E, z = 1 + m * ((z - 1) * c) := fun z => by
    linear_combination (1 - z) * hmc
  have hint' : ∀ y, C y → HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := fun y hy => by
    rw [hdec (HeckeCharacterZeroLocus.ThmBIn.finPart F E y)]
    exact add_mem intAE_one (intAE_mul (intAE_nat m) hy)
  have hCmul : ∀ y z, C y → C z → C (y * z) := fun y z hy hz => by
    have e : (HeckeCharacterZeroLocus.ThmBIn.finPart F E (y * z) - 1) * c = HeckeCharacterZeroLocus.ThmBIn.finPart F E y * ((HeckeCharacterZeroLocus.ThmBIn.finPart F E z - 1) * c)
        + (HeckeCharacterZeroLocus.ThmBIn.finPart F E y - 1) * c := by
      rw [map_mul]; ring
    show _ ∈ _
    rw [e]
    exact add_mem (intAE_mul (hint' y hy) hz) hy
  have hC1 : C 1 := by
    show _ ∈ _
    rw [map_one, sub_self, zero_mul]
    exact zero_mem _
  let U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ :=
    { carrier := {x | C x ∧ C ((x⁻¹ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) : AdeleRing (𝓞 F) F ⊗[F] E)}
      one_mem' := ⟨by rw [Units.val_one]; exact hC1, by rw [inv_one, Units.val_one]; exact hC1⟩
      mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul]; exact hCmul _ _ hx.1 hy.1,
        by rw [mul_inv_rev, Units.val_mul]; exact hCmul _ _ hy.2 hx.2⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩ }
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hcont : Continuous fun y : AdeleRing (𝓞 F) F ⊗[F] E => (y - 1) * HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  have hCo : IsOpen {y | C y} := by
    have h1 : IsOpen {y : AdeleRing (𝓞 F) F ⊗[F] E |
        ∀ P, Valued.v (Φ ((y - 1) * HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹) P) ≤ 1} := (hO.preimage hΦc).preimage hcont
    convert h1 using 1
    ext y
    simp only [Set.mem_setOf_eq]
    rw [← hint, map_mul, map_sub, map_one]
  have hσ : ∀ y, (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) y
      = HeckeCharacterZeroLocus.ThmBIn.cA σ y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => rfl
  have hsc : HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ c = c := by
    change HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ (HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E (m : E)⁻¹)) = _
    rw [← finPart_cA, GlobalTheory.HeckeInhabitant.cA_inc, map_inv₀, map_natCast]
  have hCσ : ∀ y, C y → C (HeckeCharacterZeroLocus.ThmBIn.cA σ y) := fun y hy => by
    show _ ∈ _
    rw [finPart_cA, ← hsc, ← map_one (HeckeCharacterZeroLocus.ThmBIn.sigR (FiniteAdeleRing (𝓞 F) F) σ), ← map_sub, ← map_mul]
    exact sigR_intAE σ hy
  refine ⟨U, ?_, fun x hx => ⟨?_, ?_⟩, fun x hx => ⟨_, hx.1, hdec _⟩⟩
  · exact (hCo.preimage Units.continuous_val).inter (hCo.preimage Units.continuous_coe_inv)
  · change C ((Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) (x : AdeleRing (𝓞 F) F ⊗[F] E))
    rw [hσ]; exact hCσ _ hx.1
  · rw [← map_inv]
    change C ((Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ) ((x⁻¹ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) : AdeleRing (𝓞 F) F ⊗[F] E))
    rw [hσ]; exact hCσ _ hx.2

end GlobalTheory.IdeleCongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNatural
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.HodgeNat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem theta_xi_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (xi ε) = 0 := by
  have h1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
  have h2 := h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [xi, map_sum]
  simpa [map_pow, WittVector.fontaineTheta_teichmuller, zeta] using h2

theorem ghost_mu_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (n : ℕ) :
    ghost p O n (Sandwich.mu ε) = 0 := by
  induction n with
  | zero =>
    show WittVector.fontaineTheta O p (Sandwich.mu ε) = 0
    rw [Sandwich.mu, map_sub, WittVector.fontaineTheta_teichmuller, map_one, sub_eq_zero]
    exact hε.zeta_zero
  | succ n ih =>
    rw [← ghost_frobenius, Dieudonne.frobenius_mu, ghost_mul, ih, mul_zero]

noncomputable def muPair [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : TDual G where
  toFun t := Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)
  map_add' s t := by
    simp only [epsPairing, map_add (f := _), LinearMap.add_apply, mul_add]
  map_smul' a t := by
    simp only [epsPairing, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring

theorem muPair_mem [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : muPair hε G χ ∈ latt G := fun n =>
  ⟨0, fun t => by
    show ghost p O n (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) = 0
    rw [ghost_mul, ghost_mu_eq_zero hε, zero_mul]⟩

end GlobalTheory.PDivLat.HodgeNat


open GlobalTheory.PDivLat.HodgeNat in
theorem GlobalTheory.PDivLat.iota_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H f hG hH M _ _ r M' _ _ r' u ι ι' hrs hrk hu hι hι' w
  obtain ⟨hfree, hfin, -⟩ := _root_.GlobalTheory.PDivLat.latt_free_finrank p C v O hv ε hε G hG
  haveI : Nontrivial (Ainf p O) := (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv).nontrivial
  obtain ⟨hMfree, -, -⟩ := Dieudonne.free_of_reduction (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv)
    (theta_xi_eq_zero hε) r hrs fun m hm => (hrk m).1 hm
  haveI := hMfree

  have key : ∀ χ : H.dual.Tate, u (ι' (dlog H χ)) = ι (omegaMap G H f (dlog H χ)) := by
    intro χ
    let Y : latt H := ⟨muPair hε H χ, muPair_mem hε H χ⟩
    have h1 : ι' (dlog H χ) = r' Y := hι' χ Y fun t => rfl
    have h2 : ι (dlog G (tateMap H.dual G.dual O (dualHom G H f) χ)) = r (lattMap f Y) := by
      refine hι _ _ fun t => ?_
      show Sandwich.mu ε * ofPadic p O (epsPairing hε H (tateMap G H O f t) χ) = _
      rw [epsPairing, epsPairing, pairing_tateMap]
    rw [h1, hu, ← h2, dlog_tateMap]
  obtain ⟨c, hc, hcw⟩ := _root_.GlobalTheory.PDivLat.exists_smul_mem_span_dlog p C v O hv ε hε H hH
  have hspan : ∀ x ∈ Submodule.span O (Set.range (dlog H)),
      u (ι' x) = ι (omegaMap G H f x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨χ, rfl⟩ := hx; exact key χ
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have h := hspan _ (hcw w)
  simp only [map_smul] at h
  have h' : c • (u (ι' w) - ι (omegaMap G H f w)) = 0 := by rw [smul_sub, h, sub_self]
  have tf : ∀ x : M, c • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis O M
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h3 := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
    simpa using (mul_eq_zero.1 h3).resolve_left hc
  exact sub_eq_zero.1 (tf _ h')
end

