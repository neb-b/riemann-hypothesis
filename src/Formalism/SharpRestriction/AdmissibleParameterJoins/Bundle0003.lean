module

public import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0001
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces

@[expose] public section

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSk
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

private theorem hH_hP (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    ∃ h : Nat.Coprime p 2, D.R.hH (D.R.iota (hP D p)) =
      hcl D.R.e (ZMod.unitOfCoprime p (Nat.Coprime.pow_right (D.R.e + 2) h)) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : D.host.cls 2 = PrimeClass.ram2 := Formalism.BasicNotions.primeClass_two D.host.toHostRaw
    have hc' : D.host.cls 2 = PrimeClass.inertClass := hc
    rw [h2] at hc'
    cases hc'
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  refine ⟨hcop, ?_⟩
  have hN : ¬ p ∣ D.host.condN := Formalism.BasicNotions.not_dvd_conductor_of_inert hp (show D.host.cls p = PrimeClass.inertClass from hc)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨P, hPm, hPl⟩ : ∃ P : Ideal (𝓞 D.host.E), P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
    first
    | exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _
    | exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _ _
    | exact Ideal.exists_ideal_liesOver_maximal_of_isIntegral _
    | (obtain ⟨Q, hQm, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E)
          (Ideal.span {(p : ℤ)}) (by simp)
       exact ⟨Q, hQm, ⟨hQc.symm⟩⟩)
  haveI : P.IsPrime := hPm.isPrime
  obtain ⟨⟨σ, hσ⟩, -, -, -⟩ := D.host.der.frob p hN P
  have hmem : D.host.galE σ ∈ frobSet D p := ⟨P, inferInstance, hPl, σ, hσ, rfl⟩
  obtain ⟨P', hP'p, hP'l, σ', hσ', hgal⟩ := Classical.epsilon_spec ⟨_, hmem⟩
  obtain ⟨-, -, h3, -⟩ := D.host.der.frob p hN P'
  obtain ⟨-, -, v, hv, hvh⟩ := h3 σ' hσ'
  unfold hP
  simp only [Formalism.HC.Frame.iota_iotaInv]
  rw [← hgal, show ZMod.unitOfCoprime p (Nat.Coprime.pow_right (D.R.e + 2) hcop) = v from
    Units.ext (by rw [ZMod.coe_unitOfCoprime, hv])]
  exact hvh

theorem two_readings_of_Frobenius (D : D7) : Formalism.MainNotions.CornerGLContinuity.FrobeniusClassCompatibility D := by
  intro p hp hc
  obtain ⟨h2, hh⟩ := hH_hP D p hp hc
  refine ⟨fun h => ?_, ?_⟩
  · subst h
    exact absurd h2 (by decide)
  unfold Formalism.MainNotions.GlobalTheoryTheory.hOf
  split_ifs with hcond
  rw [Formalism.BasicNotions.iotaH_iotaHInv, ← hh]
  rfl

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem cc_l : PowerSeries.constantCoeff g.l = 0 := by
  unfold G1.l
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.TaylorLogMetric.flog, PowerSeries.coeff_mk, if_pos rfl]

private theorem cc_subst_lemma {R : Type} [CommRing R] {υ : Type} {a : MvPowerSeries υ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst hs]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  rcases d with _ | d
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_smul]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow (Nat.succ_ne_zero d), smul_zero]

private theorem comp_lemma_2 {υ ρ : Type} {R : Type} [CommRing R] {a : MvPowerSeries υ R}
    (ha : MvPowerSeries.constantCoeff a = 0) {c : υ → MvPowerSeries ρ R} (hc : HasSubst c)
    (f : PowerSeries R) : subst c (PowerSeries.subst a f) = PowerSeries.subst (subst c a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hc]

theorem cc_lg {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) : constantCoeff (g.lg a) = 0 :=
  cc_subst_lemma ha (cc_l g)

theorem cc_pt (hex : PowerSeries.constantCoeff g.ex = 0) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) :
    constantCoeff (g.pt a) = 0 :=
  cc_subst_lemma ha hex

theorem lg_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.lg a) = g.lg (subst c a) :=
  comp_lemma_2 ha hc g.l

theorem pt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.pt a) = g.pt (subst c a) :=
  comp_lemma_2 ha hc g.ex

theorem phAt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.phAt a) = g.phAt (subst c a) :=
  comp_lemma_2 ha hc g.ph

theorem add_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.add a b) = g.add (subst c a) (subst c b) := by
  have h0 : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add (f := _), cc_lg g ha, cc_lg g hb, add_zero]
  show subst c (g.pt (g.lg a + g.lg b)) = g.pt (g.lg (subst c a) + g.lg (subst c b))
  rw [pt_subst g hc h0, ← coe_substAlgHom hc, map_add (f := _), coe_substAlgHom, lg_subst g hc ha, lg_subst g hc hb]

theorem cc_add (hex : PowerSeries.constantCoeff g.ex = 0) {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : constantCoeff (g.add a b) = 0 :=
  cc_pt g hex (by rw [map_add (f := _), cc_lg g ha, cc_lg g hb, add_zero])

theorem be_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.be a b) = g.be (subst c a) (subst c b) := by
  have hab := cc_add g hex ha hb
  show subst c (g.phAt (g.add a b) - g.phAt a - g.phAt b) =
    g.phAt (g.add (subst c a) (subst c b)) - g.phAt (subst c a) - g.phAt (subst c b)
  rw [← coe_substAlgHom hc, map_sub, map_sub, coe_substAlgHom, phAt_subst g hc hab, phAt_subst g hc ha,
    phAt_subst g hc hb, add_subst g hex hc ha hb]

theorem dg_Cmul (ep : ℂ_[p]) (i : σ) :
    (diagS (PowerSeries.C ep * g.l) i : MvPowerSeries σ ℂ_[p]) = C ep * g.lg (X i) := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries σ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)
  unfold diagS G1.lg
  rw [← PowerSeries.smul_eq_C_mul, ← smul_eq_C_mul, ← PowerSeries.coe_substAlgHom hX, map_smul]

theorem cc_Cl (ep : ℂ_[p]) : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
  rw [map_mul, cc_l g, mul_zero]

end G1

section Lin

variable {Z E Kap : Type} {R : Type} [CommRing R]

end Lin

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVb
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem theta_injective_of_scalars (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (hI : Rows.IsotInternal D.what₂)
    (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    Function.Injective (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
  have hj' := Finset.mem_Icc.mp hj
  exact injective_of_scalars (D.what₂.isot (D.nd.j i)) (hI _ hj'.1 hj'.2) _ (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))
    (fun σ hσ => let ⟨lam, h0, hl⟩ := (h42 i σ hσ).1.1; ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩)

end Formalism.MainNotions.J

end
end

