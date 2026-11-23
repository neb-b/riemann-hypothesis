module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDir
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_char {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (T : CDVR) (io : c.F →+* T.Fr) (σ : E →+* ℂ) :
    ∃ χ : 𝓞 E →+* T.V, ∀ a : 𝓞 E, algebraMap T.V T.Fr (χ a) = io (embK c σ a) := by
  have hint : ∀ a : 𝓞 E, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c σ a) := by
    intro a
    have h1 : IsIntegral T.V ((io.comp (embK c σ)) a) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom T.V) (io.comp (embK c σ)) (RingHom.ext_int _ _)
        (RingOfIntegers.isIntegral a)
    exact IsIntegrallyClosed.isIntegral_iff.1 h1
  choose χ hχ using hint
  refine ⟨{ toFun := χ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hχ⟩ <;>
    intros <;> apply IsFractionRing.injective T.V T.Fr <;> simp [hχ]

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEigPf
section
noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem linEigSt_holds : LinEigSt := LinEig.linEig_holds

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RPfVal

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Pj.Crude Formalism.MainNotions.ModuliIntegralCharts.H1

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem vLa_int_not_mem {a : 𝓞 K} (ha : a ∉ la.asIdeal) : vLa la (a : K) = 0 := by
  have h : (a : K) = algebraMap (𝓞 K) K a := rfl
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 ha]
  simp

theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hl := resCharOf_prime la
    have hnd : ¬ resCharOf la ∣ p := fun hd =>
      hne ((Nat.prime_dvd_prime_iff_eq hl hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

theorem padic_prime (l : ℕ) [Fact l.Prime] {p : ℕ} (hp : p.Prime) :
    padicValNat l p = if l = p then 1 else 0 := by
  rw [Nat.padicValNat_def]
  split_ifs with h
  · subst h; exact Nat.multiplicity_self hp.one_lt
  · have : Fact p.Prime := ⟨hp⟩
    exact multiplicity_primes h

theorem vLa_pPow {Q q d : ℕ} (hQ : Q ≠ 0) (hq : q.Prime) (hd : d.Prime) (a b c : ℕ) :
    vLa la (((Q ^ a * q ^ b * d ^ c : ℕ) : ℕ) : K) =
      (((a * padicValNat (resCharOf la) Q + b * (if resCharOf la = q then 1 else 0) +
        c * (if resCharOf la = d then 1 else 0)) * ramOverZ la : ℕ) : ℤ) := by
  have hl := resCharOf_prime la
  have : Fact (resCharOf la).Prime := ⟨hl⟩
  have h2 : (Q ^ a : ℕ) ≠ 0 := pow_ne_zero _ hQ
  have hq' : (q ^ b : ℕ) ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hd' : (d ^ c : ℕ) ≠ 0 := pow_ne_zero _ hd.ne_zero
  rw [crv_vLa_natCast la (Nat.mul_ne_zero (Nat.mul_ne_zero h2 hq') hd')]
  congr 2
  have e1 : padicValNat (resCharOf la) (Q ^ a) = a * padicValNat (resCharOf la) Q := by
    simp only [Nat.padicValNat_def, Nat.multiplicity_pow]
  have e2 : padicValNat (resCharOf la) (q ^ b) = b * padicValNat (resCharOf la) q := by
    simp only [Nat.padicValNat_def, Nat.multiplicity_pow]
  have e3 : padicValNat (resCharOf la) (d ^ c) = c * padicValNat (resCharOf la) d := by
    simp only [Nat.padicValNat_def, Nat.multiplicity_pow]
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.mul_ne_zero h2 hq') hd', (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) h2 hq', e1, e2, e3,
    padic_prime _ hq, padic_prime _ hd]

theorem nat_mem_iff (n : ℕ) : ((n : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la ∣ n := by
  constructor
  · intro hm
    by_contra hnd
    exact crv_not_mem la hnd hm
  · rintro ⟨k, rfl⟩
    push_cast
    exact la.asIdeal.mul_mem_right _ (crv_char_mem la)

variable {D : D7} {j : ℕ}

theorem piG_mul_bar (EX : ErrX D) (i : Fin 2) :
    EX.piG i * piBarO EX i = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
  apply RingOfIntegers.coe_injective
  have h := EX.piG_norm i
  push_cast
  exact h

theorem nnW_not_mem (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∉ la.asIdeal) :
    nnW B hinj EX w ∉ la.asIdeal := by
  have hπ : ∀ i, iE D hinj B (EX.piG i) ∉ la.asIdeal ∧ iE D hinj B (piBarO EX i) ∉ la.asIdeal := by
    intro i
    have hn : iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 B.KO) := by
      rw [← map_mul, piG_mul_bar, map_natCast]
    exact ⟨fun hm => hg i (hn ▸ la.asIdeal.mul_mem_right _ hm),
      fun hm => hg i (hn ▸ la.asIdeal.mul_mem_left _ hm)⟩
  have : nnW B hinj EX w ∈ la.asIdeal.primeCompl := by
    unfold nnW
    exact Submonoid.prod_mem _ fun i _ =>
      Submonoid.mul_mem _ (Submonoid.pow_mem _ (hπ i).1 _) (Submonoid.pow_mem _ (hπ i).2 _)
  exact this

theorem vAdd_sW (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∉ la.asIdeal) :
    ((vAdd la (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) : ℤ) : ℝ) =
      (ramOverZ la : ℝ) * clOf w la := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hq2 : D.host.q ≠ 2 := by omega
  have hd2 : D.host.d ≠ 2 := by omega
  have hqd : D.host.q ≠ D.host.d := by omega
  have hnn := nnW_not_mem B hinj EX w la hg
  have hnn0 : ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 := fun h =>
    hnn ((NumberField.RingOfIntegers.coe_eq_zero_iff.1 h) ▸ la.asIdeal.zero_mem)
  have hP : pPow D (c2 D w) (cHalf w) (cHalf w) = D.host.QS ^ c2 D w * D.host.q ^ cHalf w * D.host.d ^ cHalf w := rfl
  have hN0 : ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) ≠ 0 := by
    rw [hP]
    exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
      (pow_ne_zero _ hd.ne_zero)
  have hc : (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) =
      ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) := by
    show algebraMap (𝓞 B.KO) B.KO _ = _
    rw [map_mul, map_natCast]
  show ((vLa la _ : ℤ) : ℝ) = _
  rw [hc, crv_vLa_mul la hnn0 hN0, vLa_int_not_mem la hnn, hP, vLa_pPow la D.host.QS_pos.ne' hq hd]
  unfold clOf
  rw [show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
  simp only [nat_mem_iff la D.host.QS, prime_mem_iff la hq, prime_mem_iff la hd]
  by_cases hS : resCharOf la ∣ D.host.QS
  · have h1 : resCharOf la ≠ D.host.q := fun h => D.host.q_not_dvd_QS (h ▸ hS)
    have h2 : resCharOf la ≠ D.host.d := fun h => D.host.d_not_dvd_QS (h ▸ hS)
    rw [if_pos hS, if_neg h1, if_neg h2]
    generalize padicValNat (resCharOf la) D.host.QS = m
    push_cast; ring
  · rw [if_neg hS, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hS]
    split_ifs <;> (try (exfalso; omega)) <;> (try (exfalso; tauto)) <;> push_cast <;> ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.RPfVal
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

namespace H1algLink

open Formalism.L2.Pj.Crude

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem liesOver_resChar : la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := resCharOf_prime la
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ la.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) ((resCharOf la : ℕ) : ℤ) ∈ la.asIdeal
    rw [map_natCast]
    exact crv_char_mem la
  have hne : la.asIdeal.under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ la.asIdeal.under ℤ := by rw [h]; trivial
    change algebraMap ℤ (𝓞 K) 1 ∈ la.asIdeal at h1
    rwa [map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem span_resChar_ne_bot : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (resCharOf_prime la).ne_zero

theorem eWL_eq : eWL K la = ramOverZ la := by
  have := liesOver_resChar la
  unfold eWL ramOverZ
  exact (Ideal.ramificationIdx'_eq_ramificationIdx _ _ (span_resChar_ne_bot la)).symm

theorem ramOverZ_ne_zero : ramOverZ la ≠ 0 := by
  have := liesOver_resChar la
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la.asIdeal (span_resChar_ne_bot la)

theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hnd : ¬ resCharOf la ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq (resCharOf_prime la) hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

variable {D : D7}

end H1algLink


end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

