module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Formalism.LocalToGlobal.Columns.BaseInst
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Divisibility.CoeffLemmas
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0004
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0004
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Formalism.LocalToGlobal.Columns.LevGCount
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Formalism.LogVandermondeBounds.Bundle0001
public import Formalism.LogVandermondeBounds.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.AtTOwedC
section
open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Res

variable {A : Type} [CommRing A] [Finite A] {p : ℕ}

def owedC_res (hp : p.Prime) (h : Nat.card A = p) : A ≃+* ZMod p :=
  letI := Fintype.ofFinite A
  (ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card]; exact h)).symm

theorem owedC_res_intCast (hp : p.Prime) (h : Nat.card A = p) (a : ℤ) :
    owedC_res hp h (a : A) = (a : ZMod p) := map_intCast _ _

theorem owedC_exists_int (hp : p.Prime) (h : Nat.card A = p) (x : A) : ∃ a : ℤ, x = (a : A) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨((owedC_res hp h x).val : ℤ), ?_⟩
  apply (owedC_res hp h).injective
  rw [owedC_res_intCast]
  simp

theorem owedC_intCast_eq_iff (hp : p.Prime) (h : Nat.card A = p) (a b : ℤ) :
    (a : A) = (b : A) ↔ (p : ℤ) ∣ a - b := by
  rw [← (owedC_res hp h).injective.eq_iff, owedC_res_intCast, owedC_res_intCast,
    ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]

variable {K : Type} [Field K]

end Res

section Chars

variable {X : Fields} {Pr : Primes X}

theorem card_quotient_eq_prime (hPr : Pr.Ok) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
  rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Chars

section Weil

variable {X : Fields} {Pr : Primes X}

def CharT.psiC (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    AddChar (𝓞 X.E ⧸ P.1.asIdeal) ℂ :=
  (σ₀ : X.K →* ℂ).compAddChar (Ps.psiT u P)

theorem CharT.psiC_apply (Ps : CharT X Pr) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u})
    (c : 𝓞 X.E ⧸ P.1.asIdeal) : Ps.psiC σ₀ u P c = σ₀ (Ps.psiT u P c) := rfl

theorem CharT.Ok.psiC_ne {Ps : CharT X Pr} (h : Ps.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (P : {P // P ∈ Pr.vT u}) :
    Ps.psiC σ₀ u P ≠ 1 := by
  intro h1
  apply h.ne u P
  ext c
  apply σ₀.injective
  rw [← CharT.psiC_apply, h1, AddChar.one_apply, AddChar.one_apply, map_one]

end Weil

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end Gauss

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.BaseHost
section
open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)


end Host

section Host2

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)



variable (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (hE : H.EQ ≤ LL)




end Host2

section Host3

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)
variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)


end Host3

theorem ram_conj_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hrank : Module.finrank F E = 2) (c : 𝓞 E →+* 𝓞 E) (hcc : ∀ x, c (c x) = x)
    (hcF : ∀ a : 𝓞 F, c (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a)
    (P : HeightOneSpectrum (𝓞 E))
    (hP : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) (x : 𝓞 E) :
    c x - x ∈ P.asIdeal := by
  classical
  set p : Ideal (𝓞 F) := P.asIdeal.under (𝓞 F) with hp
  have hPmax : P.asIdeal.IsMaximal := P.isMaximal
  have hPprime : P.asIdeal.IsPrime := P.isPrime
  have hpmax : p.IsMaximal := Ideal.IsMaximal.under (𝓞 F) P.asIdeal
  have hp0 : p ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P.ne_bot
  have hlies : P.asIdeal.LiesOver p := ⟨rfl⟩
  have hmap0 : p.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).not.2 hp0

  let Q : Ideal (𝓞 E) := P.asIdeal.comap c
  have hQprime : Q.IsPrime := Ideal.comap_isPrime c P.asIdeal
  have hQlies : Q.LiesOver p := by
    refine ⟨?_⟩
    ext a
    show a ∈ p ↔ c (algebraMap (𝓞 F) (𝓞 E) a) ∈ P.asIdeal
    rw [hcF]
    rfl
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hfr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← hrank]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hfr] at hsum
  have he : 2 ≤ P.asIdeal.ramificationIdx (𝓞 F) := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P.asIdeal hmap0]
    have hfin : FiniteMultiplicity P.asIdeal (p.map (algebraMap (𝓞 F) (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (fun h => hPprime.ne_top (Ideal.isUnit_iff.1 h)) hmap0
    exact hfin.le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.2 hP)
  have hfP : 0 < P.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos P.asIdeal (𝓞 F)
  have hfQ : 0 < Q.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos Q (𝓞 F)
  have heQ : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) Q
  let P' : p.primesOver (𝓞 E) := ⟨P.asIdeal, hPprime, hlies⟩
  let Q' : p.primesOver (𝓞 E) := ⟨Q, hQprime, hQlies⟩

  have hQP : Q = P.asIdeal := by
    by_contra hne
    have hne' : Q' ≠ P' := fun h => hne (congrArg Subtype.val h)
    have h2 : ∑ q ∈ ({P', Q'} : Finset (p.primesOver (𝓞 E))), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) ≤
        ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne'.symm, hsum] at h2
    have h3 : 2 ≤ P.asIdeal.ramificationIdx (𝓞 F) * P.asIdeal.inertiaDeg (𝓞 F) := by nlinarith
    have h4 : 1 ≤ Q.ramificationIdx (𝓞 F) * Q.inertiaDeg (𝓞 F) := Nat.mul_pos heQ hfQ
    have h5 : P'.1 = P.asIdeal := rfl
    have h6 : Q'.1 = Q := rfl
    rw [h5, h6] at h2
    omega

  have hf1 : P.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    have h2 : P'.1.ramificationIdx (𝓞 F) * P'.1.inertiaDeg (𝓞 F) ≤
        ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) :=
      Finset.single_le_sum (f := fun q : p.primesOver (𝓞 E) => q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ P')
    rw [hsum] at h2
    have h5 : P'.1 = P.asIdeal := rfl
    rw [h5] at h2
    nlinarith
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P.asIdeal] at hf1
  let : Field (𝓞 F ⧸ p) := Ideal.Quotient.field p
  let : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  obtain ⟨a', ha'⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 E ⧸ P.asIdeal) one_ne_zero).1 hf1 (Ideal.Quotient.mk P.asIdeal x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  have hxa : x - algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq, ← ha', Algebra.smul_def, mul_one]
    rfl
  have hc : c (x - algebraMap (𝓞 F) (𝓞 E) a) ∈ P.asIdeal := by
    rw [← hQP]
    show c (c (x - algebraMap (𝓞 F) (𝓞 E) a)) ∈ P.asIdeal
    rw [hcc]
    exact hxa
  rw [map_sub, hcF] at hc
  have := P.asIdeal.sub_mem hc hxa
  have e : c x - algebraMap (𝓞 F) (𝓞 E) a - (x - algebraMap (𝓞 F) (𝓞 E) a) = c x - x := by ring
  rwa [e] at this

theorem Fields.Ok.ram_conj {X : Fields} (h : X.Ok) (P : HeightOneSpectrum (𝓞 X.E))
    (hP : (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2) (x : 𝓞 X.E) :
    X.conjO x - x ∈ P.asIdeal := by
  refine ram_conj_mem h.rankE X.conjO ?_ ?_ P hP x
  · intro y
    apply RingOfIntegers.ext
    show star (star (y : X.E)) = y
    exact star_star _
  · intro a
    apply RingOfIntegers.ext
    exact h.star_F (a : X.F)

theorem Fields.Ok.unram_of_inertia {X : Fields} (h : X.Ok)
    (hin : ∀ P : HeightOneSpectrum (𝓞 X.E), ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2 :=
  fun hP => hin P (h.ram_conj P hP)

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ExistsUnitOfPowEqOne
section
open Polynomial CategoryTheory NumberField

noncomputable section

namespace Formalism.L2.Col

section Rep

variable {Γ : Type} [Group Γ] [Fintype Γ]

end Rep

section Series

variable {g : ℕ} [Fact g.Prime]

end Series

section Assemble

theorem residueField_equiv_zmod {X : Fields} (w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.E)) (g : ℕ) [Fact g.Prime]
    (hw : Ideal.absNorm w.asIdeal = g) : Nonempty ((𝓞 X.E ⧸ w.asIdeal) ≃+* ZMod g) := by
  have hc : Nat.card (𝓞 X.E ⧸ w.asIdeal) = g := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 X.E ⧸ w.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : g.Prime).ne_zero)
  letI : Fintype (𝓞 X.E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc' : Fintype.card (𝓞 X.E ⧸ w.asIdeal) = g := by rw [← Nat.card_eq_fintype_card, hc]
  have : CharP (𝓞 X.E ⧸ w.asIdeal) g := charP_of_card_eq_prime hc'
  exact ⟨(ZMod.ringEquiv _ hc').symm⟩

def generalLinearEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (r : ℕ) (e : R ≃+* S) : GL (Fin r) R ≃* GL (Fin r) S :=
  Units.mapEquiv (e.mapMatrix (m := Fin r)).toMulEquiv

end Assemble

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RowFormsSel
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.EigenvalueLevelCeiling

section Sel

variable {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem rf_tup_fin : (Qprime (mu : Chr X.F X.E X.K)).Finite :=
  auxiliary_primes_finite X.F X.E X.K _ ((mem_tupGrp (mu : Chr X.F X.E X.K)).mp mu.2).1.2.1

theorem mem_QE (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ QE sel (mu : Chr X.F X.E X.K) ↔ ∃ v ∈ Qprime (mu : Chr X.F X.E X.K), sel v = P := by
  unfold QE
  rw [dite_eq_left (rf_tup_fin mu)]
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]

variable {sel}

end Sel

section Disj

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)


open Classical in
theorem QE_disj (hP : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) (w : HeightOneSpectrum (𝓞 X.E))
    (hw : w ∈ Pr.vGs) : w ∉ QE sel (mu : Chr X.F X.E X.K) := by
  intro hQ
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu w).mp hQ
  have hg : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
    have key : ∀ i, sel v ∈ Pr.vG i → ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
      intro i hi
      have h0 : X.conjO (Pr.piG i) ≠ 0 := by
        intro h0
        have := hP.piG_norm i
        rw [h0, mul_zero] at this
        exact (Nat.cast_ne_zero.mpr (hP.g_prime i).ne_zero) this.symm
      rw [← hP.piG_norm i]
      exact Ideal.mul_mem_left _ _ ((mem_divs h0 _).mp hi)
    rcases Finset.mem_union.mp hw with h | h
    · exact ⟨0, key 0 h⟩
    · exact ⟨1, key 1 h⟩
  obtain ⟨i, hi⟩ := hg
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v]
    show algebraMap (𝓞 X.F) (𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal
    rw [map_natCast]
    exact hi
  have h2 : plc v ∣ Pr.g i := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
    exact (ringChar.spec _ _).mp h1
  have hpp : (plc v).Prime := by
    have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : v.asIdeal.IsPrime := v.isPrime
    exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
  have h3 : plc v = Pr.g i := (Nat.prime_dvd_prime_iff_eq hpp (hP.g_prime i)).mp h2
  exact (mu.good hv).2.2 (h3 ▸ hS i)

end Disj

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RowFormsSym
section
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section RBlockSym

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def rPsymF : LevFam X.E X.K R.r Pr.vGs := fun w =>
  ⟨HPsymF (𝓞 X.E ⧸ w.1.asIdeal) R.r R.k R.rS, chiSymF (Ch.psi0 w) R.r R.k R.rS⟩

theorem rowTyG_PsymF_H (w : {w // w ∈ Pr.vGs}) :
    (rowTyG Ch (rPsymF Ch) w).H = HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := rfl

end RBlockSym

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.SmulMemTrpSet
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Coord

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

structure CoordAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, co (x + y) = co x + co y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, co (a • x) = Ideal.Quotient.mk P.asIdeal a • co x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → co x = 0
  surj : ∀ c, ∃ x ∈ N, co x = c
  ker : ∀ x ∈ N, co x = 0 → x ∈ P.asIdeal • N

structure FunAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, f (x + y) = f x + f y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, f (a • x) = Ideal.Quotient.mk P.asIdeal a * f x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → f x = 0

def coF {P : HeightOneSpectrum (𝓞 E)} (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) (c : Fin n → 𝓞 E ⧸ P.asIdeal)
    (y : Sp E n) : 𝓞 E ⧸ P.asIdeal := ∑ i, c i * co y i

def dualV {κ : Type} [CommRing κ] (x : Fin n → κ) : Fin n → κ := Classical.epsilon fun c => ∑ i, c i * x i = 1

def liftV {P : HeightOneSpectrum (𝓞 E)} (N : Submodule (𝓞 E) (Sp E n)) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.asIdeal) : Sp E n := Classical.epsilon fun y => y ∈ N ∧ co y = x

end Coord

section Fib

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.fibF (d : Deco E n ST SG) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : Deco E n ST SG := d.repl P d.N (coF co c)

def DecoSet.fibF (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) :=
  open Classical in if h : (d.1.fibF P co c).Ok then ⟨_, h⟩ else d

def DecoSet.fibX (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 E) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) :=
  (d.fibF P co (dualV x)).up P q (liftV d.1.N co x)

structure SepElt (ST : Finset (HeightOneSpectrum (𝓞 E))) (a : 𝓞 E) : Prop where
  conj : ∀ P : ST, cO (E := E) a ∈ P.1.asIdeal
  off : ∀ P : ST, a ∉ P.1.asIdeal

end Fib

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

variable {C Λ}

def resX {R : Type} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (P : ST) (q : 𝓞 X.E)
    (co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)) (ℓ : C.V → R) (φ : (formGSD C Λ).EqFun) :
    (Fin n → 𝓞 X.E ⧸ P.1.asIdeal) → R :=
  fun x => ℓ ((φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.fibX P q co x))

end Ops

@[reducible] def resField {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal

@[reducible] def resFintype {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _

section Below

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ} (emb : ι → E →+* K)

def SameBelow (w : HeightOneSpectrum (𝓞 K)) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ τ, (∀ x ∈ L, ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L') ∧
    ∀ x ∈ L', ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L

end Below

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end Cols

end Formalism.L2.Col
end
end

