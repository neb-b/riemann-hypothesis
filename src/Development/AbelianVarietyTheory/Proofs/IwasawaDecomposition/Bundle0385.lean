module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem mem_aboveF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)} :
    P ∈ aboveF (L := D.host.E) D.host.F v ↔ P.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

theorem absNorm_eq_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (h : (Ideal.absNorm P.asIdeal).Prime) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
  rw [mem_aboveF_iff] at hP
  subst hP
  have hd : Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.card_dvd_of_injective
      (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) le_rfl).toAddMonoidHom
      Ideal.quotientMap_injective
  exact ((Nat.dvd_prime h).1 hd).resolve_left fun h1 =>
    (P.under (𝓞 D.host.F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m)
    (h' : ¬ x ≤ WithZero.exp (m - 1)) : x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem degreeOne_of_prime_absNorm_not_mem_sq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (h1 : (Ideal.absNorm P.asIdeal).Prime) (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∉ P.asIdeal ^ 2) : Deg1 P := by
  refine ⟨h1, ?_⟩
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qP P : ℕ) : P.adicCompletion L) =
      algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L)) := by
    simp [qP]
  have hv : ∀ y : L, Valued.v (algebraMap L (P.adicCompletion L) y) = P.valuation L y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P y
  rw [e, hv, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (P.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hmem)
  have a2 : ¬ P.intValuation ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem _ 2).1 h)
  refine eq_exp_of_le (by simpa using a1) fun h => a2 ?_
  convert h using 2
  norm_num

theorem ramTransfer : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place

theorem finite_inQ (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {v : HeightOneSpectrum (𝓞 D.host.F) | Tp.InQ' μ v}.Finite := by
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).image fun w => w.under (𝓞 D.host.F)).subset ?_
  rintro v ⟨w, hw, hr⟩
  exact ⟨w, hr, mem_aboveF_iff.1 hw⟩

theorem prime_eq_of_overP {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h : ((a * p + b * q : ℤ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by exact_mod_cast h1))
      (w.asIdeal.mul_mem_left _ (by exact_mod_cast h2))
  rw [hab, Int.cast_one] at h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem finite_qp (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {p : ℕ | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}.Finite := by
  have hs : ∀ w : HeightOneSpectrum (𝓞 D.host.E), Set.Subsingleton {p : ℕ | p.Prime ∧ OverP D.host p w} :=
    fun w p hp q hq => prime_eq_of_overP hp.1 hq.1 hp.2 hq.2
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).biUnion fun w _ => (hs w).finite).subset ?_
  rintro p ⟨hp, w, hw, hr⟩
  exact Set.mem_biUnion hr ⟨hp, hw⟩

def qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Finset ℕ := (finite_qp Tp μ).toFinset

theorem mem_qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) (p : ℕ) :
    p ∈ qpSet Tp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w := by
  rw [qpSet, Set.Finite.mem_toFinset]; rfl

theorem ramifiedRationalPrimesOfTuple_baseTuple_eq_empty (Tp : TupTied D C nch) : qpSet Tp D.what₂.mu0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨-, w, -, hr⟩ := (mem_qpSet Tp _ p).1 hp
  exact hr fun x _ => by rw [Tp.trueColumnChoices_heckeChar_reference_eq_one]; rfl

theorem qpSet_muAt (Tp : TupTied D C nch) (hp : TupPins Tp) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w ∉ qpSet Tp (D.what₂.muAt w) := fun h => by
  obtain ⟨-, w', hw', hr⟩ := (mem_qpSet Tp _ _).1 h
  exact hr (hp.atl w w' hw')

theorem qpSet_g (Tp : TupTied D C nch) (hp : TupPins Tp) (μ : D.what₂.Tup) (i : Fin 2) :
    D.host.g i ∉ qpSet Tp μ := fun h => by
  obtain ⟨-, w, hw, hr⟩ := (mem_qpSet Tp _ _).1 h
  exact (hp.ram μ w hr).2.2.2 i hw

theorem one_lt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)


include hp hPv in
theorem ram_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ¬ (Tp.xi μ).UnrAt (Pv v.1) := by
  obtain ⟨w, hw, hr⟩ := v.2
  exact ramTransfer D C nch Tp hp μ v.1 w (Pv v.1) hw (hPv v.1) hr

include hp hPv in
theorem chosenPrimeAbove_ramifiedPlace_degreeOne (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : Deg1 (Pv v.1) :=
  degreeOne_of_prime_absNorm_not_mem_sq _ (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1 (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.1

include hp hPv in
theorem offg_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ∀ k, ¬ OverP D.host (D.host.g k) (Pv v.1) :=
  (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.2

include hp hPv in
theorem absNorm_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    Ideal.absNorm v.1.asIdeal = qP (Pv v.1) :=
  absNorm_eq_of_mem (hPv v.1) (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1

theorem one_le_letterBlockLength : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega


include hp hPv in
theorem stepEx (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) (j : ℕ) :
    (∃ n, TypeDimAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j n) ∧
      ∃ z, StepAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j z :=
  _root_.GlobalTheory.TypeStep.exists_typeDim_step D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _ (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v))
    (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v)) D.R.r D.R.t j one_le_letterBlockLength

def zq (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : ℕ → ℂ
  | 0 => 0
  | j + 1 => (stepEx Tp hp Pv hPv μ v j).2.choose

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}
variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)

def reQ (Z₀ : DivX D) : DivX D :=
  { Z₀ with
    Qp := qpSet Tp
    degreeZero_partial_set_empty := ramifiedRationalPrimesOfTuple_baseTuple_eq_empty Tp
    Qp_muAt := qpSet_muAt Tp hp
    Qp_g := fun μ _ i => qpSet_g Tp hp μ i
    QPl := fun μ => {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
    finQ := fun μ => by
      haveI : Finite {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v} := (finite_inQ Tp μ).to_subtype
      exact Fintype.ofFinite _
    qv := fun _ v => Ideal.absNorm v.1.asIdeal
    qv_gt := fun _ v => one_lt_absNorm v.1
    qv_char := fun μ _ v => by
      obtain ⟨w, hw, hr⟩ := v.2
      have hpr := (hp.ram μ w hr).2.1
      refine ⟨Ideal.absNorm v.1.asIdeal, (mem_qpSet Tp μ _).2 ⟨?_, w, ?_, hr⟩, ?_, rfl⟩
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
      · rw [absNorm_eq_of_mem hw hpr]; exact Ideal.absNorm_mem _
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
    nu := fun _ v i => ((nuP C (Pv v.1) i (piP (Pv v.1)) : ℂˣ) : ℂ)
    nu_ne := fun _ _ _ => Units.ne_zero _
    nu_abs := fun μ v i => (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) i).unitary _
    ZQ := zq Tp hp Pv hPv
    quotientLocalValueFirst := fun _ v => (zVal1 (qP (Pv v.1)) D.R.r D.R.t : ℂ)
    typeDim := fun μ v j => (stepEx Tp hp Pv hPv μ v j).1.choose }

def reducedDivisorCharacter (Z₀ : DivX D) : DivisorCharacterCompatibility D C nch Tp (reQ Tp hp Pv hPv Z₀) where
  Qp_iff := mem_qpSet Tp
  eQPl := fun _ => Equiv.refl _
  qv_eq := fun _ _ => rfl

theorem reLoc (Z₀ : DivX D) : QLocTiedC (reducedDivisorCharacter Tp hp Pv hPv Z₀) Pv := by
  refine ⟨fun μ v => hPv _, ?_⟩
  refine
    { qv_eq := fun μ v => absNorm_Pv Tp hp Pv hPv μ v
      deg1 := fun μ v => chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v
      ram := fun μ v => ram_Pv Tp hp Pv hPv μ v
      off_g := fun μ v => offg_Pv Tp hp Pv hPv μ v
      nu_eq := fun μ v i => ?_
      typeDim_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).1.choose_spec
      ZQ_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).2.choose_spec
      quotientLocalValueFirst_eq := fun μ v j _ _ => _root_.GlobalTheory.Mem.SingleQ.stepAt_one D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _
        (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v)) (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) j) D.R.r D.R.t one_le_letterBlockLength }
  show ((nuP C (Pv v.1) (i.1 + 1) (piP (Pv v.1)) : ℂˣ) : ℂ) = _
  rw [nuP_succ]
  rfl

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

end GlobalTheory.Mem.HD.ReQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardFrameConjugateClose
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.StdFrames GlobalTheory.AdIsom GlobalTheory.IdemSupport

namespace GlobalTheory.ConjLt
variable {D : D7}

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨n, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
    have : (n : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd n) := rfl
    rw [this, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [this, WithZero.exp_le_exp]
    omega

theorem cpt_sg_lt_one (Q : Pl D.host.E) (z : EAf D) (h : Valued.v (cpt Q z) < 1) :
    Valued.v (cpt (cP Q) (sg D z)) < 1 := by
  obtain ⟨π, hπ⟩ := Q.intValuation_exists_uniformizer
  set p : D.host.E := (π : D.host.E) with hp
  have hvp : Valued.v (cpt Q (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p)) = WithZero.exp (-1) := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap, hp, ← hπ]
    exact Q.valuation_of_algebraMap π
  have hp0 : p ≠ 0 := by
    rintro h0
    rw [h0, map_zero, map_zero, map_zero] at hvp
    exact WithZero.exp_ne_zero hvp.symm
  set a := z * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p⁻¹ with ha
  have hza : z = a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p := by
    rw [ha, mul_assoc, ← map_mul, inv_mul_cancel₀ hp0, map_one, mul_one]
  have hva : Valued.v (cpt Q a) ≤ 1 := by
    have e1 : Valued.v (cpt Q a) * WithZero.exp (-1) = Valued.v (cpt Q z) := by
      rw [← hvp, ← Valuation.map_mul, ← map_mul, ← hza]
    have e2 := lt_one_le_exp h
    rw [← e1] at e2
    by_contra hc
    push_neg at hc
    have : WithZero.exp (-1) < Valued.v (cpt Q a) * WithZero.exp (-1) := by
      calc WithZero.exp (-1) = 1 * WithZero.exp (-1) := (one_mul _).symm
        _ < _ := mul_lt_mul_of_pos_right hc (WithZero.exp_pos)
    exact absurd e2 (not_le.2 this)
  have h1 := (cpt_cjA_le_iff Q a).2 hva
  have hs : sg D z = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p) := by
    rw [hza, map_mul]; rfl
  have h2 : Valued.v (cpt (cP Q) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p))) < 1 := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]
    have e : star p = ((cO D π : 𝓞 D.host.E) : D.host.E) := rfl
    rw [e, (cP Q).valuation_lt_one_iff_mem, mem_cP, cO_cO, ← Q.intValuation_lt_one_iff_mem, hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  rw [hs, map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h1) h2

theorem conj_sub_one {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (β x : GL (Fin n) A)
    (R U' : Matrix (Fin n) (Fin n) A) (hX : Formalism.UG.cT σ x.val * R * x.val = R)
    (hU : U' * (Formalism.UG.cT σ β.val * R * β.val) = 1) :
    (β⁻¹ * x * β).val - 1 = U' * (Formalism.UG.cT σ (β⁻¹ * x⁻¹ * β).val - 1) * (Formalism.UG.cT σ β.val * R * β.val) := by
  set G := Formalism.UG.cT σ β.val * R * β.val with hG
  set Y := (β⁻¹ * x * β).val with hYdef
  set Yi := (β⁻¹ * x⁻¹ * β).val with hYidef
  have hYYi : Y * Yi = 1 := by
    rw [hYdef, hYidef, ← Units.val_mul]
    rw [show β⁻¹ * x * β * (β⁻¹ * x⁻¹ * β) = 1 by group, Units.val_one]
  have hY : Y = (β⁻¹).val * x.val * β.val := by rw [hYdef, Units.val_mul, Units.val_mul]
  have c1 : ∀ Z : Matrix (Fin n) (Fin n) A, Formalism.UG.cT σ (β⁻¹).val * (Formalism.UG.cT σ β.val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← cT_mul', Units.mul_inv, cT_one', Matrix.one_mul]
  have c2 : ∀ Z : Matrix (Fin n) (Fin n) A, β.val * ((β⁻¹).val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hUY : Formalism.UG.cT σ Y * G * Y = G := by
    rw [hY, hG, cT_mul', cT_mul']
    simp only [Matrix.mul_assoc, c1, c2]
    rw [show Formalism.UG.cT σ x.val * (R * (x.val * β.val)) = (Formalism.UG.cT σ x.val * R * x.val) * β.val by
        simp only [Matrix.mul_assoc], hX]
  have hGY : G * Y = Formalism.UG.cT σ Yi * G := by
    have := congrArg (fun Z => Formalism.UG.cT σ Yi * Z) hUY
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul', hYYi, cT_one', Matrix.one_mul]
  have e1 : Y = U' * (G * Y) := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  calc Y - 1 = U' * (G * Y) - U' * G := by rw [← e1, hU]
    _ = U' * (Formalism.UG.cT σ Yi * G) - U' * G := by rw [hGY]
    _ = U' * (Formalism.UG.cT σ Yi - 1) * G := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc]

theorem frame_mat_sub_one_lt : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V β Λ N hSD g Q h a b
  obtain ⟨hGi, U', hU'i, hU'⟩ := unimod_of_isSD hSD
  have hX : Formalism.UG.cT (sg D) (finE V g).val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * (finE V g).val =
      GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram := GlobalTheory.LevSplit.finE_mem_UA V g
  have hYsub := conj_sub_one (sg D) β (finE V g) _ U' hX hU'
  have hM : ∀ i j, Valued.v (cpt (cP Q) ((Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j)) < 1 := by
    intro i j
    have e : (Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j =
        sg D ((β⁻¹ * (finE V g)⁻¹ * β).val j i - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) j i) := by
      simp only [Formalism.UG.cT, Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
    rw [e]
    exact cpt_sg_lt_one Q _ (h j i)
  have hint : ∀ x ∈ GlobalTheory.StdFrames.OA D, Valued.v (cpt (cP Q) x) ≤ 1 := fun x hx => (mem_OA x).1 hx (cP Q)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.sub_apply, hYsub, Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_lt' _ zero_lt_one fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, Valuation.map_mul, Matrix.mul_apply, map_sum]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' (hint _ (hGi j b))) ?_
  refine Valuation.map_sum_lt' _ zero_lt_one fun i _ => ?_
  rw [map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _ (hU'i a i))) (hM i j)

end GlobalTheory.ConjLt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharacters
section
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.HCChar

open Formalism.IrreducibleCountingLemmas.TYPES

theorem trace_hcRep_eq_hcL : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b →
    ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
      (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x := by
  intro g _ r s b lam _ x
  classical
  have h1 : LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x) =
      (Representation.coind (parab (ZMod g) b).subtype (PI.SerBridgeGLW.inflRep (ZMod g) b lam)).character x := rfl
  rw [h1, GlobalTheory.GoodTypeGeneric.character_coind_eq_ind]
  let d : Fin s → ℕ := fun c => Fintype.card {i // b i = c}
  let α : ∀ c, GlobalTheory.GLq.Gn g (d c) → ℂ := fun c y => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character y
  let j : ∀ c, Fin (d c) → Fin r := fun c t => ((Fintype.equivFin {i // b i = c}).symm t).1
  obtain ⟨σ, hσ1, -, hσ3, hσ4⟩ := GlobalTheory.TypeCharProduct.exists_enum b d α j
    (fun c => Subtype.val_injective.comp (Equiv.injective _))
    (fun c t => ((Fintype.equivFin {i // b i = c}).symm t).2)
    (fun i => ⟨Fintype.equivFin {k // b k = b i} ⟨i, rfl⟩, by simp [j]⟩)
    (List.finRange s) (List.pairwise_lt_finRange s)
  have hL : GlobalTheory.SerCmp.canonList b lam = (List.finRange s).map fun c => (⟨d c, α c⟩ : GlobalTheory.GLq.Pc g) := rfl
  rw [hL, ← GlobalTheory.TypeCharProduct.ind_eq_hcL _ ?_ r σ ⟨hσ1, fun i => hσ3 i (List.mem_finRange _)⟩
    (fun y => y ∈ parab (ZMod g) b)
    (fun y => if h : y ∈ parab (ZMod g) b then (PI.SerBridgeGLW.inflRep (ZMod g) b lam).character ⟨y, h⟩ else 0)
    ?_ ?_]
  · unfold GlobalTheory.BI.ind GlobalTheory.TypeCharProduct.ind
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold GlobalTheory.BI.ext0
    beta_reduce
    by_cases h : y⁻¹ * x * y ∈ parab (ZMod g) b
    · rw [dite_eq_left h, if_pos h]
    · rw [dite_eq_right h, if_neg h]
  · intro q hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    intro y z
    exact FDRep.char_conj _ y z
  · intro y
    rw [(hσ4 _).1, GlobalTheory.HCInduction.parab_eq_blockTri]
    show Matrix.BlockTriangular _ _ ↔ _
    simp only [List.mem_finRange, true_implies]
    exact ⟨fun h i k hik => h hik, fun h i k hik => h i k hik⟩
  · intro y hy
    rw [dite_eq_left hy, (hσ4 _).2, ← Fin.prod_univ_def]
    show LinearMap.trace ℂ _ (PiTensorProduct.map fun c => (lam c).ρ (levi (ZMod g) b c ⟨y, hy⟩)) = _
    rw [PI.SerBridgeGLW.trace_piTensorMap]
    refine Finset.prod_congr rfl fun c _ => ?_
    have hu : (y : Matrix (Fin r) (Fin r) (ZMod g)).submatrix (j c) (j c) =
        ((glEquiv (ZMod g) (Fintype.equivFin {i // b i = c}) (levi (ZMod g) b c ⟨y, hy⟩) : GL _ (ZMod g)) :
          Matrix _ _ (ZMod g)) := by
      ext t t'
      simp [glEquiv, levi, blk, j, Matrix.reindexAlgEquiv]
    have hg : GlobalTheory.GLq.toG ((y : Matrix (Fin r) (Fin r) (ZMod g)).submatrix (j c) (j c)) =
        glEquiv (ZMod g) (Fintype.equivFin {i // b i = c}) (levi (ZMod g) b c ⟨y, hy⟩) := by
      apply Units.ext
      rw [GlobalTheory.TypeCharProduct.coe_toG (by rw [hu]; exact Units.isUnit _), hu]
    show _ = (transp (Fintype.equivFin {i // b i = c}) (lam c)).character _
    rw [hg]
    show _ = LinearMap.trace ℂ _ ((lam c).ρ ((glEquiv (ZMod g) (Fintype.equivFin {i // b i = c})).symm _))
    rw [MulEquiv.symm_apply_apply]

end GlobalTheory.HCChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistResidueCharacterComplexEqLevelCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.LevResXi

theorem embLL_resChar_eq_xiR : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (t : TupU I U) (w : Pl X.toD7.host.E),
      w ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) → ∀ (u : (kP w)ˣ),
      X.toD7.what₂.embLL ((Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) w u :
        X.B.fields.Kˣ) : X.B.fields.K) = ((L.xiR t w u : ℂˣ) : ℂ) := by
  intro X px I U L hI hV hL t w hw u
  rw [xiR_eq_map_resChar X px I U L hI hV hL t w hw u]
  rfl

end GlobalTheory.Mem.LevResXi
end

