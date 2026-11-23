module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0132
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResLoc

open GlobalTheory.IdemSupport Formalism.L2.JoinChr Formalism.L2.Host

theorem val_alg {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem le_exp_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem locK_eq_of_tame {E : Type} [Field E] [NumberField E] (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (ht : χ.TameAt P) (k l : Eˣ) (hk : P.valuation E (k : E) = 1) (hl : P.valuation E (l : E) = 1)
    (h : P.valuation E ((k : E) - l) ≤ WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.locK P l := by
  have h1 : χ.locK P (k * l⁻¹) = 1 := by
    refine ht (atFin P (k * l⁻¹)) ?_ ?_
    · change Valued.v (algebraMap E (P.adicCompletion E) ((k * l⁻¹ : Eˣ) : E)) = 1
      rw [val_alg, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hk, hl, inv_one, one_mul]
    · change Valued.v (algebraMap E (P.adicCompletion E) ((k * l⁻¹ : Eˣ) : E) - 1) ≤ _
      have e : ((k * l⁻¹ : Eˣ) : E) - 1 = ((k : E) - l) * (l : E)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ l.ne_zero]
      rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub, val_alg, e, map_mul, map_inv₀, hl, inv_one,
        mul_one]
      exact h
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem exists_lift_lt_one {R T O K Γ : Type} [CommRing R] [CommRing T] [CommRing O] [CommRing K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (t : R →+* T) (ev : R →+* K) (S : Subring T) (o : O →+* S)
    (I : Ideal O) (hs : ∀ s : T, ∃ z, t z = s) (hint : ∀ z, t z ∈ S → v (ev z) ≤ 1)
    (hI : ∀ a ∈ I, ∃ z, t z = o a ∧ v (ev z) < 1) (s : S) (h : s ∈ I.map o) : ∃ z, t z = s ∧ v (ev z) < 1 := by
  refine Submodule.span_induction (p := fun (s : S) _ => ∃ z, t z = s ∧ v (ev z) < 1) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  · exact ⟨0, map_zero _, by rw [map_zero, map_zero]; exact zero_lt_one⟩
  · rintro x y _ _ ⟨z, hz, h⟩ ⟨z', hz', h'⟩
    refine ⟨z + z', by rw [map_add (f := _), hz, hz']; rfl, ?_⟩
    rw [map_add (f := _)]
    exact Valuation.map_add_lt _ h h'
  · rintro c x _ ⟨z, hz, h⟩
    obtain ⟨w, hw⟩ := hs c
    refine ⟨w * z, by rw [map_mul, hz, hw]; rfl, ?_⟩
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint w (hw ▸ c.2))) h

theorem map_eq_one_of_supp {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {e x y k : R} (he : f e = 0)
    (hx : e * (x - 1) = x - 1) (hy : x = y * (1 + e * (k - 1))) : f y = 1 := by
  have h1 := congrArg f hx
  have h2 := congrArg f hy
  simp only [map_mul, map_add (f := _), map_sub, map_one, he, zero_mul, add_zero, mul_one] at h1 h2
  rw [← h2, ← sub_eq_zero, ← h1]

theorem map_eq_mul_of_supp {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {e x y k : R} (he : f e = 1)
    (hy : x = y * (1 + e * (k - 1))) : f x = f y * f k := by
  rw [hy]
  simp only [map_mul, map_add (f := _), map_sub, map_one, he]
  ring

theorem exists_units_quot {R : Type} [CommRing R] (x l : Rˣ) {r : R} (hl : (l : R) = r) :
    ∃ y : Rˣ, x = y * l ∧ (x : R) = y * r :=
  ⟨x * l⁻¹, (inv_mul_cancel_right x l).symm, by rw [← hl, ← Units.val_mul, inv_mul_cancel_right]⟩

variable {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

def evAt (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E :=
  (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.adicCompletion D.host.E) Q).comp Φ

theorem ev_sub (a b : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (a - b) Q = Φ a Q - Φ b Q := by rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 D.host.E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp D Φ) (a : D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (incA D a) Q = algebraMap D.host.E (Q.adicCompletion D.host.E) a := by rw [hΦ.inc]; rfl

theorem ev_eq_zero (hΦ : Comp D Φ) {z : AE D} (hz : finPart D z = 0) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ z Q = 0 := by
  let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
  have h0 : finPart D u = 0 := TensorProduct.zero_tmul _ _
  have h1 : infPart D u = 1 := rfl
  have h2 : z = u * z := by
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, h1, one_mul]
    · rw [RingHom.map_mul, hz, mul_zero]
  have h3 : Φ u Q = 0 := (hΦ.base _ Q).trans (map_zero _)
  rw [h2, ev_mul, h3, zero_mul]

theorem toEAf_surj (s : Datum.EAf D) : ∃ z : AE D, toEAf D z = s := by
  obtain ⟨y, rfl⟩ := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective s
  obtain ⟨z, -, hz⟩ := GlobalTheory.PlaceIdem.parts_surj D 0 y
  exact ⟨z, congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) hz⟩

theorem val_le_one (hΦ : Comp D Φ) {z : AE D} (hz : toEAf D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : Valued.v (Φ z Q) ≤ 1 :=
  (hΦ.int z).1 ((mem_intAE_iff _).2 hz) Q

theorem val_lt_one_of_mem (hΦ : Comp D Φ) (P : HeightOneSpectrum (𝓞 D.host.E))
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (hs : s ∈ idS D.host.F P.asIdeal) :
    ∀ z : AE D, toEAf D z = s → Valued.v (Φ z P) < 1 := by
  have key : ∃ z : AE D, toEAf D z = s ∧ Valued.v (Φ z P) < 1 := by
    refine exists_lift_lt_one Valued.v (toEAf D) (evAt Φ P) (Formalism.L2.Herm.intAf D.host.F D.host.E)
      (oToS D.host.F D.host.E) P.asIdeal toEAf_surj (fun z hz => val_le_one hΦ hz P) (fun a ha => ?_) s hs
    refine ⟨incA D a, rfl, ?_⟩
    change Valued.v (Φ (incA D a) P) < 1
    rw [ev_inc hΦ, val_alg]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) P a).2 ha
  obtain ⟨w, hw, h⟩ := key
  intro z hz
  have h1 : finPart D (z - w) = 0 := by
    apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    change toEAf D (z - w) = _
    rw [RingHom.map_sub, hz, hw, sub_self, map_zero]
  have h2 := ev_eq_zero hΦ h1 P
  rw [ev_sub, sub_eq_zero] at h2
  rwa [h2]

theorem exists_modulus (hΦ : Comp D Φ) (c : (AE D)ˣ →* Circle) (hc : Continuous c) :
    ∃ N : ℕ, 0 < N ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : (AE D)ˣ), infPart D (y : AE D) = 1 →
      (∀ Q, Q ≠ P → Φ (y : AE D) Q = 1) → Valued.v (Φ (y : AE D) P) = 1 →
      Valued.v (Φ (y : AE D) P - 1) ≤ P.valuation D.host.E (N : D.host.E) → c y = 1 := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc
  refine ⟨N, hN, fun P y h0 h1 h2 h3 => ?_⟩
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hv : ∀ Q, Valued.v (Φ (y : AE D) Q) = 1 := fun Q => by
    by_cases hQ : Q = P
    · rw [hQ, h2]
    · rw [h1 Q hQ, map_one]
  have hv' : ∀ Q, Valued.v (Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q) = 1 := fun Q => by
    have : Valued.v (Φ (y : AE D) Q) * Valued.v (Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q) = 1 := by
      rw [← map_mul, ← ev_mul, Units.mul_inv, ev_one, map_one]
    rwa [hv, one_mul] at this
  refine hker y ⟨h0, (hΦ.int _).2 fun Q => (hv Q).le, (hΦ.int _).2 fun Q => (hv' Q).le⟩
    ⟨finPart D (incA D (N : D.host.E)⁻¹ * ((y : AE D) - 1)), (hΦ.int _).2 fun Q => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_mul, val_alg, map_inv₀]
    by_cases hQ : Q = P
    · subst hQ
      exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0))).2 h3
    · rw [h1 Q hQ, sub_self, map_zero, mul_zero]
      exact zero_le
  · have e : (N : AE D) * (incA D (N : D.host.E)⁻¹ * ((y : AE D) - 1)) = (y : AE D) - 1 := by
      rw [← mul_assoc, ← map_natCast (incA D) N, ← RingHom.map_mul, mul_inv_cancel₀ hN0, RingHom.map_one, one_mul]
    rw [nsmul_eq_mul, ← map_natCast (finPart D) N, ← RingHom.map_mul, e, RingHom.map_sub, RingHom.map_one]

theorem val_sub_lt_one (hΦ : Comp D Φ) (P : Pl D.host.E) (x : AE D)
    (hi : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (b : 𝓞 D.host.E)
    (hb : resS D.host.F P ⟨toEAf D x, hi⟩ = Ideal.Quotient.mk P.asIdeal b) :
    Valued.v (Φ x P - algebraMap D.host.E (P.adicCompletion D.host.E) (b : D.host.E)) < 1 := by
  have hm : (⟨toEAf D (x : AE D), hi⟩ - oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈
      idS D.host.F P.asIdeal := by
    have h0 : resS D.host.F P (⟨toEAf D (x : AE D), hi⟩ - oToS D.host.F D.host.E b) = 0 := by
      rw [RingHom.map_sub, resS_oToS, hb, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS D.host.F P.asIdeal)
      (cmpS_bij (F := D.host.F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  have h1 := val_lt_one_of_mem hΦ P _ hm ((x : AE D) - incA D b) (by rw [RingHom.map_sub]; rfl)
  rw [ev_sub, ev_inc hΦ] at h1
  exact h1

theorem resAt_of_tame (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (P : Pl D.host.E)
    (a : (kP P)ˣ →* ℂˣ) (ht : χ.TameAt P) (ha : IsRes χ P a) : GlobalTheory.StepLaw.ResAt c P a := by
  intro e he x hx hi u hu
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨d0, d1, d2⟩ := delta_of_isIdemAt hΦ he
  obtain ⟨N, hN, hker⟩ := exists_modulus hΦ c hc.1.1
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  have hbP : b ∉ P.asIdeal := fun h => by
    have := P.isPrime
    exact u.ne_zero (hb.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
  have hb0 : (b : D.host.E) ≠ 0 := fun h => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hbv : P.valuation D.host.E (b : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := b)).2 hbP
  have h1 := val_sub_lt_one hΦ P x hi b (hu.symm.trans hb.symm)
  have h2 : Valued.v (Φ (x : AE D) P) = 1 := by
    rw [← hbv, ← val_alg]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rwa [val_alg, hbv]
  obtain ⟨k, k1, k2, k3⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (Φ (x : AE D) P) (fun h => by
    rw [h, map_zero] at h2
    exact zero_ne_one h2)
  rw [h2] at k1
  rw [← k1, mul_one] at k2 k3
  have hpl : IsPlIdem D e P := by
    obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := he
    exact ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  obtain ⟨l, hl⟩ : ∃ l : (AE D)ˣ, (l : AE D) = 1 + e * (incA D (k : D.host.E) - 1) := ⟨locU hpl.1 k, rfl⟩
  obtain ⟨y, hy, hy'⟩ := exists_units_quot x l hl
  have hyP : Φ (x : AE D) P = Φ (y : AE D) P * algebraMap D.host.E _ (k : D.host.E) := by
    rw [← ev_inc hΦ]
    exact map_eq_mul_of_supp (evAt Φ P) d1 hy'
  have hcy : c y = 1 := by
    refine hker P y (map_eq_one_of_supp (infPart D) d0 hx hy')
      (fun Q hQ => map_eq_one_of_supp (evAt Φ Q) (d2 Q hQ) hx hy') ?_ ?_
    · rwa [hyP, map_mul, val_alg, ← k1, mul_one] at h2
    · rwa [hyP, ← sub_one_mul, map_mul, val_alg, ← k1, mul_one] at k2
  have hcx : c x = c l := by rw [hy, map_mul, hcy, one_mul]
  rw [ha b (Units.mk0 _ hb0) u rfl hb.symm, hcx, hc.2 P e hpl k l hl,
    locK_eq_of_tame χ P ht k (Units.mk0 _ hb0) k1.symm hbv]
  have e5 : algebraMap D.host.E (P.adicCompletion D.host.E) ((k : D.host.E) - (b : D.host.E)) =
      (Φ (x : AE D) P - algebraMap D.host.E _ (b : D.host.E)) - (Φ (x : AE D) P - algebraMap D.host.E _ (k : D.host.E)) := by
    rw [map_sub]
    ring
  rw [Units.val_mk0, ← val_alg, e5]
  exact Valuation.map_sub_le _ (le_exp_of_lt_one h1) k3

theorem resAt_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ PP : Pl D.host.E, (∀ a : (kP PP)ˣ →* ℂˣ, χ.TameAt PP → IsRes χ PP a → GlobalTheory.StepLaw.ResAt c PP a) ∧ (χ.UnrAt PP → GlobalTheory.StepLaw.ResAt c PP 1) := by
  intro D c χ hc P
  refine ⟨fun a => resAt_of_tame c χ hc P a, fun h => resAt_of_tame c χ hc P 1 (fun x hx _ => h x hx) ?_⟩
  intro b k u hk hu
  refine (h (atFin P k) ?_).symm
  change Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
  rw [val_alg, hk]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := b)).2 fun hb => ?_
  have := P.isPrime
  exact u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 hb))

end GlobalTheory.ResLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveOfIndep
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.GeoActCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsLift IsGeo ReadTwist KeepsIntegral IsIntegralForm ConstEquiv IsKappa GeoActAt)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levChi_flag (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (flagL (R.datWp i R.triv)) k = 1 := by
  simp [levChi, Formalism.L2.DIV.levFn, flagL, withP, LevCh.datWp, datY, LevelP.full]
  first
    | exact subgroupCharExtension_one_apply _ _
    | (unfold Formalism.L2.DIV.ext1; exact dite_eq_right_iff.2 fun _ => rfl)

private theorem wall_apply_mul_eq_levChi_mul_of_mem_levS {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {T : MMap (R.MW i σ)} (hT : T ∈ R.Wall i σ)
    (v : (R.MW i σ).Vec) {k : GA D (Wc D i)} (hk : k ∈ levS _ (R.βW i) (R.datWp i R.triv)) (g : GA D (Wc D i)) :
    T v (g * k) = levChi _ (R.βW i) (R.datWp i R.triv) k * T v g := by
  unfold RealDat.Wall Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx =>
    have hx' : IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) x := hx
    exact hx'.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]
    ring
  | smul a x _ hx =>
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]
    ring

theorem hasType_e (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := by
    rw [← (he i σ).2.1]
    exact LinearMap.mem_range_self _ y
  intro k hk h
  exact wall_apply_mul_eq_levChi_mul_of_mem_levS R hm v hk h

theorem actW_apply (he : R.models_HW) {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G} {k : GA D (Wc D i)}
    (hk : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec)
    (x : GA D (Wc D i)) : actW R i σ g ((R.HW i σ).e y) v x = (R.HW i σ).e y v (x * k) := by
  have hs := level_action_spec (hasType_e R he i σ y v) ⟨k, hk⟩ k hk x
  rw [levChi_flag R i k, inv_one, one_mul] at hs
  exact hs

end Model

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

variable {T R κ v₀}

end GlobalTheory.GeoActCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameUnimod

theorem isLattice_of_squeeze {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module E M] [Module (𝓞 E) M]
    [IsScalarTower (𝓞 E) E M] {L Λ : Submodule (𝓞 E) M} (hL : Submodule.IsLattice E L) {c : E} (hc : c ≠ 0)
    (h1 : ∀ x ∈ L, c • x ∈ Λ) (h2 : ∀ x ∈ Λ, c • x ∈ L) : Submodule.IsLattice E Λ := by
  let f : M →ₗ[𝓞 E] M := ((c⁻¹ • LinearMap.id : M →ₗ[E] M)).restrictScalars (𝓞 E)
  have hfg : (L.map f).FG := hL.fg.map f
  have hle : Λ ≤ L.map f := fun x hx => ⟨c • x, h2 x hx, by simp [f, smul_smul, hc]⟩
  exact Submodule.IsLattice.of_fg E (hfg.of_le hle)

theorem coe_span_dualSet {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) :
    (Submodule.span (𝓞 E) (dualSet σ J L) : Set (n → E)) = dualSet σ J L := by
  refine Set.Subset.antisymm (fun y hy => ?_) Submodule.subset_span
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simpa [Formalism.UG.hform] using (algebraMap (𝓞 E) E).range.zero_mem
  | add y z _ _ hy hz =>
    intro x hx
    have : Formalism.UG.hform σ J x (y + z) = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x z := by
      simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
    rw [this]
    exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : Formalism.UG.hform σ J x (a • y) = algebraMap (𝓞 E) E a * Formalism.UG.hform σ J x y := by
      simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact mul_mem ⟨a, rfl⟩ (hy x hx)

theorem isDefUnimod_of_isBaseFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), V.SigOK → V.IsPosDef → IsBaseFrame V β Λ N → IsDefUnimod D.sp.cm V.gram Λ := by
  intro D V β Λ N hs hp ⟨_, hdual, hN, h1, h2⟩
  obtain ⟨-, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hL : Submodule.IsLattice D.host.E (Formalism.L2.Herm.crdLat V V.L0) :=
    Submodule.IsLattice.of_fg D.host.E (V.standardTuple_isLattice.fg.map _)
  have hmem : ∀ x, x ∈ Formalism.L2.Herm.crdLat V V.L0 ↔ x ∈ L0c D V := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  refine ⟨Matrix.ext fun i j => (hJ V).1 i j, (hJ V).2.isUnit,
    GlobalTheory.Proof.TotallyDefiniteMass.isTotDef_gram D.sp.cm V hs hp,
    isLattice_of_squeeze hL (Nat.cast_ne_zero.2 hN.ne') (fun x hx => h1 x ((hmem x).1 hx))
      (fun x hx => (hmem _).2 (h2 x hx)), ?_⟩
  rw [← coe_span_dualSet]
  exact congrArg SetLike.coe hdual

end GlobalTheory.BaseFrameUnimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOfFinOrderOfConjMemSelfDualLatticeStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem isOfFinOrder_of_conjIn_mem_St :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), IsDefUnimod hc J Λ → IsFrame β Λ → ∀ (u : UR hc J) (x : UA hc J), conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ St β → IsOfFinOrder u := by
  intro F E _ _ _ _ _ _ hc n J L β hU hβ u x hu
  open Matrix in
  have hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    classical
    by_contra hspan
    have hproper : Submodule.span E (L : Set (Fin n → E)) < ⊤ := lt_top_iff_ne_top.mpr hspan
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
    let σ : E →+* E := hc.sig
    let z : Fin n → E := J⁻¹ *ᵥ (fun i => σ (f (Pi.single i 1)))
    have hpair (x : Fin n → E) : Formalism.UG.hform σ J x z = σ (f x) := by
      rw [Formalism.UG.P.hform_eq_dot, show J *ᵥ z = (fun i => σ (f (Pi.single i 1))) by
        simp only [z, mulVec_mulVec, J.mul_nonsing_inv hU.unit, one_mulVec], dotProduct]
      have hx : ∑ i, x i • Pi.single i (1 : E) = x := by
        simpa only [← Pi.single_smul', smul_eq_mul, mul_one] using
          LinearMap.sum_single_apply (fun _ : Fin n => E) x
      conv_rhs => rw [← hx, map_sum, map_sum]
      simp only [Function.comp_apply, LinearMap.map_smul, smul_eq_mul, map_mul]
    have hz : z ≠ 0 := by
      intro hz
      apply hf
      apply LinearMap.ext
      intro x
      apply σ.injective
      rw [LinearMap.zero_apply, map_zero, ← hpair, hz, Formalism.UG.P.csScale_hform_zero_right]
    have hann (x : Fin n → E) (hx : x ∈ L) : Formalism.UG.hform σ J x z = 0 := by
      have hfx : f x ∈ (Submodule.span E (L : Set (Fin n → E))).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span hx)
      rw [hmap, Submodule.mem_bot] at hfx
      rw [hpair, hfx, map_zero]
    have hzL : z ∈ L := by
      change z ∈ (L : Set (Fin n → E))
      rw [← hU.selfdual]
      intro x hx
      rw [hann x hx]
      exact (algebraMap (𝓞 E) E).range.zero_mem
    let v : InfinitePlace F := Classical.choice inferInstance
    let ι := v.embedding_of_isReal (hc.totReal.isReal v)
    rcases hU.tdef.2 ι with hpos | hneg
    · obtain ⟨a, ha, hsign⟩ := hpos z hz
      rw [hann z hzL, ← map_zero (algebraMap F E)] at ha
      exact (lt_irrefl (0 : ℝ)) (by simpa [(algebraMap F E).injective ha] using hsign)
    · obtain ⟨a, ha, hsign⟩ := hneg z hz
      rw [hann z hzL, ← map_zero (algebraMap F E)] at ha
      exact (lt_irrefl (0 : ℝ)) (by simpa [(algebraMap F E).injective ha] using hsign)
  have hfin := Formalism.UG.Final.AdelicStabFiniteL F E (Fin n) hc.sig J (cm_comp hc) hU.herm hU.unit hU.tdef L
    (Module.Finite.iff_fg.2 hU.lat.fg) hspan x
  have hb := base_level_eq_adelic_level F E hc n J L β hβ
  let H : Subgroup (UR hc J) :=
    (Formalism.UG.levelAfL hc.sig J L).comap (conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
  have hH : Finite H := by
    let f : H → Formalism.UG.stabAt (UQ hc J) ((Formalism.UG.levelAfL hc.sig J L).subgroupOf (UA hc J)) x :=
      fun γ => ⟨ratEl γ.1, (ratEl_mem_stabAt x γ.1).2 γ.2⟩
    refine Finite.of_injective f ?_
    intro a b hab
    exact Subtype.ext (ratEl_injective (congrArg Subtype.val hab))
  have huH : u ∈ H := by
    show conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ Formalism.UG.levelAfL hc.sig J L
    rw [← hb]
    refine ⟨?_, hu⟩
    rw [conjIn_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) (ratEl u).1.2) x.2
  have := isOfFinOrder_of_finite (⟨u, huH⟩ : H)
  exact H.subtype.isOfFinOrder this

end GlobalTheory.DefFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquivStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type) [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  first | exact @GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | exact GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | (intros; apply GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisableStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecGL w ρ x B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | exact GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | (intros; apply GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv <;> assumption)
end

