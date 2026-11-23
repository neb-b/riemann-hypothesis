module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def IsClassTerm {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (y : (Af E)ˣ) (T : ℂ) : Prop :=
  ∃ S : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y) S ∧ T = ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0

theorem isToricSum_iff {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (T : ℂ) :
    IsToricSum φ s κ c χ T ↔ Finite (PicO c) ∧ ∃ t : PicO c → ℂ, (∀ q, IsClassTerm φ s κ c χ q.out (t q)) ∧ T = ∑ᶠ q, t q := by
  refine and_congr_right fun _ => ⟨fun ⟨S, hS, hT⟩ => ⟨_, fun q => ⟨S q, hS q, rfl⟩, hT⟩, fun ⟨t, ht, hT⟩ => ?_⟩
  choose S hS hS' using ht
  exact ⟨S, hS, by rw [hT]; exact finsum_congr hS'⟩

def IsHostDatum {R : Ranks} (H : Host R) {I : Type} [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E))
    (χ : HChar H.E) : Prop :=
  IsCMType φ ∧ (∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) ∧ 1 ≤ s ∧ (∀ τ, 1 ≤ κ τ) ∧ IsBaseCond 𝔣 ∧ IsValChar φ s κ 𝔣 ∅ χ

def below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (OF E) :=
  P.under (OF E)

theorem over_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Over P (below P) := rfl


open Classical in
def belowSet {E : Type} [Field E] [NumberField E] (Q : Finset (HeightOneSpectrum (𝓞 E))) : Finset (HeightOneSpectrum (OF E)) :=
  Q.image below

theorem splits_below {R : Ranks} (H : Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : Splits (below P) := by
  obtain ⟨x, hx, hx'⟩ := h
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  have hc : ∀ a : 𝓞 H.E, ((c a : 𝓞 H.E) : H.E) = H.conj (a : H.E) := fun a => rfl
  refine ⟨P, P.comap c.toRingHom c.surjective, fun e => ?_, rfl, ?_⟩
  · have : x ∈ (P.comap c.toRingHom c.surjective).asIdeal := e ▸ hx
    exact hx' (c x) (hc x) this
  · ext a
    have : c (algebraMap (OF H.E) (𝓞 H.E) a) = algebraMap (OF H.E) (𝓞 H.E) a := by
      apply RingOfIntegers.ext
      apply H.φ₀.injective
      show H.φ₀ (H.conj ((a : maximalRealSubfield H.E) : H.E)) = H.φ₀ ((a : maximalRealSubfield H.E) : H.E)
      rw [H.toHostAx.conjE_apply]
      exact (a : maximalRealSubfield H.E).2 H.φ₀
    show c (algebraMap (OF H.E) (𝓞 H.E) a) ∈ P.asIdeal ↔ algebraMap (OF H.E) (𝓞 H.E) a ∈ P.asIdeal
    rw [this]

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

abbrev Kbar (i : X.Tw) : Type := AlgebraicClosure (FractionRing (X.O i))

def toBar (i : X.Tw) : FractionRing (X.O0 i) →+* Kbar X i :=
  (algebraMap (FractionRing (X.O i)) (Kbar X i)).comp
    (IsFractionRing.lift (g := (algebraMap (X.O i) (FractionRing (X.O i))).comp (algebraMap (X.O0 i) (X.O i)))
      ((IsFractionRing.injective (X.O i) (FractionRing (X.O i))).comp (X.O_inj i)))

def IsRecMap (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) {c : Ideal (OF D.host.E)} (π : PicO c →* X.RCG i Q) : Prop :=
  ∀ P, P ∉ X.S0 i → P ∉ Q → ∀ σ : G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ →
    π (QuotientGroup.mk (unifAt P)) = (X.art i Q σ)⁻¹

def IsToricEltAt (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (s : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E)
    (u : Kbar X i),
    IsHostDatum D.host φ s κ 𝔣 χ ∧
    (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
    (∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (val χ P : ℂ) = 1) ∧
    u ≠ 0 ∧
    ∀ Q, BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q)

def atSide {i : X.Tw} (b : Bool) (ι : ℂ →+* Kbar X i) : ℂ →+* Kbar X i := if b then ι else ι.comp (starRingEnd ℂ)

def IsToricElt : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s → IsToricEltAt X i (atSide X (X.sideL i lam) ι) lam s

variable {X}

theorem placesBelow_splitCoprimeConductor_of_admissible {i : X.Tw} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (hQ : BlochKatoReduction.Gen.QOk X i Q) {𝔣 : Ideal (OF D.host.E)}
    (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) :
    IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q) ∧ ∀ q ∈ belowSet Q, ((X.l i : ℕ) : OF D.host.E) ∉ q.asIdeal := by
  classical
  constructor
  · intro q hq
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨splits_below D.host (hQ.1 P hP), fun h => Finset.disjoint_left.1 hQ.2.1 hP (h𝔣 P h)⟩
  · intro q hq h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine Finset.disjoint_left.1 hQ.2.1 hP (X.twistExcludedPlaces_contains_residueChar i ?_)
    have : algebraMap (OF D.host.E) (𝓞 D.host.E) ((X.l i : ℕ) : OF D.host.E) ∈ P.asIdeal := h
    rwa [map_natCast] at this

end Record

end GlobalTheory.ToricDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RestrictionH1MemBlochKato
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BKIntegralToRational

theorem exists_mul_pow_eq {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {p : A}
    (hu : ¬ IsUnit p) (a : FractionRing A) :
    ∃ (x : A) (N : ℕ), a * algebraMap A (FractionRing A) p ^ N = algebraMap A (FractionRing A) x := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd0 hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hu
  obtain ⟨c, hc⟩ : d ∣ p ^ N := hN.dvd.trans (pow_dvd_pow_of_dvd h1 N)
  refine ⟨n * c, N, ?_⟩
  have hd1 : algebraMap A (FractionRing A) d ≠ 0 := by
    simpa using hd0
  rw [← map_pow, hc, map_mul, map_mul]
  field_simp

theorem continuous_div_mk {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [TopologicalSpace O₀] [IsTopologicalRing O₀] (had : IsAdic (IsLocalRing.maximalIdeal O₀))
    [CommRing O'] [IsDomain O'] (ι : O₀ →+* O') {d : O₀} (hd : d ≠ 0) (hd' : ι d ≠ 0) :
    Continuous fun x : O₀ => (Submodule.Quotient.mk (algebraMap O' (FractionRing O') (ι x) /
      algebraMap O' (FractionRing O') (ι d)) : KmodO O') := by
  have hd1 : algebraMap O' (FractionRing O') (ι d) ≠ 0 := by simpa using hd'
  have hop : IsOpen ((Ideal.span {d} : Ideal O₀) : Set O₀) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
    have := (isAdic_iff.1 had).1 N
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at this
    rwa [Ideal.span_singleton_eq_span_singleton.2 hN]
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((Ideal.span {d} : Ideal O₀) : Set O₀),
    hop.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ : d ∣ y - x := Ideal.mem_span_singleton.1 hy
  rw [Submodule.Quotient.eq]
  refine ⟨ι c, ?_⟩
  rw [← sub_div, ← map_sub, ← map_sub, hc, map_mul, map_mul]
  simp only [Algebra.linearMap_apply]
  field_simp

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem continuous_of_toLL {X : Type} [TopologicalSpace X] (f : X → O₀)
    (h : Continuous fun x => Bw.toLL (f x)) : Continuous f := by
  have h1 : Continuous fun x => Bw.eO (f x) := continuous_induced_rng.2 h
  simpa [Function.comp_def] using Bw.eO_symm_cont.comp h1

theorem continuous_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (j : Fin m) : Continuous fun g => f g j := by
  apply continuous_of_toLL Bw
  have := ((continuous_apply j).comp hf.1.1).comp Bw.e_cont
  simpa [Function.comp_def] using this

theorem cocycle_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (g h : ↥Gw) (j : Fin m) :
    f (g * h) j = f g j + ∑ b, ((T g : GL (Fin m) O₀) : Matrix (Fin m) (Fin m) O₀) j b * f h b := by
  apply toLL_injective Bw
  have := congrFun (hf.1.2 (Bw.e g) (Bw.e h)) j
  simpa [← map_mul, LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply] using this

end Bridge

section Main

variable (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ)

variable (ψ : GE D →* (D.ntw.Ok i k)ˣ) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i))
  (hψ : ∀ σ ∈ decAt D v, ψ σ = 1)


end Main

end GlobalTheory.BKIntegralToRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ToNatAddValMul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.NormValExt

open IsDiscreteValuationRing

variable {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

theorem toNat_addVal_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    (addVal R (a * b)).toNat = (addVal R a).toNat + (addVal R b).toNat := by
  rw [addVal_mul]
  exact ENat.toNat_add (fun h => ha ((addVal_eq_top_iff).mp h)) (fun h => hb ((addVal_eq_top_iff).mp h))

theorem nval_mul (l : ℕ) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    BlochKatoReduction.Gen.nval R l (a * b) =
      BlochKatoReduction.Gen.nval R l a + BlochKatoReduction.Gen.nval R l b := by
  unfold BlochKatoReduction.Gen.nval
  rw [toNat_addVal_mul ha hb, Nat.cast_add, add_div]

theorem vK_eq (l : ℕ) {x : FractionRing R} (hx : x ≠ 0) {a b : R} (hb : b ≠ 0)
    (h : x * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) :
    BlochKatoReduction.Gen.vK R l x =
      BlochKatoReduction.Gen.nval R l a - BlochKatoReduction.Gen.nval R l b := by
  unfold BlochKatoReduction.Gen.vK
  generalize_proofs hE
  have hinj := IsFractionRing.injective R (FractionRing R)
  have key : ∀ q : R × nonZeroDivisors R,
      x * algebraMap R (FractionRing R) q.2 = algebraMap R (FractionRing R) q.1 →
      BlochKatoReduction.Gen.nval R l q.1 - BlochKatoReduction.Gen.nval R l q.2 =
        BlochKatoReduction.Gen.nval R l a - BlochKatoReduction.Gen.nval R l b := by
    intro q hq
    have hq2 : (q.2 : R) ≠ 0 := nonZeroDivisors.ne_zero q.2.2
    have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hb) h
    have hq1 : q.1 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hq
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hq2) hq
    have hcross : a * q.2 = q.1 * b := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hq]
      ring
    have hc := congrArg (BlochKatoReduction.Gen.nval R l) hcross
    rw [nval_mul l ha hq2, nval_mul l hq1 hb] at hc
    linarith
  exact key hE.choose hE.choose_spec

end GlobalTheory.NormValExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

noncomputable section

namespace GlobalTheory.EmbInj

open Formalism.BasicNotions.Loc

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_iff_norm (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_iff (LL : FinExt l) (x : ↥LL.1) : x ∈ OL LL ↔ ‖(x : Om l)‖ ≤ 1 := by
  rw [← isIntegral_iff_norm, OL, mem_integralClosure_iff]
  exact (isIntegral_algHom_iff (LL.1.val.restrictScalars ℤ_[l]) LL.1.val.toRingHom.injective).symm

theorem norm_algHom (K L : FinExt l) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective x
  have h2 := minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
  [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : _root_.Formalism.BasicNotions.LocBridge l E Ω Gw O)

theorem norm_le_one_iff (y : ↥B.LL.1) : ‖(y : Om l)‖ ≤ 1 ↔ ∃ n : O, y = B.toLL n := by
  rw [← mem_OL_iff]
  constructor
  · intro h
    refine ⟨B.eO.symm ⟨y, h⟩, ?_⟩
    simp [LocBridge.toLL]
  · rintro ⟨n, rfl⟩
    exact (B.eO n).2

theorem toLL_inj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)

theorem exists_frac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
  by_cases h : ‖(y : Om l)‖ ≤ 1
  · obtain ⟨n, hn⟩ := (norm_le_one_iff B y).1 h
    refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
    have := congrArg B.toLL h1
    simp at this
  · have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
    obtain ⟨d, hd⟩ := (norm_le_one_iff B _).1 h'
    refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
    rw [h1, map_zero] at hd
    exact hy (inv_eq_zero.1 hd)

theorem algHom_ext (τ τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1)
    (h : ∀ x : E, τ ⟨B.j (algebraMap E Ω x), B.j_E x⟩ = τ' ⟨B.j (algebraMap E Ω x), B.j_E x⟩) :
    τ = τ' := by
  ext y
  by_contra hne
  have hpos : 0 < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (B.j_dense y.2) _ (half_pos hpos)
  rw [dist_eq_norm] at hx
  set z : ↥B.Kw.1 := ⟨B.j (algebraMap E Ω x), B.j_E x⟩ with hz
  have e : ((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1) =
      ((τ (y - z) : ↥B.LL.1) : Om l) - (τ' (y - z) : ↥B.LL.1) := by
    rw [map_sub, map_sub, hz, h x]
    push_cast
    ring
  have h1 := norm_algHom _ _ τ (y - z)
  have h2 := norm_algHom _ _ τ' (y - z)
  have h3 := norm_sub_le ((τ (y - z) : ↥B.LL.1) : Om l) (τ' (y - z) : ↥B.LL.1)
  have h4 : ‖((y - z : ↥B.Kw.1) : Om l)‖ < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ / 2 := hx
  rw [← e, h1, h2] at h3
  linarith

end Local

end GlobalTheory.EmbInj
end
end

