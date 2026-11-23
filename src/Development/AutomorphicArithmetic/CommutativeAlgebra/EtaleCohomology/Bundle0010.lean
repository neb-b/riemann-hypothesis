module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.QuasiCompactOfProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ResidueExistence.ResEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FinAllOf
section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.finAll_of :
    (∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K) (f : ℕ), 0 < f → CIn l K r f) → UpperTheory.Gal.crystallineComparison.Br.FinAll := by
  intro h l _ K _ _ _ f hf hc ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨r⟩ := UpperTheory.Gal.CD.resEx l K
  have hx : ∀ x : r.k, x ^ l ^ f = x := by
    have hker : RingHom.ker r.ρ = IsLocalRing.maximalIdeal (OK l K) := by
      have hm : (RingHom.ker r.ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective r.ρ r.surj
      exact IsLocalRing.eq_maximalIdeal hm
    have e : IsLocalRing.ResidueField (OK l K) ≃+* r.k :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective r.surj)
    have hcard : Nat.card r.k = l ^ f := by
      rw [← Nat.card_congr e.toEquiv]
      exact hc
    have hfin : Finite r.k :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    have := Fintype.ofFinite r.k
    intro x
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  exact UpperTheory.Ru.crystallineComparison.final l K r f hf hx (h l K r f hf) ϖ hϖ M hM n j T hr hPt A hA B₀
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module Matrix
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.Int.Geo

def InCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
    [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (f q n : ℕ) (ϑ : ℕ → Om l) {a : ℕ}
    (r₀ : ↥Gw →* GL (Fin a) (Om l)) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℚ_[l] V) (_ : Module.Finite ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK Bw.Kw) V)
    (T : ℕ → End ℚ_[l] V) (b : (Fin a → Om l) →ₗ[Om l] Om l ⊗[ℚ_[l]] V), IsCrys (P.PD Bw.Kw) ρ ∧ AnnD (σCr P Bw.Kw) (ψCr P f) q n ρ T ∧
    Function.Injective b ∧ (∀ g x, b ((r₀ g : Matrix (Fin a) (Fin a) (Om l)) *ᵥ x) = (ρ (Bw.e g)).baseChange (Om l) (b x)) ∧
    ∀ j ≤ n, ∀ x, (T j).baseChange (Om l) (b x) = ϑ j • b x

def GeoSide : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (H : HTower E) (θ : H.Γ → Om l), Nice H → ∀ (a : ℕ) (ρ₀ : G E Ω →* GL (Fin a) (Om l)), IsMat l H Ω (Om l) θ ρ₀ →
    ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∀ (n : ℕ) (ϑ : ℕ → Om l), CongAt H θ w n ϑ →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw →
      InCrys P Bw (resDeg l w) (normV w) n ϑ (ρ₀.comp (Dec (F := E) A).subtype)

def JoinQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (f q n : ℕ) (ϑ : ℕ → Om l) (a : ℕ) (r₀ r : ↥Gw →* GL (Fin a) (Om l)),
    Continuous r → IsGr r₀ r → InCrys P Bw f q n ϑ r₀ →
    ∃ (LL : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL.1) (ϑ' : ℕ → ↥LL.1), IsModel Bw r LL r' ∧ Bw.IsCrysE P LL r' ∧
      (∀ j ≤ n, algebraMap ↥LL.1 (Om l) (ϑ' j) = ϑ j) ∧ NilD (σSt P Bw.Kw) (ψSt P f) (Bw.repE LL r') (heckePol q n ϑ')

def NilToPhi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (a : ℕ)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (LL : FinExt l) (r' : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1),
    IsModel Bw r LL r' → Bw.IsCrysE P LL r' → ∀ (Q : Polynomial ↥LL.1), NilD (σSt P Bw.Kw) (ψSt P (resDeg l w)) (Bw.repE LL r') Q →
    ∀ (s : Multiset ℂ) (u : ℂ), u ≠ 0 → Q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = Polynomial.C u * rootPol s →
    IsCrysAt P Bw r ∧ ∃ g : ↥(Weil h), deg g = -1 ∧ ∃ m : ℕ, (wdAt P ι Bw h hj r).charPol g ∣ rootPol s ^ m

def PtIdBC : Prop :=
  ∀ (l q n : ℕ) (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (φ : O →+* O') (ϖ : O), Irreducible ϖ → Irreducible (φ ϖ) → (∀ x : O', φ ϖ ∣ x ^ q - x) →
    ∀ (Y Y' : Scheme.{0}) (p : Y ⟶ Spec (CommRingCat.of O)) (p' : Y' ⟶ Spec (CommRingCat.of O')) (g : Y' ⟶ Y),
    IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)) → ∀ T : Fin (n + 1) → Corr l Y, (∀ j, (T j).r ≫ p = (T j).p ≫ p) →
    PtId l q n (fn p ϖ) T → ∃ (T' : Fin (n + 1) → Corr l Y') (κ : ∀ j, (T' j).Z ⟶ (T j).Z),
      (∀ j, IsPullback (κ j) (T' j).p (T j).p g ∧ κ j ≫ (T j).r = (T' j).r ≫ g ∧ (T' j).r ≫ p' = (T' j).p ≫ p') ∧ PtId l q n (fn p' (φ ϖ)) T'

def AnnPi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (I : Type) [Fintype I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℚ_[l] (V i)] [∀ i, Module.Finite ℚ_[l] (V i)] (ρ : ∀ i, Representation ℚ_[l] ↥(GK K) (V i)) (f q n : ℕ)
    (T : ∀ i, ℕ → End ℚ_[l] (V i)) (ρ' : Representation ℚ_[l] ↥(GK K) (∀ i, V i)) (T' : ℕ → End ℚ_[l] (∀ i, V i)),
    (∀ g x i, ρ' g x i = ρ i g (x i)) → (∀ j x i, T' j x i = T i j (x i)) →
    ((∀ i, IsCrys (P.PD K) (ρ i)) → IsCrys (P.PD K) ρ') ∧
      ((∀ i, AnnD (σCr P K) (ψCr P f) q n (ρ i) (T i)) → AnnD (σCr P K) (ψCr P f) q n ρ' T')

end UpperTheory.Ru.crystallineComparison
end
end

