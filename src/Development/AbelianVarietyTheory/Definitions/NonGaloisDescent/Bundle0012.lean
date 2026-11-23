module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import GroundTheory.LocalFields.UpperNumbering
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
section
noncomputable section

namespace GlobalTheory.TripleGal

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf)

def rk1 {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) : Γ →* GL (Fin 1) K :=
  (Units.map (Matrix.scalar (Fin 1) : K →+* Matrix (Fin 1) (Fin 1) K).toMonoidHom).comp χ


open Classical in
def GalAbove (D : D7) : Prop :=
  ∀ (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l)), IsGaloisRepOf D π l ι r →
    ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      IsdRAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (D.naut.mono0 (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∃ J : Multiset ℤ, IsJumpsAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ J ∧
          J.map (fun n : ℤ => (n : ℂ)) =
            (D.naut.infG π (ι.toRingHom.comp τ)).map fun z => ((D.R.r : ℂ) - 1) / 2 - z

def CharAbove : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
    (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
      IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧ IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
      (χ.UnrAt w → IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype)) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) τ {-n (ι.toRingHom.comp τ)}

end GlobalTheory.TripleGal

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys

def Cheb : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → U.Normal → ∀ (g : G F Ω) (A : Finset (HeightOneSpectrum (𝓞 F))),
  ∃ v, v ∉ A ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧
    ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Ine (F := F) B ≤ U ∧ ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ σ * g⁻¹ ∈ U

def OrdHyp (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l M R nmax v : ℕ)
    (f : MvPolynomial (Fin R ⊕ Fin R) O) : Prop :=
  ∃ Dd g : MvPolynomial (Fin R ⊕ Fin R) O,
    f - Dd * g ∈ Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
      Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ∧
    IsDiscreteValuationRing.addVal O (g.coeff 0) ≤ v ∧
    ∃ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ), u.coeff 0 ≠ 0 ∧ (∀ i, n i ≤ nmax) ∧
      Dd.map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈
        Ideal.span (Set.range fun q =>
          (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M))

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def K1 : Prop := ∀ (i : X.Tw) (M : ℕ), 1 ≤ M → ∃ H S d, AdmFam X i M H S d

def PropE (N0 : X.Tw → ℕ) : Prop :=
  ∀ (i : X.Tw) (lam : X.abelian₂ i) (z : GE N), X.NonzeroIndexPlace i → (∃ s, SOk X i lam s) → (∑ δ, X.th i ∅ lam δ) ≠ 0 → IsTameInertiaElementAtTwistPrime X i z →
    ∃ (H : Subgroup (GE N)) (v : ℕ), IsOpen (H : Set (GE N)) ∧ H.Normal ∧
      (v : ℝ) / ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ) = c0 X i lam + N0 i ∧
      ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d (Q : Finset (PlE D.host)), 1 ≤ M →
        SlopeTestRemainingChoices X i M ∅ P d → Steps X i M H z P d → IsQ P Q →
        ∃ f : MvPolynomial (Fin R ⊕ Fin R) (X.O i), OrdHyp (X.O i) (X.l i) M R 2 v f ∧
          ∀ (k : ℕ) (u : Fin R ⊕ Fin R → (X.Ok i k)ˣ) (ψ' : X.RCG i Q →* (X.Ok i k)ˣ), (∀ q, u q ^ (X.l i ^ M) = 1) →
            (∀ g, ψ' (X.art i Q g) = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) →
            algebraMap (X.Ok i k) (FractionRing (X.Ok i k))
                (MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f) =
              ((X.l i : ℕ) : FractionRing (X.Ok i k)) ^ N0 i * thEval X i Q lam k ψ'

variable {X} (bkP : BKPh X)

def ThmS : Prop :=
  ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) d
    (Q : Finset (PlE D.host)), 1 ≤ M → SlopeTestRemainingChoices X i M ∅ P d → IsQ P Q →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c)

def SelmerLengthsByDeterminant : Prop :=
  ∀ (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) d (Q : Finset (PlE D.host)),
    1 ≤ M → SlopeTestRemainingChoices X i M ∅ P d → IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)),
    Computes bkP i s M d Q Φ → ∀ F, toLam X i M ι F = Φ.det → SelPoly bkP i s M d Q F

def OrdBound (i : X.Tw) (μ : ℕ∞) : Prop :=
  ∀ (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∃ R Dd M₀ : ℕ, ∀ M, M₀ ≤ M →
    ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
        Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ Dd ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤ μ

def ResidualBoundOddPrimes : Prop := ∀ i : X.Tw, nu X i = 0 → OrdBound bkP i 0

def ThmC : Prop :=
  ∀ i : X.Tw, 0 < nu X i → OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i))

def GaloisSideTwistedSelmerAuxiliaryPrimes : Prop :=
  ∀ (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∃ R Dd M₀ : ℕ, 1 ≤ M₀ ∧ ∀ M, M₀ ≤ M →
    ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∃ F, SelPoly bkP i s M (fun q => d (P q)) Q F ∧
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ Dd ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤
          IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def IsCoord (i : X.Tw) (M : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  ∀ Q, ConjCl (D := D) Q → ∀ (P : PlE D.host) (hP : P ∈ Q) (σ : GE N),
    Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (d P σ)

def DelUTie : Prop := ∀ (i : X.Tw) (M : ℕ), X.NonzeroIndexPlace i → 1 ≤ M → ∃ H S d, AdmFam X i M H S d ∧ IsCoord Y i M d

def HeckeLaws : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → (∀ j b k P k' P', Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P → Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P' →
      Y.hkF i j b k P * Y.hkF i j b k' P' = Y.hkF i j b k' P' * Y.hkF i j b k P) ∧
    ∀ s P, X.hEig i s 0 P = 1

def PqF (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) (y : X.Ok i k) :
    Module.End (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  1 + ∑ n ∈ Finset.Icc 1 D.R.r, ((-1 : X.Ok i k) ^ n * ((normV P : ℕ) : X.Ok i k) ^ (n * (n - 1) / 2) * y ^ n) •
    (Formalism.MainNotions.IntegralHeckeForms.hkO Y i j b n P).baseChange (X.Ok i k)


open Classical in
def ThURel : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    ∃ (ch : Set (PlE D.host)) (sg : Bool), (∀ P P', IsConjPl D.host P P' → P ≠ P' → (P ∈ ch ↔ P' ∉ ch)) ∧
      (∀ M k χ (a : Y.Dat i j b), Formalism.MainNotions.IntegralHeckeForms.specU Y i j b ∅ M k χ (Y.thU i j b ∅ M a) =
        (1 : X.Ok i k) ⊗ₜ[X.O i] Y.th i j b a) ∧
      ∀ (M : ℕ) d (Q : Finset (PlE D.host)) (a : Y.Dat i j b), IsCoord Y i M d → QOk X i Q →
        Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q → Disjoint Q (Y.lev i j b a) →
        (∀ P ∈ Q, GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
        ∀ (P Pb : PlE D.host), P ∈ Q → Pb ∈ Q → P ≠ Pb → IsConjPl D.host P Pb → P ∈ ch →
        ∀ (k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
          (χ' : Multiplicative (DelQM D.host (X.l i) ((Q.erase P).erase Pb) M) →* (X.Ok i k)ˣ),
          (∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) = χ' (Multiplicative.ofAdd fun v =>
            x ⟨v.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase v.2)⟩)) →
          ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ →
            Formalism.MainNotions.IntegralHeckeForms.specU Y i j b Q M k χ (Y.thU i j b Q M a) =
              PqF Y i j b k P ((psiAt sg χ' (Y.delU i ((Q.erase P).erase Pb) M σ) : (X.Ok i k)ˣ) : X.Ok i k)
                (Formalism.MainNotions.IntegralHeckeForms.specU Y i j b ((Q.erase P).erase Pb) M k χ' (Y.thU i j b ((Q.erase P).erase Pb) M a))

def PropABCD : Prop :=
  ∀ (i : X.Tw) (F : Formalism.MainNotions.IntegralHeckeForms.RFam Y i) (j : ℕ) (b : Bool) (z : GE N), X.NonzeroIndexPlace i → j ∈ Finset.Icc 1 D.R.m →
    Formalism.MainNotions.IntegralHeckeForms.ABHyp Y i F j b → IsTameInertiaElementAtTwistPrime X i z →
    ∃ (H : Subgroup (GE N)) (A : Finset (PlE D.host)) (v nmax : ℕ), IsOpen (H : Set (GE N)) ∧ H.Normal ∧
      ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d (Q : Finset (PlE D.host)), 1 ≤ M → IsCoord Y i M d →
        SlopeTestRemainingChoices X i M A P (fun q => d (P q)) → Steps X i M H z P (fun q => d (P q)) → (hQ : IsQ P Q) →
        ∃ f : MvPolynomial (Fin R ⊕ Fin R) (X.O i), OrdHyp (X.O i) (X.l i) M R nmax v f ∧
          ∀ (k : ℕ) (u : Fin R ⊕ Fin R → (X.Ok i k)ˣ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
            (∀ q, u q ^ (X.l i ^ M) = 1) →
            (∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) =
              ∏ q, u q ^ (x ⟨P q, (hQ _).2 ⟨q, Or.inl rfl⟩⟩).val) →
            MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f ≠ 0 →
            ∀ Tψ : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b),
              Formalism.MainNotions.IntegralHeckeForms.IsLatIn Tψ (((Submodule.span (FractionRing (X.O i)) (F.B j b : Set (Y.Fm i j b))).restrictScalars
                (X.O i)).baseChange (X.Ok i k)) →
              (∀ a ∈ F.S j b, ((F.A j b).baseChange (X.Ok i k))
                (Formalism.MainNotions.IntegralHeckeForms.specU Y i j b Q M k χ (Y.thU i j b Q M a)) ∈ Tψ) →
              Formalism.MainNotions.IntegralHeckeForms.sIdx (X.l i) ((F.B j b).baseChange (X.Ok i k)) Tψ ≤
                Formalism.MainNotions.IntegralHeckeForms.sIdx (X.l i) (F.B j b) (F.Th j b) +
                  (nval (X.Ok i k) (X.l i) (MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f) -
                    (v : ℝ) / ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ))

def AllGood : Prop := ∀ i : X.Tw, X.NonzeroIndexPlace i → ∀ s : X.Sig i, goodE Y i s

end GlobalTheory.TwSys

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField

namespace GlobalTheory.PMon.Ram


open Classical in
def jumpSum {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) : ℕ :=
  ∑ᶠ t : ℕ, if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)

section

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def wild (t : ℕ) : Subgroup (L ≃ₐ[K] L) := lowerRamificationGroup K L ((t : ℤ) + 1)

def AxIn (p : ℕ) : Prop :=
  ∀ (J : Subgroup (L ≃ₐ[K] L)) (x : L), (∀ σ ∈ J, σ x - x ∈ 𝒪[L]) →
    ∃ y : L, (∀ σ ∈ J, σ y = y) ∧ (p : L) ^ 2 * (x - y) ∈ 𝒪[L]


variable {K L} in
def Detects (p r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)) : Prop :=
  ∀ σ₀ ∈ A, σ₀ ∉ B → ∃ (x : L) (a : (L ≃ₐ[K] L) → ℤ),
    (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) ∧ ¬ (p : ℤ) ^ r ∣ a σ₀

end

def OrdIs (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] (p E : ℕ) : Prop :=
  IsDiscreteValuationRing.addVal 𝒪[L] (p : 𝒪[L]) = (E : ℕ∞)

def NoTower : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (N : ℕ → Subgroup ↥(GK K)), Antitone N →
    (∀ k, IsOpen (N k : Set ↥(GK K))) →
    (∀ k, ∀ σ ∈ N k, σ ^ l ∈ N (k + 1)) →
    (∀ j, ∀ σ ∈ N 0, σ ^ l ∈ N (j + 1) → σ ∈ N j) →
    (∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → ℂ_[l]) (a : ι → ↥(GK K) → ℤ_[l]),
      (∀ i, ∀ σ ∈ N k, ‖Formalism.Per.σC (σ : GQ l) (x i) - x i - algebraMap ℚ_[l] ℂ_[l] (a i σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧
      ∀ σ ∈ N k, (∀ i, (l : ℤ_[l]) ^ r ∣ a i σ) → σ ∈ N (k + r)) →
    ∃ k, ∀ j, IK K ⊓ N k ≤ N j

def NoTowerQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N : ℕ → Subgroup (GQ l)), Antitone N →
    (∀ k, IsOpen (N k : Set (GQ l))) →
    (∀ k, ∀ σ ∈ N k, σ ^ l ∈ N (k + 1)) →
    (∀ j, ∀ σ ∈ N 0, σ ^ l ∈ N (j + 1) → σ ∈ N j) →
    (∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → Om l) (a : ι → GQ l → ℤ),
      (∀ i, ∀ σ ∈ N k, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧
      ∀ σ ∈ N k, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N (k + r)) →
    ∃ k, ∀ j, ∀ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → σ ∈ N j

end GlobalTheory.PMon.Ram

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.Prism
open scoped Formalism.Per

namespace GlobalTheory.BKReal

variable {l : ℕ} [hl : Fact l.Prime]

theorem semiBC_of_basis {A B M N J : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (b : Module.Basis J A M)
    (c : Module.Basis J B N) (h : ∀ i, u (b i) = c i) : SemiBC u := by
  intro Q _ _ v
  refine ⟨c.constr B fun i => v (b i), fun x => ?_, fun w hw => c.ext fun i => ?_⟩
  · exact LinearMap.congr_fun (b.ext (f₁ := (c.constr B fun i => v (b i)).comp u) (f₂ := v) fun i => by
      rw [LinearMap.comp_apply, h, Module.Basis.constr_basis]) x
  · rw [Module.Basis.constr_basis, ← h, hw]

def piMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (J : Type) : (J → A) →ₛₗ[f] (J → B) where
  toFun x i := f (x i)
  map_add' x y := funext fun i => map_add f (x i) (y i)
  map_smul' c x := funext fun i => map_mul f c (x i)

theorem piMap_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {J : Type} [DecidableEq J] (i : J) :
    piMap f J (Pi.single i 1) = Pi.single i 1 := by
  ext1 k
  change f (Pi.single (M := fun _ => A) i 1 k) = _
  simp [Pi.single_apply, apply_ite f]

theorem semiBC_piMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (J : Type) [Fintype J]
    [DecidableEq J] : SemiBC (piMap f J) :=
  semiBC_of_basis (Pi.basisFun A J) (Pi.basisFun B J) fun i => by
    rw [Pi.basisFun_apply, Pi.basisFun_apply, piMap_single]

def piFrob {A : Type} [CommRing A] (φ : A →+* A) (d : A) (J : Type) :
    (J → A) →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) (J → A) where
  toFun x := LocalizedModule.mk (piMap φ J x) 1
  map_add' x y := by simp
  map_smul' c x := by
    rw [RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk, LinearMap.map_smulₛₗ]

theorem exists_of_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A} {y m : M} {k : ℕ}
    (h : IsFrac d (LocalizedModule.mk y 1) m k) : ∃ r : ℕ, d ^ r • d ^ k • y = d ^ r • m := by
  obtain ⟨⟨_, r, rfl⟩, hr⟩ := LocalizedModule.mk_eq.1 h
  exact ⟨r, by simpa [Submonoid.smul_def] using hr⟩

def unitPow (l : ℕ) (R : Type) [CommRing R] (J : Type) [Fintype J] [DecidableEq J] : FCrys l R where
  M P := J → P.A
  fin _ := inferInstance
  proj _ := inferInstance
  tr f := piMap f.f J
  tr_bc f := semiBC_piMap f.f J
  tr_id _ _ := rfl
  tr_comp _ _ _ := rfl
  Φ P d := piFrob P.D.φ d J
  Φ_bc P d := semiBC_of_basis (Pi.basisFun _ J) ((Pi.basisFun P.A J).ofIsLocalizedModule
    (Localization.Away (d : P.A)) (Submonoid.powers (d : P.A)) (LocalizedModule.mkLinearMap _ _)) fun i => by
      rw [Module.Basis.ofIsLocalizedModule_apply, Pi.basisFun_apply]
      exact congrArg (LocalizedModule.mk · 1) (piMap_single _ i)
  Φ_nat := by
    intro P P' f d d' x m k n j h1 h2
    obtain ⟨r, hr⟩ := exists_of_isFrac h1
    obtain ⟨s, hs⟩ := exists_of_isFrac h2
    refine ⟨r + s, funext fun i => ?_⟩
    have ha : (d : P.A) ^ r * ((d : P.A) ^ k * P.D.φ (x i)) = (d : P.A) ^ r * m i := congrFun hr i
    have hb : (d' : P'.A) ^ s * ((d' : P'.A) ^ j * P'.D.φ (f.f (x i))) = (d' : P'.A) ^ s * n i := congrFun hs i
    have ha' := congrArg f.f ha
    simp only [map_mul, map_pow, f.f_φ] at ha'
    change (f.f d * d') ^ (r + s) * ((d' : P'.A) ^ j * f.f (m i) - f.f d ^ k * n i) = 0
    linear_combination (-(f.f d) ^ s * (d' : P'.A) ^ (r + s + j)) * ha' +
      (f.f d ^ (r + s + k) * (d' : P'.A) ^ r) * hb

def unitPowMap (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] [DecidableEq J]
    (β : Module.Basis J ℤ_[l] T) : (unitPow l ↥(OL F) J).M (ainfObj F) →ₛₗ[(inclW l).comp (ainfId F).toRingHom]
      (WCb l ⊗[ℤ_[l]] T) :=
  (β.baseChange (WCb l)).equivFun.symm.toLinearMap.comp (piMap ((inclW l).comp (ainfId F).toRingHom) J)

theorem unitPowMap_apply (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (x : J → Ainf l) :
    unitPowMap F β x = ∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i := by
  refine ((β.baseChange (WCb l)).equivFun_symm_apply fun i => inclW l (x i)).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  rw [Module.Basis.baseChange_apply, smul_tmul', smul_eq_mul, mul_one]

theorem sum_frob {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] (β : J → T) {d : Ainf l}
    (hd : d ≠ 0) (x m : J → Ainf l) (k r : ℕ)
    (h : ∀ i, d ^ r * (d ^ k * WittVector.frobenius (x i)) = d ^ r * m i) :
    inclW l d ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i) =
      ∑ i, inclW l (m i) ⊗ₜ[ℤ_[l]] β i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, frobW_inclW,
    ← mul_left_cancel₀ (pow_ne_zero r hd) (h i), map_mul, map_pow, smul_tmul', smul_eq_mul]

theorem sum_gal {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] (β : J → T) (g : GQ l)
    (ρ : T →ₗ[ℤ_[l]] T) (hρ : ∀ x, ρ x = x) (x : J → Ainf l) :
    ∑ i, inclW l (Per.σA g (x i)) ⊗ₜ[ℤ_[l]] β i =
      TensorProduct.map (galW l g).toLinearMap ρ (∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, galW_inclW, hρ]

theorem unitPowMap_frob (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (d : Ainf l) (hd : d ≠ 0) (x m : J → Ainf l) (k : ℕ)
    (h : IsFrac d (LocalizedModule.mk (piMap WittVector.frobenius J x) 1) m k) :
    inclW l d ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (unitPowMap F β x) =
      unitPowMap F β m := by
  obtain ⟨r, hr⟩ := exists_of_isFrac h
  rw [unitPowMap_apply, unitPowMap_apply]
  exact sum_frob β hd x m k r fun i => congrFun hr i

theorem unitPowMap_gal (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (g : GQ l) (ρ : T →ₗ[ℤ_[l]] T) (hρ : ∀ x, ρ x = x)
    (x : J → Ainf l) : unitPowMap F β (fun i => Per.σA g (x i)) =
      TensorProduct.map (galW l g).toLinearMap ρ (unitPowMap F β x) := by
  rw [unitPowMap_apply, unitPowMap_apply]
  exact sum_gal β g ρ hρ x

theorem realises_unitPow (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (ρ : ↥(GK F) → (T →ₗ[ℤ_[l]] T)) (hρ : ∀ g x, ρ g x = x) :
    Realises F (unitPow l ↥(OL F) J) (ainfObj F) (ainfId F) T ρ (unitPowMap F β) := by
  have hAinf : IsAinf F (ainfObj F) (ainfId F) := by
    refine ⟨fun _ => rfl, fun _ => Iff.rfl, ?_⟩
    intro x a h
    have hθ : ainfQuot l (Ideal.Quotient.mk _ a) = ainfQuot l ((ainfQuot l).symm (intToOC F x)) :=
      congrArg (ainfQuot l) h
    rw [RingEquiv.apply_symm_apply] at hθ
    exact congrArg Subtype.val hθ
  refine ⟨hAinf, ?_, ?_, ?_⟩
  · exact SemiBC.comp_equiv (semiBC_piMap ((inclW l).comp (ainfId F).toRingHom) J)
      (β.baseChange (WCb l)).equivFun.symm
  · intro d hd x m k h
    exact unitPowMap_frob F β d.1 hd x m k h
  · intro g x
    exact unitPowMap_gal F β g (ρ g) (hρ g) x

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

namespace GlobalTheory.EtaJoin

variable (D : D7)

def ratSub (μ : D.what₂.Tup) (j : ℕ) (U : Submodule ℂ (D.what₂.Mt μ j)) : Submodule D.what₂.LL (D.what₂.MtL μ j) :=
  U.comap (D.what₂.jMt μ j)

def genSet (μ : D.what₂.Tup) (j : ℕ) : Set (D.what₂.MtL μ j) :=
  {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen}

def lat (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Submodule.span (𝓞 D.what₂.LL) (genSet D μ j)

def up (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  (ratSub D μ j (Idx.Z0 D μ j)).restrictScalars (𝓞 D.what₂.LL) ⊓
    (lat D μ j ⊔ (ratSub D μ j (Idx.Z0 D μ j)ᗮ).restrictScalars (𝓞 D.what₂.LL))

def low (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  lat D μ j ⊓ (ratSub D μ j (Idx.Z0 D μ j)).restrictScalars (𝓞 D.what₂.LL)

def etaRat (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl) : ℚ :=
  Formalism.L2.Col.lenUW (D.plEq w) (up D μ j) (low D μ j)

def ZRat (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ratSub D μ j (Idx.Z0 D μ j) ⊔ ratSub D μ j (Idx.Z0 D μ j)ᗮ = ⊤

def SpecPr (i : D.nd.Loc) : Prop :=
  (∀ y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i)),
    D.nd.prMt i y ∈ D.nd.eigSum i (↑(D.nd.Zgood i))) ∧
  (∀ y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ,
    D.nd.prMt i y ∈ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ)

def ZSpec (i : D.nd.Loc) : Prop :=
  ∀ P : D.naut.AV i,
    (D.naut.typeV i P ≤ Idx.Z0 D (D.nd.mu i) (D.nd.j i) ∨ D.naut.typeV i P ≤ (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ) ∧
    ∀ x, D.naut.ptV i P = some x →
      (x ∈ D.nd.Zgood i → D.naut.typeV i P ≤ Idx.Z0 D (D.nd.mu i) (D.nd.j i)) ∧
      (x ∉ D.nd.Zgood i → D.naut.typeV i P ≤ (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ)

def TypeTie (i : D.nd.Loc) : Prop :=
  ∀ (S : Set (D.naut.AV i)) (y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt (D.nd.mu i) (D.nd.j i) y ∈ (⨆ P ∈ S, D.naut.typeV i P) →
    D.nd.prMt i y ∈ D.nd.eigSum i {x | ∃ P ∈ S, D.naut.ptV i P = some x}

def TypeOrth (i : D.nd.Loc) : Prop :=
  ∀ P P' : D.naut.AV i, P ≠ P' → D.naut.typeV i P ⟂ D.naut.typeV i P'

def ThetaCut (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  D.what₂.Zj μ j ≤ LinearMap.range (D.what₂.eMt μ j)

def SplitUnif : Prop :=
  ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ

variable {D}

def HeckeScalar (M : MtFam D) (i : D.nd.Loc) : Prop :=
  ∀ (P : D.naut.AV i) (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut D.nd i w → IsConjPl D.host w s.w →
    IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ D.naut.typeV i P,
    NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = c • (M.loc i).real y

def latLoc {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : Submodule (B.Oc j w) (B.V j w) :=
  Submodule.span (B.Oc j w) (B.iV j w '' genSet D (D.what₂.muTw w) j)

def LatStable {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : Prop :=
  ∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ x ∈ latLoc B j w, B.hK j w v k x ∈ latLoc B j w

end GlobalTheory.EtaJoin
end
end

