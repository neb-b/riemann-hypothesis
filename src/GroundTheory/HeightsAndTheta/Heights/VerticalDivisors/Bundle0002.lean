module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreClosedComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

theorem FibreClosedComponent.proof : FibreClosedComponent.Statement := by
  intro O _ _ F _ _ _ n P W v hP hPO hW hWmax
  classical
  have := hP
  have : W.IsPrime := hW.1.1

  set mk : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) O ⧸ P := Ideal.Quotient.mk P with hmk_def
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hvW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W := le_sup_right.trans hW.1.2
  have hker : RingHom.ker mk = P := Ideal.mk_ker
  have hQprime : (W.map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hPW)
  let Q : PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P) := ⟨W.map mk, hQprime⟩
  have hcomapQ : (W.map mk).comap mk = W := by
    rw [Ideal.comap_map_of_surjective _ hmk, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW]
  have halg : algebraMap O (MvPolynomial (Fin n) O ⧸ P) = mk.comp C := by
    exact RingHom.ext fun _ => rfl

  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) O)
    (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal)
  let U : Set (PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P)) :=
    {q | ∀ W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes,
      W' ≠ W → ¬ W' ≤ q.asIdeal.comap mk}
  have hU : IsOpen U := by
    have hUc : Uᶜ = ⋃ W' ∈ {W' | W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O)
        v.asIdeal).minimalPrimes ∧ W' ≠ W},
        PrimeSpectrum.zeroLocus ((W'.map mk : Ideal (MvPolynomial (Fin n) O ⧸ P)) : Set _) := by
      ext q
      simp only [U, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not, Set.mem_iUnion,
        PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, exists_prop,
        and_assoc]
    rw [← isClosed_compl_iff, hUc]
    exact Set.Finite.isClosed_biUnion (hfin.subset (by exact fun _ h => h.1))
      fun _ _ => PrimeSpectrum.isClosed_zeroLocus _
  have hiso : IsOpen (X := PrimeSpectrum.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P)) ⁻¹'
      {Q.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P))}) {⟨Q, rfl⟩} := by
    refine isOpen_induced_iff.mpr ⟨U, hU, ?_⟩
    ext ⟨q, hq⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hqU
      have hq' : q.asIdeal.comap (algebraMap O _) = Q.asIdeal.comap (algebraMap O _) :=
        congrArg PrimeSpectrum.asIdeal hq
      have hle : P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ q.asIdeal.comap mk := by
        refine sup_le ?_ ?_
        · intro x hx
          show mk x ∈ q.asIdeal
          rw [show mk x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx]
          exact q.asIdeal.zero_mem
        · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← halg, hq', halg, ← Ideal.comap_comap]
          show v.asIdeal ≤ ((W.map mk).comap mk).comap C
          rw [hcomapQ, ← Ideal.map_le_iff_le_comap]
          exact hvW
      obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
      have hW''W : W'' = W := by
        by_contra hne
        exact hqU W'' hW'' hne hW''le
      rw [hW''W] at hW''le
      have heq : W = q.asIdeal.comap mk :=
        hWmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hW''le
      apply Subtype.ext
      apply PrimeSpectrum.ext
      change q.asIdeal = W.map mk
      rw [heq, Ideal.map_comap_of_surjective _ hmk]
    · intro h
      obtain rfl : q = Q := congrArg Subtype.val h
      intro W' hW' hne hle
      change W' ≤ (W.map mk).comap mk at hle
      rw [hcomapQ] at hle
      exact hne (le_antisymm hle (hW.2 hW'.1 hle))
  have : Algebra.QuasiFiniteAt O Q.asIdeal :=
    (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber Q).mpr hiso

  obtain ⟨r, hrQ, hr, hm⟩ :=
    Algebra.zariskisMainProperty_iff.mp (Algebra.ZariskisMainProperty.of_finiteType (R := O) Q.asIdeal)
  have hr0 : r ≠ 0 := fun h => hrQ (h ▸ Q.asIdeal.zero_mem)
  have hDalg : ∀ d : MvPolynomial (Fin n) O ⧸ P, IsAlgebraic O d := by
    intro d
    obtain ⟨m, hm⟩ := hm d
    exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hr0))
      (hr.pow m).isAlgebraic hm.isAlgebraic

  have hIprime : (P.map (MvPolynomial.map (algebraMap O F) :
      MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)).IsPrime := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := O) (S := F)
    have hloc : IsLocalization ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O))
        (MvPolynomial (Fin n) F) := MvPolynomial.isLocalization _ _
    refine IsLocalization.isPrime_of_isPrime_disjoint
      ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O)) (MvPolynomial (Fin n) F) P hP ?_
    rw [Set.disjoint_left]
    rintro x hx hxP
    obtain ⟨c, hc, rfl⟩ := Submonoid.mem_map.mp hx
    have hcP : c ∈ P.comap (C : O →+* MvPolynomial (Fin n) O) := hxP
    rw [hPO, Ideal.mem_bot] at hcP
    exact nonZeroDivisors.ne_zero hc hcP

  let I := P.map (MvPolynomial.map (algebraMap O F) : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)
  let φ : (MvPolynomial (Fin n) O ⧸ P) →ₐ[O] (MvPolynomial (Fin n) F ⧸ I) :=
    Ideal.quotientMapₐ I (MvPolynomial.mapAlgHom (Algebra.ofId O F)) Ideal.le_comap_map
  have hX : ∀ i, IsIntegral F (Ideal.Quotient.mk I (X i)) := by
    intro i
    have h : Ideal.Quotient.mk I (X i) = φ (Ideal.Quotient.mk P (X i)) := by
      show _ = Ideal.Quotient.mk I (MvPolynomial.map (algebraMap O F) (X i))
      rw [MvPolynomial.map_X]
    rw [h]
    exact (((hDalg _).algHom φ).extendScalars (IsFractionRing.injective O F)).isIntegral
  have hint : ∀ x : MvPolynomial (Fin n) F ⧸ I, IsIntegral F x := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p i hp => rw [map_mul]; exact hp.mul (hX i)
  have : Algebra.IsIntegral F (MvPolynomial (Fin n) F ⧸ I) := ⟨hint⟩
  have hfield : IsField (MvPolynomial (Fin n) F ⧸ I) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap F _).injective).mp (Field.toIsField F)
  exact ringKrullDim_eq_zero_of_isField hfield

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

abbrev Par (e n : ℕ) : Type := (Fin e × Fin n) ⊕ Fin n

section Section

variable {R : Type*} [CommRing R] {n e : ℕ}

def secForm (y : Par e n → R) (i : Fin e) : MvPolynomial (Fin n) R :=
  linForm fun j => y (.inl (i, j))

def chartForm (y : Par e n → R) : MvPolynomial (Fin n) R :=
  linForm fun j => y (.inr j)

def secIdeal (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    Ideal (MvPolynomial (Fin n) R) :=
  Q ⊔ Ideal.span (Set.range (secForm y)) ⊔ Ideal.span {chartForm y - 1}

abbrev SecAlg (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) : Type _ :=
  MvPolynomial (Fin n) R ⧸ secIdeal Q y

def secCoord (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (j : Fin n) : SecAlg Q y :=
  Ideal.Quotient.mk _ (X j)

def secLin (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (u : Fin n → R) : SecAlg Q y :=
  Ideal.Quotient.mk _ (linForm u)

end Section

section NormForm

variable {R : Type*} [CommRing R] {n : ℕ}

def normForm (A : Type*) [CommRing A] [Algebra R A] (x : Fin n → A) : MvPolynomial (Fin n) R :=
  letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
    MvPolynomial.algebraMvPolynomial
  Algebra.norm (MvPolynomial (Fin n) R) (∑ j, X j * C (x j) : MvPolynomial (Fin n) A)

end NormForm

section Spec

variable {R S : Type*} [CommRing R] [CommRing S] {n e : ℕ}

def specRest (φ : R →+* S) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    MvPolynomial (Fin n) S :=
  eval₂ (C.comp φ)
    (fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) S) (X ij.2)
      (fun i => C (y (.inl (i, ij.2)))) ij.1) f

end Spec

section Incidence

variable {R : Type*} [CommRing R] {n : ℕ}

def incIdeal (I : Ideal (MvPolynomial (Fin n) R)) (k : ℕ) :
    Ideal (MvPolynomial (Fin n ⊕ (Fin k × Fin n)) R) :=
  I.map (rename Sum.inl) ⊔
    Ideal.span (Set.range fun i : Fin k => ∑ j, X (Sum.inr (i, j)) * X (Sum.inl j))

end Incidence

def NormLength.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] (b : B), Function.Injective (fun x : B => b * x) →
      Ring.ord R (Algebra.norm R b) = Module.length R (B ⧸ Ideal.span {b})

def LengthDecomp.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (b : B), Module.length R (B ⧸ Ideal.span {b}) ≠ ⊤ →
      Module.length R (B ⧸ Ideal.span {b}) =
        ∑ᶠ 𝔫 : MaximalSpectrum B,
          Ring.ord (Localization.AtPrime 𝔫.asIdeal) (algebraMap B (Localization.AtPrime 𝔫.asIdeal) b) *
            Module.length R (B ⧸ 𝔫.asIdeal)

def NormFormEval.Statement : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (n : ℕ) (x : Fin n → A) (u : Fin n → R),
      eval u (normForm A x) = Algebra.norm R (∑ j, algebraMap R A (u j) * x j)

def NormFormLocalization.Statement : Prop :=
  ∀ (R F A A' : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A] [CommRing A'] [Algebra R A']
    [Algebra A A'] [Algebra F A'] [IsScalarTower R A A'] [IsScalarTower R F A']
    [IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) A'] (n : ℕ) (x : Fin n → A),
      (normForm A x).map (algebraMap R F) = normForm A' (fun j => algebraMap A A' (x j))

def ChartTorsion.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)),
    P.IsPrime → (∀ c : D, C c ∈ P → c = 0) →
      ∀ (c : D) (g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D), c ≠ 0 → C c * g ∈ incIdeal P k →
        ∀ j : Fin n, ∃ N : ℕ, X (Sum.inl j) ^ N * g ∈ incIdeal P k

def IncidenceNull.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F), IsChowForm I k f →
      ∃ m : ℕ, ∀ j : Fin n, (rename Sum.inr f * X (Sum.inl j)) ^ m ∈ incIdeal I k

def ChowFormHomog.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F), IsChowForm I k f → IsMultiHomog (chowDegree I k) f

def ChowNormForm.Statement : Prop :=
  ∀ (k E : Type) [Field k] [PerfectField k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), AlgebraicIndependent k y → IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ∧
        ∃ c : E, c ≠ 0 ∧ specRest (algebraMap k E) g y =
          C c * normForm (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)
            (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y)

def ChowSecDegree.Statement : Prop :=
  ∀ (k E : Type) [Field k] [PerfectField k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), AlgebraicIndependent k y → IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.finrank E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) = chowDegree Q (e + 1)

def SecLinNZD.Statement : Prop :=
  ∀ (k E : Type) [Field k] [PerfectField k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E) (u : Fin n → k), AlgebraicIndependent k y → IsProjPrime Q →
      IsChowForm Q (e + 1) g → linForm u ∉ Q →
        secLin (Q.map (MvPolynomial.map (algebraMap k E))) y (fun j => algebraMap k E (u j)) ∈
          nonZeroDivisors (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)

end

end GroundTheory.Heights₂.Heights.Vertical
end

