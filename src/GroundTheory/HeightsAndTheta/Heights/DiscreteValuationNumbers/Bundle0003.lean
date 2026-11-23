module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialDimensionInequality
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Polynomial

theorem PolynomialDimensionInequality.proof (h : PolynomialPrimeOverZeroHeight.Statement.{u}) :
    PolynomialDimensionInequality.Statement.{u} := by
  intro A _ _ _ P _
  set p := P.under A with hp
  let I : Ideal A[X] := p.map (algebraMap A A[X])
  let Pb : Ideal (A[X] ⧸ I) := P.map (Ideal.Quotient.mk I)
  have hIP : I ≤ P := Ideal.map_comap_le
  have hPb : Pb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hIP)

  let x : A[X] ⧸ P := Ideal.Quotient.mk P X
  have key : ∀ f : A[X], aeval x (f.map (Ideal.Quotient.mk p)) = Ideal.Quotient.mk P f := by
    intro f
    rw [← Ideal.Quotient.algebraMap_eq, aeval_map_algebraMap]
    change aeval (Ideal.Quotient.mkₐ A P X) f = _
    rw [aeval_algHom_apply, aeval_X_left_apply]
    rfl
  have hsurj : Function.Surjective (aeval (R := A ⧸ p) x) := by
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, key f⟩

  have hPb1 : Pb.height ≤ 1 := by
    let e : (A[X] ⧸ I) ≃+* (A ⧸ p)[X] := (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
    let Q : Ideal (A ⧸ p)[X] := Pb.map e
    have hQ : Q.IsPrime := Ideal.map_isPrime_of_equiv e
    have hQb : Q.comap (C : A ⧸ p →+* (A ⧸ p)[X]) = ⊥ := by
      refine le_bot_iff.mp fun a ha => ?_
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.mem_comap] at ha
      have he : C (Ideal.Quotient.mk p b) = e (Ideal.Quotient.mk I (C b)) := by
        change _ = (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
          (Ideal.Quotient.mk (p.map C) (C b))
        rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]
      rw [he] at ha
      obtain ⟨y, hy, hye⟩ := (Ideal.mem_map_of_equiv e _).mp ha
      rw [e.injective hye, Ideal.mem_quotient_iff_mem hIP] at hy
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hp, Ideal.under_def, Ideal.mem_comap,
        Polynomial.algebraMap_eq]
      exact hy
    have := h (A ⧸ p) Q hQb
    rwa [RingEquiv.height_map] at this
  have hht : P.height ≤ p.height + Pb.height := Ideal.height_le_height_add_of_liesOver p P
  by_cases hb : Pb = ⊥
  ·
    have : Nontrivial (A[X] ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hIP)
    rw [hb, Ideal.height_bot, add_zero] at hht
    have htr : Algebra.trdeg (A ⧸ p) (A[X] ⧸ P) ≤ 1 :=
      (trdeg_le_of_surjective _ hsurj).trans (Polynomial.trdeg_of_isDomain).le
    exact add_le_add (Cardinal.ofENat_le_ofENat.mpr hht) htr
  ·
    obtain ⟨y, hyPb, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨f, hfP, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hyPb
    have hfI : f ∉ I := fun hf => hy0 (Ideal.Quotient.eq_zero_iff_mem.mpr hf)
    have hg : f.map (Ideal.Quotient.mk p) ≠ 0 := by
      intro hg
      apply hfI
      rw [show I = p.map C from rfl, Ideal.mem_map_C_iff]
      intro n
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, hg, coeff_zero]
    have hx : IsAlgebraic (A ⧸ p) x :=
      ⟨_, hg, by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hfP⟩
    have hadj : Algebra.adjoin (A ⧸ p) {x} = ⊤ := by
      rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
      exact hsurj
    have halg : Algebra.IsAlgebraic (A ⧸ p) (A[X] ⧸ P) := by
      have := Algebra.isAlgebraic_adjoin_singleton_iff.mpr hx
      rw [hadj] at this
      exact ⟨fun z => this z Algebra.mem_top⟩
    rw [trdeg_eq_zero_iff.mpr halg, add_zero, ← Cardinal.ofENat_one, ← Cardinal.ofENat_add,
      Cardinal.ofENat_le_ofENat]
    exact hht.trans (add_le_add le_rfl hPb1)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialPrimeOverZeroHeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Polynomial


attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
theorem PolynomialPrimeOverZeroHeight.proof : PolynomialPrimeOverZeroHeight.Statement := by
  intro D _ _ Q _ hQ
  let K := FractionRing D
  have disj : Disjoint ((nonZeroDivisors D).map (C : D →+* D[X]) : Set D[X]) (Q : Set D[X]) := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ ?_
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb.1
    apply hb0
    have : b ∈ Q.comap (C : D →+* D[X]) := by
      rw [Ideal.mem_comap]
      simpa [hb.2] using ha
    rwa [hQ, Ideal.mem_bot] at this
  have hK : ringKrullDim K[X] = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one K[X] (Polynomial.not_isField K)
  have h := IsLocalization.height_map_of_disjoint ((nonZeroDivisors D).map (C : D →+* D[X]))
    (S := K[X]) Q disj
  have hP : (Q.map (algebraMap D[X] K[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors D).map (C : D →+* D[X])) K[X] Q
      ‹_› disj
  have hle : ((Q.map (algebraMap D[X] K[X])).height : WithBot ℕ∞) ≤ 1 :=
    hK ▸ Ideal.height_le_ringKrullDim_of_isPrime
  rw [h] at hle
  exact_mod_cast hle

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PQuotientHeightAddOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem QuotientHeightAddOne.proof : QuotientHeightAddOne.Statement := by
  intro R _ _ I hI P _
  let φ : PrimeSpectrum (R ⧸ I) → PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hφ : StrictMono φ := RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  let z : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩

  have hz : ∀ q : PrimeSpectrum (R ⧸ I), z < φ q := by
    intro q
    refine lt_of_le_of_ne (show z.asIdeal ≤ (φ q).asIdeal from bot_le) fun h => hI ?_
    have hle : I ≤ (φ q).asIdeal := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q.asIdeal.zero_mem
    rw [← h] at hle
    exact le_bot_iff.mp hle
  let p : PrimeSpectrum (R ⧸ I) := ⟨P, ‹_›⟩
  have h1 : P.height = Order.height p := PrimeSpectrum.height_eq_orderHeight p
  have h2 : (P.comap (Ideal.Quotient.mk I)).height = Order.height (φ p) :=
    PrimeSpectrum.height_eq_orderHeight (φ p)
  have hne : Nonempty { l : LTSeries (PrimeSpectrum (R ⧸ I)) // l.last = p } :=
    ⟨⟨RelSeries.singleton _ p, rfl⟩⟩
  rw [h1, h2, Order.height_eq_iSup_last_eq p, iSup_subtype', ENat.iSup_add, iSup_le_iff]
  rintro ⟨l, hl⟩
  let l' : LTSeries (PrimeSpectrum R) :=
    (l.map φ hφ).cons z (by simpa using hz l.head)
  have hlast : l'.last = φ p := by simp [l', hl]
  have := Order.length_le_height (p := l') hlast.le
  simpa [l'] using this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PReesAlgebraDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Polynomial

universe u

theorem ReesAlgebraDim.proof (h₁ : DimensionInequality.Statement.{u, u}) :
    ReesAlgebraDim.Statement.{u} := by
  intro A _ _ _ I hI n hn
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hinj : Function.Injective (algebraMap A (reesAlgebra I)) := by
    intro x y h
    have := congrArg (fun r : reesAlgebra I => (r : A[X])) h
    simpa using this
  apply le_antisymm
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    have key := h₁ A (reesAlgebra I) hinj P
    have htd : Algebra.trdeg A (reesAlgebra I) ≤ 1 := by
      calc Algebra.trdeg A (reesAlgebra I) ≤ Algebra.trdeg A A[X] :=
            trdeg_le_of_injective (reesAlgebra I).val Subtype.val_injective
        _ = 1 := Polynomial.trdeg_of_isDomain
    have hp : (P.under A).height ≤ n := by
      have := Ideal.height_le_ringKrullDim_of_ne_top (inferInstance : (P.under A).IsPrime).ne_top
      rw [hn] at this
      exact_mod_cast this
    have hc : Cardinal.ofENat P.height ≤ Cardinal.ofENat ((n + 1 : ℕ) : ℕ∞) := by
      calc Cardinal.ofENat P.height
          ≤ Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (reesAlgebra I ⧸ P) :=
            le_self_add
        _ ≤ Cardinal.ofENat (P.under A).height + Algebra.trdeg A (reesAlgebra I) := key
        _ ≤ Cardinal.ofENat (n : ℕ∞) + 1 := by gcongr
        _ = Cardinal.ofENat ((n + 1 : ℕ) : ℕ∞) := by simp
    have : P.height ≤ ((n + 1 : ℕ) : ℕ∞) := Cardinal.ofENat_le_ofENat.mp hc
    exact_mod_cast this
  · let f : reesAlgebra I →+* A := (Polynomial.constantCoeff).comp (reesAlgebra I).val.toRingHom
    have hf : Function.Surjective f := fun x => ⟨algebraMap A (reesAlgebra I) x, by simp [f]⟩
    let r : reesAlgebra I := ⟨monomial 1 a, reesAlgebra.monomial_mem.mpr (by simpa using haI)⟩
    have hr0 : r ≠ 0 := by
      intro h
      have := congrArg (fun s : reesAlgebra I => (s : A[X])) h
      simp [r] at this
      exact ha0 this
    have h := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero hr0)
      (by simp [f, r])
    rw [hn] at h
    exact_mod_cast h
end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u v

abbrev LengthFormulaDimTwo.Statement : Prop := ReciprocityTheory.ChartRestriction.G.AI.LocalLengthMultiplicativity.{u}

def ConservationOfNumber.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ a : Fin d → K → ℤ,
        cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a


open scoped Classical in
open Classical in
def CutByEffectiveDivisor.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
      ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
      (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
          cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
              else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)

def VerticalDivisorsCommute.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b b' : K → ℤ) (f g f' g' : MRing ι O),
        IsVerticalDivisor P ϖ b f g → IsVerticalDivisor P ϖ b' f' g' →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g) =
          cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g')

section Examples

theorem isPrime_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    W.IsPrime := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.1
  · exact absurd rfl h

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDvrConeDimTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def DvrConeDimTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
      ringKrullDim (MRing ι O ⧸ P) =
        (((Algebra.trdeg O (MRing ι O ⧸ P)).toENat + 1 : ℕ∞) : WithBot ℕ∞)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericDimGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def GenericDimGe.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    P.IsPrime → P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι O ⧸ P) ≤ ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMultAtOfSaturated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def MultAtOfSaturated.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) (ι : K → Type) (J Q : Ideal (MRing ι R)) [Q.IsPrime],
    J ≤ Q → (∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) → Q ∈ J.minimalPrimes ∧ multAt J Q = 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

