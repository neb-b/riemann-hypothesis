module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ResidualNewVarMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem residual_newVar_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u}
    [CommRing R] [IsNoetherianRing R] {P : Ideal (MRing ι R)} [P.IsPrime] {s g f m : MRing ι R}
    (e : K → ℕ) (hfP : f ∉ P) (hmP : m ∉ P) {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)}
    (hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G')
    (hres : 0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G') :
    ∀ j, j ≠ none → (newVar j : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof R (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim hfP hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hres; omega
  rintro (_ | _ | i) hj
  · exact absurd rfl hj
  · exact hY₁G'
  by_contra hYi
  have hrel : liftForm (powMonomial e i) * newVar (some none) -
      liftForm m * newVar (some (some i)) ∈ P' := by
    rw [hP'def, blowUpOf, RingHom.mem_ker]
    simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
    ring
  have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => hYi (hP'G' h)
  by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι R) ∈ P'
  · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
    rw [sub_sub_cancel] at h
    exact (hP'prime.mem_or_mem h).elim hlm hYiP'
  · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
    rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
    simp only [Pi.add_apply] at h1
    have h2 : divCycle P' (newVar (some (some i))) G' = 0 := by
      by_contra h; exact hYi (form_mem_of_divCycle_ne_zero h)
    have h3 := hnonneg (liftForm (powMonomial e i)) G'
    unfold ratDiv at hres; omega

theorem ResidualContractionComponent.proof (hpieces : BlowUpDecomposition.Statement.{u}) :
    ResidualContractionComponent.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', hsc', hsP', -⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have : P.IsPrime := hP.multiProj.isPrime
  have hG'supp : G' ∈ (blowUpOf P (blowUpGens s g f m e) ⊔ Ideal.span {liftForm s}).minimalPrimes ∧
      IsRelevant G' := by
    unfold divCycle at hsG'
    split_ifs at hsG' with hG'
    · exact hG'
    · exact (lt_irrefl _ hsG').elim
  have : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hY := residual_newVar_mem e hD.1.num_not_mem hmP hP'G' hresG'
  have hdim' := ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) _ (d + 1) hP'
    (liftMDeg c) (liftForm s) hsc' hsP' G' hsG'.ne' hϖG'
  have hdim := ringKrullDim_quotient_le_comap_add_one G' none hY
  refine mem_minimalPrimes_of_ringKrullDim P _ s hsP (d + 1 + 1 + Fintype.card K) hP.dim ?_ ?_
  · refine sup_le (fun p hp => hP'G' ?_) ?_
    · rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
        Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hG'supp.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  · rw [Fintype.card_option, show d + 1 + (Fintype.card K + 1) = d + 1 + 1 + Fintype.card K by omega]
      at hdim'
    exact hdim' ▸ hdim

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimLeOfIsAlgebraicAdjoinSingleton
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

theorem ringKrullDim_le_of_isAlgebraic_adjoin_singleton {A B : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) (y : B)
    [Algebra.IsAlgebraic (Algebra.adjoin A ({y} : Set B)) B] (N : ℕ)
    (hA : ringKrullDim A < (N : WithBot ℕ∞)) : ringKrullDim B ≤ (N : WithBot ℕ∞) := by
  rw [ringKrullDim_le_iff_height_le]
  intro 𝔓 h𝔓
  have key := DimensionInequality.full A B hinj 𝔓
  have htd : Algebra.trdeg A B ≤ 1 := by
    simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk A ({y} : Set B)
  have hp : (𝔓.under A).height + 1 ≤ (N : ℕ∞) := by
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top (inferInstance :
      (𝔓.under A).IsPrime))
    have h2 : ((𝔓.under A).height : WithBot ℕ∞) < (N : WithBot ℕ∞) := h1.trans_lt hA
    have h3 : (𝔓.under A).height < (N : ℕ∞) := by exact_mod_cast h2
    exact Order.add_one_le_of_lt h3
  have hc : Cardinal.ofENat 𝔓.height ≤ Cardinal.ofENat (N : ℕ∞) := by
    calc Cardinal.ofENat 𝔓.height
        ≤ Cardinal.ofENat 𝔓.height + Algebra.trdeg (A ⧸ 𝔓.under A) (B ⧸ 𝔓) := le_self_add
      _ ≤ Cardinal.ofENat (𝔓.under A).height + Algebra.trdeg A B := key
      _ ≤ Cardinal.ofENat (𝔓.under A).height + 1 := by gcongr
      _ = Cardinal.ofENat ((𝔓.under A).height + 1) := by simp
      _ ≤ Cardinal.ofENat (N : ℕ∞) := Cardinal.ofENat_le_ofENat.mpr hp
  exact_mod_cast Cardinal.ofENat_le_ofENat.mp hc

private theorem lt_natCast_of_add_one_le_withBotENat {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by norm_cast)
    | coe a =>
      norm_cast at h ⊢

end Helpers

section Proof

theorem ExceptionalContraction.proof (h₁ : BlowUpDecomposition.Statement.{u}) :
    ExceptionalContraction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  obtain ⟨hQm, -, -, hY₀Q, hD₁, -, -, -⟩ :=
    h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH
  set Q := blowUpOf P (blowUpGens s g f m e) with hQdef
  set G := G'.comap (liftForm (J := BlowUpIdx ι)) with hGdef
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hQp : Q.IsPrime := hQm.multiProj.isPrime
  obtain ⟨hG'p, hQG', hG'rel⟩ := le_and_isRelevant_of_divCycle_ne_zero hY₀.ne'
  obtain ⟨hGp, hPG, hGrel, -⟩ := comap_liftForm_facts hG'p hQG' hG'rel

  have hlift : ∀ {p : MRing ι O}, p ∉ P → liftForm (J := BlowUpIdx ι) p ∉ Q :=
    fun hp => liftForm_not_mem_blowUpOf hp
  have hfP : f ∉ P := hD.1.num_not_mem
  have hgP : g ∉ P := hD.1.den_not_mem
  have hY₁Q : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ Q := hD₁.1.num_not_mem
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) Q
  have hnm : ∀ {x y}, x ∉ Q → y ∉ Q → x * y ∉ Q := fun hx hy h => (hQp.mem_or_mem h).elim hx hy
  have e1 := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, hmul _ _ hQp (hnm (hlift hsP) (hlift hgP)) hY₁Q, hmul _ _ hQp (hlift hsP) (hlift hgP),
    hmul _ _ hQp (hlift (fun h => (hPp.mem_or_mem h).elim hfP hmP)) hY₀Q] at e1
  simp only [Pi.add_apply] at e1
  have hE' := hE
  unfold ratDiv at hE'
  rw [hmul _ _ hQp (hlift hgP) hY₁Q] at hE'
  simp only [Pi.add_apply] at hE'
  have hspos : 0 < divCycle Q (liftForm s) G' := by linarith
  have hsG' : liftForm (J := BlowUpIdx ι) s ∈ G' := form_mem_of_divCycle_ne_zero hspos.ne'
  have hsG : s ∈ G := hsG'

  have hY₀G' : (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' :=
    form_mem_of_divCycle_ne_zero hY₀.ne'
  obtain ⟨i, hi⟩ := powMonomial_not_mem hGp hGrel e
  have := hGp
  have := hG'p
  let φ : MRing ι O ⧸ G →+* MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G' :=
    Ideal.quotientMap G' (liftForm (J := BlowUpIdx ι) : MRing ι O →ₐ[O] _).toRingHom le_rfl
  let _ : Algebra (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := φ.toAlgebra
  have hφ : ∀ p : MRing ι O, algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G')
      (Ideal.Quotient.mk G p) = Ideal.Quotient.mk G' (liftForm p) := fun p => Ideal.quotientMap_mk
  have : IsScalarTower O (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := by
    refine IsScalarTower.of_algebraMap_eq (R := O) (S := MRing ι O ⧸ G)
      (A := MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') fun r => ?_
    change Ideal.Quotient.mk G' (algebraMap O (MRing (extIdx ι (BlowUpIdx ι)) O) r) =
      algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (algebraMap O (MRing ι O) r))
    rw [hφ, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, liftForm_C]
  have hinj : Function.Injective (algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G')) :=
    Ideal.quotientMap_injective
  have : Algebra.FiniteType O (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O G') (Ideal.Quotient.mkₐ_surjective O G')
  have : Algebra.FiniteType (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  set y : MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G' := Ideal.Quotient.mk G' (newVar (some (some i))) with hy
  set Cy := Algebra.adjoin (MRing ι O ⧸ G) ({y} : Set (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G'))
  let _ : CommRing Cy := inferInstance
  have hAalg : ∀ a : MRing ι O ⧸ G, IsAlgebraic Cy
      (algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') a) := fun a =>
    isAlgebraic_algebraMap (⟨_, Subalgebra.algebraMap_mem Cy a⟩ : Cy)
  have hpi : Ideal.Quotient.mk G' (liftForm (J := BlowUpIdx ι) (powMonomial e i)) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hi
  have hX : ∀ v, IsAlgebraic Cy (Ideal.Quotient.mk G' (X v : MRing (extIdx ι (BlowUpIdx ι)) O)) := by
    rintro ⟨_ | k, j⟩
    · rcases j with _ | j'
      · change IsAlgebraic Cy (Ideal.Quotient.mk G' (newVar none))
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hY₀G']
        exact isAlgebraic_zero
      · set c : MRing ι O := Option.elim j' m (fun i' => powMonomial e i') with hc
        have hrel : newVar (some j') * liftForm (powMonomial e i) - newVar (some (some i)) * liftForm c ∈ Q :=
          mem_blowUpOf_of_sub (by
            rcases j' with _ | i' <;> simp only [blowUpGens, hc, Option.elim] <;>
              convert P.zero_mem using 1 <;> ring)
        have hrel' := Ideal.Quotient.eq_zero_iff_mem.mpr (hQG' hrel)
        rw [map_sub, map_mul, map_mul] at hrel'
        let a' : Cy := ⟨_, Subalgebra.algebraMap_mem Cy (Ideal.Quotient.mk G (powMonomial e i))⟩
        let z' : Cy := ⟨y * algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G c),
          Cy.mul_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem Cy _)⟩
        refine ⟨Polynomial.C a' * Polynomial.X - Polynomial.C z', fun h0 => hpi ?_, ?_⟩
        · have h1 := congrArg (fun p : Polynomial Cy => p.coeff 1) h0
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, ite_true,
            Polynomial.coeff_C_of_ne_zero one_ne_zero, sub_zero, Polynomial.coeff_zero] at h1
          have h2 := congrArg Subtype.val h1
          simpa [a', hφ] using h2
        · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
          change (algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (powMonomial e i))) *
            Ideal.Quotient.mk G' (newVar (some j')) -
            y * algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G c) = 0
          rw [hφ, hφ, hy]
          linear_combination hrel'
    · rw [← liftForm_X (J := BlowUpIdx ι) (R := O) ⟨k, j⟩, ← hφ]
      exact hAalg _
  have : Algebra.IsAlgebraic Cy (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := ⟨fun x => by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction t using MvPolynomial.induction_on with
    | C r =>
      have : Ideal.Quotient.mk G' (C r : MRing (extIdx ι (BlowUpIdx ι)) O) =
          algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (C r)) := by
        rw [hφ, liftForm_C]
      rw [this]
      exact hAalg _
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p v hp => rw [map_mul]; exact hp.mul (hX v)⟩
  have hdimB := ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q (d + 1) hQm
    (Pi.single none 1) (newVar none) (isWeightedHomogeneous_X _ _ _) hY₀Q G' hY₀.ne' hϖG'
  have hdimA : ¬ ringKrullDim (MRing ι O ⧸ G) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro hlt
    have h := ringKrullDim_le_of_isAlgebraic_adjoin_singleton hinj y _ hlt
    rw [hdimB, Fintype.card_option] at h
    have h' : d + 1 + (Fintype.card K + 1) ≤ d + 1 + Fintype.card K := by exact_mod_cast h
    omega

  have hsum : ringKrullDim (MRing ι O ⧸ (P ⊔ Ideal.span {s})) <
      ((d + 1 + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    have := hPp
    have h := ringKrullDim_succ_le_of_surjective
      (Ideal.Quotient.factor (le_sup_left : P ≤ P ⊔ Ideal.span {s})) (Ideal.Quotient.factor_surjective _)
      (r := Ideal.Quotient.mk P s)
      (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    rw [hP.dim] at h
    exact lt_natCast_of_add_one_le_withBotENat (by convert h using 2; omega)
  exact TopDimMinimal.proof DimStrictDrop.proof (MRing ι O) (P ⊔ Ideal.span {s}) G
    (d + 1 + Fintype.card K) (sup_le hPG ((Ideal.span_singleton_le_iff_mem _).mpr hsG)) hsum hdimA

end Proof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFiniteCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {A : Type*} [CommRing A] (L : Type*) [Field L] [Algebra A L]

def blowUpColon (I : Ideal A) : Submodule A L :=
  ⨆ n : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ n / (Submodule.map (Algebra.linearMap A L) I) ^ n

end Objects

section Lemmas

def BlowUpOverLocInChart.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (J : Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], IsMultiHomogIdeal P → W.IsPrime → P ≤ W → IsRelevant W →
    ∀ (N : K → ℕ) (u : J → MRing ι R), (∀ j, IsMultiHomog (u j) N) → ∀ j, u j ∉ P →
      blowUpOverLoc P W u ≤ Subring.closure ((homLocRing P W : Set (FractionRing (MRing ι R ⧸ P))) ∪
        Set.range fun k =>
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u k)) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u j)))

def ChartsInColon.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (L : Type u) [Field L] [Algebra A L] (J : Type) [Fintype J] (a : J → A) (f : L),
    (∀ j, algebraMap A L (a j) ≠ 0 →
      f ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) →
    f ∈ blowUpColon L (Ideal.span (Set.range a))

def BlowUpColonFinite.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (L : Type u) [Field L]
    [Algebra A L], Function.Injective (algebraMap A L) → ringKrullDim A = 1 →
    ∀ I : Ideal A, I ≠ ⊥ → (blowUpColon L I).FG

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocMaxPoint.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)) (h𝔫 : 𝔫.IsMaximal),
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          (W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W) ∧
          (∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            letI := (Subring.inclusion h).toAlgebra
            haveI := h𝔫.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) ∧
          𝔫.inertiaDeg (homLocRing P W) = specialRelDeg W'

def BlowUpOverLocPointMax.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          letI := (Subring.inclusion h).toAlgebra
          haveI := h𝔫.isPrime
          IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

def BlowUpLocRingInj.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (J : Type)
    (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (Q Q' : Ideal (MRing (extIdx ι J) R)),
    Q.IsPrime → IsMultiHomogIdeal Q → IsRelevant Q → blowUpOf P u ≤ Q →
    Q'.IsPrime → IsMultiHomogIdeal Q' → IsRelevant Q' → blowUpOf P u ≤ Q' →
    blowUpLocRing P u Q = blowUpLocRing P u Q' → Q = Q'

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

