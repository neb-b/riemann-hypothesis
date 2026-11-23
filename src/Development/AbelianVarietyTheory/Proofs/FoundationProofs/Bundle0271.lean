module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.HarderNarasimhan.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuadraticCharNegOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0266

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeSumWeylAndDualWeylLatticesLe
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

private theorem selfDualK_full {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : IsSelfDualK G M) : Submodule.IsFullLattice K M := by
  classical
  haveI : Submodule.IsLattice K M := hM.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hM.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin n → K) → K := fun x => star x ⬝ᵥ G *ᵥ y
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) s f
  have ha0 : (algebraMap (𝓞 K) K a) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 K) (Fin n → K) := {
    carrier := {x | ∃ b : 𝓞 K, (b : K) = (algebraMap (𝓞 K) K a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : K) + c = _
      rw [hb, hc]
      simp [f, dotProduct, Matrix.mulVec, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd K) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def,
        RingOfIntegers.mapRingHom_apply, Pi.star_apply, star_mul, dotProduct, Matrix.mulVec,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : K) * _ = _
      ring }
  have hsP : (s : Set (Fin n → K)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 K) K a) • y ∈ M := by
    rw [← hM.2]
    change ∀ x ∈ M, star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) ∈ (1 : Submodule (𝓞 K) K)
    intro x hx
    obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
    have hpair : (b : K) = star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) := by
      rw [hb]
      simp only [f, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    refine ⟨b, ?_⟩
    simpa [LinearMap.toSpanSingleton_apply, Algebra.smul_def] using hpair
  have hy' : (algebraMap (𝓞 K) K a) • y ∈ Submodule.span K (M : Set (Fin n → K)) :=
    Submodule.subset_span hy
  have := (Submodule.span K (M : Set (Fin n → K))).smul_mem (algebraMap (𝓞 K) K a)⁻¹ hy'
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem testLatticeCondition_sumLat_nabK_and_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  classical
  obtain ⟨s, hs0, hs, hlog⟩ := _root_.GlobalTheory.extNorm_eq_nat_log_le_bound K ι n lam R hR hsp
  have hlat := fun c => _root_.GlobalTheory.TransLattice.nabDelLattice K ι n lam (M c) (fun τ => selfDualK_full (G τ) (M c τ) (hM c τ))
  have main : ∀ T : C → Submodule (𝓞 K) (VV K lam), (∀ c, Submodule.IsFullLattice K (T c)) →
      (∀ c, T c ≤ nabK lam (M c)) → TestLatticeCondition N X (sumLat lam e T) (bound (Fintype.card ι) n R) := by
    intro T hT hle
    obtain ⟨hL, hN, -⟩ := GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual K ι n lam C N e T (fun c => (hT c).toIsLattice)
    haveI : Finite C :=
      Finite.of_injective (fun c => e.symm (c, (e ⟨0, hN⟩).2)) (fun a b h => by
        simpa using h)
    letI : Fintype C := Fintype.ofFinite C
    obtain ⟨hval, hdef, -, hdet⟩ := _root_.GlobalTheory.TestLat.sumGram_spec K ι n lam G hG C N e
    have hne : sumLat lam e T ≠ ⊥ := by
      intro h
      obtain ⟨c⟩ := (inferInstance : Nonempty C)
      obtain ⟨i⟩ := GlobalTheory.TestLat.SumLat.idx_nonempty lam
      have ht : ∃ t ∈ T c, t ≠ 0 := by
        by_contra hn
        push_neg at hn
        have hb : T c = ⊥ := by
          apply le_antisymm _ bot_le
          intro t ht
          simpa using hn t ht
        have hs := (hT c).span_eq_top
        rw [hb] at hs
        have hv := congrArg (fun S : Submodule K (VV K lam) => (bVV K lam i) ∈ S) hs
        have hv0 : bVV K lam i = 0 := by simpa using hv
        exact (bVV K lam).ne_zero i hv0
      obtain ⟨t, ht, ht0⟩ := ht
      let f := GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e
      let z := f.symm (Pi.single c t)
      have hz : z ∈ sumLat lam e T := by
        rw [GlobalTheory.TestLat.Model.mem_sumLat]
        intro c'
        have heq : valAt lam e c' z = (Pi.single c t : C → VV K lam) c' :=
          congrFun (f.apply_symm_apply (Pi.single c t)) c'
        rw [heq]
        by_cases hc : c' = c
        · subst hc; simpa using ht
        · simp [Pi.single_eq_of_ne hc]
      rw [h] at hz
      have hz0 : z = 0 := by simpa using hz
      have heq := congrFun (f.apply_symm_apply (Pi.single c t)) c
      change valAt lam e c z = (Pi.single c t : C → VV K lam) c at heq
      rw [hz0, map_zero, Pi.single_eq_same] at heq
      exact ht0 heq.symm
    refine ⟨hL.fg, hne, fun v => (hX v).1, le_trans ?_ hlog⟩
    refine _root_.GlobalTheory.muMaxDef_le_log_of_integral K v₀ hv N (sumGram lam e G) X ⟨hdef.2.1, hX⟩ s hs0 _ hL.fg hne ?_
    intro x hx y hy
    rw [hval, Finset.mul_sum, ← hs]
    refine Subring.sum_mem _ fun c _ => ?_
    have hmem : ∀ z ∈ sumLat lam e T, valAt lam e c z ∈ nabK lam (M c) := fun z hz =>
      hle c ((Submodule.mem_iInf _).1 hz c)
    exact _root_.GlobalTheory.PairInt.extNorm_mul_pairK_integral K ι n lam G (M c) (fun τ => (hG τ).1) hdet (hM c) _ (hmem x hx) _ (hmem y hy)
  exact ⟨main _ (fun c => (hlat c).1) (fun c => le_rfl),
    main _ (fun c => (hlat c).2) (fun c => delLeNab K ι n lam (M c))⟩

end GlobalTheory.TestLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MinkowskiBoundComapLattice
section
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Compare

section Space

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Space

section Sum

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}

end Sum

section DualSpace

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}

end DualSpace

section Nabla

variable {K : Type} [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}


omit [NumberField K] in
theorem pairK_basis [StarRing K] (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (i j : VVIdx lam) :
    pairK lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j) =
      pairBK lam (bVV K lam i) (rhoK lam g (bVV K lam j)) := by
  rw [pairK_apply, pairP_eq_pairB, pairBK_apply, rhoK_coe]
  congr 2
  rw [bVV_coe]
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [hQ, MvPolynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

def gramB (K : Type) [Field K] (lam : ι → DomWeight n) : Matrix (VVIdx lam) (VVIdx lam) K :=
  Matrix.of fun i j => pairBK lam (bVV K lam i) (bVV K lam j)

omit [NumberField K] in
theorem gramB_transpose (lam : ι → DomWeight n) : (gramB K lam)ᵀ = gramB K lam := by
  ext i j
  simp only [gramB, Matrix.transpose_apply, Matrix.of_apply, pairBK_apply]
  exact pairingBSymm_holds K ι n lam _ _

theorem hdualFr_triv {m : ℕ} (P : Matrix (Fin m) (Fin m) K) (M : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) :
    x ∈ @hdualFr K _ m starRingOfComm P M ↔ P *ᵥ x ∈ dualFr M := by
  change (∀ y ∈ M, y ⬝ᵥ (P *ᵥ x) ∈ (1 : Submodule (𝓞 K) K)) ↔ ∀ y ∈ M, (P *ᵥ x) ⬝ᵥ y ∈ (1 : Submodule (𝓞 K) K)
  simp only [dotProduct_comm]

end Nabla

section Clauses

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι C : Type} [Fintype ι] {n N : ℕ}
  (emb : ι → E →+* K) (lam : ι → DomWeight n) (R : ℝ) (J : Matrix (Fin n) (Fin n) E)
  (L : C → Submodule (𝓞 E) (Fin n → E)) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ)

end Clauses

end GlobalTheory.TestLat.Compare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NoRatInert
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise
open Formalism.FrobeniusOrbits GlobalTheory.NormSign

namespace GlobalTheory.NormSignInert

theorem descent_rat {d q : ℕ} [Fact d.Prime] (hq : q.Prime) (hne : q ≠ d) {u : ℤ}
    (hu : quadraticChar (ZMod d) (-(u : ZMod d)) = -1) (C X Y : ℚ)
    (h : C ^ 2 * u + X ^ 2 = q * d * Y ^ 2) : C = 0 := by
  have key := descent hq hne (quadraticChar_neg_one_iff_not_isSquare.1 hu) _ (C.num * X.den * Y.den)
    (X.num * C.den * Y.den) (Y.num * C.den * X.den) rfl (by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [← Rat.mul_den_eq_num C, ← Rat.mul_den_eq_num X, ← Rat.mul_den_eq_num Y]
      linear_combination ((C.den : ℚ) ^ 2 * X.den ^ 2 * Y.den ^ 2) * h)
  simpa [X.den_nz, Y.den_nz] using key

theorem char_eq {d q : ℕ} [Fact d.Prime] [Fact q.Prime] (hd : d % 4 = 3) (h2 : q ≠ 2) (hne : q ≠ d) :
    quadraticChar (ZMod d) q = quadraticChar (ZMod q) (-(d : ZMod q)) := by
  have hl2 : ringChar (ZMod d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h := quadraticChar_card_card hl2 (F' := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
    (by rwa [ZMod.ringChar_zmod_n, ZMod.ringChar_zmod_n])
  rw [quadraticChar_neg_one' hd, ZMod.card, ZMod.card] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem no_rat_inert {q d : ℕ} [Fact d.Prime] (h : HostHyp q d) {m : ℕ} (hm : EvenSq d m) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : Odd f) (hpd : p ≠ d → ¬ IsSquare (-(d : ZMod p))) (A W : ℚ) :
    W ^ 2 ≠ q * d * (A ^ 2 - 4 * (p ^ f * m)) := by
  obtain ⟨hq, hd, hq8, hd16, hj⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, u, rfl, hu⟩ := hm
  have h1 := hq.pos
  have h2 := hd.pos
  intro hW
  push_cast at hW
  by_cases hpd' : p = d
  · subst hpd'
    obtain ⟨j, rfl⟩ := hf
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym] at hj
    push_cast at hj
    rw [← char_eq (d := p) (q := q) (by omega) (by omega) (by omega)] at hj
    have key := descent_rat (d := p) hq (by omega) (u := q * u) (by
      rw [← neg_one_mul, map_mul, quadraticChar_neg_one' (by omega)]
      push_cast
      rw [map_mul, hj, hu]; norm_num) (2 * p ^ (j + k + 1)) W A (by
      push_cast
      linear_combination hW)
    have : (0 : ℚ) < 2 * p ^ (j + k + 1) := by positivity
    exact this.ne' key
  · have h3 := quadraticChar_neg_one_iff_not_isSquare.2 (hpd hpd')
    rw [← char_eq (d := d) (q := p) (by omega) hp2 hpd'] at h3
    have key := descent_rat (d := d) hq (by omega) (u := -(p ^ f * u)) (by
      push_cast
      rw [neg_neg, map_mul, map_pow, h3, hu, hf.neg_one_pow]; norm_num) (2 * q * d * d ^ k) (q * d * A) W (by
      push_cast
      linear_combination (-(q * d : ℚ)) * hW)
    have : (0 : ℚ) < 2 * q * d * d ^ k := by positivity
    exact this.ne' key

theorem exists_norm {R : Ranks} (H : Host R) (t : H.E) (ht : H.conj t = t) :
    ∃ n A W : ℚ, (n : H.E) = part H t (1, 1) * part H t (-1, 1) ∧ W ^ 2 = H.q * H.d * (A ^ 2 - 4 * n) := by
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  set s := part H (t : H.E) (1, 1) with hs
  set s' := part H (t : H.E) (-1, 1) with hs'
  have e1 : part H (t : H.E) (-1, -1) = s := by rw [part_neg H ht]; simp [hs]
  have e2 : part H (t : H.E) (1, -1) = s' := by rw [part_neg H ht]; simp [hs']
  have key : ∀ g : R.GG, (g.1.1 * g.1.2 = 1 ∧ H.sigmaOf g s = s ∧ H.sigmaOf g s' = s') ∨
      (g.1.1 * g.1.2 = -1 ∧ H.sigmaOf g s = s' ∧ H.sigmaOf g s' = s) := by
    rintro ⟨⟨u, v⟩, h⟩
    rw [hs, hs', sigmaOf_part, sigmaOf_part]
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [e1, e2, ← hs, ← hs']
  obtain ⟨n, hn⟩ := exists_rat H (x := s * s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_mul, h1, h2]
    ring
  obtain ⟨A, hA⟩ := exists_rat H (x := s + s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_add (f := _), h1, h2]
    ring
  obtain ⟨W, hW⟩ := exists_rat H (x := (s - s') * (H.sqq * H.sqd)) fun g => by
    rw [map_mul, map_mul, map_sub, sigmaOf_aE, sigmaOf_bE, mul_mul_mul_comm, ← Int.cast_mul, ← Units.val_mul]
    rcases key g with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> push_cast <;> ring
  refine ⟨n, A, W, hn, ?_⟩
  apply Rat.cast_injective (α := H.E)
  push_cast
  rw [hW, hA, hn, mul_pow, mul_pow, ha, hb]
  ring

theorem norm_neg : ∀ (D : D7) (t : 𝓞 D.host.E) (P B : Ideal (𝓞 D.host.E)), t ≠ 0 →
    D.host.conj (t : D.host.E) = t → P.IsMaximal → D.host.conj • P = P →
    Ideal.span {t} = P * B * (D.host.conj • B) → (∏ τ, embT D τ (t : D.host.E)).re < 0 := by
  intro D t P B ht0 ht hP hc hB
  obtain ⟨-, p, f, hp, -, hp2, -, hf, hN, hpd⟩ := (_root_.GlobalTheory.InertResidue.norm_prime D P hP).2.1 hc
  rw [prod_embT]
  generalize D.host = H at *
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact ht0 (by simpa using hB)
  have hm := evenSq_absNorm H.hyp ha hb B hB0
  have hm0 : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨n, A, W, hn, hWn⟩ := exists_norm H (t : H.E) ht
  have hn2 : n ^ 2 = ((p : ℚ) ^ f * (Ideal.absNorm B : ℚ)) ^ 2 := by
    have h1 : Algebra.norm ℚ (t : H.E) = n ^ 2 := by
      apply Rat.cast_injective (α := H.E)
      rw [norm_eq H ht]
      push_cast
      rw [hn]
    have h2 := congrArg Ideal.absNorm hB
    rw [map_mul, map_mul, absNorm_smul, Ideal.absNorm_span_singleton, hN] at h2
    have h3 := congrArg (fun k : ℕ => ((k : ℤ) : ℚ)) h2
    simp only [Int.natCast_natAbs] at h3
    push_cast at h3
    rw [Algebra.coe_norm_int, h1, abs_of_nonneg (sq_nonneg _)] at h3
    rw [h3]; ring
  rw [← hn, map_ratCast, Complex.ratCast_re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hn2 with h | h
  · exact absurd (by rw [hWn, h]) (no_rat_inert H.hyp hm hp hp2 hf hpd A W)
  · have := hp.pos
    have h0 : (0 : ℚ) < (p : ℚ) ^ f * (Ideal.absNorm B : ℚ) := by positivity
    have h1 : n < 0 := by rw [h]; exact neg_neg_of_pos h0
    exact_mod_cast h1

end GlobalTheory.NormSignInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqOneDistributive
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.DistTriple

theorem bc_eq_one {D : D7} {T : Tor D} {N N' : ℕ} {A₁ A₂ A₃ : AddSubgroup (VC D N N')}
    (h₁ : Nice D T A₁) (h₂ : Nice D T A₂) (h₃ : Nice D T A₃) (hd : Dist A₁ A₂ A₃)
    {x y : VC D N N'} (hx : x ∈ A₂) (hy : y ∈ A₃) (hxy : y + x ∈ A₁) : bc D T y x = 1 := by
  have hm := hd x hx y hy (by rwa [add_comm])
  obtain ⟨x₁, hx₁, x₃, hx₃, rfl⟩ := AddSubgroup.mem_sup.1 hm
  have hy₃ : y + x₃ ∈ A₁ := by
    have := A₁.sub_mem hxy hx₁.1
    have e : y + (x₁ + x₃) - x₁ = y + x₃ := by abel
    rwa [e] at this
  have e1 := h₁.2.1 _ hy₃ _ hx₁.1
  rw [bc_add_left, h₂.2.1 _ hx₃.1 _ hx₁.2, mul_one] at e1
  rw [bc_add_right, e1, h₃.2.1 _ hy _ hx₃.2, mul_one]

theorem const_eq_one : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N'))
    (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → Dist A₁ A₂ A₃ → μ = 1 := by
  intro D T N N' A₁ A₂ A₃ e μ ht hd
  obtain ⟨r, hr, hs⟩ := _root_.GlobalTheory.TripleConstant.mu_form D T N N' A₁ A₂ A₃ e μ ht
  obtain ⟨h₁, h₂, h₃, -, -, -, -, -, h8, -⟩ := ht
  have key : ∃ s : ℝ, 0 ≤ s ∧ μ * (r : ℂ) = (s : ℂ) := by
    rw [hs]
    refine finsum_induction (fun z : ℂ => ∃ s : ℝ, 0 ≤ s ∧ z = (s : ℂ)) ⟨0, le_rfl, by simp⟩ ?_ ?_
    · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_nonneg ha hb, by push_cast; rfl⟩
    · intro p
      split_ifs with h
      · exact ⟨1, zero_le_one, by
          rw [bc_eq_one h₁ h₂ h₃ hd (Quotient.out p.2 : A₂).2 (Quotient.out p.1 : A₃).2 h]; simp⟩
      · exact ⟨0, le_rfl, by simp⟩
  obtain ⟨s, hs0, hμ⟩ := key
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hμ' : μ = ((s / r : ℝ) : ℂ) := by
    push_cast; rw [eq_div_iff hr', hμ]
  rw [hμ'] at h8 ⊢
  have h8' : (s / r) ^ 8 = 1 := by exact_mod_cast h8
  have := (pow_eq_one_iff_of_nonneg (div_nonneg hs0 hr.le) (by norm_num)).1 h8'
  rw [this]; simp

end GlobalTheory.DistTriple
end

