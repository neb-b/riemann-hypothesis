module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0207
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BoundedDenominatorsOfBeta
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def ClassTermBound : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ → ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ l : ℕ, l.Prime → ∃ N : ℕ, ∀ Q : Finset (HeightOneSpectrum (OF H.E)),
      IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF H.E) ∉ q.asIdeal) → ∀ (y : (Af H.E)ˣ) (T : ℂ),
        IsClassTerm φ s κ (condQ 𝔣 Q) χ y T → IntAt l ((l : ℂ) ^ N * (T / Ω))

def ClassTermBoundBeta : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ → ∀ Λ : PeriodPair, Λ.ω₁ = 1 → Λ.ω₂ = (1 + Complex.I * (Real.sqrt H.d : ℝ)) / 2 →
      ∀ l : ℕ, l.Prime → ∃ N : ℕ, ∀ Q : Finset (HeightOneSpectrum (OF H.E)),
      IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF H.E) ∉ q.asIdeal) → ∀ (y : (Af H.E)ˣ) (T : ℂ),
        IsClassTerm φ s κ (condQ 𝔣 Q) χ y T → IntAt l ((l : ℂ) ^ N * beta H.E H.d s κ Λ T)

theorem intAt_of_pow {l m : ℕ} (hm : 0 < m) {a : ℂ} (h : IntAt l (a ^ m)) : IntAt l a := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, IsIntegral.of_pow hm ?_⟩
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : IsIntegral ℤ ((n : ℂ) ^ m) := (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))).pow m |> fun h => by simpa using h
  have e : ((n : ℂ) * a) ^ (m + 1) = (n : ℂ) ^ m * ((n : ℂ) * a ^ (m + 1)) := by ring
  rw [e]
  exact h1.mul h

theorem intAt_natMul {l : ℕ} (k : ℕ) {a : ℂ} (h : IntAt l a) : IntAt l ((k : ℂ) * a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  have h1 : IsIntegral ℤ (k : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (k : ℤ))
  rw [mul_left_comm]
  exact h1.mul h

def ringPair (d : ℕ) (hd : 0 < d) : PeriodPair where
  ω₁ := 1
  ω₂ := (1 + Complex.I * (Real.sqrt d : ℝ)) / 2
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h2 : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp at hi hr
    have hb : b = 0 := by
      rcases hi with hi | hi
      · exact hi
      · omega
    subst hb
    simpa using hr

theorem classTermBound_of_beta (h : ClassTermBoundBeta) : ClassTermBound := by
  intro R H I _ φ s κ 𝔣 χ hD
  have hd : 0 < H.d := H.hypOdd.2.1.pos
  set Λ := ringPair H.d hd
  have hC : ((C0 H.E H.d (2 * s) κ : ℝ) : ℂ) ≠ 0 := by
    have := hD.2.2.1
    exact_mod_cast (cmValueConst_pos H.E hd (by omega) κ).ne'
  have hΔ : latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (latDisc_ne_zero Λ)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) (n := 12) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hz]; simp)
  refine ⟨z / C0 H.E H.d (2 * s) κ, div_ne_zero hz0 hC, fun l hl => ?_⟩
  obtain ⟨N, hN⟩ := h R H I φ s κ 𝔣 χ hD Λ rfl rfl l hl
  refine ⟨N, fun Q hQ hQl y T hT => intAt_of_pow (m := 12) (by norm_num) ?_⟩
  have := intAt_natMul (l ^ (11 * N)) (hN Q hQ hQl y T hT)
  convert this using 1
  unfold beta
  rw [← hz]
  push_cast
  field_simp
  ring

section Integral

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l : ℕ}

theorem isIntegral_of_intAt (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (ι : ℂ →+* AlgebraicClosure (FractionRing O)) {a : ℂ}
    (h : IntAt l a) : IsIntegral O (ι a) := by
  obtain ⟨n, hn, h⟩ := h
  have hu : IsUnit (n : O) := by
    by_contra hu
    have hn' : (n : O) ∈ IsLocalRing.maximalIdeal O := hu
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hn
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have : (x : O) * n + (y : O) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hxy
      rw [← this]
      exact add_mem (Ideal.mul_mem_left _ _ hn') (Ideal.mul_mem_left _ _ hl)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have h2 : IsIntegral O (ι ((n : ℂ) * a)) := h.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h3 := (isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := v)).mul h2
  have h4 := congrArg (algebraMap O (AlgebraicClosure (FractionRing O))) hv
  rw [map_mul, map_natCast, map_one] at h4
  rwa [map_mul, map_natCast, ← mul_assoc, h4, one_mul] at h3

theorem exists_pow_mul_isIntegral (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (u : AlgebraicClosure (FractionRing O)) :
    ∃ M : ℕ, IsIntegral O ((l : AlgebraicClosure (FractionRing O)) ^ M * u) := by
  have ha : IsAlgebraic O u :=
    (IsFractionRing.isAlgebraic_iff O (FractionRing O) _).2 (Algebra.IsAlgebraic.isAlgebraic u)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hl
  obtain ⟨c, hc⟩ := hl
  refine ⟨n, ?_⟩
  have h3 := (isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := c ^ n * (↑v⁻¹ : O))).mul hint
  refine (congrArg (IsIntegral O) ?_).mpr h3
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← map_natCast (algebraMap O (AlgebraicClosure (FractionRing O))), ← map_pow, hc]
  congr 2
  rw [mul_assoc, ← mul_assoc (↑v⁻¹ : O), Units.inv_mul, one_mul, mul_pow, mul_comm]

theorem exists_eq_of_isIntegral {x : FractionRing O}
    (h : IsIntegral O (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O)) x)) :
    ∃ y : O, algebraMap O (FractionRing O) y = x :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algebraMap_iff ).1 h)

end Integral

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_bound_at (h : ClassTermBound) {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {s : ℕ}
    (ht : IsToricEltAt X i ι lam s) :
    ∃ n : ℕ, ∀ Q, BlochKatoReduction.Gen.QOk X i Q → ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
      ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q lam δ := by
  obtain ⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, -, hth⟩ := ht
  obtain ⟨Ω, hΩ, hb⟩ := h D.R D.host I φ s κ 𝔣 χ hD
  obtain ⟨n, hn⟩ := hb (X.l i) (X.lPrime i).out
  obtain ⟨M, hM⟩ := exists_pow_mul_isIntegral (X.O_l i) (u * ι Ω)
  refine ⟨M + n, fun Q hQ δ => exists_eq_of_isIntegral ?_⟩
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth Q hQ
  obtain ⟨h1, h2⟩ := placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣
  have hf : ({q | π q⁻¹ = δ} : Set (PicO (condQ 𝔣 (belowSet Q)))).Finite := Set.toFinite _
  have hs : IsIntegral (X.O i) (∑ q ∈ hf.toFinset, ι (((X.l i : ℕ) : ℂ) ^ n * (T q / Ω))) :=
    IsIntegral.sum _ fun q _ => isIntegral_of_intAt (X.O_l i) ι (hn _ h1 h2 _ _ (hT q))
  refine (congrArg (IsIntegral (X.O i)) ?_).mpr (hM.mul hs)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_pow, map_natCast, hδ, finsum_mem_eq_finite_toFinset_sum _ hf, ← map_sum, ← Finset.mul_sum, ← Finset.sum_div,
    map_mul, map_pow, map_natCast, map_div₀]
  have : ι Ω ≠ 0 := (map_ne_zero ι).2 hΩ
  field_simp
  ring

variable (X)

theorem exists_gen_bound (h : ClassTermBound) (ht : IsToricElt X) : ∃ N0 : X.Tw → ℕ, BlochKatoReduction.Gen.adm9 X N0 := by
  classical
  have key : ∀ (i : X.Tw) (lam : X.abelian₂ i), ∃ n : ℕ, X.NonzeroIndexPlace i → ∀ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s → ∀ Q, BlochKatoReduction.Gen.QOk X i Q →
      ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
        ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q lam δ := by
    intro i lam
    by_cases hx : X.NonzeroIndexPlace i ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s
    · obtain ⟨hi, s, hs⟩ := hx
      obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)
      obtain ⟨ι, -, hι⟩ := ht i hi
      obtain ⟨n, hn⟩ := exists_bound_at h (hι lam s hs)
      exact ⟨n, fun _ _ _ => hn⟩
    · exact ⟨0, fun hi s hs => (hx ⟨hi, s, hs⟩).elim⟩
  choose n hn using key
  refine ⟨fun i => Finset.univ.sup (n i), fun i hi Q hQ lam s hs δ => ?_⟩
  obtain ⟨y, hy⟩ := hn i lam hi s hs Q hQ δ
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n i) (Finset.mem_univ lam))
  refine ⟨((X.l i : ℕ) : X.O i) ^ k * y, ?_⟩
  rw [map_mul, map_pow, map_natCast, hy]
  show _ = _ ^ (Finset.univ.sup (n i)) * _
  rw [hk]
  ring

end Record

end GlobalTheory.ToricDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColAddGenRenameCastSucc
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching.AddColumn

theorem weight_mapDomain (r n : ℕ) (u : Fin r × Fin n →₀ ℕ) :
    (∀ i : Fin n, Finsupp.weight (colW r (n + 1))
        (Finsupp.mapDomain (Prod.map id Fin.castSucc) u) i.castSucc = Finsupp.weight (colW r n) u i) ∧
      Finsupp.weight (colW r (n + 1)) (Finsupp.mapDomain (Prod.map id Fin.castSucc) u) (Fin.last n) = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, ha.1, hb.1]
    · rw [Finsupp.mapDomain_add, map_add (f := _), Pi.add_apply, ha.2, hb.2]
  | single v k =>
    refine ⟨fun i => ?_, ?_⟩
    · simp [Finsupp.mapDomain_single, Finsupp.weight_single, colW, Pi.single_apply]
    · simp [Finsupp.mapDomain_single, Finsupp.weight_single, colW, Pi.single_apply,
        (Fin.castSucc_lt_last v.2).ne']

theorem colAddGen_rename_castSucc (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l.castSucc j.castSucc
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) =
      rename (Option.map (Prod.map id Fin.castSucc)) (colAddGen R l j f) := by
  have e : (colAddGen R (r := r) l.castSucc j.castSucc).comp
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
      (rename (Option.map (Prod.map id Fin.castSucc))).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hv : s = j
    · simp [colAddGen, hv]
    · simp [colAddGen, hv]
  exact DFunLike.congr_fun e f

theorem colAddGen_rename_last (R : Type*) [CommRing R] {r n : ℕ} (l : Fin (n + 1))
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l (Fin.last n)
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) =
      rename some (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) := by
  have e : (colAddGen R (r := r) l (Fin.last n)).comp
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
      (rename some).comp (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [colAddGen, (Fin.castSucc_lt_last s).ne]
  exact DFunLike.congr_fun e f

theorem add_column : ∀ (r n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → (∀ f ∈ dualWeyl ℂ r n (fun i => ν i.castSucc), rename (Prod.map id Fin.castSucc) f ∈ dualWeyl ℂ r (n + 1) ν) ∧ ∀ (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ), rowAct ℂ g (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) = rename (Prod.map id Fin.castSucc) (rowAct ℂ g f) := by
  intro r n ν hν
  refine ⟨fun f hf => ?_, fun g f => ?_⟩
  · simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
    refine ⟨fun d hd => ?_, fun l j hlj => ?_⟩
    · obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
      have h := hf.1 hu
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [(weight_mapDomain r n u).2, hν]
      · rw [(weight_mapDomain r n u).1, h]
    · induction j using Fin.lastCases with
      | last => exact colAddGen_rename_last ℂ l f
      | cast j =>
        induction l using Fin.lastCases with
        | last => exact absurd hlj (not_lt.2 (Fin.le_last _))
        | cast l =>
          rw [colAddGen_rename_castSucc, hf.2 l j (Fin.castSucc_lt_castSucc_iff.1 hlj), rename_rename,
            rename_rename]
          rfl
  · have e : (rowAct ℂ g).comp (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
        (rename (Prod.map id Fin.castSucc)).comp (rowAct ℂ g) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, s⟩
      simp [rowAct]
    exact DFunLike.congr_fun e f

end GlobalTheory.Branching.AddColumn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjugateModularFunctionSomeLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_conj_of_inR : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω) (f : ℍ → ℂ), InR ε.range f → ∃ f' : ℍ → ℂ, InR ε.range f' ∧ ∀ h h' : HahnSeries ℚ Ω, IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s f hf
  obtain ⟨N, w, hN, hLv⟩ := hf
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.FN.exists_ringEquiv_extend_of_embedding Ω ε s
  have hgE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨s y, (hg y).symm⟩
  obtain ⟨d, hd⟩ := GlobalTheory.WpFam.exists_unit_zetaAct N g
  obtain ⟨f', hLv', hconj⟩ := _root_.GlobalTheory.FN.lv_galois_conj g ε.range N d w f hgE hd hLv
  refine ⟨f', ⟨N, w, hN, hLv'⟩, ?_⟩
  intro h h' hh hh' r
  have h1 : dg d * redGL N 1 = redGL N 1 * dg d := by
    rw [GlobalTheory.WpFam.Act.redGL_one]; simp
  have hc := hconj 1 1 h1
  simp only [one_smul] at hc
  have hq := hLv.2 1
  simp only [one_smul] at hq
  exact _root_.GlobalTheory.FN.exp_conj Ω ε s.toRingHom g N w f f' h h' hg hN hq hc hh hh' r

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemWpNormSubLtOne
section
open Formalism.MainNotions

namespace GlobalTheory.ResidueRoot

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : ℂ_[p])‖ ≤ 1; simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : ℂ_[p])‖ ≤ 1; simp
  neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rw [norm_neg]; exact ha

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_add_lt_one {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem sub_one_lt_of_pow_p {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p - 1‖ < 1) : ‖y - 1‖ < 1 := by
  let Y : ball p := ⟨y, hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (Y - 1) 1
  have hr' := congrArg (fun t : ball p => (t : ℂ_[p])) hr
  simp only [sub_add_cancel, one_pow, mul_one] at hr'
  push_cast at hr'
  have hz : ‖y - 1‖ ≤ 1 := (Y - 1).2
  have hrr : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have e : (y - 1) ^ p = (y ^ p - 1) + -((p : ℂ_[p]) * (y - 1) * r) := by
    have : (Y : ℂ_[p]) = y := rfl
    rw [this] at hr'
    rw [hr']; ring
  have h2 : ‖(y - 1) ^ p‖ < 1 := by
    rw [e]
    refine norm_add_lt_one h ?_
    rw [norm_neg, norm_mul, norm_mul, mul_assoc]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_p_lt_one
      (mul_le_one₀ hz (norm_nonneg _) hrr)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).1 h2

theorem sub_one_lt_of_pow_p_pow (k : ℕ) {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p ^ k - 1‖ < 1) :
    ‖y - 1‖ < 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply sub_one_lt_of_pow_p
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    · rwa [← pow_mul, ← pow_succ]

theorem exists_root {x : ℂ_[p]} {m : ℕ} (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[p], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm hξ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  rw [e, norm_prod] at h
  by_contra hc
  push Not at hc
  refine absurd h (not_lt.2 ?_)
  exact Finset.prod_induction _ (fun r : ℝ => 1 ≤ r) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun ζ hζ => hc ζ ((mem_nthRootsFinset hm _).1 hζ)

theorem exists_pow_alg (x : PadicAlgCl p) (hx : ‖x‖ = 1) : ∃ n, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | (apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one ..)

end GlobalTheory.ResidueRoot

namespace GlobalTheory

open ResidueRoot

theorem exists_mem_Wp_norm_sub_lt_one (p : ℕ) [hp : Fact p.Prime] (x : ℂ_[p]) (hx : ‖x‖ ≤ 1) :
    ∃ w ∈ GL3Theta.Wp p, ‖x - w‖ < 1 := by
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) x 1 one_pos
  rw [dist_eq_norm] at hy
  have hy1 : ‖(y : ℂ_[p])‖ ≤ 1 := by
    have : (y : ℂ_[p]) = x + -(x - y) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  rcases hy1.lt_or_eq with h | h
  · refine ⟨0, zero_mem _, ?_⟩
    have := norm_add_lt_one hy h
    simpa using this
  · obtain ⟨n, hn, hyn⟩ := exists_pow_alg y (by rwa [PadicComplex.norm_extends] at h)
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))
    have h3 : ‖((y : ℂ_[p]) ^ m) ^ p ^ k - 1‖ < 1 := by
      rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, map_pow, map_one,
        ← PadicComplex.coe_eq] at hyn
      rwa [← pow_mul, mul_comm]
    have h4 := sub_one_lt_of_pow_p_pow k
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy1) h3
    obtain ⟨ζ, hζ, h5⟩ := exists_root hm0 h4
    refine ⟨ζ, Subring.le_topologicalClosure _ (Subring.subset_closure
      ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm, hζ⟩), ?_⟩
    have := norm_add_lt_one hy h5
    simpa using this

end GlobalTheory
end

