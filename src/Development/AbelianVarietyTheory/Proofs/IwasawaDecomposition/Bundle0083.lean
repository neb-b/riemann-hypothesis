module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumFactorial
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogKer

theorem exists_sum_factorial {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (l : ℕ) (hl : 0 < l)
    (hA : IsAdicComplete (Ideal.span {(l : A)}) A) (γ : ℕ → R) :
    ∃ Y : A, ∀ r n : ℕ, l ^ r ≤ n → ∃ w : A,
      Y = f (∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : R) * γ k) + (l : A) ^ r * w := by
  obtain ⟨Y, hY⟩ := LogEx.exists_sum (l : A) (fun k => f ((-1) ^ k * ((k.factorial : ℕ) : R) * γ k))
    (fun r => l ^ r) (fun a b hab => Nat.pow_le_pow_right hl hab) (fun r k hk => by
      obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hl r) hk
      refine ⟨f ((-1) ^ k * (m : R) * γ k), ?_⟩
      simp only [hm, map_mul, map_natCast, Nat.cast_mul, Nat.cast_pow, map_pow]
      ring)
  refine ⟨Y, fun r n hn => ?_⟩
  obtain ⟨w, hw⟩ := hY r n hn
  exact ⟨w, by rw [map_sum, ← hw]; ring⟩

theorem sum_eq {P : Type} [CommRing P] (u γ : ℕ → P) (x : P) (hu : ∀ k : ℕ, ((k + 1 : ℕ) : P) * u k = 1)
    (hγ : ∀ k : ℕ, (((k + 1).factorial : ℕ) : P) * γ k = x ^ (k + 1)) (n : ℕ) :
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : P) * γ k =
      ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hγ k, Nat.factorial_succ, Nat.cast_mul]
  linear_combination (-((-1) ^ k * ((k.factorial : ℕ) : P) * γ k)) * hu k

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem exists_log : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ z : Per.Ainf l, Per.θ l z = 0 → ∃ Y : Per.Acris l, ∀ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * Per.ev l n (j Y) = Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1)) := by
  intro l _ j hj z hz
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  have hγ : ∀ k : ℕ, ∃ γ : Per.Acris0 l, (((k + 1).factorial : ℕ) : Per.AinfP l) * (γ : Per.AinfP l) =
      (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := fun k => by
    obtain ⟨d, hd⟩ := (hf (k + 1)).exists_right_inv
    have h : (((k + 1).factorial : ℕ) : Per.AinfP l) *
        (d * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1)) =
        (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := by rw [← mul_assoc, hd, one_mul]
    exact ⟨⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l z (k + 1) _ hz h⟩, h⟩
  choose γ hγ using hγ
  have hmem : algebraMap (Per.Ainf l) (Per.AinfP l) z ∈ Per.kerP l :=
    GlobalTheory.RingIface.alg_mem_kerP l hz
  obtain ⟨Y, hY⟩ := exists_sum_factorial (algebraMap (Per.Acris0 l) (Per.Acris l)) l
    (Fact.out : l.Prime).pos (acris_basic l).1 γ
  refine ⟨Y, fun n => ?_⟩
  have hs : ∀ m : ℕ, ((∑ k ∈ Finset.range m, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * γ k :
      Per.Acris0 l) : Per.AinfP l) =
      ∑ k ∈ Finset.range m, (-1) ^ k * u k * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := by
    intro m
    rw [← sum_eq u (fun k => (γ k : Per.AinfP l)) _ hu hγ m]
    change (Per.Acris0 l).val _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_pow, map_natCast, map_neg, map_one]
    rfl
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (_root_.GlobalTheory.MemLoc.crisP_unique_equivariant l j hj).2.2 n Y (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨w, hw⟩ := hY r (max (l ^ r) n) (le_max_left _ _)
    refine ⟨_, w, 0, hw, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ hmem (le_max_right _ _)))
  rw [key, LogFun.ev_alg]
  simpa only [map_mul, map_natCast] using congrArg (Ideal.Quotient.mk (Per.kerP l ^ n)) hc

end GlobalTheory.MemLoc.LogKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZetaPowCloseToUnitZpow
section
open NumberField IsDedekindDomain

namespace GlobalTheory.TamePowTeich

variable {Ω : Type} [Field Ω]

theorem valuation_pow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) : ∀ k : ℕ, A.valuation (x ^ k - y ^ k) < 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [h]
    apply Valuation.map_add_lt
    · rw [map_mul, hx, one_mul]; exact ih
    · rw [map_mul, map_pow, hy, one_pow, mul_one]; exact hxy

theorem valuation_zpow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) (e : ℤ) : A.valuation (x ^ e - y ^ e) < 1 := by
  cases e with
  | ofNat k => simpa using valuation_pow_sub_lt A hx hy hxy k
  | negSucc k =>
    simp only [zpow_negSucc]
    have hxk : A.valuation (x ^ (k + 1)) = 1 := by rw [map_pow, hx, one_pow]
    have hyk : A.valuation (y ^ (k + 1)) = 1 := by rw [map_pow, hy, one_pow]
    have hx0 : x ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxk; exact zero_ne_one hxk
    have hy0 : y ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hyk; exact zero_ne_one hyk
    rw [inv_sub_inv hx0 hy0, map_div₀, map_mul, hxk, hyk, mul_one, div_one, Valuation.map_sub_swap]
    exact valuation_pow_sub_lt A hx hy hxy (k + 1)

end GlobalTheory.TamePowTeich

open GlobalTheory.TamePowTeich in
theorem GlobalTheory.TamePowTeich.exists_zeta_pow_close : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ P A ζ hA hζ u e hu
  classical
  set n := Formalism.ConjugateSelfDual.normV P - 1 with hn_def
  letI : Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Formalism.ConjugateSelfDual.normV P = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    show Nat.card _ = _
    exact Nat.card_eq_fintype_card
  have hn : 0 < n := by
    have : 1 < Fintype.card (𝓞 E ⧸ P.asIdeal) := Fintype.one_lt_card
    omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero, hn_def, hcard]
    apply FiniteField.pow_card_sub_one_eq_one
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  set U : Ω := algebraMap E Ω (u : E) with hU
  have hUn : A.valuation (U ^ n - 1) < 1 := by
    have := (hA (u ^ n - 1)).2 hmem
    simpa [hU] using this
  have hUint : U ∈ A := by
    apply ReciprocityTheory.Gal.mem_of_isIntegral_int
    exact (u.isIntegral_coe).algebraMap
  have hU1 : A.valuation U = 1 := by
    apply le_antisymm ((A.valuation_le_one_iff U).2 hUint)
    rw [← not_lt]
    intro h
    exact hu ((hA u).1 h)
  have hζ1 : A.valuation ζ = 1 :=
    ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hn.ne' hζ.pow_eq_one

  have hprod : U ^ n - 1 = ∏ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), (U - μ) := by
    have := congrArg (Polynomial.eval U) (Polynomial.X_pow_sub_one_eq_prod hn hζ)
    simpa [Polynomial.eval_prod] using this
  have hex : ∃ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), A.valuation (U - μ) < 1 := by
    by_contra hcon
    push_neg at hcon
    have : 1 ≤ A.valuation (U ^ n - 1) := by
      rw [hprod, map_prod]
      exact Finset.one_le_prod' hcon
    exact absurd hUn (not_lt.2 this)
  obtain ⟨μ, hμ, hμU⟩ := hex
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hn 1).1 hμ)
  have hb1 : A.valuation (ζ ^ b) = 1 := by rw [map_pow, hζ1, one_pow]
  have hclose : A.valuation (ζ ^ b - U) < 1 := by
    rw [Valuation.map_sub_swap, hb]; exact hμU
  have key := valuation_zpow_sub_lt A hb1 hU1 hclose e

  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  refine ⟨((b * e) % (n : ℤ)).toNat, ?_⟩
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnonneg : 0 ≤ (b * e) % (n : ℤ) := Int.emod_nonneg _ hnz
  have hpow : (ζ ^ b) ^ e = ζ ^ ((b * e) % (n : ℤ)).toNat := by
    have h1 : ζ ^ ((b * e) % (n : ℤ)).toNat = ζ ^ ((b * e) % (n : ℤ)) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg]
    rw [h1, ← zpow_natCast ζ b, ← zpow_mul]
    conv_lhs => rw [← Int.emod_add_mul_ediv ((b : ℤ) * e) n]
    rw [zpow_add₀ hζ0, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]
  rw [← hpow]
  exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasSignatureDiagonalSgn
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem hasSignature_diagonal_sgn (N : ℕ) (neg : Fin N → Bool) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i : Fin N => (Examples₂.sgn (neg i) : ℂ))
      (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card := by
  classical
  let e1 : {i // neg i = false} ≃ Fin (Finset.univ.filter fun i => neg i = false).card :=
    Fintype.equivFinOfCardEq (Fintype.card_subtype _)
  let e2 : {i // ¬ neg i = false} ≃ Fin (Finset.univ.filter fun i => neg i = true).card :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simp)
  let f : Fin (Finset.univ.filter fun i => neg i = false).card ⊕
      Fin (Finset.univ.filter fun i => neg i = true).card ≃ Fin N :=
    (Equiv.sumCongr e1.symm e2.symm).trans (Equiv.sumCompl fun i => neg i = false)
  have h1 : ∀ i, neg (f (Sum.inl i)) = false := fun i => (e1.symm i).2
  have h2 : ∀ i, neg (f (Sum.inr i)) = true := fun i => by
    have h : ¬ neg (f (Sum.inr i)) = false := (e2.symm i).2
    simpa using h
  refine ⟨f.symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h1, h2, Examples₂.sgn]
  split_ifs <;> simp

theorem stdSpace_sigOK_count (E : Type) [Field E] [NumberField E] [StarRing E]
    (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) (neg : Fin N → Bool) :
    (Formalism.BasicNotions.Examples₂.stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card).SigOK := by
  intro τ
  have hg : (Formalism.BasicNotions.Examples₂.stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card).gram.map τ =
      Matrix.diagonal fun i : Fin N => (Examples₂.sgn (neg i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (Examples₂.stdSpace_gram_apply hstar N neg _ _ i j)).trans ?_
    change τ (if i = j then (Examples₂.sgn (neg i) : E) else 0) =
      if i = j then (Examples₂.sgn (neg i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, Examples₂.map_sgn]
  rw [hg]
  exact hasSignature_diagonal_sgn N neg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSstResToOfIsPst
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstSst

variable {l : ℕ} [Fact l.Prime]

theorem apply_mem_kur (g : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (c : Om l) ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    conv_lhs => rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨x, ⟨m, h0, hm, hx⟩, rfl⟩
    exact ⟨m, h0, hm, by rw [← map_pow, hx, map_one]⟩
  exact h ⟨c, c.2, rfl⟩

theorem mem_of_fixed (K : FinExt l) (x : Om l) (hx : ∀ g ∈ GK K, g x = x) : x ∈ K.1 := by
  have : IsGalois ℚ_[l] (Om l) := {}
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
  exact hx

def incl (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  IntermediateField.inclusion (inf_le_right : K.1 ⊓ MaximalUnramifiedExtension l ≤ MaximalUnramifiedExtension l)

section

variable (P : LocPrime l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
  (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem mulV_smul (q : ℚ_[l]) (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) :
    mulV P LL V (q • c) x = q • mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, mulV_tmul, ← tmul_smul, ← smul_mul_assoc]
    congr 2
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, smul_C]
    congr 1
    exact map_smul (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) q c
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

def comb (K' : FinExt l) {n : ℕ} (b : Fin n → V ⊗[ℚ_[l]] Bst P) :
    (Fin n → ↥(K0 K')) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P where
  toFun c := ∑ i, mulV P LL V (incl K' (c i)) (b i)
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' q c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mulV_smul]
    exact congrArg (fun a => mulV P LL V a (b i)) (map_smul (incl K').toLinearMap q (c i))

variable {LL V} {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

theorem coe_sum {n : ℕ} (b : Fin n → DpstUr P ρ) (c : Fin n → ↥(MaximalUnramifiedExtension l)) :
    (((toUr P ρ).symm (∑ i, c i • b i) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      ∑ i, mulV P LL V (c i) (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Submodule.coe_sum]
  rfl

theorem finrank_dst {n : ℕ} (b : Basis (Fin n) ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)) (K' : FinExt l) (h : K.1 ≤ K'.1)
    (hb : ∀ i (g : ↥(GK K)), (g : GQ l) ∈ GK K' →
      stRep P ρ g ((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) = ((toUr P ρ).symm (b i) : ↥(Dpst P ρ))) :
    finrank ℚ_[l] ↥(Dst P (resTo ρ h)) = n * finrank ℚ_[l] ↥(K0 K') := by
  have := K'.2
  have hle : K0 K' ≤ K'.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] ↥(K0 K') :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  set β : Fin n → V ⊗[ℚ_[l]] Bst P := fun i => ((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) with hβ
  have huniq : ∀ c d : Fin n → ↥(MaximalUnramifiedExtension l),
      ∑ i, mulV P LL V (c i) (β i) = ∑ i, mulV P LL V (d i) (β i) → c = d := by
    intro c d hcd
    rw [← coe_sum, ← coe_sum] at hcd
    have h1 := (toUr P ρ).symm.injective (Subtype.ext hcd)
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h1
    exact b.equivFun.symm.injective h1
  have hact : ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' → ∀ c : Fin n → ↥(MaximalUnramifiedExtension l),
      stRep P ρ g (∑ i, mulV P LL V (c i) (β i)) =
        ∑ i, mulV P LL V ⟨_, apply_mem_kur (g : GQ l) (c i)⟩ (β i) := by
    intro g hg c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← End.mul_apply, stRep_mulV P ρ g (c i) ⟨_, apply_mem_kur (g : GQ l) (c i)⟩ rfl, End.mul_apply,
      hb i g hg]
  have hinj : Function.Injective (comb P LL V K' β) := fun c d hcd =>
    funext fun i => (incl K').injective (congrFun (huniq _ _ hcd) i)
  have hrange : LinearMap.range (comb P LL V K' β) = (Dst P (resTo ρ h)).restrictScalars ℚ_[l] := by
    ext x
    rw [Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨c, rfl⟩
      refine (mem_Dst_resTo P ρ h).mpr fun g hg => ?_
      refine (hact g hg fun i => incl K' (c i)).trans (Finset.sum_congr rfl fun i _ => ?_)
      congr 2
      exact Subtype.ext (mem_GK.mp hg _ (c i).2.1)
    · intro hx
      let c : Fin n → ↥(MaximalUnramifiedExtension l) := b.repr (toUr P ρ ⟨x, Dst_resTo_le P ρ h hx⟩)
      have hc : ∑ i, mulV P LL V (c i) (β i) = x := by
        rw [← coe_sum, b.sum_repr, AddEquiv.symm_apply_apply]
      have hK : ∀ i, (c i : Om l) ∈ K'.1 := fun i => mem_of_fixed K' _ fun g hg => by
        have h1 := hact ⟨g, GK_le h hg⟩ hg c
        rw [hc, (mem_Dst_resTo P ρ h).mp hx ⟨g, GK_le h hg⟩ hg, ← hc] at h1
        exact (congrArg Subtype.val (congrFun (huniq _ _ h1) i)).symm
      exact ⟨fun i => ⟨c i, hK i, (c i).2⟩, hc⟩
  have h1 := LinearMap.finrank_range_of_inj hinj
  rw [hrange, finrank_pi_fintype] at h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  exact h1

end

theorem isSst_resTo_of_isPst (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type)
    [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (hV : IsPst P ρ) :
    ∃ (K₁ : FinExt l), K.1 ≤ K₁.1 ∧
      ∀ (K' : FinExt l) (h : K.1 ≤ K'.1), K₁.1 ≤ K'.1 → IsSst P (resTo ρ h) := by
  have := LL.2
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨_, hdim⟩ := (isPst_iff P ρ).mp hV
  let b := finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)
  choose F hF using fun i => (mem_Dpst P ρ).mp ((toUr P ρ).symm (b i)).2
  have := fun i => (F i).2
  refine ⟨supExt K ⟨⨆ i, (F i).1, inferInstance⟩, le_sup_left, fun K' h h₁ => ?_⟩
  have h1 := finrank_dst P ρ b K' h fun i g hg =>
    hF i g (GK_le (K := F i) (((le_iSup (fun i => (F i).1) i).trans le_sup_right).trans h₁) hg)
  rw [hdim, ← finrank_mul_finrank ℚ_[l] ↥LL.1 V, ← finrank_mul_finrank ℚ_[l] ↥LL.1, mul_assoc] at h1
  rw [IsSst, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

end GlobalTheory.PstSst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonVEqZeroIffMemRangeCrisIncl
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

theorem monV_eq_zero_iff_mem_range_crisIncl {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (x : V ⊗[ℚ_[l]] Bst P) : monV P LL V x = 0 ↔ ∃ y, crisIncl P LL V y = x := by
  have h : Function.Exact (CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap (monSt P) := fun p =>
    (monSt_eq_zero_iff P p).trans ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  exact Module.Flat.lTensor_exact V h x

theorem mem_Dst_and_monV_eq_zero_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V ⊗[ℚ_[l]] Bst P), (x ∈ Dst P ρ ∧ monV P ↥LL.1 V x = 0) ↔ x ∈ (Dcris (P.PD K) ρ).map (crisIncl P ↥LL.1 V) := by
  intro l _ P K LL V _ _ _ _ ρ x
  have key : ∀ y, crisIncl P ↥LL.1 V y ∈ Dst P ρ ↔ y ∈ Dcris (P.PD K) ρ := fun y => by
    rw [mem_Dst, Dcris, Submodule.mem_iInf]
    refine forall_congr' fun g => ?_
    rw [stRep_crisIncl, (crisIncl_injective P).eq_iff, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  rw [monV_eq_zero_iff_mem_range_crisIncl, Submodule.mem_map]
  constructor
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, (key y).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(key y).mpr hy, y, rfl⟩

end GlobalTheory.Pst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdNormEmbeddingsEqAbsNorm
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem prod_norm_embeddings_eq_abs_norm (E : Type) [Field E] [NumberField E] (γ : E) :
    ∏ φ : E →+* ℂ, ‖φ γ‖ = |((Algebra.norm ℚ γ : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ γ
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod, eq_ratCast] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => ‖φ γ‖)
    (fun φ : E →ₐ[ℚ] ℂ => ‖φ γ‖) (fun _ => rfl), ← h2]
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  simp

theorem norm_typeNorm_sq_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (γ : E) (σ : K →+* ℂ), ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ n := by
  intro E _ _ _ _ r n hr K _ hK γ σ
  let s : (E →+* ℂ) → (E →+* ℂ) := fun τ => σ.comp (τ.codRestrict K (hK τ))
  have hs : ∀ τ x, s τ x = σ ⟨τ x, hK τ x⟩ := fun _ _ => rfl
  have hinj : Function.Injective s := by
    intro a b hab
    ext x
    have := DFunLike.congr_fun hab x
    rw [hs, hs] at this
    exact congrArg Subtype.val (σ.injective this)
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  have hconj : ∀ τ, ‖s (ComplexEmbedding.conjugate τ) γ‖ = ‖s τ γ‖ := by
    intro τ
    have h1 : s (ComplexEmbedding.conjugate τ) γ = s τ (IsCMField.complexConj E γ) := by
      rw [hs, hs]
      congr 2
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    rw [h1, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have hinv : Function.Involutive
      (fun τ : E →+* ℂ => ComplexEmbedding.conjugate τ) := fun τ => star_star τ
  have hP : ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ := by
    rw [map_prod, norm_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, norm_pow, hs]
  have hQ : ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ
      = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r (ComplexEmbedding.conjugate τ) := by
    rw [← hinv.bijective.prod_comp (fun τ => ‖s τ γ‖ ^ r τ)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hconj]
  rw [hP, sq]
  nth_rewrite 2 [hQ]
  rw [← Finset.prod_mul_distrib, ← prod_norm_embeddings_eq_abs_norm,
    ← hbij.prod_comp (fun φ => ‖φ γ‖), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← pow_add, hr]

end GlobalTheory.Mem
end

