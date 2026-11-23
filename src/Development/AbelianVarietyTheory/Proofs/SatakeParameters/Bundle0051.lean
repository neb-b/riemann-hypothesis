module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBounds
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

private theorem cast_succ_div_two_of_odd {t : ℕ} (ht : Odd t) :
    (((t + 1) / 2 : ℕ) : ℝ) = ((t : ℝ) + 1) / 2 := by
  obtain ⟨k, rfl⟩ := ht
  have h : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h]
  push_cast
  ring

theorem _root_.GlobalTheory.HTW.wHat_le : ∀ {D : _root_.Formalism.BasicNotions.D7} (L : _root_.Formalism.BasicNotions.SizeData₂ D) (C : ℝ),
    _root_.GlobalTheory.HTW.Roomy L C →
    (_root_.GlobalTheory.HTW.wHat D : ℝ) = _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + (L.etaSz + D.R.t + 2) ≤ 2 * L.sc.b' ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + _root_.GlobalTheory.HTW.sHat L + _root_.GlobalTheory.HTW.etaHat L + 1
      ≤ 2 * L.sc.b' := by
  intro D L C hL
  have hw : (_root_.GlobalTheory.HTW.wHat D : ℝ) =
      _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 := by
    unfold _root_.GlobalTheory.HTW.wHat
    push_cast [cast_succ_div_two_of_odd D.R.t_odd]
    rfl
  have hmax := (_root_.GlobalTheory.HTW.wMax_le_and_ge L C hL).1
  have hR := hL
  unfold _root_.GlobalTheory.HTW.Roomy at hR
  obtain ⟨-, -, h3, h4, -, -⟩ := hR
  have hS := L.Sc_pos
  have hE := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hfS : (_root_.GlobalTheory.HTW.sHat L : ℝ) ≤ L.Sc := by
    unfold _root_.GlobalTheory.HTW.sHat
    exact Nat.floor_le hS.le
  have hfE : (_root_.GlobalTheory.HTW.etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold _root_.GlobalTheory.HTW.etaHat
    push_cast
    linarith [Nat.floor_le hE.le]
  refine ⟨hw, ?_, ?_⟩
  · rw [hw]; nlinarith
  · rw [hw]; nlinarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimitiveRootNotPrimePowMapNeOne
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory

theorem primitiveRoot_notPrimePow_map_ne_one :
    ∀ (k : Type) [Field k] (O : Type) [CommRing O] [IsDomain O] (f : O →+* k) (ζ : O) (n : ℕ),
      1 < n → IsPrimitiveRoot ζ n → (¬ IsPrimePow n) → f ζ ≠ 1 := by
  intro k _ O _ _ f ζ n hn hζ hpp h1
  have hroot : IsRoot (cyclotomic n O) ζ := hζ.isRoot_cyclotomic (by omega)
  have h0 : eval (f ζ) (cyclotomic n k) = 0 := by
    rw [← map_cyclotomic n f, eval_map, eval₂_at_apply, hroot.eq_zero, map_zero]
  have hone : eval (1 : k) (cyclotomic n k) = 1 := by
    apply eval_one_cyclotomic_not_prime_pow
    intro p hp j hj
    exact hpp (hj ▸ (Nat.Prime.isPrimePow hp).pow (by rintro rfl; simp at hj; omega))
  rw [h1, hone] at h0
  exact one_ne_zero h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement
section
noncomputable section

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem normV_pos (w : PlE H) : 0 < normV w := by
  have h := GlobalTheory.LocalInv.one_lt_normV w
  have : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by linarith
  exact_mod_cast this

theorem frob_one {w : PlE H} {a : A.LP w} (hu : A.unr a) (hd : A.lpDim a = 1) : ∃ c, A.frobEig a = {c} :=
  Multiset.card_eq_one.1 (by rw [A.frobEig_card a hu, hd])

theorem eta_frob (hAut : At.TieAut N A) (w : PlE H) : ∃ b, A.frobEig (A.locG A.etaT w) = {b} ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := frob_one (A.etaT_unr w) (A.locG_dim A.etaT w)
  refine ⟨b, hb, (A.tempered_unr _ (A.etaT_unr w)).1 (hAut.2.2.1 w) b ?_⟩
  rw [hb]
  exact Multiset.mem_singleton_self b

theorem norm_first_character_frobenius (hAut : At.TieAut N A) (i : N.Loc) {w : PlE H} (hw : SplitOut N i w)
    (huμ : A.unr (A.locG (A.muC i) w)) {B : ValuationSubring N.Om} {σ : G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    ‖A.iotaQC i (iotaOQ N A i (chi1 N i σ))‖ =
      (normV w : ℝ) ^ (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2) := by
  obtain ⟨hu, hf⟩ := A.chi_mu i w hw
  have e : A.frobEig (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2)) =
      {A.iotaQC i (iotaOQ N A i (chi1 N i σ))} := hf B σ hB hσ
  rw [A.frobEig_tw _ _ hu, A.locG_tw] at e
  obtain ⟨m, hm⟩ := frob_one huμ (A.locG_dim (A.muC i) w)
  have hm1 : ‖m‖ = 1 := (A.tempered_unr _ huμ).1 (hAut.2.2.2 i w) m (by rw [hm]; exact Multiset.mem_singleton_self m)
  obtain ⟨b, hb, hb1⟩ := eta_frob hAut w
  obtain ⟨hui, hfi⟩ := A.etaTinv_def w
  have hfi' : A.frobEig (A.locG A.etaTinv w) = {b⁻¹} := by rw [hfi, hb, Multiset.map_singleton]
  have hfe := A.frobEig_char (A.locG (A.muC i) w) (A.locG A.etaTinv w) b⁻¹ huμ hui (A.locG_dim _ w) hfi'
  rw [hfe, hm, Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at e
  rw [← e, norm_mul, norm_mul, hm1, norm_inv, hb1, inv_one, one_mul, one_mul,
    Complex.norm_natCast_cpow_of_pos (normV_pos w), Complex.ofReal_re]

theorem eps_frob (i : N.Loc) {w : PlE H} (hl : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    A.iotaQC i (iotaOQ N A i ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i)) = (normV w : ℂ) := by
  have hc := cycZ_of_isFrob (F := H.E) (Ω := N.Om) (l := N.l i) (by simpa [placesOver] using hl) hB hσ
  have e1 : ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [e1, hc]
  show A.iotaQC i (A.iotaQ i (algebraMap (N.O i) (FractionRing (N.O i))
    (algebraMap ℤ_[N.l i] (N.O i) ((normV w : ℕ) : ℤ_[N.l i])))) = _
  rw [A.iotaQ_alg i, PadicInt.coe_natCast, map_natCast, map_natCast]

end GlobalTheory.FrobeniusCharacterNorms

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

end GlobalTheory.FrobeniusCharacterNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitBCOfGalIso
section
noncomputable section

namespace GlobalTheory.SplitDetermines

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_unr (p : Part A.CG) (w : PlE H) (h : A.unr (A.locG p.π w)) : A.unr (spehLoc N A p w) := by
  unfold spehLoc
  induction List.range p.d with
  | nil => exact A.lpZero_unr w
  | cons k l ih => exact (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 h, ih⟩

theorem isoLoc_unr_ae (P : List (Part A.CG)) : ∀ᶠ w in Filter.cofinite, A.unr (isoLoc N A P w) := by
  induction P with
  | nil => exact Filter.Eventually.of_forall fun w => A.lpZero_unr w
  | cons p P ih =>
    filter_upwards [ih, A.locG_unr_ae p.π] with w h1 h2
    exact (A.unr_sum _ _).2 ⟨spehLoc_unr N A p w h2, h1⟩

end GlobalTheory.SplitDetermines

namespace GlobalTheory.RowTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

end GlobalTheory.RowTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingleton
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.SixthNumerics

theorem numerics : Numerics := by
  intro r t d n a A hr ht had hw hsum hpos hn hle
  have hd : d = t + 2 * a := by omega
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hmem : ∀ x ∈ A, x = 1 := by
    intro x hx
    have h1 := Multiset.count_le_of_le x hle
    rw [Multiset.count_nsmul] at h1
    have hc : 1 ≤ Multiset.count x A := Multiset.one_le_count_iff_mem.mpr hx
    have h2 : d ≤ Multiset.count x (r ::ₘ Multiset.replicate t 1) :=
      le_trans (by nlinarith) h1
    by_contra hx1
    rw [Multiset.count_cons, Multiset.count_replicate] at h2
    split_ifs at h2 <;> omega
  have hrep : A = Multiset.replicate (Multiset.card A) 1 := Multiset.eq_replicate_card.mpr hmem
  have hcard : 1 ≤ Multiset.card A := Multiset.card_pos.mpr hA
  have h1 := Multiset.count_le_of_le 1 hle
  rw [Multiset.count_nsmul, Multiset.count_cons, Multiset.count_replicate_self] at h1
  have hc1 : Multiset.count 1 A = Multiset.card A := by
    conv_lhs => rw [hrep]
    exact Multiset.count_replicate_self _ _
  rw [hc1] at h1
  have hr1 : (1 : ℕ) ≠ r := by omega
  simp [hr1] at h1
  have hsum' : n = Multiset.card A := by
    rw [← hsum, hrep]; simp
  have : Multiset.card A = 1 := by nlinarith
  refine ⟨by omega, ?_⟩
  have : a = 0 := by nlinarith
  omega

theorem rest : Rest := by
  intro ι _ d A r hd hA hs
  have hc := congrArg Multiset.card hs
  have hc' : ∑ k, d k * Multiset.card (A k) = 1 := by
    rw [Multiset.card_sum] at hc
    simpa [Multiset.card_nsmul] using hc
  have hterm : ∀ k, 1 ≤ d k * Multiset.card (A k) := fun k =>
    Nat.mul_le_mul (hd k) (Multiset.card_pos.mpr (hA k))
  have hle : ∀ k, d k * Multiset.card (A k) = 1 := by
    intro k
    have := Finset.single_le_sum (f := fun k => d k * Multiset.card (A k))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    have := hterm k
    omega
  have hcardle : Fintype.card ι ≤ 1 := by
    have := Finset.card_nsmul_le_sum Finset.univ (fun k => d k * Multiset.card (A k)) 1
      (fun k _ => hterm k)
    simp at this
    omega
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs
  have hcard : Fintype.card ι = 1 := le_antisymm hcardle Fintype.card_pos
  refine ⟨hcard, fun k => ?_⟩
  have hdk : d k = 1 := Nat.eq_one_of_mul_eq_one_right (hle k)
  refine ⟨hdk, ?_⟩
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcardle
  rw [Finset.sum_eq_single k (fun b _ hb => absurd (Subsingleton.elim b k) hb)
    (fun h => absurd (Finset.mem_univ k) h), hdk, one_smul] at hs
  exact hs

theorem numerics_and_rest : Numerics ∧ Rest := ⟨numerics, rest⟩

end GlobalTheory.SixthNumerics
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamified
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CartanCoinv

open GlobalTheory.PRep

section Gen
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)

theorem sub_mem_coinv {k : G} (hk : k ∈ K) (v : V) : ρ k v - v ∈ twKer ρ K 1 :=
  Submodule.subset_span ⟨⟨k, hk⟩, v, by simp⟩

theorem apply_mem_coinv {k : G} (hk : k ∈ K) {v : V} (hv : v ∈ twKer ρ K 1) : ρ k v ∈ twKer ρ K 1 := by
  have := (twKer ρ K 1).add_mem (sub_mem_coinv ρ K hk v) hv
  simpa using this

theorem mem_coinv_of_eigen {k : G} (hk : k ∈ K) {v : V} {c : ℂ} (hc : c ≠ 1) (hv : ρ k v = c • v) :
    v ∈ twKer ρ K 1 := by
  have h := (twKer ρ K 1).smul_mem (c - 1)⁻¹ (sub_mem_coinv ρ K hk v)
  have e : (c - 1)⁻¹ • (ρ k v - v) = v := by
    have : ρ k v - v = (c - 1) • v := by rw [hv, sub_smul, one_smul]
    rw [this, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc), one_smul]
  rwa [e] at h

end Gen

def diagUnit {R : Type} [CommRing R] {a : ℕ} (f : Fin a → Rˣ) : GL (Fin a) R where
  val := Matrix.diagonal fun i => (f i : R)
  inv := Matrix.diagonal fun i => ((f i)⁻¹ : Rˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

theorem exists_diag {L : Type} [Field L] (O : Subring L) {a : ℕ} (ha : 1 ≤ a) (u : Lˣ) (h1 : (u : L) ∈ O)
    (h2 : ((u⁻¹ : Lˣ) : L) ∈ O) : ∃ d ∈ Formalism.UG.GLint (Fin a) O, Matrix.GeneralLinearGroup.det d = u ∧
      ∃ f : Fin a → L, (d : Matrix (Fin a) (Fin a) L) = Matrix.diagonal f := by
  let u' : Oˣ := ⟨⟨u, h1⟩, ⟨(u⁻¹ : Lˣ), h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  let f : Fin a → Oˣ := Function.update 1 ⟨0, ha⟩ u'
  have hm : ((Formalism.UG.bc O.subtype (diagUnit f) : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.diagonal fun i => ((f i : O) : L) := by
    change (Matrix.diagonal fun i => (f i : O)).map O.subtype = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
  refine ⟨Formalism.UG.bc O.subtype (diagUnit f), ⟨_, rfl⟩, ?_, _, hm⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hm, Matrix.det_diagonal,
    Finset.prod_eq_single (⟨0, ha⟩ : Fin a)]
  · simp [f, u']
  · intro b _ hb
    simp [f, Function.update_of_ne hb]
  · simp

theorem translate_mem_twKer : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := a), ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
  intro E _ _ w a V _ _ ρ χ u ha hu hχ y hy g
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, e⟩ :=
    Formalism.UG.Final.CartanDecomp E w a ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ g
  set D : GL (Fin a) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hg : g = k₁ * D * k₂ := by rw [hDdef]; group
  clear_value D
  have h1 : (u : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v (u : w.adicCompletion E) ≤ 1
    exact hu.le
  have h2 : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  obtain ⟨d, hd, hdet, f, hf⟩ := exists_diag (Formalism.UG.Ov E w) ha u h1 h2
  have hcomm : d * D = D * d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, hf, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hDy : ρ D y ∈ twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
    refine mem_coinv_of_eigen ρ _ hd (c := (((χ u)⁻¹ : ℂˣ) : ℂ)) ?_ ?_
    · intro h
      exact hχ (inv_eq_one.1 (Units.ext h))
    · rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hy d hd, hdet, map_smul]
  rw [hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hy k₂ hk₂, map_smul, map_smul]
  exact Submodule.smul_mem _ _ (apply_mem_coinv ρ _ hk₁ hDy)

end GlobalTheory.CartanCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualContinuousIntegralOverEnlargedCoeff
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedDualLoc

theorem continuous_T2O (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous (T2O D.nd i ρ π) := by
  have h1 : Continuous fun g : GE D.nd => ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) :=
    D.nd.chi_cont i 1
  have h2 : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  have h3 : Continuous fun g : GE D.nd => ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := hρ.comp continuous_inv
  refine continuous_matrix fun a b => ?_
  have h : ∀ g : GE D.nd, T2O D.nd i ρ π g a b =
      ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) * (((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) *
        ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) b a) := by
    intro g
    simp [T2O, WpO, rhoO, twistM, dualM]
  simp only [h]
  exact h2.mul (h1.mul (h3.matrix_elem b a))

theorem continuous_and_integral : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → Continuous (fun g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g) ∧ ∀ g a b, ‖((mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g a b : ↥LL'.1) : Om (D.nd.l i))‖ ≤ 1 := by
  intro D i w hw LL' h ρ π hρ
  have hc := GlobalTheory.WordJumpsCompare.continuous_loc D i w hw (T2O D.nd i ρ π) (continuous_T2O D i ρ π hρ)
  refine ⟨continuous_matrix fun a b => ?_, fun g a b => ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp (hc.matrix_elem a b)) _
  · exact GlobalTheory.LocalH1Finiteness.norm_toLL_le (D.nbr i w hw) _

end GlobalTheory.TwistedDualLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbedding
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thick_iff : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → ∀ i, (pageWord L j ε τ φ).thick i ↔ Thick D.host (letter τ φ i) := by
  intro D L C j ε τ φ hR i
  obtain ⟨hlo, -⟩ := bHat_window L C hR
  obtain ⟨hwM, hwle⟩ := _root_.GlobalTheory.HTW.wMax_le_and_ge L C hR
  have hR' := hR
  obtain ⟨hC, hw, ht, hwb, -, hb⟩ := hR'
  obtain ⟨c, hc⟩ := D.R.t_odd
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  have hdiv : (D.R.t + 1) / 2 = c + 1 := by omega
  have hdivZ : ((D.R.t : ℤ) + 1) / 2 = (c : ℤ) + 1 := by omega
  have htc : (D.R.t : ℝ) = 2 * c + 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ L.sc.b by linarith)
  have hle := Nat.le_ceil L.sc.b
  have hsub : c + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((c + 1 : ℕ) : ℝ) ≤ (⌈L.sc.b⌉₊ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hbH : bHat L + (c + 1) = ⌈L.sc.b⌉₊ := by
    unfold bHat
    rw [hdiv]
    omega
  have hfl := Nat.lt_floor_add_one L.etaSz
  have hη : etaHat L = ⌊L.etaSz⌋₊ + D.R.t + 2 := rfl
  have hsz : ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ + ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = true) ∨
      ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ - ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = false) := by
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _ ∨
      szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _
    unfold szT
    cases pos ε (letter τ φ i) <;> simp [hdivZ]
  have hbW : (pageWord L j ε τ φ).b = bHat L := rfl
  have hηW : (pageWord L j ε τ φ).η = etaHat L := rfl
  unfold WordData.thick
  rw [hbW, hηW, hη]
  generalize hE : ⌊(hcAt D (letter τ φ i)).e j⌋ = E at hsz
  constructor
  · rintro ⟨ha, hz⟩
    by_contra hnT
    have hEw : E ≤ (wMax D : ℤ) := hE ▸ hwle _ j hnT
    have hlt2 : ((wMax D + (c + 1) : ℕ) : ℝ) < (bHat L : ℝ) := by
      push_cast
      rw [htc] at hlo ht
      linarith
    have hlt3 : wMax D + (c + 1) < bHat L := by exact_mod_cast hlt2
    omega
  · intro hT
    obtain ⟨hA, hB⟩ := GlobalTheory.T.floor_size_bounds_at_thick_embedding L _ j hT
    rw [hE] at hA hB
    have hBE : ((⌈L.sc.b⌉₊ : ℤ)) ≤ E := by
      have : ((⌈L.sc.b⌉₊ : ℤ) : ℝ) < ((E + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_lt.mp this
      omega
    have hEB : E < (⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 := by
      have : ((E : ℤ) : ℝ) < (((⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    omega

end GlobalTheory.HTW
end

