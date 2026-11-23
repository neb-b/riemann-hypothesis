module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGaussSumIntegerDvdResidueCardPow
section
noncomputable section

namespace GlobalTheory.GaussDiv

section Finite

theorem exists_int_of_pow_eq_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {z : ℂ} {n : ℕ} (hn : 0 < n)
    (hz : z ^ n = 1) (h : z ∈ Set.range σ) : ∃ g : NumberField.RingOfIntegers K, σ g = z := by
  obtain ⟨x, rfl⟩ := h
  have hx : x ^ n = 1 := σ.injective (by rw [map_pow, hz, map_one])
  have hi : IsIntegral ℤ x := IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)
  exact ⟨⟨x, hi⟩, rfl⟩

theorem exists_int_gauss {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {R : Type} [CommRing R] [Fintype R]
    [DecidableEq R] [Fintype Rˣ] (m : Ideal R) (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (χ : Rˣ →* ℂ) (hχ : ∀ u, ‖χ u‖ = 1) (t₀ : Rˣ)
    (ht₀ : ∀ x ∈ m, ((t₀ : R) - 1) * x = 0) (hχt₀ : χ t₀ ≠ 1) (hr : ∀ u, χ u ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ Fintype.card R = 1 → ζ ∈ Set.range σ) :
    ∃ g g' : NumberField.RingOfIntegers K, σ g = ∑ u : Rˣ, (χ u)⁻¹ * ψ u ∧
      g * g' = (Fintype.card R : NumberField.RingOfIntegers K) := by
  have hN := GlobalTheory.gauss_units_norm_sq m hm ψ hψ χ (map_mul χ) hχ t₀ ht₀ hχt₀
  have h1 : ∀ u, ∃ g : NumberField.RingOfIntegers K, σ g = χ u := fun u =>
    exists_int_of_pow_eq_one σ (Fintype.card_pos (α := Rˣ)) (by rw [← map_pow, pow_card_eq_one, map_one]) (hr u)
  have h2 : ∀ y, ∃ g : NumberField.RingOfIntegers K, σ g = ψ y := fun y => by
    have : ψ y ^ Fintype.card R = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
    exact exists_int_of_pow_eq_one σ (Fintype.card_pos (α := R)) this (hζ _ this)
  choose a ha using h1
  choose b hb using h2
  have hinv : ∀ u, χ u⁻¹ = (χ u)⁻¹ := fun u =>
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  have hg : σ ((∑ u : Rˣ, a u⁻¹ * b u : NumberField.RingOfIntegers K) : K) = ∑ u : Rˣ, (χ u)⁻¹ * ψ u := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, ha, hb, hinv]
  have hg' : σ ((∑ u : Rˣ, a u * b (-u) : NumberField.RingOfIntegers K) : K) =
      starRingEnd ℂ (∑ u : Rˣ, (χ u)⁻¹ * ψ u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, ha, hb]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.inv_eq_conj (hχ z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  refine ⟨_, ∑ u : Rˣ, a u * b (-u), hg, ?_⟩
  apply NumberField.RingOfIntegers.ext
  apply σ.injective
  have e : ∀ x y : NumberField.RingOfIntegers K, σ ((x * y : NumberField.RingOfIntegers K) : K) = σ x * σ y :=
    fun x y => by simp only [map_mul]
  rw [e, hg, hg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hN]
  simp

end Finite

section Local

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_res (e : ℕ) : Fintype.card (Res k e) = resCard k ^ e := by
  rw [← Nat.card_eq_fintype_card]
  have hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

theorem val_rep_sub {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (y : Res k c) (a : 𝒪[k])
    (h : y = Ideal.Quotient.mk _ a) : valuation k (rep y - a) ≤ valuation k (ϖ : k) ^ c :=
  (mk_eq_mk_iff hϖ c (Quotient.out y) a).1 (by rw [Ideal.Quotient.mk_out, h])


open Classical in
theorem exists_int_gS {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ψl : k → ℂ}
    (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
    (hcond : ∀ x : k, (∀ y : k, valuation k y ≤ 1 → ψl (x * y) = 1) → valuation k x ≤ 1)
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
    (hmin : ∃ u ∈ unitCong (ϖ ^ (c - 1)), ν u ≠ 1) (hun : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (hr : ∀ x : kˣ, valuation k (x : k) = 1 → (ν x : ℂ) ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ (resCard k ^ c) = 1 → ζ ∈ Set.range σ) :
    ∃ g g' : NumberField.RingOfIntegers K, σ g = gS ψl ν hϖ hc1 1 ∧
      g * g' = (resCard k : NumberField.RingOfIntegers K) ^ c := by
  have hdiv : ∀ a b : k, valuation k (a - b) ≤ valuation k (ϖ : k) ^ c →
      ψl (a / (ϖ : k) ^ c) = ψl (b / (ϖ : k) ^ c) := fun a b h => by
    apply psi_congr hadd hO
    rw [← sub_div, map_div₀, map_pow]
    exact div_le_one_of_le₀ h zero_le'
  have hmul : ∀ x y : Res k c, valuation k (rep (x * y) - rep x * rep y) ≤ valuation k (ϖ : k) ^ c := fun x y =>
    val_rep_sub hϖ (x * y) (Quotient.out x * Quotient.out y)
      (by rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out])
  let Ψ : AddChar (Res k c) ℂ :=
    { toFun := fun y => ψl (rep y / (ϖ : k) ^ c)
      map_zero_eq_one' := by
        rw [hdiv _ 0 (val_rep_sub hϖ (0 : Res k c) 0 (map_zero _).symm), zero_div]
        exact hO 0 (by simp)
      map_add_eq_mul' := fun x y => by
        rw [← hadd, ← add_div]
        exact hdiv _ _ (val_rep_sub hϖ (x + y) (Quotient.out x + Quotient.out y)
          (by rw [map_add (f := _), Ideal.Quotient.mk_out, Ideal.Quotient.mk_out])) }
  let χ : (Res k c)ˣ →* ℂ :=
    { toFun := fun u => ν (uRep hϖ hc1 u)
      map_one' := by
        rw [nu_congr hϖ hc1 hc (b := 1) (by simp) (val_rep_sub hϖ (1 : Res k c) 1 (map_one _).symm)]
        simp
      map_mul' := fun u w => by
        rw [nu_congr hϖ hc1 hc (b := uRep hϖ hc1 u * uRep hϖ hc1 w)
          (by simp [map_mul, uRep, val_rep_unit hϖ hc1]) (hmul u w)]
        simp }
  have hΨ : ∀ d : Res k c, (∀ x, Ψ (d * x) = 1) → d = 0 := fun d hd => by
    have h3 := hcond (rep d / (ϖ : k) ^ c) fun a ha => by
      rw [← hd (Ideal.Quotient.mk _ ⟨a, ha⟩), div_mul_eq_mul_div]
      exact (hdiv _ _ (val_rep_sub hϖ _ (Quotient.out d * ⟨a, ha⟩) (by rw [map_mul, Ideal.Quotient.mk_out]))).symm
    rw [← Ideal.Quotient.mk_out d, ← map_zero (Ideal.Quotient.mk _)]
    apply (mk_eq_mk_iff hϖ c _ _).2
    have e2 : rep d = rep d / (ϖ : k) ^ c * (ϖ : k) ^ c := by field_simp
    change valuation k (rep d - 0) ≤ _
    rw [sub_zero, e2, map_mul, map_pow]
    exact mul_le_of_le_one_left' h3
  haveI : Nontrivial (Res k c) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top (top_le_iff.1 (h.ge.trans (Ideal.pow_le_self (by omega))))
  haveI : IsLocalRing (Res k c) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨u, ⟨hu1, hu2⟩, hν⟩ := hmin
  have hu' : IsUnit (⟨u, hu1.le⟩ : 𝒪[k]) :=
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 hu1
  set ub : (Res k c)ˣ := (hu'.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).unit with hub_def
  have hub : (ub : Res k c) = Ideal.Quotient.mk _ ⟨u, hu1.le⟩ := rfl
  have ht₀ : ∀ x ∈ IsLocalRing.maximalIdeal (Res k c), ((ub : Res k c) - 1) * x = 0 := fun x hx => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : valuation k (a : k) < 1 := lt_of_le_of_ne a.2 fun h => hx
      (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h).map _)
    have hx' : valuation k (a : k) ≤ valuation k (ϖ : k) := by rw [hϖ]; exact le_uniformizer_iff.2 ha
    have hu2' : valuation k ((u : k) - 1) ≤ valuation k (ϖ : k) ^ (c - 1) := by
      simpa [Units.val_pow_eq_pow_val] using hu2
    rw [hub, ← map_one (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)), ← map_sub, ← map_mul,
      ← map_zero (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))]
    apply (mk_eq_mk_iff hϖ c _ _).2
    change valuation k (((u : k) - 1) * a - 0) ≤ _
    rw [sub_zero, map_mul]
    calc valuation k ((u : k) - 1) * valuation k (a : k) ≤ valuation k (ϖ : k) ^ (c - 1) * valuation k (ϖ : k) :=
          mul_le_mul' hu2' hx'
      _ = valuation k (ϖ : k) ^ c := by rw [← pow_succ]; congr 1; omega
  have hχt₀ : χ ub ≠ 1 := by
    change ((ν (uRep hϖ hc1 ub) : ℂˣ) : ℂ) ≠ 1
    rw [nu_congr hϖ hc1 hc (b := u) hu1 (val_rep_sub hϖ _ _ hub)]
    exact fun h => hν (Units.ext h)
  obtain ⟨g, g', h1, h2⟩ := exists_int_gauss σ (IsLocalRing.maximalIdeal (Res k c))
    (fun x => by simp [IsLocalRing.mem_maximalIdeal]) Ψ hΨ χ (fun u => hun _) ub ht₀ hχt₀
    (fun u => hr _ (val_rep_unit hϖ hc1 u)) (by rwa [card_res])
  refine ⟨g, g', ?_, by rw [h2, card_res, Nat.cast_pow]⟩
  rw [h1]
  unfold gS
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [one_mul, Units.val_inv_eq_inv_val]
  rfl

end Local

end GlobalTheory.GaussDiv

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)


open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem GlobalTheory.GaussDiv.gauss_dvd_pow : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (ν : (Fv F v)ˣ →* ℂˣ), PsiUnr ψ v →
    Continuous (fun x : (Fv F v)ˣ => (ν x : ℂ)) → (∀ x, ‖(ν x : ℂ)‖ = 1) → 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν →
    (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F → ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F →
      (ν x : ℂ) ∈ Set.range σ) →
    (∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) = 1 → ζ ∈ Set.range σ) →
    ∃ g g' : 𝓞 K, σ g = gauss ψ ν ∧ g * g' = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν := by
  intro F _ _ K _ _ σ ψ v ν hψ hcont hun hc1 hr hζ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hadd : ∀ x y, psiLoc ψ v (x + y) = psiLoc ψ v x * psiLoc ψ v y := fun x y => by
    simp only [psiLoc, map_add (f := _)]
    exact AddChar.map_add_eq_mul ψ _ _
  have hO : ∀ x : Fv F v, valuation (Fv F v) x ≤ 1 → psiLoc ψ v x = 1 := fun x hx => by
    have := ((hψ 1).2 ((val_le_one_iff v 1).1 (by simp))) x ((val_le_one_iff v x).1 hx)
    rwa [one_mul] at this
  have hcond : ∀ x : Fv F v, (∀ y : Fv F v, valuation (Fv F v) y ≤ 1 → psiLoc ψ v (x * y) = 1) →
      valuation (Fv F v) x ≤ 1 := fun x h =>
    (val_le_one_iff v x).2 ((hψ x).1 fun y hy => h y ((val_le_one_iff v y).2 hy))
  have hne : {c | CondLE (unifAt v) c ν}.Nonempty := exists_condLE hϖ ν hcont
  have hmem : CondLE (unifAt v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) ν := Nat.sInf_mem hne
  have hmin : ∃ u ∈ unitCong (unifAt v ^ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1)), ν u ≠ 1 := by
    have hlt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1 < sInf {c | CondLE (unifAt v) c ν} := by
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1 < GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν
      omega
    have h : ¬ CondLE (unifAt v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1) ν := Nat.notMem_of_lt_sInf hlt
    simpa [CondLE] using h
  have hq : GlobalTheory.SplitWeil.resCard (Fv F v) = Ideal.absNorm v.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion v
  obtain ⟨g, g', h1, h2⟩ := GlobalTheory.GaussDiv.exists_int_gS σ hadd hO hcond hϖ hc1 hmem hmin hun
    (fun x hx => hr x ((val_le_one_iff v _).1 hx.le)
      ((val_le_one_iff v _).1 (by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])))
    (by rwa [hq])
  refine ⟨g, g', ?_, by rw [h2, hq]⟩
  rw [h1]
  unfold gauss gS
  refine Finset.sum_congr rfl fun y _ => ?_
  have hr := rep_ne_zero hϖ hc1 y
  unfold rep at hr
  rw [dite_eq_right hr, one_mul]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixAdelicDecompositionAtFinitePlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LatPtDecomp

theorem exists_zsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (w : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  exact _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem L hL w

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_mem (v : Pl (F := F)) (t : Fv F v) {k : F} (hk : k ≠ 0) :
    ∃ s : F, (algebraMap F (Fv F v) k)⁻¹ * (t - algebraMap F (Fv F v) s) ∈ v.adicCompletionIntegers F := by
  have hk' : algebraMap F (Fv F v) k ≠ 0 := (map_ne_zero _).2 hk
  have hkv : Valued.v (algebraMap F (Fv F v) k) ≠ 0 := (Valuation.ne_zero_iff _).2 hk'
  have hd : DenseRange (algebraMap F (v.adicCompletion F)) := HeightOneSpectrum.denseRange_algebraMap (K := F) v
  have hN : {y : v.adicCompletion F | Valued.v (t - y) < Valued.v (algebraMap F (Fv F v) k)} ∈ nhds t := by
    have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict (algebraMap F (Fv F v) k))).preimage
      (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => t - y)
    simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (t - t) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hkv
  obtain ⟨s, hs⟩ := hd.mem_nhds hN
  refine ⟨s, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
  have hs' : Valued.v (t - algebraMap F (Fv F v) s) < Valued.v (algebraMap F (Fv F v) k) := hs
  rw [inv_mul_le_iff₀ (zero_lt_iff.2 hkv), mul_one]
  exact hs'.le

theorem incM_single {n d : ℕ} (i : Fin n) (j : Fin d) (y : E) :
    incM F (Matrix.single i j y) = Matrix.single i j ((1 : AF F) ⊗ₜ[F] y) := by
  ext a b
  simp only [incM, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [inclR]

theorem single_sub {A : Type} [AddGroup A] {n d : ℕ} (i : Fin n) (j : Fin d) (a b : A) :
    Matrix.single i j a - Matrix.single i j b = Matrix.single i j (a - b) := by
  ext k l; simp only [Matrix.sub_apply, Matrix.single_apply]; split_ifs <;> simp

theorem atPlace_one_smul_tmul (v : Pl (F := F)) (a : AF F) (x : E) :
    GlobalTheory.EmbChart.atPlace v 1 • (a ⊗ₜ[F] x) = GlobalTheory.EmbChart.atPlace v (evFin F v a) ⊗ₜ[F] x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem core {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsFullLattice E) (hY : Y.L.IsFullLattice E) (v : Pl (F := F))
    (i : Fin n) (j : Fin d) (t : Fv F v) (x : E) :
    ∃ X₀ : Matrix (Fin n) (Fin d) E,
      Matrix.single i j (GlobalTheory.EmbChart.atPlace v t ⊗ₜ[F] x) - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  obtain ⟨N, hN, hNx⟩ := exists_zsmul_mem X.L hX (Pi.single i x)
  obtain ⟨N', hN', hNy⟩ := exists_zsmul_mem Y.L hY (Pi.single j 1)
  have hK : ((N * N' : ℤ) : F) ≠ 0 := Int.cast_ne_zero.2 (mul_ne_zero hN hN')
  obtain ⟨s, hs⟩ := exists_sub_mem v t hK
  set r := (algebraMap F (Fv F v) ((N * N' : ℤ) : F))⁻¹ * (t - algebraMap F (Fv F v) s) with hr
  refine ⟨Matrix.single i j (algebraMap F E s * x), ?_⟩
  refine AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v r, (fun u hu => by
    rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]), ?_, _, hNx, _, hNy, ?_⟩
  · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact hs
  · have hv : Matrix.vecMulVec (N • Pi.single i x) (N' • Pi.single j (1 : E)) =
        Matrix.single i j (((N * N' : ℤ) : F) • x) := by
      ext a b
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.single_apply, Matrix.single_apply]
      by_cases h1 : a = i <;> by_cases h2 : b = j
      · subst h1 h2
        simp only [if_true, and_self, smul_eq_mul, mul_one]
        rw [Algebra.smul_def (A := E) ((N * N' : ℤ) : F), map_intCast]
        simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul, mul_one]; push_cast; ring
      all_goals simp [h1, h2, eq_comm (a := i), eq_comm (a := j)]
    have hev : ∀ c : F, evFin F v (c • (1 : AF F)) = algebraMap F (Fv F v) c := fun c => by
      rw [map_smul, map_one, Algebra.algebraMap_eq_smul_one]
    have hK' : algebraMap F (Fv F v) ((N * N' : ℤ) : F) ≠ 0 := (map_ne_zero _).2 hK
    rw [hv, incM_single, incM_single, Matrix.smul_single, Matrix.smul_single, single_sub]
    congr 1
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, atPlace_one_smul_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, ← TensorProduct.sub_tmul, ← map_sub,
      hev, hev, hr]
    congr 2
    field_simp

theorem decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → Y.L.IsFullLattice E → ∀ (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (AE F E)),
    At (evFin F v) z → ∃ X₀ : Matrix (Fin n) (Fin d) E, z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  intro F E _ _ _ _ _ n d X Y hX hY v z hz
  have hz' : z = GlobalTheory.EmbChart.atPlace v 1 • z := by
    have h := hz (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h
  let P : Matrix (Fin n) (Fin d) (AE F E) → Prop := fun w =>
    ∃ X₀ : Matrix (Fin n) (Fin d) E, GlobalTheory.EmbChart.atPlace v 1 • w - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v
  have P0 : P 0 := ⟨0, by simp [incM]⟩
  have Padd : ∀ w w', P w → P w' → P (w + w') := by
    rintro w w' ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B, ?_⟩
    have : GlobalTheory.EmbChart.atPlace v 1 • (w + w') - GlobalTheory.EmbChart.atPlace v 1 • incM F (A + B) =
        (GlobalTheory.EmbChart.atPlace v 1 • w - GlobalTheory.EmbChart.atPlace v 1 • incM F A) +
        (GlobalTheory.EmbChart.atPlace v 1 • w' - GlobalTheory.EmbChart.atPlace v 1 • incM F B) := by
      have hI : incM F (A + B) = incM F A + incM F B := by ext; simp [incM]
      rw [hI, smul_add, smul_add]; abel
    rw [this]; exact add_mem hA hB
  have Psum : ∀ {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin d) (AE F E)), (∀ k ∈ s, P (f k)) → P (∑ k ∈ s, f k) := by
    intro ι s f h
    classical
    induction s using Finset.induction_on with
    | empty => simpa using P0
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact Padd _ _ (h k (Finset.mem_insert_self _ _)) (ih fun m hm => h m (Finset.mem_insert_of_mem hm))
  have Psingle : ∀ (i : Fin n) (j : Fin d) (w : AE F E), P (Matrix.single i j w) := by
    intro i j w
    induction w using TensorProduct.induction_on with
    | zero => simpa using P0
    | add a b ha hb => rw [Matrix.single_add]; exact Padd _ _ ha hb
    | tmul a x =>
      rw [show P (Matrix.single i j (a ⊗ₜ[F] x)) ↔ ∃ X₀ : Matrix (Fin n) (Fin d) E,
          Matrix.single i j (GlobalTheory.EmbChart.atPlace v (evFin F v a) ⊗ₜ[F] x) - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈
            latAtV X Y v by
        simp only [P, Matrix.smul_single, atPlace_one_smul_tmul]]
      exact core X Y hX hY v i j _ x
  obtain ⟨X₀, h⟩ : P z := by
    rw [Matrix.matrix_eq_sum_single z]
    exact Psum _ _ fun i _ => Psum _ _ fun j _ => Psingle i j _
  exact ⟨X₀, by rw [hz']; exact h⟩

end GlobalTheory.LatPtDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicLatticeAtFinitePlaceIffInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSphLat

open GlobalTheory.InertLocField InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_inclR (a : AF F) (e : E) : a • inclR (F := F) (AF F) e = a ⊗ₜ[F] e := by
  rw [show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem iotaW_toCompl {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (y : Fv F v ⊗[F] E) :
    GlobalTheory.InertBigCell.iotaW hw (toCompl (under_eq_of_isInertAt hw) y) = liftT (E := E) v y := by
  show liftT (E := E) v ((complEquiv hw (under_eq_of_isInertAt hw)).symm
    (complEquiv hw (under_eq_of_isInertAt hw) y)) = liftT (E := E) v y
  rw [RingEquiv.symm_apply_apply]

theorem gen_mem {v : Pl (F := F)} {d : ℕ} (W : Spc F E d) {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F)
    {y : Fin d → E} (hy : y ∈ W.L) :
    (fun i => GlobalTheory.LatVac.liftV v t ⊗ₜ[F] y i) ∈ GlobalTheory.InertSph.latAt W v :=
  AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v t, GlobalTheory.LatVac.at_liftV v t,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact ht, y, hy, by funext i; rw [Pi.smul_apply, smul_inclR]⟩

theorem mem_latAt_iff {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ}
    (W : Spc F E d) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ ∃ u ∈ GlobalTheory.LFun.latAt w W.L, z = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := by
  have liftT_tmul (a : Fv F v) (e : E) :
      liftT (E := E) v (a ⊗ₜ[F] e) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] e := rfl
  have h := under_eq_of_isInertAt hw
  let f : (Fin d → w.adicCompletion E) →+ (Fin d → AE F E) :=
    AddMonoidHom.compLeft (GlobalTheory.InertBigCell.iotaW hw) (Fin d)
  have hf : ∀ u, f u = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := fun _ => rfl
  constructor
  · intro hz
    have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.LFun.latAt w W.L).toAddSubgroup.map f := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, haO, y, hy, rfl⟩
      refine ⟨fun i => complMap h (evFin F v a) * algebraMap E _ (y i), ?_, ?_⟩
      · have e1 : (fun i => complMap h (evFin F v a) * algebraMap E (w.adicCompletion E) (y i)) =
            (⟨complMap h (evFin F v a), complMap_mem h haO⟩ : Formalism.UG.Ov E w) •
              (fun i => algebraMap E (w.adicCompletion E) (y i)) := rfl
        rw [Submodule.coe_toAddSubgroup, SetLike.mem_coe, e1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
      · funext i
        rw [hf]
        dsimp only
        rw [← toCompl_tmul, iotaW_toCompl, liftT_tmul, ← eq_liftV_of_at v ha, Pi.smul_apply, smul_inclR]
    obtain ⟨u, hu, e⟩ := AddSubgroup.mem_map.1 (hle hz)
    exact ⟨u, hu, e.symm⟩
  · rintro ⟨u, hu, rfl⟩
    have key : ∀ u ∈ GlobalTheory.LFun.latAt w W.L, ∀ o : Formalism.UG.Ov E w, f (o • u) ∈ GlobalTheory.InertSph.latAt W v := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        intro o
        obtain ⟨t, ht⟩ := toCompl_surjective h (o : w.adicCompletion E)
        have htI : t ∈ intLoc F E v := (mem_intLoc_iff hw h t).2 (ht ▸ o.2)
        have e1 : f (o • fun i => algebraMap E (w.adicCompletion E) (y i)) =
            fun i => liftT (E := E) v (t * ((1 : Fv F v) ⊗ₜ[F] y i)) := by
          funext i
          rw [hf]
          dsimp only
          rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, ← ht,
            show algebraMap E (w.adicCompletion E) (y i) = toCompl h ((1 : Fv F v) ⊗ₜ[F] y i) by
              rw [toCompl_tmul, map_one, one_mul], ← map_mul, iotaW_toCompl]
        rw [e1]
        refine intLoc_induction (p := fun t => (fun i => liftT (E := E) v (t * ((1 : Fv F v) ⊗ₜ[F] y i))) ∈
          GlobalTheory.InertSph.latAt W v) (fun a ha x => ?_) ?_ (fun p q hp hq => ?_) (fun p hp => ?_) htI
        · convert gen_mem W ha (W.L.smul_mem x hy) using 1
          funext i
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, liftT_tmul, Pi.smul_apply, Algebra.smul_def]
        · convert (zero_mem (GlobalTheory.InertSph.latAt W v)) using 1
          funext i
          simp
        · convert add_mem hp hq using 1
          funext i
          simp [add_mul, map_add (f := _)]
        · convert neg_mem hp using 1
          funext i
          simp [neg_mul, map_neg]
      | zero => intro o; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro o; rw [smul_add, map_add (f := _)]; exact add_mem (hx o) (hy o)
      | smul a x _ hx => intro o; rw [smul_smul]; exact hx (o * a)
    have := key u hu 1
    rw [one_smul] at this
    exact this

end GlobalTheory.InertSphLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNormStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_leviInverse_quotient_det_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) ((p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
    (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin n) = diagCols (Fin n) * t.val →
    At (evFin F v) (t.val.det - 1) ∧ At (evFin F v) (Algebra.norm (AF F) t.val.det - 1) ∧
      ∃ s : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), s.val = ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₂₁ ∧
        Algebra.norm (AF F) s.val.det = Algebra.norm (AF F) t.val.det := by
  first | exact @GlobalTheory.InertLagLevi.levi_det | exact GlobalTheory.InertLagLevi.levi_det | (intros; apply GlobalTheory.InertLagLevi.levi_det <;> assumption)
end

