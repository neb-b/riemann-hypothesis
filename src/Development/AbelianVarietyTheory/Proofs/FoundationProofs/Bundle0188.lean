module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.EmbThroughCompletion

section Norm

theorem norm_le_one_of_isIntegral {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C]
    [Algebra R C] (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {x : C} (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  let f : R →+* (NormedField.valuation (K := C)).integer :=
    (algebraMap R C).codRestrict _ (fun r => by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      exact hR r)
  have h1 : IsIntegral (NormedField.valuation (K := C)).integer x :=
    hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe] at h2
  exact h2

variable {E C : Type} [Field E] [NumberField E] [NormedField C] [IsUltrametricDist C]

theorem norm_int_le_one (a : E →+* C) (x : 𝓞 E) : ‖a (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (R := ℤ) (fun r => by simpa using IsUltrametricDist.norm_intCast_le_one C r)
    (map_isIntegral_int a x.isIntegral_coe)

theorem norm_lt_one_iff (v : HeightOneSpectrum (𝓞 E)) (a b : E →+* C)
    (ha : ∀ x : 𝓞 E, ‖a (x : E)‖ < 1 ↔ x ∈ v.asIdeal) (hb : ∀ x : 𝓞 E, ‖b (x : E)‖ < 1 ↔ x ∈ v.asIdeal)
    (x : E) : ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  have hd : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ‖c ((d : 𝓞 E) : E)‖ = 1 :=
    fun c hc => le_antisymm (norm_int_le_one c _) (not_lt.1 fun h' => d.2 ((hc _).1 h'))
  rcases h with h | h
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) →
        (‖c x‖ < 1 ↔ n ∈ v.asIdeal) := by
      intro c hc
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      rw [← hc n]
      change ‖c x‖ * ‖c ((d : 𝓞 E) : E)‖ = ‖c (n : E)‖ at h1
      rw [hd c hc, mul_one] at h1
      rw [h1]
    rw [key a ha, key b hb]
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ¬ ‖c x‖ < 1 := by
      intro c hc hlt
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      change ‖c x‖ * ‖c (n : E)‖ = ‖c ((d : 𝓞 E) : E)‖ at h1
      rw [hd c hc] at h1
      have h2 := norm_int_le_one c n
      have h3 := norm_nonneg (c x)
      have h4 := norm_nonneg (c (n : E))
      nlinarith
    exact iff_of_false (key a ha) (key b hb)

end Norm

section Padic

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_iff (K : Loc.FinExt l) (x : K.1) : x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  refine (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).symm.trans
    ⟨fun h => norm_le_one_of_isIntegral (fun r => ?_) h, fun h => isIntegral_of_norm_le_one _ h⟩
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact r.2

theorem not_isUnit_iff (K : Loc.FinExt l) (x : Loc.OL K) :
    ¬ IsUnit x ↔ ‖((x : K.1) : PadicAlgCl l)‖ < 1 := by
  have hx := (mem_OL_iff K _).1 x.2
  constructor
  · intro h
    refine lt_of_le_of_ne hx fun h1 => h ?_
    have h0 : (x : K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : K.1)⁻¹, (mem_OL_iff K _).2 ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
  · intro h hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hu
    have hy' := (mem_OL_iff K _).1 y.2
    have h1 := congrArg (fun z : Loc.OL K => ‖((z : K.1) : PadicAlgCl l)‖) hy
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h1
    have h3 := norm_nonneg ((x : K.1) : PadicAlgCl l)
    have h4 := norm_nonneg ((y : K.1) : PadicAlgCl l)
    nlinarith

variable {E : Type} [Field E] [NumberField E]

theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {n : ℕ}
    (y : Fin n → E) (c : Fin n → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) : ∑ k, c k • b (y k) = 0 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : Fin n → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : Fin n → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : Fin n → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

theorem exists_conj (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, g (a x) = b x := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ E
  have hroot : Polynomial.aeval (b pb.gen) (minpoly ℚ_[l] (a pb.gen)) = 0 := by
    have h0 := minpoly.aeval ℚ_[l] (a pb.gen)
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range] at h0 ⊢
    simp only [← map_pow] at h0 ⊢
    exact sum_eq_zero a b h _ _ h0
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) hroot
  refine ⟨g, fun x => ?_⟩
  have : ((g : PadicAlgCl l →+* PadicAlgCl l).comp a).toRatAlgHom = b.toRatAlgHom :=
    pb.algHom_ext hg
  exact DFunLike.congr_fun this x

variable {Ω : Type} [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

end Padic

end GlobalTheory.EmbThroughCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory.WildInertiaChar

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

theorem wild_pow (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (h : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (i : ℕ) :
    ∀ y : Ω, y ≠ 0 → A.valuation ((σ ^ i) y / y - 1) < 1 := by
  induction i with
  | zero => intro y hy; simp [hy]
  | succ i ih =>
    intro y hy
    have hz : (σ ^ i) y ≠ 0 := (map_ne_zero (σ ^ i)).mpr hy
    have h1 := h _ hz
    have h2 := ih y hy
    have e : (σ ^ (i + 1)) y / y - 1
        = (σ ((σ ^ i) y) / (σ ^ i) y - 1) * ((σ ^ i) y / y - 1)
          + ((σ ((σ ^ i) y) / (σ ^ i) y - 1) + ((σ ^ i) y / y - 1)) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [e]
    refine A.valuation.map_add_lt ?_ (A.valuation.map_add_lt h1 h2)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2.le) h1

theorem fixed_of_pow_fixed (A : ValuationSubring Ω) (τ : Ω ≃ₐ[E] Ω)
    (h : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) (k : ℕ)
    (hk : ¬ A.valuation (k : Ω) < 1) (x : Ω) (hx : (τ ^ k) x = x) : τ x = x := by
  by_contra hne
  have hd : τ x - x ≠ 0 := sub_ne_zero.mpr hne
  have hs : ∑ i ∈ Finset.range k, (τ ^ i) (τ x - x) = 0 := by
    have : ∀ i, (τ ^ i) (τ x - x) = (τ ^ (i + 1)) x - (τ ^ i) x := by
      intro i; rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (τ ^ i) x), hx]
    simp
  have e : (k : Ω) = - ∑ i ∈ Finset.range k, ((τ ^ i) (τ x - x) / (τ x - x) - 1) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]
    simp
  apply hk
  rw [e, Valuation.map_neg]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => wild_pow A τ h i _ hd

theorem trivial_on_wild (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (l : ℕ)
    (hl : l.Prime) (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (hA : IsPlaceOver A v)
    (Γ : Type) [CommGroup Γ] (ψ : G E Ω →* Γ) (hop : IsOpen (ψ.ker : Set (G E Ω)))
    (hψ : ∀ g, ∃ n : ℕ, ψ g ^ (l ^ n) = 1) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : ψ σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (one_mem ψ.ker))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine fixed_of_pow_fixed A (σ ^ m) (wild_pow A σ hσ m) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : ψ σ ^ m = 1 := by
    rw [← map_pow]; exact hsub hτ
  obtain ⟨n, hn⟩ := hψ σ
  have hc : Nat.Coprime (l ^ n) m := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).pow_left n
  have := (pow_gcd_eq_one (a := ψ σ) (m := l ^ n) (n := m)).mpr ⟨hn, h1⟩
  rwa [hc, pow_one] at this

end GlobalTheory.WildInertiaChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTypePrimesOfAdmissible
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
open Formalism.MainNotions.N
open scoped Matrix Pointwise

namespace GlobalTheory.InertiaTypePrimes

section General

variable {Γ R : Type} [Group Γ] [CommRing R] {r : ℕ}

theorem mem_ker_mapRep_iff (J : Ideal R) (ρ : Γ →* GL (Fin r) R) (g : Γ) :
    g ∈ (mapRep (Ideal.Quotient.mk J) ρ).ker ↔
      ∀ a b, (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change (Ideal.Quotient.mk J).mapMatrix ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = 1 ↔ _
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]

theorem isOpen_ker_mapRep [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (ρ : Γ →* GL (Fin r) R)
    (hρ : Continuous fun g => ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)) :
    IsOpen ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) := by
  have : ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) = ⋂ a, ⋂ b,
      (fun g => (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_mapRep_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => hJ.preimage ?_
  exact (hρ.sub continuous_const).matrix_elem a b

end General

theorem isWild_of_isWildAt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω) (h : IsWildAt A σ) : IsWild A σ := by
  have h1 : ∀ x : Ω, x ≠ 0 → A.valuation (σ x - x) < A.valuation x := fun x hx => by
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    have h0 : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx)
    rw [e, map_mul]
    exact mul_lt_of_lt_one_left h0 (h x hx)
  have h2 : ∀ x : Ω, A.valuation (σ x) = A.valuation x := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact Valuation.map_eq_of_sub_lt _ (h1 x hx)
  refine ⟨⟨?_, fun x hx => ?_⟩, h1⟩
  · change σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, ← h2, AlgEquiv.smul_def, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · exact (h1 x hx0).trans_le hx

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {r : ℕ} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

end Wild

end GlobalTheory.InertiaTypePrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BlochKatoIntegralScalars

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_of_norm_le_one (K : Loc.FinExt l) (x : K.1) (h : ‖(x : PadicAlgCl l)‖ ≤ 1) :
    x ∈ Loc.OL K :=
  (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1
    (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : Loc.FinExt l) : CompactSpace ↥(Loc.GK K) := by
  haveI := K.2
  have h : IsClosed ((Loc.GK K : Subgroup (Loc.GQ l)) : Set (Loc.GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.1 h.isCompact

theorem exists_pow_mul_mem_OL {X : Type} [TopologicalSpace X] [CompactSpace X] (K : Loc.FinExt l) {m : ℕ}
    (c : X → Fin m → K.1) (hc : Continuous c) :
    ∃ N : ℕ, ∀ g j, (l : K.1) ^ N * c g j ∈ Loc.OL K := by
  have hc' : Continuous fun g (j : Fin m) => ((c g j : K.1) : PadicAlgCl l) :=
    continuous_pi fun j => continuous_subtype_val.comp ((continuous_apply j).comp hc)
  obtain ⟨C, hC⟩ := (isCompact_range hc').isBounded.exists_norm_le
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hl
  refine ⟨N, fun g j => mem_OL_of_norm_le_one K _ ?_⟩
  have h1 : ‖((c g j : K.1) : PadicAlgCl l)‖ ≤ C :=
    (norm_le_pi_norm (fun j : Fin m => ((c g j : K.1) : PadicAlgCl l)) j).trans (hC _ ⟨g, rfl⟩)
  have h2 : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
  have h3 : (((l : K.1) ^ N * c g j : K.1) : PadicAlgCl l) =
      (l : PadicAlgCl l) ^ N * ((c g j : K.1) : PadicAlgCl l) := by
    push_cast
    rfl
  rw [h3, norm_mul, norm_pow, h2, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact h1.trans hN.le

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

end Local

theorem mem_of_mk_mem_span {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R G M) (S : Submodule R (G → M)) (hB : ∀ x : M, (fun g => ρ g x - x) ∈ S)
    (A : Set (ReciprocityTheory.Gal.H1 ρ))
    (hA : ∀ x ∈ A, ∃ w : ReciprocityTheory.Gal.Z1 ρ, (w : G → M) ∈ S ∧ x = Submodule.Quotient.mk w)
    (w : ReciprocityTheory.Gal.Z1 ρ) (hw : Submodule.Quotient.mk w ∈ Submodule.span R A) : (w : G → M) ∈ S := by
  have hB' : (ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype ≤ S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype := by
    intro w hw
    obtain ⟨x, hx⟩ := (mem_coboundaries1 ρ _).1 hw
    have : (ReciprocityTheory.Gal.Z1 ρ).subtype w = fun g => ρ g x - x := funext hx
    rw [Submodule.mem_comap, this]
    exact hB x
  have hle : Submodule.span R A ≤ (S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map (Submodule.mkQ _) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hA x hx
    exact ⟨w, hw, rfl⟩
  have h2 : w ∈ ((S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map
      (Submodule.mkQ ((ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype))).comap (Submodule.mkQ _) :=
    hle hw
  rw [Submodule.comap_map_mkQ, sup_eq_right.2 hB'] at h2
  exact h2

end GlobalTheory.BlochKatoIntegralScalars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRingOfIntegersOfHol
section
noncomputable section

open scoped MatrixGroups UpperHalfPlane
open Polynomial

namespace GlobalTheory.K4.TopUnits

open GlobalTheory.KZ GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def holSub (X : Tower Ω ε) : Subring X.K where
  carrier := {f | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)}
  mul_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩
  one_mem' := ⟨1, differentiableOn_const 1, by rw [map_one, Filter.Germ.coe_one]⟩
  add_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ + ψ, h1.add h3, by rw [map_add (f := _), h2, h4, Filter.Germ.coe_add]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, by rw [map_zero, Filter.Germ.coe_zero]⟩
  neg_mem' := by
    rintro f ⟨φ, h1, h2⟩
    exact ⟨-φ, h1.neg, by rw [map_neg, h2, Filter.Germ.coe_neg]⟩

theorem siegel_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {y : Fin 2 → ℚ} (hy : admitted c y) :
    siegel X c y ∈ holSub X ∧ (siegel X c y)⁻¹ ∈ holSub X := by
  have hd : DifferentiableOn ℂ (sgC c y) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c y hy)
  have hne : ∀ z, sgC c y z ≠ 0 := fun z => GlobalTheory.Sieg.sg_ne_zero c y _ hy
  have ha := SiegelMem.an_siegel_eq Ω ε X c y hy
  refine ⟨⟨_, hd, ha⟩, (sgC c y)⁻¹, hd.inv fun z _ => hne z, ?_⟩
  have h1 : X.an (siegel X c y)⁻¹ * X.an (siegel X c y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (_root_.GlobalTheory.KZ.siegel_ne_zero Ω ε X c y hy), map_one]
  have h2 : X.an (siegel X c y) * (((sgC c y)⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [ha, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
    congr 1
    funext z
    exact mul_inv_cancel₀ (hne z)
  rw [← mul_one (X.an _), ← h2, ← mul_assoc, h1, one_mul]

def IsTopUnit (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  f ≠ 0 ∧ f ∈ topF X M ∧ ∃ hf : f ∈ topL X M,
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    (⟨f, hf⟩ : topL X M) ∈ FunctionField.ringOfIntegers Ω (topL X M) ∧
      (⟨f, hf⟩ : topL X M)⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M)

end GlobalTheory.K4.TopUnits

namespace GlobalTheory.K4

open GlobalTheory.KZ

end GlobalTheory.K4
end
end

