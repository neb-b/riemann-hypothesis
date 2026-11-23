module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import ReciprocityTheory.GaloisValuations.Global

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PAlgType
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace AlgType

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime]

private theorem isAlgPos_mul {χ χ' : HChar K} {n n' : (K →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar K} {n : (K →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

def Good (art : Ideles K →* Gab K Ω) (ι : Qbar l ≃+* ℂ) (t : (K →+* ℂ) → ℤ) (ψ : G K Ω →* (Qbar l)ˣ) : Prop :=
  ∃ Y : HChar K, IsAlgPos Y t ∧ IsLAdicOf art ι Y t ψ

theorem good_cong {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t t' : (K →+* ℂ) → ℤ}
    {ψ ψ' : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) (ht : t = t') (hψ : ψ = ψ') : Good art ι t' ψ' := by
  subst ht hψ
  exact h

theorem good_mul {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t t' : (K →+* ℂ) → ℤ}
    {ψ ψ' : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) (h' : Good art ι t' ψ') : Good art ι (t + t') (ψ * ψ') := by
  obtain ⟨Y, h1, h2⟩ := h
  obtain ⟨Y', h1', h2'⟩ := h'
  exact ⟨Y * Y', isAlgPos_mul h1 h1', h2.mul h2'⟩

theorem good_one {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t : (K →+* ℂ) → ℤ}
    {ψ : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) : Good art ι 0 1 := by
  obtain ⟨Y, h1, h2⟩ := h
  exact good_cong ⟨Y * Y⁻¹, isAlgPos_mul h1 (isAlgPos_inv h1), h2.mul h2.inv⟩ (add_neg_cancel t) (mul_inv_cancel ψ)

theorem good_cyc {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) :
    Good art ι (fun _ => 1) (cycBar K Ω l) := by
  have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos K 1
  obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
  have e : μ = cycBar K Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at e
  subst e
  exact good_cong ⟨_, h, hL⟩ (funext fun _ => Nat.cast_one) rfl

end AlgType


end UpperTheory.V.Cu2

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PGoodJ
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace GoodJ

theorem isAlg_of_pos {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {κ : HChar K}
    {m : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ m) : κ.IsAlg m := fun k => hκ k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

theorem infChar_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (P : CuspSub K n)
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ m) (τ : K →+* ℂ) :
    (CG.mk (P.twist κ)).infChar τ = ((CG.mk P).infChar τ).map (· + ((m τ : ℤ) : ℂ)) := by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [(InfType.expo_of_infType K κ).1 m (isAlg_of_pos hκ) τ]
  try ring

end GoodJ

theorem goodJ : GoodJ := by
  intro K _ _ _ hK π hreg m hm
  classical
  let S : Finset ℂ := Finset.univ.biUnion fun τ : K →+* ℂ =>
    (((CG.mk π).infChar τ).toFinset ×ˢ ((CG.mk π).infChar (ComplexEmbedding.conjugate τ)).toFinset).image
      fun p => p.1 - p.2
  have h2 : ∀ τ : K →+* ℂ, ((CG.mk π).infChar τ).toFinset.card ≤ 2 := fun τ =>
    (Multiset.toFinset_card_le _).trans (CG.card_infChar _ τ).le
  have hS : S.card ≤ 8 := by
    refine (Finset.card_biUnion_le_card_mul _ _ 4 fun τ _ => ?_).trans ?_
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product]
      have a1 := h2 τ
      have a2 := h2 (ComplexEmbedding.conjugate τ)
      nlinarith
    · rw [Finset.card_univ, NumberField.Embeddings.card K ℂ, hK]
  have hinj : Function.Injective fun j : ℕ => ((2 * m * j : ℕ) : ℂ) := by
    intro a b h
    have h' : 2 * m * a = 2 * m * b := Nat.cast_injective h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h'
  have hcard : S.card < ((Finset.Icc 1 9).image fun j : ℕ => ((2 * m * j : ℕ) : ℂ)).card := by
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  obtain ⟨_, hz, hzS⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
  rw [Finset.mem_Icc] at hj
  refine ⟨j, hj.1, hj.2, fun Y a e hY ha ha' => ?_⟩
  have eM := GoodJ.infChar_twist π hY e
  have eM' := GoodJ.infChar_twist π hY (ComplexEmbedding.conjugate e)
  rw [ha] at eM
  rw [ha'] at eM'
  refine ⟨(CG.mk (π.twist Y)).infChar e, (CG.mk (π.twist Y)).infChar (ComplexEmbedding.conjugate e),
    ParLaws.hasInfChar_infChar (CG.mk (π.twist Y)) e,
    ParLaws.hasInfChar_infChar (CG.mk (π.twist Y)) (ComplexEmbedding.conjugate e), ?_, ?_, ?_⟩
  · intro h0
    have h1 := CG.card_infChar (CG.mk (π.twist Y)) e
    rw [h0] at h1
    simp at h1
  · rw [Multiset.nodup_add, eM, eM']
    refine ⟨(hreg e).1.map (add_left_injective _), (hreg _).1.map (add_left_injective _),
      Multiset.disjoint_left.2 fun {z} hz hz' => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨x', hx', hxx⟩ := Multiset.mem_map.1 hz'
    refine hzS (Finset.mem_biUnion.2 ⟨e, Finset.mem_univ _, Finset.mem_image.2
      ⟨(x, x'), Finset.mem_product.2 ⟨Multiset.mem_toFinset.2 hx, Multiset.mem_toFinset.2 hx'⟩, ?_⟩⟩)
    push_cast at hxx ⊢
    linear_combination -hxx
  · intro z hz
    rcases Multiset.mem_add.1 hz with hz | hz
    · rw [eM] at hz
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
      obtain ⟨k, rfl⟩ := (hreg e).2 x hx
      exact ⟨k - ((m * j : ℕ) : ℤ) - 1, by push_cast; ring⟩
    · rw [eM'] at hz
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
      obtain ⟨k, rfl⟩ := (hreg _).2 x hx
      exact ⟨k + ((m * j : ℕ) : ℤ) - 1, by push_cast; ring⟩

end UpperTheory.V.Cu2

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PKapEx
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace KapEx

theorem norm_eq_one {l : ℕ} [Fact l.Prime] {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 :=
  _root_.UpperTheory.Reformulated.B.Qk14.norm_eq_one h

def W (l : ℕ) [Fact l.Prime] : Subgroup (Qbar l)ˣ where
  carrier := {a | ‖(a : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    have e : (a : Qbar l) * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ha)
    rw [norm_mul, norm_eq_one ha, one_mul]
    exact hb
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have ha0 : (a : Qbar l) ≠ 0 := a.ne_zero
    have e : ((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = -((a : Qbar l)⁻¹ * (a - 1)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ ha0, mul_one]
      ring
    rw [e, norm_neg, norm_mul, norm_inv, norm_eq_one ha, inv_one, one_mul]
    exact ha

theorem isOpen_kappaOpenNeighbourhood (l : ℕ) [Fact l.Prime] : IsOpen ((W l : Subgroup (Qbar l)ˣ) : Set (Qbar l)ˣ) := by
  show IsOpen {a : (Qbar l)ˣ | ‖(a : Qbar l) - 1‖ < 1}
  exact isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const

theorem cong_of_mem {l : ℕ} [Fact l.Prime] {x : (Qbar l)ˣ} (hx : x ∈ W l) : Cong x 1 := by
  unfold Cong
  rw [Units.val_one]
  exact hx

theorem exists_pow_cong {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {l : ℕ} [Fact l.Prime] (f : Γ →* (Qbar l)ˣ) (hf : Continuous f) : ∃ d : ℕ, 0 < d ∧ ∀ g, f g ^ d ∈ W l := by
  have hU : IsOpen (((W l).comap f : Subgroup Γ) : Set Γ) := (isOpen_kappaOpenNeighbourhood l).preimage hf
  haveI := Subgroup.quotient_finite_of_isOpen _ hU
  have hi : ((W l).comap f).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨((W l).comap f).index.factorial, Nat.factorial_pos _, fun g => ?_⟩
  rw [← map_pow]
  exact Subgroup.pow_mem_of_index_ne_zero_of_dvd hi g fun n h0 hn => Nat.dvd_factorial h0 hn

theorem cc_notMem {Ω : Type} [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [_root_.NumberField.IsTotallyComplex K]
    {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := hc
  intro h
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hj (algebraMap K Ω x)
  rw [h x] at this
  exact this.symm

end KapEx

end UpperTheory.V.Cu2

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PTauEx
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)

end UpperTheory.V.Cu2

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PTwistIne
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix Pointwise

namespace UpperTheory.V.Cu2

namespace TwistIne

private theorem not_lt_of_not_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime)
    (hA : A.valuation (l : Ω) < 1) {d : ℤ} (hd : ¬ (l : ℤ) ∣ d) : ¬ A.valuation (d : Ω) < 1 := by
  intro hdA
  obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.mp hl).coprime_iff_not_dvd.2 hd
  have e : (1 : Ω) = (u : Ω) * (l : Ω) + (v : Ω) * (d : Ω) := by
    have := congrArg (Int.cast : ℤ → Ω) huv
    push_cast at this
    exact this.symm
  have h1 : ∀ (a : ℤ) (x : Ω), A.valuation x < 1 → A.valuation ((a : Ω) * x) < 1 := fun a x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hx
  have := Valuation.map_add_lt A.valuation (h1 u _ hA) (h1 v _ hdA)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

private theorem emb_two {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (τ e : K →+* ℂ) : e = τ ∨ e = ComplexEmbedding.conjugate τ := by
  classical
  have hc : Fintype.card (K →+* ℂ) = 2 := by rw [Embeddings.card, hK]
  have hne : τ ≠ ComplexEmbedding.conjugate τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h.symm)
  by_contra h
  push Not at h
  have h3 : ({e, τ, ComplexEmbedding.conjugate τ} : Finset (K →+* ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair hne]
  have := Finset.card_le_univ ({e, τ, ComplexEmbedding.conjugate τ} : Finset (K →+* ℂ))
  omega

theorem emb_unique {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (K' : IntermediateField ℚ Ω) [NumberField K'] (hdeg : Module.finrank ℚ K' = 2)
    (hsplit : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup)
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (w : HeightOneSpectrum (𝓞 K'))
    (hw : Formalism.ConjugateSelfDual.IsPlaceOver A w) (j j' : w.adicCompletion K' →+* Qbar l) (hj : Continuous j) (hj' : Continuous j') :
    j = j' := by
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : Algebra.IsQuadraticExtension ℚ K' := { toFree := inferInstance, finrank_eq_two' := hdeg }
  have : Normal ℚ K' := Algebra.IsQuadraticExtension.normal ℚ K'
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g : G ℚ Ω, g ∉ K'.fixingSubgroup := by
    by_contra! h
    have h2 := IntermediateField.finrank_eq_fixingSubgroup_index (L := K')
    rw [show K'.fixingSubgroup = ⊤ from eq_top_iff.2 fun g _ => h g, Subgroup.index_top, hdeg] at h2
    norm_num at h2
  let r : K' ≃ₐ[ℚ] K' := g.restrictNormal K'
  have hr' : ∀ x : K', algebraMap K' Ω (r x) = g (algebraMap K' Ω x) := fun x =>
    AlgEquiv.restrictNormal_commutes g K' x

  have hkey : ∀ y : K', j' (algebraMap K' (w.adicCompletion K') y) = j (algebraMap K' (w.adicCompletion K') (r y)) := by
    let ψ : K' →+* Qbar l := j.comp (algebraMap K' (w.adicCompletion K'))
    let ψ' : K' →+* Qbar l := j'.comp (algebraMap K' (w.adicCompletion K'))
    let ψr : K' →+* Qbar l := ψ.comp (r : K' →+* K')
    have h12 : ψ ≠ ψ' := by
      intro h
      apply hne
      apply DFunLike.coe_injective
      refine (HeightOneSpectrum.denseRange_algebraMap K' w).equalizer hj hj' ?_
      funext k
      exact DFunLike.congr_fun h k
    have h13 : ψ ≠ ψr := by
      intro h
      apply hg
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have e := ψ.injective (show ψ ⟨x, hx⟩ = ψ (r ⟨x, hx⟩) from DFunLike.congr_fun h ⟨x, hx⟩)
      have e2 := hr' ⟨x, hx⟩
      rw [← e] at e2
      exact e2.symm
    by_contra hne3
    have h23 : ψ' ≠ ψr := fun h => hne3 fun y => DFunLike.congr_fun h y
    have inj : ∀ φ φ' : K' →+* Qbar l, φ.toRatAlgHom = φ'.toRatAlgHom → φ = φ' := fun φ φ' h => by
      ext x
      exact DFunLike.congr_fun h x
    let f : Fin 3 → (K' →ₐ[ℚ] Qbar l) := ![ψ.toRatAlgHom, ψ'.toRatAlgHom, ψr.toRatAlgHom]
    have hf : Function.Injective f := by
      intro i k hik
      fin_cases i <;> fin_cases k <;> first
        | rfl
        | exact absurd (inj _ _ hik) h12 | exact absurd (inj _ _ hik).symm h12
        | exact absurd (inj _ _ hik) h13 | exact absurd (inj _ _ hik).symm h13
        | exact absurd (inj _ _ hik) h23 | exact absurd (inj _ _ hik).symm h23
    have h3 := Nat.card_le_card_of_injective f hf
    have h4 := card_algHom_le_finrank ℚ K' (Qbar l)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
    rw [hdeg] at h4
    omega

  have hval : ∀ y : Ω, (g⁻¹ • A).valuation y < 1 ↔ A.valuation (g y) < 1 := fun y => by
    rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ValuationSubring.mem_inv_pointwise_smul_iff,
      ValuationSubring.mem_inv_pointwise_smul_iff, AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀,
      map_eq_zero_iff _ g.injective]
  have hB1 : (g⁻¹ • A).valuation (l : Ω) < 1 := by
    rw [hval, map_natCast]
    exact hA
  have hBt : g⁻¹ • A ≠ ⊤ := fun h => ((UpperTheory.V.Base.places K' Ω l _).2.1 h).2 hB1
  obtain ⟨w', hw'⟩ := (UpperTheory.V.Base.places K' Ω l _).1 hBt
  have hne' : w' ≠ w := by
    intro e
    subst e
    obtain ⟨h, hh⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver (F := K') hw hw'
    apply hg
    have e1 : (resQ K' h) • A = h • A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    have hD : g * resQ K' h ∈ Dec (F := ℚ) A := by
      show (g * resQ K' h) • A = A
      rw [mul_smul, e1, hh, smul_inv_smul]
    have hm : resQ K' h ∈ K'.fixingSubgroup :=
      (K'.mem_fixingSubgroup_iff _).2 fun x hx => h.commutes ⟨x, hx⟩
    exact (Subgroup.mul_mem_cancel_right _ hm).1 (hsplit A hA hD)
  have hcop := Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun e => hne' (HeightOneSpectrum.ext e.symm)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hcop)
  have h1 := norm_lt_one_of_contEmb w j' hj' a ha
  have hbB : A.valuation (g (algebraMap K' Ω (b : K'))) < 1 := (hval _).1 ((hw' b).2 hb)
  have hint : IsIntegral ℤ (r (b : K')) :=
    (NumberField.RingOfIntegers.isIntegral_coe b).map ((r : K' →ₐ[ℚ] K').restrictScalars ℤ)
  let rb : 𝓞 K' := ⟨r (b : K'), hint⟩
  have hrb : rb ∈ w.asIdeal := (hw rb).1 (by
    rw [show algebraMap K' Ω ((rb : 𝓞 K') : K') = g (algebraMap K' Ω (b : K')) from hr' _]
    exact hbB)
  have h2 := norm_lt_one_of_contEmb w j hj rb hrb
  have h2' : ‖j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' b))‖ < 1 := by
    rw [hkey]
    exact h2
  have h4 := IsUltrametricDist.norm_add_le_max
    (j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' a)))
    (j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' b)))
  rw [← map_add (f := _), ← map_add (f := _), ← map_add (f := _), hab, map_one, map_one, map_one, norm_one] at h4
  exact absurd (h4.trans_lt (max_lt h1 h2')) (lt_irrefl _)

end TwistIne

open TwistIne in
theorem twistIne : TwistIne := by
  intro Ω _ _ _ l _ ι K' _ hdeg htc hdisc hsplit cc κ₀ hT A hA
  have := htc
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  obtain ⟨art, Y, a, τ, hart, -, hL, ha1, ha0, hYu⟩ := hT.alg
  have hAt : A ≠ ⊤ := fun h => ((UpperTheory.V.Base.places K' Ω l A).2.1 h).2 hA
  obtain ⟨w, hw⟩ := (UpperTheory.V.Base.places K' Ω l A).1 hAt
  have hdw : ((discr K' : ℤ) : 𝓞 K') ∉ w.asIdeal := by
    intro hd
    have h1 : A.valuation ((discr K' : ℤ) : Ω) < 1 := by simpa using (hw _).2 hd
    exact not_lt_of_not_dvd A (Fact.out : l.Prime) hA hdisc h1
  have hYw := hYu w hdw
  obtain ⟨μ, hμ, hM⟩ := hart.exists_isLAdicOf ι (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos K' 1)
  have hμe : μ = cycBar K' Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow hart hμ hM
  rw [pow_one] at hμe
  subst hμe
  have hval : ∀ σ ∈ Ine (F := K') A, ∃ x : (w.adicCompletion K')ˣ,
      ((κ₀ σ : (Qbar l)ˣ) : Qbar l) = locPow ι a w (x : w.adicCompletion K') ∧
        ((cycBar K' Ω l σ : (Qbar l)ˣ) : Qbar l) = locPow ι (fun _ => ((1 : ℕ) : ℤ)) w (x : w.adicCompletion K') := by
    intro σ hσ
    obtain ⟨x, hx, e⟩ := (hart.ine w A hw (toAb K' Ω σ)).2 ⟨σ, hσ, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · rw [hL.loc x σ e, hYw x hx, Units.val_one, map_one, one_mul]
    · rw [hM.loc x σ e, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow K' ((1 : ℕ) : ℝ)).1 w x hx, Units.val_one, map_one, one_mul]
  haveI : Subsingleton {j : w.adicCompletion K' →+* Qbar l // Continuous j} :=
    ⟨fun j j' => Subtype.ext (emb_unique K' hdeg hsplit A hA w hw j.1 j'.1 j.2 j'.2)⟩
  rcases isEmpty_or_nonempty {j : w.adicCompletion K' →+* Qbar l // Continuous j} with hJ | hJ
  · right
    intro σ hσ
    obtain ⟨x, h1, -⟩ := hval σ hσ
    apply Units.ext
    rw [h1, Units.val_one]
    unfold locPow
    exact finprod_of_isEmpty _
  · obtain ⟨j0⟩ := hJ
    have hlp : ∀ (n : (K' →+* ℂ) → ℤ) (y : w.adicCompletion K'), locPow ι n w y =
        j0.1 y ^ n ((ι.toRingHom.comp j0.1).comp (algebraMap K' (w.adicCompletion K'))) := fun n y => by
      haveI : Unique {j : w.adicCompletion K' →+* Qbar l // Continuous j} := uniqueOfSubsingleton j0
      unfold locPow
      rw [finprod_unique, Subsingleton.elim (default : {j : w.adicCompletion K' →+* Qbar l // Continuous j}) j0]
    rcases emb_two hdeg τ ((ι.toRingHom.comp j0.1).comp (algebraMap K' (w.adicCompletion K'))) with he | he
    · left
      intro σ hσ
      obtain ⟨x, h1, h2⟩ := hval σ hσ
      apply Units.ext
      rw [Units.val_inv_eq_inv_val, h1, h2, hlp, hlp, he, ha1]
      simp
    · right
      intro σ hσ
      obtain ⟨x, h1, -⟩ := hval σ hσ
      apply Units.ext
      rw [h1, hlp, he, ha0, zpow_zero, Units.val_one]

end UpperTheory.V.Cu2

end
end

