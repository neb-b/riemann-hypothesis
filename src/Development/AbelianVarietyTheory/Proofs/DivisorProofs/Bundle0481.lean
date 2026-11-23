module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimit
section
open IsLocalRing Polynomial CategoryTheory Limits

namespace GlobalTheory.TorsorColimElem

theorem exists_torsor_model_of_elements : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  intro ι _ _ _ R _ f hid hcomp B _ g hcompat hsurj hinj q hq D _ _ act hT
  let F : ι ⥤ CommRingCat.{0} :=
    { obj := fun i => CommRingCat.of (R i)
      map := fun {i j} h => CommRingCat.ofHom (f i j h.le)
      map_id := fun i => by
        ext x
        simp [hid]
      map_comp := fun {i j k} a b => by
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply]
        exact (RingHom.congr_fun (hcomp i j k a.le b.le) x).symm }
  let c : Cocone F :=
    { pt := CommRingCat.of B
      ι := { app := fun i => CommRingCat.ofHom (g i)
             naturality := fun i j h => by
               ext x
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
                 CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, F]
               exact RingHom.congr_fun (hcompat i j h.le) x } }
  have hc : IsColimit c := by
    haveI : ReflectsColimit F (forget CommRingCat) :=
      reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat)
    apply isColimitOfReflects (forget CommRingCat)
    apply Types.FilteredColimit.isColimitOf
    · intro x
      obtain ⟨i, y, hy⟩ := hsurj x
      exact ⟨i, y, hy.symm⟩
    · intro i j x y hxy
      have hxy' : g i x = g j y := hxy
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      have h0 : g k (f i k hik x - f j k hjk y) = 0 := by
        have e1 : g k (f i k hik x) = g i x := by rw [← hcompat i k hik]; rfl
        have e2 : g k (f j k hjk y) = g j y := by rw [← hcompat j k hjk]; rfl
        rw [map_sub, e1, e2, hxy', sub_self]
      obtain ⟨l, hkl, hl⟩ := hinj k _ h0
      refine ⟨l, homOfLE (hik.trans hkl), homOfLE (hjk.trans hkl), ?_⟩
      change f i l _ x = f j l _ y
      rw [map_sub, sub_eq_zero] at hl
      rw [← hcomp i k l hik hkl, ← hcomp j k l hjk hkl]
      exact hl
  have hT' : GlobalTheory.LocAcyc.IsZModTorsor B D q act := hT
  obtain ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩ :=
    @GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit ι _ _ F c hc q hq D _ ‹Algebra B D› act hT'
  exact ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩

end GlobalTheory.TorsorColimElem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformiserSplitPlaceCmOrderNonunit
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem span_sup_pow_eq_of_notMem_sq {R : Type} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {x : R}
    (hx : x ∈ v.asIdeal) (hx2 : x ∉ v.asIdeal ^ 2) (n : ℕ) : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal := by
  have hd : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) ∣ v.asIdeal ^ (n + 1) := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow v.prime _).1 hd
  rw [associated_iff_eq] at hi
  have hle : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) ≤ v.asIdeal :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hx) (Ideal.pow_le_self (by omega))
  have hxi : x ∈ v.asIdeal ^ i := hi ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)
  rw [hi] at hle ⊢
  match i, hle, hxi with
  | 0, hle, _ => exact absurd (top_le_iff.1 (by simpa using hle)) v.isPrime.ne_top
  | 1, _, _ => exact pow_one _
  | i + 2, _, hxi => exact absurd (Ideal.pow_le_pow_right (by omega) hxi) hx2

theorem eq_exp_neg_one_of_le_of_not_le {g : WithZero (Multiplicative ℤ)} (h1 : g ≤ WithZero.exp (-1 : ℤ))
    (h2 : ¬ g ≤ WithZero.exp (-2 : ℤ)) : g = WithZero.exp (-1 : ℤ) := by
  have h0 : g ≠ 0 := fun h => h2 (h ▸ zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  omega

theorem locIn_succ_nonunit_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → ∃ x : OF E, (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) ∧ ∀ (n : ℕ) (π y : (Af E)ˣ), (∀ P, Over P v → (π : Af E) P = iota x P) → (LocIn n v ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (n + 1) v (y : Af E) ∧ ¬ ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) := by
  intro E _ _ _ v hv
  have he := fun P hP => ((_root_.GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hv).2 P hP).2.1
  obtain ⟨x, hx1, hx2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have hval : ∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ) := fun P hP =>
    eq_exp_neg_one_of_le_of_not_le (by simpa using val_iota_le_of_mem hP 1 hx1)
      (fun h => hx2 ((he P hP x 2).1 ((val_iota_le_iff P 2 x).1 (by simpa using h))))
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  refine ⟨x, hval, fun n π y hπ => ?_⟩
  have hx0 : ∀ P, Over P v → iota x P ≠ 0 := fun P hP h => by
    have := hval P hP
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hq : ∀ P, Over P v → ((π⁻¹ * y : (Af E)ˣ) : Af E) P = (iota x P)⁻¹ * (y : Af E) P := fun P hP => by
    rw [Units.val_mul, mul_coord, inv_coord, hπ P hP]
  constructor
  · intro h
    refine ⟨?_, fun hu => ?_⟩
    · obtain ⟨b, hb⟩ := h
      refine ⟨x * b, fun P hP => ?_⟩
      have h0 := hx0 P hP
      have : (y : Af E) P - iota (x * b) P = iota x P * (((π⁻¹ * y : (Af E)ˣ) : Af E) P - iota b P) := by
        rw [hq P hP, iota_mul, mul_coord]; field_simp
      rw [this, map_mul, hval P hP]
      refine (mul_le_mul' le_rfl (hb P hP)).trans_eq ?_
      rw [← WithZero.exp_add]; congr 1; push_cast; ring
    · obtain ⟨P, -, -, hP, -⟩ := hv
      have h1 := h.val_le hP
      rw [hq P hP, map_mul, map_inv₀, hval P hP, hu P hP, mul_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h1
      omega
  · rintro ⟨h, hu⟩
    push Not at hu
    obtain ⟨Q, hQ, hyQ⟩ := hu
    have hyQ' : Valued.v ((y : Af E) Q) < 1 := lt_of_le_of_ne (h.val_le hQ) hyQ
    obtain ⟨a, ha⟩ := h
    have hav : a ∈ v.asIdeal := by
      have h2 : Valued.v ((y : Af E) Q - iota a Q) < 1 :=
        ((ha Q hQ).trans (WithZero.exp_le_exp.2 (by push_cast; omega))).trans_lt hlt
      have h3 := Valuation.map_sub_lt _ hyQ' h2
      rw [sub_sub_cancel] at h3
      have h4 : Valued.v (iota a Q) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
        by_cases h0 : Valued.v (iota a Q) = 0
        · rw [h0]; exact zero_le'
        · rw [← WithZero.exp_log h0] at h3 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
          rw [WithZero.exp_le_exp]; push_cast; omega
      simpa using (he Q hQ a 1).1 ((val_iota_le_iff Q 1 a).1 h4)
    rw [← span_sup_pow_eq_of_notMem_sq v (by simpa using hx1) hx2 n] at hav
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hav
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    refine ⟨b, fun P hP => ?_⟩
    have h0 := hx0 P hP
    have : ((π⁻¹ * y : (Af E)ˣ) : Af E) P - iota b P =
        (iota x P)⁻¹ * (((y : Af E) P - iota (b * x + t) P) + iota t P) := by
      rw [hq P hP, iota_add, iota_mul, add_coord, mul_coord]; field_simp; ring
    rw [this, map_mul, map_inv₀, hval P hP]
    refine (mul_le_mul' le_rfl (Valuation.map_add_le _ (ha P hP) (val_iota_le_of_mem hP (n + 1) ht))).trans_eq ?_
    rw [← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; push_cast; ring

end GlobalTheory.CMVal.Euler
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryWithDeterminant
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UnitDet

theorem exists_imag (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ ξ : E, ξ ≠ 0 ∧ IsCMField.complexConj E ξ = -ξ := by
  obtain ⟨t, ht⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  refine ⟨t - IsCMField.complexConj E t, sub_ne_zero.2 (fun h => ht h.symm), ?_⟩
  simp [IsCMField.complexConj_apply_apply]

theorem herm_single {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.single_apply, apply_ite, ite_mul]

theorem exists_aniso {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {G : Matrix (Fin r) (Fin r) E} (hdet : G.det ≠ 0) (hr : 0 < r) :
    ∃ e : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G e e ≠ 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨ξ, hξ0, hξ⟩ := exists_imag E
  have h0 : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm G x y = 0 := by
    intro x y
    have h1 := hne (x + (1:E) • y)
    have h2 := hne (x + ξ • y)
    rw [GlobalTheory.FlagData.herm_add_smul_left, GlobalTheory.FlagData.herm_add_smul_right,
      GlobalTheory.FlagData.herm_add_smul_right, hne x, hne y] at h1 h2
    simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, hξ] at h1 h2
    have h3 : (-2 * ξ) * ReciprocityTheory.ChartRestriction.G.FD.herm G x y = 0 := by linear_combination h2 - ξ * h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (by simpa using hξ0)
    · exact h
  apply hdet
  have hG0 : G = 0 := by
    ext a b
    rw [← herm_single G a b, h0]
    rfl
  rw [hG0]
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (u : E), 0 < r → (∀ a b, IsCMField.complexConj E (G a b) = G b a) → G.det ≠ 0 → u * IsCMField.complexConj E u = 1 → ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (γ : Matrix (Fin r) (Fin r) E).det = u := by
  intro E _ _ _ r G u hr hG hdet hu
  obtain ⟨e, he⟩ := exists_aniso hdet hr
  have hG' : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := hG
  have hch : IsCMField.complexConj E (ReciprocityTheory.ChartRestriction.G.FD.herm G e e) = ReciprocityTheory.ChartRestriction.G.FD.herm G e e :=
    GlobalTheory.FlagData.cc_herm hG' e e
  set h := ReciprocityTheory.ChartRestriction.G.FD.herm G e e with hh
  set α : E := (u - 1) / h with hα
  have hdetT : (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α).det = u := by
    set v : Fin r → E := fun b => α * ∑ k, G b k * ReciprocityTheory.ChartRestriction.G.FD.cc (e k) with hv
    have hT : ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α = 1 + replicateCol (Fin 1) e *
        replicateRow (Fin 1) v := by
      ext a b
      simp [ReciprocityTheory.ChartRestriction.G.FD.transvMat, replicateCol, replicateRow, Matrix.mul_apply, Matrix.one_apply]
      ring
    have hd := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) e v
    rw [hT]
    refine hd.trans ?_
    have : v ⬝ᵥ e = α * h := by
      rw [hh, hv]
      simp only [dotProduct, ReciprocityTheory.ChartRestriction.G.FD.herm, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, hα]
    field_simp
    ring
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have key : IsCMField.complexConj E α + α + α * IsCMField.complexConj E α * h = 0 := by
    have hca : IsCMField.complexConj E α = (IsCMField.complexConj E u - 1) / h := by
      rw [hα, map_div₀, map_sub, map_one, hch]
    rw [hca, hα]
    field_simp
    linear_combination hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdetT ▸ hu0), ?_, ?_⟩
  · intro x y
    show ReciprocityTheory.ChartRestriction.G.FD.herm G (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α *ᵥ x)
      (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α *ᵥ y) = ReciprocityTheory.ChartRestriction.G.FD.herm G x y
    rw [GlobalTheory.FlagData.transvMat_mulVec, GlobalTheory.FlagData.transvMat_mulVec, GlobalTheory.FlagData.herm_add_smul_left,
      GlobalTheory.FlagData.herm_add_smul_right, GlobalTheory.FlagData.herm_add_smul_right]
    have e1 : ReciprocityTheory.ChartRestriction.G.FD.cc (α * ReciprocityTheory.ChartRestriction.G.FD.herm G y e) =
        IsCMField.complexConj E α * ReciprocityTheory.ChartRestriction.G.FD.herm G e y := by
      rw [← GlobalTheory.FlagData.cc_herm hG' y e]
      exact map_mul (IsCMField.complexConj E) _ _
    rw [e1, ← hh]
    linear_combination (ReciprocityTheory.ChartRestriction.G.FD.herm G x e * ReciprocityTheory.ChartRestriction.G.FD.herm G e y) * key
  · exact hdetT

end GlobalTheory.UnitDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIndexLeftRightCosetSumsEq
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem sum_out_left_translate {A : Type} [Group A] (U : Subgroup A) [Fintype (A ⧸ U)] (F : A → ℂ)
    (hF : ∀ u ∈ U, ∀ a, F (a * u) = F a) (g : A) :
    ∑ y : A ⧸ U, F (g * y.out) = ∑ y : A ⧸ U, F y.out := by
  refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun y => ?_
  have h1 : (MulAction.toPerm g y : A ⧸ U) = ((g * y.out : A) : A ⧸ U) := by
    rw [MulAction.toPerm_apply, ← MulAction.Quotient.coe_smul_out, smul_eq_mul]
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (g * y.out)
  rw [h1, hu, hF u u.2]

theorem unimodFin : UnimodFin := by
  intro A _ U V f hU hV hl hr
  haveI : U.FiniteIndex := ⟨hU⟩
  haveI : V.FiniteIndex := ⟨hV⟩
  letI : Fintype (A ⧸ U) := Fintype.ofFinite _
  letI : Fintype (A ⧸ V) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have e1 : ∀ x : A ⧸ U, ∑ y : A ⧸ V, f (y.out⁻¹ * x.out) = ∑ y : A ⧸ V, f y.out⁻¹ := by
    intro x
    have := sum_out_left_translate V (fun a => f a⁻¹)
      (fun v hv a => by simp only [mul_inv_rev]; exact hl _ (V.inv_mem hv) _) x.out⁻¹
    simpa [mul_inv_rev] using this
  have e2 : ∀ y : A ⧸ V, ∑ x : A ⧸ U, f (y.out⁻¹ * x.out) = ∑ x : A ⧸ U, f x.out :=
    fun y => sum_out_left_translate U f hr _
  have := Finset.sum_comm (s := (Finset.univ : Finset (A ⧸ U))) (t := (Finset.univ : Finset (A ⧸ V)))
    (f := fun x y => f (y.out⁻¹ * x.out))
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact this

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjModIdealExistsCongrOneMulMemRange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem finite_surj_mod_ideal_exists_congr_one_mul_mem_range :
    ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), f.Finite → ∀ J : Ideal B,
      Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) →
      ∃ r : B, r - 1 ∈ J ∧ ∀ c : C, ∃ b : B, f r * c = f b := by
  intro B C _ _ f hf J hs
  letI := f.toAlgebra
  haveI : Module.Finite B C := hf
  set P : Submodule B C := LinearMap.range (Algebra.linearMap B C) with hP
  have hle : (⊤ : Submodule B (C ⧸ P)) ≤ J • ⊤ := by
    rintro m -
    obtain ⟨c, rfl⟩ := P.mkQ_surjective m
    obtain ⟨b, hb⟩ := hs (Ideal.Quotient.mk _ c)
    have hy : c - f b ∈ J • (⊤ : Submodule B C) := by
      rw [Ideal.smul_top_eq_map]
      exact Ideal.Quotient.eq.mp hb.symm
    have hfb : P.mkQ (f b) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩
    have hc : P.mkQ c = P.mkQ (c - f b) := by rw [map_sub, hfb, sub_zero]
    rw [hc]
    have h1 : P.mkQ (c - f b) ∈ (J • (⊤ : Submodule B C)).map P.mkQ := Submodule.mem_map_of_mem hy
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤
    Module.Finite.fg_top hle
  refine ⟨r, hr1, fun c => ?_⟩
  have h := hr (P.mkQ c) trivial
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  rw [Algebra.smul_def] at hb
  exact hb.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetCharacterOrthZero
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetOrth

def twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) : Representation ℂ H V where
  toFun x := ((η x : ℂ) ^ a) • ρ x
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, Units.val_mul, mul_pow, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_comm]

theorem trace_twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) (x : H) :
    LinearMap.trace ℂ V (twist η a ρ x) = LinearMap.trace ℂ V (ρ x) * (η x : ℂ) ^ a := by
  show LinearMap.trace ℂ V (((η x : ℂ) ^ a) • ρ x) = _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem sum_trace_mul_star_nat {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ H W) :
    ∃ k : ℕ, ∑ x, LinearMap.trace ℂ V (ρ x) * star (LinearMap.trace ℂ W (σ x)) = (Nat.card H : ℂ) * k := by
  have hne : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hne
  have h := FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of σ) (FDRep.of ρ)
  refine ⟨Module.finrank ℂ (FDRep.of σ ⟶ FDRep.of ρ), ?_⟩
  rw [← h, mul_inv_cancel_left₀ hne]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.BadShare.ZCalc.character_inv]
  rfl

end GlobalTheory.Shin.CosetOrth

open GlobalTheory.Shin.CosetOrth in
theorem GlobalTheory.Shin.finsum_coset_mul_star_eq_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  intro G Γ _ _ _ _ φ s hp hs X Y hX hY h0
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have gen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hl0 : Nat.card Γ ≠ 0 := hp.ne_zero
  obtain ⟨η, -, -, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s gen _ (Complex.isPrimitiveRoot_exp _ hl0)
  obtain ⟨e1, e2⟩ := hF X Y
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  letI : Fintype (G ⋊[φ] Γ) := Fintype.ofFinite _
  have hm : ∀ a : ℕ, ∃ k : ℕ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = (Nat.card (G ⋊[φ] Γ) : ℂ) * k := by
    intro a
    obtain ⟨n, ρ, hρ⟩ := hX
    obtain ⟨m, σ, hσ⟩ := hY
    obtain ⟨k, hk⟩ := sum_trace_mul_star_nat ρ (twist η a σ)
    refine ⟨k, ?_⟩
    rw [finsum_eq_sum_of_fintype, ← hk]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [trace_twist, hρ x, hσ x]
    rfl
  choose k hk using hm
  have hH : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsum : ∑ a ∈ Finset.range (Nat.card Γ), k a = 0 := by
    rw [h0, mul_zero] at e1
    simp_rw [hk] at e1
    rw [← Finset.mul_sum] at e1
    have := (mul_eq_zero.mp e1.symm).resolve_left hH
    exact_mod_cast this
  have hk0 : ∀ a ∈ Finset.range (Nat.card Γ), k a = 0 := Finset.sum_eq_zero_iff.mp hsum
  have hR : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hk a, hk0 a ha]; simp
  rw [hR] at e2
  exact (mul_eq_zero.mp e2).resolve_left (by exact_mod_cast hl0)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallAevalLineVanishingIdealIff
section
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

theorem aeval_smul_of_isHomogeneous {k K : Type} [Field k] [Field K] [Algebra k K] {N d : ℕ}
    {g : MvPolynomial (Fin N) k} (hg : g.IsHomogeneous d) (t : K) (z : Fin N → K) :
    aeval (t • z) g = t ^ d * aeval z g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hg (mem_support_iff.1 hs)
  have hd : ∑ i, s i = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring



end GlobalTheory.ChowHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtDeformedProductDerivativeTermStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_deformedProductDerivativeTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x) (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by
  first | exact @GlobalTheory.DeformedSum.hasFDerivAt_dTerm | exact GlobalTheory.DeformedSum.hasFDerivAt_dTerm | (intros; apply GlobalTheory.DeformedSum.hasFDerivAt_dTerm <;> assumption)
end

