module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PAlgOfFix
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

private theorem chi_fixed {E : Type} [Field E] [NumberField E] [IsCMField E] (χ : HChar E)
    (hfix : ∀ z, cj E z = z → χ.1 z = 1) (τ : E →+* ℂ) (z : ℂ)
    (hs : expU (atEmb τ (starRingEnd ℂ z)) = expU (atEmb τ z)) :
    Complex.exp (expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z) = 1 := by
  rw [← chiInf_expU_atEmb]
  have h1 : cj E (infId E (expU (atEmb τ z))) = infId E (expU (atEmb τ z)) := by
    refine (GlobalTheory.NormExpo.conjAd_infId E _).trans ?_
    rw [GlobalTheory.NormExpo.star_expU_atEmb, hs]
  have h2 : chiInf χ (expU (atEmb τ z)) = 1 := hfix _ h1
  rw [h2]
  rfl

private theorem expU_neg_pi {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    expU (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I))) = expU (atEmb τ ((Real.pi : ℂ) * Complex.I)) := by
  classical
  refine Units.ext (funext fun w => ?_)
  change Complex.exp (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I)) w) =
    Complex.exp (atEmb τ ((Real.pi : ℂ) * Complex.I) w)
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    split_ifs <;> simp [Complex.exp_neg, Complex.exp_pi_mul_I]
  · simp [Pi.single_eq_of_ne hw]

private theorem add_eq_zero_of {p q : ℂ} (h : ∀ t : ℝ, Complex.exp (p * t + q * starRingEnd ℂ (t : ℂ)) = 1) : p + q = 0 := by
  have hf : (fun t : ℝ => Complex.exp ((p + q) * t)) = fun _ => 1 := by
    funext t
    have := h t
    rw [Complex.conj_ofReal] at this
    rw [add_mul]; exact this
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((p + q) * t)) (Complex.exp ((p + q) * ((0 : ℝ) : ℂ)) * ((p + q) * 1)) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (p + q) * (t : ℂ)) ((p + q) * 1) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (p + q)
    exact h0.cexp
  rw [hf] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using this

theorem UpperTheory.Gal.Int.Div.algOfFix_of :
    AlgOfFix := by
  intro E _ _ _ χ hfix
  have key : ∀ τ : E →+* ℂ, ∃ n : ℤ, expo χ τ = n := by
    intro τ
    have hpq : expo χ τ + expo χ (ComplexEmbedding.conjugate τ) = 0 :=
      add_eq_zero_of fun t => chi_fixed χ hfix τ t (by rw [Complex.conj_ofReal])
    have h := chi_fixed χ hfix τ _ (expU_neg_pi τ)
    have hq : expo χ (ComplexEmbedding.conjugate τ) = - expo χ τ := by linear_combination hpq
    rw [hq] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ h2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hn
    linear_combination hn
  choose n hn using key
  exact ⟨n, isAlgPos_of_expo E χ n hn⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCharOfZeta
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.charOfZeta_of :
    CharOfZeta := by
  intro E _ _ _ a U hU ζ hζ hcen hrat hsc
  choose c hc using hsc
  obtain ⟨φ₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ₀ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hval : ∀ z, φ₀ (g₀ * ζ z) = c z * φ₀ g₀ := fun z => by
    have := congrFun (hc z φ₀ h₀) g₀
    rwa [GlobalTheory.DefU.RU_apply, Pi.smul_apply, smul_eq_mul] at this
  have hcz : ∀ z, c z = φ₀ (g₀ * ζ z) / φ₀ g₀ := fun z => by
    rw [hval z, mul_div_cancel_right₀ _ hg₀]
  have hcont : Continuous c := by
    have h1 : Continuous fun z => φ₀ (g₀ * ζ z) :=
      (hU.aut φ₀ h₀).cont.comp (continuous_const.mul hζ)
    have h2 : c = fun z => φ₀ (g₀ * ζ z) / φ₀ g₀ := funext hcz
    rw [h2]
    exact h1.div_const _
  have hone : c 1 = 1 := by
    rw [hcz, map_one, mul_one, div_self hg₀]
  have hmul : ∀ z z', c (z * z') = c z * c z' := fun z z' => by
    have h1 : RU E a (ζ (z * z')) φ₀ = (c z * c z') • φ₀ := by
      rw [map_mul, map_mul, Module.End.mul_apply, hc z' φ₀ h₀, map_smul, hc z φ₀ h₀, smul_smul, mul_comm]
    rw [hc _ φ₀ h₀] at h1
    exact smul_left_injective ℂ hne h1
  let f : Ideles E →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  have hinvc : Continuous fun z => (c z)⁻¹ := by
    refine hcont.inv₀ fun z => ?_
    intro h0
    have := hmul z z⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  refine ⟨⟨f.toHomUnits, ?_, fun k => ?_⟩, fun z φ hφ => ?_⟩
  · refine Units.continuous_iff.2 ⟨hcont, ?_⟩
    have : (fun z => (((f.toHomUnits z)⁻¹ : ℂˣ) : ℂ)) = fun z => (c z)⁻¹ := by
      funext z
      rw [Units.val_inv_eq_inv_val]
      rfl
    exact this ▸ hinvc
  · refine Units.ext ?_
    change c (diagUnits E k) = 1
    rw [hcz, ← hcen, (hU.aut φ₀ h₀).left _ (hrat k), div_self hg₀]
  · exact hc z φ hφ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCplMem
section
open NumberField IsDedekindDomain

namespace UpperTheory.Gal.Int.Div

theorem cplMem_of : CplMem := by
  intro E _ _ _ w y y' hy
  exact (GlobalTheory.Mem.Chr.conjPl_iff_mem (GlobalTheory.SplitPts.conjE E) (cpl w) w).1
    (GlobalTheory.CuspRep.conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) w) y y' hy

end UpperTheory.Gal.Int.Div
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PGapLac
section
noncomputable section

open GlobalTheory.RoadWGeo GlobalTheory.CongL

namespace UpperTheory.Gal.Int.Div

private theorem getD_eq (J : Finset ℤ) (a : ℕ) (hcard : J.card = a) (i : ℕ) (hi : i < a) :
    (J.val.sort (· ≤ ·)).getD i 0 = J.orderEmbOfFin hcard ⟨i, hi⟩ := by
  rw [Finset.orderEmbOfFin_apply]
  have hl : i < (J.val.sort (· ≤ ·)).length := by
    simpa [hcard] using hi
  rw [List.getD_eq_getElem _ _ hl]
  rfl

private theorem sum_shift (A : Finset ℤ) (c : ℤ) : ∑ x ∈ A, (x - c) = A.sum id - (A.card : ℤ) * c := by
  simp [Finset.sum_sub_distrib]

private theorem avg_lt {J A B : Finset ℤ} {c : ℤ} (hmin : ∀ x ∈ J, c ≤ x)
    (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * (x - c) < y - c) (hA : A ⊆ J) (hB : B ⊆ J)
    (hBn : B.Nonempty) {m : ℤ} (hm : m ∈ A) (hlt : ∀ b ∈ B, b < m) :
    (A.card : ℤ) * B.sum id < (B.card : ℤ) * A.sum id := by
  have h1 : m - c ≤ ∑ x ∈ A, (x - c) :=
    Finset.single_le_sum (f := fun x => x - c) (fun x hx => sub_nonneg.2 (hmin x (hA hx))) hm
  have hc : (A.card : ℤ) ≤ J.card := by exact_mod_cast Finset.card_le_card hA
  have h2 : ∑ b ∈ B, (A.card : ℤ) * (b - c) < ∑ _b ∈ B, (m - c) := by
    refine Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_
    have h3 := hg b (hB hb) m (hA hm) (hlt b hb)
    have h4 := mul_le_mul_of_nonneg_right hc (sub_nonneg.2 (hmin b (hB hb)))
    linarith
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, sum_shift] at h2
  rw [sum_shift] at h1
  have h5 : (B.card : ℤ) * (m - c) ≤ B.card * (A.sum id - (A.card : ℤ) * c) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

private theorem lacunary_of_shift {J : Finset ℤ} {c : ℤ} (hmin : ∀ x ∈ J, c ≤ x)
    (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * (x - c) < y - c) : Lacunary J := by
  intro A B hA hB hd hAn hBn
  have hne : (A ∪ B).Nonempty := hAn.mono Finset.subset_union_left
  have hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne := fun x hx => Finset.le_max' _ _ hx
  rcases Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm
  · refine (avg_lt hmin hg hA hB hBn hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'
    intro e
    exact Finset.disjoint_left.1 hd hm (e ▸ hb)
  · refine (avg_lt hmin hg hB hA hAn hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne
    intro e
    exact Finset.disjoint_left.1 hd hb (e ▸ hm)

theorem gapLac_of : GapLac := by
  intro a J hcard hgap
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hJ : J = ∅ := Finset.card_eq_zero.1 hcard
    subst hJ
    exact lacunary_of_shift (c := 0) (by simp) (by simp)
  have hmem : ∀ x ∈ J, ∃ i, J.orderEmbOfFin hcard i = x := by
    intro x hx
    have : x ∈ Set.range (J.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    exact this
  refine lacunary_of_shift (c := J.orderEmbOfFin hcard ⟨0, ha⟩) (fun x hx => ?_) fun x hx y hy hxy => ?_
  · obtain ⟨i, rfl⟩ := hmem x hx
    exact (J.orderEmbOfFin hcard).monotone (Fin.mk_le_of_le_val (Nat.zero_le _))
  · obtain ⟨i, rfl⟩ := hmem x hx
    obtain ⟨j, rfl⟩ := hmem y hy
    have hij : i < j := (J.orderEmbOfFin hcard).lt_iff_lt.1 hxy
    obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by have : (i : ℕ) < j := hij; omega⟩
    have hk1 : k + 1 < a := hk ▸ j.2
    have hk0 : k < a := by omega
    have hjk : j = ⟨k + 1, hk1⟩ := Fin.ext hk
    have hg := hgap k hk1
    rw [getD_eq J a hcard (k + 1) hk1, getD_eq J a hcard 0 ha, getD_eq J a hcard k hk0] at hg
    have hik : J.orderEmbOfFin hcard i ≤ J.orderEmbOfFin hcard ⟨k, hk0⟩ :=
      (J.orderEmbOfFin hcard).monotone (by
        have : (i : ℕ) < j := hij
        show (i : ℕ) ≤ k
        omega)
    rw [hcard, hjk]
    have h6 := mul_le_mul_of_nonneg_left (sub_le_sub_right hik (J.orderEmbOfFin hcard ⟨0, ha⟩))
      (Int.natCast_nonneg a)
    linarith

end UpperTheory.Gal.Int.Div

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLacConj
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private theorem lacunary_image_sub {J : Finset ℤ} (c : ℤ) (h : Lacunary J) :
    Lacunary (J.image fun x => c - x) := by
  classical
  intro A B hA hB hd hAn hBn e
  have inj : Function.Injective (fun x : ℤ => c - x) := fun x y e => by simpa using e
  have back : ∀ S : Finset ℤ, S ⊆ J.image (fun x => c - x) → S.image (fun x => c - x) ⊆ J := by
    intro S hS x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 (hS hy)
    simpa using hz
  have hsum : ∀ S : Finset ℤ, (S.image fun x => c - x).sum id = (S.card : ℤ) * c - S.sum id := by
    intro S
    rw [Finset.sum_image (fun x _ y _ e => inj e)]
    simp only [id]
    rw [Finset.sum_sub_distrib (fun _ => c) (fun x => x), Finset.sum_const, nsmul_eq_mul]
  refine h _ _ (back A hA) (back B hB) ((Finset.disjoint_image inj).2 hd) (hAn.image _) (hBn.image _) ?_
  rw [Finset.card_image_of_injective _ inj, Finset.card_image_of_injective _ inj, hsum, hsum]
  linear_combination -e

private theorem wtJumps_dual {a : ℕ} (lam : DomWeight a) :
    wtJumps lam.dual = (wtJumps lam).image fun x => ((a : ℤ) - 1) - x := by
  have key : ∀ k : Fin a, ((k : ℕ) : ℤ) - lam.dual.w k = ((a : ℤ) - 1) - (((k.rev : ℕ) : ℤ) - lam.w k.rev) := by
    intro k
    have h1 : lam.dual.w k = -lam.w k.rev := rfl
    have h2 := Fin.val_rev k
    have h3 := k.2
    rw [h1]
    omega
  ext x
  simp only [wtJumps, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k.rev, rfl⟩, (key k).symm⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨k.rev, ?_⟩
    rw [key, Fin.rev_rev]

theorem UpperTheory.Gal.Int.Div.lacConj_of :
    CplMem → LacConj := by
  intro hC E _ _ _ l _ ι a ha U v ⟨τ, hτ, lam, hw, hl⟩
  refine ⟨ComplexEmbedding.conjugate τ, ?_, lam.dual, GlobalTheory.DefiniteBC.hasWeightAt_conjugate ha hw, ?_⟩
  · intro x hx
    have hy : ((IsCMField.ringOfIntegersComplexConj E x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := rfl
    have h := hτ _ ((hC E v x _ hy).1 hx)
    rw [hy, IsCMField.complexEmbedding_complexConj] at h
    exact h
  · rw [wtJumps_dual]
    exact lacunary_image_sub _ hl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocIso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

open GlobalTheory.SplitPts in
private noncomputable def cEq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cpl w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc (conjE E) w) ⟨(conjLoc (conjE E) w).injective, fun y => ⟨psi w y, conjLoc_psi w y⟩⟩

open GlobalTheory.SplitPts in
private theorem conjInvT_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    (g : GL (Fin a) ((cpl w).adicCompletion E)) :
    GlobalTheory.LFun.ConjPlace.invT (cEq w) a g = invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

private theorem invT_invT {R : Type} [CommRing R] {a : ℕ} (h : GL (Fin a) R) : invT a R (invT a R h) = h := by
  apply Units.ext
  change ((invT a R h)⁻¹ : GL (Fin a) R).val.transpose = h.val
  rw [← map_inv]
  change (((h⁻¹)⁻¹ : GL (Fin a) R).val.transpose).transpose = h.val
  rw [inv_inv, Matrix.transpose_transpose]

open GlobalTheory.SplitPts in
private theorem conjInvT_symm_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    (h : GL (Fin a) (w.adicCompletion E)) :
    (GlobalTheory.LFun.ConjPlace.invT (cEq w) a).symm h = invT a _ (Matrix.GeneralLinearGroup.map (psi w) h) := by
  rw [MulEquiv.symm_apply_eq, conjInvT_eq, invT_map,
    show Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (Matrix.GeneralLinearGroup.map (psi w) h) = h from
      Units.ext (Matrix.ext fun i j => conjLoc_psi w _), invT_invT]

open GlobalTheory.SplitPts in
theorem UpperTheory.Gal.Int.Div.locIso_of :
    LocIso := by
  intro E _ _ _ a w hw
  refine ⟨?_, ?_⟩
  · unfold locU
    rw [(over_split hw).2.1]
  let e := GlobalTheory.LFun.ConjPlace.invT (cEq w) a
  have hc1 : Continuous e := by
    have e1 : (e : GL (Fin a) ((cpl w).adicCompletion E) → GL (Fin a) (w.adicCompletion E)) =
        fun g => invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g) := funext (conjInvT_eq w)
    rw [e1]
    exact (continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec (conjE E) w).1))
  have hc2 : Continuous e.symm := by
    have e1 : (e.symm : GL (Fin a) (w.adicCompletion E) → GL (Fin a) ((cpl w).adicCompletion E)) =
        fun h => invT a _ (Matrix.GeneralLinearGroup.map (psi w) h) := funext (conjInvT_symm_eq w)
    rw [e1]
    exact (continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))
  refine ⟨{ e with continuous_toFun := hc1, continuous_invFun := hc2 }, fun x => ?_, fun g hg => ?_, ?_⟩
  · change e (cLoc (cpl w) x) = cLoc w x
    have h := comp_eq x w
    rw [conjInvT_eq w]
    set m := Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (cLoc (cpl w) x) with hm
    have h' : m.val.transpose * (cLoc w x).val = 1 := h
    apply Units.ext
    change ((m⁻¹ : GL (Fin a) _).val).transpose = (cLoc w x).val
    calc ((m⁻¹ : GL (Fin a) _).val).transpose
        = ((m⁻¹ : GL (Fin a) _).val).transpose * (m.val.transpose * (cLoc w x).val) := by rw [h', Matrix.mul_one]
      _ = (m.val * (m⁻¹ : GL (Fin a) _).val).transpose * (cLoc w x).val := by
          rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (cLoc w x).val := by
          rw [Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  · exact (GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (cEq w)
      (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff (cEq w) (conjLoc_spec (conjE E) w).2.2) g).1 hg
  · intro V _ _ σ hσ
    have h1 := GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap (cEq w).symm
      (conjLoc_spec (conjE E) w).1 (σ.comp (GlobalTheory.TypeTame.invTranspose a))
      (GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose _ a V σ hσ)
    convert h1 using 1
    refine MonoidHom.ext fun g => ?_
    change σ (e g) = σ (GlobalTheory.TypeTame.invTranspose a (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g))
    rw [conjInvT_eq w]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PTyConj
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private def smIrrComap {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (β : G ≃ₜ* H) (σ : SmIrr G) : SmIrr H :=
  ⟨σ.V, σ.ρ.comp β.symm.toMulEquiv.toMonoidHom, fun v => (σ.smooth v).preimage β.symm.continuous,
    (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv (ρ := σ.ρ.comp β.symm.toMulEquiv.toMonoidHom) (σ := σ.ρ)
      (fun h => β.symm h) β.symm.surjective (LinearEquiv.refl ℂ _) (fun _ _ => rfl)).2 σ.irred⟩

theorem UpperTheory.Gal.Int.Div.tyConj_of :
    LocIso → TyConj := by
  intro hL E _ _ _ l a U w hw hT
  obtain ⟨hU, β, hβ, -, hc⟩ := hL E a w hw
  obtain ⟨m, J, θ, χ, hJo, hJc, hJt, hθ, hχ, hcus, φ, hφU, hφ0, hφ⟩ := hT
  let J' : Subgroup (GL (Fin a) ((cpl w).adicCompletion E)) := J.comap β.toMulEquiv.toMonoidHom
  let r : J' →* J :=
    { toFun := fun g => ⟨β g.1, g.2⟩
      map_one' := Subtype.ext (map_one β)
      map_mul' := fun x y => Subtype.ext (map_mul β _ _) }
  refine ⟨m, J', θ.comp r, χ, ?_, ?_, ?_, ?_, hχ, ?_, φ, hφU, hφ0, ?_⟩
  · exact hJo.preimage β.continuous
  · exact β.toHomeomorph.isCompact_preimage.2 hJc
  · intro x hx k hk hxk
    have h := hJt (β x) hx k hk (by rw [← map_pow, hxk, map_one])
    exact β.injective (h.trans (map_one β).symm)
  · intro t
    obtain ⟨g, rfl⟩ := hθ t
    have hg : β.symm g.1 ∈ J' := by
      show β (β.symm g.1) ∈ J
      rw [β.apply_symm_apply]
      exact g.2
    refine ⟨⟨β.symm g.1, hg⟩, ?_⟩
    show θ (r _) = θ g
    exact congrArg θ (Subtype.ext (β.apply_symm_apply _))
  · intro σ' v hv he
    have hcu : GlobalTheory.SmGL.IsCuspidal (smIrrComap β σ').ρ := by
      refine hcus (smIrrComap β σ') v hv fun g => ?_
      have hg : β.symm g.1 ∈ J' := by
        show β (β.symm g.1) ∈ J
        rw [β.apply_symm_apply]
        exact g.2
      have h := he ⟨β.symm g.1, hg⟩
      have e : r ⟨β.symm g.1, hg⟩ = g := Subtype.ext (β.apply_symm_apply _)
      have e' : (θ.comp r) ⟨β.symm g.1, hg⟩ = θ g := congrArg θ e
      rw [e'] at h
      exact h
    have h3 := hc σ'.V (σ'.ρ.comp β.symm.toMulEquiv.toMonoidHom) hcu
    have e : (σ'.ρ.comp β.symm.toMulEquiv.toMonoidHom).comp β.toMulEquiv.toMonoidHom = σ'.ρ :=
      MonoidHom.ext fun g => congrArg σ'.ρ (β.symm_apply_apply g)
    rwa [e] at h3
  · intro x hx h
    have hx' : x ∈ locU a w := hU ▸ hx
    have hm : cLoc w x ∈ J := by
      rw [← hβ]
      exact h
    rw [hφ x hx' hm]
    have e : r ⟨cLoc (cpl w) x, h⟩ = ⟨cLoc w x, hm⟩ := Subtype.ext (hβ x)
    show _ = ((χ (θ (r ⟨cLoc (cpl w) x, h⟩)) : ℂˣ) : ℂ) • φ
    rw [e]
end

