module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeSignatureOnePreservesPosDefForm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.PositiveDefiniteFormIdentities

theorem form_pull {n : ℕ} (h Z : Matrix (Fin n) (Fin n) ℂ) (v v' : Fin n → ℂ) :
    star (Z *ᵥ v) ⬝ᵥ h *ᵥ (Z *ᵥ v') = star v ⬝ᵥ (Zᴴ * h * Z) *ᵥ v' := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem form_swap {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ Q *ᵥ x = star (star x ⬝ᵥ Q *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hQ.eq, ← dotProduct_mulVec]

theorem form_expand {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (w z : Fin n → ℂ) (a : ℂ)
    (hwz : star z ⬝ᵥ Q *ᵥ w = 0) :
    star (w + a • z) ⬝ᵥ Q *ᵥ (w + a • z) =
      star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * (star z ⬝ᵥ Q *ᵥ z) := by
  have hzw : star w ⬝ᵥ Q *ᵥ z = 0 := by rw [form_swap hQ, hwz, star_zero]
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hwz, hzw, smul_eq_mul, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
  ring

theorem form_self_ofReal {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x : Fin n → ℂ) :
    ((star x ⬝ᵥ Q *ᵥ x).re : ℂ) = star x ⬝ᵥ Q *ᵥ x := by
  have h := form_swap hQ x x
  exact Complex.conj_eq_iff_re.mp h.symm

end GlobalTheory.PositiveDefiniteFormIdentities

namespace GlobalTheory


open GlobalTheory.PositiveDefiniteFormIdentities in
theorem similitude_preserves_posDef : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  intro n h Q M hh Z s hdet hsig hQZ hs hsim z c hz hMz
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hQ : Q.IsHermitian := by
    rw [hQZ]
    simp [IsHermitian, conjTranspose_mul, hh.eq, Matrix.mul_assoc]
  set q0 : ℝ := (star z ⬝ᵥ Q *ᵥ z).re with hq0
  have hq : star z ⬝ᵥ Q *ᵥ z = (q0 : ℂ) := (form_self_ofReal hQ z).symm
  have hq0ne : (q0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  set u : Fin n → ℂ := Q *ᵥ z with hu
  set H : Matrix (Fin n) (Fin n) ℂ := ((2 / q0 : ℝ) : ℂ) • vecMulVec u (star u) - Q with hH
  have hsu : ∀ x : Fin n → ℂ, star u ⬝ᵥ x = star z ⬝ᵥ Q *ᵥ x := by
    intro x
    rw [hu, star_mulVec, ← dotProduct_mulVec, hQ.eq]
  have hus : ∀ x : Fin n → ℂ, star x ⬝ᵥ u = star (star z ⬝ᵥ Q *ᵥ x) := by
    intro x
    rw [hu, ← form_swap hQ]

  have hval : ∀ x : Fin n → ℂ, star x ⬝ᵥ H *ᵥ x =
      ((2 / q0 * Complex.normSq (star z ⬝ᵥ Q *ᵥ x) - (star x ⬝ᵥ Q *ᵥ x).re : ℝ) : ℂ) := by
    intro x
    rw [hH, sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, hsu, hus, smul_eq_mul, smul_eq_mul]
    have e := form_self_ofReal hQ x
    push_cast
    rw [e, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hHh : H.IsHermitian := by
    rw [hH]
    refine IsHermitian.sub ?_ hQ
    ext i j
    simp [vecMulVec_apply, mul_comm]
  have hpos : H.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hHh fun x hx => ?_
    rw [hval x]
    refine Complex.zero_lt_real.mpr ?_
    set p := star z ⬝ᵥ Q *ᵥ x with hp
    set a : ℂ := p / (q0 : ℂ) with ha
    have hpa : p = a * q0 := by rw [ha]; field_simp
    set w := x - a • z with hw
    have hxw : x = w + a • z := by rw [hw]; abel
    have hwz : star z ⬝ᵥ Q *ᵥ w = 0 := by
      rw [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hq, ← hp, hpa, sub_self]
    have hexp : star x ⬝ᵥ Q *ᵥ x = star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * q0 := by
      conv_lhs => rw [hxw]
      rw [form_expand hQ w z a hwz, hq]
    have hre : (star x ⬝ᵥ Q *ᵥ x).re = (star w ⬝ᵥ Q *ᵥ w).re + Complex.normSq a * q0 := by
      rw [hexp, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hnp : Complex.normSq p = Complex.normSq a * q0 ^ 2 := by
      rw [hpa, Complex.normSq_mul, Complex.normSq_ofReal]; ring
    have h2 : 2 / q0 * (Complex.normSq a * q0 ^ 2) = 2 * Complex.normSq a * q0 := by
      field_simp
    rw [hre, hnp, h2]
    by_cases hw0 : w = 0
    · have ha0 : a ≠ 0 := by
        intro ha0
        apply hx
        rw [hxw, hw0, ha0, zero_smul, add_zero]
      have e : (star w ⬝ᵥ Q *ᵥ w).re = 0 := by simp [hw0]
      rw [e]
      nlinarith [Complex.normSq_pos.mpr ha0]
    · have hZw : Zm *ᵥ w ≠ 0 := by
        intro h0
        apply hw0
        have hinv : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm = 1 := Units.inv_mul Z
        calc w = (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm) *ᵥ w := by rw [hinv, one_mulVec]
          _ = 0 := by rw [← mulVec_mulVec, h0, mulVec_zero]
      have hneg := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet hsig (Zm *ᵥ z) (Zm *ᵥ w)
        (by rw [form_pull, ← hQZ]; exact hz) (by rw [form_pull, ← hQZ]; exact hwz) hZw
      rw [form_pull, ← hQZ] at hneg
      nlinarith [Complex.normSq_nonneg a]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hc : star c * c = (s : ℂ) := by
    have e1 := congrArg (fun A => star z ⬝ᵥ A *ᵥ z) hsim
    rw [← form_pull Q M z z, hMz] at e1
    simp only [star_smul, mulVec_smul, smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e1
    rw [← hu, hq] at e1
    have e3 : (star c * c - s) * (q0 : ℂ) = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right hq0ne)
  have hMu : Mᴴ *ᵥ u = star c • u := by
    have e2 := congrArg (fun A => A *ᵥ z) hsim
    rw [← mulVec_mulVec, ← mulVec_mulVec, hMz, mulVec_smul, mulVec_smul, smul_mulVec, ← hu] at e2
    apply smul_right_injective _ hs0
    change (s : ℂ) • (Mᴴ *ᵥ u) = (s : ℂ) • (star c • u)
    calc (s : ℂ) • (Mᴴ *ᵥ u) = star c • (c • Mᴴ *ᵥ u) := by rw [smul_smul, hc]
      _ = star c • ((s : ℂ) • u) := by rw [e2]
      _ = (s : ℂ) • (star c • u) := smul_comm _ _ _
  have hstar : star u ᵥ* M = c • star u := by
    have e : star (Mᴴ *ᵥ u) = star u ᵥ* M := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [← e, hMu, star_smul, star_star]
  have hM1 : Mᴴ * vecMulVec u (star u) * M = (s : ℂ) • vecMulVec u (star u) := by
    rw [mul_vecMulVec, vecMulVec_mul, hMu, hstar, ← hc]
    ext i j
    simp [vecMulVec_apply]
    ring
  refine ⟨H, hpos, ?_⟩
  rw [hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hM1, hsim, smul_sub,
    smul_comm ((2 / q0 : ℝ) : ℂ) (s : ℂ)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixed
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix Filter Topology

noncomputable section

namespace GlobalTheory.CuspRep.TailFix

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem entry_int {w : HeightOneSpectrum (𝓞 E)} {g : GL (Fin a) (w.adicCompletion E)} (hg : g ∈ KGL w (n := a))
    (i j : Fin a) : g i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨h, rfl⟩ := hg
  exact (h i j).2

theorem tendsto_of_loc {α : Type} {l : Filter α} {f : α → Af E} {x : Af E}
    (hx : ∀ v, pLoc E v x ∈ v.adicCompletionIntegers E) (hf : ∀ b v, pLoc E v (f b) ∈ v.adicCompletionIntegers E)
    (h : ∀ v, ∀ᶠ b in l, pLoc E v (f b) = pLoc E v x) : Tendsto f l (𝓝 x) := by
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : ∀ y : Af E, (∀ v, pLoc E v y ∈ v.adicCompletionIntegers E) →
      ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletionIntegers E : Set (v.adicCompletion E)) :=
    fun y hy v => ⟨pLoc E v y, hy v⟩
  have hl : ∀ y hy, s (lift y hy) = y := fun y hy => FiniteAdeleRing.ext _ fun v => rfl
  have h1 : Tendsto (fun b => lift (f b) (hf b)) l (𝓝 (lift x hx)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| (h v).mono fun b hb => Subtype.ext hb.symm
  have h2 := (hs.tendsto _).comp h1
  rw [hl] at h2
  exact h2.congr fun b => hl _ _

theorem exists_tail {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 (1 : GL (Fin a) (Af E))) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 E)), ∀ r : GL (Fin a) (Af E),
      (∀ v, GeneralLinearGroup.map (pLoc E v) r ∈ KGL v (n := a)) →
      (∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) r = 1) → r ∈ U := by
  classical
  by_contra hn
  push_neg at hn
  choose r hr1 hr2 hrU using hn
  have ent : ∀ q : Finset (HeightOneSpectrum (𝓞 E)) → GL (Fin a) (Af E),
      (∀ F v, GeneralLinearGroup.map (pLoc E v) (q F) ∈ KGL v (n := a)) →
      (∀ F, ∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) (q F) = 1) →
      Tendsto (fun F => (q F).val) atTop (𝓝 1) := fun q hq1 hq2 =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (fun v => by rw [Matrix.one_apply]; split_ifs <;> simp)
        (fun F v => entry_int (hq1 F v) i j) fun v => by
        filter_upwards [eventually_ge_atTop {v}] with F hF
        have e := hq2 F v (hF (Finset.mem_singleton_self v))
        rw [← map_one (GeneralLinearGroup.map (pLoc E v))] at e
        exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) e
  have ht : Tendsto r atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent r hr1 hr2).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
      (ent (fun F => (r F)⁻¹) (fun F v => by rw [map_inv]; exact inv_mem (hr1 F v))
        (fun F v hv => by rw [map_inv, hr2 F v hv, inv_one])))
  obtain ⟨F, hF⟩ := (ht.eventually hU).exists
  exact hrU F hF

end GlobalTheory.CuspRep.TailFix


open GlobalTheory.CuspRep.TailFix in
theorem GlobalTheory.CuspRep.fixed_of_locFixed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)),
    (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E),
    (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) →
    (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  classical
  intro E _ _ _ a φ hφ S hS k hk1 hk2
  have hU : {x : GL (Fin a) (Af E) | finRep E a x φ = φ} ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
    hφ.level.mem_nhds (by simp)
  obtain ⟨F, hF⟩ := exists_tail hU
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) →
      (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∀ w ∈ F, w ∉ T → GeneralLinearGroup.map (pLoc E w) k = 1) → finRep E a k φ = φ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k h1 h2 h3
      refine hF k (fun v => ?_) (fun v hv => h3 v hv (by simp))
      by_cases hv : v ∈ S
      · rw [h2 v hv]; exact one_mem _
      · exact h1 v hv
    | insert w T hw ih =>
      intro k h1 h2 h3
      obtain ⟨g, hg⟩ : ∃ g, g = locGL E a w (GeneralLinearGroup.map (pLoc E w) k) := ⟨_, rfl⟩
      have hgH : finRep E a g φ = φ := by
        by_cases hwS : w ∈ S
        · rw [hg, h2 w hwS, map_one, map_one]; rfl
        · rw [hg]; exact hS w hwS _ (h1 w hwS)
      have e : ∀ v, GeneralLinearGroup.map (pLoc E v) (g⁻¹ * k) =
          if v = w then 1 else GeneralLinearGroup.map (pLoc E v) k := fun v => by
        rw [map_mul, map_inv]
        split_ifs with hv
        · subst hv; rw [hg, pLoc_locGL, inv_mul_cancel]
        · rw [hg, pLoc_locGL_of_ne hv, inv_one, one_mul]
      have hk' : finRep E a (g⁻¹ * k) φ = φ := by
        refine ih _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv hvT => ?_)
        · rw [e]; split_ifs
          · exact one_mem _
          · exact h1 v hv
        · rw [e]; split_ifs
          · rfl
          · exact h2 v hv
        · rw [e]; split_ifs with h
          · rfl
          · exact h3 v hv (by simp [h, hvT])
      calc finRep E a k φ = finRep E a (g * (g⁻¹ * k)) φ := by rw [mul_inv_cancel_left]
        _ = φ := by rw [map_mul, Module.End.mul_apply, hk', hgH]
  exact key F k hk1 hk2 (fun w hw hwF => absurd hw hwF)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SplitFullyNorm

theorem exists_prime_absNorm_eq_of_splitsFully (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (W : HeightOneSpectrum (𝓞 E)) (h : SplitsFully E (W.under (𝓞 F))) :
    ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  classical

  set P : Ideal ℤ := W.asIdeal.under ℤ with hPdef
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot W.ne_bot
  haveI hPprime : P.IsPrime := Ideal.IsPrime.under ℤ W.asIdeal
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0

  have hunder : (W.under (𝓞 F)).asIdeal.under ℤ = P := by
    change (W.asIdeal.under (𝓞 F)).under ℤ = W.asIdeal.under ℤ
    exact Ideal.under_under _
  have hcard : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
    have h' := h
    unfold SplitsFully at h'
    rwa [hunder] at h'

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum

  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    intro q
    haveI : q.1.IsPrime := q.2.1
    have hpos := Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) q.1) (Ideal.inertiaDeg_pos q.1 ℤ)
    by_contra hne
    have hlt : ∑ _r : P.primesOver (𝓞 E), (1 : ℕ) <
        ∑ r : P.primesOver (𝓞 E), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
      apply Finset.sum_lt_sum
      · intro r _
        haveI : r.1.IsPrime := r.2.1
        exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) r.1) (Ideal.inertiaDeg_pos r.1 ℤ)
      · exact ⟨q, Finset.mem_univ _, by omega⟩
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_eq_nat_card,
      Nat.card_coe_set_eq, hcard] at hlt
    exact lt_irrefl _ hlt
  have hWmem : W.asIdeal ∈ P.primesOver (𝓞 E) := ⟨W.isPrime, ⟨rfl⟩⟩
  have hw := hone ⟨W.asIdeal, hWmem⟩
  have he : W.asIdeal.ramificationIdx ℤ = 1 := Nat.eq_one_of_mul_eq_one_right hw
  have hf : W.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left hw

  set n : ℕ := (Submodule.IsPrincipal.generator P).natAbs with hn
  have hspan : Ideal.span {((n : ℕ) : ℤ)} = P := by
    rw [hn, Int.span_natAbs, Ideal.span_singleton_generator]
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply hP0
    rw [← hspan, h0, Ideal.span_singleton_eq_bot]
  have hnprime : n.Prime := by
    rw [Nat.prime_iff_prime_int, ← Ideal.span_singleton_prime hn0, hspan]
    exact hPprime
  haveI : W.asIdeal.LiesOver (Ideal.span {((n : ℕ) : ℤ)}) := ⟨by rw [hspan]⟩
  refine ⟨n, hnprime, ?_, ?_⟩
  ·
    rw [← Ideal.pow_inertiaDeg n W.asIdeal, hf, pow_one]
  ·
    intro hmem
    have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ W.asIdeal ^ 2 := by
      rw [← hspan, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    have hdvd : W.asIdeal ^ 2 ∣ P.map (algebraMap ℤ (𝓞 E)) := Ideal.dvd_iff_le.mpr hle
    have hfin : FiniteMultiplicity W.asIdeal (P.map (algebraMap ℤ (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact W.isPrime.ne_top) hmap0
    have h2 := hfin.le_multiplicity_of_pow_dvd hdvd
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P W.asIdeal hmap0, he] at h2
    omega

end GlobalTheory.SplitFullyNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem grp_similitude_herm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : grp G β), ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ))ᴴ * herm G v β *
      (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) = (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β := by
  intro p _ G v β y
  obtain ⟨⟨u, s⟩, hy, _⟩ := y
  change (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β at hy
  have hV : ((toV G v β ⟨(u, s), hy, ‹_›⟩ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (u : G.C) := rfl
  rw [hV]
  change (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
    ((s : ℚ) : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C))
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hu : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u =
      algebraMap ℚ G.C (s : ℚ) * ((β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (u * β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (u : G.C) * β * (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u)
        = ((u : G.C) * β * sh G (u : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) * u := by
          simp only [mul_assoc]
      _ = (s : ℚ) • ((β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
          rw [hy, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (s : ℚ) • ((u : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (u : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v (u : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((s : ℚ) : ℚ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationQuaternionNormOneSplit
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem isPlacesIdem_mul_self {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  have h1 : fstA F (ε * ε) = fstA F ε := by
    rw [map_mul]
    funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [hε.1 w hw, one_mul]
    · rw [hε.2.1 w hw, zero_mul]
  have h2 : sndA F (ε * ε) = sndA F ε := by
    rw [map_mul]
    refine RestrictedProduct.ext _ _ fun v => ?_
    change evalV F v (sndA F ε * sndA F ε) = evalV F v (sndA F ε)
    rw [map_mul]
    by_cases hv : v ∈ S₂
    · rw [hε.2.2.1 v hv, one_mul]
    · rw [hε.2.2.2 v hv, zero_mul]
  exact Prod.ext h1 h2

theorem strongApprox_nrm_one : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∃ p q : AF F, ε * (algebraMap F (AF F) b - (p ^ 2 - algebraMap F (AF F) a * q ^ 2)) = 0) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb S₁ S₂ ε hε hS hpq g hg
  by_cases hiso : ∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0
  · exact GlobalTheory.T.strongApproximation_normOne_splitQuaternionAlgebra F a b ha hb hiso S₁ S₂ ε hε hS g hg
  · have hdiv : ∀ x : ℍ[F, a, b], nrm x = 0 → x = 0 := fun x hx =>
      by_contra fun h => hiso ⟨x, h, hx⟩
    obtain ⟨p, q, hpq⟩ := hpq
    refine GlobalTheory.T.mem_closure_normOne_of_strongApproximation F a b ha hb hdiv S₁ S₂ ε hε hS (fun t => ?_) g hg
    have h2 : IsUnit (2 : AF F) := by
      have : IsUnit (algebraMap F (AF F) 2) := (IsUnit.mk0 (2 : F) two_ne_zero).map _
      rwa [map_ofNat] at this
    exact _root_.GlobalTheory.quat_norm_one_re_at_idem (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b) ε p q
      (isPlacesIdem_mul_self hε) ((IsUnit.mk0 a ha).map _) ((IsUnit.mk0 b hb).map _) h2 hpq t

end GlobalTheory.QSA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPartFibreLieAlgebraCharactersStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_part_fibre_lie_algebra_characters : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (E : TorusExtension ((Over.pullback x).obj G)), letI := E.addCommGroup; ∃ (ρ : O →+* Module.End ℤ E.X) (U : (E.X →+ k) → (epsPt x ⟶ G)), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk x ⟶ G).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ a l, U l ≫ act a = U (l.comp (ρ a).toAddMonoidHom) := by
  first | exact @GlobalTheory.torus_part_lie | exact GlobalTheory.torus_part_lie | (intros; apply GlobalTheory.torus_part_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompactStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHeckeTestFunction_support_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  first | (exact @GlobalTheory.isTest_support_compact) | (exact GlobalTheory.isTest_support_compact) | (intros; apply GlobalTheory.isTest_support_compact  <;> assumption)
end

