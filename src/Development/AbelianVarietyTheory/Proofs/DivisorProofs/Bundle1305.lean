module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTwConjMemCentMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStableCharacterFlagOfCharpolyFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingActionCommutesTranslation
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertUniq

section Fixed
variable {L : Type} [Field L]

abbrev fixF (σ : L →+* L) : Subfield L := σ.eqLocusField (RingHom.id L)

abbrev starOfInv (σ : L →+* L) (h : ∀ x, σ (σ x) = x) : StarRing L where
  star := σ
  star_involutive := h
  star_mul x y := by rw [map_mul]; exact mul_comm _ _
  star_add := map_add σ

theorem finrank_fixF (σ : L →+* L) (h : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Module.finrank (fixF σ) L = 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hd : x₀ - σ x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hx₀)
  have hli : LinearIndependent (fixF σ) ![(1 : L), x₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : σ (s : L) = s := s.2
    have ht : σ (t : L) = t := t.2
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    change (s : L) + (t : L) * x₀ = 0 at hst
    have h2 : (s : L) + (t : L) * σ x₀ = 0 := by
      have := congrArg σ hst
      rwa [map_add, map_mul, hs, ht, map_zero] at this
    have ht0 : (t : L) = 0 := by
      have : (t : L) * (x₀ - σ x₀) = 0 := by linear_combination hst - h2
      exact (mul_eq_zero.1 this).resolve_right hd
    refine ⟨Subtype.ext ?_, Subtype.ext ht0⟩
    simpa [ht0] using hst
  have hsp : ⊤ ≤ Submodule.span (fixF σ) (Set.range ![(1 : L), x₀]) := by
    intro y _
    set b := (y - σ y) / (x₀ - σ x₀) with hbdef
    have hb : σ b = b := by
      rw [hbdef, map_div₀, map_sub, map_sub, h, h, ← neg_sub y (σ y), ← neg_sub x₀ (σ x₀), neg_div_neg_eq]
    set a := y - b * x₀ with hadef
    have hbm : b * (x₀ - σ x₀) = y - σ y := div_mul_cancel₀ _ hd
    have ha : σ a = a := by
      rw [hadef, map_sub, map_mul, hb]
      linear_combination hbm
    have hy : y = (⟨a, ha⟩ : fixF σ) • (1 : L) + (⟨b, hb⟩ : fixF σ) • x₀ := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change y = a * 1 + b * x₀
      rw [hadef]; ring
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
  simp

end Fixed

theorem eq_twCent_mul_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  intro E _ _ _ hU n w hs y g hy hbez hyg
  obtain ⟨hc, hinv, hval, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨-, ⟨ϖ, q, hϖ, -⟩, -⟩ := hns hs
  obtain ⟨-, -, hϖf, hϖv, ⟨x₀, -, hx₀⟩, -⟩ := hϖ
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  letI : StarRing (w.adicCompletion E) := starOfInv (cj w) hinv
  have hle1 : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  have hneq : ∀ x y : w.adicCompletion E, Valued.v x = Valued.v y → ‖x‖ = ‖y‖ := fun x y h =>
    le_antisymm (Valued.toNormedField.norm_le_iff.2 h.le) (Valued.toNormedField.norm_le_iff.2 h.ge)
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖi : cj w ϖ⁻¹ = ϖ⁻¹ := by rw [map_inv₀, hϖf]
  have hϖn : 1 < ‖ϖ⁻¹‖ := by
    rw [Valued.toNormedField.one_lt_norm_iff, map_inv₀, hϖv]
    exact one_lt_inv₀ (by simp) |>.2 (by rw [← WithZero.coe_one, WithZero.coe_lt_coe]; decide)
  letI nF : NontriviallyNormedField (fixF (cj w)) :=
    { (inferInstance : NormedField (fixF (cj w))) with non_trivial := ⟨⟨ϖ⁻¹, hϖi⟩, hϖn⟩ }
  letI : NormedAlgebra (fixF (cj w)) (w.adicCompletion E) :=
    { (inferInstance : Algebra (fixF (cj w)) (w.adicCompletion E)) with
      norm_smul_le := fun r x => by rw [Algebra.smul_def, norm_mul]; exact le_of_eq rfl }
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI hUn : GlobalTheory.JR.Unram (fixF (cj w)) (w.adicCompletion E) :=
    { charZero := ⟨fun a b h => Nat.cast_injective (R := w.adicCompletion E) (by simpa using congrArg (algebraMap (fixF (cj w)) (w.adicCompletion E)) h)⟩
      ultraF := inferInstance
      ultraE := inferInstance
      lcF := (isClosed_eq hc continuous_id).isClosedEmbedding_subtypeVal.locallyCompactSpace
      lcE := inferInstance
      finrank_eq := finrank_fixF (cj w) hinv ⟨x₀, fun h => by rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      star_fix := fun x => x.2
      star_ne := ⟨x₀, fun h => by change cj w x₀ = x₀ at h; rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      norm_star := fun x => hneq _ _ (hval x)
      unram := by
        intro x
        by_cases hx : x = 0
        · exact ⟨0, by rw [hx]; rfl⟩
        · have hv0 : Valued.v x ≠ 0 := by simpa using hx
          refine ⟨⟨ϖ ^ (-WithZero.log (Valued.v x)), by
            change cj w (ϖ ^ (-WithZero.log (Valued.v x))) = ϖ ^ (-WithZero.log (Valued.v x)); rw [map_zpow₀, hϖf]⟩, ?_⟩
          change ‖x‖ = ‖ϖ ^ (-WithZero.log (Valued.v x))‖
          apply hneq
          rw [map_zpow₀, hϖv, show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) from rfl,
            ← WithZero.exp_zsmul, smul_eq_mul, neg_mul_neg, mul_one, WithZero.exp_log hv0] }
  have hcs : cj w = starRingEnd (w.adicCompletion E) := RingHom.ext fun _ => rfl
  have hth : ∀ h : GLw n w, (thL n w h).val = GlobalTheory.Tw.theta h.val := by
    intro h
    rw [thL, if_neg hs, hcs, thetaGL_val]
  have hnr : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
    rw [nrmL, if_neg hs, Units.val_mul, hcs, thetaGL_val]; rfl

  have hmem (O : Subring (w.adicCompletion E)) (h : GLw n w) :
      h ∈ GLint (Fin n) O ↔
        (∀ i j, h.val i j ∈ O) ∧ ∀ i j, (h⁻¹).val i j ∈ O := by
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
      Matrix.map_injective Subtype.val_injective
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
      · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact h.mul_inv
      · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact h.inv_mul
  have hint : ∀ h : GLw n w, h ∈ GlobalTheory.LFun.KGL w (n := n) → (∀ i j, ‖h.val i j‖ ≤ 1) ∧ ‖h.val.det‖ = 1 := by
    intro h hh
    obtain ⟨h1, h2⟩ := (hmem (Ov E w) h).1 hh
    have hdet : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ i j, M i j ∈ Ov E w) → M.det ∈ Ov E w := by
      intro M hM
      let M₀ : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨M i j, hM i j⟩
      have hM₀ : M = (Ov E w).subtype.mapMatrix M₀ := by ext i j; rfl
      rw [hM₀, ← RingHom.map_det]
      exact (M₀.det).2
    have d1 : ‖h.val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h1)
    have d2 : ‖(h⁻¹).val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h2)
    have hprod : ‖h.val.det‖ * ‖(h⁻¹).val.det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
    refine ⟨fun i j => (hle1 _).2 (h1 i j), ?_⟩
    nlinarith [norm_nonneg h.val.det, norm_nonneg (h⁻¹).val.det]
  have hintR : ∀ h : GLw n w, (∀ i j, ‖h.val i j‖ ≤ 1) → ‖h.val.det‖ = 1 → h ∈ GlobalTheory.LFun.KGL w (n := n) := by
    intro h h1 h2
    refine (hmem (Ov E w) h).2 ⟨fun i j => (hle1 _).1 (h1 i j), fun i j => ?_⟩
    rw [Matrix.coe_units_inv]
    exact (hle1 _).1 (GlobalTheory.TwIntegral.intg_inv h1 h2 i j)
  obtain ⟨hy1, hy2⟩ := hint y hy
  obtain ⟨hg1, hg2⟩ := hint _ hyg
  have htw : GlobalTheory.Tw.twConj g.val y.val = (g⁻¹ * y * thL n w g).val := by
    rw [Units.val_mul, Units.val_mul, hth, Matrix.coe_units_inv]; rfl
  obtain ⟨u, v, hu, hv, huv⟩ := hbez
  rw [hnr] at huv
  obtain ⟨t, ⟨htu, htc⟩, k, hk1, hk2, hx⟩ := GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul (fixF (cj w)) (w.adicCompletion E) n
    y.val g.val hy1 hy2 ⟨u, v, fun i => (hle1 _).2 (hu i), fun i => (hle1 _).2 (hv i), huv⟩ g.isUnit
    (by rw [htw]; exact hg1) (by rw [htw]; exact hg2)
  have hku : IsUnit k := GlobalTheory.TwIntegral.isUnit_of_norm_det hk2
  refine ⟨htu.unit, ?_, hku.unit, hintR _ (by simpa using hk1) (by simpa using hk2), Units.ext ?_⟩
  · show htu.unit * y = y * thL n w htu.unit
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hth, IsUnit.unit_spec]
    exact htc
  · rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
    exact hx

end GlobalTheory.InertUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPair
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.WachBlock

theorem integralBlock_of_blockPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  intro E Ω _ _ _ _ _ l _ n t J bot hB
  obtain ⟨r, a, ρ, χ, hat, hr, hρ, hχ, hcong⟩ := hB
  obtain ⟨LL, hζ, hτ, hrL, hρL, hχL⟩ := _root_.GlobalTheory.RepFinExtJoint.finext_joint E Ω l n a t r ρ χ hr.1 hρ (fun s => (hχ s).1)
  obtain ⟨A, hA1, hA2, hAr⟩ := _root_.GlobalTheory.GalIntegral.exists_conj_integral E Ω l n LL r hr.1 hrL
  obtain ⟨B, hB1, hB2, hBρ⟩ := _root_.GlobalTheory.GalIntegral.exists_conj_integral E Ω l a LL ρ hρ hρL
  have memLL : ∀ {m : ℕ} (X Y Z : Matrix (Fin m) (Fin m) (PadicAlgCl l)), (∀ i j, X i j ∈ LL.1) →
      (∀ i j, Y i j ∈ LL.1) → (∀ i j, Z i j ∈ LL.1) → ∀ i j, (X * Y * Z) i j ∈ LL.1 := by
    intro m X Y Z hX hY hZ i j
    simp only [Matrix.mul_apply]
    exact LL.1.sum_mem fun k _ => LL.1.mul_mem (LL.1.sum_mem fun k' _ => LL.1.mul_mem (hX _ _) (hY _ _)) (hZ _ _)
  have cj : ∀ {m : ℕ} (C : GL (Fin m) (PadicAlgCl l)) (x : GL (Fin m) (PadicAlgCl l)),
      (((MulAut.conj C⁻¹).toMonoidHom x : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) =
        ((C⁻¹ * x * C : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) := by
    intro m C x
    simp [MulAut.conj_apply]
  obtain ⟨r', hr'⟩ := (GlobalTheory.IntDescend.descend l LL (G E Ω)).1 n ((MulAut.conj A⁻¹).toMonoidHom.comp r) (fun g i j => by
    rw [MonoidHom.comp_apply, cj]
    refine ⟨?_, hAr g i j⟩
    simpa [Units.val_mul] using memLL _ _ _ hA2 (hrL g) hA1 i j)
  obtain ⟨ρ', hρ'⟩ := (GlobalTheory.IntDescend.descend l LL (G E Ω)).1 a ((MulAut.conj B⁻¹).toMonoidHom.comp ρ) (fun g i j => by
    rw [MonoidHom.comp_apply, cj]
    refine ⟨?_, hBρ g i j⟩
    simpa [Units.val_mul] using memLL _ _ _ hB2 (hρL g) hB1 i j)
  choose ψ hψ using fun s => (GlobalTheory.IntDescend.descend l LL (G E Ω)).2 (χ s) (fun g => ⟨hχL s g, _root_.GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one E Ω l (χ s) (hχ s).1 g⟩)
  haveI : IsDiscreteValuationRing ↥(OL LL) := Examples₂.LB.OL_dvr LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hmat : ∀ g, (r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).map (GlobalTheory.WachBlock.ofOL l LL) =
      ((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
    intro g
    rw [← cj]
    exact congrArg (fun f : G E Ω →* GL (Fin n) (PadicAlgCl l) => ((f g : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l))) hr'
  have hmatρ : ∀ g, (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).map (GlobalTheory.WachBlock.ofOL l LL) =
      ((B⁻¹ * ρ g * B : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
    intro g
    rw [← cj]
    exact congrArg (fun f : G E Ω →* GL (Fin a) (PadicAlgCl l) => ((f g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) hρ'
  have hψv : ∀ s g, GlobalTheory.WachBlock.ofOL l LL ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) = ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    intro s g
    exact congrArg (fun f : G E Ω →* (PadicAlgCl l)ˣ => ((f g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) (hψ s)
  have hcp : ∀ {m : ℕ} (C : GL (Fin m) (PadicAlgCl l)) (N : Matrix (Fin m) (Fin m) (PadicAlgCl l)),
      (((C⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) * N * (C : Matrix (Fin m) (Fin m) (PadicAlgCl l))).charpoly = N.charpoly := by
    intro m C N
    simpa using Matrix.charpoly_units_conj C⁻¹ N
  have hc : ∀ g m, ((r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).charpoly - (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).charpoly *
      ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)))).coeff m ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    intro g m
    rw [GlobalTheory.IntMaxFinExt.mem_maximalIdeal_iff_norm_lt_one]
    have e : GlobalTheory.WachBlock.ofOL l LL (((r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).charpoly - (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).charpoly *
      ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)))).coeff m) =
        ((r g).val.charpoly - (ρ g).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l))).coeff m := by
      rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map,
        ← Matrix.charpoly_map, hmat, hmatρ]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hψv, Units.val_mul]
      rw [hcp, hcp]
    have h := hcong g m
    rw [← e] at h
    exact h
  obtain ⟨R, M, rs, hM0, hML, hMm, hMs, hrs, hline⟩ := GlobalTheory.integral_flag_lift_of_residue ↥(OL LL) (G E Ω) n a t r' ρ' ψ ϖ hϖ hat hc _root_.GlobalTheory.CharFlag.main
  refine ⟨LL, r', ψ, ϖ, R, M, rs, hζ, hτ, ?_, fun s => ?_, hϖ, hM0, hML, hMm, hMs, hrs, hline⟩
  · have : (Matrix.GeneralLinearGroup.map (GlobalTheory.WachBlock.ofOL l LL)).comp r' = (MulAut.conj A⁻¹).toMonoidHom.comp r := hr'
    rw [this]
    exact GlobalTheory.crysWith_conj E Ω l n r A LL _ (fun i j => ⟨hA1 i j, hA2 i j⟩) hr
  · have : (Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp (ψ s) = χ s := hψ s
    rw [this]
    exact hχ s

end GlobalTheory.WachBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPolarisedTopFormDbarExactEqZero
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integral_mixTop_mdbar_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (θ : Fin n → Fin n → V n → Matrix r r ℂ) (j : Fin n) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v) → (∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ∀ a p q, ‖θ j a v p q‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q, ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ c) → IntegrableOn (fun v => mixTop fun i a b => mdbar (θ i a) v (coordVec b)) (offHyp S U) ∧ ∫ v in offHyp S U, (mixTop fun i a b => mdbar (θ i a) v (coordVec b)) = 0 := by
  intro n r _ _ S U K θ j c hU hK hKU hS hθ h0 hb hd
  have key : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      IntegrableOn (fun v => (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det = 0 := by
    intro p π u
    exact _root_.GlobalTheory.GoodTop.integral_det_dbar_eq_zero_of_poincare S U K (fun i x => θ i (u i) x (p i) (p (π i))) j u c hU hK hKU hS
      (fun i v hv => (hθ i (u i) v hv (p i) (p (π i))).contDiffWithinAt)
      (fun v hv hvK => by simp [h0 (u j) v hv hvK])
      (fun v hv hvK => hb v hv hvK (u j) _ _)
      (fun v hv hvK i b => hd v hv hvK i (u i) b (p i) (p (π i)))
  have hI : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      Integrable (fun v => ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π u => Integrable.const_mul (key p π u).1 _
  have hI2 : ∀ (p : Fin n → r) (π : Equiv.Perm (Fin n)),
      Integrable (fun v => ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π => integrable_finsetSum _ fun u _ => hI p π u
  have hI3 : ∀ (p : Fin n → r),
      Integrable (fun v => ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p => integrable_finsetSum _ fun π _ => hI2 p π
  unfold mixTop
  refine ⟨Integrable.const_mul (integrable_finsetSum _ fun p _ => hI3 p) _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun p _ => hI3 p]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => ?_)
  rw [integral_finsetSum _ fun π _ => hI2 p π]
  refine Finset.sum_eq_zero fun π _ => ?_
  rw [integral_finsetSum _ fun u _ => hI p π u]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [integral_const_mul, (key p π u).2, mul_zero]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTwoSmulMemAdelicLatticeAtFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d)
    (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ z ∈ GlobalTheory.InertSph.latAt W v, (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertSph.invTwo_smul_mem_latAt | exact GlobalTheory.InertSph.invTwo_smul_mem_latAt | (intros; apply GlobalTheory.InertSph.invTwo_smul_mem_latAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreduciblePencilLinePolynomialGenericLineStatement
section
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line : ∀ (F : Type) [Field F] (D N : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), Irreducible f → Irreducible (GlobalTheory.PencilDisc.line (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F)) (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  first | exact @GlobalTheory.PencilDisc.irreducible_line_generic | exact GlobalTheory.PencilDisc.irreducible_line_generic | (intros; apply GlobalTheory.PencilDisc.irreducible_line_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutOfMemAutForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UAut GlobalTheory.Mem.Th GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem isSm_of_smF (hθ : IsInfFam θ) (R : RealPoints θ V) (f : SmF θ V) : IsSm D.sp.cm.sig V.gram f.1 := by
  intro k γ hγ g
  choose p hp e using fun i => (hγ i).eq_oneP hθ
  simpa only [e] using (smooth_iff R f.1).2 f.2 k (fun i => (p i).1) (fun i => (p i).2) hp g

theorem exists_word (hθ : IsInfFam θ) (R : RealPoints θ V) (l : List (ℝ → GA D V))
    (hl : ∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ w : GlobalTheory.AutFinLit.Env V, ∀ f : SmF θ V, l.foldr lineDer f.1 = (envRepAll R w f).1 := by
  classical
  induction l with
  | nil => exact ⟨1, fun f => by rw [map_one]; rfl⟩
  | cons γ l ih =>
    obtain ⟨w, hw⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    obtain ⟨⟨τ, X⟩, hX, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
    refine ⟨UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] ⟨X, hX⟩)) * w,
      fun f => ?_⟩
    rw [map_mul, Module.End.mul_apply, ← envIncl_ι, envRepAll_envIncl, envRep_ι, opInf_coe, ← hw, List.foldr_cons]
    exact Rder_eq R τ ⟨X, hX⟩ _

theorem exists_env (hθ : IsInfFam θ) (R : RealPoints θ V) (z : List (ℝ → GA D V) →₀ ℂ)
    (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ u : GlobalTheory.AutFinLit.Env V, ∀ f : SmF θ V, dop z f.1 = (envRepAll R u f).1 := by
  classical
  choose! w hw using fun l (hl : l ∈ z.support) => exists_word hθ R l (hz l hl)
  refine ⟨∑ l ∈ z.support, z l • w l, fun f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply, Submodule.coe_sum]
  funext g
  simp only [dop, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← hw l hl]

theorem mem_center_of_comm (u : GlobalTheory.AutFinLit.Env V)
    (h : ∀ x, UniversalEnvelopingAlgebra.ι ℂ x * u = u * UniversalEnvelopingAlgebra.ι ℂ x) :
    u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (GlobalTheory.AutFinLit.LieC V)) := by
    unfold UniversalEnvelopingAlgebra.mkAlgHom
    first | exact RingCon.mkₐ_surjective _ _ | exact RingCon.mkₐ_surjective _ | exact fun b => Quotient.inductionOn' b fun t => ⟨t, rfl⟩ | exact Quot.mk_surjective
  obtain ⟨t, rfl⟩ := hs b
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r u
  | ι x => exact h x
  | mul a b ha hb => rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [map_add (f := _), add_mul, mul_add, ha, hb]

theorem mem_of_mem_center (R : RealPoints θ V) {W : Submodule ℂ (GA D V → ℂ)}
    (hs : ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) {u : GlobalTheory.AutFinLit.Env V}
    (hu : u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V)) : ∀ f : SmF θ V, f.1 ∈ W → (envRepAll R u f).1 ∈ W := by
  classical
  choose c hc hg using exists_gelf R
  have hloc : ∀ τ, ∀ z ∈ Subalgebra.center ℂ (EnvAt V τ), ∀ f : SmF θ V, f.1 ∈ W → (envRep R τ z f).1 ∈ W := by
    intro τ z hz
    rw [hc τ] at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; intro f hf; rw [← hg]; exact hs τ k _ hf
    | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
    | add x y _ _ hx hy => intro f hf; simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using add_mem (hx f hf) (hy f hf)
    | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)
  rw [GlobalTheory.EnvCentre.center_directSum D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) (fun τ => envIncl V τ)
    (fun τ x => envIncl_ι τ x)] at hu
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, z, hz, rfl⟩ := Set.mem_iUnion.1 hx |>.imp fun τ h => h
    intro f hf; rw [envRepAll_envIncl]; exact hloc τ z hz f hf
  | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
  | add x y _ _ hx hy => intro f hf; simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using add_mem (hx f hf) (hy f hf)
  | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)

theorem exists_center (hθ : IsInfFam θ) (R : RealPoints θ V) {z : List (ℝ → GA D V) →₀ ℂ}
    (hz : IsCentral D.sp.cm.sig V.gram z) :
    ∃ u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V), ∀ f : SmF θ V, dop z f.1 = (envRepAll R u f).1 := by
  obtain ⟨u, hu⟩ := exists_env hθ R z hz.1
  refine ⟨u, mem_center_of_comm u fun x => GlobalTheory.T.enveloping_representation_injective _ _ hθ V R ?_, hu⟩
  rw [map_mul, map_mul]
  refine _root_.GlobalTheory.EnvCommLie.envRepAll_comm_lie _ _ hθ V R u (fun a ha f hfa => ?_) x
  rw [← hu, ← hu]
  funext g
  exact hz.2 f.1 (isSm_of_smF hθ R f) a ha g

end GlobalTheory.CentralOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalIsomorphismScalars
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolIso

theorem modelI_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Λ : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ W.J) : M.I om (Λ • Φ) h = Λ * M.I om Φ h := by
  unfold Model.I theta thetaSum
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext g
  exact tsum_mul_left

end GlobalTheory.PolIso
end

