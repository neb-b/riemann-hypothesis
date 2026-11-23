module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadTorsorToEtaleAlgebraStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spread_torsor_to_etale_algebra : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.LocAcyc.spread_torsor_to_etale) | (exact GlobalTheory.LocAcyc.spread_torsor_to_etale) | (intros; apply GlobalTheory.LocAcyc.spread_torsor_to_etale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNonzeroIntegersPrincipalIdealsUnits
section
open NumberField MeasureTheory

namespace GlobalTheory

theorem sum_over_principal_ideals_units (K : Type) [Field K] [NumberField K] (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : 𝓞 K → E) : f 0 = 0 → ∀ (c : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → E) (β : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → (𝓞 K)ˣ → ℝ) (b : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → ℝ), (∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, HasSum (fun u : (𝓞 K)ˣ => f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))) (c J)) → (∀ (J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}) (u : (𝓞 K)ˣ), ‖f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))‖ ≤ β J u) → (∀ J, HasSum (β J) (b J)) → Summable b → HasSum f (∑' J, c J) := by
  intro hf0 c β b hc hbd hβ hbs
  classical
  let gen : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → 𝓞 K := fun J => haveI := J.2.2; Submodule.IsPrincipal.generator J.1
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {gen J} = J.1 := fun J => by
    haveI := J.2.2
    exact Submodule.IsPrincipal.span_singleton_generator J.1
  have hgen0 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, gen J ≠ 0 := fun J => by
    intro h
    apply J.2.1
    rw [← hspan J, h, Ideal.span_singleton_eq_bot]
  let g : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) → 𝓞 K := fun p => (p.2 : 𝓞 K) * gen p.1
  have hginj : Function.Injective g := by
    rintro ⟨J, u⟩ ⟨J', u'⟩ h
    simp only [g] at h
    have hJ : J = J' := by
      apply Subtype.ext
      rw [← hspan J, ← hspan J', Ideal.span_singleton_eq_span_singleton]
      have h1 : gen J = ((u⁻¹ * u' : (𝓞 K)ˣ) : 𝓞 K) * gen J' := by
        rw [Units.val_mul, mul_assoc, ← h, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      rw [h1]
      exact (associated_unit_mul_left _ _ (Units.isUnit _))
    subst hJ
    have hu : u = u' := Units.ext (mul_right_cancel₀ (hgen0 J) h)
    subst hu
    rfl
  have hrange : ∀ x ∉ Set.range g, f x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, hf0]
    · exfalso
      apply hx
      let J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} := ⟨Ideal.span {x}, by rwa [Ne, Ideal.span_singleton_eq_bot], ⟨⟨x, rfl⟩⟩⟩
      have hass : Associated (gen J) x := by
        rw [← Ideal.span_singleton_eq_span_singleton, hspan J]
      obtain ⟨u, hu⟩ := hass
      exact ⟨⟨J, u⟩, by simp only [g]; rw [mul_comm]; exact hu⟩
  have hnorm : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => β p.1 p.2) := by
    rw [summable_sigma_of_nonneg]
    · refine ⟨fun J => (hβ J).summable, ?_⟩
      simpa [(hβ _).tsum_eq] using hbs
    · intro p
      exact (norm_nonneg _).trans (hbd p.1 p.2)
  have hF : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => f (g p)) :=
    Summable.of_norm_bounded hnorm (fun p => hbd p.1 p.2)
  have hcs : HasSum c (∑' p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ), f (g p)) :=
    HasSum.sigma hF.hasSum (fun J => hc J)
  rw [hcs.tsum_eq]
  exact (hginj.hasSum_iff hrange).mp hF.hasSum
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionUnitClass
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUnit

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  exact this.symm

theorem res_resGen {q : ℕ} [NeZero q] (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  unfold resGen
  rw [res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ]

theorem val_one_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (y : M) :
    (1 : ZMod q).val • y = y := by
  by_cases hq : q = 1
  · subst hq
    have : Subsingleton M := Module.subsingleton (ULift.{1} (ZMod 1)) M
    exact Subsingleton.elim _ _
  · haveI : Fact (1 < q) := ⟨by have := NeZero.ne q; omega⟩
    rw [ZMod.val_one, one_smul]

theorem resGen_zero_eq {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) : resGen 0 ζ = resGen 0 ξ := by
  apply (_root_.GlobalTheory.EtC.sec_ext_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.1 ζ ξ
  refine ⟨S, hS, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP W h hh
  rw [res_resGen, res_resGen]
  have := (GlobalTheory.T.tateTwist_sections_locally_generated q 0).2.2.2.2.1 W (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha
  unfold resGen
  rw [this, zpow_zero, Units.val_one, val_one_smul]

end GlobalTheory.EtC.RedUnit

theorem GlobalTheory.EtC.red_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  intro Q q _ hqQ E hE
  haveI : NeZero q := ⟨fun h => by subst h; exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)⟩
  have hEq : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨α, hα1, hα2⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec Q).1 E hE
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).1 E 0 α
  have hred : red Q q E 0 0 (one Q E) = CohomologyClass.mk β := by
    rw [← hα1]; exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).2 E 0 α β hβ
  rw [hred]
  refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 E hEq β fun U x ξ => ?_
  apply (_root_.GlobalTheory.EtC.sec_ext_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  obtain ⟨ξ', hξ'⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(V, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1 0 0 _ V U g x, hβ 0 0 _ V (x.res g), hα2 V (x.res g) ζ,
    GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 0 V ζ ξ' hξ', RedUnit.res_resGen]
  exact RedUnit.resGen_zero_eq _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementConjugatedByFrameMemSpecialUnitary
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TorusFrame

theorem sum_angles {r : ℕ} (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ (Fin.castSucc i) = φ ⟨i, by simpa using i.isLt⟩ := by
      intro i; unfold angles; rw [dite_eq_left (by simpa using i.isLt)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dite_eq_right (by simp)]
    rw [h2, Finset.sum_congr rfl (fun i _ => h1 i)]
    simp

theorem hermC_eq_dot {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  simp only [hermC, dotProduct, mulVec, map_apply, Finset.mul_sum, mul_assoc]

theorem conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => (starRingEnd ℂ) ((M *ᵥ w) b)) = M.map (starRingEnd ℂ) *ᵥ fun b => (starRingEnd ℂ) (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem hermC_mulVec {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ w) = u ⬝ᵥ ((Mᵀ * G.map τ * M.map (starRingEnd ℂ)) *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  rw [hermC_eq_dot, conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_phase {r : ℕ} (φ : Fin (r - 1) → ℝ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).det = 1 := by
  rw [det_diagonal, ← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, sum_angles]
  simp

theorem phase_gram {r : ℕ} (φ : Fin (r - 1) → ℝ) (s : Fin r → ℂ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ))))ᵀ * diagonal s *
      (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).map (starRingEnd ℂ) = diagonal s := by
  rw [diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext a
  rw [← Complex.exp_conj, mul_comm (Complex.exp _) (s a), mul_assoc, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

theorem torusGL_mem_realSU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ), torusGL hx θ ∈ realSU X.Ψ X.Gm := by
  intro E _ _ _ r X x hx θ
  intro τ
  have hu := isUnit_det_of_isOrth hx τ
  rw [torusGL_val]
  refine ⟨?_, fun u w => ?_⟩
  · rw [det_mul, det_mul, det_phase, mul_one, det_nonsing_inv, Ring.mul_inverse_cancel _ hu]
  · rw [hermC_mulVec, hermC_eq_dot]
    congr 2
    have hG := hx τ
    rw [gram_eq] at hG
    have h1 : (mat x τ)⁻¹ᵀ * (mat x τ)ᵀ = 1 := by
      rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
    have h2 : (mat x τ).map (starRingEnd ℂ) * ((mat x τ)⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGτ : X.Gm.map τ.1 = (mat x τ)⁻¹ᵀ * ((mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) *
        ((mat x τ)⁻¹).map (starRingEnd ℂ) := by
      rw [Matrix.mul_assoc _ _ ((mat x τ)⁻¹.map _), Matrix.mul_assoc _ ((mat x τ).map _), h2, Matrix.mul_one,
        ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [hG] at hGτ
    simp only [transpose_mul, Matrix.map_mul]
    rw [hGτ]
    have h1' : (mat x τ)ᵀ * (mat x τ)⁻¹ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ hu, transpose_one]
    have h2' : ((mat x τ)⁻¹).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have key := fun (Q : Matrix (Fin r) (Fin r) ℂ) =>
      (show (diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ)))ᵀ *
          ((diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          ((diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))).map (starRingEnd ℂ) * Q)) =
          (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * Q by
        simp only [← Matrix.mul_assoc, phase_gram])
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (mat x τ)ᵀ, h1', Matrix.one_mul, ← Matrix.mul_assoc ((mat x τ)⁻¹.map _), h2',
      Matrix.one_mul, key]

end GlobalTheory.TorusFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentMemSpecialUnitaryLieDiagonal
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem torusDer_sum_angles (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ i.castSucc = φ ⟨i, by simp⟩ := by
      intro i; unfold angles; rw [dite_eq_left (by simp)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dite_eq_right (by simp)]
    rw [h2, Finset.sum_congr rfl fun i _ => h1 i]
    rw [add_neg_eq_zero]
    exact Fintype.sum_equiv (finCongr (by simp)) _ _ (fun i => rfl)

theorem torusDer_hermC_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (w b)) := by
  simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem torusDer_conj_mulVec (Y : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => conj ((Y *ᵥ w) b)) = Y.map (starRingEnd ℂ) *ᵥ fun b => conj (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem torusDer_skew_of_mat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ)
    (hK : Yᵀ * G.map τ + G.map τ * Y.map (starRingEnd ℂ) = 0) (u w : Fin r → ℂ) :
    hermC τ G (Y *ᵥ u) w + hermC τ G u (Y *ᵥ w) = 0 := by
  rw [torusDer_hermC_dot, torusDer_hermC_dot, torusDer_conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, ← dotProduct_add, ← add_mulVec, hK, zero_mulVec, dotProduct_zero]

end GlobalTheory.TorusFrame

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

theorem skewHermitian_of_diagonal_imaginary_frame {r : ℕ} (G M Y : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s)
    (hYM : Y * M = M * diagonal d) :
    Yᵀ * G + G * Y.map (starRingEnd ℂ) = 0 := by
  have e1 : Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = diagonal d * diagonal s := by
    calc Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = (Y * M)ᵀ * G * M.map (starRingEnd ℂ) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal d * diagonal s := by
          rw [hYM, transpose_mul, diagonal_transpose, ← hJ]; simp only [Matrix.mul_assoc]
  have e2 : Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) =
      diagonal s * (diagonal d).map (starRingEnd ℂ) := by
    calc Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = Mᵀ * G * (Y * M).map (starRingEnd ℂ) := by
          rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal s * (diagonal d).map (starRingEnd ℂ) := by
          rw [hYM, Matrix.map_mul, ← hJ]; simp only [Matrix.mul_assoc]
  have h2 : Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, e1, e2]
    ext a b
    by_cases h : a = b
    · subst h; simp [diagonal_apply, hd]; ring
    · simp [diagonal_apply, h]
  have hL : (M⁻¹)ᵀ * Mᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
  have hR : M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Yᵀ * G + G * Y.map (starRingEnd ℂ)
      = ((M⁻¹)ᵀ * Mᵀ) * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) *
          (M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ)) := by rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
    _ = (M⁻¹)ᵀ * (Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ)) *
          (M⁻¹).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h2, Matrix.mul_zero, Matrix.zero_mul]

theorem torusDer_skew_diag {r : ℕ} (G M : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s) :
    (M * diagonal d * M⁻¹)ᵀ * G + G * (M * diagonal d * M⁻¹).map (starRingEnd ℂ) = 0 :=
  skewHermitian_of_diagonal_imaginary_frame G M _ hu d s hd hJ (by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one])

theorem torusDer_mem_realLie_and_inFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ∀ θ : X.Ψ → Fin (r - 1) → ℝ, torusDer x θ ∈ realLie X.Ψ X.Gm ∧
      ∀ τ a b, inFrame x (torusDer x θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0 := by
  intro E _ _ _ r X x hx θ
  have key : ∀ τ : X.Ψ, Matrix.of (torusDer x θ τ) =
      mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ := fun τ => rfl
  refine ⟨?_, fun τ a b => ?_⟩
  · intro τ
    have hu := isUnit_det_of_isOrth hx τ
    refine ⟨?_, fun u w => ?_⟩
    · rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, trace_diagonal,
        ← Finset.mul_sum, ← ofReal_sum, torusDer_sum_angles, ofReal_zero, mul_zero]
    · rw [key]
      refine torusDer_skew_of_mat τ.1 X.Gm _ ?_ u w
      refine torusDer_skew_diag _ _ hu _ (fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (fun a => ?_) ?_
      · simp
      · rw [← gram_eq]; exact hx τ
  · have hu := isUnit_det_of_isOrth hx τ
    unfold inFrame
    rw [key, show (mat x τ)⁻¹ * (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) * mat x τ =
        ((mat x τ)⁻¹ * mat x τ) * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * ((mat x τ)⁻¹ * mat x τ) by
        simp only [Matrix.mul_assoc], nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one, diagonal_apply]

end GlobalTheory.TorusFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumRingEqSumIdealCosetsTsum
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory

noncomputable def quotCosetProdEquiv (R : Type) [CommRing R] (M : Ideal R) : (R ⧸ M) × M ≃ R where
  toFun p := Quotient.out p.1 + (p.2 : R)
  invFun α := (Ideal.Quotient.mk M α, ⟨α - Quotient.out (Ideal.Quotient.mk M α), by
    rw [← Ideal.Quotient.eq]
    exact (Ideal.Quotient.mk_out _).symm⟩)
  left_inv p := by
    obtain ⟨c, μ⟩ := p
    have hc : Ideal.Quotient.mk M (Quotient.out c + (μ : R)) = c := by
      rw [map_add (f := _), Ideal.Quotient.mk_out, Ideal.Quotient.eq_zero_iff_mem.mpr μ.2, add_zero]
    ext
    · exact hc
    · simp only [hc]; ring
  right_inv α := by simp

theorem tsum_eq_sum_quotient_tsum_ideal (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)]
    (h : R → ℂ) (hs : Summable h) :
    ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) := by
  rw [← (quotCosetProdEquiv R M).tsum_eq h]
  have hs' : Summable (h ∘ quotCosetProdEquiv R M) := (quotCosetProdEquiv R M).summable_iff.mpr hs
  rw [show (∑' c : (R ⧸ M) × ↥M, h (quotCosetProdEquiv R M c)) = ∑' p, (h ∘ quotCosetProdEquiv R M) p from rfl,
    hs'.tsum_prod, tsum_fintype]
  rfl

theorem cosets_main : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) :=
  fun R _ M _ h hs => tsum_eq_sum_quotient_tsum_ideal R M h hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCellSumLeviReductionOfStepsStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCellSumLeviReduction_of_steps : GlobalTheory.SatakeWeyl.RankOne → GlobalTheory.SatakeWeyl.EmbExists → GlobalTheory.SatakeWeyl.EmbMem → GlobalTheory.SatakeWeyl.EmbTorus → GlobalTheory.SatakeWeyl.LeviRad → GlobalTheory.SatakeWeyl.UnipSplit → GlobalTheory.SatakeWeyl.Contract → GlobalTheory.SatakeWeyl.TorusConj → GlobalTheory.SatakeWeyl.LeviStep := by
  first | exact @GlobalTheory.SatakeWeyl.leviStep_of_steps | exact GlobalTheory.SatakeWeyl.leviStep_of_steps | (intros; apply GlobalTheory.SatakeWeyl.leviStep_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSqStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.IndexFour := by
  first | exact @GlobalTheory.SatakeWeyl.IdxFour.indexFour | exact GlobalTheory.SatakeWeyl.IdxFour.indexFour | (intros; apply GlobalTheory.SatakeWeyl.IdxFour.indexFour <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankTwoRootIndexOfTraceZeroCardStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard : GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexTwo := by
  first | exact @GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | exact GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | (intros; apply GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffAdjacentSwapOfLeviReductionStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction : GlobalTheory.SatakeWeyl.LeviStep → GlobalTheory.SatakeWeyl.IndexFour → GlobalTheory.SatakeWeyl.CartanFour → GlobalTheory.SatakeWeyl.CoeffSwap := by
  first | exact @GlobalTheory.SatakeWeyl.Swap.coeffSwap | exact GlobalTheory.SatakeWeyl.Swap.coeffSwap | (intros; apply GlobalTheory.SatakeWeyl.Swap.coeffSwap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentRadicalSplittingOfLeviPartStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart : GlobalTheory.SatakeWeyl.LeviPart → GlobalTheory.SatakeWeyl.UnipSplit := by
  first | exact @GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | exact GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | (intros; apply GlobalTheory.SatakeWeyl.unipSplit_of_leviPart <;> assumption)
end

