module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0010
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOscillatorIntegralSymplecticPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterGlobalArtinUnitsTrivialUniformiserPower
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem chi_artin_restrict : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω] (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK → ∀ (ρ : Gab K Ω →* Gab E Ω), (∀ τ : G K Ω, ρ (toAb K Ω τ) = toAb E Ω (τ.restrictScalars E)) → ∀ (B : Type) [CommGroup B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → (∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) → (∀ x, IsUnitAt w x → χ (ρ (artK (localIdele K w x))) = 1) ∧ ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → χ (ρ (artK (localIdele K w x))) = χ (art (localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  intro E Ω _ _ _ _ _ K _ _ _ art artK ha haK ρ hρ B _ χ v w hwv hχ
  obtain ⟨A, hAw⟩ := exists_isPlaceOver (F := K) Ω w
  obtain ⟨hAv, -, hine, hfrob⟩ := GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia E Ω K v w hwv A hAw

  have hI : ∀ ι ∈ Ine (F := E) A, χ (toAb E Ω ι) = 1 := by
    intro ι hι
    obtain ⟨u, hu, e⟩ := (ha.ine v A hAv (toAb E Ω ι)).mpr ⟨ι, hι, rfl⟩
    rw [← e]
    exact hχ u hu
  refine ⟨fun x hx => ?_, fun x ϖ hx hϖ => ?_⟩
  · obtain ⟨ι, hι, e⟩ := (haK.ine w A hAw _).mp ⟨x, hx, rfl⟩
    rw [← e, hρ]
    exact hI _ (hine ι hι)
  · obtain ⟨σ, hσ, e⟩ := (haK.frob w A hAw _).mp ⟨x, hx, rfl⟩
    obtain ⟨φ, hφ, e'⟩ := (ha.frob v A hAv _).mp ⟨ϖ, hϖ, rfl⟩
    have hm := hI _ (hfrob σ φ hσ hφ)
    have hr : (σ⁻¹).restrictScalars E = (σ.restrictScalars E)⁻¹ := AlgEquiv.ext fun _ => rfl
    rw [← e, hρ, ← e', hr, map_inv, map_inv, map_inv, map_inv, inv_pow]
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at hm
    rw [inv_inj]
    exact mul_inv_eq_one.mp hm

end GlobalTheory.NormCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPoints
section
noncomputable section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.UDense

theorem map_inv_field_hom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.adjugate.map f = (A.map f).adjugate := by
    have := RingHom.map_adjugate f A; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (A.map f).det = f A.det := by
    have := RingHom.map_det f A; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

theorem eval_bind₁_scale {ι : Type} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X,
      MvPolynomial.eval_C]

theorem vanish_generic (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hF : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hX : IsUPt X) (hd : ∀ σ, (1 + X σ).det ≠ 0) :
    MvPolynomial.eval (upt X) F = 0 := by
  classical
  let V : (L →+* ℂ) → Matrix (Fin n) (Fin n) (MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :=
    fun σ => Matrix.of fun i j => MvPolynomial.X (σ, i, j)
  let P : (L →+* ℂ) × Fin n × Fin n → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    fun p => ((1 + V p.1) * (1 - V p.1).adjugate) p.2.1 p.2.2
  let D : (L →+* ℂ) × Fin n × Fin n → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    fun p => (1 - V p.1).det
  obtain ⟨G, M, hGM⟩ := _root_.GlobalTheory.clearDenominators F P D
  have evV : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) σ,
      (V σ).map (MvPolynomial.eval (upt y)) = y σ := by
    intro y σ; ext i j; simp [V, upt]
  have evDet : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) σ,
      MvPolynomial.eval (upt y) ((1 - V σ).det) = (1 - y σ).det := by
    intro y σ
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), evV]
  have evP : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), (∀ σ, (1 - y σ).det ≠ 0) →
      (fun p => MvPolynomial.eval (upt y) (P p) / MvPolynomial.eval (upt y) (D p)) =
        upt (fun σ => (1 + y σ) * (1 - y σ)⁻¹) := by
    intro y hy
    funext p
    have hm : ((1 + V p.1) * (1 - V p.1).adjugate).map (MvPolynomial.eval (upt y)) =
        (1 + y p.1) * (1 - y p.1).adjugate := by
      rw [Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate,
        RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _), evV]
    have hP : MvPolynomial.eval (upt y) (P p) = ((1 + y p.1) * (1 - y p.1).adjugate) p.2.1 p.2.2 := by
      rw [← hm]; rfl
    rw [hP, show MvPolynomial.eval (upt y) (D p) = (1 - y p.1).det from evDet y p.1]
    simp only [upt, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    rw [div_eq_inv_mul]
  let Q := G * ∏ σ, (1 - V σ).det
  have hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0 := by
    intro S hS
    have hdS : ∀ σ : L →+* ℂ, (1 - ratPt S σ).det = σ (1 - S).det := by
      intro σ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    simp only [Q, map_mul, map_prod, evDet, hdS]
    by_cases h0 : (1 - S).det = 0
    · have σ0 : L →+* ℂ := Classical.arbitrary _
      rw [Finset.prod_eq_zero (Finset.mem_univ σ0) (by rw [h0, map_zero]), mul_zero]
    · obtain ⟨γ₀, hγ, hγv⟩ := _root_.GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian L n S hS h0
      have hne : ∀ σ : L →+* ℂ, (1 - ratPt S σ).det ≠ 0 := fun σ => by
        rw [hdS]; exact (map_ne_zero σ).2 h0
      have hDy : ∀ p, MvPolynomial.eval (upt (ratPt S)) (D p) ≠ 0 := fun p => by
        rw [show MvPolynomial.eval (upt (ratPt S)) (D p) = _ from evDet _ p.1]; exact hne p.1
      obtain ⟨-, hG⟩ := hGM _ hDy
      rw [hG, evP _ hne]
      have hc : (fun σ => (1 + ratPt S σ) * (1 - ratPt S σ)⁻¹) = ratPt (γ₀ : Matrix (Fin n) (Fin n) L) := by
        funext σ
        rw [hγv]
        simp only [ratPt, Matrix.map_mul, map_inv_field_hom, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [hc, hF γ₀ hγ, mul_zero, zero_mul]
  obtain ⟨Y, hYs, hYd, hYX⟩ := _root_.GlobalTheory.unitary_isCayley_of_det_ne_zero L n X hX hd
  have hQY := GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian L n Q hQ Y hYs
  have hDY : ∀ p, MvPolynomial.eval (upt Y) (D p) ≠ 0 := fun p => by
    rw [show MvPolynomial.eval (upt Y) (D p) = _ from evDet _ p.1]; exact hYd p.1
  obtain ⟨hM, hG⟩ := hGM _ hDY
  simp only [Q, map_mul, map_prod, evDet] at hQY
  have hprod : ∏ σ, (1 - Y σ).det ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hYd σ
  have hG0 : MvPolynomial.eval (upt Y) G = 0 := (mul_eq_zero.1 hQY).resolve_right hprod
  rw [hG, evP _ hYd, show (fun σ => (1 + Y σ) * (1 - Y σ)⁻¹) = X from funext hYX] at hG0
  exact (mul_eq_zero.1 hG0).resolve_left hM

theorem eval_eq_zero_of_rat : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) →
    ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by
  intro L _ _ _ n F hF X hX
  obtain ⟨a, ha, hdet⟩ := _root_.GlobalTheory.exists_normOne_det_one_add_ne_zero L n X
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := complexConj_invol L
  have ha' : c a * a = 1 := by rw [mul_comm]; exact ha
  have hca0 : c a ≠ 0 := left_ne_zero_of_mul_eq_one ha'
  have hemb : ∀ (σ : L →+* ℂ) x, ComplexEmbedding.conjugate σ x = σ (c x) := fun σ x =>
    (IsCMField.complexEmbedding_complexConj L σ x).symm
  let F' := MvPolynomial.bind₁ (fun p : (L →+* ℂ) × Fin n × Fin n => MvPolynomial.C (p.1 (c a)) * MvPolynomial.X p) F
  have hF'ev : ∀ z, MvPolynomial.eval z F' = MvPolynomial.eval (fun p => p.1 (c a) * z p) F :=
    fun z => eval_bind₁_scale _ z F
  have hF' : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F' = 0 := by
    intro γ₀ hγ
    let s : GL (Fin n) L := Units.map (algebraMap L (Matrix (Fin n) (Fin n) L) : L →* Matrix (Fin n) (Fin n) L)
      (Units.mk0 (c a) hca0)
    have hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.scalar (Fin n) (c a) := rfl
    have hmem : s * γ₀ ∈ GQ0 L n := by
      refine (GQ0 L n).mul_mem ?_ hγ
      show (s : Matrix (Fin n) (Fin n) L) * conjT c s = 1
      rw [hs, conjT]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply, hcc, ha']
      · simp [Matrix.scalar_apply, Matrix.one_apply, hij]
    have := hF _ hmem
    rw [hF'ev, ← this]
    refine congrArg (fun z => MvPolynomial.eval z F) ?_
    funext p
    simp [upt, ratPt, hs, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  let X' : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ => σ a • X σ
  have hX' : IsUPt X' := by
    intro σ
    simp only [X', Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX σ, hemb, ← map_mul, ha, ha',
      map_one, one_smul]
  have h := vanish_generic L n F' hF' X' hX' hdet
  rw [hF'ev] at h
  rw [← h]
  refine congrArg (fun z => MvPolynomial.eval z F) ?_
  funext p
  simp only [upt, X', Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, ha', map_one, one_mul]

end GlobalTheory.UDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplex
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem exists_isBEig_of_isPolyRep :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
      IsPolyRep Φ → ∃ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam := by
  intro n ι _ _ _ Φ hΦ
  obtain ⟨μ₀, hμ₀⟩ := _root_.GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep n ι Φ hΦ
  obtain ⟨μ, ⟨v, hv0, hvw⟩, hmax⟩ := _root_.GlobalTheory.AlgWtHW.MaxWeight.exists_max_weight n ι Φ μ₀ hμ₀
  refine ⟨v, μ, hv0, fun B hB => ?_⟩
  have hU : ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → Φ U *ᵥ v = v := by
    refine _root_.GlobalTheory.unitriangular_induction_transvection n (fun U => Φ U *ᵥ v = v) (by simp [hΦ.one]) (fun A C hA hC => ?_) ?_
    · show Φ (A * C) *ᵥ v = v
      rw [hΦ.mul, ← mulVec_mulVec, hC, hA]
    · intro i j hij s C hC
      show Φ C *ᵥ v = v
      obtain ⟨K, w, hw0, hww, hsum⟩ := _root_.GlobalTheory.transvection_weightVec_expansion n ι Φ hΦ i j (ne_of_lt hij) μ v hvw
      have hz : ∀ k, k ≠ 0 → w k = 0 := by
        intro k hk
        by_contra hne
        have := hmax _ ⟨w k, hne, hww k⟩
        have hk' : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
        have hij' : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
        have key : ∑ l : Fin n, ((n : ℤ) - ((l : ℕ) : ℤ)) * ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l)
            = ∑ l : Fin n, ((n : ℤ) - ((l : ℕ) : ℤ)) * μ l + k * (((n : ℤ) - ((i : ℕ) : ℤ)) - ((n : ℤ) - ((j : ℕ) : ℤ))) := by
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
            mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
          ring
        rw [key] at this
        nlinarith
      rw [hsum s C hC, Finset.sum_eq_single 0 (fun k _ hk => by rw [hz k hk, smul_zero]) (by simp), hw0, pow_zero, one_smul]
  obtain ⟨D, U, rfl, hD, hDd, hUb, hU1⟩ := _root_.GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular n B hB
  rw [hΦ.mul, ← mulVec_mulVec, hU U hUb hU1, hvw D hD]
  simp only [hDd]

end GlobalTheory.AlgWtHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplEquiv
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory.SplitComplHomeo


open scoped WithZeroTopology in
theorem exists_complEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L,
      Continuous i ∧ Continuous i.symm ∧ ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro E _ _ _ s
  have : s.w.asIdeal.LiesOver s.v.asIdeal := ⟨s.w_under.symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (maximalRealSubfield E) E s.v s.w).continuous
  let φ : s.v.adicCompletion (maximalRealSubfield E) →+* s.w.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E s.w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv (maximalRealSubfield E) s.v).toRingHom
  have hφ : ∀ x : maximalRealSubfield E, φ (algebraMap (maximalRealSubfield E) _ x) =
      algebraMap E _ (algebraMap (maximalRealSubfield E) E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E s.w).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion (maximalRealSubfield E) s.v))
  have hi : ∀ x : E, φ (s.i x) = algebraMap E (s.w.adicCompletion E) x := fun x => by
    have key : ∀ y, Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x) := fun y =>
      (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) s.v).induction_on
        (p := fun y => Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x)) y
        (isClosed_eq
          ((Valued.continuous_valuation_of_surjective (s.w.valuedAdicCompletion_surjective E)).comp
            (hcont.sub continuous_const))
          ((Valued.continuous_valuation_of_surjective (s.v.valuedAdicCompletion_surjective _)).comp
            (continuous_id.sub continuous_const))) fun k => by
        rw [hφ, ← map_sub, ← PI.CompAtExist.stepA s, map_sub, AlgHom.commutes]
    have h0 := key (s.i x)
    rw [sub_self, map_zero, map_eq_zero, sub_eq_zero] at h0
    exact h0
  letI : Algebra (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) := φ.toAlgebra
  haveI : ContinuousSMul (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ hcont
  letI : NontriviallyNormedField (s.v.adicCompletion (maximalRealSubfield E)) :=
    Valued.toNontriviallyNormedField _ _
  have hs : Function.Surjective φ := by
    have hcl : IsClosed (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E)) := Submodule.closed_of_finiteDimensional _
    intro y
    exact (HeightOneSpectrum.denseRange_algebraMap E s.w).induction_on
      (p := fun y => y ∈ (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E))) y hcl fun x => ⟨s.i x, hi x⟩
  let e : s.v.adicCompletion (maximalRealSubfield E) ≃ₗ[s.v.adicCompletion (maximalRealSubfield E)]
      s.w.adicCompletion E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) ⟨φ.injective, hs⟩
  haveI : FiniteDimensional (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    e.finiteDimensional
  have hinv : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  refine ⟨RingEquiv.ofBijective φ ⟨φ.injective, hs⟩, hcont, hinv.congr fun y => ?_, hi⟩
  exact (RingEquiv.symm_apply_eq _).2 (e.apply_symm_apply y).symm |>.symm

end GlobalTheory.SplitComplHomeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueEmbeddingEigenspaceSum
section
noncomputable section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField

namespace GlobalTheory.EigDecomp

theorem exists_integral_separating (E : Type) [Field E] [NumberField E] :
    ∃ α : 𝓞 E, (∀ τ τ' : E →+* ℂ, τ (α : E) = τ' (α : E) → τ = τ') ∧
      ∀ a : 𝓞 E, ∃ N : ℤ, N ≠ 0 ∧ ∃ g : ℤ[X], aeval α g = N • a := by
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({α0} : Finset E)
  have hi : IsIntegral ℤ (d • α0) := hint α0 (Finset.mem_singleton_self _)
  let α : 𝓞 E := ⟨d • α0, hi⟩
  have hαE : (α : E) = d • α0 := rfl
  have hadjF : ℚ⟮(α : E)⟯ = ⊤ := by
    refine top_le_iff.mp (hα0 ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have h1 : α0 = ((d : ℚ)⁻¹) • (α : E) := by
      rw [hαE, zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap ℚ E) d, ← map_mul,
        inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd), map_one, one_mul]
    rw [h1]
    exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hadj : Algebra.adjoin ℚ {(α : E)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (α : E)), hadjF, IntermediateField.top_toSubalgebra]
  refine ⟨α, fun τ τ' h => ?_, fun a => ?_⟩
  · have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom)
      (by rintro x rfl; exact h)
    ext x
    exact congrArg (fun f : E →ₐ[ℚ] ℂ => f x) this
  · have ha : (a : E) ∈ Algebra.adjoin ℚ {(α : E)} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨g, hg⟩ := ha
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
    refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors ℤ) g, ?_⟩
    apply RingOfIntegers.coe_injective
    have hg' : aeval (algebraMap (𝓞 E) E α) g = algebraMap (𝓞 E) E a := hg
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap ℚ, hb, map_zsmul, hg', map_zsmul]

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem nodal_eq_minpoly_map (c : Coeff l) (α : 𝓞 E)
    (hinj : Function.Injective fun τ : E →+* ℂ => embK c τ α) :
    Lagrange.nodal Finset.univ (fun τ : E →+* ℂ => embK c τ α) = (minpoly ℤ α).map (Int.castRingHom c.F) := by
  have hint : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hintE : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) ?_ ?_
  · rw [Lagrange.nodal]
    refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _) fun τ _ => dvd_iff_isRoot.mpr ?_
    have h := aeval_algHom_apply (embK c τ).toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    rw [IsRoot.def, eval_map, ← algebraMap_int_eq, ← aeval_def]
    exact h
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int _), Lagrange.natDegree_nodal, Finset.card_univ,
      NumberField.Embeddings.card E ℂ, ← RingOfIntegers.minpoly_coe,
      ← natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintE]
    exact minpoly.natDegree_le _

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

theorem X_sub_C_mul_basis {ι F : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} {i : ι}
    (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero _) (Lagrange.X_sub_C_dvd_nodal v hi)

theorem exists_unique_eigen_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R)
    (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V,
      (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  intro E _ _ _ H l c R V _ _ _ φ ρ v
  classical
  obtain ⟨α, hinj, hden⟩ := exists_integral_separating E
  let lam : (E →+* ℂ) → c.F := fun τ => embK c τ α
  have hlinj : Function.Injective lam := fun τ τ' h => hinj τ τ' (by
    have := congrArg (fun x : c.F => (x : ℂ)) h
    simpa [lam, embK_coe] using this)
  let A : Module.End R V := ρ α
  let ψ : c.F →+* Module.End R V := (algebraMap R (Module.End R V)).comp φ
  have hc : ∀ x, Commute (ψ x) A := fun x => Algebra.commute_algebraMap_left (φ x) A
  let ev : Polynomial c.F →+* Module.End R V := eval₂RingHom' ψ A hc
  have hev : ∀ p, ev p = p.eval₂ ψ A := fun p => rfl
  have hev_int : ∀ g : ℤ[X], ev (g.map (Int.castRingHom c.F)) = aeval A g := by
    intro g
    rw [hev, eval₂_map, aeval_def]
    congr 1
    exact RingHom.ext_int _ _
  have heig : ∀ (μ : c.F) (x : V), A x = φ μ • x → ∀ p : Polynomial c.F, ev p x = φ (p.eval μ) • x := by
    intro μ x hx p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add (f := _), LinearMap.add_apply, hp, hq, eval_add, map_add (f := _), add_smul]
    | monomial k a =>
      have hk : ∀ k : ℕ, (A ^ k) x = φ μ ^ k • x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ, mul_comm]
      rw [hev, eval₂_monomial, eval_monomial, Module.End.mul_apply, hk, map_mul, map_pow]
      simp [ψ, smul_smul, mul_comm]
  have hnodal : ev (Lagrange.nodal Finset.univ lam) = 0 := by
    rw [nodal_eq_minpoly_map c α hlinj, hev_int]
    have h := aeval_algHom_apply ρ.toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    exact h
  let P : (E →+* ℂ) → Module.End R V := fun τ => ev (Lagrange.basis Finset.univ lam τ)
  have hPeig : ∀ τ x, A (P τ x) = φ (lam τ) • P τ x := by
    intro τ x
    have h := congrArg (fun p => ev p x) (X_sub_C_mul_basis (s := Finset.univ) (v := lam) (Finset.mem_univ τ))
    simp only [map_mul, map_sub, hnodal, mul_zero, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply] at h
    rw [hev X, eval₂_X, hev (C _), eval₂_C] at h
    simpa [ψ, sub_eq_zero, P] using h
  have hsum : ∑ τ, P τ = 1 := by
    simp only [P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Lagrange.sum_basis hlinj.injOn Finset.univ_nonempty, map_one]
  have hall : ∀ τ x, A x = φ (lam τ) • x → ∀ a, ρ a x = φ (embK c τ a) • x := by
    intro τ x hx a
    obtain ⟨N, hN, g, hg⟩ := hden a
    have h1 : ρ (N • a) x = φ (embK c τ (N • a)) • x := by
      rw [← hg]
      have e1 := aeval_algHom_apply ρ.toIntAlgHom α g
      have e2 := aeval_algHom_apply (embK c τ).toIntAlgHom α g
      change ρ (aeval α g) x = φ (embK c τ (aeval α g)) • x
      rw [← show aeval A g = ρ (aeval α g) from e1, ← show aeval (lam τ) g = embK c τ (aeval α g) from e2,
        ← hev_int, heig _ _ hx, eval_map, ← algebraMap_int_eq, ← aeval_def]
    have hu : IsUnit (N : R) := by
      rw [← map_intCast φ]
      exact (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hN)).map φ
    rw [map_zsmul, map_zsmul, map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul R,
      ← Int.cast_smul_eq_zsmul R, smul_assoc] at h1
    exact hu.smul_left_cancel.mp h1
  refine ⟨fun τ => P τ v, ⟨fun τ a => hall τ _ (hPeig τ v) a, ?_⟩, ?_⟩
  · show ∑ τ, P τ v = v
    rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
  · rintro w ⟨hw, hws⟩
    funext τ
    show w τ = P τ v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hws, map_sum, Finset.sum_eq_single τ]
    · rw [heig (lam τ) _ (hw τ α), Lagrange.eval_basis_self hlinj.injOn (Finset.mem_univ τ), map_one, one_smul]
    · intro τ' _ hne
      rw [heig (lam τ') _ (hw τ' α), Lagrange.eval_basis_of_ne (Ne.symm hne) (Finset.mem_univ τ'), map_zero, zero_smul]
    · simp

end GlobalTheory.EigDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOscillatorIntegralSymplecticPathStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_oscillatorIntegral_symplecticPath : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (a : ℝ → V →L[ℝ] V) (X : V →L[ℝ] V), a 0 = 1 → HasDerivAt a X 0 → (∀ t x y, omJ J (a t x) (a t y) = omJ J x y) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (omJ J) X c p q → ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t : ℝ => ∫ w, ρ (a t w) (∫ u, gau u • ρ (a t u) (proj h (ρ (-w) f)))) (quad ρ c p q f + lam • f) 0 := by
  first | exact @GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc | exact GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc | (intros; apply GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc <;> assumption)
end

