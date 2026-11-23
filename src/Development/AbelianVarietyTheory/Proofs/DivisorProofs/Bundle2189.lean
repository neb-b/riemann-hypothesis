module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
section
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

namespace GlobalTheory.TopFrameEt

theorem isFreeGen_dForm_of_formallyEtale_mvPolynomial :
    ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  intro k A₀ A _ _ _ α β ρ hc n r z b hb t hφ
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A₀ A := IsScalarTower.of_algebraMap_eq' hc.symm
  let φ := MvPolynomial.eval₂Hom ρ t
  letI : Algebra (MvPolynomial (Fin r) A₀) A := φ.toAlgebra
  haveI : IsScalarTower A₀ (MvPolynomial (Fin r) A₀) A :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = φ (MvPolynomial.C a)
      simp [φ, RingHom.algebraMap_toAlgebra]
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) A₀) A := hφ
  haveI : Algebra.FormallySmooth A₀ A :=
    Algebra.FormallySmooth.comp A₀ (MvPolynomial (Fin r) A₀) A
  haveI : Subsingleton (Algebra.H1Cotangent A₀ A) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k A₀ A) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k A₀ A y).1 hy
    rw [Subsingleton.elim w 0, map_zero]
  let w : Module.Basis (Fin r) A (Ω[A⁄A₀]) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale A₀ (MvPolynomial (Fin r) A₀) A).basis
      (KaehlerDifferential.mvPolynomialBasis A₀ (Fin r))
  have hw : ∀ i, w i = KaehlerDifferential.D A₀ A (t i) := fun i ↦ by
    simp [w, IsBaseChange.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.map_D, RingHom.algebraMap_toAlgebra, φ]
  obtain ⟨B, hB⟩ := exists_basis_of_exact
    (KaehlerDifferential.mapBaseChange k A₀ A) (KaehlerDifferential.map k A₀ A A) hinj
    (KaehlerDifferential.exact_mapBaseChange_map k A₀ A)
    (b.baseChange A) w (fun i ↦ KaehlerDifferential.D k A (t i))
    (fun i ↦ by rw [hw, KaehlerDifferential.map_D]; rfl)
  let e : Fin (r + n) ≃ Fin n ⊕ Fin r := finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
  refine isFreeGen_dForm _ (B.reindex e.symm) fun a ↦ ?_
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) a
  · simp [e, Fin.append_left]
  · simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumComm_apply,
      Sum.swap_inr, Sum.elim_inl, Module.Basis.baseChange_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul, hb, dFun, KaehlerDifferential.map_D,
      Fin.append_right]
    rfl

end GlobalTheory.TopFrameEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GrpPB

theorem isGrpPullback_comp {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {P : Over T} [GrpObj P] {f : S' ⟶ S} {t : T ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : P.left ⟶ G'.left}
    (h₁ : IsGrpPullback P G' t ψ) (h₂ : IsGrpPullback G' G f φ) :
    IsGrpPullback P G (t ≫ f) (ψ ≫ φ) := by
  refine ⟨h₁.1.paste_horiz h₂.1, fun T₀ x y x₀ y₀ hx hy => ?_⟩
  have wx : ∀ z : T₀ ⟶ P, (z.left ≫ ψ) ≫ G'.hom = (Over.mk (T₀.hom ≫ t)).hom := fun z => by
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w z]; rfl
  let x' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (x.left ≫ ψ) (wx x)
  let y' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (y.left ≫ ψ) (wx y)
  have e₁ : (x' * y').left = (x * y).left ≫ ψ := h₁.2 T₀ x y x' y' rfl rfl
  let e : Over.mk ((Over.mk (T₀.hom ≫ t)).hom ≫ f) ⟶ Over.mk (T₀.hom ≫ t ≫ f) :=
    Over.homMk (𝟙 _) (by simp)
  have e₂ : ((e ≫ x₀) * (e ≫ y₀)).left = (x' * y').left ≫ φ :=
    h₂.2 _ x' y' (e ≫ x₀) (e ≫ y₀) (by simp [e, x', hx]) (by simp [e, y', hy])
  rw [← MonObj.comp_mul, Over.comp_left] at e₂
  simp only [e, Over.homMk_left, Category.id_comp] at e₂
  rw [e₂, e₁, Category.assoc]

theorem baseChange_square {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (t : T ⟶ S') :
    IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧
      ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := by
  have hc := isGrpPullback_comp (isGrpPullback_pullback G' t) h
  refine ⟨hc, ?_⟩
  set P := (Over.pullback t).obj G'
  have w : ∀ q : P ⊗ P ⟶ P, (q.left ≫ pullback.fst G'.hom t ≫ φ) ≫ G.hom = (Over.mk ((P ⊗ P).hom ≫ t ≫ f)).hom :=
    fun q => by
      rw [Category.assoc, Category.assoc, ← Category.assoc _ φ, hc.1.w, ← Category.assoc, Over.w q]; rfl
  let a : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (fst P P))
  let b : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (snd P P))
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]; rfl
  · rw [← Over.comp_left, lift_snd]; rfl

end GlobalTheory.GrpPB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertEisensteinLatticeValueOfEisensteinSerie
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt eisClass_mk)

namespace GlobalTheory.HilbFam.EisCmp

variable {F : Type} [Field F] [NumberField F]

theorem card_realEmb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem mem_split (𝔞 𝔟 : Frac F) (v : Fin 2 → F) :
    v ∈ split 𝔞 𝔟 0 ↔ v 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 ∈ latM 𝔞 := by
  show v 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * 0 ∈ latM 𝔞 ↔ _
  rw [mul_zero, sub_zero]

theorem unit_smul_apply (ε : (𝓞 F)ˣ) (v : Fin 2 → F) (i : Fin 2) : (ε • v) i = ((ε : 𝓞 F) : F) * v i := by
  rw [Pi.smul_apply, Units.smul_def, Algebra.smul_def]

def pair (𝔞 𝔟 : Frac F) (q : cls (split 𝔞 𝔟 0)) : LatPair 𝔞 𝔟 :=
  ⟨(q.1.out 1, q.1.out 0), ((mem_split 𝔞 𝔟 _).1 q.2.1).2, ((mem_split 𝔞 𝔟 _).1 q.2.1).1, fun h ↦ q.2.2 (by
    funext i
    fin_cases i
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h)⟩

theorem bij (𝔞 𝔟 : Frac F) :
    Function.Bijective (fun q : cls (split 𝔞 𝔟 0) ↦ Quotient.mk (latRel 𝔞 𝔟) (pair 𝔞 𝔟 q)) := by
  constructor
  · intro q1 q2 h
    obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    refine (Quotient.sound ?_).symm
    refine ⟨ε, ?_⟩
    funext i
    show (ε • q1.1.out) i = _
    rw [unit_smul_apply]
    fin_cases i
    · exact h2.symm
    · exact h1.symm
  · intro cl
    obtain ⟨p, rfl⟩ := Quotient.exists_rep cl
    let v : Fin 2 → F := ![p.1.2, p.1.1]
    have hv : v ∈ split 𝔞 𝔟 0 := (mem_split 𝔞 𝔟 v).2 ⟨p.2.2.1, p.2.1⟩
    have hv0 : v ≠ 0 := fun h ↦ p.2.2.2 (Prod.ext (congrFun h 1) (congrFun h 0))
    obtain ⟨ε, hε⟩ : (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v).out ∈ MulAction.orbit (𝓞 F)ˣ v :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v))
    have hε' : (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v).out = ε • v := hε.symm
    refine ⟨⟨Quotient.mk _ v, ?_, ?_⟩, ?_⟩
    · rw [hε']; exact Submodule.smul_mem _ (ε : 𝓞 F) hv
    · rw [hε']; exact (smul_ne_zero_iff_ne ε).2 hv0
    · refine (Quotient.sound (show (latRel 𝔞 𝔟).r p _ from ⟨ε, ?_, ?_⟩)).symm
      · exact (congrFun hε' 1).trans (unit_smul_apply ε v 1)
      · exact (congrFun hε' 0).trans (unit_smul_apply ε v 0)

theorem term_eq [IsTotallyReal F] (k : ℕ) (σ : ℂ) (w : Emb F → ℂ) (x : Fin 2 → F) :
    gTerm k σ w 1 x = (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
      ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * eisTerm k σ w (x 1, x 0) := by
  have hP : ∏ τ, latPt w (x 1, x 0) τ = (2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * ∏ τ, coord w 1 x τ := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ ↦ ?_
    simp only [latPt, coord, Pi.one_apply]; ring
  have hΛ : (2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F ≠ 0 := pow_ne_zero _ Complex.two_pi_I_ne_zero
  unfold gTerm eisTerm
  rw [hP]
  generalize (2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F = Λ at hΛ
  have hn : ((‖Λ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hΛ)
  have h1 : Λ ^ k * Λ⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hΛ, one_pow]
  have h2 : ((‖Λ‖ : ℝ) : ℂ) ^ (2 * σ) * ((‖Λ‖ : ℝ) : ℂ) ^ (-2 * σ) = 1 := by
    rw [← Complex.cpow_add _ _ hn, show 2 * σ + -2 * σ = 0 by ring, Complex.cpow_zero]
  rw [mul_inv, mul_pow, norm_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  generalize (∏ τ, coord w 1 x τ)⁻¹ ^ k = A
  generalize ((‖∏ τ, coord w 1 x τ‖ : ℝ) : ℂ) ^ (-2 * σ) = B
  linear_combination (-(A * B) * (((‖Λ‖ : ℝ) : ℂ) ^ (2 * σ) * ((‖Λ‖ : ℝ) : ℂ) ^ (-2 * σ))) * h1 - (A * B) * h2

theorem hasSum_gTerm [IsTotallyReal F] (𝔞 𝔟 : Frac F) {k : ℕ} (hk : Even k) (σ : ℂ) (w : Emb F → ℂ) (S : ℂ)
    (h : HasSum (eisClass 𝔞 𝔟 k σ w) S) :
    HasSum (fun q : cls (split 𝔞 𝔟 0) ↦ gTerm k σ w 1 q.1.out)
      ((((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * S) := by
  have h1 := ((Equiv.hasSum_iff (Equiv.ofBijective _ (bij 𝔞 𝔟))).2 h).mul_left
    (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ))
  have h2 : (fun q : cls (split 𝔞 𝔟 0) ↦ gTerm k σ w 1 q.1.out) = fun q : cls (split 𝔞 𝔟 0) ↦
      (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) *
        eisClass 𝔞 𝔟 k σ w (Quotient.mk (latRel 𝔞 𝔟) (pair 𝔞 𝔟 q)) := by
    funext q
    rw [eisClass_mk 𝔞 𝔟 hk, term_eq]
    rfl
  rw [h2]
  exact h1

theorem isGVal_of_isEis : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ)
    (w : Emb F → ℂ), Even k → IsEis 𝔞 𝔟 k G → w ∈ upperHalf F →
    IsGVal k (split 𝔞 𝔟 0) w 1 (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k * G w) := by
  intro F _ _ _ k 𝔞 𝔟 G w hk hG hw
  constructor
  · intro h2
    have h := hasSum_gTerm 𝔞 𝔟 hk 0 w _ (hG.1 h2 w hw)
    rwa [mul_zero, Complex.cpow_zero, mul_one] at h
  · rintro rfl
    obtain ⟨H, hH, rfl⟩ := hG.2 rfl
    have hn : ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (pow_ne_zero _ Complex.two_pi_I_ne_zero))
    refine ⟨fun σ ↦ (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ 2 *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * H σ w, ?_, ?_, ?_⟩
    · have hHd : DifferentiableOn ℂ (fun σ ↦ H σ w) {σ : ℂ | -1 / 2 < σ.re} := hH.2.2 [] w hw
      have hAd : Differentiable ℂ fun σ : ℂ ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ 2 *
          ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ) := fun σ ↦
        (differentiableAt_const _).mul (((differentiableAt_const (2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn))
      exact hAd.differentiableOn.mul hHd
    · intro σ hσ
      obtain ⟨hsm, hHe⟩ := hH.1 σ hσ w hw
      exact hasSum_gTerm 𝔞 𝔟 hk σ w _ (by rw [hHe]; exact hsm.hasSum)
    · simp only [mul_zero, Complex.cpow_zero, mul_one]

end GlobalTheory.HilbFam.EisCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegral
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam

theorem isIntegral_coord_of_isIntegral (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ)
    (x : Fin 2 → FR E) (_hD : 0 < D) (hθ : IsIntegral ℤ θ)
    (hr : (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E))
    (hu : IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E))) (j : Fin 2) :
    IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  have hc : ∀ y : E, IsIntegral ℤ y → IsIntegral ℤ (IsCMField.complexConj E y) := fun y hy =>
    map_isIntegral_int (IsCMField.complexConj E) hy
  have hfix : ∀ y : FR E, IsCMField.complexConj E (y : E) = y := fun y =>
    IsCMField.complexConj_apply_eq_self E y
  set r := θ - IsCMField.complexConj E θ with hrdef
  have hri : IsIntegral ℤ r := hθ.sub (hc _ hθ)
  have h0 : IsIntegral ℤ ((x 0 : E) * r) := by
    have := hu.sub (hc _ hu)
    rw [map_add (f := _), map_mul, hfix, hfix] at this
    have e : (x 0 : E) * r = (x 0 : E) * θ + (x 1 : E) -
        ((x 0 : E) * IsCMField.complexConj E θ + (x 1 : E)) := by rw [hrdef]; ring
    rw [e]; exact this
  have h1 : IsIntegral ℤ ((x 1 : E) * r) := by
    have := (hu.mul hri).sub (h0.mul hθ)
    have e : (x 1 : E) * r = ((x 0 : E) * θ + (x 1 : E)) * r - (x 0 : E) * r * θ := by ring
    rw [e]; exact this
  have hj : IsIntegral ℤ ((x j : E) * r) := by
    fin_cases j
    · exact h0
    · exact h1
  have hD' : (D : E) = -r ^ 2 := by rw [hr]; ring
  have hinj : Function.Injective (algebraMap (FR E) E) := (algebraMap (FR E) E).injective
  have hx : algebraMap (FR E) E (x j) = (x j : E) := rfl
  constructor
  · rw [← (isIntegral_algebraMap_iff (B := E)), map_mul, map_pow, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) ^ 2 = -((x j : E) * r * ((x j : E) * r)) := by ring
    rw [e]; exact (hj.mul hj).neg
  · rw [← (isIntegral_algebraMap_iff (B := E)), map_mul, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) = -((x j : E) * r * r) := by ring
    rw [e]; exact (hj.mul hri).neg

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralImageOfField
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem isIntegral_image_of_field {K : Type} [Field K] {S : Scheme.{0}} (g : Sp K ⟶ S) : IsIntegral g.image := by
  have : QuasiCompact g := inferInstance
  have := GlobalTheory.isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  have hi : IsIrreducible (Set.range g.toImage) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ g.toImage.continuous.continuousOn
  have hc := hi.closure
  rw [g.toImage.denseRange.closure_range] at hc
  have : IrreducibleSpace g.image := { isPreirreducible_univ := hc.2, toNonempty := ⟨hc.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem lbIso_factor {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {M : LB Z} (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB)
    {F : Y ⟶ X} {a' : Z ⟶ Y} {a : Z ⟶ X} (e : a' ≫ F = a) (h' : LBIso L' (L.pull F)) (h : LBIso M (L.pull a)) :
    LBIso M (L'.pull a') :=
  LBIso.trans hM (pull_isLB hL _) (pull_isLB hL' _) h
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' a' a' rfl) (chartPullSame L (fun _ => a) (fun _ => F) _ a' fun _ => e.symm) h').symm

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFiniteEtaleOfExistsUniqueLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isIso_of_finite_etale_of_existsUnique_lift (W S : Scheme.{0}) (w : W ⟶ S) (hf : IsFinite w)
    (he : Etale w) (hc : PreconnectedSpace S) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S)
    (hs : ∃! x : Sp Ω ⟶ W, x ≫ w = s) : IsIso w := by
  obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨x₀, hx₀, hu⟩ := hs
  have hsub : Subsingleton {x : Sp Ω ⟶ W // x ≫ w = s} :=
    ⟨fun a b => Subtype.ext ((hu a.1 a.2).trans (hu b.1 b.2).symm)⟩
  have hne : Nonempty {x : Sp Ω ⟶ W // x ≫ w = s} := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨_, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank w s z
  have h1 : w.finrank (s z) = 1 := by
    rw [← hcard, Nat.card_eq_one_iff_unique]
    exact ⟨hsub, hne⟩
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext y
  rw [Pi.one_apply, ← h1]
  exact (Scheme.Hom.isLocallyConstant_finrank w).apply_eq_of_preconnectedSpace y (s z)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem isLab_onto_and_ker : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy → Function.Surjective yy ∧ yy.ker = X₁.S.HH X₁.M z₁ := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ p _ z₁ c yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR', y₀, hy₀, u, l, j, -, hyy, -⟩ := hl
  have hm : NeZero (X₁.S.r * X₁.S.N) :=
    ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)⟩
  refine ⟨?_, ?_⟩
  · intro m
    obtain ⟨χ', rfl⟩ := QuotientAddGroup.mk_surjective m
    obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm χ'))
    exact ⟨a, by rw [hyy a _ ha, j.apply_symm_apply]⟩
  have hker : yy.ker = l.yy.ker := by
    ext a
    simp only [AddMonoidHom.mem_ker]
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [hyy a χ hχ.symm, ← hχ, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨j.symm v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv, j.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨j v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv]
  have hint : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one c.cen ((X₁.M.O z₁).algebraMap_mem a)
  have hcl := GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint
  rw [hker, ← hcl.2]

  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  set val := X₁.M.val (gPt p ≫ c.y) with hval
  have hsp : ∀ w, (gPt p ≫ c.y) w ⤳ (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ z₁ :=
    RatModel.gPt_specializes c.cen _
  have hy : ∀ x, y₀ ⟨c₀ * X₁.S.th x, hth x⟩ = val (c₀ * X₁.S.th x) := fun x => hy₀ _
  have hmul : ∀ x, ‖val (c₀ * X₁.S.th x)‖ = ‖val (X₁.S.th x / X₁.S.th x₀)‖ * ‖val (c₀ * X₁.S.th x₀)‖ := by
    intro x
    rw [← norm_mul, hval, ← RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth x₀))]
    congr 2
    have := hx₀.1
    field_simp
  have hδ : ‖val (c₀ * X₁.S.th x₀)‖ = (X₁.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    apply le_antisymm
    · rw [← hy]
      exact le_ciSup (f := fun x => ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖) (Set.finite_range _).bddAbove x₀
    · obtain ⟨x₁, hx₁⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖)
      change ⨆ x, ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖ ≤ _
      rw [← hx₁, hy, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one c.cen (hx₀.2 x₁))
  have key : ∀ x, x ∈ X₁.S.supI X₁.M z₁ ↔
      ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖ = (X₁.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    intro x
    change X₁.M.Div X₁.S.th x z₁ ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff c.cen (hx₀.2 x), hy, hmul x, hδ]
    exact (mul_eq_right₀ hcl.1.ne').symm
  rw [ThetaSys.HH]
  congr 1
  ext x
  exact (key x).symm

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvdStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardSmooth_localizationAway_jacobian_dvd : ∀ (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν), Function.Injective m → ∀ (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R), (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h → Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  first | exact @GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd | exact GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd | (intros; apply GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd <;> assumption)
end

