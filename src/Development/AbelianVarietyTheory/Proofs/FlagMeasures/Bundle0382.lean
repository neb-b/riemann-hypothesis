module

public import Mathlib
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0158
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive
section
noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory.BinaryRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gram_diag_pos {r : ℕ} (τ : E →+* ℂ) (d : Fin r → E)
    (hd : ∀ i, (τ (d i)).im = 0 ∧ 0 < (τ (d i)).re) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ (Matrix.diagonal d) Q = Matrix.diagonal fun a : Fin r => ((FD.sgn r (a : ℕ) : ℝ) : ℂ) := by
  classical
  set q : Fin r → ℝ := fun i => (Real.sqrt (τ (d i)).re)⁻¹ with hq
  have hq2 : ∀ i, (q i : ℂ) * τ (d i) * (q i : ℂ) = 1 := by
    intro i
    have h1 : τ (d i) = ((τ (d i)).re : ℂ) := Complex.ext rfl (by simp [(hd i).1])
    have h2 : q i * q i * (τ (d i)).re = 1 := by
      rw [hq]
      simp only
      rw [← mul_inv, Real.mul_self_sqrt (hd i).2.le, inv_mul_cancel₀ (hd i).2.ne']
    rw [h1]
    exact_mod_cast (by linarith [h2] : q i * (τ (d i)).re * q i = 1)
  refine ⟨Matrix.diagonal fun i => (q i : ℂ), ?_, ?_⟩
  · rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have : (q i : ℂ) ≠ 0 := fun h => by simpa [h] using hq2 i
    exact this
  · ext a b
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      have hs : FD.sgn r (a : ℕ) = 1 := by simp [FD.sgn, a.isLt]
      simp [hs, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.conj_ofReal]
      rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp only [if_true, Complex.conj_ofReal]
      linear_combination hq2 a
    · simp [hab, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : a = x
      · subst hx
        simp [hab]
      · simp [hx]

end GlobalTheory.BinaryRep

namespace GlobalTheory.BinaryRep

theorem represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n →
    (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) →
    ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  intro K _ _ _ hc a b n ha hb hn hpa hpb hpn
  haveI : IsCMField K := GlobalTheory.OrthoLattice.isCMField_of_star K hc.1 hc.2.1
  let φ0 : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hst : ∀ x : K, star x = FD.cc x := fun x =>
    φ0.injective (by rw [FD.cc, IsCMField.complexEmbedding_complexConj]; exact hc.2.1 φ0 x)
  have hreal : ∀ x : K, star x = x → ∀ τ : K →+* ℂ, (τ x).im = 0 := by
    intro x hx τ
    have h := hc.2.1 τ x
    rw [hx] at h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hne : ∀ x : K, (∀ φ : K →+* ℂ, 0 < (φ x).re) → x ≠ 0 := by
    intro x hx h0
    have := hx φ0
    simp [h0] at this
  have ha0 := hne a hpa
  have hb0 := hne b hpb
  have hn0 := hne n hpn
  have hca : FD.cc a = a := by rw [← hst, ha]
  have hcb : FD.cc b = b := by rw [← hst, hb]
  have hcn : FD.cc n = n := by rw [← hst, hn]
  have hcab : FD.cc (a * b * n) = a * b * n := by
    rw [← hst, star_mul, star_mul, ha, hb, hn]; ring
  set G : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![a, b] with hG
  set G' : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![n, a * b * n] with hG'
  have herm_diag : ∀ d : Fin 2 → K, (∀ i, FD.cc (d i) = d i) →
      ∀ i j, FD.cc (Matrix.diagonal d i j) = Matrix.diagonal d j i := by
    intro d hd i j
    by_cases h : i = j
    · subst h; simp [hd]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), FD.cc]
  have hGh : ∀ i j, FD.cc (G i j) = G j i :=
    herm_diag _ (fun i => by fin_cases i <;> simp [hca, hcb])
  have hG'h : ∀ i j, FD.cc (G' i j) = G' j i :=
    herm_diag _ (fun i => by fin_cases i <;> simp [hcn, hcab])
  have hdG : G.det = a * b := by simp [hG, Matrix.det_diagonal, Fin.prod_univ_two]
  have hdG' : G'.det = n * (a * b * n) := by simp [hG', Matrix.det_diagonal, Fin.prod_univ_two]
  have hpos : ∀ d : Fin 2 → K, (∀ i, star (d i) = d i ∧ ∀ φ : K →+* ℂ, 0 < (φ (d i)).re) →
      ∀ τ : K →+* ℂ, ∀ i, (τ (d i)).im = 0 ∧ 0 < (τ (d i)).re :=
    fun d hd τ i => ⟨hreal _ (hd i).1 τ, (hd i).2 τ⟩
  have habn : star (a * b * n) = a * b * n := by rw [star_mul, star_mul, ha, hb, hn]; ring
  have hpabn : ∀ φ : K →+* ℂ, 0 < (φ (a * b * n)).re := by
    intro φ
    have e : ∀ x : K, star x = x → (φ x : ℂ) = ((φ x).re : ℂ) := fun x hx =>
      Complex.ext rfl (by simp [hreal x hx φ])
    rw [map_mul, map_mul, e a ha, e b hb, e n hn]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_pos (mul_pos (hpa φ) (hpb φ)) (hpn φ)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.QNorm.landherr_and_landherrSt.2) K 2 G G' hGh hG'h
    (by rw [hdG]; exact mul_ne_zero ha0 hb0)
    (by rw [hdG']; exact mul_ne_zero hn0 (mul_ne_zero (mul_ne_zero ha0 hb0) hn0))
    (fun τ => ⟨2,
      gram_diag_pos τ ![a, b] (hpos _ (fun i => by fin_cases i <;> simp [ha, hb, hpa, hpb]) τ),
      gram_diag_pos τ ![n, a * b * n]
        (hpos _ (fun i => by fin_cases i; exacts [⟨hn, hpn⟩, ⟨habn, hpabn⟩]) τ)⟩)
    ⟨n, by rw [hdG', hdG, hcn]; ring⟩
  have h := hγ (Pi.single 0 1) (Pi.single 0 1)
  set v := (γ : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 1 with hv
  refine ⟨v 0, v 1, ?_⟩
  simp only [FD.herm, Fin.sum_univ_two, hG, hG', Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)] at h
  simp [FD.cc] at h
  rw [hst, hst]
  simp only [FD.cc]
  linear_combination h

end GlobalTheory.BinaryRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmSplitPlaceEqOfPrimeEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitUniqSer

theorem splitPlace_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L),
    s.w = s'.w → s = s' :=
  GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq

end GlobalTheory.SplitUniqSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenusStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → (∃ s : Finset (Ideal (𝓞 K)), s.card = fDeg K ∧ (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) ∧ IsCoprime (∏ P ∈ s, P) (conjIdeal (K := K) (∏ P ∈ s, P)) ∧ (∏ P ∈ s, P) * conjIdeal (K := K) (∏ P ∈ s, P) = Ideal.span {(T : 𝓞 K)}) ∧ ∀ L N : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → (N ∈ genus h L ↔ IsIntLat h N ∧ Nonempty ((↥(dual h N) ⧸ N.comap (dual h N).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}))) := by
  first | exact @GlobalTheory.Mass.CyclicGenus.main | exact GlobalTheory.Mass.CyclicGenus.main | (intros; apply GlobalTheory.Mass.CyclicGenus.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.AdaptedExists

theorem exists_complement (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q : ℕ) (he : ∀ y, e (star y) = star (e y))
    {κ : Type} [Fintype κ] [DecidableEq κ] (hI : HasSig I p q)
    (hI₀ : HasSig I₀ (p - Fintype.card κ) (q - Fintype.card κ)) (hn : I.n = I₀.n + 2 * Fintype.card κ)
    (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hΛ : Submodule.IsLattice I.E Λ)
    (hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (I.J *ᵥ x) ∈ (algebraMap (𝓞 I.E) I.E).range)
    (T T' : Matrix (Fin I.n) κ I.E) (B : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (h1 : Tᴴ * I.J * T = 0) (h2 : T'ᴴ * I.J * T' = 0) (h3 : Tᴴ * I.J * T' = 1) (h4 : Tᴴ * I.J * B = 0)
    (h5 : T'ᴴ * I.J * B = 0) (h6 : (Bᴴ * I.J * B).det ≠ 0)
    (h7 : ∀ z ∈ Λ, ∃ y, B *ᵥ y ∈ Λ ∧ (Bᴴ * I.J) *ᵥ (z - B *ᵥ y) = 0) :
    ∃ (γ : GL (Fin I₀.n) I.E) (x₀ : I₀.Gf), (B * γ.1)ᴴ * I.J * (B * γ.1) = I₀.J.map e ∧
      ∀ y, y ∈ lamX I₀ (1, x₀) ↔ ((B * γ.1) *ᵥ fun l => e (y l)) ∈ Λ := by
  obtain ⟨xΛ, hxΛ⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I Λ hΛ (by simpa only [hform_eq] using hdual)
  have hΛfull : Submodule.IsFullLattice I.E Λ :=
    { toIsLattice := hΛ
      span_eq_top := by rw [← hxΛ]; exact (GlobalTheory.PointLattice.lamX_selfDual I (1, xΛ)).2.2.1 }
  have he' : ∀ y, e.symm (star y) = star (e.symm y) := fun y => e.injective (by simp [he])
  set G : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E := (Bᴴ * I.J * B).map e.symm with hG
  have hGe : Bᴴ * I.J * B = G.map e := by ext r s; exact (e.apply_symm_apply _).symm
  have hGd : G.det ≠ 0 := fun h => h6 (by
    rw [hGe]; exact ((e : I₀.E →+* I.E).map_det G).symm.trans (by rw [h, map_zero]))
  have hGh : Gᴴ = G := by
    rw [hG, ← Matrix.conjTranspose_map _ he', ← gram_swap (J_herm I)]
  obtain ⟨L, hL, -, hLd⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J B G Λ (J_herm I) hGe hGd hΛfull hdual h7
  obtain ⟨γ, hγ⟩ := GlobalTheory.FlagMeas.sameKindIsometric I₀.E I₀.cm.cmUnram I₀.n G I₀.J hGh (J_herm I₀) hGd I₀.J_det ⟨L, hL.toIsLattice, hLd⟩
    ⟨I₀.L, Submodule.IsLattice.of_fg I₀.E I₀.L_fg, by simpa only [hform_eq] using I₀.L_dual⟩ (fun φ => by
      refine ⟨_, _, ?_, hasSignature_map I₀ _ _ hI₀ φ⟩
      set ψ : I.E →+* ℂ := φ.comp e.symm.toRingHom
      have hψ : ∀ x, ψ (star x) = star (ψ x) := I.cm.cmUnram.2.1 ψ
      have hm : G.map φ = (B.map ψ)ᴴ * I.J.map ψ * B.map ψ := by rw [map_gram ψ hψ]; rfl
      rw [hm]
      refine hasSignature_complement _ _ p q κ _ (T.map ψ) (T'.map ψ) _ ?_ (hasSignature_map I p q hI ψ) hn ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← Matrix.conjTranspose_map _ hψ, J_herm]
      · rw [map_gram ψ hψ, h1, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h2, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h3, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
      · rw [map_gram ψ hψ, h4, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h5, Matrix.map_zero _ (map_zero ψ)]
      · rw [← hm]
        exact fun h => hGd (φ.injective ((φ.map_det G).trans (h.trans (map_zero φ).symm))))
  set γ' : GL (Fin I₀.n) I.E := Matrix.GeneralLinearGroup.map (e : I₀.E →+* I.E) γ
  have hγ' : γ'.1 = γ.1.map (e : I₀.E →+* I.E) := rfl
  have hT : (B * γ'.1)ᴴ * I.J * (B * γ'.1) = I₀.J.map e := by
    have := map_gram (e : I₀.E →+* I.E) he G γ.1 γ.1
    rw [hγ, ← hγ'] at this
    refine Eq.trans ?_ this
    rw [show G.map (e : I₀.E →+* I.E) = _ from hGe.symm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  obtain ⟨L', hL', hm, hLd'⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J (B * γ'.1) I₀.J Λ (J_herm I) hT I₀.J_det hΛfull hdual
    fun z hz => by
      obtain ⟨y, hy, hy'⟩ := h7 z hz
      have : (B * γ'.1) *ᵥ (γ'⁻¹.1 *ᵥ y) = B *ᵥ y := by
        rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      refine ⟨γ'⁻¹.1 *ᵥ y, by rwa [this], ?_⟩
      rw [this, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hy', mulVec_zero]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I₀ L' hL'.toIsLattice (by simpa only [hform_eq] using hLd')
  exact ⟨γ', x₀, hT, by rwa [hx₀]⟩

theorem exists_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  intro I I₀ e p q a j he hI hp hq hI₀ xf S ⟨h0, hmono, hrk, hsat, hiso⟩
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  simp only [hform_eq] at hdual hiso
  have hn : I.n = I₀.n + 2 * ∑ i, j i := by
    have h1 := (GlobalTheory.FlagMeas.instance_numbers I).2.2.2.2.2 _ _ hI
    have h2 := (GlobalTheory.FlagMeas.instance_numbers I₀).2.2.2.2.2 _ _ hI₀
    omega
  have hle : ∀ k, S k ≤ lamX I (1, xf) := fun k y hy => ((hsat k y).1 hy).1
  have hSfg : (S (Fin.last a)).FG := hfg.of_le (hle _)
  obtain ⟨A, hA⟩ := GlobalTheory.saturatedFlag_splits I.E I.n a S h0 hmono hSfg fun i y hy h => (hsat i y).2 ⟨hle _ hy, h⟩
  obtain ⟨Λ, Ti, hΛ, hS⟩ := exists_blocks I.E I.n a j S A h0 hmono hSfg hrk hA
  set κ := Σ i, Fin (j i)
  have hκ : Fintype.card κ = ∑ i, j i := by simp [κ]
  have hsum : ∀ (M : Matrix (Fin I.n) κ I.E) (u : κ → I.E),
      M *ᵥ u = ∑ i, M.submatrix id (Sigma.mk i) *ᵥ fun s => u ⟨i, s⟩ := fun M u => by
    ext r
    simp [mulVec, dotProduct, Finset.sum_apply, κ, Fintype.sum_sigma]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin I.n) κ I.E, ∀ i, Ti i = T.submatrix id (Sigma.mk i) :=
    ⟨fun r s => Ti s.1 r s.2, fun _ => rfl⟩
  have hlast : ∀ z, z ∈ S (Fin.last a) ↔ ∃ u : κ → I.E, (∀ i, (fun s => u ⟨i, s⟩) ∈ Λ i) ∧ z = T *ᵥ u := fun z => by
    rw [hS]
    refine ⟨fun ⟨u, hu, _, hz⟩ => ⟨fun s => u s.1 s.2, hu, by rw [hsum, hz]; simp only [hT]⟩,
      fun ⟨u, hu, hz⟩ => ⟨_, hu, fun i hi => absurd (Fin.castSucc_lt_last i) hi, by rw [hz, hsum]; simp only [hT]⟩⟩
  have hone : ∀ i, ∀ t ∈ Λ i, Ti i *ᵥ t ∈ S (Fin.last a) := fun i t ht => by
    refine (hS _ _).2 ⟨Pi.single i t, fun k => ?_, fun i hi => absurd (Fin.castSucc_lt_last i) hi, ?_⟩
    · by_cases h : k = i
      · subst h; simpa using ht
      · simp [h]
    · rw [Finset.sum_eq_single i] <;> simp +contextual
  set W := Submodule.span I.E (S (Fin.last a) : Set (Fin I.n → I.E)) with hW
  have hrange : LinearMap.range T.mulVecLin = W := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun z hz => ?_)
    · rintro _ ⟨u, rfl⟩
      rw [mulVecLin_apply, hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) ≤ W.comap (Ti i).mulVecLin :=
        Submodule.span_le.2 fun t ht => Submodule.subset_span (hone i t ht)
      rw [← hT]
      have hsp := Submodule.IsFullLattice.span_eq_top (self := hΛ i)
      exact this (hsp ▸ Submodule.mem_top)
    · obtain ⟨u, -, rfl⟩ := (hlast z).1 hz
      exact ⟨u, rfl⟩
  have hdim : Module.finrank I.E W = Fintype.card κ := by
    have := telescope a j (fun k => Formalism.HN.rkK (S k)) hrk
    simp only [h0] at this
    rw [hκ]
    rw [show Formalism.HN.rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 by
      rw [Formalism.HN.rkK, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot], zero_add] at this
    exact this
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (I.J *ᵥ y) = 0 := fun x hx y hy => by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact hiso x hx y hy
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h h' => simp [h, h']
    | add_right x y z _ _ _ h h' => simp [mulVec_add, h, h']
    | smul_left c x y _ _ h => simp [h]
    | smul_right c x y _ _ h => simp [mulVec_smul, h]
  obtain ⟨W', hW'iso, hW'dim, hW'nd, hsplit⟩ := GlobalTheory.WittInt.main I.E I.cm.cmUnram I.n I.J (J_herm I) I.J_det _
    (Submodule.IsLattice.of_fg I.E hfg) hdual W hWiso
  obtain ⟨T', B, hrange', h3, h6, hB⟩ := exists_witt I.E I.n I₀.n κ I.J T W W' (J_herm I) I.J_det (hκ ▸ hn) hrange hdim
    (hW'dim.trans hdim) hWiso hW'iso hW'nd
  have mT : ∀ u, T *ᵥ u ∈ W := fun u => hrange ▸ ⟨u, rfl⟩
  have mT' : ∀ u, T' *ᵥ u ∈ W' := fun u => hrange' ▸ ⟨u, rfl⟩
  have h1 : Tᴴ * I.J * T = 0 := gram_eq_zero _ _ _ fun x y => hWiso _ (mT x) _ (mT y)
  have h2 : T'ᴴ * I.J * T' = 0 := gram_eq_zero _ _ _ fun x y => hW'iso _ (mT' x) _ (mT' y)
  have h4 : Tᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_left (mT x))
  have h5 : T'ᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_right (mT' x))
  have hdec : ∀ z ∈ lamX I (1, xf), ∃ u u' y, T *ᵥ u ∈ S (Fin.last a) ∧ T' *ᵥ u' ∈ lamX I (1, xf) ∧
      B *ᵥ y ∈ lamX I (1, xf) ∧ z = T *ᵥ u + T' *ᵥ u' + B *ᵥ y := fun z hz => by
    obtain ⟨x, hx, y, hy, hxW, hyW, h⟩ := hsplit z hz
    obtain ⟨w, hw⟩ := (hB _).2 h
    have hxS := (hsat _ x).2 ⟨hx, hxW⟩
    rw [← hrange] at hxW
    rw [← hrange'] at hyW
    obtain ⟨u, rfl⟩ := hxW
    obtain ⟨u', rfl⟩ := hyW
    simp only [mulVecLin_apply] at hw hx hy hxS
    exact ⟨u, u', w, hxS, hy, hw ▸ sub_mem (sub_mem hz hx) hy, by rw [hw]; abel⟩
  obtain ⟨γ, x₀, hG, hx₀⟩ := exists_complement I I₀ e p q he hI (hκ ▸ hI₀) (hκ ▸ hn) _ (Submodule.IsLattice.of_fg I.E hfg) hdual T T' B
    h1 h2 h3 h4 h5 h6 fun z hz => by
      obtain ⟨u, u', y, -, -, hy, rfl⟩ := hdec z hz
      refine ⟨y, hy, ?_⟩
      rw [add_sub_cancel_right, mulVec_add, mulVec_mulVec, mulVec_mulVec, gram_swap (J_herm I) T,
        gram_swap (J_herm I) T', h4, h5]
      simp
  have hsub : ∀ {l : Type} (M : Matrix (Fin I.n) κ I.E) (N : Matrix (Fin I.n) l I.E) {k₁ k₂ : Type}
      (f : k₁ → κ) (g : k₂ → l),
      (M.submatrix id f)ᴴ * I.J * N.submatrix id g = (Mᴴ * I.J * N).submatrix f g := fun M N _ _ f g => by
    ext r s
    simp [Matrix.mul_apply]
  have hpair : ∀ i t u', star (Ti i *ᵥ t) ⬝ᵥ (I.J *ᵥ (T' *ᵥ u')) = star t ⬝ᵥ fun s => u' ⟨i, s⟩ := fun i t u' => by
    rw [form_mulVec, hT, ← Matrix.submatrix_id_id T', hsub, h3]
    congr 1
    ext s
    simp [mulVec, dotProduct, Matrix.one_apply]
  refine ⟨Λ, x₀, Ti, fun i => T'.submatrix id fun s => ⟨i, s⟩, B * γ.1, he, hn, hΛ, fun i k => ⟨?_, ?_, fun h => ?_⟩,
    fun i => ⟨?_, ?_, ?_⟩, hG, fun z => ⟨fun hz => ?_, ?_⟩, hS⟩
  · rw [hT, hT, hsub, h1]; rfl
  · rw [hsub, h2]; rfl
  · rw [hT, hsub, h3]
    ext r s
    simp [h]
  · rw [hT, hsub, h3]
    ext r s
    simp [Matrix.one_apply]
  · rw [← Matrix.mul_assoc, hT, ← Matrix.submatrix_id_id B, hsub, h4]
    simp
  · rw [← Matrix.mul_assoc, ← Matrix.submatrix_id_id B, hsub, h5]
    simp
  · obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := hdec z hz
    obtain ⟨v, hv, hv'⟩ := (hlast _).1 hu
    have hy' : ((B * γ.1) *ᵥ fun l => e (e.symm ((γ⁻¹.1 *ᵥ y) l))) = B *ᵥ y := by
      simp only [e.apply_symm_apply]
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    refine ⟨fun i s => v ⟨i, s⟩, fun i s => u' ⟨i, s⟩, fun l => e.symm ((γ⁻¹.1 *ᵥ y) l), hv, fun i t ht => ?_,
      (hx₀ _).2 (hy' ▸ hy), ?_⟩
    · rw [← hpair]
      exact (hdual _).1 hu' _ (hle _ (hone i t ht))
    · rw [hy', hv', hsum T, hsum T']
      simp only [hT]
  · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
    refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => hle _ (hone i _ (hu i))) ?_) ((hx₀ y).1 hy)
    have e1 := hsum T' fun s => u' s.1 s.2
    refine e1 ▸ (hdual _).2 fun w hw => ?_
    obtain ⟨v, v', y', hv, -, -, rfl⟩ := hdec w hw
    obtain ⟨t, ht, ht'⟩ := (hlast _).1 hv
    rw [star_add, star_add, add_dotProduct, add_dotProduct, form_mulVec _ T', form_mulVec _ B, h2,
      gram_swap (J_herm I) T', h5, ht', hsum T, star_sum, sum_dotProduct]
    simp only [← hT, hpair, conjTranspose_zero, zero_mulVec, dotProduct_zero, add_zero]
    exact Subring.sum_mem _ fun i _ => hu' i _ (ht i)

end GlobalTheory.AdaptedExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicTorusMeasureStabiliserHaar
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem omT_stab_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ a : ℕ, 1 ≤ a → 2 * a < n → ∀ (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 → ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (μ' : Measure (stabT (AF F) σ J X0)), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧ μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ a ha1 ha2 X0 hT hdet μ hμ
  obtain ⟨νX, hν⟩ := PI.VolStabS.Assembly.exOmT_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μ', hμ'H, hμ'C⟩ := PI.VolStabS.exStab_of_nu PI.VolStabS.Assembly.nuInv_holds
    PI.VolStabS.nuFin_holds
    (PI.VolStabS.nuNeZero_of_dens PI.VolStabS.archPos_holds PI.VolStabS.locPos_holds
      (PI.VolStabS.densAA_of_open PI.VolStabS.volAA_holds PI.VolStabS.hensAA_holds
        PI.VolStabS.idxH_holds PI.VolStabS.cntAA_holds) PI.VolStabS.qvSum_holds)
    F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  exact ⟨νX, μ', hν, hμ'H, hμ'C⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIndependentSubfamilySameISup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem indep_subfamily_of_disjoint_or_le : ∀ (ι M : Type) [AddCommGroup M] [Module ℂ M] (N : ι → Submodule ℂ M), (∀ i (J : Finset ι), Disjoint (N i) (⨆ j ∈ J, N j) ∨ N i ≤ ⨆ j ∈ J, N j) → ∀ F : Finset ι, ∃ J ⊆ F, (⨆ j ∈ J, N j) = (⨆ j ∈ F, N j) ∧ ∀ f f' : ι → M, (∀ j ∈ J, f j ∈ N j) → (∀ j ∈ J, f' j ∈ N j) → ∑ j ∈ J, f j = ∑ j ∈ J, f' j → ∀ j ∈ J, f j = f' j := by
  intro ι M _ _ N h F
  classical
  refine Finset.induction_on F ?_ ?_
  · exact ⟨∅, Finset.Subset.refl _, rfl, by simp⟩
  · intro i F hi ih
    obtain ⟨J, hJF, hJsup, huniq⟩ := ih
    have hiJ : i ∉ J := fun hh => hi (hJF hh)
    rcases h i J with hd | hle
    · refine ⟨insert i J, Finset.insert_subset_insert _ hJF, ?_, ?_⟩
      · rw [Finset.iSup_insert, Finset.iSup_insert, hJsup]
      · intro f f' hf hf' hsum
        rw [Finset.sum_insert hiJ, Finset.sum_insert hiJ] at hsum
        have hdiff : f i - f' i = ∑ j ∈ J, f' j - ∑ j ∈ J, f j := by
          rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
        have hmem : f i - f' i ∈ N i ⊓ ⨆ j ∈ J, N j := by
          refine ⟨Submodule.sub_mem _ (hf i (Finset.mem_insert_self _ _))
            (hf' i (Finset.mem_insert_self _ _)), ?_⟩
          rw [hdiff]
          exact Submodule.sub_mem _
            (Submodule.sum_mem_biSup fun j hj => hf' j (Finset.mem_insert_of_mem hj))
            (Submodule.sum_mem_biSup fun j hj => hf j (Finset.mem_insert_of_mem hj))
        rw [hd.eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
        rw [hmem] at hsum
        have hJs : ∑ j ∈ J, f j = ∑ j ∈ J, f' j := add_left_cancel hsum
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hmem
        · exact huniq f f' (fun k hk => hf k (Finset.mem_insert_of_mem hk))
            (fun k hk => hf' k (Finset.mem_insert_of_mem hk)) hJs j hj
    · refine ⟨J, hJF.trans (Finset.subset_insert _ _), ?_, huniq⟩
      rw [Finset.iSup_insert, ← hJsup]
      exact (sup_eq_right.mpr hle).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLatticeOfUnimodularLandherr
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem exists_orthoLattice_of_unimodular : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) :=
  fun K _ _ _ hK => GlobalTheory.OrthoLattice.hasOrtho K hK

end GlobalTheory.Mass
end

