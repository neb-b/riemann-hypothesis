module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CharLaws

variable {D : D7}

section Conj

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem embedded_anisotropic_inv_fixes_isotropic (k : GA D S₀) : mt S (d.emb0 k)⁻¹ ⬝ d.jX = d.jX := by
  rw [← map_inv]; exact d.wittDecomp_anisotropicEmbedding_inclX k⁻¹

theorem witt_isotropic_projection_embedded_anisotropic_mul {m : ℕ} (k : GA D S₀) (x : Mx D S.rank m) : d.pX ⬝ (mt S (d.emb0 k) ⬝ x) = d.pX ⬝ x := by
  rw [← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding]

theorem blockX_conj (k : GA D S₀) (n : GA D S) :
    blockX d (d.emb0 k * n * (d.emb0 k)⁻¹) = blockX d n := by
  rw [blockX, blockX, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [embedded_anisotropic_inv_fixes_isotropic, witt_isotropic_projection_embedded_anisotropic_mul]

theorem coefX_conj (k : GA D S₀) (n : GA D S) (z : Fin S₀.rank → D.host.E)
    (hz : mt S₀ k⁻¹ *ᵥ ratV z = ratV z) :
    coefX d z (d.emb0 k * n * (d.emb0 k)⁻¹) = coefX d z n := by
  rw [coefX, coefX, mt_mul, mt_mul, ← map_inv]
  simp only [Matrix.mul_assoc]
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, witt_isotropic_projection_embedded_anisotropic_mul]
  have e : d.pX ⬝ (mt S n ⬝ (d.j0 ⬝ mt S₀ k⁻¹)) = d.pX ⬝ (mt S n ⬝ d.j0) ⬝ mt S₀ k⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, hz]

theorem conj_mem_flagN (k : GA D S₀) {n : GA D S} (hn : n ∈ flagN d) :
    d.emb0 k * n * (d.emb0 k)⁻¹ ∈ flagN d := by
  have hi := (isIsoSub_e d).1
  change n ∈ NFlag S d.e at hn
  change _ ∈ NFlag S d.e
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e hi] at hn ⊢
  have he : mt S (d.emb0 k) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX k
  have he' : mt S (d.emb0 k)⁻¹ ⬝ d.e.map (incA D) = d.e.map (incA D) := embedded_anisotropic_inv_fixes_isotropic d k
  rw [mt_mul, mt_mul]
  exact hn.conj he he' (mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end Conj

section Cont

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem continuous_psiBes (hψ : Continuous ψ) (θ : D.host.E) (z : Fin S₀.rank → D.host.E) :
    Continuous (psiBes ψ d θ z) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hm : Continuous (mt S) := GlobalTheory.MixModel.continuous_mt S
  have hb : Continuous fun g => blockX d g := continuous_const.matrix_mul (hm.matrix_mul continuous_const)
  have hc : Continuous fun g => coefX d z g :=
    (continuous_const.matrix_mul (hm.matrix_mul continuous_const)).matrix_mulVec continuous_const
  have hu : Continuous fun g => upSum (blockX d g) := by
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hb)
    · exact continuous_const
  have hd : Continuous fun g => ell D ρ ⬝ᵥ coefX d z g := continuous_const.dotProduct hc
  exact hψ.comp (ht.comp (continuous_const.mul (hu.add hd)))

end Cont

end GlobalTheory.CharLaws

namespace GlobalTheory.CharLaws

variable {D : D7}

section Rat

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem upSum_rat (N : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    upSum (rat N) = incA D (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then N i j else 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [upSum, rat, Matrix.map_apply, map_sum, apply_ite (incA D), map_zero]

theorem ratV_dotProduct {m : ℕ} (a b : Fin m → D.host.E) : ratV a ⬝ᵥ ratV b = incA D (a ⬝ᵥ b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, ratV, map_sum, map_mul]

theorem ell_eq : ell D ρ = ratV (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0) := by
  funext i
  simp only [ell, ratV]
  split_ifs <;> simp

theorem simpleSum_rat (z : Fin S₀.rank → D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) :
    ∃ x : D.host.E, simpleSum d z γ = incA D x := by
  obtain ⟨M, hM⟩ := (mem_GQ_iff S γ).1 hγ
  have hM' : rat M = mt S γ := hM
  have hb : blockX d γ = rat (d.qX * (M * d.e)) := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  have hc : coefX d z γ = ratV ((d.qX * (M * d.i₀)) *ᵥ z) := by
    rw [coefX, ← hM', ratV_mulVec, rat_mul, rat_mul]; rfl
  rw [simpleSum, hb, hc, upSum_rat, ell_eq, ratV_dotProduct, ← map_add (f := _)]
  exact ⟨_, rfl⟩

theorem psiBes_rat (hψ : ∀ a : D.host.F, ψ (algebraMap D.host.F (AF D.host.F) a) = 1) (θ : D.host.E)
    (z : Fin S₀.rank → D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) : psiBes ψ d θ z γ = 1 := by
  obtain ⟨x, hx⟩ := simpleSum_rat d z hγ
  rw [psiBes, hx, ← map_mul, psiE, GlobalTheory.BesselChar.trace_incA]
  exact hψ _

end Rat

end GlobalTheory.CharLaws

namespace GlobalTheory.CharLaws

variable {D : D7}

section Bes

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

theorem emb_vecB (a : GA D A) (ζ : Fin L.rank → D.host.E) :
    mt S₀ (o.emb (a, 1)) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
  rw [vecB, ratV_mulVec, Matrix.mulVec_mulVec]
  change (mt S₀ (o.emb (a, 1)) ⬝ o.jB) *ᵥ _ = o.jB *ᵥ _
  rw [o.emb_jB, mt_one, Matrix.mul_one]

theorem psiBes_conj (θ : D.host.E) (ζ : Fin L.rank → D.host.E) (n : GA D S) (h : GA D A) :
    psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n := by
  have hz : mt S₀ (o.emb (h, 1))⁻¹ *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    rw [← map_inv, Prod.inv_mk, inv_one]; exact emb_vecB o h⁻¹ ζ
  rw [embA_apply, psiBes, psiBes, simpleSum, simpleSum, blockX_conj, coefX_conj d _ n _ hz]

theorem psiFlag_conj (n : GA D S) (h : GA D S₀) :
    psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n := by
  rw [psiFlag, psiFlag, blockX_conj]

theorem embA_conj_mem (h : GA D A) {n : GA D S} (hn : n ∈ flagN d) :
    embA d o h * n * (embA d o h)⁻¹ ∈ flagN d :=
  conj_mem_flagN d _ hn

theorem mem_besGrp (g : GA D S) : g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h := by
  constructor
  · intro hg
    let K : Subgroup (GA D S) :=
      { carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
        one_mem' := ⟨1, one_mem _, 1, by rw [map_one, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨n₁, hn₁, h₁, rfl⟩ ⟨n₂, hn₂, h₂, rfl⟩
          refine ⟨n₁ * (embA d o h₁ * n₂ * (embA d o h₁)⁻¹), mul_mem hn₁ (embA_conj_mem d o h₁ hn₂), h₁ * h₂, ?_⟩
          rw [map_mul]; group
        inv_mem' := by
          rintro _ ⟨n, hn, h, rfl⟩
          refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, embA_conj_mem d o h⁻¹ (inv_mem hn), h⁻¹, ?_⟩
          rw [map_inv]; group }
    have hle : besGrp d o ≤ K := sup_le (fun n hn => ⟨n, hn, 1, by rw [map_one, mul_one]⟩)
      (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, (one_mul _).symm⟩)
    exact hle hg
  · rintro ⟨n, hn, h, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem embRel_embA (ι : A.V →ₗ[D.host.E] S.V) (hι : frameMat S A ι = d.i₀ * o.iA) (h : GA D A) :
    EmbRel S A ι (embA d o h) h := by
  rw [EmbRel, hι]
  refine ⟨?_, fun x hx => ?_⟩
  · change mt S (d.emb0 (o.emb (h, 1))) ⬝ rat (d.i₀ * o.iA) = rat (d.i₀ * o.iA) ⬝ mt A h
    rw [rat_mul]
    change mt S (d.emb0 (o.emb (h, 1))) ⬝ (d.j0 ⬝ o.jA) = d.j0 ⬝ o.jA ⬝ mt A h
    rw [← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  · have hι₂ : frameMat S₀ A (Matrix.toLin A.frame S₀.frame o.iA) = o.iA := LinearMap.toMatrix_toLin _ _ _
    have hA := (o.embRel_left _ hι₂ h).2
    rw [hι₂] at hA
    have hw : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) o.iA * S₀.gram) *ᵥ (d.q0 *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec, cT_sig, HypDec.q0]
      have e : o.iAᴴ * S₀.gram * (S₀.gram⁻¹ * (d.i₀ᴴ * S.gram)) = (d.i₀ * o.iA)ᴴ * S.gram := by
        rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S₀.gram,
          Matrix.mul_nonsing_inv _ (gram_isUnit_det S₀), Matrix.one_mul, Matrix.mul_assoc]
      rw [e, ← cT_sig]; exact hx
    have h1 : mt S₀ (o.emb (h, 1)) *ᵥ ratV (d.q0 *ᵥ x) = ratV (d.q0 *ᵥ x) := hA _ hw
    have h2 : d.p0 *ᵥ ratV x = ratV (d.q0 *ᵥ x) := (ratV_mulVec _ _).symm
    have h3 := congrArg (· *ᵥ ratV x) d.sum_eq_one
    change mt S (d.emb0 (o.emb (h, 1))) *ᵥ ratV x = ratV x
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h3
    rw [d.unitaryMatrix_wittCoreEmbedding]
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    rw [h2, h1, ← h2]
    exact h3

end Bes

end GlobalTheory.CharLaws

namespace GlobalTheory.MixPer

theorem charLaws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (θ : D.host.E), (∀ z, Continuous (psiBes ψ d θ z)) ∧ (∀ z, ∀ γ ∈ GQ S, psiBes ψ d θ z γ = 1) ∧ (∀ n h, psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n) ∧ (∀ n h, psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n) ∧ (∀ g, g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h) ∧ ∀ ι : A.V →ₗ[D.host.E] S.V, frameMat S A ι = d.i₀ * o.iA → ∀ h, EmbRel S A ι (embA d o h) h := by
  intro D ψ hψ S S₀ A L ρ d o ζ θ
  exact ⟨fun z => GlobalTheory.CharLaws.continuous_psiBes ψ d hψ.1 θ z,
    fun z γ hγ => GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ z hγ,
    fun n h => GlobalTheory.CharLaws.psiBes_conj ψ d o θ ζ n h,
    fun n h => GlobalTheory.CharLaws.psiFlag_conj ψ d n h,
    fun g => GlobalTheory.CharLaws.mem_besGrp d o g,
    fun ι hι h => GlobalTheory.CharLaws.embRel_embA d o ι hι h⟩

end GlobalTheory.MixPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockNormMinorProductDeltaAtEmbeddingPos
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockDelta

variable {D : D7}

theorem minor_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k =>
      (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have hev := congrArg (MvPolynomial.eval fun y : FVar D m n =>
    if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at hev
  have hI : (MvPolynomial.eval fun y : FVar D m n =>
      if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.isLt
    have hβ := β.isLt
    have hc : a + (β : ℕ) < m ∧ b + (α : ℕ) < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    unfold varF
    rw [dite_eq_left hc, MvPolynomial.eval_X]
    dsimp only
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 (Fin.ext (by omega))).elim
    · exact (h1 (by subst h2; omega)).elim
    · rfl
  rw [hI, Matrix.det_one] at hev
  exact one_ne_zero hev

theorem minorPlus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (k : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
    (minorPlus τ k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorPlus
  have h := minor_ne_zero (D := D) (m := m) (n := n) τ 0 0 k (by omega) (by omega)
  simpa only [zero_add] using h

theorem minorMinus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p k : ℕ) (hm : p + k ≤ m) (hn : k ≤ n) :
    (minorMinus τ p k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorMinus
  exact minor_ne_zero τ p (n - k) k hm (by omega)

theorem deltaAt_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p : ℕ) (ap : ℕ → ℕ) (q : ℕ) (am : ℕ → ℕ)
    (hpq : p + q ≤ m) (hmn : m ≤ n) :
    (deltaAt τ p ap q am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold deltaAt
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorPlus_ne_zero τ (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorMinus_ne_zero τ p (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega

theorem delta_ne_zero {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta
  exact Finset.prod_ne_zero_iff.mpr fun τ _ => deltaAt_ne_zero τ _ _ _ _ (hpq τ) hmn

theorem fock_self_pos {σ : Type*} (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ Formalism.E.fock P P = (a : ℂ) := by
  refine ⟨∑ m ∈ P.support, Complex.normSq (P.coeff m) * (Formalism.A.mfact m : ℝ), ?_, ?_⟩
  · refine Finset.sum_pos (fun m hm => mul_pos ?_ ?_) ?_
    · exact Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm)
    · unfold Formalism.A.mfact
      exact Nat.cast_pos.mpr (Finset.prod_pos fun i _ => Nat.factorial_pos _)
    · exact Finset.nonempty_iff_ne_empty.mpr fun he => hP (MvPolynomial.support_eq_empty.mp he)
  · unfold Formalism.E.fock
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.ofReal_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_natCast]

end GlobalTheory.FockDelta


open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in
theorem GlobalTheory.FockDelta.fock_deltaAtEmb_pos :
    ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∃ a : ℝ, 0 < a ∧
      Formalism.E.fock (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) = (a : ℂ) := by
  intro D i σ
  apply GlobalTheory.FockDelta.fock_self_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb
  have hi := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
  apply GlobalTheory.FockDelta.delta_ne_zero
  · intro ρ
    exact le_of_eq (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _)
  · rw [hW]
    exact r_le_V i
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAway
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceStable

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem symplO_of_place {p : Place D} {x y : WO S T} (hx : wAt p x = x) (hy : wAt p y = 0) : symplO S T x y = 0 := by
  rw [← hx, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.2.1 p, ← wAt_eq_smul, hy,
    GlobalTheory.SplitScalar.symplO_zero_right]

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (_root_.GlobalTheory.PlaceTensor.idem_spec D).1 p]

theorem wAt_wAt_ne {p q : Place D} (h : q ≠ p) (w : WO S T) : wAt q (wAt p w) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.1 q p h, zero_smul]

theorem heisO_swap {u w : WO S T} (h : symplO S T u w = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w (heisO ψ S T u f) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, h, AddChar.map_zero_eq_one, one_smul]

theorem isLatVac_map {Λ : AddSubgroup (WO S T)} {A : (WO S T → ℂ) → WO S T → ℂ} {f : WO S T → ℂ}
    (h : ∀ u ∈ Λ, heisO ψ S T u (A f) = A (heisO ψ S T u f)) (hf : IsLatVac (heisO ψ S T) Λ f) :
    IsLatVac (heisO ψ S T) Λ (A f) :=
  ⟨fun u hu => by rw [h _ (Λ.nsmul_mem hu 2), hf.1 u hu], fun e he u hu hh => by rw [h u hu, hf.2 e he u hu hh]⟩

theorem latO_empty {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {P : FinPl D → Prop}
    (hP : ∀ v, ¬ P v) {u : WO S T} (hu : u ∈ latO S T LS LT P) : u = 0 := by
  have h : latO S T LS LT P ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨α, -, h0, a, -, s, -, t, -, rfl⟩
    have hα : α = 0 := RestrictedProduct.ext _ _ fun v => h0 v (hP v)
    subst hα
    refine AddSubgroup.mem_bot.2 (Matrix.ext fun i j => ?_)
    exact TensorProduct.zero_tmul _ _
  exact AddSubgroup.mem_bot.1 (h hu)

theorem wAt_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    wAt (.inr τ) (lineAt θ τ z t : WO S T) = lineAt θ τ z t := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, h1, h2⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨-, -, -, -, h3, -, h4⟩ := _root_.GlobalTheory.PlaceTensor.idem_spec D
  refine funext fun i => funext fun j => ?_
  show idem D (.inr τ) * lineAt θ τ z t i j = lineAt θ τ z t i j
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [← sub_eq_zero, ← RingHom.map_sub]
    refine GlobalTheory.FockCompare.ThetaCont.infPart_eq_zero hσ _ fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul]
    by_cases h : τ' = τ
    · subst h
      rw [(h4 θ hθ τ').1, one_mul, sub_self]
    · have h5 : θ τ' (infPart D (lineAt θ τ z t i j)) = 0 := by
        have := h2 t τ'
        rw [if_neg h] at this
        exact congrFun (congrFun this i) j
      rw [h5, mul_zero, sub_self]
  · have h5 : finPart D (lineAt θ τ z t i j) = 0 := congrFun (congrFun (h1 t) i) j
    rw [RingHom.map_mul, h5, mul_zero]

theorem dRho_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T w g) =
      heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [heisO, ← deriv_const_mul_field]
  congr 1
  funext t
  rw [heisO_swap (symplO_of_place (wAt_lineAt hθ τ z t) hw)]
  rfl

theorem isFockVacAt_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ} {f : WO S T → ℂ}
    (hf : IsFockVacAt (heisO ψ S T) θ τ J f) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T w f) := by
  intro z
  have h := congrArg (GlobalTheory.SplitScalar.heisL ψ S T w) (hf z)
  rw [annih, map_add (f := _), map_smul, map_zero] at h
  rw [annih, dRho_heisO hθ hw, dRho_heisO hθ hw]
  exact h

theorem heis_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (q : Place D) (w : WO S T), wAt q w = 0 → VacAt ψ θ S T sS sT ΛS ΛT q f → VacAt ψ θ S T sS sT ΛS ΛT q (heisO ψ S T w f)) ∧ ∀ (p : Place D), IsLocal ψ θ S T sS sT ΛS ΛT p f → (∀ w : WO S T, IsLocal ψ θ S T sS sT ΛS ΛT p (heisO ψ S T (wAt p w) f)) ∧ (∀ (c : ℂ) g, IsLocal ψ θ S T sS sT ΛS ΛT p g → IsLocal ψ θ S T sS sT ΛS ΛT p (c • f + g)) ∧ ∀ τ : D.what₂.Tau, p = .inr τ → ∀ z, IsLocal ψ θ S T sS sT ΛS ΛT p (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT hψ hθ f hf
  refine ⟨fun q w hw hv => ?_, fun p hp => ⟨fun w => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _, ?_, fun τ hτ => ?_⟩,
    fun c g hg => ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul c hf) hg.1, ?_, fun τ hτ z => ?_⟩,
    fun τ hτ z => ⟨GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hf, ?_, fun τ' hτ' z' => ?_⟩⟩⟩
  · cases q with
    | inl v =>
      refine isLatVac_map (fun u hu => heisO_swap (symplO_of_place ?_ hw) f) hv
      have h := (_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT _ u hu (.inl v)).2.1
      exact (sub_eq_zero.1 (latO_empty (fun v' h' => h'.2 (by rw [h'.1])) h)).symm
    | inr τ => exact isFockVacAt_heisO hθ hw hv
  · refine isLatVac_map (fun u hu => (heisO_swap (symplO_of_place (wAt_wAt p w) ?_) f).symm) hp.2.1
    exact (_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT _ u hu p).2.2 fun _ h => h
  · exact isFockVacAt_heisO hθ (wAt_wAt_ne hτ w) (hp.2.2 τ hτ)
  · have key : ∀ u, heisO ψ S T u f = f → heisO ψ S T u g = g → heisO ψ S T u (c • f + g) = c • f + g := fun u h1 h2 => by
      rw [← GlobalTheory.SplitScalar.heisL_apply, map_add (f := _), map_smul, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, h1, h2]
    exact ⟨fun u hu => key _ (hp.2.1.1 u hu) (hg.2.1.1 u hu),
      fun e he u hu hh => key _ (hp.2.1.2 e he u hu hh) (hg.2.1.2 e he u hu hh)⟩
  · have h1 := hp.2.2 τ hτ z
    have h2 := hg.2.2 τ hτ z
    have hc := GlobalTheory.WeilVacMove.isTheta_smul c hf
    rw [annih] at h1 h2 ⊢
    rw [GlobalTheory.FockIndep.dRho_add hψ hθ _ _ hc hg.1, GlobalTheory.FockIndep.dRho_add hψ hθ _ _ hc hg.1,
      GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ c hf, GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ c hf, smul_add, smul_comm,
      add_add_add_comm, ← smul_add, h1, h2, smul_zero, add_zero]
  · refine isLatVac_map (fun u hu => (dRho_heisO hθ ?_ z f).symm) hp.2.1
    exact (_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT _ u hu (.inr τ)).2.2 fun _ _ => Sum.inl_ne_inr
  · have hne : τ' ≠ τ := fun h => hτ' (by rw [h, hτ])
    have hc : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' y (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' y f) := fun y => by
      rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ' y τ z hf, GlobalTheory.FockIndep.omDir, if_neg hne, Complex.ofReal_zero, mul_zero,
        zero_smul, zero_add]
    have ht := fun y => GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ' y hf
    have h1 := hp.2.2 τ' hτ' z'
    have h0 := GlobalTheory.FockIndep.dRho_smul hψ hθ τ z 0 hf
    rw [zero_smul, zero_smul] at h0
    rw [annih] at h1 ⊢
    rw [hc, hc, ← GlobalTheory.FockIndep.dRho_smul hψ hθ τ z _ (ht _),
      ← GlobalTheory.FockIndep.dRho_add hψ hθ τ z (ht _) (GlobalTheory.WeilVacMove.isTheta_smul _ (ht _)), h1, h0]

end GlobalTheory.PlaceStable

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZeroStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k))
    (N : Subgroup (GL (Fin r) k)) (ν : Measure N) [ν.IsMulLeftInvariant] (H : Subgroup (GL (Fin r) 𝓀[k])),
    NoFixed τ H → ∀ x : GL (Fin r) k,
    (∀ v ∈ H, ∃ n ∈ N, ∃ hn : x * n * x⁻¹ ∈ KO k (Fin r), GlobalTheory.LocGL.redK k (Fin r) ⟨x * n * x⁻¹, hn⟩ = v) →
    ∀ w : GL (Fin r) k, ∫ u : N, idemGL k μ τ (x * u * w) ∂ν = 0 := by
  first | exact @GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero | exact GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero | (intros; apply GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero <;> assumption)
end

