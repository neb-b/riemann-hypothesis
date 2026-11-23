module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceComponentArchLineComplexStructure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
noncomputable section

namespace GlobalTheory.CartanLinTransfer

variable {D : D7}

theorem phi_smul_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AE D) :
    θ τ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 1 • a)) = θ τ (infPart D a) := by
  rw [GlobalTheory.ArchLineSum.infPart_smul, map_mul, GlobalTheory.ArchLineSum.theta_realAd hθ, Complex.ofReal_one, one_mul]

theorem phi_incM {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : Type} (J : Matrix m n D.host.E) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).map ((θ τ).comp (infPart D)) = J.map (tauE D τ) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, ← (hθ τ).1]
  rfl

theorem cartH_gram {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
  have hu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hJ : (Formalism.REAL.Jm (A.ε τ))ᴴ = Formalism.REAL.Jm (A.ε τ) := by
    ext a b; by_cases h : a = b
    · subst h; simp [Formalism.REAL.Jm, Matrix.conjTranspose_apply]; split_ifs <;> simp
    · simp [Formalism.REAL.Jm, Matrix.conjTranspose_apply, h, Ne.symm h]
  have hJJ : Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ) = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext a; split_ifs <;> simp
  rw [← A.fr_gram τ, Fr.cart, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_nonsing_inv]
  have h1 : ((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ = 1 := Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hu.star)
  have h2 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        simp only [Matrix.mul_assoc]
    _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * ((A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ))) * A.fr τ := by
        rw [h1, h2, Matrix.mul_one, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem cart_frSgn' (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (frSgn ε A).cart τ = (if ε then -1 else 1 : ℂ) • A.cart τ := by
  cases ε
  · simp [Fr.cart, frSgn]
  · have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
      ext a b
      by_cases hab : a = b
      · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
      · simp [Formalism.REAL.Jm, hab]
    show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = _
    rw [h, Matrix.mul_neg, Matrix.neg_mul]; simp [Fr.cart]

end GlobalTheory.CartanLinTransfer

namespace GlobalTheory.CartanLinTransfer

theorem map_conj_conj {m n : Type} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
  ext i j; simp

theorem map_conj_smul {m n : Type} (c : ℂ) (M : Matrix m n ℂ) :
    (c • M).map (starRingEnd ℂ) = (starRingEnd ℂ c) • M.map (starRingEnd ℂ) := by
  ext i j; simp

theorem map_conj_transpose {m n : Type} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j; simp [Matrix.conjTranspose_apply]

theorem alg_step {m n k : ℕ} (e : Fin m ≃ Fin k) (Ac G : Matrix (Fin n) (Fin n) ℂ) (Bc : Matrix (Fin m) (Fin m) ℂ)
    (P P' : Matrix (Fin n) (Fin k) ℂ) (s : ℂ) (hs : starRingEnd ℂ s = s) (hAG : Acᴴ * G = G * Ac)
    (h : P'.map (starRingEnd ℂ) =
      Complex.I • ((-s) • Ac * P.map (starRingEnd ℂ) * ((Matrix.reindex e e Bc).map (starRingEnd ℂ))ᵀ)) :
    P'ᵀ.submatrix e id * (s • G) = Complex.I • (Bc * (Pᵀ.submatrix e id * (s • G)) * (s • Ac)) := by
  have h2 := congrArg (fun M => M.map (starRingEnd ℂ)) h
  simp only [map_conj_conj, map_conj_smul, Matrix.map_mul, Matrix.transpose_map, Complex.conj_I, map_neg, hs] at h2
  rw [h2]
  have hsub : (Matrix.reindex e e Bc).submatrix e e = Bc := by
    ext i j; simp [Matrix.reindex_apply]
  have hprod : ∀ K : Matrix (Fin n) (Fin n) ℂ,
      (Matrix.reindex e e Bc * (Pᵀ * K)).submatrix e id = Bc * (Pᵀ.submatrix e id * K) := by
    intro K
    rw [← Matrix.submatrix_mul_equiv (Matrix.reindex e e Bc) (Pᵀ * K) e e id, hsub]
    congr 1
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul, map_conj_transpose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul, Pi.smul_apply, smul_smul]
  rw [hprod]
  simp only [Matrix.mul_assoc, hAG]
  congr 1
  ring

end GlobalTheory.CartanLinTransfer


open GlobalTheory.CartanLinTransfer in
theorem GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u u' : Matrix (Fin S.rank) (Fin d) (AE D),
      (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
        Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ)) →
    ∀ τ, compAt θ τ (GlobalTheory.VacTransfer.archLine cS u' 1) =
      cplxO ((frSgn ε A).cart τ) (B.cart τ) (compAt θ τ (GlobalTheory.VacTransfer.archLine cS u 1)) := by
  intro D θ hθ ε S X A B d e Bs Vs Ws hBs cS hcS u u' hu τ
  obtain ⟨τw, hemb, hV, hW⟩ := hBs (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
  set w : InfinitePlace D.host.F := InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) with hw
  have hembR : (Bs.emb w).1 = (starRingEnd ℂ).comp (tauE D τw) := RingHom.ext hemb
  have hτ : τw = τ := by
    apply (GlobalTheory.CMTypePlaces.places_bijective D).1
    have h2 := (Bs.emb w).2
    rw [hembR] at h2
    have h3 := congrArg InfinitePlace.mk h2
    have hc : (starRingEnd ℂ).comp ((tauE D τw).comp (algebraMap D.host.F D.host.E)) =
        ComplexEmbedding.conjugate ((tauE D τw).comp (algebraMap D.host.F D.host.E)) :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [InfinitePlace.mk_embedding, RingHom.comp_assoc, hc, InfinitePlace.mk_conjugate_eq] at h3
    exact h3
  rw [hτ] at hembR hV hW
  have hcomp : ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding := by
    rw [← hembR]; exact (Bs.emb w).2
  have hE : Bs.emb w = ⟨(starRingEnd ℂ).comp (tauE D τ), hcomp⟩ := Subtype.ext hembR
  have hpi : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = starRingEnd ℂ (((θ τ).comp (infPart D)) y) := by
    intro y; rw [hE]; exact GlobalTheory.ConjInfExp.piInf_eq θ hθ τ w hcomp y
  have hmap : ∀ v : Matrix (Fin S.rank) (Fin d) (AE D),
      v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (v.map ((θ τ).comp (infPart D))).map (starRingEnd ℂ) := by
    intro v; ext i j; simp only [Matrix.map_apply, hpi]
  have hu1 := hu w
  rw [hmap, hmap, hV, hW] at hu1
  have hz : ∀ v : Matrix (Fin S.rank) (Fin d) (AE D), compAt θ τ (GlobalTheory.VacTransfer.archLine cS v 1) =
      (v.map ((θ τ).comp (infPart D)))ᵀ.submatrix e id * ((if ε then -1 else 1 : ℂ) • gramAt D S τ) := by
    intro v
    show (cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 1 • v)).map ((θ τ).comp (infPart D)) = _
    rw [hcS, Matrix.map_mul, phi_incM hθ]
    congr 1
    · ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, id,
        RingHom.comp_apply, phi_smul_realAd hθ]
    · ext i j
      cases ε <;> simp [gramAt, Matrix.smul_apply]
  have hsgn : (if ε then 1 else -1 : ℂ) = -(if ε then -1 else 1 : ℂ) := by cases ε <;> simp
  have hs : starRingEnd ℂ (if ε then -1 else 1 : ℂ) = (if ε then -1 else 1 : ℂ) := by cases ε <;> simp
  rw [hsgn] at hu1
  rw [hz, hz, cart_frSgn', cplxO]
  exact alg_step e (A.cart τ) (gramAt D S τ) (B.cart τ) _ _ _ hs (cartH_gram A τ) hu1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerDerivRelationOfHeisenbergDeriv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

open GlobalTheory.ThetaTransform

noncomputable section

namespace GlobalTheory.LineDerivTransfer

theorem hasDerivAt_heisV_of {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) (hΦ'm : Φ' ∈ GlobalTheory.WeilM.schA F (Fin N)) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (hΦ'd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0) (w : VA F N) :
    HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := GlobalTheory.ThetaDeriv.decay_majorant hF (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ :=
    GlobalTheory.ThetaDeriv.decay_majorant hF (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (GlobalTheory.SWQ.rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (GlobalTheory.SWQ.rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (GlobalTheory.SWQ.rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (GlobalTheory.ThetaDeriv.hasDerivAt_schr hF ψ hM hΦ'd (GlobalTheory.SWQ.rat ξ + w.1) t).const_mul (ph ξ))
    (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this

theorem thV_smul {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (c : ℂ) (Φ : (Fin N → AF F) → ℂ) : thV ψ (c • Φ) = c • thV ψ Φ := by
  funext w
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

end GlobalTheory.LineDerivTransfer


open GlobalTheory.LineDerivTransfer in
theorem GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  intro D ψ hψ S T JB ξ hB κ _ co hrat Φ hΦ L L' hL hL0 hL' hL0' c hrel x
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  let e := numCoord co σ
  have he : ∀ w w', symplO S T w w' = symV (e w) (e w') := fun w w' => by
    rw [symplO_eq_symp rfl hB, co.form]
    simp only [e, symV, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
  obtain ⟨-, -, hfin, -⟩ := _root_.GlobalTheory.AdelicCoord.coord D T.rank S.rank _ e
  have hc : Continuous e := (_root_.GlobalTheory.AdelicCoord.coord D T.rank S.rank _ e).1
  have hΦσ := comp_mem_schA σ hΦ
  have key : ∀ L : ℝ →+ WO S T, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∃ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin (Fintype.card κ)),
        (∀ x, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) (Φ' (x ∘ σ.symm)) 0) ∧
        (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
          thV ψ Φ' ∘ e := by
    intro L hL hL0
    have hM : IsRealLine (e.toLinearMap.toAddMonoidHom.comp L) := ⟨hc.comp hL, fun t => (hfin _).1 (hL0 t)⟩
    obtain ⟨Φ', hm, hd⟩ := GlobalTheory.ThetaDeriv.exists_deriv_schr hR ψ hψ.1 hM hΦσ
    refine ⟨Φ', hm, fun x => ?_, funext fun w => ?_⟩
    · have h : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) =
          fun t => GlobalTheory.WeilM.schr ψ (e.toLinearMap.toAddMonoidHom.comp L t) (fun y => Φ (y ∘ σ)) (x ∘ σ.symm) := by
        funext t
        simp only [GlobalTheory.WeilM.schr, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          LinearEquiv.coe_coe, e, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
        congr 2
        funext i
        simp
      rw [h]
      exact hd _
    · rw [thetaTr_eq co σ]
      have h : (fun t : ℝ => heisO ψ S T (L t) (thV ψ (fun y => Φ (y ∘ σ)) ∘ e) w) =
          fun t => heisV ψ (e.toLinearMap.toAddMonoidHom.comp L t) (thV ψ (fun y => Φ (y ∘ σ))) (e w) :=
        funext fun t => congrFun (heisO_comp he (L t) _) w
      rw [show numCoord co σ = e from rfl, h]
      exact (hasDerivAt_heisV_of ψ hR hψ.1 hΦσ hm hM hd (e w)).deriv
  obtain ⟨Φ₁, hm₁, hd₁, hh₁⟩ := key L hL hL0
  obtain ⟨Φ₂, hm₂, hd₂, hh₂⟩ := key L' hL' hL0'
  rw [hh₁, hh₂] at hrel
  have h2 : thV ψ Φ₂ = thV ψ (c • Φ₁) := by
    rw [thV_smul]
    funext v
    obtain ⟨w, rfl⟩ := e.surjective v
    exact congrFun hrel w
  have h3 := thV_injOn hR hψ.1 hm₂ (Submodule.smul_mem _ c hm₁) h2
  rw [(hd₂ x).deriv, (hd₁ x).deriv, h3]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrTheta

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

theorem placeModel_induction (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {T₁ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₁)
    (p : (WO S T → ℂ) → Prop) (p0 : p 0) (padd : ∀ f g, p f → p g → p (f + g)) (psmul : ∀ (c : ℂ) f, p f → p (c • f))
    (px : ∀ x ∈ half S T e, ∀ f, p f → p (heisO ψ S T x f))
    (py : ∀ y ∈ half S T (cA D e), ∀ f, p f → p (heisO ψ S T y f)) (pf : p f₀)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : p (T₁ Φ) := by
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e)) (Λ ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e Λ
    have s1 : IsSBHalf e Λ fun t => ψ (symplO S T t y) * halfInd e Λ t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e Λ t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := h₁.vac
    rw [one_smul] at v1
    rw [e1, h₁.trans _ s1 x ((isHalf_iff S T).2 hx), h₁.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    exact px x hx _ (py y hy _ pf)
  | zero => rw [LinearMap.map_zero]; exact p0
  | add f g _ _ hf hg => rw [LinearMap.map_add (f := _)]; exact padd _ _ hf hg
  | smul c f _ hf => rw [LinearMap.map_smul]; exact psmul _ _ hf

theorem isTheta_heis_fin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {a : WO S T} (ha : a.map (infPart D) = 0) : IsThetaFunO ψ S T (heisO ψ S T a f) := by
  have := GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf Unit {()} (fun _ => a) (fun _ => 1)
    fun _ _ => ha
  rwa [Finset.sum_singleton, one_smul] at this

theorem isTheta_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → infPart D e = 0 → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ Φ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ → IsThetaFunO ψ S T (Tm Φ) := by
  intro D ψ hψ S T ΛS ΛT hS hT e he hinf f₀ hf₀ Tm hTm Φ hΦ
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hz : IsThetaFunO ψ S T 0 := by
    refine ⟨?_, ?_, continuous_const, ?_⟩
    · intro γ w; simp only [Pi.zero_apply, mul_zero]
    · exact ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
    · intro k L _ _ w; exact contDiff_const
  have hadd : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T (f + g) := by
    intro f g hf hg
    refine ⟨?_, ?_, hf.cont.add hg.cont, ?_⟩
    · intro γ w; simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    · intro k L h1 h2 w; exact (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)
  have hsmul : ∀ (c : ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T (c • f) := by
    intro c f hf
    refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
    · intro γ w; rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    · obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    · intro k L h1 h2 w; exact contDiff_const.mul (hf.smooth k L h1 h2 w)
  refine placeModel_induction ψ _ (fun u hu y hy => ?_) (fun x hx h => ?_)
    (fun k hk => ?_) (fun y hy => ?_) hTm (IsThetaFunO ψ S T) hz
    hadd hsmul
    (fun x hx f hf => isTheta_heis_fin hψ hf (infPart_of_half hinf ((isHalf_iff S T).2 hx)))
    (fun y hy f hf => isTheta_heis_fin hψ hf (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))) hf₀ hΦ
  · exact (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  · refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  · exact exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))

end GlobalTheory.SchrTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModuleMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.CoinvLine

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (hψ : IsStdChar D ψ (-1)) [Nonempty D.what₂.Tau] {W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X) {Ψ : WO W₁ X → ℂ}
    (hΨ : Ψ ∈ algF ψ θ false A₁ B) : IsThetaFunO ψ W₁ X Ψ := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact (GlobalTheory.LieScalar.ptF_laws hθ hψ (frSgn false A₁) B hf).1 (Classical.arbitrary _) P
  | zero => exact Formalism.IndefR.Fock.CCR.theta_zero ψ W₁ X
  | add x y _ _ hx hy => exact Formalism.IndefR.Fock.CCR.theta_add hx hy
  | smul c x _ hx => exact Formalism.IndefR.Fock.CCR.theta_smul hx c

end GlobalTheory.CoinvLine
end
end

