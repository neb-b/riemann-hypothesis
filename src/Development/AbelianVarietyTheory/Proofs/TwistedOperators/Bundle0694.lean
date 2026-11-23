module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingIntegralIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepCommuteAtGoodPlacesAlgebraicVectors
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0583
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.Onto

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_hasSig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_hasSig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_factor {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

theorem map_darbAlg_eq_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) (hM : M.IsGood ψ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) (hpr : (M.Pol ψ τ).map pr = ⊤)
    (hpv : ∀ v, (GlobalTheory.WeilM.SB _).map (pv v) = ⊤) :
    (darbAlg M ψ τ).map (liftPure M pr pv s) = ⊤ := by
  classical
  have H := GlobalTheory.T.weil_model_projection_factorisation σ Y Z M ψ hM P pr N pv s hs
  have hq : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      liftPure M pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
    unfold liftPure
    rw [dite_eq_left H]
    exact H.choose_spec
  have key : ∀ (x : P) (ξ : ∀ v, N v), Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      x ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT s ξ ∈ (darbAlg M ψ τ).map (liftPure M pr pv s) := by
    intro x ξ hξ
    obtain ⟨f, hf, rfl⟩ : x ∈ (M.Pol ψ τ).map pr := hpr ▸ Submodule.mem_top
    have h1 : ∀ v, ∃ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), pv v φ = ξ v ∧ (pv v (M.vac v) = ξ v → φ = M.vac v) := by
      intro v
      by_cases hv : pv v (M.vac v) = ξ v
      · exact ⟨M.vac v, (hM.vac v).1, hv, fun _ => rfl⟩
      · obtain ⟨φ, hφ, e⟩ : ξ v ∈ (GlobalTheory.WeilM.SB _).map (pv v) := (hpv v) ▸ Submodule.mem_top
        exact ⟨φ, hφ, e, fun k => absurd k hv⟩
    choose φ hφ hφ1 hφ2 using h1
    have h2 : ∀ᶠ v in Filter.cofinite, φ v = M.vac v := by
      have h3 : ∀ᶠ v in Filter.cofinite, ξ v = s v := hξ
      filter_upwards [hs, h3] with v a b using hφ2 v (a.trans b.symm)
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, Submodule.subset_span ⟨f, φ, hf, hφ, h2, rfl⟩, ?_⟩
    rw [hq f φ hφ h2, funext hφ1]
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  have hy : y ∈ Submodule.span ℂ {z | ∃ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ ∧ z = GlobalTheory.SmallThetaModules.pureT s ξ} := by
    rw [GlobalTheory.SmallThetaModules.pureT_span]; trivial
  rw [SetLike.mem_coe]
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨ξ, hξ, rfl⟩ := hz; exact key x ξ hξ
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [TensorProduct.tmul_smul]; exact Submodule.smul_mem _ c ha

theorem map_thetaLift {D : D7} {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (S : Submodule ℂ ((Fin m × Fin k → AF D.host.F) → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pD : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] P)
    (hS : S ≤ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k))
    (T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ))
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ)
    (hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0) :
    (S.map T).map (thetaLift Mo ψ G e S pD) = S.map pD := by
  have H : ∃ q : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P, ∀ Ψ ∈ S, q (GlobalTheory.TripleRead.thO Mo ψ G e Ψ) = pD Ψ := by
    obtain ⟨q, hq⟩ := exists_factor T S (fun x hx => hinj x (hS hx)) pD
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hS hΨ)]; exact hq Ψ hΨ⟩
  have hq : ∀ Ψ ∈ S, thetaLift Mo ψ G e S pD (T Ψ) = pD Ψ := by
    intro Ψ hΨ
    rw [hT Ψ (hS hΨ)]
    unfold thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec Ψ hΨ
  ext x
  constructor
  · rintro ⟨_, ⟨Ψ, hΨ, rfl⟩, rfl⟩
    exact ⟨Ψ, hΨ, (hq Ψ hΨ).symm⟩
  · rintro ⟨Ψ, hΨ, rfl⟩
    exact ⟨T Ψ, ⟨Ψ, hΨ, rfl⟩, hq Ψ hΨ⟩

end GlobalTheory.TripleAssembly.Onto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawIdentityWeilTriple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.RegGood

theorem isTriple_atPlace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hv : X.Good v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple { B with v₁ := v, τ₁ := t } G X om om' :=
  { h with
    base := { h.base with }
    geo := { h.geo with hV := { h.geo.hV with }, hV' := { h.geo.hV' with }, hW := { h.geo.hW with } }
    chars := { h.chars with good := hv } }

end GlobalTheory.RegGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly

variable {D : D7}

theorem toUX_one (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) : GlobalTheory.TripleRead.toUX X e hJ 1 = 1 := by
  apply Subtype.ext; apply Units.ext
  show (GlobalTheory.TripleRead.toUX X e hJ 1).1.1 = 1
  rw [GlobalTheory.TripleRead.toUX_val]
  simp [Formalism.L2.Theta.mt]


end GlobalTheory.TripleAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly.LieInv

theorem exists_factor {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_hasSig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_hasSig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ darbAlg M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ τ ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 hΨ
  have hg' := fun i => (g i).2
  simp only [Set.mem_setOf_eq] at hg'
  choose f φ hf hφ hφv hfe using hg'
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hφv i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfe i]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

variable {D : D7}

theorem toUX_one (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) : GlobalTheory.TripleRead.toUX X e hJ 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.TripleRead.toUX_val]
  simp [Formalism.L2.Theta.mt]

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem conjU_mul (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} (c : D.host.E) (hc : J = c • M.gram)
    (g h : GA D M) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (g * h) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc h := by
  apply Subtype.ext
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul]
  rfl

theorem conjU_one' (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} (c : D.host.E) (hc : J = c • M.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc 1 = 1 := by
  apply Subtype.ext
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one]
  rfl

theorem finTens_cA (z : AE D) : GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.cA D z) =
    Algebra.TensorProduct.map (AlgHom.id D.host.F _) D.sp.cm.sig (GlobalTheory.LFun.finTens D.host.F D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem conjU_mem_UAt (M : HSp D) (Yd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (c : D.host.E)
    (hc : Yd.J = c • M.gram) {g : GA D M} (hg : g ∈ GinfC M) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Yd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have hf : finHom M g = 1 := hg
  have hent : ∀ a b, GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.mt M g a b) =
      (1 : Matrix (Fin M.rank) (Fin M.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    have := congrArg (fun k : GL (Fin M.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf
    exact this
  ext i j
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g) i j = Formalism.L2.Theta.cA D (Formalism.L2.Theta.mt M g i j) := rfl
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  apply GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu
  rw [hm, map_sub, finTens_cA, hent, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem exists_line_conjU (θ : InfFam D) (M : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin M.rank) (Fin M.rank) ℂ)
    (hθ : IsInfFam θ) (hY : Y ∈ lieAt M τ) (Yd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (c : D.host.E)
    (hc : Yd.J = c • M.gram) :
    ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Yd, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y t) := by
  let γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Yd.J :=
    { toFun := fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y (Multiplicative.toAdd t))
      map_one' := by
        show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y 0) = 1
        rw [GlobalTheory.Mem.Lift.oneP_zero hθ, conjU_one']
      map_mul' := fun s t => by
        show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
        rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, conjU_mul] }
  refine ⟨γ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · exact (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU M c hc).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_toAdd)
  · exact conjU_mem_UAt M Yd c hc (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY _).1

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

end GlobalTheory.TripleAssembly.LieInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly.ReadDerB

private theorem pure_smul_twisted_operators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ)
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ τ ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = M.vac v)) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
    exact ⟨1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, hv⟩, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h₁ j
      · simpa using h₂ j
    · simp [Fin.sum_univ_add]
  | smul c x _ hx =>
    obtain ⟨m, f, φ, h, rfl⟩ := hx
    refine ⟨m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ τ).smul_mem c (h i).1, (h i).2⟩, ?_⟩
    simp [Finset.smul_sum, pure_smul_twisted_operators]

end GlobalTheory.TripleAssembly.ReadDerB

end
end

