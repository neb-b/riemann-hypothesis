module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WittSig

open Matrix
open scoped ComplexOrder

theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, conjTranspose_apply]

theorem Jpq_conjTranspose (q p : ℕ) : (Formalism.UG.Jpq q p)ᴴ = Formalism.UG.Jpq q p := by
  simp [Formalism.UG.Jpq, fromBlocks_conjTranspose]

theorem le_of_isotropic {n : Type} [Fintype n] [DecidableEq n] {q p r : ℕ} (J : Matrix n n ℂ)
    (hS : Formalism.UG.HasSignature J q p) (X Y : Matrix n (Fin r) ℂ) (hxx : Xᴴ * J * X = 0)
    (hxy : Xᴴ * J * Y = 1) : r ≤ p := by
  obtain ⟨e, P, hP⟩ := hS
  rw [cT_conj_eq] at hP
  set Q : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := (↑(P⁻¹) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) with hQdef
  have hPQ : (P : Matrix _ _ ℂ) * Q = 1 := by simp [Q]
  have hJ : J.reindex e e = Qᴴ * Formalism.UG.Jpq q p * Q := by
    rw [← hP]
    have h1 : Qᴴ * (P : Matrix _ _ ℂ)ᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
    calc J.reindex e e = (Qᴴ * (P : Matrix _ _ ℂ)ᴴ) * J.reindex e e * ((P : Matrix _ _ ℂ) * Q) := by
          rw [h1, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  set Z := Q * X.reindex e (Equiv.refl _) with hZdef
  set W := Q * Y.reindex e (Equiv.refl _) with hWdef
  have key : ∀ A B : Matrix n (Fin r) ℂ,
      (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) = Aᴴ * J * B := by
    intro A B
    have : (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) =
        (A.reindex e (Equiv.refl _))ᴴ * (Qᴴ * Formalism.UG.Jpq q p * Q) * B.reindex e (Equiv.refl _) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, ← hJ]
    ext i j
    simp [Matrix.mul_apply, Matrix.reindex_apply, conjTranspose_apply]
    rw [← Fintype.sum_sum_type (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k (e.symm x)) * B (e.symm x) j)]
    exact e.symm.sum_comp (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k x) * B x j)
  have hZZ : Zᴴ * Formalism.UG.Jpq q p * Z = 0 := by rw [hZdef, key, hxx]
  have hWZ : Wᴴ * Formalism.UG.Jpq q p * Z = 1 := by
    have h := key X Y
    rw [hxy, ← hZdef, ← hWdef] at h
    have h2 := congrArg conjTranspose h
    simpa [conjTranspose_mul, Jpq_conjTranspose, Matrix.mul_assoc] using h2
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin p → ℂ) := (Z.submatrix Sum.inr id).mulVecLin
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set u := Z *ᵥ c with hu
    have hlow : ∀ i, u (Sum.inr i) = 0 := fun i => by
      have := congrFun hc i
      simpa [L, u, mulVec, dotProduct, submatrix] using this
    have h0 : star u ⬝ᵥ (Formalism.UG.Jpq q p *ᵥ u) = 0 := by
      have : star c ⬝ᵥ ((Zᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c) = 0 := by rw [hZZ]; simp
      rw [← this, hu, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    have hup : (fun i => u (Sum.inl i)) = 0 := by
      rw [← dotProduct_star_self_eq_zero, ← h0]
      simp [Formalism.UG.Jpq, dotProduct, mulVec, Fintype.sum_sum_type, hlow, Matrix.one_apply]
    have hu0 : u = 0 := by
      funext x
      rcases x with i | i
      · exact congrFun hup i
      · exact hlow i
    calc c = (Wᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c := by rw [hWZ, one_mulVec]
      _ = (Wᴴ * Formalism.UG.Jpq q p) *ᵥ u := by rw [hu, mulVec_mulVec]
      _ = 0 := by rw [hu0, mulVec_zero]
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem wittIndex_le_neg {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}
    (hS : Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) {r : ℕ}
    {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf) : r ≤ p := by
  have hc := (GlobalTheory.AdelicU.isCMExt_host D).2.2.2 (tauE D τ)
  have hmap : ∀ {a b : ℕ} (A : Matrix (Fin M.rank) (Fin a) D.host.E)
      (B : Matrix (Fin M.rank) (Fin b) D.host.E),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * M.gram * B).map (tauE D τ) =
        (A.map (tauE D τ))ᴴ * gramAt D M τ * B.map (tauE D τ) := by
    intro a b A B
    rw [Matrix.map_mul, Matrix.map_mul, gramAt]
    congr 2
    ext i j
    simp [Formalism.UG.cT, conjTranspose_apply, hc]
  apply le_of_isotropic (gramAt D M τ) hS (Xf.map (tauE D τ)) (Yf.map (tauE D τ))
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittSig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegratedOperatorNormalizedIndicatorProdFixed
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem integralOp_normInd_fix : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, IsOpen (K' v : Set (GLoc D.sp.cm.sig V.gram v))) → (∀ v, K' v ≤ Kv V v) → (∀ᶠ v in cofinite, K' v = Kv V v) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W), (∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x) → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)))) P → P x = x := by
  intro D V μf hH h1 ν hν K' hO hle hcof W _ _ σ x hx P hP
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  set c : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ :=
    fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)) with hc
  have hcpt : ∀ v, IsCompact (K' v : Set (GLoc D.sp.cm.sig V.gram v)) := fun v =>
    (isCompact_stabLoc _ _ (frameLat V) v).of_isClosed_subset ((K' v).isClosed_of_isOpen (hO v)) (hle v)
  have hpos : ∀ v, (μf v).real (K' v : Set (GLoc D.sp.cm.sig V.gram v)) ≠ 0 := fun v => by
    have := hH v
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(hO v).measure_ne_zero (μf v) ⟨1, (K' v).one_mem⟩, (hcpt v).measure_lt_top.ne⟩
  have hint : ∀ v, ∫ y, c v y ∂μf v = 1 := fun v => by
    simp only [hc, normInd, Pi.smul_apply]
    rw [integral_smul]
    erw [integral_indicator_const (μ := μf v) (1 : ℂ) (hO v).measurableSet]
    simp only [Complex.real_smul, smul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (hpos v))
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) c := by
    refine ⟨fun v => Submodule.smul_mem _ _ (indicator_mem_SB (hO v) (hcpt v)), ?_⟩
    filter_upwards [hcof, h1] with v hv hv1
    simp only [hc, normInd, unitLoc, hv]
    simp [Measure.real, hv1]
  have hI : ∫ g, finFn V c g ∂ν = 1 := by
    rw [hν.2 c hfam]
    simp [hint]
  have hsupp : ∀ g : GfC V, finFn V c g ≠ 0 → ∀ v, finLoc V v g ∈ K' v := by
    intro g hg v
    have hfin : (Function.mulSupport fun v => c v (proj D.sp.cm.sig V.gram v (g : GA D V))).Finite :=
      Filter.eventually_cofinite.1 ((hfam.2.and (eventually_proj_mem_stabLoc _ _ (frameLat V) (g : GA D V))).mono
        fun v hv => by show c v _ = 1; rw [hv.1, unitLoc, indicator_of_mem hv.2, Pi.one_apply])
    by_contra hv
    apply hg
    refine finprod_eq_zero _ v ?_ hfin
    change normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)) (finLoc V v g) = 0
    simp [normInd, Set.indicator_of_notMem hv]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  have e : (fun g => finFn V c g * l (σ g x)) = fun g => finFn V c g * l x := by
    funext g
    by_cases h : finFn V c g = 0
    · simp [h]
    · rw [hx g (hsupp g h)]
  rw [map_sub, (hP x l).2, e, integral_mul_const, hI, one_mul, sub_self]

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleRead

variable {D : D7}

def toUX (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨⟨(mt X g).submatrix e e, (mt X g⁻¹).submatrix e e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]; exact Matrix.submatrix_one_equiv e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]; exact Matrix.submatrix_one_equiv e⟩, by
    subst hJ
    have k : (mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (mt X g).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
      have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    show ((mt X g).submatrix e e)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) *
      ((mt X g).submatrix e e).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((X.gramᵀ).submatrix e e) = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ).submatrix e e := rfl
    have e2 : ((mt X g).submatrix e e).map (cA D) = ((mt X g).map (cA D)).submatrix e e := rfl
    rw [e1, e2, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, k]⟩

theorem toUX_val (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : (toUX X e hJ g).1.1 = (mt X g).submatrix e e := rfl

end GlobalTheory.TripleRead

namespace GlobalTheory.TripleRead

variable {D : D7}

structure IsReading (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  ψ : Bs.ψ = ψ

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Γ.V.θ w = A.cart τ ∧ Γ.V'.θ w = -A₁.cart τ ∧
    Γ.W.θ w = ((B.cart τ).submatrix e e).map conj

  α : Xc.α = α

  β : Xc.β = β

def ptO {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin m) (AE D)) :
    Matrix (Fin m) (Fin k) (AE D) :=
  ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹)ᵀ).submatrix id e

def thO {m k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) {d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ) (x : Matrix (Fin d) (Fin m) (AE D)) : ℂ :=
  GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ (ptO G e x) Φ)

def IsTransp (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {M X : HSp D} {k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Z) (ω : WRep M X) (e : Fin k ≃ Fin X.rank)
    (gM : GA D M → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (gX : GA D X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Z.J) : Prop :=
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), ∀ g h,
    thO Mo ψ (sgn ε M).gram e (om (gM g, gX h) Φ) = ω (g, h) (thO Mo ψ (sgn ε M).gram e Φ)

end GlobalTheory.TripleRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRestrictedFiniteTensorFamilyTypeIdempotents
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

variable {D : D7} {V : HSp D}

theorem levelFam_open_compact (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧
      IsCompact (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) := by
  by_cases hu : v = U.u
  · subst hu
    rw [levelFam_u]
    exact ⟨U.frame.isOpen_iwahori, U.frame.isCompact_iwahori⟩
  by_cases hv : v ∈ T.S
  · have e : levelFam T U v = kerSub T ⟨v, hv⟩ := by
      rw [levelFam, Function.update_of_ne hu, dite_eq_left hv]
    rw [e]
    have ho : IsOpen (kerSub T ⟨v, hv⟩ : Set (GLoc D.sp.cm.sig V.gram v)) := by
      rw [kerSub, Subgroup.coe_map]
      exact (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v).isOpenMap_subtype_val _
        (T.frame ⟨v, hv⟩).isOpen_ker_red
    refine ⟨ho, (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ ho) ?_⟩
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rw [levelFam_of_notMem T U hv hu]
    exact ⟨isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v, isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v⟩

theorem isFinFamily_fam : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V)
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) →
    (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → U.u ∉ T.S → ∀ A,
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fam T U μf A) := by
  intro D V T U μf _ h1 _ A
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v ∈ T.S ∧ v ∈ A
    · rw [fam_of_mem T U μf A hv.1 hv.2]
      exact (T.frame ⟨v, hv.1⟩).idem_mem _ _
    · rw [fam_of_not T U μf A hv, normInd]
      obtain ⟨ho, hc⟩ := levelFam_open_compact T U v
      exact Submodule.smul_mem _ _ (indicator_mem_SB ho hc)
  · filter_upwards [T.S.eventually_cofinite_notMem, eventually_cofinite_ne U.u, h1] with v hS hU hK
    rw [fam_of_not T U μf A (fun h => hS h.1), levelFam_of_notMem T U hS hU, normInd, measureReal_def]
    funext g
    simp only [Pi.smul_apply, unitLoc]
    rw [hK]
    simp

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProducts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem meanX_prod_zero_eq : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  intro D V W a b P Q hP hQ hiso ψ hψ μ 𝓨 hμ F₁ F₁' F₂ F₂' h₁ h₁' h₂ h₂' H
  obtain ⟨k, B, horth, hdec, huniq, hrat, hsep⟩ := _root_.GlobalTheory.IsoCompl.ratCompl D V W a b P Q hP hQ hiso ψ hψ
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  obtain ⟨η, 𝓩, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 k
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 := hμ
  have hν2 : IsAddFundamentalDomain (ratL W V) 𝓕 ν := hν.2.1
  obtain ⟨κ, hκ, hU⟩ := _root_.GlobalTheory.IsoMean.integral_coef_eq_mul_meanX D V W a b P Q hP hQ hiso k B horth hdec huniq hrat ψ hψ μ 𝓨 hμ' η 𝓩 hη.1 hη.2.1 ν 𝓕
    hν.1 hν2 (_root_.GlobalTheory.IsoMean.integrable_coef D V W a b P Q hP hQ hiso ψ hψ μ hμ.1 ν 𝓕 hν.1 hν2)
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  set ι := GlobalTheory.IsoMean.cplx V W B with hι
  have hιrat : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ι c ∈ ratL W V := by
    rintro _ ⟨c, rfl⟩
    exact ⟨_, (GlobalTheory.IsoMean.cplx_rat V W B c).symm⟩
  have hT := @GlobalTheory.ThetaClosed.isThetaFunO_heisO_all D ψ hψ V W

  have hcomp : ∀ (w ξ : WO V W), symplOH V W ξ w = 0 → ∀ G : WO V W → ℂ,
      heisO ψ V W (w + ξ) G = heisO ψ V W ξ (heisO ψ V W w G) := by
    intro w ξ h G
    funext u
    simp only [heisO]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, l2, l1, h, add_zero, add_comm (symplOH V W u w),
      show u + ξ + w = u + (w + ξ) by abel]

  have hcoef : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∫ y, (∫ u in 𝓕, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) ∂μ =
        κ * ∫ z in 𝓩, ψ (symplO V W (ι z) (ι c)) *
          (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z))) ∂η := by
    intro c hc G G' hG hG'
    have e1 : ∀ y, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G =
        heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) (heisO ψ V W (ι c) G) := fun y =>
      hcomp _ _ (by rw [skew, hH0 _ _ (horth c y), neg_zero]) G
    simp only [e1]
    rw [hU _ G' (hT hG (ι c)) hG']
    congr 1
    congr 1
    funext z
    rw [GlobalTheory.IsoMean.meanX_heisO_rat V W P Q μ 𝓨 ψ G hG (ι c) (hιrat c hc) (horth c) (ι z) (horth z)]
    ring
  set g : (WO V W → ℂ) → (WO V W → ℂ) → Mx D 1 k → ℂ := fun G G' z =>
    GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z)) with hg
  have hιc : Continuous ι := GlobalTheory.IsoMean.continuous_cplx V W B
  have hgc : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (g G G') :=
    fun G G' hG hG' => ((_root_.GlobalTheory.IsoMean.continuous_meanX D V W a b P Q ψ hψ μ 𝓨 hμ' G hG).comp hιc).mul
      ((_root_.GlobalTheory.IsoMean.continuous_meanX D V W a b P Q ψ hψ μ 𝓨 hμ' G' hG').comp hιc).star
  have hgp : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ z, g G G' (γ + z) = g G G' z := by
    intro G G' hG hG' γ hγ z
    simp only [hg]
    rw [show ι (γ + z) = ι γ + ι z from GlobalTheory.IsoMean.cplx_add V W B γ z]
    exact GlobalTheory.IsoMean.meanX_mul_star_rat V W P Q μ 𝓨 ψ hψ G G' hG hG' (ι γ) (hιrat γ hγ) (horth γ) (ι z)
  have hχ1 : ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (ι γ) (ι c)) = 1 :=
    fun γ hγ => (hsep γ).2 hγ
  have hchar : ∀ c z z', ψ (symplO V W (ι (z + z')) (ι c)) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z') (ι c)) := by
    intro c z z'
    rw [show ι (z + z') = ι z + ι z' from GlobalTheory.IsoMean.cplx_add V W B z z', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l1, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hchar2 : ∀ c c' z, ψ (symplO V W (ι z) (ι (c + c'))) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z) (ι c')) := by
    intro c c' z
    rw [show ι (c + c') = ι c + ι c' from GlobalTheory.IsoMean.cplx_add V W B c c', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l2, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hχc : ∀ c, Continuous fun z => ψ (symplO V W (ι z) (ι c)) := by
    intro c
    have h := (GlobalTheory.FinTranslate.continuous_symplOH V W (ι c)).comp hιc
    have e : (fun z => ψ (symplO V W (ι z) (ι c))) = fun z => ψ (symplOH V W (ι z) (ι c) + symplOH V W (ι z) (ι c)) := by
      funext z; rw [GlobalTheory.IsoMean.symplO_eq_add]
    rw [e]
    exact hψ.1.1.comp (h.add h)
  have hint : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      IntegrableOn (fun z => ψ (symplO V W (ι z) (ι c)) * g G G' z) 𝓩 η := by
    intro c hc G G' hG hG'
    refine GlobalTheory.MixModel.covolOne_integrableOn hη _ ((hχc c).mul (hgc G G' hG hG')) fun γ hγ z => ?_
    rw [hchar, hχ1 γ hγ c hc, one_mul, hgp G G' hG hG' γ hγ z]
  have key := _root_.GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (Mx D 1 k) (GlobalTheory.MixModel.ratMx D 1 k) K hK hKc (GlobalTheory.MixModel.ratMx D 1 k)
    (fun c z => ψ (symplO V W (ι z) (ι c))) (fun c => hχc c) (fun c z z' => hchar c z z')
    (fun c c' z => by exact hchar2 c c' z)
    (fun z => by
      show ψ (symplO V W (ι z) (ι 0)) = 1
      have h0 : symplOH V W (ι z) 0 = 0 := by
        have h := l2 (ι z) 0 0
        rw [add_zero] at h
        linear_combination -h
      rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B, GlobalTheory.IsoMean.symplO_eq_add, h0, add_zero,
        AddChar.map_zero_eq_one])
    (fun c z => hψ.1.2.1 _)
    (fun z => by rw [← hsep z]; exact Subtype.forall)
    η 𝓩 hη.1 hη.2.1 (fun z => g F₁ F₁' z - g F₂ F₂' z) ((hgc F₁ F₁' h₁ h₁').sub (hgc F₂ F₂' h₂ h₂'))
    (fun γ hγ z => by simp only [hgp F₁ F₁' h₁ h₁' γ hγ z, hgp F₂ F₂' h₂ h₂' γ hγ z])
    (fun c => by
      have e1 := hcoef c c.2 F₁ F₁' h₁ h₁'
      have e2 := hcoef c c.2 F₂ F₂' h₂ h₂'
      have e3 := H ν 𝓕 hν.1 hν2 (ι c) (horth c)
      rw [e1, e2] at e3
      have e4 := mul_left_cancel₀ hκ e3
      simp only [mul_sub]
      rw [integral_sub (hint c c.2 F₁ F₁' h₁ h₁') (hint c c.2 F₂ F₂' h₂ h₂')]
      exact sub_eq_zero.2 e4)
  have e := congrFun key 0
  simp only [Pi.zero_apply, hg] at e
  rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B] at e
  exact sub_eq_zero.1 e

end GlobalTheory.IsoMean

end
end

