module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorPureTensorCoefficientSplitsTrivialPlac
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCoeffSplit

theorem ip_double_sum {D : D7} {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {ι κ : Type}
    (s : Finset ι) (t : Finset κ) (a : ι → ℂ) (b : κ → ℂ) (u : ι → WO S T → ℂ) (w : κ → WO S T → ℂ)
    (hI : ∀ i j, IntegrableOn (fun z => u i z * (starRingEnd ℂ) (w j z)) 𝓕 μ) :
    ipO μ 𝓕 (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • w j) =
      ∑ i ∈ s, ∑ j ∈ t, a i * (starRingEnd ℂ) (b j) * ipO μ 𝓕 (u i) (w j) := by
  unfold ipO
  have e : (fun z => (∑ i ∈ s, a i • u i) z * (starRingEnd ℂ) ((∑ j ∈ t, b j • w j) z)) =
      fun z => ∑ i ∈ s, ∑ j ∈ t, a i * (starRingEnd ℂ) (b j) * (u i z * (starRingEnd ℂ) (w j z)) := by
    funext z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hI i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hI i j).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _


open Classical in
def monoFactor {D : D7} {m n : ℕ} (k : FVar D m n →₀ ℕ) (τ : D.what₂.Tau) : MvPolynomial (FVar D m n) ℂ :=
  ∏ y ∈ k.support with y.1 = τ, MvPolynomial.X y ^ k y

theorem monoFactor_supported {D : D7} {m n : ℕ} (k : FVar D m n →₀ ℕ) (τ : D.what₂.Tau) :
    monoFactor k τ ∈ MvPolynomial.supported ℂ {y : FVar D m n | y.1 = τ} := by
  classical
  unfold monoFactor
  refine Subalgebra.prod_mem _ fun y hy => Subalgebra.pow_mem _ (MvPolynomial.X_mem_supported.2 ?_) _
  exact (Finset.mem_filter.1 hy).2

theorem prod_monoFactor {D : D7} {m n : ℕ} (k : FVar D m n →₀ ℕ) :
    ∏ τ, monoFactor k τ = MvPolynomial.monomial k 1 := by
  classical
  unfold monoFactor
  rw [Finset.prod_fiberwise k.support (fun y => y.1) (fun y => MvPolynomial.X y ^ k y), MvPolynomial.monomial_eq,
    MvPolynomial.C_1, one_mul]
  rfl

theorem fockPure_any {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (x : Place D → WO S T → ℂ) (f : WO S T → ℂ) (hx : IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f)
    (hx0 : ∀ τ, x (.inr τ) = f₀) (P : D.what₂.Tau → MvPolynomial (FVar D T.rank S.rank) ℂ)
    (hP : ∀ τ, P τ ∈ MvPolynomial.supported ℂ {y : FVar D T.rank S.rank | y.1 = τ}) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
      (Sum.elim (fun v => x (.inl v)) fun τ => pureTensorO ψ θ S T sS sT BS BT f₀ (P τ))
      (pureTensorO ψ θ S T sS sT BS BT f (∏ τ, P τ)) := by
  classical
  have hl : GlobalTheory.FockPureTensor.IsMultiLin (IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀) :=
    (_root_.GlobalTheory.PureLinear.isPure_linear_and_dRho D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ).1
  have h1 : ∀ g, pureTensorO ψ θ S T sS sT BS BT g 1 = g := fun g => GlobalTheory.Ker.FockAlg.pure_one g
  have key := GlobalTheory.FockPureTensor.prod_step hl (pureTensorO ψ θ S T sS sT BS BT f)
    (pureTensorO ψ θ S T sS sT BS BT f₀)
    (fun τ => {y : FVar D T.rank S.rank | y.1 = τ})
    (fun τ y hy z R Q h => by
      rw [GlobalTheory.FockPureTensor.pureTensorO_X_mul hb BS BT hx.2.1,
        GlobalTheory.FockPureTensor.pureTensorO_X_mul hb BS BT (base_theta hb)]
      obtain rfl : y.1 = τ := hy
      unfold aPlusAll
      exact GlobalTheory.FockPureTensor.isPure_aPlus hb hμ z _ _ _ _ _ h) hP (x := x) (by rw [h1]; exact hx)
    (fun τ => by rw [h1]; exact hx0 τ) Finset.univ
  simp only [Finset.mem_univ, if_true] at key
  exact key

theorem pureTensorO_eq_sum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT f P =
      ∑ k ∈ P.support, P.coeff k • pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial k 1) := by
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem coeff_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (x : Place D → WO S T → ℂ), (∀ τ, x (.inr τ) = f₀) → ∀ (v : FinPl D) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (g : GA D S), gAt S (.inl v) g = 1 → ∃ C : ℂ, ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), (∀ p, p ≠ .inl v → x₁ p = x p) → (∀ p, p ≠ .inl v → x₂ p = x p) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → ipO μ 𝓕 (om (g, 1) (pureTensorO ψ θ S T sS sT BS BT f₁ P)) (pureTensorO ψ θ S T sS sT BS BT f₂ P) = C * ipO μ 𝓕 (x₁ (.inl v)) (x₂ (.inl v)) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW _ hb hμ BS BT x hx0 v P g hg
  classical
  let Y : (FVar D T.rank S.rank →₀ ℕ) → Place D → WO S T → ℂ := fun k =>
    Sum.elim (fun u => x (.inl u)) fun τ => pureTensorO ψ θ S T sS sT BS BT f₀ (monoFactor k τ)
  let R : (FVar D T.rank S.rank →₀ ℕ) → (FVar D T.rank S.rank →₀ ℕ) → ℂ := fun k l =>
    ∏ᶠ (p : Place D) (_ : p ≠ .inl v), ipO μ 𝓕 (om (gAt S p g, gAt T p 1) (Y k p)) (Y l p)
  refine ⟨∑ k ∈ P.support, ∑ l ∈ P.support, P.coeff k * (starRingEnd ℂ) (P.coeff l) * R k l, ?_⟩
  intro x₁ x₂ f₁ f₂ e1 e2 hp1 hp2
  have hne : ∀ τ : D.what₂.Tau, (Sum.inr τ : Place D) ≠ .inl v := fun τ h => by cases h
  have pure : ∀ (y : Place D → WO S T → ℂ) (f : WO S T → ℂ), (∀ p, p ≠ .inl v → y p = x p) →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f → ∀ k, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
        (Sum.elim (fun u => y (.inl u)) fun τ => pureTensorO ψ θ S T sS sT BS BT f₀ (monoFactor k τ))
        (pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial k 1)) := fun y f ey hy k => by
    have := fockPure_any BS BT hb hμ y f hy (fun τ => (ey _ (hne τ)).trans (hx0 τ)) (monoFactor k)
      (monoFactor_supported k)
    rwa [prod_monoFactor] at this
  have om1 : ∀ u : WO S T → ℂ, om (1, 1) u = u := fun u => by
    have : om (1, 1) = 1 := map_one om
    rw [this]; rfl
  have ipb := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 (base_std hb) hμ
  have pom := fun k => GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hb hμ _ _
    (pure x₁ f₁ e1 hp1 k) g 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pureTensorO_eq_sum ψ θ S T sS sT BS BT f₁, pureTensorO_eq_sum ψ θ S T sS sT BS BT f₂, map_sum]
  simp only [map_smul]
  rw [ip_double_sum μ 𝓕 _ _ _ _ _ _ fun k l => (ipb _ _ (pom k).2.1 (pure x₂ f₂ e2 hp2 l).2.1).1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc (P.coeff k * (starRingEnd ℂ) (P.coeff l))]
  congr 1
  obtain ⟨hfin, heq⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ _ _ _
    (pom k) (pure x₂ f₂ e2 hp2 l)
  rw [heq, ← mul_finprod_cond_ne (.inl v) hfin, mul_comm]
  congr 1
  · refine finprod_congr fun p => finprod_congr fun hp => ?_
    cases p with
    | inl u => simp only [Sum.elim_inl, Y, e1 _ hp, e2 _ hp]
    | inr τ => simp only [Sum.elim_inr, Y]
  · simp only [Sum.elim_inl, hg, gAt_one, om1]

end GlobalTheory.FockCoeffSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupSplitRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacSplit

open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem tensNU_map (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (h : ∀ a, j (φ a) = j 1 * a)
    (z : R' ⊗[F] E) : tensNU j hj (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = tensNU (E := E) j hj 1 * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Algebra.TensorProduct.one_def, h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, mul_add]

theorem mat_extH_mapH (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (h : ∀ a, j (φ a) = j 1 * a)
    (g : HA R' σ J) : ∃ c : R' ⊗[F] E, (HA.mat R' σ J (extH σ J j hj (mapH σ J φ g))).1 =
      (1 - c) • (1 : Matrix (Fin M) (Fin M) (R' ⊗[F] E)) + c • (HA.mat R' σ J g).1 := by
  refine ⟨tensNU (E := E) j hj 1, ?_⟩
  ext r s
  rw [GlobalTheory.AutFunCompare.mat_extH, GlobalTheory.AutFunCompare.mat_mapH, tensNU_map φ j hj h]
  rfl

omit [Algebra F R] in
theorem conj_mix {k n m : ℕ} (c : R) (P : Matrix (Fin k) (Fin n) R) (G : Matrix (Fin n) (Fin n) R)
    (Q : Matrix (Fin n) (Fin m) R) :
    P * (((1 - c) • (1 : Matrix (Fin n) (Fin n) R) + c • G) * Q) = (1 - c) • (P * Q) + c • (P * (G * Q)) := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]

omit [Algebra F R] in
theorem mix_zero {k m : ℕ} (c : R) {A B : Matrix (Fin k) (Fin m) R} (hA : A = 0) (hB : B = 0) :
    (1 - c) • A + c • B = 0 := by rw [hA, hB, smul_zero, smul_zero, add_zero]

omit [Algebra F R] in
theorem mix_uni {k : ℕ} (c : R) {A B : Matrix (Fin k) (Fin k) R} (hA : A = 1)
    (hB : ∀ i j : Fin k, (j < i → B i j = 0) ∧ B i i = 1) (i j : Fin k) :
    (j < i → ((1 - c) • A + c • B) i j = 0) ∧ ((1 - c) • A + c • B) i i = 1 := by
  subst hA
  refine ⟨fun hji => ?_, ?_⟩
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, (hB i j).1 hji, Matrix.one_apply_ne hji.ne',
      mul_zero, add_zero]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, (hB i i).2, Matrix.one_apply_eq, mul_one,
      sub_add_cancel]

end Gen

variable {D : D7}

theorem mt_ofInf_projInf (V : HSp D) (g : GA D V) : ∃ c : AE D,
    mt V (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g)) = (1 - c) • (1 : Mx D V.rank V.rank) + c • mt V g :=
  mat_extH_mapH (R' := AF D.host.F) D.sp.cm.sig V.gram (fstA D.host.F) _ _
    (fun a => Prod.ext (one_mul a.1).symm (zero_mul a.2).symm) g

theorem mt_ofFin_projFin (V : HSp D) (g : GA D V) : ∃ c : AE D,
    mt V (ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g)) = (1 - c) • (1 : Mx D V.rank V.rank) + c • mt V g :=
  mat_extH_mapH (R' := AF D.host.F) D.sp.cm.sig V.gram (sndA D.host.F) _ _
    (fun a => Prod.ext (zero_mul a.1).symm (one_mul a.2).symm) g

theorem mem_jacGrp_of_mat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : AE D) {g h : GA D S} (hg : g ∈ jacGrp d)
    (hh : mt S h = (1 - c) • (1 : Mx D S.rank S.rank) + c • mt S g) : h ∈ jacGrp d := by
  obtain ⟨h0, hY, hX⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d g).1 hg
  have e : ∀ {k : ℕ} (P : Mx D k S.rank),
      P * (mt S h * d.jX) = (1 - c) • (P * d.jX) + c • (P * (mt S g * d.jX)) := fun P =>
    (congrArg (fun N : Mx D S.rank S.rank => P * (N * d.jX)) hh).trans (conj_mix c P (mt S g) d.jX)
  refine (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d h).2
    ⟨(e _).trans (mix_zero c d.p0_jX h0), (e _).trans (mix_zero c d.pY_jX hY), ?_⟩
  rw [e]
  exact mix_uni c d.pX_jX hX

end GlobalTheory.JacSplit

namespace GlobalTheory

open GlobalTheory.AdelicU

theorem jacGrp_split_inf_fin : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ∀ a ∈ GinfC V, ∀ b ∈ GfC V,
    a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d := by
  intro D V V₀ ρ d a ha b hb hab
  rw [GinfC_eq, mem_infPts] at ha
  rw [GfC_eq, mem_finPts] at hb
  have hA : ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram (a * b)) = a := by
    rw [map_mul, hb, mul_one]
    conv_rhs => rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram a]
    rw [ha, map_one, mul_one]
  have hB : ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram (a * b)) = b := by
    rw [map_mul, ha, one_mul]
    conv_rhs => rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram b]
    rw [hb, map_one, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.JacSplit.mt_ofInf_projInf V (a * b)
  obtain ⟨c', hc'⟩ := GlobalTheory.JacSplit.mt_ofFin_projFin V (a * b)
  rw [hA] at hc
  rw [hB] at hc'
  exact ⟨GlobalTheory.JacSplit.mem_jacGrp_of_mat d c hab hc, GlobalTheory.JacSplit.mem_jacGrp_of_mat d c' hab hc'⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.GelfCyc

open GlobalTheory.SmoothForms (gelfA gelfA_eq_sum_pow)

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem gelfA_conj (G : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (k : ℕ) :
    gelfA (fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) k = gelfA G k := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix
  have hc : ∀ (M : Matrix (Fin n) (Fin n) A) a b, (φ P * M * φ Q) a b = ∑ c, ∑ d, (P a c * Q d b) • M c d := by
    intro M a b
    simp only [Matrix.mul_apply, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_comm]
  have h1 : (Matrix.of fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) = φ P * Matrix.of G * φ Q := by
    ext a b
    rw [hc]
    rfl
  have h2 : ∀ m : ℕ, (φ P * Matrix.of G * φ Q) ^ m = φ P * Matrix.of G ^ m * φ Q := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, mul_one, ← map_mul, hPQ, map_one]
    | succ m ih =>
      have : φ Q * φ P = 1 := by rw [← map_mul, hQP, map_one]
      rw [pow_succ, pow_succ, ih]
      simp only [mul_assoc]
      rw [← mul_assoc (φ Q), this, one_mul]
  rw [gelfA_eq_sum_pow, gelfA_eq_sum_pow, h1, h2]
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have : ∀ d, ∑ a, (P a c * Q d a) • (Matrix.of G ^ (k + 1)) c d = (Q * P) d c • (Matrix.of G ^ (k + 1)) c d := by
    intro d
    rw [← Finset.sum_smul, Matrix.mul_apply]
    simp only [mul_comm]
  simp [this, hQP, Matrix.one_apply]

theorem gelfA_swap (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA (fun a b => E b a) k = ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).reverse.prod := by
  rw [gelfA]
  refine (Fintype.sum_equiv ((Equiv.neg (Fin (k + 1))).arrowCongr (Equiv.refl _)) _ _ fun idx => ?_).symm
  congr 1
  have h : ∀ a : Fin (k + 1), a.rev + 1 = -a := fun a => by
    have : a.rev + a = Fin.last k := Fin.ext (by
      have := a.2
      rw [Fin.val_add, Fin.val_rev, Fin.val_last, Nat.mod_eq_of_lt] <;> omega)
    rw [eq_neg_iff_add_eq_zero, add_right_comm, this, Fin.last_add_one]
  have h' : ∀ a : Fin (k + 1), a.rev = -(a + 1) := fun a => by
    rw [neg_add, ← h, add_neg_cancel_right]
  have e : ∀ g : Fin (k + 1) → A, (List.ofFn g).reverse = List.ofFn fun a => g a.rev := fun g => by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp
  rw [e]
  congr 1
  funext a
  rw [h, h']
  rfl

theorem prod_ofFn_neg : ∀ (m : ℕ) (g : Fin m → A),
    (List.ofFn fun a => -g a).prod = (-1 : ℂ) ^ m • (List.ofFn g).prod
  | 0, _ => by simp
  | m + 1, g => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, prod_ofFn_neg m fun a => g a.succ, pow_succ]
    simp

theorem sum_words (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).reverse.prod := by
  have e : ∀ a b, φ (M * (Matrix.single a b 1)ᵀ * M⁻¹) = ∑ c, ∑ d, (M⁻¹ a c * M d b) • φ (Matrix.single d c 1) := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    congr 1
    rw [Matrix.matrix_eq_sum_single (M * _ * _), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    simp [Matrix.mul_apply, Matrix.single, ite_and, mul_comm]
  rw [← gelfA_swap (fun a b => φ (Matrix.single a b 1)),
    ← gelfA_conj _ M⁻¹ M (Matrix.mul_nonsing_inv M hM), gelfA, Finset.smul_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  simp only [map_neg, e]
  exact prod_ofFn_neg _ _

end Alg

open GlobalTheory.Mem.RealTranslate (derEnd)

theorem wordDer_eq {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (τ : D.what₂.Tau)
    (w : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : SmFun θ V) :
    wordDer θ V τ w f.1 = ((w.map (derEnd hθ τ)).prod f).1 := by
  induction w with
  | nil => rfl
  | cons Z w ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    show RderC θ V τ Z (wordDer θ V τ w f.1) = _
    rw [ih]
    rfl

end GlobalTheory.RegSch.GelfCyc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntertwiningStabilizerTranslateScalar
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.IkStab

variable {D : D7}

theorem exists_valuation_adapted_index {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) {p : GA D T} (hp : p ∈ stab d) :
    ∃ (β : Mx D t T'.rank) (g : GA D T'), mt T p ⬝ d.j0 = d.jX ⬝ β + d.j0 ⬝ mt T' g := by
  obtain ⟨α, hα⟩ := hp
  have hu := mt_unitary T p
  have h1 : adj (mt T p ⬝ d.jX) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ hu, d.wittDecomp_gram_X_anisotropic]
  have h2 : d.pY ⬝ (mt T p ⬝ d.j0) = 0 := by
    rw [hα, adj_mul, Matrix.mul_assoc] at h1
    have h3 := congrArg (fun z : Mx D t T'.rank => adj (α⁻¹).1 ⬝ z) h1
    simp only [← Matrix.mul_assoc (adj (α⁻¹).1), ← adj_mul, Units.mul_inv, adj_one, Matrix.one_mul,
      Matrix.mul_zero] at h3
    rw [d.pY_eq, Matrix.mul_assoc, h3]
  have h4 : mt T p ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt T p ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt T p ⬝ d.j0)) := by
    conv_lhs => rw [← Matrix.one_mul (mt T p ⬝ d.j0), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_zero, add_zero]
  have h5 : adj (mt T p ⬝ d.j0) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) = gA T' := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ hu, d.gram_00]
  generalize d.pX ⬝ (mt T p ⬝ d.j0) = β at h4
  generalize d.p0 ⬝ (mt T p ⬝ d.j0) = g at h4
  rw [h4] at h5
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₃ d.gram_XX,
    cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero] at h5
  exact ⟨β, ofMat T' g h5, h4⟩

end GlobalTheory.RegSch.IkStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSectionGraphSplitPlaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSection_graph_splitPlace : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := A.rank), ∀ k₂ ∈ KGL w (n := A.rank), φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  first | exact @GlobalTheory.Core.Rk.KerSplit.sphSec_split | exact GlobalTheory.Core.Rk.KerSplit.sphSec_split | (intros; apply GlobalTheory.Core.Rk.KerSplit.sphSec_split <;> assumption)
end

