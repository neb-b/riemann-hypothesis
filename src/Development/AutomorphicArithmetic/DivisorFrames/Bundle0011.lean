module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.EvalLocalElementMatrixEqOneOfPrimeNotDvd
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem norm_int_le_one {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (j : E →+* PadicAlgCl l) (x : 𝓞 E) :
    ‖j (x : E)‖ ≤ 1 := by
  have h1 : IsIntegral ℤ (j (x : E)) := x.isIntegral_coe.map j.toIntAlgHom
  have h2 : IsIntegral (PadicAlgCl.valued l).v.integer (j (x : E)) := h1.tower_top
  have h3 := (Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral h2
  rw [Valuation.mem_integer_iff, PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

private theorem norm_le_of_int {D : D7} {l : ℕ} [Fact l.Prime]
    (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)
    (h : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
      ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) (z) (hz : z ∈ intAE D) : ‖ev z‖ ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    have e : a ⊗ₜ[D.host.F] (x : D.host.E) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (x : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, RingHom.map_mul, norm_mul]
    have h2 := norm_int_le_one (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) x
    exact mul_le_one₀ (h a ha) (norm_nonneg _) h2
  | zero => rw [RingHom.map_zero, norm_zero]; exact zero_le_one
  | add x y _ _ hx hy =>
    rw [RingHom.map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rw [RingHom.map_neg, norm_neg]; exact hx

private theorem ev_idem {D : D7} {l : ℕ} [Fact l.Prime]
    (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)
    (h : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
      ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (e : AE D) (he : e * e = e)
    (hx : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) :
    ev (finPart D e) = 0 := by
  have hl : l.Prime := Fact.out
  have hcO : ((l : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have h1 := (hx _ hcO).not.1 hP
  rw [not_not] at h1
  have h2 := norm_le_of_int ev h _ h1
  by_contra hne
  have h3 : ev (finPart D e) * ev (finPart D e) = ev (finPart D e) := by
    rw [← RingHom.map_mul, ← RingHom.map_mul, he]
  have h4 : ev (finPart D e) = 1 := mul_left_cancel₀ hne (h3.trans (mul_one _).symm)
  rw [RingHom.map_mul, RingHom.map_mul, h4, one_mul] at h2
  have h5 : ev (finPart D (incA D ((((l : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹))) = ((l : ℕ) : PadicAlgCl l)⁻¹ := by
    change (ev.comp ((finPart D).comp (incA D))) _ = _
    rw [map_inv₀]
    congr 1
    simp only [map_natCast]
  rw [h5, norm_inv] at h2
  have h6 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have h7 : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  exact absurd h2 (not_le.2 ((one_lt_inv₀ h7).2 h6))

private theorem finPart_cA {D : D7} (w : AE D) :
    finPart D (cA D w) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

private theorem placeIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F}
    (h : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : α * α = α := by
    refine DFunLike.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (α * α) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, mul_one]
    · rw [h0 w hw, mul_zero]
  exact Prod.ext (mul_zero _) this

private theorem finPart_sub_one {D : D7} (V : HSp D) (h : GA D V) (i j : Fin V.rank) :
    finPart D ((Formalism.L2.Theta.mt V h - 1) i j) = ((finHom V h).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
  congr 1
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]

theorem UpperTheory.eval_localElement_matrix_eq_one_of_prime_not_dvd :
    ∀ (D : D7) (V : HSp D) (l : ℕ) [Fact l.Prime]
        (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l),
        (∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) → ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) →
        ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ x : Bridge.Gf V, GlobalTheory.Hk3.IsLocElt V P x →
          Matrix.map x.1.val ev = 1 := by
  intro D V l _ ev h P hP x ⟨e, f, g, hef, _, hx, hs⟩
  have hf : ev (finPart D f) = 0 := by
    rcases hef with ⟨⟨⟨h1, -⟩, h2⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hε, h1⟩, h2⟩
    · have a1 := ev_idem ev h P hP e h1 h2
      have a2 := ev_idem (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig))
        (fun a ha => by
          change ‖ev (a ⊗ₜ[D.host.F] D.sp.cm.sig 1)‖ ≤ 1
          rw [map_one]; exact h a ha) P hP e h1 h2
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), a1, finPart_cA, zero_add]
      exact a2
    · refine ev_idem ev h P hP f ?_ h2
      rw [h1, ← RingHom.map_mul, placeIdem hε]
  ext i j
  have h1 := congrArg (fun z => ev (finPart D z)) (hs i j)
  simp only [RingHom.map_mul, hf, zero_mul] at h1
  rw [finPart_sub_one, ← hx, Matrix.sub_apply, RingHom.map_sub, eq_comm, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1]
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsInjectiveSemilinearNablaTWtOpEquivariant
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

noncomputable section

namespace UpperTheory.RingTransport

open MvPolynomial GlobalTheory.ExpFrame

private theorem map_mem {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    map σ f ∈ Formalism.GradedWeylDivisibility.dualWeyl S r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro l j hlj
    have e := h2 l j hlj
    simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at e ⊢
    have hc : ∀ g : MvPolynomial (Fin r × Fin n) R,
        map σ (Formalism.GradedWeylDivisibility.colAddGen R l j g) = Formalism.GradedWeylDivisibility.colAddGen S l j (map σ g) := by
      intro g
      unfold Formalism.GradedWeylDivisibility.colAddGen
      rw [aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
      congr 2
      funext v
      split_ifs <;> simp
    rw [← hc, e, map_rename]

private def onFactor {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl R r n ν →+ Formalism.GradedWeylDivisibility.dualWeyl S r n ν where
  toFun f := ⟨map σ (f : MvPolynomial (Fin r × Fin n) R), map_mem σ f.2⟩
  map_zero' := by ext1; simp
  map_add' f f' := by ext1; simp

private theorem onFactor_smul {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (r n : ℕ) (ν : Fin n → ℕ) (c : R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : onFactor σ r n ν (c • f) = σ c • onFactor σ r n ν f := by
  ext1
  simp [onFactor, smul_eq_C_mul]

private def Tw {R S : Type} [CommRing R] [CommRing S] (_σ : R →+* S) (M : Type) : Type := M

private instance instAdd {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (M : Type) [AddCommGroup M] :
    AddCommGroup (Tw σ M) :=
  inferInstanceAs (AddCommGroup M)

private instance instMod {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (M : Type) [AddCommGroup M] [Module S M] :
    Module R (Tw σ M) :=
  Module.compHom M σ

variable {R S : Type} [CommRing R] [CommRing S] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

private def mlin (σ : R →+* S) :
    MultilinearMap (RingHom.id R) (fun τ : ι => Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ)))
      (Tw σ (NablaT S N mu)) where
  toFun x := (PiTensorProduct.tprod S (fun τ => onFactor σ N N _ (x τ)) : NablaT S N mu)
  map_update_add' := by
    intro _ x i a b
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, map_add (f := _)]
    exact (PiTensorProduct.tprod S).map_update_add _ i _ _
  map_update_smul' := by
    intro _ x i c a
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, onFactor_smul]
    exact (PiTensorProduct.tprod S).map_update_smul _ i _ _

private def semi (σ : R →+* S) : NablaT R N mu →+ NablaT S N mu :=
  (PiTensorProduct.lift (mlin N mu σ)).toAddMonoidHom

private theorem semi_tprod (σ : R →+* S) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    semi N mu σ (PiTensorProduct.tprod R x) = PiTensorProduct.tprod S (fun τ => onFactor σ N N _ (x τ)) := by
  show (PiTensorProduct.lift (mlin N mu σ)) (PiTensorProduct.tprod R x) = _
  rw [PiTensorProduct.lift.tprod]; rfl

private theorem semi_smul (σ : R →+* S) (c : R) (y : NablaT R N mu) :
    semi N mu σ (c • y) = σ c • semi N mu σ y :=
  (PiTensorProduct.lift (mlin N mu σ)).map_smul c y

private theorem semi_left_inv (g : R ≃+* S) (y : NablaT R N mu) :
    semi N mu g.symm.toRingHom (semi N mu g.toRingHom y) = y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [semi_smul, semi_smul, semi_tprod, semi_tprod]
    congr 1
    · simp
    · congr 1
      funext τ
      ext1
      simp [onFactor, map_map, MvPolynomial.map_id]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

private theorem onFactor_rep (σ : R →+* S) (u : GL (Fin N) R) (ν : Fin N → ℕ)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R N N ν) :
    onFactor σ N N ν (Formalism.UG.dualWeylRep R N N ν u f) =
      Formalism.UG.dualWeylRep S N N ν (Matrix.GeneralLinearGroup.map σ u) (onFactor σ N N ν f) := by
  ext1
  simp only [onFactor, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Formalism.UG.dualWeylRep_apply]
  unfold Formalism.UG.dwAct Formalism.GradedWeylDivisibility.rowAct
  rw [aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
  congr 2
  funext v
  rw [← map_inv]
  simp only [map_sum, map_mul, map_C, map_X, Matrix.GeneralLinearGroup.map_apply]

private theorem semi_grp [DecidableEq ι] (σ : R →+* S) (h : ι → GL (Fin N) R) (y : NablaT R N mu) :
    semi N mu σ (grp R N mu h y) =
      grp S N mu (fun τ => Matrix.GeneralLinearGroup.map σ (h τ)) (semi N mu σ y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, semi_smul, semi_smul, map_smul, GlobalTheory.SemilinTransport.grp_tprod, semi_tprod, semi_tprod,
      GlobalTheory.SemilinTransport.grp_tprod]
    congr 2
    funext τ
    exact onFactor_rep N σ (h τ) _ (x τ)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

private theorem det_map (σ : R →+* S) (u : GL (Fin N) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map σ u) =
      Units.map (σ : R →* S) (Matrix.GeneralLinearGroup.det u) := by
  ext
  simp [RingHom.map_det]

private theorem semi_wtOp [Fintype ι] [DecidableEq ι] (sh : ι → ℤ) (σ : R →+* S) (h : ι → GL (Fin N) R) (y : NablaT R N mu) :
    semi N mu σ (wtOp R N mu sh h y) =
      wtOp S N mu sh (fun τ => Matrix.GeneralLinearGroup.map σ (h τ)) (semi N mu σ y) := by
  rw [wtOp_apply, wtOp_apply, semi_smul, semi_grp]
  congr 1
  simp only [det_map, ← map_zpow, ← map_prod]
  rfl

end UpperTheory.RingTransport

end

theorem UpperTheory.exists_injective_semilinear_nablaT_wtOp_equivariant :
    ∀ (K K' : Type) [CommRing K] [CommRing K'] (io : K ≃+* K') (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
        (mu : ι → ℕ → ℕ) (sh : ι → ℤ), ∃ Φ : NablaT K n mu →+ NablaT K' n mu, Function.Injective Φ ∧ (∀ (c : K) u, Φ (c • u) = io c • Φ u) ∧
          ∀ (g : ι → GL (Fin n) K) u,
            Φ (wtOp K n mu sh g u) = wtOp K' n mu sh (fun τ => Matrix.GeneralLinearGroup.map io.toRingHom (g τ)) (Φ u) := by
  intro K K' _ _ io n ι _ _ mu sh
  refine ⟨UpperTheory.RingTransport.semi n mu io.toRingHom, fun y y' e => ?_,
    fun c x => UpperTheory.RingTransport.semi_smul n mu _ c x,
    fun h x => UpperTheory.RingTransport.semi_wtOp n mu sh _ h x⟩
  rw [← UpperTheory.RingTransport.semi_left_inv n mu io y, ← UpperTheory.RingTransport.semi_left_inv n mu io y', e]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsInvariantPerfectPairingNablaSqDualWeyl
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

section SlopeTestRemainingChoices

open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
open scoped Matrix

private theorem fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  simp only [fockF, MvPolynomial.coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]

private theorem fock_smul_right {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  simp only [fockF, coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

private noncomputable def fischer (σ : Type) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f h => fockF f (map (starRingEnd ℂ) h))
    (fun f f' h => by
      rw [Formalism.GradedWeylDivisibility.fockHerm σ _ (f + f'), fock_add_right, star_add, ← Formalism.GradedWeylDivisibility.fockHerm, ← Formalism.GradedWeylDivisibility.fockHerm])
    (fun c f h => by
      rw [Formalism.GradedWeylDivisibility.fockHerm σ _ (c • f), fock_smul_right, star_mul', star_star, ← Formalism.GradedWeylDivisibility.fockHerm, smul_eq_mul])
    (fun f h h' => by rw [map_add (f := _), fock_add_right])
    (fun c f h => by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, fock_smul_right, smul_eq_mul]
      simp)

private theorem fischer_apply {σ : Type} (f h : MvPolynomial σ ℂ) :
    fischer σ f h = fockF f (map (starRingEnd ℂ) h) := rfl

private theorem map_rowAct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : MvPolynomial (Fin n × Fin n) ℂ) :
    map (starRingEnd ℂ) (rowAct ℂ A h) = rowAct ℂ (Aᵀ)ᴴ (map (starRingEnd ℂ) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [rowAct]

private theorem fischer_adj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (f h : MvPolynomial (Fin n × Fin n) ℂ) :
    fischer _ (rowAct ℂ Aᵀ f) h = fischer _ f (rowAct ℂ A h) := by
  rw [fischer_apply, fischer_apply, Formalism.GradedWeylDivisibility.fockRowAdj, map_rowAct]

private theorem rowAct_rowAct {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : B * A = 1)
    (h : MvPolynomial (Fin n × Fin n) ℂ) : rowAct ℂ A (rowAct ℂ B h) = h := by
  have : (rowAct ℂ (n := n) A).comp (rowAct ℂ B) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, algHom_C, AlgHom.id_apply]
    simp only [algebraMap_eq, Finset.mul_sum, ← mul_assoc, ← C_mul]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, hAB, Matrix.one_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  exact DFunLike.congr_fun this h

private theorem lp_ne (n : ℕ) : lpMinor ℂ n (le_refl n) (le_refl n) ≠ 0 := by
  intro h
  have h1 := GlobalTheory.Branching.genericDet_pow_mul_hw ℂ n 1 (fun _ => 0)
  rw [h, pow_one, zero_mul] at h1
  exact hwNe ℂ n n le_rfl _ h1.symm

private theorem exists_j (n : ℕ) (ν : Fin n → ℕ) (s : ℤ) (lam : DomWeight n) (hl : ∀ a, lam.w a = (ν a : ℤ) + s) :
    ∃ j : nablaSq ℂ n lam →ₗ[ℂ] dualWeyl ℂ n n ν, Function.Bijective j ∧
      ∀ (g : GL (Fin n) ℂ) v, (j (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) =
        ((Matrix.GeneralLinearGroup.det g ^ s : ℂˣ) : ℂ) • rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (j v) := by
  obtain ⟨c, hc, hdet⟩ : ∃ c : ℕ, (fun a => lam.natW a + c) = ν ∧ ∀ g : GL (Fin n) ℂ,
      detPow ℂ n g lam.detShift = detPow ℂ n g s * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨0, funext fun a => a.elim0, fun g => ?_⟩
      have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
      simp [detPow, this]
    · have h3 : lam.detShift = lam.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
      refine ⟨ν ⟨n - 1, by omega⟩, funext fun a => ?_, fun g => ?_⟩
      · have h1 : lam.w ⟨n - 1, by omega⟩ ≤ lam.w a := lam.anti (by
          have := a.2
          rw [Fin.le_def]
          simp only
          omega)
        simp only [DomWeight.natW, h3]
        rw [hl, hl] at h1
        rw [hl, hl]
        omega
      · rw [h3, hl, add_comm, detPow, detPow, zpow_add, zpow_natCast]
        simp
  subst hc
  obtain ⟨dm, de, -⟩ := GlobalTheory.Branching.genericDet_pow_mul n c lam.natW
  let D : nablaSq ℂ n lam →ₗ[ℂ] dualWeyl ℂ n n (fun i => lam.natW i + c) :=
    { toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩
      map_add' := fun f f' => Subtype.ext (by simp [mul_add])
      map_smul' := fun a f => Subtype.ext (by simp) }
  refine ⟨D, ⟨fun f f' e => Subtype.ext ?_, fun f => ?_⟩, fun g f => ?_⟩
  · exact mul_left_cancel₀ (pow_ne_zero c (lp_ne n)) (congrArg Subtype.val e)
  · obtain ⟨f', hf', e⟩ := PI.WMI.determinant_splitting_formula n lam.natW c
      (fun h => by simp [DomWeight.natW, DomWeight.detShift, h]) f f.2
    exact ⟨⟨f', hf'⟩, Subtype.ext e.symm⟩
  · change lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n lam g f =
      detPow ℂ n g s • rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ
        (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))
    rw [de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_invariant_perfect_pairing_nablaSq_dualWeyl :
    ∀ (n : ℕ) (ν : Fin n → ℕ) (s : ℤ) (lam : DomWeight n), (∀ a, lam.w a = (ν a : ℤ) + s) →
        ∃ P : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ, Function.Bijective P.flip ∧
          ∀ (g : GL (Fin n) ℂ) v u, P (GlobalTheory.Branching.sqRep ℂ n lam g v) (Formalism.UG.dualWeylRep ℂ n n ν g u) =
            ((Matrix.GeneralLinearGroup.det g ^ s : ℂˣ) : ℂ) * P v u := by
  intro n ν s lam hl
  obtain ⟨j, hj, he⟩ := exists_j n ν s lam hl
  let P : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ :=
    (fischer _).compl₁₂ ((Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype ∘ₗ j) (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype
  have hP : ∀ v u, P v u = fischer _ (j v : MvPolynomial (Fin n × Fin n) ℂ) u := fun _ _ => rfl
  let e := LinearEquiv.ofBijective j hj
  haveI : FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) := e.finiteDimensional
  have hinj : Function.Injective P.flip := by
    refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
    obtain ⟨v, hv⟩ := hj.2 ⟨_, Formalism.GradedWeylDivisibility.dualWeylMap ℂ ℂ (starRingEnd ℂ) n n ν u u.2⟩
    have h0 : P v u = 0 := LinearMap.congr_fun hu v
    rw [hP, hv, fischer_apply] at h0
    by_contra hne
    have hne' : MvPolynomial.map (starRingEnd ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h =>
      hne (Subtype.ext (MvPolynomial.map_injective _ (starRingEnd ℂ).injective (h.trans (map_zero _).symm)))
    have := (Formalism.GradedWeylDivisibility.fockPos _ _ hne').1
    rw [h0] at this
    simp at this
  refine ⟨P, ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩, fun g v u => ?_⟩
  · rw [← e.finrank_eq]
    exact (Subspace.dual_finrank_eq).symm
  · rw [hP, hP, he, map_smul, LinearMap.smul_apply, fischer_adj, Formalism.UG.dualWeylRep_apply, Formalism.UG.dwAct,
      rowAct_rowAct _ _ (by simp), smul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.LevChiEqOneOfGoodPlace
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.hecke_offprime_preimage {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hβ : ∃ c : ℕ, Formalism.IndefR.Lev.IsBaseFrame V β Λ (1 ^ c)) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ v ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP v) :
    ∀ k ∈ GlobalTheory.Hk3.hyp V v, ∃ h : (Formalism.L2.Theta.finHom V).rangeRestrict k ∈ (levEnv V β L).J,
      (levEnv V β L).χ ⟨_, h⟩ = 1 := by
  refine hβ.elim fun c hc => ?_
  have hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (Formalism.IndefR.Lev.flag1L L) hc').2 v e f' he h1 hoff
  rintro a ⟨ha, e, f', he, hs⟩
  have hm := ((hl e f' he).1 a hs).2 ha
  exact ⟨hm.2, Units.ext ((hl e f' he).2.1 a hm hs)⟩

theorem UpperTheory.levChi_eq_one_of_good_place :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (v : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good p.R.toRealDat t v →
        ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) v, ∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t, levChi p j t ⟨_, h⟩ = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t v hv
  exact UpperTheory.hecke_offprime_preimage (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) (p.charW.base.lev.βV j) v hv
end

