module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetUnit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detUnit_of :
    UnitOfSpan := by
  intro S _ a v hv
  have hmem : ∀ i : Fin a, ∃ c : Fin a → S, ∑ k, c k • v k = Pi.single i 1 := fun i => by
    have h : (Pi.single i 1 : Fin a → S) ∈ Submodule.span S (Set.range v) := by
      rw [hv]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun S).1 h
  choose c hc using hmem
  have hQN : (Matrix.of fun i k => v k i) * (Matrix.of fun k i => c i k) =
      (1 : Matrix (Fin a) (Fin a) S) := by
    ext i j
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    simp only [mul_comm (v _ i)]
    rw [h, Pi.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hQN
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetWdLift
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem letter_lift {LL U D N : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    [AddCommGroup N] [Module LL N] [Module F N] [IsScalarTower LL F N] (κ' : D →ₗ[LL] N)
    (hκ : ∀ c x, κ' (m c x) = τ c • κ' x) :
    ∃ j : Letter m F τ →ₗ[F] N, ∀ x, j (letterMk m F τ x) = κ' x := by
  have hk : letterKer m F τ ≤ LinearMap.ker (κ'.liftBaseChange F) := by
    refine iSup_le fun c => ?_
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul z x =>
      simp [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul, hκ, smul_smul, mul_comm]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  refine ⟨(letterKer m F τ).liftQ (κ'.liftBaseChange F) hk, fun x => ?_⟩
  show (letterKer m F τ).liftQ (κ'.liftBaseChange F) hk ((letterKer m F τ).mkQ ((1 : F) ⊗ₜ[LL] x)) = κ' x
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.liftBaseChange_tmul, one_smul]

theorem UpperTheory.Gal.crystallineComparison.detWdLift_of :
    WdLift := by
  intro l _ P ι K LL V _ _ _ _ ρ N _ _ κ hadd hsmul hmul
  letI := algC ι LL
  letI : Module ↥LL.1 N := Module.compHom N (algebraMap ↥LL.1 ℂ)
  haveI : IsScalarTower ↥LL.1 ℂ N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let κ' : ↥(Dpst P ρ) →ₗ[↥LL.1] N :=
    { toFun := κ
      map_add' := hadd
      map_smul' := fun c x => hsmul c x }
  exact letter_lift (mulD P ρ) ℂ (urC ι) κ' (fun c x => hmul c x)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetWeil
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL V : Type} [Field LL] [Algebra ℚ_[l] LL]
  [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem phiV_pow_tmul (n : ℕ) (v : V) (b : Bst P) :
    (phiV P LL V ^ n) (v ⊗ₜ[ℚ_[l]] b) = v ⊗ₜ[ℚ_[l]] (phiSt P ^ n) b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, phiV_tmul, ih, pow_succ, AlgHom.mul_apply]

variable {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

private theorem coe_phiD_pow (n : ℕ) (x : ↥(Dpst P ρ)) :
    (((phiD P ρ ^ n) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n) (x : V ⊗[ℚ_[l]] Bst P) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, coe_phiD, pow_succ, Module.End.mul_apply]

private theorem stRep_phiV_pow (γ : ↥(GK K)) (n : ℕ) (y : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρ γ ((phiV P LL V ^ n) y) =
      AlgebraTensorModule.map (ρ γ) ((actSt P (γ : GQ l)).comp (phiSt P ^ n)).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [phiV_pow_tmul, stRep_tmul]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end

theorem UpperTheory.Gal.crystallineComparison.detWeil_of :
    WeilCo := by
  intro l _ P E Ω _ _ _ _ _ A w h O _ _ _ Bw LL V _ _ _ _ ρ _ g hg x
  have e : -alpha l g = (resDeg l w : ℤ) := by simp [alpha, hg]
  rw [weilD_apply, e, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU, End.mul_apply, coe_actD,
    coe_phiD_pow, stRep_phiV_pow]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil
section
noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

def CorrPull : Prop :=
  ∀ (l : ℕ) (S S' Y Y' : Scheme.{0}) (u : S' ⟶ S) (f : Y ⟶ S) (f' : Y' ⟶ S') (h : Y' ⟶ Y), IsPullback h f' f u →
    ∀ T : Corr l Y, T.r ≫ f = T.p ≫ f → ∃ (T' : Corr l Y') (g : T'.Z ⟶ T.Z),
      IsPullback T'.p g h T.p ∧ T'.r ≫ h = g ≫ T.r ∧ T'.r ≫ f' = T'.p ≫ f' ∧ T'.d = T.d

def PtIdBC : Prop :=
  ∀ (l q n : ℕ) (O O' : Type) [CommRing O] [CommRing O'] (σ : O →+* O'), σ.Flat → ∀ (ϖ : O) (ϖ' : O'),
    (∀ P : Ideal O', P.IsPrime → (σ ϖ ∈ P ↔ ϖ' ∈ P)) → (∀ a : O', a ^ q - a ∈ Ideal.span {ϖ'}) →
    ∀ (Y Y' : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of O)) (f' : Y' ⟶ Spec (CommRingCat.of O')) (h : Y' ⟶ Y),
    IsPullback h f' f (Spec.map (CommRingCat.ofHom σ)) → ∀ (T : Fin (n + 1) → Corr l Y) (T' : Fin (n + 1) → Corr l Y')
      (g : ∀ j, (T' j).Z ⟶ (T j).Z), (∀ j, IsPullback (T' j).p (g j) h (T j).p) → (∀ j, (T' j).r ≫ h = g j ≫ (T j).r) →
      (∀ j, (T' j).r ≫ f' = (T' j).p ≫ f') → PtId l q n (fn f ϖ) T → PtId l q n (fn f' ϖ') T'

def DvdOfNil : Prop :=
  ∀ (K W : Type) [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W] [Module.Finite K W] (M : End K W) (s : Multiset K) (u : K),
    u ≠ 0 → IsNilpotent (Polynomial.aeval M (Polynomial.C u * rootPol s)) → ∃ m : ℕ, M.charpoly ∣ rootPol s ^ m

def PhiKOfNil : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (a : ℕ)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (LL : FinExt l) (r' : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1),
    IsModel Bw r LL r' → Bw.IsCrysE P LL r' → ∀ (Q : Polynomial ↥LL.1), NilD (σSt P Bw.Kw) (ψSt P (resDeg l w)) (Bw.repE LL r') Q →
    ∀ (s : Multiset ℂ) (u : ℂ), u ≠ 0 → Q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = Polynomial.C u * rootPol s →
    ∃ g : ↥(Weil h), deg g = -1 ∧ ∃ m : ℕ, (wdAt P ι Bw h hj r).charPol g ∣ rootPol s ^ m

end UpperTheory.Gal.crystallineComparison
end
end

