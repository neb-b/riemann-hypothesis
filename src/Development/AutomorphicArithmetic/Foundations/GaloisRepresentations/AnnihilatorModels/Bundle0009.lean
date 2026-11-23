module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleOfCrystalline
section
noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per

namespace UpperTheory.Gal.crystallineComparison

def AffFinProj : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f → AffFin Y

theorem heckePol_map {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (q n : ℕ) (θ : ℕ → K) :
    (heckePol q n θ).map f = heckePol q n fun j => f (θ j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [heckePol, Polynomial.map_sum]

def AdmOfCrys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → admitted (σCr P K) (finrank ℚ_[l] ↥(K0 K)) ρ

theorem admissible_of_crystalline : AdmOfCrys := by
  intro l _ P K V _ _ ρ h
  have e : Dinv (σCr P K) ρ = Dcris (P.PD K) ρ := by
    unfold Dinv Dcris actVB σCr
    refine iInf_congr fun g => ?_
    congr 3
    ext b
    simp [P.PD_actB]
  unfold admitted
  rw [e]
  exact h

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

def co {F L B : Type} [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] {a : ℕ} (x : (Fin a → L) ⊗[F] B) (i : Fin a) :
    L ⊗[F] B := AlgebraTensorModule.map (LinearMap.proj i : (Fin a → L) →ₗ[L] L) (LinearMap.id : B →ₗ[F] B) x

theorem co_tmul {F L B : Type} [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] {a : ℕ} (v : Fin a → L) (b : B) (i : Fin a) :
    co (v ⊗ₜ[F] b) i = v i ⊗ₜ[F] b := rfl

def onR {F B : Type} (L : Type) [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] (s : B →ₐ[F] B) : L ⊗[F] B →+* L ⊗[F] B :=
  (Algebra.TensorProduct.map (AlgHom.id F L) s).toRingHom

def CoFacts : Prop :=
  ∀ (F L B : Type) [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] (a : ℕ),
    (∀ x y : (Fin a → L) ⊗[F] B, co (x + y) = co x + co y) ∧
    (∀ (c : L) (x : (Fin a → L) ⊗[F] B), co (c • x) = (c ⊗ₜ[F] (1 : B)) • co x) ∧
    (∀ (b : B) (x : (Fin a → L) ⊗[F] B), co (AlgebraTensorModule.map (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L))
      (LinearMap.mulLeft F b) x) = ((1 : L) ⊗ₜ[F] b) • co x) ∧
    (∀ (T : End L (Fin a → L)) (A : Matrix (Fin a) (Fin a) L), (∀ v, T v = A.mulVec v) → ∀ (s : B →ₐ[F] B) (x : (Fin a → L) ⊗[F] B),
      co (AlgebraTensorModule.map T s.toLinearMap x) = (A.map (algebraMap L (L ⊗[F] B))).mulVec fun i => onR L s (co x i)) ∧
    Function.Bijective fun x : (Fin 1 → L) ⊗[F] B => co x 0

def RingS : Prop :=
  ∀ (F L U B C : Type) [Field F] [Field L] [Field U] [CommRing B] [Field C] [Algebra F L] [Algebra F U] [Algebra F B] [Algebra U B]
    [IsScalarTower F U B] [Nontrivial B] (τL : L →+* C) (τU : U →+* C), (∀ z : F, τL (algebraMap F L z) = τU (algebraMap F U z)) →
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra C S) (π : L ⊗[F] B →+* S), Nontrivial S ∧
      (∀ x : L, π (x ⊗ₜ[F] (1 : B)) = algebraMap C S (τL x)) ∧ ∀ c : U, π ((1 : L) ⊗ₜ[F] algebraMap U B c) = algebraMap C S (τU c)

def UnitOfSpan : Prop :=
  ∀ (S : Type) [CommRing S] (a : ℕ) (v : Fin a → Fin a → S), Submodule.span S (Set.range v) = ⊤ →
    IsUnit (Matrix.det (Matrix.of fun i k => v k i))

def BasisIn : Prop :=
  ∀ (C W X : Type) [Field C] [AddCommGroup W] [Module C W] [Module.Finite C W] (a : ℕ) (mk : X → W),
    Submodule.span C (Set.range mk) = ⊤ → finrank C W = a → ∃ (x : Fin a → X) (b : Basis (Fin a) C W), ∀ k, b k = mk (x k)

def DetCore : Prop :=
  ∀ (C R S W W' X X' : Type) [Field C] [CommRing R] [CommRing S] [Algebra C S] [Nontrivial S] [AddCommGroup W] [Module C W]
    [Module.Finite C W] [AddCommGroup W'] [Module C W'] [Module.Finite C W'] (a : ℕ) (π : R →+* S) (mk : X → W) (mk' : X' → W')
    (c : X → Fin a → R) (c' : X' → R) (j : W →ₗ[C] (Fin a → S)) (j' : W' →ₗ[C] S) (M : End C W) (M' : End C W')
    (w : X → X) (w' : X' → X') (A : Matrix (Fin a) (Fin a) R) (s : R →+* R),
    finrank C W = a → finrank C W' = 1 → Submodule.span C (Set.range mk) = ⊤ →
    (∀ x i, j (mk x) i = π (c x i)) → (∀ x, j' (mk' x) = π (c' x)) →
    (∀ x, M (mk x) = mk (w x)) → (∀ x, M' (mk' x) = mk' (w' x)) →
    (∀ x, c (w x) = A.mulVec fun i => s (c x i)) → (∀ x, c' (w' x) = A.det * s (c' x)) →
    (∀ x : Fin a → X, ∃ x', c' x' = Matrix.det (Matrix.of fun i k => c (x k) i)) →
    Submodule.span S (Set.range fun x i => π (c x i)) = ⊤ → LinearMap.det M = LinearMap.det M'

def WdLift : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (N : Type) [AddCommGroup N] [Module ℂ N]
    (κ : ↥(Dpst P ρ) → N), (∀ x y, κ (x + y) = κ x + κ y) →
    (∀ (c : ↥LL.1) x, κ ((Dpst P ρ).module.toSMul.smul c x) = ι (c : Om l) • κ x) →
    (∀ (c : ↥(MaximalUnramifiedExtension l)) x, κ (mulD P ρ c x) = ι (c : Om l) • κ x) → ∃ j : WDSpace P ι ρ →ₗ[ℂ] N, ∀ x, j (wdMk P ι ρ x) = κ x

def DetMem : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (a : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1))
    (ρ' : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (A : ↥(GK K) → Matrix (Fin a) (Fin a) ↥LL.1)
    (A' : ↥(GK K) → Matrix (Fin 1) (Fin 1) ↥LL.1), (∀ g v, ρ g v = (A g).mulVec v) → (∀ g v, ρ' g v = (A' g).mulVec v) →
    (∀ g, (A' g).det = (A g).det) → ∀ x : Fin a → ↥(Dpst P ρ), ∃ x' : ↥(Dpst P ρ'),
      co (x' : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) 0 =
        Matrix.det (Matrix.of fun i k => co (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)

def WeilCo : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (g : ↥(Weil h)), deg g = -1 →
    ∀ x : ↥(Dpst P ρ), (weilD Bw h P ρ g x : V ⊗[ℚ_[l]] Bst P) = AlgebraTensorModule.map (ρ (weilToGK Bw h g))
      ((actSt P (weilToGK Bw h g : GQ l)).comp (phiSt P ^ resDeg l w)).toLinearMap (x : V ⊗[ℚ_[l]] Bst P)

def SpanS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (K LL : FinExt l) (a : ℕ)
    (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1)), IsSst P ρ → ∀ (S : Type) [CommRing S] (π : ↥LL.1 ⊗[ℚ_[l]] Bst P →+* S),
    Submodule.span S (Set.range fun (x : ↥(Dpst P ρ)) i => π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) = ⊤

def CoLift : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l) (a : ℕ)
    (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1)) (S : Type) [CommRing S] [Algebra ℂ S] (π : ↥LL.1 ⊗[ℚ_[l]] Bst P →+* S),
    (∀ x : ↥LL.1, π (x ⊗ₜ[ℚ_[l]] (1 : Bst P)) = algebraMap ℂ S (ι (x : Om l))) →
    (∀ c : ↥(MaximalUnramifiedExtension l), π ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) = algebraMap ℂ S (ι (c : Om l))) →
    ∃ j : WDSpace P ι ρ →ₗ[ℂ] (Fin a → S), ∀ x i, j (wdMk P ι ρ x) i = π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)

def DetE : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (a : ℕ) (LL : FinExt l)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1) (c : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1),
    (∀ g, Matrix.GeneralLinearGroup.det (c g) = Matrix.GeneralLinearGroup.det (r g)) → IsSst P (Bw.repE LL r) →
    ∀ (hr : IsPst P (Bw.repE LL r)) (hc : IsPst P (Bw.repE LL c)) (g : ↥(Weil h)), deg g = -1 →
      haveI := hr.finite; haveI := hc.finite
      LinearMap.det (GlobalTheory.Pst.wdRho P ι Bw h hj (Bw.repE LL r) g) =
        LinearMap.det (GlobalTheory.Pst.wdRho P ι Bw h hj (Bw.repE LL c) g)

def CommonModel : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ)
    (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l)), IsCrysAt P Bw r → IsPstAt P Bw c →
    ∃ (LL : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL.1) (c' : ↥Gw →* GL (Fin 1) ↥LL.1), IsModel Bw r LL r' ∧ IsModel Bw c LL c' ∧
      IsSst P (Bw.repE LL r') ∧ IsPst P (Bw.repE LL r') ∧ IsPst P (Bw.repE LL c')

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBoundSt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.boundSt_of :
    BoundSt := by
  intro l _ P AI hT K LL
  obtain ⟨T⟩ := hT
  refine ⟨?_, fun f g => ?_⟩
  · intro U _ _ _ _ _ ρ
    rw [dinv_σSt]
    haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] U := Module.Finite.trans ↥LL.1 U
    obtain ⟨hfin, hb⟩ := GlobalTheory.CrysSst.finrank_Dst_le P AI T (GlobalTheory.PstCoeff.resQ ρ)
    have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
      ext x
      simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
    have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) =
        finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ) := by
      rw [hD, finrank_mul_finrank]
      rfl
    have hfin' : FiniteDimensional ℚ_[l] ↥((Dst P ρ).restrictScalars ℚ_[l]) := hD ▸ hfin
    haveI : Module.Finite ℚ_[l] ↥(Dst P ρ) := hfin'
    haveI hL : FiniteDimensional ↥LL.1 ↥(Dst P ρ) :=
      Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 ↥(Dst P ρ)
    refine ⟨hL, ?_⟩
    have hV : finrank ℚ_[l] U = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U :=
      (finrank_mul_finrank ℚ_[l] ↥LL.1 U).symm
    rw [e, hV] at hb
    refine Nat.le_of_mul_le_mul_left ?_ (finrank_pos (R := ℚ_[l]) (M := ↥LL.1))
    calc finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ)
        ≤ finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U * finrank ℚ_[l] ↥(K0 K) := hb
      _ = finrank ℚ_[l] ↥LL.1 * (finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 U) := by ring
  · refine Commute.pow_right ?_ f
    exact LinearMap.ext fun p => (phiSt_actSt P (g : GQ l) p).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenScale
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem prod_map_scale (z : ℂ) (s : Multiset ℂˣ) :
    (s.map fun b : ℂˣ => z * (b : ℂ)).prod = z ^ s.card * ((s.prod : ℂˣ) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, Units.val_mul, pow_succ]
    ring

private theorem lift_map {α β : Type} (f : α → β) (B : Multiset α) (t : Multiset β)
    (h : ∀ x ∈ t, x ∈ B.map f) : ∃ t' : Multiset α, t'.map f = t ∧ ∀ x ∈ t', x ∈ B :=
  _root_.UpperTheory.Reformulated.B.Qk56.lift_map f B t h

private theorem generic_scale_units (B : Multiset ℂˣ) (z : ℂ) (hz : z ≠ 0) (hB : GenericMul B) :
    GenericMul (B.map fun b : ℂˣ => z * (b : ℂ)) := by
  intro t hc hm hp
  obtain ⟨t', rfl, h2⟩ := lift_map (fun b : ℂˣ => z * (b : ℂ)) B t hm
  have hcard : t'.card = B.card := by simpa using hc
  rw [prod_map_scale, prod_map_scale, hcard] at hp
  have hprod : t'.prod = B.prod :=
    Units.ext (mul_left_cancel₀ (pow_ne_zero _ hz) hp)
  rw [hB t' hcard h2 hprod]

theorem UpperTheory.Gal.crystallineComparison.genScale_of :
    GenericScale := by
  intro B z hz hB
  have h := generic_scale_units B z hz hB
  have e : (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map fun b : ℂˣ => (b : ℂ) := by
    simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton]
  rw [e, Multiset.map_map]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilRho
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem nil_transfer {R S M W : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module S W] (φ : R →+* S) (mk : M → W) (hzero : mk 0 = 0)
    (hadd : ∀ x y, mk (x + y) = mk x + mk y) (hsmul : ∀ (a : R) x, mk (a • x) = φ a • mk x)
    (hext : ∀ f g : End S W, (∀ x, f (mk x) = g (mk x)) → f = g)
    (T : End S W) (D : End R M) (hTD : ∀ x, T (mk x) = mk (D x)) (Q : Polynomial R)
    (hQ : IsNilpotent (Polynomial.aeval D Q)) : IsNilpotent (Polynomial.aeval T (Q.map φ)) := by
  obtain ⟨N, hN⟩ := hQ
  have hpow : ∀ (n : ℕ) x, (T ^ n) (mk x) = mk ((D ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, hTD, ih]
  have key : ∀ (R' : Polynomial R) x,
      Polynomial.aeval T (R'.map φ) (mk x) = mk (Polynomial.aeval D R' x) := by
    intro R' x
    induction R' using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq, hadd]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        End.mul_apply, End.mul_apply, hpow, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply, hsmul]
  refine ⟨N, hext _ _ fun x => ?_⟩
  rw [← map_pow, ← Polynomial.map_pow, key, map_pow, hN]
  simp [hzero]

theorem UpperTheory.Gal.crystallineComparison.nilRho_of :
    NilRho := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV Q g
  haveI := hV.finite
  exact nil_transfer (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (wdMk P ι ρ) (wdMk_zero P ι ρ)
    (wdMk_add P ι ρ) (wdMk_smul P ι ρ) (fun _ _ => wd_ext P ι ρ) _ _
    (wdRho_mk P ι Bw h hj ρ g) Q
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilWeil
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section Abstract

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

private theorem pow_restr (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (m : ℕ) :
    (∀ s ∈ S, (Φ ^ m) s ∈ S) ∧ ∀ s (hs : s ∈ S), (((T ^ m) ⟨s, hSD hs⟩ : D) : M) = (Φ ^ m) s := by
  induction m with
  | zero => exact ⟨fun s hs => hs, fun s hs => rfl⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [pow_succ', End.mul_apply]
      exact hΦ _ (ih1 s hs)
    · rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply]
      have e : (T ^ m) ⟨s, hSD hs⟩ = ⟨(Φ ^ m) s, hSD (ih1 s hs)⟩ := Subtype.ext (ih2 s hs)
      rw [e, hT _ (ih1 s hs)]

private theorem aeval_restr (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (Q : Polynomial L) :
    (∀ s ∈ S, Polynomial.aeval Φ Q s ∈ S) ∧
      ∀ s (hs : s ∈ S), ((Polynomial.aeval T Q ⟨s, hSD hs⟩ : D) : M) = Polynomial.aeval Φ Q s := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [map_add (f := _), LinearMap.add_apply]
      exact add_mem (hp.1 s hs) (hq.1 s hs)
    · rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hp.2 s hs, hq.2 s hs]
  | monomial n a =>
    obtain ⟨h1, h2⟩ := pow_restr D S hSD T Φ hΦ hT n
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [Polynomial.aeval_monomial, End.mul_apply, Module.algebraMap_end_apply]
      exact S.smul_mem a (h1 s hs)
    · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, End.mul_apply, End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, h2 s hs]

private theorem aeval_commute {D : Type} [AddCommGroup D] [Module L D] (T m : End L D) (h : Commute T m)
    (Q : Polynomial L) : Commute (Polynomial.aeval T Q) m := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact Commute.mul_left (show Commute _ m from Algebra.commutes a m) (h.pow_left n)

private theorem nil_abs {U : Type} (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (Q : Polynomial L) (N : ℕ)
    (hN : ∀ s ∈ S, (Polynomial.aeval Φ Q ^ N) s = 0) (m : U → End L D) (mV : U → End L M)
    (hm : ∀ c (x : D), ((m c x : D) : M) = mV c x) (hc : ∀ c, T * m c = m c * T)
    (hcl : ∀ x : D, (x : M) ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s}) :
    IsNilpotent (Polynomial.aeval T Q) := by
  obtain ⟨a1, a2⟩ := aeval_restr D S hSD T Φ hΦ hT Q
  obtain ⟨-, b2⟩ := pow_restr D S hSD _ _ a1 a2 N
  have hkill : ∀ s (hs' : s ∈ S), (Polynomial.aeval T Q ^ N) ⟨s, hSD hs'⟩ = 0 := by
    intro s hs'
    refine Subtype.ext ?_
    rw [b2 s hs']
    exact hN s hs'
  have hcomm : ∀ c, Commute (Polynomial.aeval T Q ^ N) (m c) := fun c =>
    Commute.pow_left (aeval_commute _ _ (hc c) Q) N
  have key : ∀ y, y ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s} →
      ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0 := by
    intro y hy
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0)
      ?_ ⟨zero_mem _, map_zero _⟩ ?_ ?_ hy
    · rintro _ ⟨c, s, hs', rfl⟩
      have e : mV c s = ((m c ⟨s, hSD hs'⟩ : D) : M) := (hm c ⟨s, hSD hs'⟩).symm
      refine ⟨e ▸ (m c ⟨s, hSD hs'⟩).2, ?_⟩
      have h1 := LinearMap.congr_fun (hcomm c).eq ⟨s, hSD hs'⟩
      rw [End.mul_apply, End.mul_apply, hkill s hs', map_zero] at h1
      have h2 : (⟨mV c s, e ▸ (m c ⟨s, hSD hs'⟩).2⟩ : D) = m c ⟨s, hSD hs'⟩ := Subtype.ext e
      rw [h2]; exact h1
    · rintro a b _ _ ⟨ha, ea⟩ ⟨hb, eb⟩
      refine ⟨add_mem ha hb, ?_⟩
      have := map_add (Polynomial.aeval T Q ^ N) ⟨a, ha⟩ ⟨b, hb⟩
      rw [ea, eb, add_zero] at this
      exact this
    · rintro a _ ⟨ha, ea⟩
      refine ⟨neg_mem ha, ?_⟩
      have := map_neg (Polynomial.aeval T Q ^ N) ⟨a, ha⟩
      rw [ea, neg_zero] at this
      exact this
  refine ⟨N, LinearMap.ext fun x => ?_⟩
  obtain ⟨hy, e⟩ := key x.1 (hcl x)
  exact e

end Abstract

theorem UpperTheory.Gal.crystallineComparison.nilWeil_of :
    NilWeil := by
  intro l _ P E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV hs Q hN g hg
  haveI := hV.finite
  obtain ⟨N, hN⟩ := hN
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs =>
    (mem_Dpst P ρ).mpr ⟨Bw.Kw, fun g _ => (mem_Dst P ρ).mp hs g⟩
  have hΦ : onPer (ψSt P (resDeg l w)) ↥LL.1 V = phiV P ↥LL.1 V ^ resDeg l w := by
    change onB P ↥LL.1 V ((phiSt P).toLinearMap ^ resDeg l w) = _
    rw [map_pow]; rfl
  have hpow : ∀ (m : ℕ) (x : ↥(Dpst P ρ)),
      (((phiD P ρ ^ m) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (phiV P ↥LL.1 V ^ m) x := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, coe_phiD, ih]
  have hst : ∀ (m : ℕ), ∀ s ∈ Dst P ρ, (phiV P ↥LL.1 V ^ m) s ∈ Dst P ρ := by
    intro m s hs'
    refine (mem_Dst P ρ).mpr fun k => ?_
    have hc : Commute (phiV P ↥LL.1 V ^ m) (stRep P ρ k) := Commute.pow_left (phiV_stRep P ρ k) m
    have := LinearMap.congr_fun hc.eq s
    rw [End.mul_apply, End.mul_apply, (mem_Dst P ρ).mp hs' k] at this
    exact this.symm
  have hW : ∀ s (hs' : s ∈ Dst P ρ), ((weilD Bw h P ρ g ⟨s, hSD hs'⟩ : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      onPer (ψSt P (resDeg l w)) ↥LL.1 V s := by
    intro s hs'
    have e : -alpha l g = ((resDeg l w : ℕ) : ℤ) := by rw [alpha, hg]; ring
    rw [weilD_apply, e, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU, End.mul_apply, coe_actD, hpow, hΦ]
    exact (mem_Dst P ρ).mp (hst _ s hs') _
  have hΦS : ∀ s ∈ Dst P ρ, onPer (ψSt P (resDeg l w)) ↥LL.1 V s ∈ Dst P ρ := by
    intro s hs'
    rw [hΦ]; exact hst _ s hs'
  have hcl := mem_closure_mulV_of_finrank_eq l P Bw.Kw LL V ρ hV (Dst P ρ) le_rfl
    (fun c hc x hx => (mem_Dst P ρ).mpr fun k => by
      rw [← Module.End.mul_apply, stRep_mulV P ρ k c c (mem_GK.mp k.2 _ hc), Module.End.mul_apply,
        (mem_Dst P ρ).mp hx k]) hs
  exact nil_abs (Dpst P ρ) (Dst P ρ) hSD (weilD Bw h P ρ g) (onPer (ψSt P (resDeg l w)) ↥LL.1 V) hΦS hW Q N
    (fun s hs' => hN s hs') (mulD P ρ) (mulV P ↥LL.1 V) (fun _ _ => rfl) (weilD_mulD Bw h P ρ hj g) (fun x => hcl x.1 x.2)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSatGeom
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem coe_bind (B : Multiset ℂˣ) :
    (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map fun b : ℂˣ => (b : ℂ) := by
  show B.bind (fun b => {(b : ℂ)}) = _
  exact Multiset.bind_singleton B _

theorem UpperTheory.Gal.crystallineComparison.satGeom_of :
    SatGeom := by
  intro E Ω _ _ _ _ _ A w h a B
  have h0 : (0 : ℂ) ∉ B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)) := by
    simp
  refine ⟨?_, ?_⟩
  · show ((WD.lpUnr h _).lpTw _).unr
    rw [WD.unr_tw]
    exact (WD.lpUnr_spec _ h0).1
  intro g hg
  show ((WD.lpUnr h _).lpTw _).charPol g = _
  unfold WD.lpUnr
  rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hg, coe_bind]
  have hsm : ∀ (s : ℂ) {ι : Type} (f : ι → ℂ), s • diagEnd f = diagEnd (fun i => s * f i) := by
    intro s ι f
    ext v i
    simp [diagEnd, mul_assoc]
  rw [hsm, charpoly_diagEnd, Finset.prod_eq_multiset_prod]
  set s : ℂ := (↑(normV w) ^ (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)) ^ (-1 : ℤ) with hs
  refine (congrArg Multiset.prod (Multiset.map_univ (B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)))
    (fun x => Polynomial.X - Polynomial.C (s * ↑(WD.unitOf x) ^ (-1 : ℤ))))).trans ?_
  unfold rootPol
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro b _
  simp only [Function.comp_apply]
  have hs' : s = (normV w : ℂ) ^ (((a : ℂ) - 1) / 2) := by
    rw [hs, zpow_neg_one, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [WD.coe_unitOf (Units.ne_zero _), Units.val_inv_eq_inv_val, zpow_neg_one, inv_inv, hs']
end

