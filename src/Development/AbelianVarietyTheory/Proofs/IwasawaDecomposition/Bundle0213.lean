module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

variable {D : D7}

def lift {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S)) (𝓕 : Set (GA D S))
    (Φ : GA D S → WO S T → ℂ) : GA D T → ℂ :=
  fun g => ∫ h in 𝓕, thetaKO om h g (Φ h) ∂ν

def along (S T : HSp D) (ξ : Fin T.rank → D.host.E) (a : Fin S.rank → AE D) : WO S T :=
  Matrix.vecMulVec (fun i => incA D (ξ i)) a


open Classical in
def KEquiv (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M) : Prop :=
  ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (e : ∀ τ', lowT M τ') (w : lowT M τ),
    ((w : M.sm τ) : M.H τ) = M.σ τ k ((e τ : M.sm τ) : M.H τ) →
      U (Function.update e τ w) = rTr V (atTau θ V τ ((M.fr τ)⁻¹ * k * M.fr τ)) (U e)

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem eq_top_of_translates (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (τ : D.what₂.Tau) (N : Submodule ℂ (lowT M τ))
    (v : lowT M τ) (hv : v ≠ 0)
    (hN : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ u : lowT M τ,
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v : M.sm τ) : M.H τ) → u ∈ N) : N = ⊤ := by
  have hU := (M.ds τ).2.2.1
  let P : Submodule ℂ (M.H τ) := Submodule.span ℂ {y | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), y = M.σ τ k ((v : M.sm τ) : M.H τ)}
  have hvL : ((v : M.sm τ) : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := v.2
  have hPle : P ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, rfl⟩
    exact (h2 τ).2.1 k hk _ hvL)
  have hmul : ∀ a ∈ Formalism.REAL.Kset (M.ε τ), ∀ b ∈ Formalism.REAL.Kset (M.ε τ), a * b ∈ Formalism.REAL.Kset (M.ε τ) := by
    intro a ha b hb
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
  have hone : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ) := ⟨one_mem _, by simp⟩
  have hst : IsKStableOn (M.ε τ) (M.σ τ) P := by
    intro g hg y hy
    refine Submodule.span_induction (p := fun y _ => M.σ τ g y ∈ P) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨k, hk, rfl⟩
      refine Submodule.subset_span ⟨g * k, hmul g hg k hk, ?_⟩
      rw [hU.1.2 _ (kset_uj hg) _ (kset_uj hk)]
      rfl
    · rw [map_zero]; exact P.zero_mem
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact P.add_mem hx hy
    · intro a x _ hx; rw [map_smul]; exact P.smul_mem a hx
  have hP : P = lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := by
    refine ((h2 τ).2.2.1 P hPle hst).resolve_left fun h0 => hv ?_
    have : M.σ τ 1 ((v : M.sm τ) : M.H τ) ∈ P := Submodule.subset_span ⟨1, hone, rfl⟩
    rw [h0, hU.1.1] at this
    exact Subtype.ext (Subtype.ext this)
  rw [eq_top_iff]
  intro u _
  have hu : ((u : M.sm τ) : M.H τ) ∈ P := hP ▸ u.2
  have key : ∀ y (hy : y ∈ P), (⟨⟨y, h1 τ (hPle hy)⟩, hPle hy⟩ : lowT M τ) ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, e⟩ := hy
      exact hN k hk _ e
    | zero => exact N.zero_mem
    | add x y _ _ hx hy => exact N.add_mem hx hy
    | smul a x _ hx => exact N.smul_mem a hx
  exact key _ hu


open Classical in
theorem mem_of_translates (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (B : MultilinearMap (RingHom.id ℂ) (fun τ => lowT M τ) Y) (N : Submodule ℂ Y) (v₀ : ∀ τ, lowT M τ) (h0 : ∀ τ, v₀ τ ≠ 0)
    (hB : B v₀ ∈ N)
    (hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → B v ∈ N → B (Function.update v τ u) ∈ N)
    (v : ∀ τ, lowT M τ) : B v ∈ N := by
  have key : ∀ s : Finset D.what₂.Tau, B (s.piecewise v v₀) ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hB
    | insert τ s hτ ih =>
      have e0 : s.piecewise v v₀ τ = v₀ τ := Finset.piecewise_eq_of_notMem _ _ _ hτ
      have := eq_top_of_translates h1 h2 τ (N.comap (B.toLinearMap (s.piecewise v v₀) τ)) (v₀ τ) (h0 τ)
        fun k hk u hu => hK τ k hk _ u (by rw [e0]; exact hu) ih
      rw [Finset.piecewise_insert]
      exact (this.ge Submodule.mem_top : v τ ∈ N.comap (B.toLinearMap (s.piecewise v v₀) τ))
  simpa using key Finset.univ

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomEndomorphismOfSpanIntertwiners
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.FinPart

open scoped MonoidAlgebra

theorem exists_algHom_end_of_span_intertwiners :
    ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V),
      σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ →
      ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  intro H W V _ _ _ _ _ _ σ ρ hirr hspan
  classical

  have hsurj : Function.Surjective σ.asAlgebraHom := by
    have hB := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hirr
    have hle : Submodule.span ℂ (Set.range σ) ≤ Subalgebra.toSubmodule σ.asAlgebraHom.range := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      exact ⟨MonoidAlgebra.single h 1, by simp [Representation.asAlgebraHom_single]⟩
    intro A
    have : A ∈ Subalgebra.toSubmodule σ.asAlgebraHom.range := hle (hB ▸ Submodule.mem_top)
    exact this

  have hint : ∀ (f : σ.IntertwiningMap ρ) (a : MonoidAlgebra ℂ H) (w : W),
      ρ.asAlgebraHom a (f.toLinearMap w) = f.toLinearMap (σ.asAlgebraHom a w) := by
    intro f a w
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add (f := _)]
    | single g c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
      congr 1
      exact (Representation.IntertwiningMap.isIntertwining σ ρ f g w).symm
  have hker : RingHom.ker σ.asAlgebraHom ≤ RingHom.ker ρ.asAlgebraHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤
        LinearMap.ker (ρ.asAlgebraHom a) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, hint, ha]
      simp
    rw [hspan, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle
  let Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V :=
    (Ideal.Quotient.liftₐ (RingHom.ker σ.asAlgebraHom) ρ.asAlgebraHom hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hΦ : ∀ a, Φ (σ.asAlgebraHom a) = ρ.asAlgebraHom a := by
    intro a
    have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a) =
        Ideal.Quotient.mk _ a := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change Ideal.Quotient.liftₐ _ _ hker ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a)) = _
    rw [this]
    rfl
  refine ⟨Φ, fun h => ?_, fun T hT A => ?_⟩
  · have := hΦ (MonoidAlgebra.single h 1)
    simpa [Representation.asAlgebraHom_single] using this
  · obtain ⟨a, rfl⟩ := hsurj A
    rw [hΦ]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _)]; exact hx.add_right hy
    | single g c =>
      rw [Representation.asAlgebraHom_single]
      exact (hT g).smul_right c

end GlobalTheory.FinPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesField
section
noncomputable section

namespace GlobalTheory.Mem.PlaceVal

section General

open Formalism.L2.DIV Formalism.BasicNotions Formalism.BasicNotions.TH

theorem exists_ext_pol {K K' I W : Type} [Field K] [Field K'] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ} (ι : K →+* K')
    (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) (U : Submodule K (MvPolynomial I K)) (c : U →ₛₗ[σ] W) :
    ∃ c' : MvPolynomial I K' →ₛₗ[σ'] W, ∀ v : U, c' (MvPolynomial.map ι (v : MvPolynomial I K)) = c v := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  let _ : Module K' W := Module.compHom W σ'
  let f : MvPolynomial I K' →ₗ[K'] W :=
    (MvPolynomial.basisMonomials I K').constr K' fun m => c (π (MvPolynomial.monomial m 1))
  have hf : ∀ m, f (MvPolynomial.monomial m 1) = c (π (MvPolynomial.monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials I K').constr_basis K' (fun m => c (π (MvPolynomial.monomial m 1))) m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have key : ∀ p : MvPolynomial I K, f (MvPolynomial.map ι p) = c (π p) := fun p => by
    induction p using MvPolynomial.induction_on' with
    | monomial m a =>
      have e1 : MvPolynomial.map ι (MvPolynomial.monomial m a) = ι a • MvPolynomial.monomial m (1 : K') := by
        rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      have e2 : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : K) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [e1, f.map_smul, hf, e2, π.map_smul, map_smulₛₗ, ← RingHom.congr_fun hσ a]
      rfl
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  refine ⟨{ toFun := f, map_add' := f.map_add, map_smul' := fun a p => f.map_smul a p }, fun v => (key v).trans ?_⟩
  exact congrArg c (LinearMap.congr_fun hπ v)

theorem exists_ext_VV {K K' I W : Type} [Field K] [Field K'] [Fintype I] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}
    (ι : K →+* K') (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) {n : ℕ} (lam : I → DomWeight n) (c : VV K lam →ₛₗ[σ] W) :
    ∃ c' : VV K' lam →ₛₗ[σ'] W, ∀ v : VV K lam, ∃ v' : VV K' lam,
      (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) ∧ c' v' = c v := by
  obtain ⟨c', hc⟩ := exists_ext_pol ι σ' hσ (VV K lam) c
  exact ⟨c'.comp (VV K' lam).subtype, fun v => ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩, rfl, hc v⟩⟩

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem exists_coef_placeEx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, (∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0') ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR _ _ i K' _ jL σ' hσ
  obtain ⟨gramR, c0R, c0L, hT⟩ := hR.fam.tie
  obtain ⟨c0', hc⟩ := exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', ⟨gramR, c0R, c0L, hT, hc⟩, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal⟩

end GlobalTheory.Mem.PlaceVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColsRowsRestPos
section
noncomputable section

namespace GlobalTheory.Mem.RowsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

abbrev Euc (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

def stdOLat (O : Type) [CommRing O] (φ : O →+* ℂ) (n : ℕ) : Rows.OLat O φ (Euc n) := by
  classical
  exact
    { gen := Finset.univ.image (fun i => EuclideanSpace.basisFun (Fin n) ℂ i)
      span_top := by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq }

theorem mem_stdOLat {O : Type} [CommRing O] {φ : O →+* ℂ} {n : ℕ} {x : Euc n}
    (hx : x ∈ (stdOLat O φ n).gen) : ∃ i, EuclideanSpace.basisFun (Fin n) ℂ i = x := by
  classical
  simpa [stdOLat] using hx

def coordEmb {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) : (Fin n → K) →ₛₗ[σ] Euc n where
  toFun x := WithLp.toLp 2 (fun i => σ (x i))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem coordEmb_single {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) (i : Fin n) :
    coordEmb σ n (Pi.single i 1) = EuclideanSpace.basisFun (Fin n) ℂ i := by
  ext j
  by_cases h : j = i
  · subst h; simp [coordEmb]
  · simp [coordEmb, h]

theorem coordEmb_basis {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) {ι : Type}
    (b : Module.Basis ι K (Fin n → K)) :
    LinearIndependent ℂ (fun i => coordEmb σ n (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) = ⊤ := by
  classical
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hs : ⊤ ≤ Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [OrthonormalBasis.coe_toBasis, ← coordEmb_single σ, ← b.sum_repr (Pi.single i 1), map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hs ?_, top_le_iff.mp hs⟩
  rw [← Module.finrank_eq_card_basis b]
  simp

theorem exists_frame {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (c : InnerProductSpace.Core ℂ V) :
    ∃ e : Euc (Module.finrank ℂ V) ≃ₗ[ℂ] V, ∀ x y, inner ℂ x y = c.inner (e x) (e y) := by
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  refine ⟨(stdOrthonormalBasis ℂ V).repr.symm.toLinearEquiv, fun x y => ?_⟩
  exact ((stdOrthonormalBasis ℂ V).repr.symm.inner_map_map x y).symm

variable {B : Base} (C : Cols B)

def ramCore (u : B.Word)
    (h1 : ∀ φ ∈ (C.mem u).A.Mram, ∀ ψ ∈ (C.mem u).A.Mram,
      (C.fm u).ipC 0 ψ φ = starRingEnd ℂ ((C.fm u).ipC 0 φ ψ))
    (h2 : ∀ φ ∈ (C.mem u).A.Mram, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re) :
    InnerProductSpace.Core ℂ (C.mem u).A.Mram where
  inner φ ψ := (C.fm u).ipC 0 φ.1 ψ.1
  conj_inner_symm φ ψ := (h1 ψ.1 ψ.2 φ.1 φ.2).symm
  re_inner_nonneg φ := by
    by_cases h : φ.1 = 0
    · show 0 ≤ ((C.fm u).ipC 0 φ.1 φ.1).re
      rw [h]
      simp [MemberForms.ipC]
    · exact (h2 φ.1 φ.2 h).le
  add_left φ ψ χ := by
    show (C.fm u).ipC 0 (φ.1 + ψ.1) χ.1 = _
    simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left φ ψ r := by
    show (C.fm u).ipC 0 (r • φ.1) ψ.1 = _
    simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm]
  definite φ h := by
    by_contra hne
    have := h2 φ.1 φ.2 (fun h0 => hne (Subtype.ext h0))
    change (C.fm u).ipC 0 φ.1 φ.1 = 0 at h
    rw [h] at this
    simp at this

theorem mram_fd (u : B.Word) : FiniteDimensional ℂ (C.mem u).A.Mram := by
  have := (C.mem u).A.Mu0_fd
  exact Submodule.finiteDimensional_of_le (show (C.mem u).A.Mram ≤ (C.mem u).A.Mu0 from inf_le_left)

def eucCast {a b : ℕ} (h : a = b) : Euc a ≃ₗᵢ[ℂ] Euc b :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)


open Classical in
def model (n : C.Tup → ℕ) (D : ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Euc (n C.mu0)) (eTw : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] Euc (n μ))
    (eM : ∀ u, Euc (C.mem u).A.du ≃ₗ[ℂ] (C.mem u).A.Mram)
    (heM : ∀ u φ ψ, inner ℂ φ ψ = (C.fm u).ipC 0 (eM u φ).1 (eM u ψ).1) : RowsRest B C where
  muAt _ := C.mu0
  muAt_conj _ := rfl
  muTw _ := C.mu0
  muTw_conj _ := rfl
  muAt_or _ := Or.inl rfl
  EE := Euc D
  Drows := D
  onb := EuclideanSpace.basisFun (Fin D) ℂ
  Dall := D
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Euc D
  D0 := D
  onb0 := EuclideanSpace.basisFun (Fin D) ℂ
  FT := Unit
  ft _ := ()
  ft0 _ := ()
  Amb μ := Euc (n μ)
  Mult μ j := Euc (if j = 0 then D else n μ)
  multZero _ := eucCast (if_pos rfl)
  multTop _ := eucCast (if_neg (by have := B.R.two_le_m; omega))
  io _ _ := Matrix.toEuclideanLin (Matrix.of fun a b => if (a : ℕ) = (b : ℕ) then 1 else 0)
  Mtilde μ := stdOLat _ _ (n μ)
  eOp _ := LinearMap.id
  eOp_idem _ := rfl
  eOp_sa _ _ _ := rfl
  Mu u := Euc (C.mem u).A.du
  perCol u μ φ F :=
    if h : μ = C.mu0 then (C.mem u).P.PtilCol (eM u φ).1 ((e0 u).symm (eucCast (congrArg n h) F))
    else (C.PTw u μ).PtilCol (C.e0Tw u μ (eM u φ).1) ((eTw u μ).symm F)
  Bu _ φ F := (∑ a, φ a) * ∑ b, F b
  ze _ _ := 1
  rowsRest_wordColumnUnit_baseTuple _ := rfl
  Mj _ := Euc D
  MjLat _ := stdOLat _ _ D
  kaBig _ _ _ := 0
  kaSmall _ _ _ := 0
  Mt _ _ := Euc D
  MtLat _ _ := stdOLat _ _ D
  MtL _ _ := Fin D → B.LL
  jMt _ _ := coordEmb B.embLL D
  jMt_basis _ _ b := coordEmb_basis B.embLL D b
  MtLat_sub _ _ x hx := by
    obtain ⟨i, rfl⟩ := mem_stdOLat hx
    exact ⟨_, coordEmb_single _ _ i⟩
  eMt _ _ := LinearMap.id
  eMt_idem _ _ := rfl
  eMt_sa _ _ _ _ := rfl
  eMt_LL _ _ x := ⟨x, rfl⟩
  thetaP _ _ := LinearMap.id
  isot _ _ := ⊤
  lamP _ _ _ := 1
  Ij _ _ _ := 0
  jw _ _ _ := 0
  etaJ _ _ := 0
  etaJ_nonneg _ _ := le_rfl
  shaLen _ _ := 0
  shaLen_nonneg _ _ := le_rfl
  eMu := eM
  eMt0 := e0
  perCol_base_eq_PtilCol u φ F := by
    rw [dite_eq_left rfl]
    rfl
  Bu_linL _ F := ⟨fun φ ψ => by simp [Finset.sum_add_distrib, add_mul],
    fun a φ => by simp [← Finset.mul_sum, mul_assoc]⟩
  Bu_linR _ φ := ⟨fun F G => by simp [Finset.sum_add_distrib, mul_add],
    fun a F => by simp [← Finset.mul_sum, mul_left_comm]⟩
  eMtTw := eTw
  perCol_tie u μ h φ F := dif_neg h
  eMu_isom := heM

end GlobalTheory.Mem.RowsModel

namespace GlobalTheory.Mem


theorem RowsModel.ipC_cols (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 φ ψ = ∑ c, starRingEnd ℂ (φ c ()) * ψ c () := by
  refine Finset.sum_congr rfl fun c _ => ?_
  show ((Nat.card PUnit : ℕ) : ℂ)⁻¹ * (starRingEnd ℂ (φ c ()) * ψ c ()) = _
  simp


end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.CuspRep.CompUniq

theorem isotypic : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  intro G H V W W' _ _ _ _ _ _ _ _ ρ s σ σ' hρ hσ hσ' hc f hf
  have hP : GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) = ⊤ := by
    rcases ((isIrreducible_iff ρ).1 hρ).2 (GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s)) (fun g v hv => by
      obtain ⟨u, hu⟩ := hc g
      have h1 := GlobalTheory.CuspRep.LocUniq.isoPart_comm σ (ρ.comp s) (ρ ((s u)⁻¹ * g)) (fun y x => by
        simp only [MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, (hu y).eq]) hv
      have h2 := GlobalTheory.CuspRep.LocUniq.isoPart_act σ (ρ.comp s) u h1
      rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h2) with h | h
    · refine absurd ?_ hf
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine LinearMap.ext fun v => ?_
      have h3 : f.toLinearMap v ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) :=
        Submodule.mem_iSup_of_mem f ⟨v, rfl⟩
      rw [h] at h3
      rw [(Submodule.mem_bot ℂ).1 h3]
      rfl
    · exact h
  refine ⟨hP, fun f' hf' => ?_⟩
  haveI := hσ
  haveI := hσ'
  exact GlobalTheory.CuspRep.LocUniq.equiv_of_isoPart σ σ' (ρ.comp s) hP f' hf'

end GlobalTheory.CuspRep.CompUniq
end

