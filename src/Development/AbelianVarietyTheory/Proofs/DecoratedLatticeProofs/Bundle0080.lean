module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.Bundle0022
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.Bundle0024
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalRingCardinality.Bundle0005
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalRingCardinality.DataArith
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.FormalDegreeBessel.StatementIO
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassLatticeSelfDual
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.ClassLatticeSelfDual

section General

open Formalism.UG Formalism.UG.P
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]


omit [NumberField F] [DecidableEq n] [Fintype n] in
theorem mem_span_of_mem_latS (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] (S : Subring (E ⊗[F] R))
    (L : Submodule (𝓞 E) (n → E)) (x : n → E)
    (hx : (fun i => inclE (F := F) R (x i)) ∈ latS (F := F) R S L) :
    x ∈ Submodule.span E (L : Set (n → E)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R →ₗ[F] F, φ 1 = 1 := Module.Projective.exists_dual_eq_one F one_ne_zero
  let π : E ⊗[F] R →ₗ[E] E :=
    (TensorProduct.AlgebraTensorModule.rid F E E).toLinearMap ∘ₗ (φ.baseChange E)
  have hπ : ∀ (s : E ⊗[F] R) (a : E), π (s * inclE (F := F) R a) = π s * a := by
    intro s a
    have : s * inclE (F := F) R a = a • s := by
      rw [mul_comm, Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have hπ1 : π 1 = 1 := by
    simp [π, Algebra.TensorProduct.one_def, hφ]
  have key : ∀ u ∈ latS (F := F) R S L, ∀ s : E ⊗[F] R,
      (fun i => π (s * u i)) ∈ Submodule.span E (L : Set (n → E)) := by
    intro u hu
    unfold latS at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      intro s
      have : (fun i => π (s * inclE (F := F) R (y i))) = π s • y := by
        funext i; rw [hπ]; rfl
      exact this ▸ Submodule.smul_mem _ _ (Submodule.subset_span hy)
    | zero =>
      intro s
      have : (fun i => π (s * (0 : n → E ⊗[F] R) i)) = 0 := by funext i; simp
      exact this ▸ zero_mem _
    | add u u' _ _ h h' =>
      intro s
      have : (fun i => π (s * (u + u') i)) = (fun i => π (s * u i)) + fun i => π (s * u' i) := by
        funext i; simp [mul_add]
      exact this ▸ add_mem (h s) (h' s)
    | smul r u _ h =>
      intro s
      have : (fun i => π (s * (r • u) i)) = fun i => π ((s * (r : E ⊗[F] R)) * u i) := by
        funext i; rw [mul_assoc]; rfl
      exact this ▸ h _
  have h := key _ hx 1
  have e : (fun i => π (1 * inclE (F := F) R (x i))) = x := by
    funext i; rw [hπ, hπ1, one_mul]
  rwa [e] at h

theorem eq_globLat (Λ L : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (hL : Module.Finite (𝓞 E) L)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : ∀ x : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (g⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) :
    L = CS.globLat g Λ := by
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨p, hp⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨p, hp.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h1 : (0 : FiniteAdeleRing (𝓞 F) F) v = (1 : FiniteAdeleRing (𝓞 F) F) v := by rw [h]
    exact (zero_ne_one : (0 : v.adicCompletion F) ≠ 1) h1
  have hG := csGlob_lattice (F := F) Λ hfin hspan g
  have hLs : Submodule.span E (L : Set (n → E)) = ⊤ := by
    rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
    intro x hx
    exact mem_span_of_mem_latS (F := F) _ _ L x ((h _).2 hx)
  ext x
  conv_lhs => rw [← global_lattice_one_holds F E n L hL hLs]
  refine Iff.trans ?_ (h _)
  show ((1⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔ _
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

end General

theorem classLattice_selfDual : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (c : (D.fm u).clsP), Submodule.IsLattice D.host.E (K.lat c) ∧ ∀ y, y ∈ K.lat c ↔ ∀ x ∈ K.lat c, Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro D u K c
  have e := eq_globLat (F := D.host.F) K.lev.Lb (K.lat c) K.lev.Lb_fin K.lev.Lb_span (K.lat_fin c) (K.y c).1 (K.y_lat c)
  have hdual : ∀ x, x ∈ K.lev.Lb ↔ ∀ y ∈ K.lev.Lb,
      Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro x
    refine ⟨fun hx => K.lev.Lb_int x hx, fun hx => ?_⟩
    have := K.lev.Lb_dual x hx
    rwa [Nat.cast_one, one_smul] at this
  rw [e]
  exact ⟨(Formalism.UG.P.csGlob_lattice (F := D.host.F) _ K.lev.Lb_fin K.lev.Lb_span _).toIsLattice,
    fun y => GlobalTheory.PointLattice.globLat_selfDual (sigD D) (gramP D) _ hdual K.lev.Lb_fin K.lev.Lb_span _ (K.y c).2 y⟩

end GlobalTheory.ClassLatticeSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParam
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section
namespace GlobalTheory.CoverDS

theorem unitEquiv_of_dsUnique : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  intro hU p q hn T R R' lam hl hR hR'
  have h0 : 0 < p + q := hn
  obtain ⟨P, e, -, h, rfl | rfl⟩ := GlobalTheory.RealPar.isParam_cases hl
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x]
    exact hV _ (h.cov_mem T x) v
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_half_iff R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_half_iff R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
    rw [hV _ (h.cov_mem T x) v]

end GlobalTheory.CoverDS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeries
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverExhaust

variable {p q n : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (finSumFinEquiv : Ix p q ≃ Fin (p + q)) fun i => (finSumFinEquiv.symm i).isLeft := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · exact hab
  · exact hab.elim
  · exact hab.elim
  · exact Nat.add_lt_add_left hab p

theorem blockOrd_perm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : BlockOrd (e.trans s.symm) (ε ∘ s) := by
  refine ⟨fun i => by simpa using h.1 i, fun j => by simpa using h.2.1 j, ?_⟩
  intro a b hab
  obtain ⟨hlt, hε⟩ := (h.posC_iff a b).1 hab
  simp only [Equiv.trans_apply]
  rcases lt_trichotomy (s.symm (e a)) (s.symm (e b)) with h1 | h1 | h1
  · exact h1
  · exact absurd (s.symm.injective h1) (ne_of_lt hlt)
  · have h2 := hs _ _ h1 (by simp only [Equiv.apply_symm_apply]; exact hε.symm)
    simp only [Equiv.apply_symm_apply] at h2
    exact absurd h2 (not_lt.2 hlt.le)

theorem exists_param_of_trivial (hE : GlobalTheory.Dec.DSExhaust) {T : GrpData p q} (R : DSRep T)
    (k : ∀ x, T.cov x = 1 → R.U.π x = 1) :
    ∃ (P : SignedPar (p + q)) (e : Ix p q ≃ Fin (p + q)), BlockOrd e P.sgn ∧ HasParam R (blockPar P e) := by
  obtain ⟨σ, hF⟩ := exists_factors R.U (finSumFinEquiv : Ix p q ≃ Fin (p + q)) k
  have hB0 := blockOrd_std p q
  have hIrr : GlobalTheory.Dec.IsSqIntIrr (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) σ :=
    ⟨R.U.cs, R.nontriv,
      (_root_.GlobalTheory.RealPar.CoverURep.urep_irred p q (p + q) _ _ T R σ hB0 hF).1,
      (_root_.GlobalTheory.RealPar.CoverURep.urep_irred p q (p + q) _ _ T R σ hB0 hF).2,
      _root_.GlobalTheory.RealPar.SqInt.isSqIntOn_of_factors p q (p + q) _ _ T R σ hB0 hF⟩
  obtain ⟨s, mu, hc, hs, hDS⟩ := hE (p + q) _ R.U.H σ hIrr
  let P : SignedPar (p + q) := ⟨mu, (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) ∘ s, hc⟩
  have hB : BlockOrd ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm) P.sgn := blockOrd_perm hB0 s hs
  have hF' : Factors R.U ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm)
      (fun g => σ (g.submatrix s.symm s.symm)) := by
    intro x
    rw [hF x]
    congr 1
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact ⟨P, _, hB, (hasParam_iff_isDSPar R P hB hF').2 hDS⟩

theorem exists_param : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  intro hE p q _ T R
  rcases Cover.trivial_or_twist R with k | k
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE R k
    exact ⟨_, isParam_blockPar P h1, h2⟩
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE (Cover.twist R) k
    exact ⟨_, isParam_half P h1, (Cover.hasParam_twist R _).1 h2⟩

end GlobalTheory.CoverExhaust
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanCoefficients
section
namespace GlobalTheory.CoefficientSpanFinite

theorem finiteDimensional_span_coefficients {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) :
    FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let Φ : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range Φ := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ∘ₗ LinearMap.applyₗ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CoefficientSpanFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FnOfMapInjective
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Core

theorem fnOf_map_injective {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (sh : ι → ℤ) (s : K →+* ℂ) {F F' : MvPolynomial (ι × Fin n × Fin n) K}
    (h : fnOf G sh 1 (MvPolynomial.map s F) = fnOf G sh 1 (MvPolynomial.map s F')) : F = F' :=
  MvPolynomial.map_injective s s.injective
    (Formalism.L2.Col.fnOf_injective G sh 1 (fun _ => by simp)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}) h)

theorem exists_ptVal_at (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K) (x : (D.fm u).ptLat.V)
    (c : (D.fm u).clsP) : ∃ F : VV D.what₂.LL (sgT u),
      W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL F.1) := by
  obtain ⟨P, hP, hv⟩ := ((W.rat _).1 ⟨x, rfl⟩).2 c
  have e : Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) = Formalism.L2.Col.RatSpanG D.what₂.embLL (D.fm u).sg :=
    Formalism.L2.Col.RatSpanG_shW D.what₂.embLL (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
  have hP' : P ∈ Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) := by rw [e]; exact hP
  obtain ⟨F, hF, rfl⟩ := Formalism.L2.Col.exists_VV_of_mem_RatSpanG _ _ hP'
  exact ⟨⟨F, hF⟩, hv⟩

theorem exists_ptVal : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K), ∃ val : (D.fm u).ptLat.V →ₗ[D.what₂.LL] ((D.fm u).clsP → VV D.what₂.LL (sgT u)), (∀ x c, W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (val x c).1)) := by
  intro D u K W
  choose val hval using exists_ptVal_at D u K W
  refine ⟨{ toFun := val, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hval⟩
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    rw [← hval, Pi.add_apply, Submodule.coe_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ← hval, ← hval, Pi.add_apply]
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    have e : MvPolynomial.map D.what₂.embLL (a • (val x c).1) =
        D.what₂.embLL a • MvPolynomial.map D.what₂.embLL (val x c).1 := by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    rw [← hval, RingHom.id_apply, Pi.smul_apply, Submodule.coe_smul, e, LinearMap.map_smul, ← hval,
      LinearMap.map_smulₛₗ, LinearEquiv.map_smul, Pi.smul_apply]

end GlobalTheory.Core
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfSqrtDetTwist
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section

namespace GlobalTheory.CoverDS.TwistTypes

variable {p q : ℕ}

theorem sum_rhoNC (lam : Ix p q → ℚ) : ∑ a, rhoNC lam a = 0 := by
  have symm : ∀ a b : Ix p q, sameBlock a b ↔ sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  have k1 : ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  have k2 : ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  simp only [rhoNC, Finset.sum_sub_distrib, ← Finset.sum_div, k1, k2, sub_self, zero_div]

theorem normSq_add_half (lam : Ix p q → ℚ) :
    normSq (fun a => lam a + 1 / 2) =
      normSq lam + ∑ a, (lam a + 1 / 2) - (Fintype.card (Ix p q) : ℚ) / 4 := by
  have e : ∀ a, (lam a + 1 / 2) ^ 2 = lam a ^ 2 + (lam a + 1 / 2) - 1 / 4 := fun a => by ring
  simp only [normSq, e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem casimir_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) :
    casimir (Cover.twAct act) v = casimir act v - act 1 v + ((Fintype.card (Ix p q) : ℂ) / 4) • v := by
  have hterm : ∀ a b, Cover.twAct act (Eab a b) (Cover.twAct act (Eab b a) v) =
      act (Eab a b) (act (Eab b a) v) - if a = b then act (Eab a a) v - (1 / 4 : ℂ) • v else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [Cover.twAct_apply, if_true, Eab, Matrix.trace_single_eq_same, map_sub, map_smul]
      module
    · simp [Cover.twAct_apply, hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab,
        Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]
  have h1 : act 1 v = ∑ a, act (Eab a a) v := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Matrix.sum_single_one, map_sum, LinearMap.sum_apply]
    rfl
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h1, Finset.sum_const, Finset.card_univ]
  module

theorem hwSub_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) :
    hwSub (Cover.twAct act) μ = hwSub act fun a => μ a + 1 / 2 := by
  ext v
  by_cases hv : v = 0
  · subst hv
    exact iff_of_true (Submodule.zero_mem _) (Submodule.zero_mem _)
  · exact ⟨fun h => ((Cover.isHW_twAct act μ v).1 ⟨hv, h⟩).2, fun h => ((Cover.isHW_twAct act μ v).2 ⟨hv, h⟩).2⟩

theorem sum_of_inCone {lam μ : Ix p q → ℚ} (h : InCone lam μ) : ∑ a, μ a = ∑ a, lam a := by
  obtain ⟨m, -, rfl⟩ := h
  have e : ∑ c, ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib, e, blattner, sum_rhoNC, add_zero]

theorem inCone_add {lam μ : Ix p q → ℚ} (c : ℚ) (h : InCone lam fun a => μ a - c) :
    InCone (fun a => lam a + c) μ := by
  obtain ⟨m, hm, hμ⟩ := h
  refine ⟨m, fun a b hab => add_lt_add_left (hm a b hab) c, funext fun a => ?_⟩
  have := congrFun hμ a
  rw [Cover.blattner_add]
  simp only at this ⊢
  linarith

theorem hasTypes_of_twist (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ)
    (h : HasTypes (Cover.twist R) lam) : HasTypes R fun a => lam a + 1 / 2 := by
  have h1 : Module.finrank ℂ ↥(hwSub (Cover.twAct R.HK.act) (blattner lam)) = 1 := h.1
  have h2 : ∀ v, casimir (Cover.twAct R.HK.act) v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v := h.2.1
  have h3 : ∀ (μ : Ix p q → ℚ) v, IsHW (Cover.twAct R.HK.act) μ v → InCone lam μ := h.2.2
  have hcone : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (fun a => lam a + 1 / 2) μ := fun μ v hv =>
    inCone_add _ (h3 _ v ((Cover.isHW_twAct _ _ v).2 (by simpa only [sub_add_cancel] using hv)))
  refine ⟨by rwa [Cover.blattner_add, ← hwSub_twAct], fun v => ?_, hcone⟩
  set c : ℂ := ((∑ a, (lam a + 1 / 2) : ℚ) : ℂ) with hc
  have htop : LinearMap.ker (R.HK.act 1 - c • LinearMap.id) = ⊤ := by
    refine _root_.GlobalTheory.HwSpan.eq_top_of_hwSub_le p q R.HK _ (fun X _ w hw => ?_) fun μ w hw => ?_
    · have e := congrArg (fun f : Module.End ℂ R.HK.V => f w) (R.HK.lie X 1)
      simp only [Matrix.mul_one, Matrix.one_mul, sub_self, map_zero, LinearMap.zero_apply, LinearMap.sub_apply,
        Module.End.mul_apply] at e
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw ⊢
      rw [← sub_eq_zero.1 e.symm, hw, map_smul]
    · by_cases h0 : w = 0
      · rw [h0]
        exact Submodule.zero_mem _
      have e := sum_of_inCone (hcone μ w ⟨h0, hw⟩)
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc, ← e, ← Matrix.sum_single_one, map_sum, LinearMap.sum_apply, Rat.cast_sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun a _ => ((mem_hwSub_iff _ _ _).1 hw).1 a
  have hv : R.HK.act 1 v = c • v := by
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      using Submodule.eq_top_iff'.1 htop v
  have e := casimir_twAct R.HK.act v
  rw [h2, hv] at e
  rw [normSq_add_half, Rat.cast_sub, Rat.cast_sub, Rat.cast_add, ← hc]
  rw [Rat.cast_sub] at e
  push_cast
  linear_combination (norm := module) -e

end GlobalTheory.CoverDS.TwistTypes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelFiniteDatumBoundedLevelSizeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (d : RowPt Pr N.R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N, SmallDatum (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) 1 := by
  first | exact @GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp | exact GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp | (intros; apply GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryFiniteDatumBoundedLevelSizeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  first | exact @GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp | exact GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp | (intros; apply GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp <;> assumption)
end

