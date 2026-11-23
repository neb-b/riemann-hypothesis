module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFinrankOfLocalizes
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (x : A.V), ∃ n : ℕ, ((l : ℕ) : O) ^ n • x ∈ LA.T := by
  intro l _ K LL _ _ _ O _ _ hG A LA x
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  haveI := IsModuleTopology.toContinuousSMul LL A.V
  have h1 : Filter.Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have h2 : Filter.Tendsto (fun n : ℕ => algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x) Filter.atTop (nhds 0) := by
    have := ((GlobalTheory.GoodCoeff.continuous_algebraMap_padic (l := l) (LL := LL)).tendsto 0).comp h1
    rw [map_zero] at this
    simpa using this.smul_const x
  have h3 : ∀ n : ℕ, ((l : ℕ) : O) ^ n • x = algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x := by
    intro n
    rw [← algebraMap_smul LL, map_pow, map_pow, map_natCast, map_natCast]
  obtain ⟨n, hn⟩ := (h2.eventually (hT.mem_nhds LA.T.zero_mem)).exists
  exact ⟨n, by rw [h3]; exact hn⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem not_isUnit_l : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ¬ IsUnit ((l : ℕ) : O) := by
  intro l _ LL _ _ _ O _ _ hG hu
  obtain ⟨u, hu⟩ := hu
  have hint := ((GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).1 (algebraMap O LL (↑u⁻¹ : O))).1 ⟨_, rfl⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hx : algebraMap O LL (↑u⁻¹ : O) = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by
    have h1 : algebraMap O LL (↑u⁻¹ : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : algebraMap O LL (u : O) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by
      rw [hu, map_natCast, map_natCast]
    rw [h2] at h1
    calc algebraMap O LL (↑u⁻¹ : O)
        = algebraMap O LL (↑u⁻¹ : O) * (algebraMap ℚ_[l] LL (l : ℚ_[l]) * algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹)) := by
          rw [← map_mul, mul_inv_cancel₀ hl0, map_one, mul_one]
      _ = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by rw [← mul_assoc, h1, one_mul]
  rw [hx] at hint
  obtain ⟨p, hpm, hp⟩ := hint
  have hp' : Polynomial.eval₂ (algebraMap ℤ_[l] ℚ_[l]) ((l : ℚ_[l])⁻¹) p = 0 := by
    apply (algebraMap ℚ_[l] LL).injective
    rw [map_zero, Polynomial.hom_eval₂]
    exact hp
  have hI : IsIntegral ℤ_[l] ((l : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have h1 : ‖(z : ℚ_[l])‖ ≤ 1 := PadicInt.norm_le_one z
  have h3 : algebraMap ℤ_[l] ℚ_[l] z = (z : ℚ_[l]) := rfl
  rw [← h3, hz, norm_inv, Padic.norm_p, inv_inv] at h1
  have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  linarith
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem finite_finrank_of_localizes : ∀ (O LL M N : Type) [CommRing O] [IsDomain O] [Field LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup M] [Module O M] [Module.Finite O M] [AddCommGroup N] [Module LL N] [Module O N] [IsScalarTower O LL N] (f : M →ₗ[O] N) (t : O), t ≠ 0 → (∀ y : N, ∃ n : ℕ, ∃ x : M, f x = t ^ n • y) → (∀ x : M, f x = 0 → ∃ n : ℕ, t ^ n • x = 0) → Module.Finite LL N ∧ finrank LL N = finrank O M := by
  intro O LL M N _ _ _ _ _ _ _ _ _ _ _ _ f t ht hs hk
  have htn : ∀ n : ℕ, t ^ n ∈ nonZeroDivisors O := fun n => pow_mem (mem_nonZeroDivisors_of_ne_zero ht) n
  haveI : IsLocalizedModule (nonZeroDivisors O) f :=
    { map_units := by
        intro s
        rw [Module.End.isUnit_iff]
        have ha : algebraMap O LL (s : O) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (nonZeroDivisors.ne_zero s.2)
        have he : ∀ y : N, (algebraMap O (Module.End O N) (s : O)) y = algebraMap O LL (s : O) • y := fun y => by
          rw [Module.algebraMap_end_apply, algebraMap_smul]
        refine ⟨fun y z h => ?_, fun y => ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩⟩
        · rw [he, he] at h
          exact smul_right_injective N ha h
        · rw [he, smul_smul, mul_inv_cancel₀ ha, one_smul]
      surj := by
        intro y
        obtain ⟨n, x, hx⟩ := hs y
        exact ⟨(x, ⟨t ^ n, htn n⟩), hx.symm⟩
      exists_of_eq := by
        intro x₁ x₂ h
        obtain ⟨n, hn⟩ := hk (x₁ - x₂) (by rw [map_sub, h, sub_self])
        exact ⟨⟨t ^ n, htn n⟩, by rw [Submonoid.smul_def]; rw [smul_sub, sub_eq_zero] at hn; exact hn⟩ }
  refine ⟨Module.Finite.of_isLocalizedModule (nonZeroDivisors O) (Rₚ := LL) f, ?_⟩
  rw [IsLocalization.finrank_eq LL (nonZeroDivisors O) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl]
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_B1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ latticeCocycles LA, c ∈ B1 A.ρ → ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCoboundaries LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c _ hc
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨n, hn⟩ := pow_smul_mem_lattice l K LL O hG A LA x
  exact ⟨n, _, hn, by rw [LinearMap.map_smul_of_tower]; rfl⟩

theorem pow_smul_mem_Z1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ continuousCocycles A.ρ, ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCocycles LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c hc
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  have hG' := hG
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG'
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  let U : ℕ → Set A.V := fun n => (fun v : A.V => ((l : ℕ) : O) ^ n • v) ⁻¹' (LA.T : Set A.V)
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    refine hT.preimage ?_
    have : (fun v : A.V => ((l : ℕ) : O) ^ n • v) = fun v : A.V => algebraMap O LL (((l : ℕ) : O) ^ n) • v :=
      funext fun v => (algebraMap_smul LL _ v).symm
    rw [this]
    exact continuous_const_smul _
  have hUm : Monotone U := by
    refine monotone_nat_of_le_succ fun n v hv => ?_
    show ((l : ℕ) : O) ^ (n + 1) • v ∈ LA.T
    rw [pow_succ', mul_smul]
    exact LA.T.smul_mem _ hv
  have hcov : Set.range c ⊆ ⋃ n, U n := fun v _ => Set.mem_iUnion.2 (pow_smul_mem_lattice l K LL O hG A LA v)
  obtain ⟨n, hn⟩ := (isCompact_range hc.1).elim_directed_cover U hUo hcov hUm.directed_le
  refine ⟨n, ⟨(continuousCocycles A.ρ).smul_of_tower_mem _ hc, fun g _ => hn ⟨g, rfl⟩⟩⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank
section
variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]
  {A : GRep ↥(GK K) ℚ_[l] LL O} (LA : Lattice (O := O) A.ρ)

def incl : ↥(latticeCocycles LA) →ₗ[O] ↥(continuousCocycles A.ρ) where
  toFun c := ⟨c, c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def toH1V : LatticeCohomology LA →ₗ[O] H1V A.ρ :=
  Submodule.liftQ ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype)
    ((((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ.restrictScalars O).comp (incl LA)) (by
      intro c hc
      obtain ⟨x, -, hx⟩ := hc
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨x, hx⟩)

theorem toH1V_mk (c : ↥(latticeCocycles LA)) :
    toH1V LA (Submodule.Quotient.mk c) = Submodule.Quotient.mk (incl LA c) := rfl
end
end GlobalTheory.H1Rank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpansLeContinuousCocycles
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CocN

open GlobalTheory.Cut.Coc

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [tw, hp, mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.CocN

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAndKernelOfLetterImageTensor
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedDim

theorem count {F M N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (g : M →ₗ[F] N) {r m s : ℕ} (v : Fin r → M) (V' : Submodule F M)
    (hle : V' ≤ Submodule.span F (Set.range v)) (hk : V' ≤ LinearMap.ker g) (hr : r ≤ m + s)
    (hm : m ≤ Module.finrank F ((Submodule.span F (Set.range v)).map g)) (hs : s ≤ Module.finrank F V') :
    Module.finrank F ((Submodule.span F (Set.range v)).map g) = m ∧
      Submodule.span F (Set.range v) ⊓ LinearMap.ker g = V' ∧ LinearIndependent F v := by
  set V := Submodule.span F (Set.range v) with hV
  haveI : FiniteDimensional F V := FiniteDimensional.span_of_finite F (Set.finite_range v)
  have h1 : Module.finrank F V ≤ r := (finrank_range_le_card (R := F) v).trans (Fintype.card_fin r).le
  have h2 := (g.domRestrict V).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h2
  haveI : FiniteDimensional F ↥(V ⊓ LinearMap.ker g) := Submodule.finiteDimensional_of_le inf_le_left
  have h3 : V' ≤ V ⊓ LinearMap.ker g := le_inf hle hk
  have h4 := Submodule.finrank_mono h3
  refine ⟨by omega, (Submodule.eq_of_le_of_finrank_le h3 (by omega)).symm, ?_⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin r) = Module.finrank F V
  rw [Fintype.card_fin]
  omega

section Abs

variable {F R EE : Type} [Field F] [CommRing R] [CommRing EE] (κ : F →+* R) (ρ : EE →+* R) (ε : R)

theorem mem_img (h1 : ∀ c, ∃ e, ε * κ c = ε * ρ e) {D N : Type} [AddCommGroup D] [Module EE D]
    [AddCommGroup N] [Module R N] [Module F N] (hκ : ∀ (c : F) (x : N), c • x = κ c • x)
    (J : D →+ N) (hJ : ∀ (e : EE) x, J (e • x) = ρ e • J x) {y : N}
    (hy : y ∈ Submodule.span F (Set.range fun x => ε • J x)) : ∃ x, y = ε • J x := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact ⟨x, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, rfl⟩ := hy; obtain ⟨x', rfl⟩ := hz
    exact ⟨x + x', by simp⟩
  | smul c y _ hy =>
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨e, he⟩ := h1 c
    exact ⟨e • x, by rw [hκ, hJ, smul_smul, smul_smul, mul_comm, he]⟩

theorem le_finrank {N : Type} [AddCommGroup N] [Module R N] [Module F N]
    (hκ : ∀ (c : F) (x : N), c • x = κ c • x) {D : Type} (w : D → N) (V : Submodule F N)
    [FiniteDimensional F V] (hw : ∀ x, w x ∈ V) {m : ℕ}
    (h : ∀ (t : ℕ) (u : Fin t → N), (∀ x, w x ∈ Submodule.span R (Set.range u)) → m ≤ t) :
    m ≤ Module.finrank F V := by
  let b := Module.finBasis F V
  refine h _ (fun j => (b j : N)) fun x => ?_
  have := congrArg Subtype.val (b.sum_repr ⟨w x, hw x⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at this
  rw [← this]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hκ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem abs_main (h1 : ∀ c, ∃ e, ε * κ c = ε * ρ e) (h2 : ∀ e, ∃ c, ε * ρ e = ε * κ c)
    {D D' M N : Type} [AddCommGroup D] [Module EE D] [AddCommGroup D'] [Module EE D']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : D →+ M) (hJ : ∀ (e : EE) x, J (e • x) = ρ e • J x) (φ : D' →ₗ[EE] D) (g : M →ₗ[R] N)
    {r m s : ℕ} (b : Module.Basis (Fin r) EE D) (hg : ∀ y, g (J (φ y)) = 0) (hr : r ≤ m + s)
    (hm : ∀ (t : ℕ) (u : Fin t → N), (∀ x, ε • g (J x) ∈ Submodule.span R (Set.range u)) → m ≤ t)
    (hs : ∀ (t : ℕ) (u : Fin t → M), (∀ y, ε • J (φ y) ∈ Submodule.span R (Set.range u)) → s ≤ t) :
    (∃ u : Fin m → D, ∀ x, ∃ c : Fin m → F, ε • g (J x) = ∑ j, κ (c j) • ε • g (J (u j))) ∧
      ∀ x, ε • g (J x) = 0 → ∃ y, ∀ j, ε * ρ (b.repr (x - φ y) j) = 0 := by
  letI : Module F M := Module.compHom M κ
  letI : Module F N := Module.compHom N κ
  have hM : ∀ (c : F) (x : M), c • x = κ c • x := fun _ _ => rfl
  have hN : ∀ (c : F) (x : N), c • x = κ c • x := fun _ _ => rfl
  let gF : M →ₗ[F] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun c x => g.map_smul (κ c) x }
  have hgF : ∀ x, gF x = g x := fun _ => rfl
  let v : Fin r → M := fun j => ε • J (b j)
  choose cc hcc using h2
  have hexp : ∀ x, ε • J x = ∑ j, cc (b.repr x j) • v j := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr x, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ, hM, smul_smul, hcc, smul_smul, mul_comm]
  have hmem : ∀ x, ε • J x ∈ Submodule.span F (Set.range v) := fun x => by
    rw [hexp]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hback : ∀ y ∈ Submodule.span F (Set.range v), ∃ x, y = ε • J x := fun y hy =>
    mem_img κ ρ ε h1 hM J hJ (Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨b j, rfl⟩) hy)
  let J' : D' →+ M := J.comp φ.toAddMonoidHom
  let V' := Submodule.span F (Set.range fun y => ε • J' y)
  have hle : V' ≤ Submodule.span F (Set.range v) :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hmem _)
  have hk : V' ≤ LinearMap.ker gF := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    change g (ε • J (φ y)) = 0
    rw [map_smul, hg, smul_zero])
  haveI : FiniteDimensional F (Submodule.span F (Set.range v)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range v)
  haveI : FiniteDimensional F V' := Submodule.finiteDimensional_of_le hle
  have hmem' : ∀ x, ε • g (J x) ∈ (Submodule.span F (Set.range v)).map gF := fun x =>
    ⟨_, hmem x, by rw [hgF, map_smul]⟩
  obtain ⟨e1, e2, e3⟩ := count gF v V' hle hk hr
    (le_finrank κ hN (fun x => ε • g (J x)) _ hmem' hm)
    (le_finrank κ hM (fun y => ε • J (φ y)) V' (fun y => Submodule.subset_span (Set.mem_range_self y)) hs)
  constructor
  · let c := Module.finBasisOfFinrankEq F _ e1
    have hu : ∀ j, ∃ x, (c j : N) = ε • g (J x) := fun j => by
      obtain ⟨y, hy, e⟩ := (c j).2
      obtain ⟨x, rfl⟩ := hback y hy
      exact ⟨x, by rw [← e, hgF, map_smul]⟩
    choose u hu using hu
    refine ⟨u, fun x => ⟨fun j => c.repr ⟨_, hmem' x⟩ j, ?_⟩⟩
    have := congrArg Subtype.val (c.sum_repr ⟨_, hmem' x⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hu, hN] at this
    exact this.symm
  · intro x hx
    have h3 : ε • J x ∈ V' := by
      rw [← e2]
      exact ⟨hmem x, by change g _ = 0; rw [map_smul, hx]⟩
    obtain ⟨y, hy⟩ := mem_img κ ρ ε h1 hM J' (fun e y => by
      change J (φ (e • y)) = _ • J (φ y); rw [map_smul, hJ]) h3
    refine ⟨y, fun j => ?_⟩
    have h4 : ε • J (x - φ y) = 0 := by rw [map_sub, smul_sub, hy]; exact sub_self _
    rw [hexp] at h4
    rw [hcc, Fintype.linearIndependent_iff.1 e3 _ h4 j, map_zero, mul_zero]

end Abs

section Comparison₂

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k]
    {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk)

theorem le_of_span (i : ZMod n) (h0 : eps E ρ i ≠ 0) (T : LocLat G Qp LL O) {m : ℕ}
    (q : ↥T.L.T →ₗ[O] (Fin m → k)) {s : ℕ} (b : Fin s → (Fin m → k)) (hb : LinearIndependent k b)
    (hq : ∀ j, ∃ x, q x = b j) (t : ℕ) (u : Fin t → Rk ⊗[k] (Fin m → k))
    (hu : ∀ x, eps E ρ i • J E ρ T q x ∈ Submodule.span Rk (Set.range u)) : s ≤ t := by
  refine card_le_of_span (eps_idem E ρ i) h0 u b hb fun j => ?_
  obtain ⟨x, hx⟩ := hq j
  have h1 : Submodule.span Rk (Set.range (J E ρ T q)) ≤
      (Submodule.span Rk (Set.range u)).comap (eps E ρ i • LinearMap.id) :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hu y)
  have h2 := h1 (J_span E ρ T q x)
  rw [hx] at h2
  simpa [TensorProduct.smul_tmul'] using h2

end Comparison₂

theorem dim_ker : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk), IsRed E ρ (k := k) lam κ → ∀ (T : LocLat G Qp LL O) (m : ℕ) (q : ↥T.L.T →ₗ[O] (Fin m → k)), Function.Surjective q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i, (∃ u : Fin m → W.DD T, ∀ x, ∃ c : Fin m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) ∧ ∀ h : LatHom T.L T'.L, (∀ x, f.f (h.f x) = algebraMap O LL lam • x) → ∀ x, eps E ρ i • J E ρ T q x = 0 → ∃ y, W.map f y = (letE i : LetA O n) • x := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W RA RW _ _ _ _
    inclR φR gR πA E k _ _ Rk _ _ _ _ ρ lam κ hR T m q hq T' f hf i
  classical
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI := (W.DD_free T).1
  haveI := GlobalTheory.EtaleExact.finite_DD E T
  haveI : Nontrivial W.EE := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply hR.eps_ne i
    rw [eps, Subsingleton.elim (algebraMap (LetA O n) W.EE (letE i)) 0, map_zero]
  set r := Module.finrank O ↥T.L.T with hr
  let t : Module.Basis (Fin r) O ↥T.L.T := Module.finBasis O _
  let b : Module.Basis (Fin r) W.EE (W.DD T) := Module.finBasisOfFinrankEq _ _ (W.DD_free T).2
  let qb : ↥T.L.T →ₗ[O] (Fin r → k) := t.constr O fun j => Pi.single j 1
  let g : (Fin r → k) →ₗ[k] (Fin m → k) := (Pi.basisFun k (Fin r)).constr k fun j => q (t j)
  have hgq : ∀ x, q x = g (qb x) := by
    have : q = (g.restrictScalars O) ∘ₗ qb := t.ext fun j => by
      have := (Pi.basisFun k (Fin r)).constr_basis k (fun j => q (t j)) j
      rw [Pi.basisFun_apply] at this
      simp only [LinearMap.comp_apply, qb, Module.Basis.constr_basis, LinearMap.restrictScalars_apply]
      exact this.symm
    intro x
    conv_lhs => rw [this]
    rfl
  have hqb : Function.Surjective qb := by
    intro y
    choose c hc using fun j => hR.res_surj (y j)
    refine ⟨∑ j, c j • t j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext a
    simp [qb, Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
  have hg : Function.Surjective g := fun y => by
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨_, (hgq x).symm⟩
  have hrk := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hg] at hrk
  simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
  let q' : ↥T'.L.T →ₗ[O] (Fin r → k) := qb ∘ₗ GlobalTheory.EtaleExact.latMap f
  have hJ' : ∀ y, J E ρ T qb (W.map f y) = J E ρ T' q' y := fun y => by
    rw [J_map E ρ f q' qb LinearMap.id (fun x x' e => congrArg qb (Subtype.ext e)), LinearMap.baseChange_id]
    rfl
  have hJ : ∀ x, g.baseChange Rk (J E ρ T qb x) = J E ρ T q x := fun x => (J_comp E ρ T qb q g hgq x).symm
  let cK := Module.finBasis k (LinearMap.ker g)
  obtain ⟨h1, h2⟩ := abs_main κ (rE E ρ) (eps E ρ i) (hR.κ_of i) (hR.of_κ i) (J E ρ T qb) (J_smul E ρ T qb)
    (W.map f) (g.baseChange Rk) (m := m) b (fun y => by
      rw [hJ, J_map E ρ f q' q 0 (fun x x' e => (hf x').2 ⟨x, x.2, e.symm⟩)]
      simp) hrk.ge
    (fun s u hu => le_of_span E ρ i (hR.eps_ne i) T q (Pi.basisFun k (Fin m))
      (Pi.basisFun k (Fin m)).linearIndependent (fun j => hq _) s u (fun x => hJ x ▸ hu x))
    (fun s u hu => le_of_span E ρ i (hR.eps_ne i) T' q' (fun j => (cK j : Fin r → k))
      (cK.linearIndependent.map' (LinearMap.ker g).subtype (Submodule.ker_subtype _)) (fun j => by
        obtain ⟨x, hx⟩ := hqb (cK j)
        obtain ⟨y, hy, e⟩ := (hf x).1 (by rw [hgq, hx]; exact (cK j).2)
        exact ⟨⟨y, hy⟩, hx ▸ congrArg qb (Subtype.ext e)⟩) s u (fun y => hJ' y ▸ hu y))
  simp only [hJ] at h1 h2
  refine ⟨h1, fun h hh x hx => ?_⟩
  obtain ⟨y, hy⟩ := h2 x hx
  choose e he using fun j => hR.ker i _ (hy j)
  have h3 : ∀ z, W.map f (W.map h z) = algebraMap O W.EE lam • z := fun z => by
    have : latComp f h = latSmul T lam := by
      have : f.f.comp h.f = algebraMap O LL lam • LinearMap.id := LinearMap.ext hh
      unfold latComp latSmul
      congr 1
    rw [← W.map_comp, this, W.map_latSmul, algebraMap_smul]
  have h4 : algebraMap (LetA O n) W.EE (letE i) • (x - W.map f y) =
      algebraMap O W.EE lam • ∑ j, e j • b j := by
    conv_lhs => rw [← b.sum_repr (x - W.map f y)]
    simp only [Finset.smul_sum, smul_smul, he]
  refine ⟨W.map h (∑ j, e j • b j) + algebraMap (LetA O n) W.EE (letE i) • y, ?_⟩
  rw [map_add (f := _), h3, ← h4, map_smul, ← smul_add, sub_add_cancel, algebraMap_smul]

end GlobalTheory.RedDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTiltStatement
section
theorem _root_.GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt : Formalism.MainNotions.ElementDenominator.ArtinSchreierWittOnto := fun l _ x =>
  PI.ArtSch.main_of witt_lift (tiltSurjectiveOfParts rootModP_holds tilt_divisibility smallSurjective) l x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExtStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.LocalIntegers.goodO_integers | exact GlobalTheory.LocalIntegers.goodO_integers | (intros; apply GlobalTheory.LocalIntegers.goodO_integers <;> assumption)
end

