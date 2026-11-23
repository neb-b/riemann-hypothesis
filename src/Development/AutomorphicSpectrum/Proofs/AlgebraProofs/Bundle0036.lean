module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0031
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0029
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHomomorphismCompatible

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeSpanIntersectionBasis
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_dual_integral_of_saturated_free_part :
    ∀ (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C]
      [IsFractionRing V C] (W : Type) [AddCommGroup W] [Module C W] [Module V W]
      [IsScalarTower V C W] [FiniteDimensional C W] (Lie : Submodule V W) (n : ℕ) (w : Fin n → W),
      Lie.FG → Submodule.span C (Lie : Set W) = ⊤ → LinearIndependent C w →
      (∀ y, y ∈ Submodule.span V (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w)) →
      ∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧
        ∀ k, φ (w k) = if k = j then 1 else 0 := by
  intro V C _ _ _ _ _ _ W _ _ _ _ _ Lie n w hfg _ hw hsat j
  classical
  let W' : Submodule C W := Submodule.span C (Set.range w)
  obtain ⟨p, q, u, t, -, hu, ht, -, -, hspan⟩ :=
    exists_basis_split_of_exact_of_fg_valuationRing V C W' W (W ⧸ W') W'.subtype W'.mkQ
      W'.injective_subtype (LinearMap.exact_subtype_mkQ W') Lie hfg
  have hwW : ∀ i, w i ∈ W' := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hli : LinearIndependent C (Sum.elim w t) := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    rw [Fintype.sum_sum_type] at hf
    simp only [Sum.elim_inl, Sum.elim_inr] at hf
    have h1 : ∀ i, f (Sum.inr i) = 0 := by
      have h := congrArg W'.mkQ hf
      have hz : ∀ i, W'.mkQ (w i) = 0 := fun i => by
        simpa using hwW i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, zero_add,
        map_zero] at h
      exact Fintype.linearIndependent_iff.mp ht _ h
    have h2 : ∀ i, f (Sum.inl i) = 0 := by
      simp only [h1, zero_smul, Finset.sum_const_zero, add_zero] at hf
      exact Fintype.linearIndependent_iff.mp hw _ hf
    rintro (i | i)
    · exact h2 i
    · exact h1 i
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination C (Sum.elim w t)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hli)
  have hgs : ∀ a, g (Sum.elim w t a) = Finsupp.single a 1 := fun a => by
    have h1 := LinearMap.congr_fun hg (Finsupp.single a 1)
    simpa [Finsupp.linearCombination_single] using h1
  let φ : Module.Dual C W := Finsupp.lapply (Sum.inl j) ∘ₗ g
  have hφw : ∀ k, φ (w k) = if k = j then 1 else 0 := fun k => by
    have h := hgs (Sum.inl k)
    simp only [Sum.elim_inl] at h
    simp [φ, h, Finsupp.single_apply]
  have hφt : ∀ i, φ (t i) = 0 := fun i => by
    have h := hgs (Sum.inr i)
    simp only [Sum.elim_inr] at h
    simp [φ, h, Finsupp.single_apply]
  let R : Submodule V C := LinearMap.range (Algebra.linearMap V C)
  have hone : (1 : C) ∈ R := ⟨1, by simp⟩
  have hzero : (0 : C) ∈ R := R.zero_mem
  have hspw : Submodule.span V (Set.range w) ≤ R.comap (φ.restrictScalars V) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change φ (w k) ∈ R
    rw [hφw]
    split_ifs
    · exact hone
    · exact hzero
  have hle : Lie ≤ R.comap (φ.restrictScalars V) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · apply hspw
      have hmem : u i ∈ Lie.comap (W'.subtype.restrictScalars V) := by
        rw [← hu]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact (hsat _).mpr ⟨hmem, (u i).2⟩
    · change φ (t i) ∈ R
      rw [hφt]
      exact hzero
  refine ⟨φ, fun y hy => ?_, hφw⟩
  obtain ⟨a, ha⟩ := hle hy
  exact ⟨a, by simpa using ha⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LieSubDegreeBoundByDual
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.FrobEst

def dotOrth {K : Type} [Field K] {d : ℕ} (X : Submodule K (Fin d → K)) :
    Submodule K (Fin d → K) where
  carrier := {u | ∀ φ ∈ X, u ⬝ᵥ φ = 0}
  add_mem' := fun {a b} ha hb φ hφ => by rw [add_dotProduct, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' := fun φ _ => zero_dotProduct φ
  smul_mem' := fun c u hu φ hφ => by rw [smul_dotProduct, hu φ hφ, smul_zero]

theorem frob_estimate : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (O : Type) [CommRing O] [StarRing O] (d : ℕ) (D : ConjData C p O d), 2 < p →
    0 ≤ deg C (dotDual C D.lie) ∧
      ∀ W : Submodule K (Fin d → K),
        ((p : ℤ) - 2) * subDeg C D.lie W ≤ deg C (dotDual C D.lie) := by
  intro K _ C p _ _ O _ _ d D hp
  obtain ⟨h0, W₀, hW₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax.subDeg_max K C (Fin d → K) D.lie D.lie_bun
  have hp2 : (0 : ℤ) < (p : ℤ) - 2 := by
    have : (2 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    linarith
  have hf := GlobalTheory.CompanionTheory.Ar.Crv.SubFrob.subDeg_frob K C p d D.lie W₀ D.lie_bun
  have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective K C (Fin d → K) ((Fin d → K) × (Fin d → K))
    (frobLat C p D.lie) D.H D.α (frobSub p W₀)
    (GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat K C p d D.lie D.lie_bun).1 D.H_bun D.conj.1
    (fun i x hx => (D.conj.2.2.2.1 i x).1 hx)
  have h2 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes.subDeg_ses K C (Fin d → K) ((Fin d → K) × (Fin d → K)) (Fin d → K)
    (dotDual C D.lie) D.H D.lie (LinearMap.inr K (Fin d → K) (Fin d → K))
    (LinearMap.fst K (Fin d → K) (Fin d → K)) (Submodule.map D.α (frobSub p W₀)) D.H_bun D.hodge
  have h3 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth K C d D.lie
    (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))))
    (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))) D.lie_bun (fun u => Iff.rfl)
  have h4 := hW₀ (Submodule.map (LinearMap.fst K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀)))
  have h5 := hW₀ (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀))))
  have hr : ((p : ℤ) - 2) * subDeg C D.lie W₀ = (p : ℤ) * subDeg C D.lie W₀ - 2 * subDeg C D.lie W₀ := by
    ring
  have key : ((p : ℤ) - 2) * subDeg C D.lie W₀ ≤ deg C (dotDual C D.lie) := by
    linarith
  have hμ : 0 ≤ subDeg C D.lie W₀ := by
    have := hW₀ ⊥
    linarith
  refine ⟨?_, fun W => ?_⟩
  · have := mul_nonneg hp2.le hμ
    linarith
  · have := mul_le_mul_of_nonneg_left (hW₀ W) hp2.le
    linarith

end GlobalTheory.CompanionTheory.Ar.Crv.FrobEst
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalComparisonOfOrbitsHoldsStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_of_orbits_holds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Sg : Type) [Fintype Sg] [DecidableEq Sg] (P : Ideal (MRing ι O)) (d p : ℕ), 2 ≤ p → ∀ (φ : Equiv.Perm Sg) (r s : Sg → ℕ) (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, ∃ (Sg' : Type) (_ : Finite Sg') (e : Sg' → Sg) (φ' : Equiv.Perm Sg'), τ ∈ Set.range e ∧ (∀ t, e (φ' t) = φ (e t)) ∧ Relations (r := fun t => r (e t)) (s := fun t => s (e t)) P d p φ' (fun t => lie (e t)) (fun t => om (e t))) → LabelChernComparison P d p φ lie om := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits | exact GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedLatticeTowerExists
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem free_on_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u → ∃ (ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)) (T : Submodule O (C ⊗[ℤ] La)) (e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C), (∀ (a : 𝓞 E) (x : La), ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧ T = Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x) ∧ IsFreeOn ρ T (fun i => 1 ⊗ₜ u i) ∧ (∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧ (∀ x, e x x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0) ∧ dualLat e T = T ∧ ∀ (a : 𝓞 E) x y, e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y) :=
  @PositivityTheory.HtPt.Gi.free_on_lift

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOnePowTwoCommutationStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_one_pow_two_commutation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowTwoSymplecticRelationStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_two_symplectic_relation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupRestriction
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem subquoHopfOrder : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable (F := F) AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable (F := F) AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) :=
  by
    intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ N _ _ _ _ AA hAA K _ _ _ _
    have hres : FStable (F := F)
        (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) := by
      rintro a _ ⟨g, hg, rfl⟩
      exact ⟨_, hAA a g hg, rfl⟩
    have hquo : FStable (F := F)
        (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) := by
      intro a g hg
      have h := hAA a _ hg
      show LinearMap.funLeft R C (K.mkQ : N → N ⧸ K) _ ∈ AA.carrier
      convert h using 1
      funext x
      show g (K.mkQ (a • x)) = g (a • K.mkQ x)
      rw [map_smul]
    have hrange : K.subtype.toAddMonoidHom.range = K.mkQ.toAddMonoidHom.ker := by
      ext x
      simp [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨AK, hAK⟩ := PositivityTheory.HtPt.Rc.exists_res hv AA
        K.subtype.toAddMonoidHom Subtype.val_injective
      exact ⟨AK, hAK, hAK ▸ hres⟩
    · obtain ⟨AQ, hAQ⟩ := PositivityTheory.HtPt.Rc.exists_quo hv AA
        K.mkQ.toAddMonoidHom K.mkQ_surjective
      exact ⟨AQ, hAQ, hAQ ▸ hquo⟩
    · exact PositivityTheory.HtPt.Rc.invFun_eq _ K.mkQ.toAddMonoidHom
        K.mkQ_surjective _ (fun x => by simp)
    · intro c cQ cK hc hQ hK
      exact PositivityTheory.HtPt.Rc.colen_ses hv AA K.subtype.toAddMonoidHom
        Subtype.val_injective K.mkQ.toAddMonoidHom K.mkQ_surjective hrange c cQ cK hc hQ hK

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEigenProjectionsEqSelf
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig

theorem sum_embeddings_eq_trace (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* C, s x = algebraMap ℚ C (Algebra.trace ℚ E x) := by
  classical
  let Ω := AlgebraicClosure C
  let f : (E →+* C) → (E →ₐ[ℚ] Ω) := fun s => RingHom.toRatAlgHom ((algebraMap C Ω).comp s)
  have hf : ∀ s y, f s y = algebraMap C Ω (s y) := fun s y => rfl
  have hinj : Function.Injective f := by
    intro s t hst
    ext y
    have h := congrArg (fun φ : E →ₐ[ℚ] Ω => φ y) hst
    simp only [hf] at h
    exact (algebraMap C Ω).injective h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hc, AlgHom.card]⟩
  have key : algebraMap ℚ Ω (Algebra.trace ℚ E x) = ∑ σ : E →ₐ[ℚ] Ω, σ x :=
    trace_eq_sum_embeddings Ω (x := x)
  rw [← hbij.sum_comp (fun σ : E →ₐ[ℚ] Ω => σ x)] at key
  simp only [hf] at key
  apply (algebraMap C Ω).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← key, eq_ratCast (algebraMap ℚ Ω), eq_ratCast (algebraMap ℚ C), map_ratCast]

theorem sum_eigProj (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M) :
    ∑ s, HT.eigProj ρ s y = y := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    calc (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      _ = algebraMap (𝓞 E) E (∑ j, b.repr 1 j • b j) := by rw [b.sum_repr]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have htr : ∀ k, Algebra.trace ℚ E (HT.dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k
    calc Algebra.trace ℚ E (HT.dualInt E k) = Algebra.traceForm ℚ E (HT.dualInt E k) 1 := by
          rw [Algebra.traceForm_apply, mul_one]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) * Algebra.traceForm ℚ E (HT.dualInt E k) (integralBasis E j) := by
          conv_lhs => rw [h1]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = ((b.repr 1 k : ℤ) : ℚ) := by
          simp only [HT.dualInt, LinearMap.BilinForm.apply_dualBasis_left, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsum : ∀ k, ∑ s : E →+* C, s (HT.dualInt E k) = ((b.repr 1 k : ℤ) : C) := by
    intro k
    rw [sum_embeddings_eq_trace E C hc, htr, map_intCast]
  calc ∑ s, HT.eigProj ρ s y = ∑ s : E →+* C, ∑ k, s (HT.dualInt E k) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [HT.eigProj]
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hb]
    _ = ∑ k, (∑ s : E →+* C, s (HT.dualInt E k)) • ρ (b k) y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, ((b.repr 1 k : ℤ) : C) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsum]
    _ = ρ (∑ k, b.repr 1 k • b k) y := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
    _ = y := by
        rw [b.sum_repr, map_one, Module.End.one_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFiniteFlatSubgroupStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_finite_flat_subgroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ K : AddSubgroup N, IsFinFlatSub G (T.A ⧸ vanIdeal T pt K) (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup | exact GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHomomorphismCompatibleStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_homomorphism_compatible : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∀ K : AddSubgroup N, (∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G), z ≫ j = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S, spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z) → ∀ jN : N →+ N', (∀ x, pt' (jN x) = pt x ≫ j) → jN.ker = K ∧ ∀ g ∈ torsFun C T pt, (∀ k ∈ jN.ker, g k = 0) → g ∈ (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible | exact GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrderStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order | exact GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order <;> assumption)
end

