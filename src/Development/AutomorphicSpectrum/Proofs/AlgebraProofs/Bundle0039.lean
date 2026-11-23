module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0015
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RcFlag
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.JoinVerticalDivisorStatement
section
namespace GlobalTheory.CompanionTheory.Heights

theorem join_vertical_divisor_statement : GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.Statement :=
  PositivityTheory.Xgn.t_s_joinvertdiv

end GlobalTheory.CompanionTheory.Heights
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisIdeals
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem flag_colen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N :=
  @PositivityTheory.HtPt.Rc.flag_colen

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupRestrictionStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_restriction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable F AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable F AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder | exact GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.subquoHopfOrder <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslation
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem step_hopf_line : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → (∃ S : HopfOrder (C := C) R F, S.carrier = stepOrder AA.carrier K t ∧ FStable (F := F) S.carrier) ∧ stepOrder AA.carrier K t = stepOrderRes AA.carrier K t := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hf N _ _ _ _ AA hst K t ht
  classical
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  have hne : K.mkQ t ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using ht
  have heq := PositivityTheory.HtPt.Rc.stepOrder_eq AA.carrier K.mkQ hsurj t
  rw [K.ker_mkQ] at heq
  obtain ⟨AQ, hAQ⟩ := PositivityTheory.HtPt.Rc.exists_quo hv AA K.mkQ.toAddMonoidHom hsurj
  obtain ⟨S, hS⟩ := PositivityTheory.HtPt.Rc.exists_res hv AQ
    (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t)).toAddMonoidHom (PositivityTheory.HtPt.Rc.span_inj hne)
  refine ⟨⟨S, ?_, ?_⟩, ?_⟩
  · rw [hS, hAQ, heq]
    rfl
  · rw [hS, hAQ]
    intro a h hh
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
    refine Submodule.mem_map.mpr ⟨fun x => g (a • x), ?_, ?_⟩
    · have hg' : (fun x => g (K.mkQ x)) ∈ AA.carrier := hg
      change (fun x => g (a • K.mkQ x)) ∈ AA.carrier
      simpa only [map_smul] using hst a _ hg'
    · funext x
      change g (a • LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t) x) =
        g (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t) (a • x))
      rw [map_smul]
  · unfold stepOrder stepOrderRes
    ext h
    constructor
    · intro hh
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
      exact ⟨g, hg.1, fun a k hk => hg.2 _ _ hk⟩
    · rintro ⟨g, hg, hgh⟩
      obtain ⟨g', hg', hg'e⟩ := PositivityTheory.HtPt.Rc.invres p C v R hv hp N AA K.toAddSubgroup
        (Submodule.span F {t} ⊔ K).toAddSubgroup
        (by
          intro x hx
          exact Submodule.mem_sup_right hx) g hg
        (by
          intro x hx k hk
          obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
          rw [add_assoc, hgh a _ (K.add_mem hz hk), hgh a z hz])
      refine Submodule.mem_map.mpr ⟨g', hg', ?_⟩
      funext a
      show g' (a • t) = h a
      rw [hg'e (a • t) (Submodule.mem_sup_left (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩))]
      simpa using hgh a 0 K.zero_mem

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEigenProjectionsEqSelfStatement
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_eigen_projections_eq_self : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [Fintype (E →+* C)], Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M), ∑ s, HT.eigProj ρ s y = y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj <;> assumption)
end

