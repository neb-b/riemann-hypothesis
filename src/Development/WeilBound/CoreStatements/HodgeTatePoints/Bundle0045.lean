module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFlat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0044
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbProj
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RcFlag

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopf
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.HopfOrderTop

private theorem btOrder_top_isHopfOrder' (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective)
    (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R' : Type) [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    [HenselianLocalRing R'] (T : Type) [CommGroup T] [Finite T] (Γ' : QFGroup R' T) :
    IsHopfOrder (Γ'.btOrder ⊤) := by
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  have hU : Γ'.IsFinOpenSub (GlobalTheory.finitePart Γ'.G.hom) := by
    apply QFGroup.isFinOpenSub_of_closedFibre
    · exact GlobalTheory.isFinite_finitePart (R := CommRingCat.of R') Γ'.G.hom
    · intro x hx
      exact GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R') _ x hx
  rw [← PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular R' T Γ' _ hU]
  exact PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub R' T Γ' _ hU

private theorem exists_smul_mem_of_extOrder {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {T : Type} [CommGroup T] [Finite T] (A : Subalgebra R (T → R))
    (hA : ∀ g : T → K, g ∈ extOrder (algebraMap R K) A) :
    ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A := by
  classical
  have key : ∀ x ∈ extOrder (algebraMap R K) A, ∃ s : R, s ≠ 0 ∧ ∃ a ∈ A,
      algebraMap R K s • x = fun t => algebraMap R K (a t) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨1, one_ne_zero, a, ha, by simp⟩
    | algebraMap k =>
      obtain ⟨⟨n, ⟨s, hs⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
      refine ⟨s, nonZeroDivisors.ne_zero hs, algebraMap R (T → R) n, Subalgebra.algebraMap_mem A n, ?_⟩
      funext t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [mul_comm]
      exact hk
    | add x y _ _ hx hy =>
      obtain ⟨s1, hs1, a1, ha1, e1⟩ := hx
      obtain ⟨s2, hs2, a2, ha2, e2⟩ := hy
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, s2 • a1 + s1 • a2, A.add_mem (A.smul_mem ha1 _) (A.smul_mem ha2 _), ?_⟩
      funext t
      have h1 := congrFun e1 t
      have h2 := congrFun e2 t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, map_mul, map_add (f := _)] at h1 h2 ⊢
      linear_combination (algebraMap R K s2) * h1 + (algebraMap R K s1) * h2
    | mul x y _ _ hx hy =>
      obtain ⟨s1, hs1, a1, ha1, e1⟩ := hx
      obtain ⟨s2, hs2, a2, ha2, e2⟩ := hy
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, a1 * a2, A.mul_mem ha1 ha2, ?_⟩
      funext t
      have h1 := congrFun e1 t
      have h2 := congrFun e2 t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul] at h1 h2 ⊢
      linear_combination (algebraMap R K s2 * y t) * h1 + (algebraMap R K (a1 t)) * h2
  choose s hs a ha e using fun t : T =>
    key _ (hA (fun u => algebraMap R K ((Pi.single t (1 : R) : T → R) u)))
  haveI := Fintype.ofFinite T
  have hδ : ∀ t, s t • (Pi.single t (1 : R) : T → R) = a t := by
    intro t
    funext u
    apply IsFractionRing.injective R K
    have := congrFun (e t) u
    simpa [Algebra.smul_def] using this
  refine ⟨∏ t, s t, Finset.prod_ne_zero_iff.mpr fun t _ => hs t, fun f => ?_⟩
  have hmem : (∏ t, s t) • f = ∑ t, (f t * ∏ t' ∈ Finset.univ.erase t, s t') • a t := by
    funext u
    simp only [← hδ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_prod_erase _ s (Finset.mem_univ u)]
    ring
  rw [hmem]
  exact A.sum_mem fun t _ => A.smul_mem (ha t) _

theorem btOrder_top_isHopfOrder (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) : IsHopfOrder (Γ.btOrder ⊤) := by
  classical
  refine PositivityTheory.HtPt.Htat.HopfOrderFlatLocal.isHopfOrder_of_flat_local R T _ ?_ ?_
  · obtain ⟨ΓK, F, hbc⟩ := hBaseChange R T Γ (FractionRing R) (algebraMap R (FractionRing R))
      (IsFractionRing.injective R _)
    have hK := btOrder_top_isHopfOrder' hHenselian hBaseChange hRegular (FractionRing R) T ΓK
    rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange R T Γ _ ΓK F hbc inferInstance] at hK
    obtain ⟨d', hd', hd'm⟩ := hK.full
    refine exists_smul_mem_of_extOrder (K := FractionRing R) _ fun g => ?_
    have := hd'm (d'⁻¹ • g)
    rwa [smul_smul, mul_inv_cancel₀ hd', one_smul] at this
  · intro P hP
    haveI := hP.isPrime
    obtain ⟨R', iR, iD, iH, iA, hic, hfl, hcomap⟩ := hHenselian R P
    have hinj : Function.Injective (algebraMap R R') := PositivityTheory.HtPt.Htat.ValuationInjectivePi.flat_inj
    obtain ⟨Γ', F, hbc⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
    refine ⟨R', iR, iD, inferInstance, iA, hfl, hcomap, ?_⟩
    rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange R T Γ R' Γ' F hbc hfl]
    exact btOrder_top_isHopfOrder' hHenselian hBaseChange hRegular R' T Γ'

end PositivityTheory.HtPt.Htat.HopfOrderTop

theorem PositivityTheory.HtPt.Htat.bt_hopf_of (hHenselian : type_of% @_root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime) (hBaseChange : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  @PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder hHenselian hBaseChange hRegular
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RdNonunitFin
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem a_nonunit_rom_of (hom : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_product) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) :=
  a_nonunit_of @PositivityTheory.HtPt.Rb.proj_props @PositivityTheory.HtPt.Rc.step hom

end PositivityTheory.HtPt.Rd
end

