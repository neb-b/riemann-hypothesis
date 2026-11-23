module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFDOfCuspFiniteClaim
section
noncomputable section

namespace GlobalTheory.CuspFormsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma zero_mem_SS_unitary_existence {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    (0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) ∈ X.SS la :=
  ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero X la, fun ξ _ x _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero X la ξ x 0⟩

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma add_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) (hQ : Q ∈ X.SS la) : P + Q ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add X hP.1 hQ.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add X hP.1 hQ.1 hξ hx 0, hP.2 ξ hξ x hx, hQ.2 ξ hξ x hx, add_zero]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma smul_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (a : ℂ) {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : a • P ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul X a hP.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul X la P ξ x 0 a, hP.2 ξ hξ x hx, mul_zero]


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CuspFormsCompare.mem_holSub_iff_forall_SS {r : ℕ} {Comp : Type}
    (X : Comp → _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ∀ k, _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r)
    (P : _root_.Formalism.L2.PjFree.FDSec X) : P ∈ _root_.Formalism.L2.PjFree.holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  constructor
  · intro hP
    unfold _root_.Formalism.L2.PjFree.holSub at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ => exact hQ
    | zero => exact fun k => zero_mem_SS_unitary_existence (X k) (la k)
    | add Q R _ _ hQ hR => exact fun k => add_mem_SS (X k) (la k) (hQ k) (hR k)
    | smul a Q _ hQ => exact fun k => smul_mem_SS (X k) (la k) a (hQ k)
  · intro hP
    exact _root_.Formalism.L2.PjFree.holCusp_mem_holSub X la hP

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end GlobalTheory.CuspFormsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DatumCommensurablePeriod
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.TwoLattices

open Module

theorem natAbs_det_gram {M κ : Type} [AddCommGroup M] [Fintype κ] [DecidableEq κ] (b : Basis κ ℤ M)
    (B : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) :
    (Matrix.of fun i k => B (b i) (b k)).det.natAbs = 1 := by
  have h := LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have e : LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective B hB : M →ₗ[ℤ] _) =
      (Matrix.of fun i k => B (b i) (b k))ᵀ := by
    ext i k
    simp [LinearMap.toMatrix_apply]
  rw [e, Matrix.det_transpose] at h
  exact Int.isUnit_iff_natAbs_eq.mp h

theorem index_similitude {M M' : Type} [AddCommGroup M] [AddCommGroup M'] [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ M'] [Module.Finite ℤ M'] (B : LinearMap.BilinForm ℤ M) (B' : LinearMap.BilinForm ℤ M')
    (hB : Function.Bijective B) (hB' : Function.Bijective B') (j : M →+ M') (hj : Function.Injective j)
    (n N : ℕ) (hn : finrank ℤ M = n) (hn' : finrank ℤ M' = n)
    (h : ∀ a b, B' (j a) (j b) = (N : ℤ) ^ 2 * B a b) : j.range.index = N ^ n := by
  let b : Basis (Fin n) ℤ M := Module.finBasisOfFinrankEq ℤ M hn
  let b' : Basis (Fin n) ℤ M' := Module.finBasisOfFinrankEq ℤ M' hn'
  let bN : Basis (Fin n) ℤ j.range := b.map (AddMonoidHom.ofInjective hj).toIntLinearEquiv
  have hbN : ∀ i, (bN i : M') = j (b i) := fun i => rfl
  rw [AddSubgroup.index_eq_natAbs_det b' j.range bN, Basis.det_apply]
  set J := b'.toMatrix (fun i => (bN i : M')) with hJ
  have key : Jᵀ * (Matrix.of fun i k => B' (b' i) (b' k)) * J =
      ((N : ℤ) ^ 2) • Matrix.of fun i k => B (b i) (b k) := by
    ext i k
    have e1 : ∀ i, j (b i) = ∑ l, J l i • b' l := fun i => by
      rw [← hbN]
      exact (b'.sum_repr _).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← h, e1, Matrix.mul_apply,
      Matrix.transpose_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have k2 := congrArg (fun X => X.det.natAbs) key
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Int.natAbs_mul, natAbs_det_gram b B hB,
    natAbs_det_gram b' B' hB', _root_.mul_one, Int.natAbs_pow, Int.natAbs_natCast, Fintype.card_fin] at k2
  have : J.det.natAbs ^ 2 = (N ^ n) ^ 2 := by
    rw [sq, k2]; ring
  exact Nat.pow_left_injective (by norm_num) this

variable {E : Type} [Field E] [NumberField E]

theorem exists_mul_mem {M' V : Type} [AddCommGroup M'] [Module (𝓞 E) M'] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (φ' : M' →ₗ[𝓞 E] V)
    (hs : Submodule.span E (Set.range φ') = ⊤) (v : V) : ∃ N : ℕ, 0 < N ∧ ∃ b, φ' b = N • v := by
  have hv : v ∈ Submodule.span E (Set.range φ') := hs ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact ⟨1, one_pos, b, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, b, hb⟩ := hx
    obtain ⟨K, hK, c, hc⟩ := hy
    refine ⟨N * K, Nat.mul_pos hN hK, K • b + N • c, ?_⟩
    rw [map_add (f := _), map_nsmul, map_nsmul, hb, hc, smul_add, smul_smul, smul_smul, mul_comm K N]
  | smul e x _ hx =>
    obtain ⟨N, hN, b, hb⟩ := hx
    have halg : IsAlgebraic ℤ e :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic e)
    obtain ⟨m, s, hm, hs⟩ := halg.exists_nsmul_eq (S := 𝓞 E)
    refine ⟨m * N, Nat.mul_pos (Nat.pos_of_ne_zero hm) hN, s • b, ?_⟩
    rw [map_smul, hb, ← IsScalarTower.algebraMap_smul E s, ← hs, smul_assoc, smul_comm e N x, mul_smul]

theorem exists_mul_le {M M' V : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [AddCommGroup M'] [Module (𝓞 E) M'] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (φ : M →ₗ[𝓞 E] V) (φ' : M' →ₗ[𝓞 E] V)
    (hs : Submodule.span E (Set.range φ') = ⊤) : ∃ N : ℕ, 0 < N ∧ ∀ a, ∃ b, φ' b = N • φ a := by
  obtain ⟨s, hS⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M)
  choose n hn c hc using exists_mul_mem φ' hs
  refine ⟨∏ x ∈ s, n (φ x), Finset.prod_pos fun x _ => hn _, fun a => ?_⟩
  have ha : a ∈ Submodule.span (𝓞 E) (s : Set M) := hS ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ x)) (Finset.mem_coe.mp hx)
    exact ⟨k • c (φ x), by rw [map_nsmul, hc, smul_smul, hk, mul_comm]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨b + d, by rw [map_add (f := _), map_add (f := _), hb, hd, smul_add]⟩
  | smul e x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨e • b, by rw [map_smul, map_smul, hb, smul_comm]⟩

theorem exists_lift {R M M' V : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup V] [Module R V] (φ : M →ₗ[R] V) (φ' : M' →ₗ[R] V)
    (hi : Function.Injective φ') (N : ℕ) (h : ∀ a, ∃ b, φ' b = N • φ a) :
    ∃ j : M →ₗ[R] M', ∀ a, φ' (j a) = N • φ a := by
  choose f hf using h
  refine ⟨⟨⟨f, fun x y => hi ?_⟩, fun c x => hi ?_⟩, hf⟩
  · rw [map_add (f := _), hf, hf, hf, map_add (f := _), smul_add]
  · simp only [RingHom.id_apply]
    rw [map_smul, hf, hf, map_smul, smul_comm]

theorem rank_of_lattice {M : Type} [AddCommGroup M] {g : ℕ} (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    finrank ℤ M = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  have h := ZLattice.rank ℝ L
  have e : M ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  rw [e.finrank_eq, h, Module.finrank_pi_fintype]
  simp [mul_comm]

variable [IsCMField E]

theorem herm_nsmul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (N : ℕ) (x y : Fin r → E) :
    FD.herm G (N • x) (N • y) = (N : E) ^ 2 * FD.herm G x y := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_lift {H : Host E} (D D' : Datum H) {r : ℕ} (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E))
    (h : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (h' : ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y)))
    (N : ℕ) (j : D.La → D'.La) (hj : ∀ a, φ' (j a) = N • φ a) (a b : D.La) :
    D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b := by
  apply Int.cast_injective (α := ℚ)
  rw [h', hj, hj, herm_nsmul]
  push_cast
  rw [h, ← smul_eq_mul ((N : ℚ) ^ 2), ← map_smul]
  congr 1
  rw [Algebra.smul_def]
  simp only [map_pow, map_natCast]
  ring

theorem hermForm_real_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm ((t : ℂ) • z) ((t : ℂ) • w) = ((t ^ 2 : ℝ) : ℂ) * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

end GlobalTheory.TwoLattices


open GlobalTheory.TwoLattices in
theorem GlobalTheory.datum_commensurable_period :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (g : ℕ) (ty : Fin g → (E →+* ℂ)), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y))) → ∀ P, IsPeriod D ty P → ∃ (N : ℕ) (j : D.La →ₗ[𝓞 E] D'.La) (j' : D'.La →ₗ[𝓞 E] D.La) (P' : D'.La →+ (Fin g → ℂ)), (0 < N ∧ (∀ a, j' (j a) = (N ^ 2) • a) ∧ (∀ a, j (j' a) = (N ^ 2) • a) ∧ (∀ a b, D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b) ∧ (∀ a b, D.EF (j' a) (j' b) = (N : ℤ) ^ 2 * D'.EF a b) ∧ Nat.card (D'.La ⧸ LinearMap.range j) = N ^ (2 * g)) ∧ IsPeriod D' ty P' ∧ (∀ a, P' (j a) = (N : ℂ) • P a) ∧ ∀ a, P (j' a) = (N : ℂ) • P' a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' g ty _ ⟨hi, hs, _, _, hE⟩ ⟨hi', hs', _, _, hE'⟩ P ⟨hPl, hPi, hPd, hPs, Hm, hH, hpos, hIm⟩
  haveI := D.fin
  haveI := D'.fin
  obtain ⟨N₁, hN₁, h₁⟩ := exists_mul_le φ φ' hs'
  obtain ⟨N₂, hN₂, h₂⟩ := exists_mul_le φ' φ hs
  set N := N₁ * N₂ with hNdef
  have hN : 0 < N := Nat.mul_pos hN₁ hN₂
  obtain ⟨j, hj⟩ := exists_lift φ φ' hi' N fun a => by
    obtain ⟨b, hb⟩ := h₁ a
    exact ⟨N₂ • b, by rw [map_nsmul, hb, smul_smul, mul_comm]⟩
  obtain ⟨j', hj'⟩ := exists_lift φ' φ hi N fun a => by
    obtain ⟨b, hb⟩ := h₂ a
    exact ⟨N₁ • b, by rw [map_nsmul, hb, smul_smul]⟩
  clear_value N
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have c₁ : ∀ a, j' (j a) = (N ^ 2) • a := fun a => hi (by rw [hj', hj, map_nsmul, smul_smul, sq])
  have c₂ : ∀ a, j (j' a) = (N ^ 2) • a := fun a => hi' (by rw [hj, hj', map_nsmul, smul_smul, sq])
  have f₁ := form_lift D D' ξ Gm φ φ' hE hE' N j hj
  have f₂ := form_lift D' D ξ Gm φ' φ hE' hE N j' hj'
  have cancel : ∀ v w : Fin r → E, N • v = N • w → v = w := fun v w h => by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at h
    exact smul_right_injective _ hNE h
  have ji : Function.Injective j := fun a b h => hi (cancel _ _ (by rw [← hj, ← hj, h]))
  have ji' : Function.Injective j' := fun a b h => hi' (cancel _ _ (by rw [← hj', ← hj', h]))
  let P' : D'.La →+ (Fin g → ℂ) :=
    { toFun := fun a => (N : ℂ)⁻¹ • P (j' a)
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add (f := _), smul_add] }
  have hP' : ∀ a, P' a = (N : ℂ)⁻¹ • P (j' a) := fun _ => rfl
  have p₂ : ∀ a, P (j' a) = (N : ℂ) • P' a := fun a => by
    rw [hP', smul_smul, mul_inv_cancel₀ hNC, one_smul]
  have p₁ : ∀ a, P' (j a) = (N : ℂ) • P a := fun a => by
    rw [hP', c₁, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast
    field_simp
  have P'i : Function.Injective P' := fun a b h => ji' (hPi (by rw [p₂, p₂, h]))
  have P'd : DiscreteTopology P'.range := by
    let f : P'.range → P.range := fun x => ⟨(N : ℂ) • (x : Fin g → ℂ), by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨j' a, by rw [p₂, ha]⟩⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.const_smul (N : ℂ)) _
    · intro x y h
      exact Subtype.ext (smul_right_injective _ hNC (congrArg Subtype.val h))
  have P's : Submodule.span ℝ (Set.range P') = ⊤ := by
    rw [eq_top_iff, ← hPs, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have : P a = (N : ℝ)⁻¹ • P' (j a) := by
      rw [p₁]
      ext i
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      push_cast
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, P'i, P'd, P's, Hm, hH, hpos, fun x y => ?_⟩
    · simp only [hP', map_smul, Pi.smul_apply, hPl, smul_eq_mul]
      ring
    · have e : ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hP', hP', e, hermForm_real_smul, Complex.im_ofReal_mul, hIm, f₂]
      push_cast
      field_simp
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) _
  haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) _
  haveI : Module.IsTorsionFree ℤ D.La := hPi.moduleIsTorsionFree P (fun c x => map_zsmul P c x)
  haveI : Module.IsTorsionFree ℤ D'.La := P'i.moduleIsTorsionFree P' (fun c x => map_zsmul P' c x)
  refine ⟨N, j, j', P', ⟨hN, c₁, c₂, f₁, f₂, ?_⟩, hper, p₁, p₂⟩
  exact index_similitude D.EF D'.EF D.unimod D'.unimod j.toAddMonoidHom ji (2 * g) N
    (rank_of_lattice P hPi hPd hPs) (rank_of_lattice P' P'i P'd P's) f₁
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionOtherModelSameValues
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FibreSection

variable {X X' Y : Scheme.{0}}

theorem chart_le (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ h ⁻¹ᵁ (L.pull F).U (fun _ => j 0) := fun y hy =>
  mem_pull.2 ((congrArg (fun q => q y ∈ L.U (j 0)) e).mpr (LB.wchart_le L _ j 0 hy))

theorem le_chart (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : L.ι) :
    h ⁻¹ᵁ (L.pull F).U (fun _ => j) ≤ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => j) := fun y hy =>
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ L.U j) e).mp (mem_pull.1 hy)

def pullAlong (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (s : LB.Sec (L.pull F)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) where
  f := fun (j : Fin 1 → L.ι) => (h.appLE _ _ (chart_le L h e j)).hom (s.f (fun _ => j 0))
  compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
    have h₁ : h y ∈ (L.pull F).U (fun _ => j 0) := chart_le L h e j hy.1
    have h₂ : h y ∈ (L.pull F).U (fun _ => j' 0) := chart_le L h e j' hy.2
    have g : gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g j j') =
        gm (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) :=
      (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 Y ≫ h) ≫ F = 𝟙 Y ≫ φ := by rw [Category.assoc, e]
    exact (gs_res _ y _ hy _).trans ((gs_appLE h _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 Y ≫ h) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (g.trans ((congrArg (fun q => gm q y (L.U (j 0) ⊓ L.U (j' 0))
          (L.g (j 0) (j' 0))) eφ).symm.trans (gm_pull_g L F (𝟙 Y ≫ h) y _ _ h₁ h₂).symm))))
        ((gs_res _ y _ hy _).trans (gs_appLE h _ _ _ (𝟙 _) y hy.2 _)))))))

theorem valAt'_appLE (pt : Sp ℂ ⟶ Y) (h : Y ⟶ X') (U : X'.Opens) (W : Y.Opens) (le : W ≤ h ⁻¹ᵁ U)
    (ge : h ⁻¹ᵁ U ≤ W) (f : Γ(X', U)) :
    valAt' pt W ((h.appLE U W le).hom f) = valAt' (pt ≫ h) U f := by
  unfold valAt'
  by_cases hp : ⊤ ≤ pt ⁻¹ᵁ W
  · have hp' : ⊤ ≤ (pt ≫ h) ⁻¹ᵁ U := fun z hz => le (hp hz)
    rw [dite_eq_left hp, dite_eq_left hp']
    unfold valAt
    congr 1
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  · have hp' : ¬ ⊤ ≤ (pt ≫ h) ⁻¹ᵁ U := fun k => hp fun z hz => ge (k hz)
    rw [dite_eq_right hp, dite_eq_right hp']

theorem exists_sec_same_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec), ∃ s' : LB.Sec (PPx y), ∀ j (pt : Sp ℂ ⟶ Gx y) (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y), x ≫ pullback.fst _ _ = pt ≫ gxFst y → x ≫ pullback.snd _ _ = 𝟙 _ → pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U (fun _ => j)) (s'.f (fun _ => j)) = valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) := by
  intro E _ _ _ H Dw l Xo y s
  have cond : gxFst y ≫ Xo.univ.t.G.hom = gxSnd y ≫ y :=
    (Over.w (CartesianMonoidalCategory.snd (Over.mk y) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk y) Xo.univ.t.G)).symm
  let h : Gx y ⟶ pullback Xo.univ.t.G.hom y := pullback.lift _ _ cond
  have hφ : h ≫ pullback.fst _ _ = gxFst y := pullback.lift_fst _ _ cond
  have hh : h ≫ pullback.snd _ _ = gxSnd y := pullback.lift_snd _ _ cond
  refine ⟨pullAlong Xo.univ.t.PP.L h hφ s, fun j pt x e₁ e₂ e₃ => ?_⟩
  have hx : x = pt ≫ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ, e₁]
    · rw [Category.assoc, hh, e₂, e₃]
  subst hx
  exact valAt'_appLE pt h _ _ (chart_le Xo.univ.t.PP.L h hφ (fun _ => j)) (le_chart Xo.univ.t.PP.L h hφ j) _

end GlobalTheory.FibreSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermEqOfNormalised
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.RiemannForm

theorem eq_of_im {g : ℕ} (h τ Hm A B : Matrix (Fin g) (Fin g) ℂ) (hA : h * A = 1) (hB : h * B = τ)
    (h1 : ∀ a b, ((Aᵀ * Hm * A.map (starRingEnd ℂ)) a b).im = 0)
    (h2 : ∀ a b, ((Aᵀ * Hm * B.map (starRingEnd ℂ)) a b).im = -(1 : Matrix (Fin g) (Fin g) ℝ) a b) :
    Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧
      Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  have hA' : A * h = 1 := mul_eq_one_comm.mp hA
  have hB' : B = A * τ := by rw [← hB, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  set M := Aᵀ * Hm * A.map (starRingEnd ℂ) with hM
  have hMB : Aᵀ * Hm * B.map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ) := by
    rw [hB', Matrix.map_mul, hM]; simp only [Matrix.mul_assoc]
  have hMY : M.map Complex.re * τ.map Complex.im = 1 := by
    ext a b
    have := h2 a b
    rw [hMB, Matrix.mul_apply, Complex.im_sum] at this
    rw [Matrix.mul_apply, ← neg_inj, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [h1 a c]
  have hinv : (τ.map Complex.im)⁻¹ = M.map Complex.re := Matrix.inv_eq_left_inv hMY
  have hMre : (M.map Complex.re).map (fun x : ℝ => (x : ℂ)) = M := by
    ext a b
    apply Complex.ext <;> simp [h1 a b]
  have hH : Hm = hᵀ * M * h.map (starRingEnd ℂ) := by
    have e1 : hᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hA', Matrix.transpose_one]
    have e2 : A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hA']; simp
    calc Hm = (hᵀ * Aᵀ) * Hm * (A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ)) := by
          rw [e1, e2]; simp
      _ = _ := by rw [hM]; simp only [Matrix.mul_assoc]
  refine ⟨by rw [hinv, hMre]; exact hH, ?_⟩
  have hd : M.det * (((τ.map Complex.im).det : ℝ) : ℂ) = 1 := by
    have e := congrArg Matrix.det hMY
    rw [Matrix.det_mul, Matrix.det_one] at e
    have e' : M.det = (((M.map Complex.re).det : ℝ) : ℂ) := by
      conv_lhs => rw [← hMre]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [e']; exact_mod_cast e
  have hc : (h.map (starRingEnd ℂ)).det = starRingEnd ℂ h.det :=
    (RingHom.map_det (starRingEnd ℂ) h).symm
  rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  have := Complex.mul_conj' h.det
  push_cast
  linear_combination (h.det * starRingEnd ℂ h.det) * hd + this

theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → Fin g → ℂ) (a b : Fin g) :
    ((Matrix.of u)ᵀᵀ * Hm * ((Matrix.of v)ᵀ).map (starRingEnd ℂ)) a b = hermForm Hm (u a) (v b) := by
  rw [Matrix.mul_assoc]
  rfl

theorem herm_eq_of_normalised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (P : D.La →+ (Fin g → ℂ)) (h τ Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) → IsPeriod D ty P → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → τ ∈ SiegelH (Fin g) → (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) → Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧ Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  intro E _ _ _ H D g ty bas P h τ Hm hE _ hn _ hH
  refine eq_of_im h τ Hm (Matrix.of fun k => P (bas (Pi.single (Sum.inl k) 1)))ᵀ
    (Matrix.of fun k => P (bas (Pi.single (Sum.inr k) 1)))ᵀ ?_ ?_ ?_ ?_
  · ext i k
    have := congrFun (hn k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  · ext i k
    have := congrFun (hn k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd]
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all [eq_comm]

end GlobalTheory.RiemannForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiCoord_exists_unique_up_to_unit_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (Dg : DegData R (maximalIdeal R)), IsIntegrallyClosed R → ∀ χ, (∃ r, PsiCoord Dg.toPre χ r ∧ r ≠ 0 ∧ (χ ≠ 0 → r ∈ maximalIdeal R) ∧ (χ = 0 → IsUnit r)) ∧ (∀ r r', PsiCoord Dg.toPre χ r → PsiCoord Dg.toPre χ r' → ∃ u : Rˣ, r' = u * r) ∧ ∀ (W : Set (Sp R)) (𝔭 : PrimeSpectrum R), IsOpen W → 𝔭 ∈ W → PsiUnitOn Dg.toPre χ W → ∀ r, PsiCoord Dg.toPre χ r → r ∉ 𝔭.asIdeal := by
  first | exact @GlobalTheory.PsiCoordLocal.main | exact GlobalTheory.PsiCoordLocal.main | (intros; apply GlobalTheory.PsiCoordLocal.main <;> assumption)
end

