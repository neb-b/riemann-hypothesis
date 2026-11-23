module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProduct
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.PadCommensurable

def sat {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] (f : V →+ V') (B : AddSubgroup V') : AddSubgroup V where
  carrier := {y | ∃ n : ℕ, 0 < n ∧ n • f y ∈ B}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨k, hk, hy⟩
    refine ⟨n * k, Nat.mul_pos hn hk, ?_⟩
    rw [map_add (f := _), smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.nsmul_mem hx _
    · rw [mul_smul]; exact B.nsmul_mem hy _
  neg_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [map_neg, smul_neg]; exact B.neg_mem hx⟩

theorem uniform_of_fg {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] (f : V →+ V') (A : AddSubgroup V)
    (B : AddSubgroup V') (hA : A.FG) (h : A ≤ sat f B) : ∃ R : ℕ, 0 < R ∧ ∀ y ∈ A, R • f y ∈ B := by
  obtain ⟨S, hS⟩ := hA
  have h' : ∀ y : S, ∃ n : ℕ, 0 < n ∧ n • f y.1.1 ∈ B :=
    fun y => h y.1.2
  choose n hn hy using h'
  refine ⟨∏ y, n y, Finset.prod_pos fun y _ => hn y, fun y hy' => ?_⟩
  have hall : ∀ x : A, x ∈ AddSubsemigroup.closure (S : Set A) →
      (∏ y, n y) • f x.1 ∈ B := by
    intro x hx
    induction hx using AddSubsemigroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ : n ⟨x, hx⟩ ∣ ∏ y, n y := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
      rw [hc, mul_comm, mul_smul]
      exact B.nsmul_mem (hy ⟨x, hx⟩) _
    | add x y _ _ hx hy =>
      change (∏ y, n y) • f (x.1 + y.1) ∈ B
      rw [map_add, smul_add]
      exact B.add_mem hx hy
  apply hall ⟨y, hy'⟩
  rw [hS]
  trivial

theorem exists_nat_mul_int {K : Type*} [Field K] [NumberField K] (κ : K) :
    ∃ (n : ℕ) (a : 𝓞 K), 0 < n ∧ (a : K) = n * κ := by
  have halg : IsAlgebraic ℤ κ := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic κ)
  obtain ⟨d, hd, hi⟩ := halg.exists_integral_multiple
  rcases Int.natAbs_eq d with h | h
  · refine ⟨d.natAbs, ⟨d • κ, hi⟩, Int.natAbs_pos.2 hd, ?_⟩
    change d • κ = _
    rw [zsmul_eq_mul]
    conv_lhs => rw [h]
    rw [Int.cast_natCast]
  · refine ⟨d.natAbs, -⟨d • κ, hi⟩, Int.natAbs_pos.2 hd, ?_⟩
    change -(d • κ) = _
    rw [zsmul_eq_mul]
    conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast]
    ring

theorem exists_nsmul_mem (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (w : ℂ) (hw : w ∈ lamOf D cc δ)
    (A : Matrix (Fin N') (Fin N) D.host.E) :
    w • embV D (tor0 D cc δ) A ∈ sat (AddMonoidHom.id _) (LaB D (tor0 D cc δ) b) := by
  obtain ⟨-, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  have e : w • embV D (tor0 D cc δ) (∑ i, κ i • b i) =
      ∑ i, (D.host.φ₀ (κ i : D.host.E) * w) • embV D (tor0 D cc δ) (b i) := by
    funext τ s t
    have h1 : ∀ i, (κ i • b i) s t = (κ i : D.host.E) * b i s t := fun i => rfl
    have h2 := hD.1 τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [embV, tor0, Pi.smul_apply, Finset.sum_apply, Matrix.sum_apply, h1, map_sum, map_mul, h2,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨n, a, hn, ha⟩ := exists_nat_mul_int (κ i)
  refine ⟨n, hn, AddSubgroup.subset_closure ⟨_, hst a w hw, i, ?_⟩⟩
  rw [AddMonoidHom.id_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ha]
  congr 1
  push_cast
  rw [map_mul, map_natCast]
  ring

theorem nsmul_pad_mem : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b → (La D (tor0 D cc δ) L L').FG → ∃ R : ℕ, 0 < R ∧ ∀ y ∈ La D (tor0 D cc δ) L L', R • pad D m y ∈ LaB D (tor0 D cc δ) b := by
  intro D hD cc δ hc N N' m r L L' b hb hfg
  refine uniform_of_fg (padL D m).toAddMonoidHom _ _ hfg ?_
  rw [La, AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, -, rfl⟩
  obtain ⟨n, hn, h⟩ := exists_nsmul_mem D hD cc δ hc b hb w hw (padM D m A)
  refine ⟨n, hn, ?_⟩
  change n • pad D m _ ∈ _
  rw [pad_smul, pad_embV D _ (fun τ => map_zero (embT D τ))]
  exact h

end GlobalTheory.PadCommensurable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalEigenbasis
section
open Module.End

namespace GlobalTheory.OrthonormalEigenbasis

theorem exists_eigenbasis_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (a : E →ₗ[ℂ] E) (ha : ∀ x y, inner ℂ (a x) (a y) = inner ℂ x y) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (l : Fin (Module.finrank ℂ E) → ℂ),
      ∀ i, a (b i) = l i • b i := by
  set a' := LinearMap.adjoint a with ha'

  have h1 : a' * a = 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    rw [Module.End.mul_apply, ha', LinearMap.adjoint_inner_left, ha, Module.End.one_apply]
  have h2 : a * a' = 1 := mul_eq_one_comm.mp h1

  set A : E →ₗ[ℂ] E := a + a' with hAdef
  set B : E →ₗ[ℂ] E := Complex.I • (a' - a) with hBdef
  have hA : A.IsSymmetric := by
    intro x y
    simp only [hAdef, LinearMap.add_apply, inner_add_left, inner_add_right, ha',
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
    ring
  have hB : B.IsSymmetric := by
    intro x y
    simp only [hBdef, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
      inner_sub_left, inner_sub_right, ha', LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right,
      Complex.conj_I]
    ring
  have hAB : Commute A B := by
    have hc : Commute (a + a') (a' - a) := by
      show (a + a') * (a' - a) = (a' - a) * (a + a')
      simp only [add_mul, mul_add, sub_mul, mul_sub, h1, h2]
      abel
    exact hc.smul_right Complex.I
  have hV := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  have hV' := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB

  have hT : Set.Finite {i : ℂ × ℂ | eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := by
    refine ((Module.End.finite_hasEigenvalue (f := B)).prod
      (Module.End.finite_hasEigenvalue (f := A))).subset fun i hi => ⟨?_, ?_⟩
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_right)
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_left)
  have : Finite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := hT.to_subtype
  have := Fintype.ofFinite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥}
  classical
  have hW := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hW' := hV'.comp (Subtype.val_injective (p := fun i : ℂ × ℂ => eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥))

  refine ⟨hW.subordinateOrthonormalBasis rfl hW', fun i =>
    ((hW.subordinateOrthonormalBasisIndex rfl i hW').1.2 +
      Complex.I * (hW.subordinateOrthonormalBasisIndex rfl i hW').1.1) / 2, fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate rfl i hW'
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hmem
  have hsum : ∀ v, A v + Complex.I • B v = (2 : ℂ) • a v := by
    intro v
    simp only [hAdef, hBdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_smul,
      Complex.I_mul_I, neg_one_smul, smul_sub, two_smul]
    abel
  calc a (hW.subordinateOrthonormalBasis rfl hW' i)
      = (2 : ℂ)⁻¹ • (A (hW.subordinateOrthonormalBasis rfl hW' i) +
          Complex.I • B (hW.subordinateOrthonormalBasis rfl hW' i)) := by
        rw [hsum, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = _ := by
        rw [hmem.1, hmem.2, smul_smul, ← add_smul, smul_smul]
        congr 1
        ring


open GlobalTheory.UnitaryTheta in
theorem exists_orthonormal_eigenbasis {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then (1 : ℂ) else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by

  let cd : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => H y x
      conj_inner_symm := fun x y => (hH.1 y x).symm
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hH.2 x hx).le
      add_left := fun x y z => by
        show H z (x + y) = H z x + H z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show H y (r • x) = (starRingEnd ℂ) r * H y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul]
      definite := fun x hx => by
        by_contra h
        have := hH.2 x h
        simp [hx] at this }
  let _ : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  have hinner : ∀ x y : V, inner ℂ x y = H y x := fun _ _ => rfl
  obtain ⟨b, l, hb⟩ := exists_eigenbasis_of_isometry a (fun x y => by rw [hinner, hinner]; exact ha y x)
  refine ⟨Module.finrank ℂ V, b.toBasis, l, fun i j => ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [OrthonormalBasis.coe_toBasis, ← hinner, orthonormal_iff_ite.mp b.orthonormal j i]
    exact if_congr eq_comm rfl rfl
  ·
    have h1 : ‖a (b i)‖ = ‖b i‖ := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner, hinner, ha]
    rw [hb i, norm_smul, b.orthonormal.1 i, mul_one] at h1
    exact h1
  · rw [OrthonormalBasis.coe_toBasis]
    exact hb i

end GlobalTheory.OrthonormalEigenbasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.MovedTheta

open Matrix GlobalTheory.NormSum.AdLattice

variable {D : D7} {N N' : ℕ}

def mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) (AE D) :=
  ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
    (g : Matrix (Fin N) (Fin N) (AE D))

theorem mv_zero (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) : mv g g' 0 = 0 := by
  unfold mv
  rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]

theorem mv_add (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z + w) = mv g g' z + mv g g' w := by
  unfold mv
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem mv_smul (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (e : D.host.E)
    (z : Matrix (Fin N') (Fin N) D.host.E) : mv g g' (e • z) = inc D e • mv g g' z := by
  unfold mv
  have : (e • z).map (inc D) = inc D e • z.map (inc D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem inc_int (o : 𝓞 D.host.E) : inc D (o : D.host.E) ∈ OhE D :=
  Formalism.UG.P.adelstab_incl_int (F := ℚ) o

theorem mulVec_mem_of_span {R m n : Type} [CommRing R] [Fintype n] {S : Subring R} (M : Matrix m n R) (i : m)
    {T : Set (n → R)} (hT : ∀ u ∈ T, (M *ᵥ u) i ∈ S) {u : n → R} (hu : u ∈ Submodule.span S T) :
    (M *ᵥ u) i ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hT u hu
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mulVec_add]; exact add_mem hu hv
  | smul s u _ hu =>
    have e : s • u = (s : R) • u := rfl
    rw [e, mulVec_smul]
    exact mul_mem s.2 hu

theorem mv_int_of_maps {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  let Λ := Formalism.UG.stdLat (n := Fin N) (A := D.host.E) (𝓞 D.host.E)
  have hstd (v : Fin N → AE D) :
      v ∈ Formalism.UG.latS (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) (OhE D) Λ ↔
        ∀ i, v i ∈ OhE D := by
    dsimp [Λ, OhE]
    rw [Formalism.UG.P.easyc_latS_std]
    exact Formalism.UG.P.adelstab_mem_stdLat (F := ℚ) (E := D.host.E) v
  have hL : L = Formalism.UG.CS.globLat g Λ := by
    ext x
    exact (h x).trans (hstd _).symm
  have h1 := (Formalism.UG.P.span_recovery_of_integral_adelic_approx
    Formalism.UG.P.csGlob_intAdApprox ℚ D.host.E (Fin N) Λ
    (Formalism.UG.P.standard_lattice_full_holds D.host.E (Fin N)).1
    (Formalism.UG.P.standard_lattice_full_holds D.host.E (Fin N)).2
    g ((g : Matrix (Fin N) (Fin N) (AE D)) *ᵥ Pi.single j 1)).2 (hstd _ |>.2 (by
    intro k
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _))
  have h3 := mulVec_mem_of_span
    (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * A.map (inc D)) i (by
      rintro _ ⟨x, hx, rfl⟩
      have h2 := (h' _).1 (hA x (hL ▸ hx)) i
      have e : (fun j => inc D ((A *ᵥ x) j)) = A.map (inc D) *ᵥ (fun j => inc D (x j)) := by
        ext k; rw [RingHom.map_mulVec]; rfl
      rw [e, mulVec_mulVec] at h2
      exact h2) h1
  rw [mulVec_mulVec, mulVec_single_one] at h3
  exact h3

theorem mv_int_of_hom {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact mv_int_of_maps h h' hA i j
  | zero => rw [mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, mv_smul]
    exact mul_mem (inc_int o) hu

theorem mul_mem_IhE {cc : Ideal (𝓞 D.host.K)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ IhE D cc) :
    s * y ∈ IhE D cc := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | neg u _ hu => rw [mul_neg]; exact neg_mem hu

theorem mv_mem_IhE {cc : Ideal (𝓞 D.host.K)} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {B : Matrix (Fin N') (Fin N) D.host.E} (hB : B ∈ YYl D L L') (i : Fin N') (j : Fin N) :
    mv g g' (((c : D.host.K) : D.host.E) • B) i j ∈ IhE D cc := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    rw [smul_smul, mv_smul]
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, _, mv_int_of_hom h h' hA i j, rfl⟩
  | zero => rw [smul_zero, mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add, mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, smul_comm, mv_smul]
    exact mul_mem_IhE (inc_int o) hu

theorem pt_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt, embV, tor0, mul_add]

theorem pt_neg (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt, embV, tor0]

theorem mv_neg (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (-z) = -mv g g' z := by
  rw [← neg_one_smul D.host.E z, mv_smul, map_neg, map_one, neg_one_smul]

end GlobalTheory.NormSum.MovedTheta


open GlobalTheory.NormSum.MovedTheta in
theorem GlobalTheory.NormSum.exists_pt_of_mem_La_moved : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  intro D hG cc δ _ N N' g g' L L' h h' x hx
  let P : VC D N N' → Prop := fun x => ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧
    ∀ i j, mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z i j ∈ IhE D cc
  have h0 : P 0 := ⟨0, (pt_zero cc δ).symm, fun i j => by rw [mv_zero]; exact zero_mem _⟩
  have hadd : ∀ u v, P u → P v → P (u + v) := by
    rintro _ _ ⟨z, rfl, hz⟩ ⟨w, rfl, hw⟩
    exact ⟨z + w, (pt_add cc δ z w).symm, fun i j => by rw [mv_add]; exact add_mem (hz i j) (hw i j)⟩
  have hneg : ∀ u, P u → P (-u) := by
    rintro _ ⟨z, rfl, hz⟩
    exact ⟨-z, (pt_neg cc δ z).symm, fun i j => by rw [mv_neg]; exact neg_mem (hz i j)⟩
  show P x
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      refine ⟨((c : D.host.K) : D.host.E) • A, ?_, mv_mem_IhE h h' hc hA⟩
      funext τ i j
      have e := hG.1 τ (c : D.host.K)
      simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [e, mul_assoc]
    | zero => rw [zero_smul]; exact h0
    | add u v _ _ hu hv => rw [add_smul]; exact hadd _ _ hu hv
    | neg u _ hu => rw [neg_smul]; exact hneg _ hu
  | zero => exact h0
  | add u v _ _ hu hv => exact hadd _ _ hu hv
  | neg u _ hu => exact hneg _ hu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubmodule
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GKSubmodule

noncomputable def resAct {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) : Mat p q →ₗ[ℂ] Module.End ℂ N where
  toFun Z := (M.act Z).restrict (h Z)
  map_add' X Y := by
    ext x
    simp [LinearMap.restrict_apply]
  map_smul' c X := by
    ext x
    simp [LinearMap.restrict_apply]

theorem resAct_coe {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) (Z : Mat p q) (x : N) :
    ((resAct M N h Z x : N) : M.V) = M.act Z x := rfl

theorem exists_submodule : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  intro p q M N h
  have hlie : IsLieAct (resAct M N h) := by
    intro X Y
    ext x
    have := congrArg (fun f : Module.End ℂ M.V => f x) (M.lie X Y)
    simpa [resAct_coe] using this
  have hk : ∀ v : N, ∃ W : Submodule ℂ N, FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (resAct M N h) W := by
    intro v
    obtain ⟨W, hW, hv, hs⟩ := M.kfin v
    refine ⟨W.comap N.subtype, ?_, hv, ?_⟩
    · exact Module.Finite.of_injective
        (N.subtype.restrict (p := W.comap N.subtype) (q := W) (fun x hx => hx))
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : W => (z : M.V)) hab)))
    · intro X hX w hw
      exact hs X hX w hw
  have hw : ∀ v : N, v ∈ ⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ := by
    intro v
    have h1 := _root_.GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q M.V M.act N (fun a => h _) v v.2 (M.wts v)
    have h2 : (⨆ μ : Ix p q → ℚ, N ⊓ wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ).map N.subtype := by
      refine iSup_le fun μ x hx => ?_
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      refine Submodule.mem_iSup_of_mem μ ?_
      have hx2 := hx.2
      simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
      intro a
      apply Subtype.ext
      simpa [resAct_coe] using hx2 a
    obtain ⟨y, hy, hyv⟩ := h2 h1
    have : y = v := Subtype.ext hyv
    exact this ▸ hy
  exact ⟨{ V := N, act := resAct M N h, lie := hlie, kfin := hk, wts := hw }, N.subtype,
    N.injective_subtype, N.range_subtype, fun _ _ => rfl⟩

end GlobalTheory.GKSubmodule
end

