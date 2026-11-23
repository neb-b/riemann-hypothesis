module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0020
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharMemClosurePrimitiveRootCard
section
open Formalism.L2.DIV

namespace GlobalTheory

theorem absIrrChar_mem_closure_primitiveRoot {G : Type} [Group G] [Fintype G] {K : Type} [Field K]
    [CharZero K] (z : K) (hz : IsPrimitiveRoot z (Fintype.card G)) (χ : G → K) (hχ : IsAbsIrrChar χ)
    (g : G) : χ g ∈ Subring.closure ({z} : Set K) := by
  obtain ⟨n, ρ, -, hch⟩ := hχ
  set N := Fintype.card G with hN
  haveI : NeZero N := ⟨Fintype.card_ne_zero⟩
  set f := ρ g with hf
  have hfN : f ^ N = 1 := by rw [hf, ← map_pow, pow_card_eq_one, map_one]
  have htr : LinearMap.trace (AlgebraicClosure K) _ f = (LinearMap.charpoly f).roots.sum := by
    rw [LinearMap.trace_eq_matrix_trace (AlgebraicClosure K) (Pi.basisFun (AlgebraicClosure K) (Fin n)),
      Matrix.trace_eq_sum_roots_charpoly, LinearMap.charpoly_toMatrix]
  have hz' : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) z) N :=
    hz.map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hroot : ∀ μ ∈ (LinearMap.charpoly f).roots,
      ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k) := by
    intro μ hμ
    have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := hv.pow_apply N
    rw [hfN] at h1
    have hμN : μ ^ N = 1 := by
      have h2 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h1, one_smul]; simp
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv.2
    obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hμN
    exact ⟨k, by rw [map_pow, hk]⟩
  have hsum : ∀ m : Multiset (AlgebraicClosure K),
      (∀ μ ∈ m, ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k)) →
      ∃ y ∈ Subring.closure ({z} : Set K), algebraMap K (AlgebraicClosure K) y = m.sum := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; exact ⟨0, zero_mem _, by simp⟩
    | cons a m ih =>
      intro h
      obtain ⟨y, hy, hy'⟩ := ih (fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ))
      obtain ⟨k, hk⟩ := h a (Multiset.mem_cons_self a m)
      refine ⟨z ^ k + y, add_mem (pow_mem (Subring.subset_closure (Set.mem_singleton z)) k) hy, ?_⟩
      rw [Multiset.sum_cons, map_add (f := _), hy', hk]
  obtain ⟨y, hy, hy'⟩ := hsum _ hroot
  have hχg : algebraMap K (AlgebraicClosure K) (χ g) = algebraMap K (AlgebraicClosure K) y := by
    rw [← hch g, hy', ← htr]; rfl
  rw [(algebraMap K (AlgebraicClosure K)).injective hχg]
  exact hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCard
section
open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.BrauerRealise

variable {G : Type} [Group G] [Fintype G]


omit [Fintype G] in
theorem isIrreducible_of_sum_char_mul_char_inv [Fintype G] {k : Type} [Field k] [CharZero k] {V : Type}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (h : ∑ x, ρ.character x * ρ.character x⁻¹ = (Nat.card G : k)) : ρ.IsIrreducible := by
  classical
  have hcard : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcard
  have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [h, inv_mul_cancel₀ hcard] at h1
  have hfr : Module.finrank k (ρ.IntertwiningMap ρ) = 1 := by exact_mod_cast h1.symm
  have hnt : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h0 : ∀ g, ρ.character g = 0 := fun g => by
      rw [Representation.character, Subsingleton.elim (ρ g) 0, map_zero]
    simp only [h0, zero_mul, Finset.sum_const_zero] at h
    exact hcard h.symm
  let idI : ρ.IntertwiningMap ρ := ⟨LinearMap.id, fun g => by rw [LinearMap.id_comp, LinearMap.comp_id]⟩
  have hid0 : idI ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro e
    exact hv (congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) e)
  have hcG : (Fintype.card G : k) ≠ 0 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · exact (top_ne_bot : (⊤ : Submodule k V) ≠ ⊥) (congrArg Subrepresentation.toSubmodule e).symm
  · by_cases hU : U.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
    · right
      apply Subrepresentation.toSubmodule_injective
      show U.toSubmodule = ⊤
      obtain ⟨W0, hW0⟩ := Submodule.exists_isCompl U.toSubmodule
      let q : V →ₗ[k] V := U.toSubmodule.subtype ∘ₗ Submodule.projectionOnto U.toSubmodule W0 hW0
      have hqU : ∀ u ∈ U.toSubmodule, q u = u := fun u hu =>
        congrArg Subtype.val (Submodule.projectionOnto_apply_left hW0 ⟨u, hu⟩)
      have hqR : ∀ v, q v ∈ U.toSubmodule := fun v => (Submodule.projectionOnto _ _ hW0 v).2
      have hinv : ∀ g, ∀ v ∈ U.toSubmodule, ρ g v ∈ U.toSubmodule := fun g v hv => U.apply_mem_toSubmodule g hv
      have hρρ : ∀ g (v : V), ρ g (ρ g⁻¹ v) = v := fun g v => by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      let P : V →ₗ[k] V := (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g ∘ₗ q ∘ₗ ρ g⁻¹
      have hPv : ∀ v, P v = (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g (q (ρ g⁻¹ v)) := fun v => by
        simp [P, LinearMap.sum_apply]
      have hPI : ∀ h, P ∘ₗ ρ h = ρ h ∘ₗ P := by
        intro h
        apply LinearMap.ext
        intro v
        set_option synthInstance.maxHeartbeats 100000 in
          rw [LinearMap.comp_apply, LinearMap.comp_apply, hPv, hPv, map_smul, map_sum]
        congr 1
        refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g => ?_)
        simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
        rw [hρρ]
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' idI hid0).mp hfr ⟨P, hPI⟩
      have hcv : ∀ v, c • v = P v := fun v => congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) hc
      have hPU : ∀ u ∈ U.toSubmodule, P u = u := fun u hu => by
        rw [hPv]
        have : ∀ g : G, ρ g (q (ρ g⁻¹ u)) = u := fun g => by rw [hqU _ (hinv _ _ hu), hρρ]
        simp only [this, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hcG, one_smul]
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      have hc1 : c = 1 := by
        have e1 := hcv u
        rw [hPU u hu] at e1
        have : (c - 1) • u = 0 := by rw [sub_smul, e1, one_smul, sub_self]
        rcases smul_eq_zero.mp this with h2 | h2
        · exact sub_eq_zero.mp h2
        · exact absurd h2 hu0
      rw [Submodule.eq_top_iff']
      intro v
      have e2 := hcv v
      rw [hc1, one_smul] at e2
      rw [e2, hPv]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => hinv g _ (hqR _))

theorem character_eq_trace_toMatrix' {k : Type} [Field k] {n : ℕ} (ρ : Representation k G (Fin n → k)) (g : G) :
    ρ.character g = Matrix.trace (LinearMap.toMatrix' (ρ g)) := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n)),
    LinearMap.toMatrix_eq_toMatrix']

def mapScalars {K k : Type} [Field K] [Field k] (f : K →+* k) {n : ℕ} (ρ : Representation K G (Fin n → K)) :
    Representation k G (Fin n → k) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toRingEquiv.toMonoidHom.comp
    ((f.mapMatrix : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) k).toMonoidHom.comp
      ((LinearMap.toMatrixAlgEquiv' : Module.End K (Fin n → K) ≃ₐ[K] Matrix (Fin n) (Fin n) K).toRingEquiv.toMonoidHom.comp ρ))

theorem character_mapScalars {K k : Type} [Field K] [Field k] (f : K →+* k) {n : ℕ}
    (ρ : Representation K G (Fin n → K)) (g : G) : (mapScalars f ρ).character g = f (ρ.character g) := by
  rw [character_eq_trace_toMatrix', character_eq_trace_toMatrix']
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mapScalars, Matrix.trace, Matrix.diag, map_sum]

theorem absIrr_realise_of_isPrimitiveRoot {K : Type} [Field K] (σ : K →+* ℂ) (z : K)
    (hz : IsPrimitiveRoot z (Fintype.card G)) (ψ : G → ℂ) (hψ : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) :
    ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  classical
  haveI : CharZero K := σ.charZero
  letI : Algebra K ℂ := σ.toAlgebra
  have hψC : GlobalTheory.BI.IsChar ℂ ℂ ψ := by
    obtain ⟨n, ρ, -, hρ⟩ := hψ
    exact ⟨n, ρ, fun g => by rw [← hρ]; rfl⟩
  obtain ⟨m, τ, hτ⟩ := GlobalTheory.BI.isChar_of_isPrimitiveRoot K ℂ (Fintype.card G) z Fintype.card_ne_zero hz G
    (fun g => pow_card_eq_one) ψ hψC
  have hτσ : ∀ g, σ (τ.character g) = ψ g := fun g => (hτ g).symm
  refine ⟨τ.character, ?_, hτσ⟩
  let A := AlgebraicClosure K
  let ρ' : Representation A G (Fin m → A) := mapScalars (algebraMap K A) τ
  have hch : ∀ g, ρ'.character g = algebraMap K A (τ.character g) := character_mapScalars _ τ
  refine ⟨m, ρ', isIrreducible_of_sum_char_mul_char_inv ρ' ?_, hch⟩
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := ℂ) hψ hψ
  rw [if_pos rfl] at horth
  have hcardC : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsumC : ∑ g, ψ g * ψ g⁻¹ = (Nat.card G : ℂ) := by
    rw [← mul_one (Nat.card G : ℂ), ← horth, ← mul_assoc, mul_inv_cancel₀ hcardC, one_mul]
  have hsumK : ∑ g, τ.character g * τ.character g⁻¹ = (Nat.card G : K) := by
    apply σ.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_natCast, ← hsumC]
    exact Finset.sum_congr rfl fun g _ => by rw [map_mul, hτσ, hτσ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hch, ← map_mul, ← map_sum, hsumK, map_natCast]

end GlobalTheory.BrauerRealise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisDivisibleOfKernelPowers
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PdModP

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def low (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) : Submodule R A :=
  Submodule.span R (γ '' {m | m < N})

theorem low_mono (γ : ℕ → A) {M N : ℕ} (h : M ≤ N) : low R γ M ≤ low R γ N :=
  Submodule.span_mono (Set.image_mono fun _ hm => lt_of_lt_of_le hm h)

theorem mem_low_succ (γ : ℕ → A) (N : ℕ) (s : A) (hs : s ∈ low R γ (N + 1)) :
    ∃ (a : R) (y : A), y ∈ low R γ N ∧ s = a • γ N + y := by
  have e : {m | m < N + 1} = insert N {m | m < N} := by
    ext m; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]; omega
  rw [low, e, Set.image_insert_eq, Submodule.mem_span_insert] at hs
  exact hs

section
variable (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (γ : ℕ → A)
  (hγ : ∀ n : ℕ, ((n.factorial : ℕ) : A) * γ n = algebraMap R A ξ ^ n)
include hu hγ

theorem pow_dvd_gamma {m n : ℕ} (h : m ≤ n) : algebraMap R A ξ ^ m ∣ γ n := by
  obtain ⟨v, hv⟩ := (hu n).exists_left_inv
  have : γ n = v * algebraMap R A ξ ^ n := by rw [← hγ, ← mul_assoc, hv, one_mul]
  rw [this]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _

theorem mul_gamma (n : ℕ) : algebraMap R A ξ * γ n = ((n + 1 : ℕ) : A) * γ (n + 1) := by
  refine (hu n).mul_left_cancel ?_
  have h1 := hγ n
  have h2 := hγ (n + 1)
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ] at h2
  linear_combination (algebraMap R A ξ) * h1 - h2

theorem low_inter (hreg : ∀ y : A, algebraMap R A ξ * y = 0 → y = 0)
    (hsat : ∀ a : R, algebraMap R A ξ ∣ algebraMap R A a → ξ ∣ a) (N : ℕ) :
    ∀ s ∈ low R γ N, algebraMap R A ξ ^ N ∣ s → ∃ c : R, s = c • ((N : A) * γ N) := by
  have hregn : ∀ (n : ℕ) (y : A), algebraMap R A ξ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => intro y hy; exact hreg y (ih _ (by rw [← hy]; ring))
  induction N with
  | zero =>
    intro s hs _
    refine ⟨0, ?_⟩
    simpa [low] using hs
  | succ N ih =>
    intro s hs hd
    obtain ⟨a, y, hy, rfl⟩ := mem_low_succ γ N s hs
    have h1 : algebraMap R A ξ ^ N ∣ a • γ N := by
      rw [Algebra.smul_def]
      exact Dvd.dvd.mul_left (pow_dvd_gamma hu ξ γ hγ le_rfl) _
    obtain ⟨c, rfl⟩ := ih y hy ((dvd_add_right h1).1 ((pow_dvd_pow _ N.le_succ).trans hd))
    obtain ⟨z, hz⟩ := hd
    have h2 : algebraMap R A ξ ∣ algebraMap R A (a + c * N) := by
      refine ⟨(N.factorial : ℕ) * z, sub_eq_zero.1 (hregn N _ ?_)⟩
      rw [Algebra.smul_def, Algebra.smul_def] at hz
      rw [map_add (f := _), map_mul, map_natCast]
      have h3 := hγ N
      linear_combination ((N.factorial : ℕ) : A) * hz - (algebraMap R A a + algebraMap R A c * N) * h3
    obtain ⟨d, hd⟩ := hsat _ h2
    refine ⟨d, ?_⟩
    have h4 := congrArg (algebraMap R A) hd
    rw [map_add (f := _), map_mul, map_natCast, map_mul] at h4
    rw [← mul_gamma hu ξ γ hγ, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    linear_combination γ N * h4

theorem split_low (N : ℕ) (w : A) (hw : w ∈ Submodule.span R (Set.range γ)) :
    ∃ w₁ ∈ low R γ N, algebraMap R A ξ ^ N ∣ w - w₁ := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremThree.main
  | exact _root_.GlobalTheory.IsolatedTheoremThree.main
  | (apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremThree.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremThree.main ..)

end

theorem exists_low (γ : ℕ → A) (s : A) (hs : s ∈ Submodule.span R (Set.range γ)) : ∃ M, s ∈ low R γ M := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m + 1, Submodule.subset_span ⟨m, m.lt_succ_self, rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, h1⟩ := hx
    obtain ⟨N, h2⟩ := hy
    exact ⟨max M N, add_mem (low_mono γ (le_max_left _ _) h1) (low_mono γ (le_max_right _ _) h2)⟩
  | smul a x _ hx =>
    obtain ⟨M, h1⟩ := hx
    exact ⟨M, Submodule.smul_mem _ _ h1⟩

theorem mem_of_forall (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (γ : ℕ → A)
    (hγ : ∀ n : ℕ, ((n.factorial : ℕ) : A) * γ n = algebraMap R A ξ ^ n)
    (hreg : ∀ y : A, algebraMap R A ξ * y = 0 → y = 0)
    (hsat : ∀ a : R, algebraMap R A ξ ∣ algebraMap R A a → ξ ∣ a) (p : ℕ) (hp : 0 < p)
    (s : A) (hs : s ∈ Submodule.span R (Set.range γ))
    (h : ∀ n : ℕ, ∃ u : A, ∃ w ∈ Submodule.span R (Set.range γ), s = u + p * w ∧ algebraMap R A ξ ^ n ∣ u) :
    ∃ w ∈ Submodule.span R (Set.range γ), s = p * w := by
  obtain ⟨M, hM⟩ := exists_low γ s hs
  obtain ⟨u, w, hw, e, hd⟩ := h (p * M)
  obtain ⟨w₁, h1, h2⟩ := split_low hu ξ γ hγ (p * M) w hw
  have h3 : s - p * w₁ ∈ low R γ (p * M) := by
    refine sub_mem (low_mono γ (Nat.le_mul_of_pos_left M hp) hM) ?_
    rw [← nsmul_eq_mul]
    exact nsmul_mem h1 p
  obtain ⟨c, hc⟩ := low_inter hu ξ γ hγ hreg hsat (p * M) _ h3
    (by convert dvd_add hd (Dvd.dvd.mul_left h2 (p : A)) using 1; rw [e]; ring)
  refine ⟨w₁ + (c * M) • γ (p * M), add_mem (Submodule.span_mono (Set.image_subset_range _ _) h1)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), ?_⟩
  rw [Algebra.smul_def] at hc
  rw [Algebra.smul_def, map_mul, map_natCast]
  push_cast at hc
  linear_combination hc

theorem exists_eps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := exists_zeta_eps l
  refine ⟨e, ?_, fun h => ?_⟩
  · have h := hr 0
    rw [h0, map_one] at h
    exact Subtype.ext h
  · have h' := hr 1
    have h2 : rootT e 1 = 1 := h
    rw [h2] at h'
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h']
    rfl

theorem xi_sat_pow {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (he : IsEps e) (k : ℕ) (a : Per.Ainf l)
    (h : xi e ∣ (l : Per.Ainf l) ^ k * a) : xi e ∣ a := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have := XiHaus.xi_sat he 1 ((l : Per.Ainf l) ^ k * a) (by rwa [pow_one, ← mul_assoc, ← pow_succ'])
    rwa [pow_one] at this

end GlobalTheory.MemLoc.PdModP

namespace GlobalTheory.MemLoc

open PdModP in
theorem dvd_of_forall_fil_add : ∀ (l : ℕ) [Fact l.Prime], ∀ s : Per.Acris0 l,
    (∀ n : ℕ, ∃ (u w : Per.Acris0 l), s = u + (l : Per.Acris0 l) * w ∧ (u : Per.AinfP l) ∈ Per.kerP l ^ n) →
    (l : Per.Acris0 l) ∣ s := by
  intro l hl s h
  obtain ⟨e, he⟩ := exists_eps l
  have hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : Per.AinfP l) := fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero
  have hex : ∀ n : ℕ, ∃ g : Per.AinfP l,
      ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n := fun n => by
    obtain ⟨v, hv⟩ := (hu n).exists_right_inv
    exact ⟨v * _, by rw [← mul_assoc, hv, one_mul]⟩
  choose γ hγ using hex
  have hspan : ∀ x : Per.AinfP l, x ∈ Per.Acris0 l ↔ x ∈ Submodule.span (Per.Ainf l) (Set.range γ) := by
    intro x
    rw [mem_Acris0_iff_span l e he]
    congr! 2
    ext y
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (hu n).mul_left_cancel (by rw [hγ, hn])⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, hγ n⟩
  have := XiHaus.isDomain_Fl (l := l)
  have hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (WittVector.p_nonzero l (Per.Fl l))
  have hdom : IsDomain (Per.AinfP l) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hinj := IsLocalization.injective (Per.AinfP l) hle
  have hx0 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    intro h0
    exact XiHaus.xi_coeff_zero_ne he (by rw [h0, WittVector.zero_coeff])
  obtain ⟨w, hw, e1⟩ := mem_of_forall hu (xi e) γ hγ (fun y hy => (mul_eq_zero.1 hy).resolve_left hx0)
    (by
      rintro a ⟨z, hz⟩
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) z
      refine xi_sat_pow he k a ⟨b, hinj ?_⟩
      simp only at hb
      rw [map_mul, map_mul, hz, ← hb]
      ring)
    l hl.out.pos s ((hspan _).1 s.2) (fun n => by
      obtain ⟨u, w, h1, h2⟩ := h n
      refine ⟨u, w, (hspan _).1 w.2, by rw [h1]; simp, ?_⟩
      rwa [ker_localizedTheta_eq_span_xi l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2)
  exact ⟨⟨w, (hspan _).2 hw⟩, Subtype.ext (by simpa using e1)⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_isEps_for_inj (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro hh
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

theorem eq_zero_of_mem_span_pow_away {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (r ξ : A)
    [IsLocalization.Away r B] (hs : ∀ n : ℕ, ∀ a : A, ξ ^ n ∣ r * a → ξ ^ n ∣ a)
    (hh : ∀ a : A, (∀ n : ℕ, ξ ^ n ∣ a) → a = 0) (x : B)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {algebraMap A B ξ} ^ n) : x = 0 := by
  have hs' : ∀ n m : ℕ, ∀ a : A, ξ ^ n ∣ r ^ m * a → ξ ^ n ∣ a := by
    intro n m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      apply ih
      apply hs
      rwa [← mul_assoc, ← pow_succ']
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  have ha : a = 0 := by
    apply hh
    intro n
    have h1 : algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span {ξ ^ n}) := by
      rw [Ideal.map_span, Set.image_singleton, map_pow, ← Ideal.span_singleton_pow,
        ← IsLocalization.mk'_spec B a s]
      exact Ideal.mul_mem_right _ _ (hx n)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r)] at h1
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := h1
    exact hs' n m a (Ideal.mem_span_singleton.1 hm)
  simp [ha]

theorem algebraMap_AinfP_BdRp_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨e, he⟩ := exists_isEps_for_inj l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_mem_span_pow_away (l : Per.Ainf l) (xi e)
    (fun n a h => XiHaus.xi_sat he n a h) (GlobalTheory.MemLoc.eq_zero_of_forall_xi_pow_dvd l e he) x fun n => ?_
  rw [← _root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l e he, ← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
    GlobalTheory.RingIface.ev_alg l n x
  rw [← h1, hx, map_zero]

end GlobalTheory.MemLoc
end

