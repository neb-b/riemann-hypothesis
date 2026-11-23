module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
section
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Unram.exists_basis_antifixed (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [h : Unram F E] :
    ∃ (b : Module.Basis (Fin 2) F E) (d : F), b 0 = 1 ∧ star (b 1) = - b 1 ∧ b 1 * b 1 = algebraMap F E d ∧ d ≠ 0 := by
  have : CharZero F := h.charZero
  have hsmul : ∀ (c : F) (z : E), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, h.star_fix, mul_comm]
  obtain ⟨y, hy⟩ := h.star_ne
  set u : E := y - star y with hu
  have hsu : star u = -u := by rw [hu, star_sub, star_star, neg_sub]
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have key : ∀ s t : F, star (s • (1 : E) + t • u) = s • 1 + t • u → t = 0 := by
    intro s t hst
    rw [star_add, hsmul, hsmul, star_one, hsu, smul_neg, add_right_inj] at hst
    have h2 : (2 : F) • (t • u) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hst]
      exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact (smul_eq_zero.mp h2).resolve_right hu0
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := key s t (by rw [hst, star_zero])
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right one_ne_zero
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [Fintype.card_fin, h.finrank_eq]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  have hsum := b.sum_repr (u * u)
  rw [Fin.sum_univ_two, hb0, hb1] at hsum
  have hfix : star (b.repr (u * u) 0 • (1 : E) + b.repr (u * u) 1 • u) =
      b.repr (u * u) 0 • 1 + b.repr (u * u) 1 • u := by
    rw [hsum, star_mul, hsu, neg_mul_neg]
  have h1 := key _ _ hfix
  rw [h1, zero_smul, add_zero] at hsum
  refine ⟨b, b.repr (u * u) 0, hb0, by rw [hb1, hsu], ?_, ?_⟩
  · rw [hb1, Algebra.algebraMap_eq_smul_one]
    exact hsum.symm
  · intro hd
    rw [hd, zero_smul] at hsum
    exact mul_self_ne_zero.mpr hu0 hsum.symm

theorem quadratic_star_structure {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (d : K) (hb0 : b 0 = 1) (hs : star (b 1) = - b 1)
    (hd : b 1 * b 1 = algebraMap K L d) (hK : ∀ x : K, star (algebraMap K L x) = algebraMap K L x)
    (hdu : IsUnit d) (h2 : IsUnit (2 : K)) :
    Function.Injective (algebraMap K L) ∧ (∀ y : L, algebraMap K L (Algebra.norm K y) = y * star y) ∧
      (∀ y : L, algebraMap K L (Algebra.trace K L y) = y + star y) ∧
      (∀ y' : L, (∀ y : L, Algebra.trace K L (star y' * y) = 0) → y' = 0) := by
  have hrep0 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 0 = a := by
    intro a c; simp
  have hrep1 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 1 = c := by
    intro a c; simp
  have hexp : ∀ y : L, y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [Fin.sum_univ_two]
  have hsmul : ∀ (c : K) (z : L), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, hK, mul_comm]
  have hstar : ∀ y : L, star y = b.repr y 0 • b 0 + (-b.repr y 1) • b 1 := by
    intro y
    conv_lhs => rw [hexp y]
    rw [star_add, hsmul, hsmul, hb0, star_one, hs, smul_neg, neg_smul]
  have hmul : ∀ z : L, z * b 1 = (b.repr z 1 * d) • b 0 + b.repr z 0 • b 1 := by
    intro z
    conv_lhs => rw [hexp z]
    simp only [Algebra.smul_def, hb0, mul_one, map_mul, add_mul]
    linear_combination (algebraMap K L (b.repr z 1)) * hd
  have hc0 : ∀ z : L, b.repr (z * b 0) = b.repr z := by
    intro z; rw [hb0, mul_one]
  have htr : ∀ z : L, Algebra.trace K L z = b.repr z 0 + b.repr z 0 := by
    intro z
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep1]
  have hmap : ∀ x : K, algebraMap K L x = x • b 0 := by
    intro x; rw [hb0, Algebra.algebraMap_eq_smul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hmap] at hx
    have := hrep0 x 0
    rw [zero_smul, add_zero, hx] at this
    simp at this
    exact this.symm
  · intro y
    rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep0, hrep1]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) * (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [Algebra.smul_def, hb0, mul_one, map_mul, map_sub, map_neg]
          linear_combination (algebraMap K L (b.repr y 1) * algebraMap K L (b.repr y 1)) * hd
      _ = y * star y := by rw [← hexp y, ← hstar y]
  · intro y
    rw [htr, hmap]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) + (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [add_smul, neg_smul]; abel
      _ = y + star y := by rw [← hexp y, ← hstar y]
  · intro y' hy'
    have g1 := hy' 1
    have g2 := hy' (b 1)
    rw [mul_one, htr, hstar, hrep0] at g1
    rw [hmul, htr, hrep0, hstar, hrep1] at g2
    have hp : b.repr y' 0 = 0 := by
      have h3 : (2 : K) * b.repr y' 0 = 0 := by rw [two_mul]; exact g1
      exact h2.mul_right_eq_zero.mp h3
    have hq : b.repr y' 1 = 0 := by
      have h3 : (2 : K) * (b.repr y' 1 * d) = 0 := by linear_combination -g2
      exact hdu.mul_left_eq_zero.mp (h2.mul_right_eq_zero.mp h3)
    rw [hexp y', hp, hq, zero_smul, zero_smul, add_zero]

theorem Et.quadratic_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nonempty (Module.Basis (Fin 2) A.K A.L) ∧ Function.Injective (algebraMap A.K A.L) ∧ (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (∀ y' : A.L, (∀ y : A.L, Algebra.trace A.K A.L (star y' * y) = 0) → y' = 0) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  let B : Module.Basis (Fin 2) A.K A.L := A.push.symm.out.basis b
  have hB : ∀ i, B i = algebraMap E A.L (b i) := fun i => by
    simp [B, IsBaseChange.basis_apply]
  have key := quadratic_star_structure B (algebraMap F A.K d) (by rw [hB, hb0, map_one])
    (by rw [hB, A.star_E, hs, map_neg])
    (by
      rw [hB, ← map_mul, hd, ← IsScalarTower.algebraMap_apply F E A.L,
        ← IsScalarTower.algebraMap_apply F A.K A.L])
    A.star_K ((isUnit_iff_ne_zero.mpr hd0).map _)
    (by
      have h2F := (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : F) ≠ 0)).map (algebraMap F A.K)
      rwa [map_ofNat] at h2F)
  exact ⟨⟨B⟩, key.1, key.2.1, key.2.2.1, key.2.2.2⟩

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientMultiplicityShiftLatticeQuotient
section
noncomputable section
namespace GlobalTheory.PhiGam.QuotShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section lin
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem mem_iSup_comap_pow (S : Module.End k U) (Q : Submodule k U) (hQ : ∀ q ∈ Q, S q ∈ Q) (p : U) :
    p ∈ ⨆ m : ℕ, Q.comap (S ^ m) ↔ ∃ m : ℕ, (S ^ m) p ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m y hy => ?_
    rw [Submodule.mem_comap, pow_succ', Module.End.mul_apply]
    exact hQ _ hy
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

theorem gmult_transport (T T' : Module.End k U) (e : U ≃ₗ[k] U) (P Q P' Q' : Submodule k U)
    (hP' : ∀ p, e p ∈ P' ↔ p ∈ P) (hQ' : ∀ p, e p ∈ Q' ↔ p ∈ Q)
    (hTP : ∀ p ∈ P, T p ∈ P) (hTQ : ∀ p ∈ Q, T p ∈ Q) (hTQ' : ∀ p ∈ Q', T' p ∈ Q') (x y : k)
    (h : ∀ p ∈ P, (T' (e p) - x • e p) - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  set S := T - algebraMap k (Module.End k U) y with hS
  set S' := T' - algebraMap k (Module.End k U) x with hS'
  have hSa : ∀ p, S p = T p - y • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have hSa' : ∀ p, S' p = T' p - x • p := fun p => by simp [hS', Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hSa]; exact P.sub_mem (hTP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hSa]; exact Q.sub_mem (hTQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hSa']; exact Q'.sub_mem (hTQ' p hp) (Q'.smul_mem _ hp)
  have key : ∀ p ∈ P, ∀ m : ℕ, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro p hp m
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ ih.1, ?_⟩
      have h1 := hSQ' _ ih.2
      have h2 := h _ ih.1
      rw [← hSa, ← hSa'] at h2
      have h3 := Q'.add_mem h1 h2
      rwa [map_sub, sub_add_sub_cancel] at h3
  have hmem : ∀ p, e p ∈ (P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)) ↔ p ∈ (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) := by
    intro p
    rw [Submodule.mem_inf, Submodule.mem_inf, mem_iSup_comap_pow S Q hSQ, mem_iSup_comap_pow S' Q' hSQ', hP']
    refine and_congr_right fun hp => exists_congr fun m => ?_
    rw [← hQ']
    have := (key p hp m).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 this
    · intro h1; simpa using Q'.add_mem this h1
  unfold gmult
  rw [← hS, ← hS']
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)
  have hA : A.map (e : U →ₗ[k] U) = A' := by
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [hmem]
    exact Submodule.map_equiv_eq_comap_symm e A ▸ by simp
  let e' : A ≃ₗ[k] A' := e.ofSubmodules A A' hA
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') e' ?_).finrank_eq.symm
  ext z
  obtain ⟨w, rfl⟩ := e'.surjective z
  have : (e' w ∈ Q'.submoduleOf A') ↔ w ∈ Q.submoduleOf A := hQ' w
  rw [this]
  exact Submodule.map_equiv_eq_comap_symm e' _ ▸ by simp

theorem fin_of_le {A B C : Submodule k U} (h : C ≤ B) (hf : FiniteDimensional k (A.map C.mkQ)) :
    FiniteDimensional k (A.map B.mkQ) := by
  have : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [this]; infer_instance

theorem fin_trans {A B C : Submodule k U} (h : C ≤ B) (h1 : FiniteDimensional k (A.map B.mkQ))
    (h2 : FiniteDimensional k (B.map C.mkQ)) : FiniteDimensional k (A.map C.mkQ) := by
  have e : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [e] at h1
  have hle : A.map C.mkQ ⊓ LinearMap.ker (Submodule.factor h) ≤ B.map C.mkQ := by
    rintro _ ⟨⟨a, -, rfl⟩, ha⟩
    exact ⟨a, (Submodule.Quotient.mk_eq_zero B).1 ha, rfl⟩
  have h3 := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor h)
    (Module.Finite.iff_fg.1 h1) (Module.Finite.iff_fg.1 h3))

theorem fin_quot {A B : Submodule k U} (h : FiniteDimensional k (A.map B.mkQ)) :
    FiniteDimensional k (↥A ⧸ B.submoduleOf A) := by
  have e := LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at e
  exact e.symm.finiteDimensional

theorem gmult_self (T : Module.End k U) (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  rw [Submodule.submoduleOf_eq_top.2 inf_le_left]
  exact Module.finrank_zero_of_subsingleton

end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_sup_le {P Q : Submodule k⟦X⟧ V} {m : ℕ} (h : sh ((m + 1 : ℕ) : ℤ) P ≤ Q) :
    sh (m : ℤ) (Q ⊔ sh 1 P) ≤ Q := by
  have : sh (m : ℤ) (Q ⊔ sh 1 P) = sh (m : ℤ) Q ⊔ sh (m : ℤ) (sh 1 P) := Submodule.map_sup _ _ _
  rw [this, sh_sh_eq]
  refine sup_le ?_ (by exact_mod_cast h)
  simpa [sh_zero_eq] using sh_le_sh_of_le (Int.natCast_nonneg m) Q

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_one_le (P : Submodule k⟦X⟧ V) : sh 1 P ≤ P := by
  simpa [sh_zero_eq] using sh_le_sh_of_le (zero_le_one' ℤ) P

theorem fin_lat (m : ℕ) : ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → sh (m : ℤ) P ≤ Q →
    FiniteDimensional k ((P.restrictScalars k).map (Q.restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    intro P Q _ _ h
    have : (P.restrictScalars k).map (Q.restrictScalars k).mkQ = ⊥ := by
      rw [← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
      rw [Nat.cast_zero, sh_zero_eq] at h
      exact h
    rw [this]; infer_instance
  | succ m ih =>
    intro P Q hP hQ h
    refine fin_trans (B := (Q ⊔ sh 1 P).restrictScalars k) (fun y hy => Submodule.mem_sup_left hy) ?_
      (ih _ _ (hQ.sup (hP.map _)) hQ (sh_sup_le h))
    exact fin_of_le (fun y hy => Submodule.mem_sup_right hy) (Window.finite_quot hP)

theorem step {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {P Q : Submodule k⟦X⟧ V}
    (hP : CondC g P) (hQ : CondC g Q) (h : sh 1 P ≤ Q) (x : k) :
    qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  have hv := vv_ne_zero k
  let e : V ≃ₗ[k] V := (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k) hv).restrictScalars k
  have he : ∀ p, e p = vv k • p := fun p => rfl
  have hN : ∀ (N : Submodule k⟦X⟧ V) p, e p ∈ (sh 1 N).restrictScalars k ↔ p ∈ N.restrictScalars k := by
    intro N p
    rw [Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, mem_sh_iff_smul_mem, he, smul_smul,
      zpow_neg_one, inv_mul_cancel₀ hv, one_smul]
  refine gmult_transport _ _ e _ _ _ _ (hN P) (hN Q) (fun p hp => Window.nab_mem hP hp)
    (fun p hp => Window.nab_mem hQ hp) (fun p hp => Window.nab_mem_sh R hg hQ 1 hp) _ _ fun p hp => ?_
  obtain ⟨n', hn', hs⟩ := Window.nab_shift R hg hP 1 hp
  rw [zpow_one, ← he, ← he] at hs
  rw [hs, ← map_smul, ← map_sub, ← map_sub, hN]
  have : nab g p - ((1 : ℤ) : k) • p + vv k • n' - x • p - (nab g p - (x + 1) • p) = vv k • n' := by
    rw [Int.cast_one, add_smul]; abel
  rw [this]
  exact h (mem_sh_iff_exists.2 ⟨n', hn', by rw [zpow_one]⟩)

theorem qmult_add (g : V →ₗ[k] V) (m : ℕ) {P Q S : Submodule k⟦X⟧ V} (hP : P.FG) (hS : S.FG) (h1 : S ≤ Q)
    (h2 : Q ≤ P) (cP : ∀ p ∈ P, nab g p ∈ P) (cQ : ∀ p ∈ Q, nab g p ∈ Q) (cS : ∀ p ∈ S, nab g p ∈ S)
    (h : sh (m : ℤ) P ≤ S) (x : k) : qmult g P S x = qmult g P Q x + qmult g Q S x :=
  GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k) (S.restrictScalars k) h1 h2 cP cQ cS
    (fin_quot (fin_lat m P S hP hS h)) x

theorem shift_of_le {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) (x : k) (m : ℕ) :
    ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → Q ≤ P → CondC g P → CondC g Q → sh (m : ℤ) P ≤ Q →
      qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  induction m with
  | zero =>
    intro P Q _ _ hle _ _ h
    rw [Nat.cast_zero, sh_zero_eq] at h
    rw [le_antisymm hle h, qmult, qmult, gmult_self, gmult_self]
  | succ m ih =>
    intro P Q hP hQ hle cP cQ h
    have hle' : Q ⊔ sh 1 P ≤ P := sup_le hle (sh_one_le P)
    have cQ' : CondC g (Q ⊔ sh 1 P) := by
      rw [condC_iff_nab_mem]
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (Window.nab_mem cQ ha) (Window.nab_mem_sh R hg cP 1 hb)
    have h' : sh ((m + 1 : ℕ) : ℤ) (sh 1 P) ≤ sh 1 Q := by
      rw [sh_sh_eq, add_comm, ← sh_sh_eq]; exact sh_le_sh 1 h
    have a1 := qmult_add g (m + 1) hP hQ (le_sup_left (b := sh 1 P)) hle' (fun p hp => Window.nab_mem cP hp)
      (fun p hp => Window.nab_mem cQ' hp) (fun p hp => Window.nab_mem cQ hp) h (x + 1)
    have a2 := qmult_add g (m + 1) (P := sh 1 P) (Q := sh 1 (Q ⊔ sh 1 P)) (S := sh 1 Q) (hP.map _) (hQ.map _)
      (sh_le_sh 1 le_sup_left) (sh_le_sh 1 hle') (fun p hp => Window.nab_mem_sh R hg cP 1 hp)
      (fun p hp => Window.nab_mem_sh R hg cQ' 1 hp) (fun p hp => Window.nab_mem_sh R hg cQ 1 hp) h' x
    rw [a1, a2, step R hg cP cQ' le_sup_right,
      ih (Q ⊔ sh 1 P) Q (hQ.sup (hP.map _)) hQ le_sup_left cQ' cQ (sh_sup_le h)]

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ x : k, qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hle cP cQ x
  obtain ⟨m, hm⟩ := Close.exists_pow hP.1 hQ.2
  exact shift_of_le R hg x m P Q hP.1 hQ.1 hle cP cQ (Close.sh_le hm)

end GlobalTheory.PhiGam.QuotShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityShiftLatticeVariablePow
section
noncomputable section
namespace GlobalTheory.PhiGam.SenShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem mem_iSup_comap_pow {k U : Type} [Field k] [AddCommGroup U] [Module k U] (S : Module.End k U)
    (Q : Submodule k U) (hQ : ∀ p ∈ Q, S p ∈ Q) (u : U) :
    u ∈ (⨆ m : ℕ, Q.comap (S ^ m)) ↔ ∃ m : ℕ, (S ^ m) u ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hQ _ hp
  exact Submodule.mem_iSup_of_directed _ hmono.directed_le

theorem gmult_transport {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T T' : Module.End k U)
    (P Q P' Q' : Submodule k U) (e : U ≃ₗ[k] U) (x y : k)
    (heP : ∀ u, e u ∈ P' ↔ u ∈ P) (heQ : ∀ u, e u ∈ Q' ↔ u ∈ Q)
    (hP : ∀ p ∈ P, T p ∈ P) (hQ : ∀ p ∈ Q, T p ∈ Q) (hQ' : ∀ p ∈ Q', T' p ∈ Q')
    (h : ∀ p ∈ P, T' (e p) - x • e p - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  unfold gmult
  set S := T - algebraMap k (Module.End k U) y with hSdef
  set S' := T' - algebraMap k (Module.End k U) x with hS'def
  have hS : ∀ u, S u = T u - y • u := fun u => by simp [hSdef, Module.algebraMap_end_apply]
  have hS' : ∀ u, S' u = T' u - x • u := fun u => by simp [hS'def, Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hS]; exact P.sub_mem (hP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hS]; exact Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hS']; exact Q'.sub_mem (hQ' p hp) (Q'.smul_mem _ hp)
  have hpow : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro m p hp
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ h1, ?_⟩
      have h3 := h _ h1
      rw [← hS, ← hS'] at h3
      have h4 := Q'.add_mem (hSQ' _ h2) h3
      rw [map_sub] at h4
      simpa using h4
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) with hA
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m) with hA'
  have heA : ∀ u, e u ∈ A' ↔ u ∈ A := by
    intro u
    rw [hA, hA', Submodule.mem_inf, Submodule.mem_inf, heP, mem_iSup_comap_pow S Q hSQ,
      mem_iSup_comap_pow S' Q' hSQ']
    refine and_congr_right fun hu => exists_congr fun m => ?_
    rw [← heQ]
    have h2 := (hpow m u hu).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 h2
    · intro h1; simpa using Q'.add_mem h2 h1
  have hmap : A.map (e : U →ₗ[k] U) = A' := by
    ext u
    obtain ⟨u, rfl⟩ := e.surjective u
    rw [heA]
    exact Submodule.mem_map_equiv A |>.trans (by simp)
  let E : A ≃ₗ[k] A' := e.ofSubmodules A A' hmap
  have hE : ∀ z : A, ((E z : A') : U) = e z := fun z => rfl
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') E ?_).finrank_eq.symm
  ext z
  obtain ⟨z, rfl⟩ := E.surjective z
  refine (Submodule.mem_map_equiv _).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  change (z : U) ∈ Q ↔ ((E z : A') : U) ∈ Q'
  rw [hE, heQ]

theorem sen_sh : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (x : k), sen g (sh a N) x = sen g N (x + a) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N _ hC a x
  have hv : vv k ≠ 0 := vv_ne_zero k
  let e : V ≃ₗ[k] V :=
    (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k ^ a) (zpow_ne_zero a hv)).restrictScalars k
  have he : ∀ u, e u = vv k ^ a • u := fun u => rfl
  have hmem : ∀ (M : Submodule k⟦X⟧ V) (u : V), e u ∈ sh a M ↔ u ∈ M := fun M u => by
    rw [he, mem_sh_iff_smul_mem, smul_smul, ← zpow_add₀ hv, neg_add_cancel, zpow_zero, one_smul]
  have hsh : sh 1 (sh a N) = sh a (sh 1 N) := by rw [sh_sh_eq, sh_sh_eq, add_comm]
  unfold sen qmult
  refine gmult_transport (nab g) (nab g) _ _ _ _ e x (x + a) (fun u => hmem N u) (fun u => ?_)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (fun p hp => ?_)
    (fun p hp => ?_)
  · rw [hsh]; exact hmem _ u
  · rw [sh_sh_eq] at hp ⊢
    exact Window.nab_mem_sh R hg hC _ hp
  · obtain ⟨n', hn', h⟩ := Window.nab_shift R hg hC a hp
    rw [← he, ← he] at h
    rw [hsh, h, ← map_smul, ← map_sub, ← map_sub]
    refine (hmem _ _).2 (mem_sh_iff_exists.2 ⟨n', hn', ?_⟩)
    rw [zpow_one, add_smul]
    abel

end GlobalTheory.PhiGam.SenShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEqSumCoordsOfAlgEquiv
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_pi_fin_self {F : Type} [Field F] (r : ℕ) (x : Fin r → F) :
    Algebra.trace F (Fin r → F) x = ∑ i, x i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun F (Fin r)), Matrix.trace]
  congr 1
  ext i
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_apply]

theorem trace_eq_sum_coords_of_algEquiv {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ)
    (e : K ≃ₐ[F] (Fin r → F)) (k : K) : Algebra.trace F K k = ∑ i, e k i := by
  rw [← Algebra.trace_eq_of_algEquiv e k, trace_pi_fin_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceTowerFiniteEtaleHermitianPair
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_tower_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (z : A.L), Algebra.trace F A.K (Algebra.trace A.K A.L z) = Algebra.trace F E (Algebra.trace E A.L z) := by
  intro F E _ _ _ _ hU A z
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  have hE : IsBaseChange E (IsScalarTower.toAlgHom F A.K A.L).toLinearMap := A.push.out
  have hK : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free E A.L := Module.Free.of_equiv hE.equiv
  haveI : Module.Finite E A.L := Module.Finite.equiv hE.equiv
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hK.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hK.equiv
  rw [Algebra.trace_trace, Algebra.trace_trace]

end GlobalTheory
end

