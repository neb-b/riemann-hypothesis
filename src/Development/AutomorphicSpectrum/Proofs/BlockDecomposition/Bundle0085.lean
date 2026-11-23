module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0072
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0082
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedUnitCoefficientRootStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open Polynomial in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutely_closed_unit_coefficient_root :
    ∀ {S : Type} [CommRing S], Aic (S := S) →
      (∀ a b : S, IsUnit (a + b) → IsUnit a ∨ IsUnit b) →
      ∀ (Q : Polynomial S) (i : ℕ), Q.coeff 0 = 1 → 0 < i → IsUnit (Q.coeff i) →
        ∃ y, Q.eval y = 0 := by
  intro S _ hA hL Q i h0 hi hu
  rcases subsingleton_or_nontrivial S with hs | hn
  · exact ⟨0, Subsingleton.elim _ _⟩
  have : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add hL
  have htd : Q.natTrailingDegree = 0 :=
    Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [h0]; exact one_ne_zero))
  have hmon : Q.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, h0]
  have hdeg : Q.reverse.natDegree = Q.natDegree := by
    rw [reverse_natDegree, htd, Nat.sub_zero]
  have hid : i ≤ Q.natDegree := le_natDegree_of_ne_zero hu.ne_zero
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA _ hmon
  by_cases hex : ∃ b ∈ s, IsUnit b
  · obtain ⟨b, hbs, hb⟩ := hex
    have hroot : Q.reverse.eval b = 0 := by
      have hdvd : (X : S[X]) - C b ∣ Q.reverse := by
        rw [hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
      exact dvd_iff_isRoot.mp hdvd
    obtain ⟨u, rfl⟩ := hb
    refine ⟨((u⁻¹ : Sˣ) : S), ?_⟩
    let : Invertible ((u⁻¹ : Sˣ) : S) := (u⁻¹).invertible
    have key := eval₂_reverse_mul_pow (RingHom.id S) ((u⁻¹ : Sˣ) : S) Q
    have hinv : ⅟((u⁻¹ : Sˣ) : S) = (u : S) := by simp
    rw [hinv, eval₂_id, eval₂_id, hroot, zero_mul] at key
    exact key.symm
  · exfalso
    let m := IsLocalRing.maximalIdeal S
    have coeff_prod_mem (t : Multiset S) (ht : ∀ b ∈ t, b ∈ m) :
        ∀ k < t.card, ((t.map fun b => (X : S[X]) - C b).prod).coeff k ∈ m := by
      induction t using Multiset.induction_on with
      | empty => intro k hk; simp at hk
      | cons a t ih =>
        intro k hk
        have ha := ht a (Multiset.mem_cons_self a t)
        have ih' := ih fun b hb => ht b (Multiset.mem_cons_of_mem hb)
        rw [Multiset.map_cons, Multiset.prod_cons, sub_mul]
        rw [Multiset.card_cons] at hk
        cases k with
        | zero =>
          simp only [coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
          exact m.neg_mem (m.mul_mem_right _ ha)
        | succ k =>
          simp only [coeff_sub, coeff_X_mul, coeff_C_mul]
          exact m.sub_mem (ih' k (by omega)) (m.mul_mem_right _ ha)
    have hall : ∀ b ∈ s, b ∈ m := fun b hb =>
      (IsLocalRing.mem_maximalIdeal b).mpr fun hbu => hex ⟨b, hb, hbu⟩
    have hcard : s.card = Q.natDegree := by
      rw [← hdeg, hs, natDegree_multiset_prod_X_sub_C_eq_card]
    have hcoeff : Q.reverse.coeff (Q.natDegree - i) = Q.coeff i := by
      rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
      congr 1
      omega
    have hmem := coeff_prod_mem s hall (Q.natDegree - i) (by omega)
    rw [← hs, hcoeff] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorOpenCompact
section
open Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.CharPerp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def perp {n : ℕ} (ψ : AddChar k Circle) (A : AddSubgroup (Fin n → k)) :
    AddSubgroup (Fin n → k) where
  carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
  zero_mem' := fun a _ => by simp
  add_mem' := fun {x y} hx hy a ha => by
    rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  neg_mem' := fun {x} hx a ha => by
    rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one]

theorem isOpen_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k))) :
    IsOpen (perp ψ A : Set (Fin n → k)) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have hN : IsOpen ((fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) ⁻¹' cball s) :=
    (isOpen_cball s).preimage continuous_dot
  have hsub : ({0} : Set (Fin n → k)) ×ˢ (A : Set (Fin n → k)) ⊆
      (fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) ⁻¹' cball s := by
    rintro ⟨x, a⟩ ⟨hx, -⟩
    obtain rfl : x = 0 := hx
    simp [cball]
  obtain ⟨u, v, hu, -, h0u, hAv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hAc hN hsub
  refine AddSubgroup.isOpen_of_mem_nhds (perp ψ A) (g := 0) ?_
  refine Filter.mem_of_superset (hu.mem_nhds (h0u rfl)) fun ξ hξ a ha => ?_
  exact hs _ (huv (Set.mk_mem_prod hξ (hAv ha)))

theorem isClosed_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (A : AddSubgroup (Fin n → k)) : IsClosed (perp ψ A : Set (Fin n → k)) := by
  have : (perp ψ A : Set (Fin n → k)) =
      ⋂ a ∈ A, (fun ξ : Fin n → k => ψ (ξ ⬝ᵥ a)) ⁻¹' {1} := by
    ext ξ
    simp [perp]
  rw [this]
  refine isClosed_biInter fun a _ => isClosed_singleton.preimage ?_
  exact hψ.comp (continuous_id.dotProduct continuous_const)

theorem isCompact_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (A : AddSubgroup (Fin n → k)) (hAo : IsOpen (A : Set (Fin n → k))) :
    IsCompact (perp ψ A : Set (Fin n → k)) := by
  classical
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  obtain ⟨s, hs⟩ := exists_box_subset (n := Fin n) (hAo.mem_nhds A.zero_mem)
  refine (isCompact_box (n := Fin n) (c * s⁻¹)).of_isClosed_subset (isClosed_perp ψ hψ A) ?_
  intro ξ hξ i _
  by_contra hi
  obtain ⟨t, ht, hne⟩ := hc.exists_ne_one s hi
  have hmem : Pi.single i t ∈ box (Fin n) s := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  apply hne
  have := hξ _ (hs hmem)
  rwa [dotProduct_single, mul_comm] at this

theorem perp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) →
    IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧
      IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo
  exact ⟨isOpen_perp ψ hψ A hAc, isCompact_perp ψ hψ h1 A hAo⟩

end GlobalTheory.CompanionTheory.CharPerp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevel
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TwCok

theorem pow_torsion_bounded {W : Type} [CommRing W] [IsNoetherianRing W] (r : W) (T : Type 1)
    [AddCommGroup T] [Module W T] [Module.Finite W T] :
    ∃ c : ℕ, ∀ (k : ℕ) (t : T), r ^ k • t = 0 → r ^ c • t = 0 := by
  haveI := isNoetherian_of_isNoetherianRing_of_finite W T
  let f : ℕ →o Submodule W T :=
    ⟨fun k => LinearMap.ker ((r ^ k) • LinearMap.id : T →ₗ[W] T), fun a b hab t ht => by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at ht ⊢
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [pow_add, mul_comm, mul_smul, ht, smul_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance f
  refine ⟨n, fun k t ht => ?_⟩
  rcases le_total k n with hkn | hnk
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [pow_add, mul_comm, mul_smul, ht, smul_zero]
  · have h1 : t ∈ f k := by
      simp only [f, OrderHom.coe_mk, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact ht
    rw [← hn k hnk] at h1
    have h2 : t ∈ LinearMap.ker ((r ^ n) • LinearMap.id : T →ₗ[W] T) := h1
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at h2
    exact h2

variable {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W}

def conn (Q : LSeq l S S') (n : ℕ) (x : S.M n) : S'.lim :=
  ⟨fun a => Q.δ n a x, fun a => Q.δ_r n a x⟩

theorem conn_smul (Q : LSeq l S S') (n : ℕ) (s : W) (x : S.M n) :
    s • conn Q n x = conn Q n (s • x) := by
  apply Subtype.ext
  funext a
  simp [conn]

theorem conn_kill (Q : LSeq l S S') (n : ℕ) (x : S.M n) : ((l : W) ^ n) • conn Q n x = 0 := by
  rw [conn_smul, Q.kill n x]
  apply Subtype.ext
  funext a
  simp [conn]

theorem lift_of_conn_zero (Q : LSeq l S S') (hA : ∀ n, IsArtinian W (S.M n)) (n : ℕ) (x : S.M n)
    (h : ∀ a, Q.δ n a x = 0) : ∃ y : S.lim, y.1 n = x := by
  classical
  have hy : ∀ m, n ≤ m → ∃ u : S.M m, Q.ρ m n u = x := fun m hm =>
    Q.ex₂ (m - n) n m (by omega) x (h _)
  let y : ∀ m, S.M m := fun m => if hm : n ≤ m then (hy m hm).choose else 0
  have hyx : ∀ m (hm : n ≤ m), Q.ρ m n (y m) = x := by
    intro m hm
    simp only [y, dif_pos hm]
    exact (hy m hm).choose_spec
  let N : ∀ m, Submodule W (S.M m) := fun m => if n ≤ m then LinearMap.ker (Q.ρ m n) else ⊤
  have hN : ∀ m (hm : n ≤ m), N m = LinearMap.ker (Q.ρ m n) := fun m hm => if_pos hm
  have hN' : ∀ m (hm : ¬ n ≤ m), N m = ⊤ := fun m hm => if_neg hm
  have hNr : ∀ m, ∀ u ∈ N (m + 1), S.r m u ∈ N m := by
    intro m u hu
    by_cases hm : n ≤ m
    · rw [hN (m + 1) (by omega), LinearMap.mem_ker] at hu
      rw [hN m hm, LinearMap.mem_ker, ← Q.ρ_succ m n hm]
      exact hu
    · rw [hN' m hm]
      exact Submodule.mem_top
  have hyr : ∀ m, S.r m (y (m + 1)) - y m ∈ N m := by
    intro m
    by_cases hm : n ≤ m
    · rw [hN m hm, LinearMap.mem_ker, map_sub, ← Q.ρ_succ m n hm, hyx (m + 1) (by omega), hyx m hm,
        sub_self]
    · rw [hN' m hm]
      exact Submodule.mem_top
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.CompanionTheory.ArtinTower.exists_compatible W S hA N y hNr hyr
  refine ⟨z, ?_⟩
  have h1 := hz n
  rw [hN n le_rfl, LinearMap.mem_ker, map_sub, Q.ρ_self, Q.ρ_self, sub_eq_zero] at h1
  have h2 := hyx n le_rfl
  rw [Q.ρ_self] at h2
  rw [← h2]
  exact h1

theorem lim_cokernel_bounded : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W)
    (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim →
    ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  intro W _ _ l S S' Q hA hF
  obtain ⟨c, hc⟩ := pow_torsion_bounded ((l : W)) S'.lim
  refine ⟨c, fun n x => lift_of_conn_zero Q hA n _ (fun a => ?_)⟩
  have h0 : conn Q n ((l : W) ^ c • x) = 0 := by
    rw [← conn_smul]
    exact hc n _ (conn_kill Q n x)
  have h3 := congrArg (fun v : S'.lim => (v : ∀ m, S'.M m) a) h0
  simpa [conn] using h3

end GlobalTheory.CompanionTheory.TwCok
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CancelLTensor
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovComp

theorem cancel_lTensor (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁]
    {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) (w : B₁ ⊗[B] (B ⊗[A] K₁)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₀ ((d.baseChange B).lTensor B₁ w) =
      d.lTensor B₁ (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₁ w) := by
  induction w with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b t =>
    induction t with
    | add x y hx hy => simp only [map_add (f := _), TensorProduct.tmul_add, hx, hy]
    | tmul c k => simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.smul_tmul']

theorem cov_comp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B](B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁] (r : ℕ → A), Pf p A → Pf p B → IsRt p r → Cov p r B → Cov p (fun k => algebraMap A B (r k)) B₁ → Cov p r B₁ := by
  intro p _ A _ B _ _ B₁ _ _ _ _ r hA hB hr h1 h2
  unfold Cov at h1 h2 ⊢
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  have e1 : Pf p (B ⊗[A] K₁) := PerfectRing.pf_tensor p A B K₁ hA hB hK₁
  have e0 : Pf p (B ⊗[A] K₀) := PerfectRing.pf_tensor p A B K₀ hA hB hK₀
  have e2 : Good p (fun k => algebraMap A B (r k)) (d.baseChange B) :=
    GoodBaseChange.good_baseChange p A B r K₁ K₀ d hd
  have hz' : (1 : B₁) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] z) ∈ (LinearMap.lTensor B₁ (d.baseChange B)).range := by
    obtain ⟨w, hw⟩ := hz
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₁).symm w, ?_⟩
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₀).injective
    rw [cancel_lTensor, LinearEquiv.apply_symm_apply, hw]
    simp
  have hB' := h2 _ _ e1 e0 (d.baseChange B) e2 _ hz' (k + 1)
  have h3 : (1 : B) ⊗ₜ[A] (r (k + 1) • z) ∈ (LinearMap.lTensor B d).range := by
    obtain ⟨v, hv⟩ := hB'
    refine ⟨v, ?_⟩
    change (d.baseChange B) v = _
    rw [hv, algebraMap_smul, ← TensorProduct.tmul_smul]
  have h4 := h1 K₁ K₀ hK₁ hK₀ d hd (r (k + 1) • z) h3 (k + 1)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    rw [← hr k, ← sq, ← pow_add, Nat.sub_add_cancel hp]
  rw [hrk, mul_smul, mul_smul]
  exact Submodule.smul_mem _ _ h4

end GlobalTheory.CompanionTheory.CovComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFibreGramDifferential
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.GramDiff

variable {E : Type} [CommRing E] (τ : E →+* E)

theorem cT_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i j
  simp [cT]

theorem cT_zero {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i j
  simp [cT]

theorem cT_neg {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) : cT τ (-A) = -cT τ A := by
  ext i j
  simp [cT]

theorem cT_smul {a b : ℕ} (c : E) (A : Matrix (Fin a) (Fin b) E) :
    cT τ (c • A) = τ c • cT τ A := by
  ext i j
  simp [cT]

theorem cT_cT (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i j
  simp [cT, hτ]

theorem cT_cross (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} {S : Matrix (Fin m) (Fin m) E} (hS : cT τ S = S)
    (x y : Matrix (Fin m) (Fin n) E) : cT τ (cT τ x * S * y) = cT τ y * S * x := by
  rw [cT_mul, cT_mul, cT_cT τ hτ, hS, Matrix.mul_assoc]

def hermSub (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) E) where
  carrier := {H | cT τ H = H}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [cT_add, ha, hb]
  zero_mem' := cT_zero τ
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [cT_neg, ha]

def diffMap (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S)
    (x : Matrix (Fin m) (Fin n) E) : Matrix (Fin m) (Fin n) E →+ hermSub τ n :=
  AddMonoidHom.mk'
    (fun y => ⟨cT τ y * S * x + cT τ x * S * y, by
      change cT τ (cT τ y * S * x + cT τ x * S * y) = cT τ y * S * x + cT τ x * S * y
      rw [cT_add, cT_cross τ hτ hS, cT_cross τ hτ hS, add_comm]⟩)
    (by
      intro a b
      apply Subtype.ext
      change cT τ (a + b) * S * x + cT τ x * S * (a + b) =
        (cT τ a * S * x + cT τ x * S * a) + (cT τ b * S * x + cT τ x * S * b)
      rw [cT_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add]
      abel)

theorem exists_trace_one {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) : ∃ θ : E, θ + τ θ = 1 := by
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : (u - τ u) * τ v = -1 := by
    have := congrArg τ hv
    rw [map_mul, map_sub, h.inv, map_one] at this
    linear_combination -this
  have h2 : τ v = -v := by
    linear_combination (-(τ v)) * hv + v * h1
  refine ⟨u * v, ?_⟩
  rw [map_mul, h2]
  linear_combination hv

theorem diffMap_surjective {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S) (T : Matrix (Fin n) (Fin n) E)
    (x : Matrix (Fin m) (Fin n) E) (hT : IsUnit T.det) (hx : cT τ x * S * x = T) :
    Function.Surjective (diffMap τ h.inv S hS x) := by
  rintro ⟨H, hH⟩
  have hH' : cT τ H = H := hH
  obtain ⟨θ, hθ⟩ := exists_trace_one τ h
  have hW : cT τ x * S * (x * T⁻¹ * (θ • H)) = θ • H := by
    calc cT τ x * S * (x * T⁻¹ * (θ • H)) = (cT τ x * S * x) * T⁻¹ * (θ • H) := by
          simp only [Matrix.mul_assoc]
      _ = θ • H := by rw [hx, Matrix.mul_nonsing_inv T hT, Matrix.one_mul]
  refine ⟨x * T⁻¹ * (θ • H), ?_⟩
  apply Subtype.ext
  change cT τ (x * T⁻¹ * (θ • H)) * S * x + cT τ x * S * (x * T⁻¹ * (θ • H)) = H
  rw [← cT_cross τ h.inv hS x (x * T⁻¹ * (θ • H)), hW, cT_smul, hH', ← add_smul, add_comm, hθ, one_smul]

theorem card_fibre_mul {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] (f : A →+ B)
    (hf : Function.Surjective f) (b : B) : Nat.card {a // f a = b} * Nat.card B = Nat.card A := by
  obtain ⟨y, rfl⟩ := hf b
  have e : {a // f a = f y} ≃ f.ker :=
    { toFun := fun a => ⟨a.1 - y, by simp [AddMonoidHom.mem_ker, a.2]⟩
      invFun := fun k => ⟨k.1 + y, by
        have : f k.1 = 0 := k.2
        simp [this]⟩
      left_inv := fun a => by simp
      right_inv := fun k => by simp }
  have hi : f.ker.index = Nat.card B := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  rw [Nat.card_congr e, ← hi]
  exact AddSubgroup.card_mul_index f.ker

theorem card_fibre_gram_differential : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin m) (Fin n) E) (H : Matrix (Fin n) (Fin n) E), cT τ S = S → cT τ T = T → IsUnit T.det → cT τ x * S * x = T → cT τ H = H → Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} = q ^ (2 * m * n - n ^ 2) := by
  intro E _ τ q ε h m n hnm S T x H hS _ hT hx hH
  have hq : 0 < q := lt_trans Nat.zero_lt_one h.one_lt
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)
  have hM : Nat.card (Matrix (Fin m) (Fin n) E) = ((q ^ 2) ^ n) ^ m := by
    change Nat.card (Fin m → Fin n → E) = _
    rw [Nat.card_fun, Nat.card_fun, h.card]
    simp
  have hHerm : Nat.card (hermSub τ n) = q ^ (n ^ 2) := GlobalTheory.T.hermitian_matrices_card E τ q ε h n
  have hfib := card_fibre_mul (diffMap τ h.inv S hS x)
    (diffMap_surjective τ h S hS T x hT hx) ⟨H, hH⟩
  have hc : Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} =
      Nat.card {y // diffMap τ h.inv S hS x y = ⟨H, hH⟩} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [Subtype.ext_iff]
      rfl)
  have hle : n ^ 2 ≤ 2 * m * n := by nlinarith
  have hpow : ((q ^ 2) ^ n) ^ m = q ^ (n ^ 2) * q ^ (2 * m * n - n ^ 2) := by
    rw [← pow_add, Nat.add_sub_cancel' hle, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hc]
  rw [hHerm, hM, hpow, mul_comm] at hfib
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq _) hfib

end GlobalTheory.CompanionTheory.UnrDens.GramDiff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeVariablesZeroCountStatement
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.change_variables_zero_count : ∀ (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ) (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → A ⊆ U → MeasurableSet A → Measurable h → ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) = ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) * ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb | exact GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeightsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crossing_of_walls_and_heights : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.HtLip → PositivityTheory.RgEis.PiLocalization₂ → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Cross := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.cross | exact GlobalTheory.CompanionTheory.RgEisCross.cross | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.cross <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGalleryStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_induction_from_gallery : PositivityTheory.RgEis.Gallery → PositivityTheory.RgEis.Transfer → PositivityTheory.RgEis.Twist → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.LeviS → PositivityTheory.RgEis.LeviQ → PositivityTheory.RgEis.ConvGrOf → PositivityTheory.RgEis.ConvU → PositivityTheory.RgEis.SgStep := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.sgStep | exact GlobalTheory.CompanionTheory.RgEis.sgStep | (intros; apply GlobalTheory.CompanionTheory.RgEis.sgStep <;> assumption)
end

