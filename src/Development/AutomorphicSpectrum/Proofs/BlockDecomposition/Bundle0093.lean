module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0079
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0037

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorGeneratedLift
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pq_baseChange : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K](S₁ : Type) [CommRing S₁] (i : S →ₐ[A] B) (I : Ideal S) (κ : K →+* S₁) (j : S →+* S₁) (i₁ : S₁ →+* B ⊗[A] K), Pf p A → Pf p K → PQ p (i : S →+* B) I → κ.comp (algebraMap A K) = j.comp (algebraMap A S) → Subring.closure (Set.range κ ∪ Set.range j) = ⊤ → (∀ a, i₁ (κ a) = (1 : B) ⊗ₜ[A] a) → (∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K)) → PQ p i₁ (I.map j) := by
  intro p _ A _ S _ _ B _ _ K _ _ S₁ _ i I κ j i₁ hA hK hQ hcomm hgen hκ hj
  have hT : Pf p (B ⊗[A] K) := GlobalTheory.T.perfect_tensor_product p A B K hA hQ.pf hK
  obtain ⟨-, hred, -, -, -⟩ := pf_facts p _ hT
  have hpS : (p : S₁) = 0 := by
    have h := congrArg κ hK.char
    simpa using h
  have addT : ∀ (k : ℕ) (a b : B ⊗[A] K), (a + b) ^ p ^ k = a ^ p ^ k + b ^ p ^ k := by
    intro k a b
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (B ⊗[A] K) hT.char k
    rw [← hF, ← hF, ← hF, map_add (f := _)]
  have hkill : ∀ x ∈ I.map j, i₁ x = 0 := by
    have hle : I.map j ≤ RingHom.ker i₁ := by
      refine Ideal.map_le_iff_le_comap.2 fun s hs => ?_
      have h0 : (i : S →+* B) s = 0 := (hQ.ker s).2 ⟨0, by simpa using hs⟩
      have h1 : i s = 0 := h0
      rw [Ideal.mem_comap, RingHom.mem_ker, hj, h1, TensorProduct.zero_tmul]
    exact fun x hx => hle hx
  refine ⟨hT, ?_, ?_⟩
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul b a =>
      obtain ⟨k, s, hs⟩ := hQ.pow b
      have hs' : b ^ p ^ k = i s := hs
      refine ⟨k, j s * κ (a ^ p ^ k), ?_⟩
      rw [map_mul, hj, hκ, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_pow, hs']
      simp
    | add y y' h h' =>
      obtain ⟨k, x, hx⟩ := h
      obtain ⟨k', x', hx'⟩ := h'
      refine ⟨k + k', x ^ p ^ k' + x' ^ p ^ k, ?_⟩
      rw [addT, map_add (f := _), map_pow, map_pow, ← hx, ← hx', ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
        Nat.add_comm k' k]
  · intro x
    constructor
    · intro hx
      obtain ⟨T', _, i', hQ'⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p S₁ (I.map j) hpS
      have hφ : ∀ s ∈ I, (i'.comp j) s = 0 := fun s hs =>
        (hQ'.ker (j s)).2 ⟨0, by simpa using Ideal.mem_map_of_mem j hs⟩
      obtain ⟨ψ, hψ, -⟩ := pq_lift p S B T' (i : S →+* B) I (i'.comp j) hQ hQ'.pf hφ
      have hψs : ∀ s, ψ (i s) = i' (j s) := fun s => by
        have h := RingHom.congr_fun hψ s
        simpa using h
      letI : Algebra A T' := ((i'.comp κ).comp (algebraMap A K)).toAlgebra
      have hal : ∀ a, algebraMap A T' a = i' (κ (algebraMap A K a)) := fun a => rfl
      let ψA : B →ₐ[A] T' :=
        { ψ with
          commutes' := fun a => by
            have h1 : algebraMap A B a = i (algebraMap A S a) := (i.commutes a).symm
            have h2 := RingHom.congr_fun hcomm a
            simp only [RingHom.comp_apply] at h2
            change ψ (algebraMap A B a) = _
            rw [h1, hψs, hal, h2] }
      let κA : K →ₐ[A] T' :=
        { i'.comp κ with
          commutes' := fun a => rfl }
      let ρ : B ⊗[A] K →ₐ[A] T' := Algebra.TensorProduct.productMap ψA κA
      have hρ : ((ρ : B ⊗[A] K →+* T').comp i₁) = i' := by
        refine RingHom.eq_of_eqOn_set_dense hgen ?_
        rintro y (⟨a, rfl⟩ | ⟨s, rfl⟩)
        · change ρ (i₁ (κ a)) = i' (κ a)
          rw [hκ]
          simp [ρ, κA]
        · change ρ (i₁ (j s)) = i' (j s)
          rw [hj]
          simp [ρ, ψA, hψs]
      have h0 : i' x = 0 := by
        rw [← hρ, RingHom.comp_apply, hx, map_zero]
      exact (hQ'.ker x).1 h0
    · rintro ⟨k, hk⟩
      have h := hkill _ hk
      rw [map_pow] at h
      exact hred _ _ h

end GlobalTheory.CompanionTheory.PerfectRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfEigencharacter
section
noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.SubEig

section Generic

variable {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]

def cyc (ρ : Representation ℂ G U) (u : U) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g : G => ρ g u)
  apply_mem_toSubmodule g v hv := by
    have hle : Submodule.span ℂ (Set.range fun g : G => ρ g u) ≤
        (Submodule.span ℂ (Set.range fun g : G => ρ g u)).comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact hle hv

theorem mem_cyc (ρ : Representation ℂ G U) (u : U) : u ∈ (cyc ρ u).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem exists_max_avoid (ρ : Representation ℂ G U) {u : U} (hu : u ≠ 0) :
    ∃ T : Subrepresentation ρ, u ∉ T.toSubmodule ∧
      ∀ T' : Subrepresentation ρ, T ≤ T' → u ∉ T'.toSubmodule → T' = T := by
  have hbot : (⊥ : Subrepresentation ρ) ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule} := by
    show u ∉ (⊥ : Submodule ℂ U)
    simpa using hu
  have hz : ∀ c ⊆ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hne : (Subrepresentation.toSubmodule '' c).Nonempty := ⟨_, y, hy, rfl⟩
    have hdir : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rcases hchain.total ha hb with h | h
      · exact ⟨_, ⟨b, hb, rfl⟩, h, le_rfl⟩
      · exact ⟨_, ⟨a, ha, rfl⟩, le_rfl, h⟩
    have hmem : ∀ x, x ∈ sSup (Subrepresentation.toSubmodule '' c) ↔
        ∃ a ∈ c, x ∈ Subrepresentation.toSubmodule a := by
      intro x
      rw [Submodule.mem_sSup_of_directed hne hdir]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, hx⟩
        exact ⟨a, ha, hx⟩
      · rintro ⟨a, ha, hx⟩
        exact ⟨_, ⟨a, ha, rfl⟩, hx⟩
    refine ⟨⟨sSup (Subrepresentation.toSubmodule '' c), ?_⟩, ?_, ?_⟩
    · intro g v hv
      obtain ⟨a, ha, hx⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a, ha, a.apply_mem_toSubmodule g hx⟩
    · intro h
      obtain ⟨a, ha, hx⟩ := (hmem u).1 h
      exact hc ha hx
    · intro z hz x hx
      exact (hmem x).2 ⟨z, hz, hx⟩
  obtain ⟨T, -, hT⟩ := zorn_le_nonempty₀ {T : Subrepresentation ρ | u ∉ T.toSubmodule} hz ⊥ hbot
  exact ⟨T, hT.prop, fun T' hle hu' => le_antisymm (hT.le_of_ge hu' hle) hle⟩

theorem cyc_gen (ρ : Representation ℂ G U) (u : U)
    (R : Subrepresentation (cyc ρ u).toRepresentation)
    (hR : (⟨u, mem_cyc ρ u⟩ : (cyc ρ u).toSubmodule) ∈ R.toSubmodule) : R = ⊤ := by
  have hle : (cyc ρ u).toSubmodule ≤ R.toSubmodule.map (cyc ρ u).toSubmodule.subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨_, R.apply_mem_toSubmodule g hR, rfl⟩
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem quot_irred (ρ : Representation ℂ G U) (T : Subrepresentation ρ) {u : U}
    (hu : u ∉ T.toSubmodule)
    (hmax : ∀ T' : Subrepresentation ρ, T ≤ T' → u ∉ T'.toSubmodule → T' = T)
    (hgen : ∀ R : Subrepresentation ρ, u ∈ R.toSubmodule → R = ⊤)
    (hst : ∀ g, T.toSubmodule ≤ T.toSubmodule.comap (ρ g)) :
    (ρ.quotient T.toSubmodule hst).IsIrreducible := by
  have hne : (Submodule.Quotient.mk u : U ⧸ T.toSubmodule) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hnt : Nontrivial (Subrepresentation (ρ.quotient T.toSubmodule hst)) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h1 : (Submodule.Quotient.mk u : U ⧸ T.toSubmodule) ∈
        (⊤ : Subrepresentation (ρ.quotient T.toSubmodule hst)).toSubmodule := trivial
    rw [← h] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  refine ⟨fun R => ?_⟩
  let T' : Subrepresentation ρ := ⟨R.toSubmodule.comap T.toSubmodule.mkQ, by
    intro g v hv
    have := R.apply_mem_toSubmodule g hv
    exact this⟩
  have hle : T ≤ T' := by
    intro x hx
    show T.toSubmodule.mkQ x ∈ R.toSubmodule
    have h0 : T.toSubmodule.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
    rw [h0]
    exact R.toSubmodule.zero_mem
  by_cases huT : u ∈ T'.toSubmodule
  · right
    have hT' := hgen T' huT
    refine le_antisymm le_top fun x _ => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : y ∈ T'.toSubmodule := by rw [hT']; trivial
    exact this
  · left
    have hT' := hmax T' hle huT
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ T'.toSubmodule := hx
    rw [hT'] at hy
    have : (Submodule.Quotient.mk y : U ⧸ T.toSubmodule) = 0 := by
      rwa [Submodule.Quotient.mk_eq_zero]
    rw [this]
    exact Submodule.zero_mem _

def mkI (ρ : Representation ℂ G U) (T : Submodule ℂ U) (hst : ∀ g, T ≤ T.comap (ρ g)) :
    Representation.IntertwiningMap ρ (ρ.quotient T hst) where
  toLinearMap := T.mkQ
  isIntertwining' g := by
    ext v
    rfl

def inclI {ρ : Representation ℂ G U} (S : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem smooth_sub {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro v
  have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : U) = v} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact hρ _

theorem smooth_quot {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (T : Submodule ℂ U)
    (hst : ∀ g, T ≤ T.comap (ρ g)) : IsSmooth (ρ.quotient T hst) :=
  _root_.UpperTheory.Reformulated.B.Gwb5.smooth_quot hρ T hst

end Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

end GlobalTheory.CompanionTheory.SubEig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPunitEqZero
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock.AmiExact

theorem pf_punit (p : ℕ) : Pf p PUnit :=
  ⟨Subsingleton.elim _ _, ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨b, Subsingleton.elim _ _⟩⟩⟩

theorem tensor_punit_eq_zero {A C : Type} [CommRing A] [AddCommGroup C] [Module A C]
    (w : C ⊗[A] PUnit) : w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => rfl
  | tmul c u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem almost_injective {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K₀ : Type) [CommRing K₀] [Algebra A K₀] (hK : Pf p K₀)
    (z : K₀) (hz : (1 : B) ⊗ₜ[A] z = 0) (k : ℕ) : r k • z = 0 := by
  have good : Good p r (0 : PUnit →ₗ[A] K₀) := by
    intro C _ _ _ w _ k
    exact ⟨0, (tensor_punit_eq_zero _).trans (tensor_punit_eq_zero _).symm⟩
  have h := hCov PUnit K₀ (pf_punit p) hK 0 good z
    ⟨0, by rw [map_zero, hz]⟩ k
  simpa using h

theorem ker_zero {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n)
    (hK : ∀ n, Pf p (K n)) (h0 : ∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z)
    (z : K 0) (hz : d 0 z = 0) (k : ℕ) : r k • z = 0 :=
  almost_injective hCov (K 0) (hK 0) z (by rw [← h0, hz, map_zero]) k

theorem exact_of_good {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n)
    (hK : ∀ n, Pf p (K n))
    (hS : ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z)
    (n : ℕ) (hG : Good p r (d n)) (z : K (n + 1)) (hz : d (n + 1) z = 0) (k : ℕ) :
    r k • z ∈ LinearMap.range (d n) :=
  hCov (K n) (K (n + 1)) (hK n) (hK (n + 1)) (d n) hG z
    ⟨H n z, by simpa [hz] using hS n z⟩ k

theorem lTensor_sq_zero {A C : Type} [CommRing A] [AddCommGroup C] [Module A C]
    {K : ℕ → Type} [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (dd : ∀ n z, d (n + 1) (d n z) = 0)
    (n : ℕ) (z : C ⊗[A] K n) : (d (n + 1)).lTensor C ((d n).lTensor C z) = 0 := by
  have h : d (n + 1) ∘ₗ d n = 0 := LinearMap.ext (dd n)
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

theorem exact_succ {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] {B : Type} [CommRing B]
    [Algebra A B] {r : ℕ → A} (hA : Pf p A) (hCov : Cov p r B) (n : ℕ) :
    ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
      (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n),
      (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) →
      ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧
        ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) →
      ∀ z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := by
  induction n with
  | zero =>
    intro K _ _ d H hK _ hH
    refine exact_of_good hCov K d H hK hH.2 0 ?_
    intro C _ _ hC w hw k
    obtain ⟨H₁, h0', _⟩ := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor A B C K d H hH
    have hz : r k • w = 0 :=
      ker_zero hCov (fun n => C ⊗[A] K n) (fun n => (d n).lTensor C) H₁
        (fun n => GlobalTheory.T.perfect_tensor_product p A C (K n) hA hC (hK n)) h0' w hw k
    rw [hz]
    exact zero_mem _
  | succ n ih =>
    intro K _ _ d H hK dd hH
    refine exact_of_good hCov K d H hK hH.2 (n + 1) ?_
    intro C _ _ hC w hw k
    obtain ⟨H₁, h0', hS'⟩ := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor A B C K d H hH
    obtain ⟨v, hv⟩ := ih (fun n => C ⊗[A] K n) (fun n => (d n).lTensor C) H₁
      (fun n => GlobalTheory.T.perfect_tensor_product p A C (K n) hA hC (hK n))
      (fun n z => lTensor_sq_zero d dd n z) ⟨h0', hS'⟩ w hw k
    refine ⟨((d n).codRestrict (LinearMap.ker (d (n + 1))) (fun z => dd n z)).lTensor C v, ?_⟩
    rw [← hv, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl

theorem exact_of_contraction :
    ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), Pf p A → Cov p r B → ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) → ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → (∀ z, d 0 z = 0 → ∀ k, r k • z = 0) ∧ ∀ n z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := by
  intro p _ A _ B _ _ r hA hCov K _ _ d H hK dd hH
  exact ⟨fun z hz k => ker_zero hCov K d H hK hH.1 z hz k,
    fun n z hz k => exact_succ hA hCov n K d H hK dd hH z hz k⟩

end GlobalTheory.CompanionTheory.Dblock.AmiExact
end

