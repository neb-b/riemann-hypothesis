module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUniformiserAbovePrime
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem exists_global_uniformiser_above_prime :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F], ∃ ϖ z : 𝓞 F,
      ϖ * z - (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ∧ (∃ n : ℕ, ϖ ^ n ∈ Ideal.span {(p : 𝓞 F)}) ∧
      IsReduced (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
  intro p hp F _ _
  set J : Ideal (𝓞 F) := (Ideal.span {(p : 𝓞 F)}).radical with hJdef
  have hp0 : (p : 𝓞 F) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := 𝓞 F)).mpr hp.out.ne_zero
  have hI0 : Ideal.span {(p : 𝓞 F) ^ 2} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hp0
  have hpJ : (p : 𝓞 F) ∈ J := Ideal.le_radical (Ideal.mem_span_singleton_self _)
  have hIJ : Ideal.span {(p : 𝓞 F) ^ 2} ≤ J := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact J.pow_mem_of_mem hpJ 2 two_pos
  obtain ⟨ϖ, hϖ⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
  have hϖJ : ϖ ∈ J := hϖ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine ⟨ϖ, ?_⟩

  have hp' : (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ⊔ Ideal.span {ϖ} := hϖ ▸ hpJ
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp'
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨z, ?_, hϖJ, ?_⟩
  · have : ϖ * z - (p : 𝓞 F) = -a := by rw [← hab]; ring
    rw [this]; exact neg_mem ha
  · have hK : Ideal.span {(p : 𝓞 F), ϖ} = J := by
      apply le_antisymm
      · rw [Ideal.span_le]
        intro x hx
        rcases hx with rfl | hx
        · exact hpJ
        · rw [Set.mem_singleton_iff] at hx; subst hx; exact hϖJ
      · rw [← hϖ]
        apply sup_le
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          rw [pow_two]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          exact Ideal.subset_span (by simp)
    rw [hK]
    exact (Ideal.isRadical_iff_quotient_reduced J).mp (Ideal.radical_isRadical _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfCompatible
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.AffineIdealGlue

variable {X : Scheme.{0}}

lemma res_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom s) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

def glueIdeal (𝒜 : Set X.affineOpens) (k : ∀ W : X.affineOpens, Ideal Γ(X, W))
    (V : X.affineOpens) : Ideal Γ(X, V) :=
  ⨅ W ∈ 𝒜, ⨅ h : W ≤ V, (k W).comap (X.presheaf.map (homOfLE h).op).hom

lemma mem_glueIdeal {𝒜 : Set X.affineOpens} {k : ∀ W : X.affineOpens, Ideal Γ(X, W)}
    {V : X.affineOpens} {s : Γ(X, V)} :
    s ∈ glueIdeal 𝒜 k V ↔
      ∀ W ∈ 𝒜, ∀ h : W ≤ V, (X.presheaf.map (homOfLE h).op).hom s ∈ k W := by
  simp [glueIdeal, Submodule.mem_iInf]

section
variable {𝒜 : Set X.affineOpens} {k : ∀ W : X.affineOpens, Ideal Γ(X, W)}
  (hk : ∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
    (k W).map (X.presheaf.map (homOfLE h).op).hom = k W')
include hk

lemma res_mem {W W' : X.affineOpens} (hW : W ∈ 𝒜) (h : W' ≤ W) {s : Γ(X, W)} (hs : s ∈ k W) :
    (X.presheaf.map (homOfLE h).op).hom s ∈ k W' := by
  rw [← hk W hW W' h]; exact Ideal.mem_map_of_mem _ hs

lemma glueIdeal_eq {V : X.affineOpens} (hV : V ∈ 𝒜) : glueIdeal 𝒜 k V = k V := by
  apply le_antisymm
  · intro s hs
    have := mem_glueIdeal.1 hs V hV le_rfl
    erw [X.presheaf.map_id] at this
    exact this
  · intro s hs
    exact mem_glueIdeal.2 fun W hW h => res_mem hk hV h hs

lemma exists_pow_mul_mem {B : X.affineOpens} (hB : B ∈ 𝒜) (g x : Γ(X, B))
    (hx : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom x ∈ k (X.affineBasicOpen g)) :
    ∃ n : ℕ, g ^ n * x ∈ k B := by
  haveI := B.2.isLocalization_basicOpen g
  rw [← hk B hB (X.affineBasicOpen g) (X.affineBasicOpen_le g)] at hx
  change algebraMap Γ(X, B) Γ(X, X.basicOpen g) x ∈
    Ideal.map (algebraMap Γ(X, B) Γ(X, X.basicOpen g)) (k B) at hx
  obtain ⟨_, ⟨n, rfl⟩, h⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g) Γ(X, X.basicOpen g) (k B) x).1 hx
  exact ⟨n, h⟩

lemma exists_pow_mul_mem_glueIdeal (h𝒜 : ∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜)
    (hcov : ∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) (U : X.affineOpens) (f a : Γ(X, U))
    (ha : ∀ W ∈ 𝒜, ∀ h : W.1 ≤ X.basicOpen f,
      (X.presheaf.map (homOfLE (h.trans (X.basicOpen_le f))).op).hom a ∈ k W) :
    ∃ m : ℕ, f ^ m * a ∈ glueIdeal 𝒜 k U := by
  classical
  have hloc : ∀ y : U.1, ∃ h : Γ(X, U), y.1 ∈ X.basicOpen h ∧ X.affineBasicOpen h ∈ 𝒜 ∧
      ∃ m : ℕ, (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (f ^ m * a) ∈
        k (X.affineBasicOpen h) := by
    intro y
    obtain ⟨W0, hW0, hyW0⟩ := hcov y.1
    obtain ⟨h, hhW0, hyh⟩ := U.2.exists_basicOpen_le (V := W0.1) ⟨y.1, hyW0⟩ y.2
    have hB : X.affineBasicOpen h ∈ 𝒜 := h𝒜 W0 hW0 _ hhW0
    refine ⟨h, hyh, hB, ?_⟩
    have hle : X.basicOpen ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom f) ≤
        X.basicOpen f := by
      rw [Scheme.basicOpen_res]; exact inf_le_right
    obtain ⟨m, hm⟩ := exists_pow_mul_mem hk hB
      ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom f)
      ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom a) (by
        have hmem := ha (X.affineBasicOpen _) (h𝒜 _ hB _ (X.affineBasicOpen_le _)) hle
        erw [res_res]; exact hmem)
    refine ⟨m, ?_⟩
    rw [map_mul, map_pow]; exact hm
  choose h hyh hB m hm using hloc
  obtain ⟨F, hF⟩ := U.2.isCompact.elim_finite_subcover (fun y => (X.basicOpen (h y) : Set X))
    (fun y => (X.basicOpen (h y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyh ⟨y, hy⟩⟩)
  have hspan : Ideal.span (h '' ↑F) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro z hz
    obtain ⟨y, hyF, hzy⟩ : ∃ y ∈ F, z ∈ X.basicOpen (h y) := by simpa using hF hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨h y, y, hyF, rfl⟩, hzy⟩
  refine ⟨∑ y ∈ F, m y, mem_glueIdeal.2 fun W hW hWU => ?_⟩
  set ρ := (X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op).hom with hρ
  have hspanW : Ideal.span (ρ '' (h '' ↑F)) = ⊤ := by
    rw [← Ideal.map_span, hspan, Ideal.map_top]
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (k W) _ hspanW _ ?_
  rintro ⟨_, _, ⟨y, hyF, rfl⟩, rfl⟩

  have hBy : (X.presheaf.map (homOfLE (X.basicOpen_le (h y))).op).hom
      (f ^ (∑ y ∈ F, m y) * a) ∈ k (X.affineBasicOpen (h y)) := by
    have hle : m y ≤ ∑ y ∈ F, m y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyF
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]
    exact Ideal.mul_mem_left _ _ (hm y)
  obtain ⟨n, hn⟩ := exists_pow_mul_mem hk hW (ρ (h y)) (ρ (f ^ (∑ y ∈ F, m y) * a)) (by
    have hle : (X.affineBasicOpen (ρ (h y))) ≤ X.affineBasicOpen (h y) := by
      change X.basicOpen (ρ (h y)) ≤ X.basicOpen (h y)
      rw [hρ, Scheme.basicOpen_res]; exact inf_le_right
    have := res_mem hk (hB y) hle hBy
    erw [res_res] at this
    rw [hρ]
    erw [res_res]
    exact this)
  exact ⟨n, hn⟩

lemma glueIdeal_basicOpen (h𝒜 : ∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜)
    (hcov : ∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) (U : X.affineOpens) (f : Γ(X, U)) :
    (glueIdeal 𝒜 k U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      glueIdeal 𝒜 k (X.affineBasicOpen f) := by
  haveI := U.2.isLocalization_basicOpen f
  have halg : ∀ y, algebraMap Γ(X, U) Γ(X, X.basicOpen f) y =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom y := fun _ => rfl
  apply le_antisymm
  · refine Ideal.map_le_of_le_comap ?_
    intro s hs
    have key : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom s ∈
        glueIdeal 𝒜 k (X.affineBasicOpen f) := by
      refine mem_glueIdeal.2 fun W hW hWf => ?_
      erw [res_res]
      exact mem_glueIdeal.1 hs W hW _
    exact key
  · intro t ht
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) t
    have hspec := IsLocalization.mk'_spec Γ(X, X.basicOpen f) a
      (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    simp only at hspec
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_glueIdeal hk h𝒜 hcov U f a (by
      intro W hW hWf
      have e := res_res (X.basicOpen_le f) hWf a
      rw [← e, ← halg, ← hspec, map_mul]
      exact Ideal.mul_mem_right _ _ (mem_glueIdeal.1 ht W hW hWf))
    show _ ∈ Ideal.map (algebraMap Γ(X, U) Γ(X, X.basicOpen f)) (glueIdeal 𝒜 k U)
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)]
    refine ⟨⟨⟨f ^ m * a, hm⟩, ⟨f ^ (m + n), m + n, rfl⟩⟩, ?_⟩
    simp only
    rw [pow_add, map_mul, map_mul]
    linear_combination (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ m)) * hspec

end

theorem exists_idealSheafData_of_compatible :
    ∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) →
      (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)),
      (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
        (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') →
      ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W := by
  intro X 𝒜 h𝒜 hcov k hk
  exact ⟨{ ideal := glueIdeal 𝒜 k, map_ideal_basicOpen := glueIdeal_basicOpen hk h𝒜 hcov },
    fun W hW => glueIdeal_eq hk hW⟩

end GlobalTheory.AffineIdealGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftAdicCompleteFreeAlgebra
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.IdemNewton

variable {A : Type} [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]

theorem mem_smul_top_iff_repr {ι : Type} [Fintype ι] (b : Module.Basis ι A Λ) (J : Ideal A) (z : Λ) :
    z ∈ J • (⊤ : Submodule A Λ) ↔ ∀ i, b.repr z i ∈ J := by
  constructor
  · intro hz i
    refine Submodule.smul_induction_on hz (fun r hr y _ => ?_) (fun y w hy hw => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · rw [map_add (f := _), Finsupp.add_apply]
      exact add_mem hy hw
  · intro h
    rw [← b.sum_repr z]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem mul_mem_right {J : Ideal A} {z : Λ} (y : Λ) (hz : z ∈ J • (⊤ : Submodule A Λ)) :
    z * y ∈ J • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [add_mul]
    exact add_mem hu hw

theorem mul_mem_left {J : Ideal A} {z : Λ} (y : Λ) (hz : z ∈ J • (⊤ : Submodule A Λ)) :
    y * z ∈ J • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [mul_add]
    exact add_mem hu hw

theorem mul_mem {J K : Ideal A} {z y : Λ} (hz : z ∈ J • (⊤ : Submodule A Λ))
    (hy : y ∈ K • (⊤ : Submodule A Λ)) : z * y ∈ (J * K) • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_mem_left w hy)
  · rw [add_mul]
    exact add_mem hu hw

theorem exists_idem : ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (Λ : Type) [Ring Λ]
    [Algebra A Λ] [Module.Free A Λ] [Module.Finite A Λ] (x : Λ),
    x * x - x ∈ I • (⊤ : Submodule A Λ) →
      ∃ e : Λ, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule A Λ) := by
  intro A _ I _ Λ _ _ _ _ x hx
  let b := Module.Free.chooseBasis A Λ
  have mono : ∀ {k m : ℕ}, k ≤ m → ∀ {z : Λ}, z ∈ (I ^ m) • (⊤ : Submodule A Λ) →
      z ∈ (I ^ k) • (⊤ : Submodule A Λ) := fun hkm _ hz =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hkm) hz
  let f : ℕ → Λ := fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k
  have f0 : f 0 = x := rfl
  have fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k) := fun k => rfl
  have h1 : ∀ k, (f k * f k - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k
    induction k with
    | zero => simpa [f0] using hx
    | succ k ih =>
      have e : f (k + 1) * f (k + 1) - f (k + 1) =
          ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3) := by
        rw [fs]; noncomm_ring
      rw [e]
      refine mul_mem_right _ ?_
      have := mul_mem ih ih
      rw [← pow_add] at this
      exact mono (by omega) this
  have h2 : ∀ k, (f (k + 1) - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k
    have e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k) := by
      rw [fs]; noncomm_ring
    rw [e]
    exact mul_mem_right _ (h1 k)
  have h3 : ∀ k m, k ≤ m → (f m - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k) := by abel
      rw [e]
      exact add_mem (mono (by omega) (h2 m)) ih
  have h4 : ∀ i, ∃ L : A, ∀ k, b.repr (f k) i - L ∈ I ^ k := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i) (fun {k m} hkm => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      have := (mem_smul_top_iff_repr b _ _).1 (mono (Nat.le_succ k) (h3 k m hkm)) i
      rwa [map_sub, Finsupp.sub_apply] at this)
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using h4
  let e : Λ := b.equivFun.symm L
  have he : ∀ i, b.repr e i = L i := fun i => by
    have := congrFun (b.equivFun.apply_symm_apply L) i
    rwa [Module.Basis.equivFun_apply] at this
  have hL' : ∀ k, (f k - e) ∈ (I ^ k) • (⊤ : Submodule A Λ) := fun k =>
    (mem_smul_top_iff_repr b _ _).2 fun i => by
      rw [map_sub, Finsupp.sub_apply, he]
      exact hL i k
  refine ⟨e, ?_, ?_⟩
  · change e * e = e
    rw [← sub_eq_zero]
    refine b.ext_elem fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    refine (mem_smul_top_iff_repr b _ _).1 ?_ i
    have e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e)) := by
      noncomm_ring
    rw [e1]
    exact sub_mem (mono (Nat.le_succ k) (h1 k))
      (add_mem (mul_mem_right _ (hL' k)) (mul_mem_left _ (hL' k)))
  · have e1 : e - x = (f 1 - f 0) - (f 1 - e) := by rw [f0]; abel
    rw [e1]
    have a := h2 0
    have c := hL' 1
    rw [zero_add, pow_one] at a
    rw [pow_one] at c
    exact sub_mem a c

end GlobalTheory.IdemNewton
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_idempotent_basicOpen_eq_of_isClopen :
    ∀ (X : Scheme.{0}) (U : Set X), IsClopen U →
      ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by
  intro X U hU
  let O : Bool → X.Opens := fun i => bif i then ⟨U, hU.isOpen⟩ else ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
  have hd : O true ⊓ O false = ⊥ := by
    ext x
    simp [O]
  have hcov : (⊤ : X.Opens) ≤ ⨆ i, O i := fun x _ => by
    by_cases hx : x ∈ U
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, hx⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, hx⟩
  let sf : ∀ i, Γ(X, O i) := fun i => bif i then 1 else 0
  have sub : ∀ T : X.Opens, T = ⊥ → Subsingleton Γ(X, T) := fun T hT => by
    subst hT; infer_instance
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 O sf := by
    intro i j
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' O ⊤ (fun i => homOfLE le_top) hcov sf hcompat
  obtain ⟨t, hs'⟩ : ∃ t : Γ(X, ⊤), ∀ i, X.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op t = sf i :=
    ⟨s, hs⟩
  clear hs s
  refine ⟨t, ?_, ?_⟩
  · refine X.sheaf.eq_of_locally_eq' O ⊤ (fun i => homOfLE le_top) hcov (t * t) t fun i => ?_
    have e1 : X.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op (t * t) = sf i * sf i := by
      rw [map_mul, hs' i]
    refine e1.trans (Eq.trans ?_ (hs' i).symm)
    cases i
    · exact mul_zero _
    · exact mul_one _
  · have h1 : O true ⊓ X.basicOpen t = O true := by
      rw [← Scheme.basicOpen_res, hs' true]
      exact X.basicOpen_of_isUnit isUnit_one
    have h0 : O false ⊓ X.basicOpen t = ⊥ := by
      rw [← Scheme.basicOpen_res, hs' false]
      exact X.basicOpen_zero _
    ext x
    constructor
    · intro hx
      by_contra hxU
      have : x ∈ O false ⊓ X.basicOpen t := ⟨hxU, hx⟩
      rw [h0] at this
      exact this
    · intro hx
      have : x ∈ O true := hx
      rw [← h1] at this
      exact this.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveNormLeOne
section
namespace GlobalTheory.InjectiveAlgebraMapTorsionFree

variable (p : ℕ) [Fact (Nat.Prime p)]

theorem algebraMap_injective_of_ne (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D]
    (hp : (p : D) ≠ 0) : Function.Injective (algebraMap ℤ_[p] D) := by
  by_contra hinj
  have hker : RingHom.ker (algebraMap ℤ_[p] D) ≠ ⊥ := fun h =>
    hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h)
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (algebraMap ℤ_[p] D) := by
    rw [hn]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact hp (pow_eq_zero_iff'.mp hmem).1

theorem isTorsionFree_of_injective {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Module.IsTorsionFree R S :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr h

theorem norm_algebraMap_le (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends]
  simpa using PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral (x : PadicAlgCl p) (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  haveI : IsUltrametricDist (PadicAlgCl p) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)
  by_contra h
  push_neg at h
  obtain ⟨q, hqm, hq⟩ := hx
  rw [hqm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hq
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq
  have hxn : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hq
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hn
  · rw [h0] at hxn
    simp at hxn
  have hx1 : 1 ≤ ‖x‖ := h.le
  have hle : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (q.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.mp hi
    calc ‖algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (q.natDegree - 1) :=
          mul_le_mul (norm_algebraMap_le p _) (pow_le_pow_right₀ hx1 (by omega))
            (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖x‖ ^ (q.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ q.natDegree ≤ ‖x‖ ^ (q.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (q.natDegree - 1) < ‖x‖ ^ q.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

theorem exists_injective_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (D : Type) [CommRing D]
    [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D] (hp : (p : D) ≠ 0) :
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d : D, ‖φ d‖ ≤ 1 := by
  have hM : Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
    apply algebraMap_injective_of_ne
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI := isTorsionFree_of_injective (algebraMap_injective_of_ne p D hp)
  haveI := isTorsionFree_of_injective hM
  let φ : D →ₐ[ℤ_[p]] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, ?_, fun d => ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap ℤ_[p] (PadicAlgCl p) a = 0 := by
      rw [← φ.commutes]; exact ha
    exact (map_eq_zero_iff _ hM).mp this
  · exact norm_le_one_of_isIntegral p _ ((Algebra.IsIntegral.isIntegral d).map φ)

end GlobalTheory.InjectiveAlgebraMapTorsionFree
end

