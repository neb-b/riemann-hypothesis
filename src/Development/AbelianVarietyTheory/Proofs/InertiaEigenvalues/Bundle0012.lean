module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBilinCyclic
section
open Polynomial

namespace GlobalTheory.SimilarTranspose


open Polynomial in
theorem _root_.GlobalTheory.SimilarTranspose.exists_form {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ l : k[X] →ₗ[k] k, (∀ a, f ∣ a → l a = 0) ∧ ∀ a, (∀ b, l (a * b) = 0) → f ∣ a := by
  set g := f * C f.leadingCoeff⁻¹ with hg
  have hgm : g.Monic := monic_mul_leadingCoeff_inv hf
  have hdvd : ∀ a, f ∣ a ↔ g ∣ a := fun a =>
    (associated_mul_unit_right f _
      (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hf))))).dvd_iff_dvd_left
  let l : k[X] →ₗ[k] k := (lcoeff k (g.natDegree - 1)).comp (modByMonicHom g)
  refine ⟨l, fun a ha => ?_, fun a ha => ?_⟩
  · simp [l, (modByMonic_eq_zero_iff_dvd hgm).2 ((hdvd a).1 ha)]
  · rw [hdvd, ← modByMonic_eq_zero_iff_dvd hgm]
    by_contra hr
    have hg1 : g ≠ 1 := by
      rintro h
      apply hr
      rw [h, modByMonic_one]
    have hlt := natDegree_modByMonic_lt a hgm hg1
    set r := a %ₘ g with hrdef
    set m := g.natDegree - 1 - r.natDegree with hm
    have hsub : (a * X ^ m) %ₘ g = (r * X ^ m) %ₘ g := by
      apply modByMonic_eq_of_dvd_sub hgm
      refine ⟨(a /ₘ g) * X ^ m, ?_⟩
      have := modByMonic_add_div a g
      rw [hrdef]
      linear_combination -(X ^ m) * this
    have hdeg : (r * X ^ m).natDegree = g.natDegree - 1 := by
      rw [natDegree_mul_X_pow m hr]
      omega
    have hself : (r * X ^ m) %ₘ g = r * X ^ m := by
      rw [modByMonic_eq_self_iff hgm]
      apply degree_lt_degree
      omega
    have h := ha (X ^ m)
    simp only [l, LinearMap.comp_apply, modByMonicHom_apply, lcoeff_apply] at h
    rw [hsub, hself] at h
    have hidx : g.natDegree - 1 = r.natDegree + m := by omega
    rw [hidx, coeff_mul_X_pow] at h
    exact hr (leadingCoeff_eq_zero.1 h)

open Polynomial in
private theorem exists_nondegenerate_X_symmetric_form_quotient {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ G : (k[X] ⧸ (k[X] ∙ f)) →ₗ[k] (k[X] ⧸ (k[X] ∙ f)) →ₗ[k] k,
      (∀ x y, G ((X : k[X]) • x) y = G x ((X : k[X]) • y)) ∧ ∀ x, (∀ y, G x y = 0) → x = 0 := by
  obtain ⟨l, h1, h2⟩ := _root_.GlobalTheory.SimilarTranspose.exists_form f hf
  have hsurj := Submodule.Quotient.mk_surjective (k[X] ∙ f)
  let rep := Function.surjInv hsurj
  have hrep : ∀ x, Submodule.Quotient.mk (p := k[X] ∙ f) (rep x) = x := Function.surjInv_eq hsurj
  have hdiff : ∀ a a' : k[X], Submodule.Quotient.mk (p := k[X] ∙ f) a =
      Submodule.Quotient.mk (p := k[X] ∙ f) a' → f ∣ a - a' := by
    intro a a' h
    rw [Submodule.Quotient.eq, Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩
  let g : (k[X] ⧸ (k[X] ∙ f)) → (k[X] ⧸ (k[X] ∙ f)) → k := fun x y => l (rep x * rep y)
  have hg : ∀ a b, g (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = l (a * b) := by
    intro a b
    have ha := hdiff _ _ (hrep (Submodule.Quotient.mk a))
    have hb := hdiff _ _ (hrep (Submodule.Quotient.mk b))
    have : rep (Submodule.Quotient.mk a) * rep (Submodule.Quotient.mk b) - a * b =
        (rep (Submodule.Quotient.mk a) - a) * rep (Submodule.Quotient.mk b) +
          a * (rep (Submodule.Quotient.mk b) - b) := by ring
    have h0 := h1 _ (this ▸ dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _))
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  refine ⟨LinearMap.mk₂ k g ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hsurj z
    rw [← Submodule.Quotient.mk_add, hg, hg, hg, add_mul, map_add (f := _)]
  · intro c x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← Submodule.Quotient.mk_smul, hg, hg, smul_mul_assoc, map_smul]
  · intro x y z
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hsurj z
    rw [← Submodule.Quotient.mk_add, hg, hg, hg, mul_add, map_add (f := _)]
  · intro c x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← Submodule.Quotient.mk_smul, hg, hg, mul_smul_comm, map_smul]
  · intro x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    simp only [LinearMap.mk₂_apply]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hg, hg, smul_eq_mul,
      smul_eq_mul, mul_assoc, mul_left_comm]
  · intro x hx
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨c, hc⟩ := h2 a fun b => by
      have := hx (Submodule.Quotient.mk b)
      rw [LinearMap.mk₂_apply, hg] at this
      exact this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩

open Polynomial in
private theorem exists_nondegenerate_X_symmetric_form_torsion {k : Type} [Field k] {M : Type} [AddCommGroup M]
    [Module k[X] M] [Module k M] [IsScalarTower k k[X] M] [Module.Finite k[X] M]
    (hM : Module.IsTorsion k[X] M) :
    ∃ B : M →ₗ[k] M →ₗ[k] k, (∀ m n, B ((X : k[X]) • m) n = B m ((X : k[X]) • n)) ∧
      ∀ m, (∀ n, B m n = 0) → m = 0 := by
  classical
  obtain ⟨ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_directSum_of_isTorsion hM
  have hne : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
  choose G hGX hGn using fun i => exists_nondegenerate_X_symmetric_form_quotient (p i ^ e i) (hne i)
  let ψ : M →ₗ[k] (DirectSum ι fun i => k[X] ⧸ k[X] ∙ p i ^ e i) :=
    φ.toLinearMap.restrictScalars k
  have hψ : ∀ m, ψ m = φ m := fun m => rfl
  have happ : ∀ m n, (∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ)
      ((DirectSum.component k ι _ i).comp ψ)) m n = ∑ i, G i (φ m i) (φ n i) := by
    intro m n
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply, hψ]
    rfl
  refine ⟨∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ)
      ((DirectSum.component k ι _ i).comp ψ), ?_, ?_⟩
  · intro m n
    rw [happ, happ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, DirectSum.smul_apply, DirectSum.smul_apply, hGX]
  · intro m hm
    apply φ.injective
    rw [map_zero]
    refine DFinsupp.ext fun i => ?_
    apply hGn i
    intro y
    have h := hm (φ.symm (DirectSum.of _ i y))
    rw [happ, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji
      rw [DirectSum.of_eq_of_ne _ _ _ hji, map_zero]
    · simp


open Polynomial in
theorem _root_.GlobalTheory.SimilarTranspose.main : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P * A = A.transpose * P := by
  intro k ι _ _ _ A
  have hT := Module.AEval.isTorsion_of_finiteDimensional k (ι → k) (Matrix.toLin' A)
  obtain ⟨B, hBX, hBn⟩ := exists_nondegenerate_X_symmetric_form_torsion (M := Module.AEval' (Matrix.toLin' A)) hT
  let o := Module.AEval'.of (Matrix.toLin' A)
  let Q : (ι → k) →ₗ[k] (ι → k) →ₗ[k] k := B.compl₁₂ o.toLinearMap o.toLinearMap
  have hQ : Q.compl₁₂ (Matrix.toLin' A) LinearMap.id = Q.compl₁₂ LinearMap.id (Matrix.toLin' A) := by
    refine LinearMap.ext₂ fun v w => ?_
    simp only [Q, LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearEquiv.coe_coe, o]
    rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, hBX]
  have hQP : ∀ v w, Q v w = Matrix.vecMul v (LinearMap.toMatrix₂' k Q) ⬝ᵥ w := by
    intro v w
    rw [← Matrix.dotProduct_mulVec, ← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix']
  refine ⟨LinearMap.toMatrix₂' k Q, ?_, ?_⟩
  · rw [← Matrix.vecMul_injective_iff_isUnit]
    intro v w hvw
    have h0 : ∀ u, Q (v - w) u = 0 := by
      intro u
      rw [hQP, Matrix.sub_vecMul]
      simp only at hvw
      rw [hvw, sub_self, zero_dotProduct]
    have := hBn (o (v - w)) fun n => by
      have := h0 (o.symm n)
      simpa [Q] using this
    rw [map_eq_zero_iff _ o.injective, sub_eq_zero] at this
    exact this
  · have := congrArg (LinearMap.toMatrix₂' k) hQ
    rw [LinearMap.toMatrix₂'_compl₁₂, LinearMap.toMatrix₂'_compl₁₂] at this
    simpa [LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] using this.symm

end GlobalTheory.SimilarTranspose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCorestrictionCocycle
section
namespace GlobalTheory

open scoped BigOperators

theorem corCoc_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * g * q.out ∈ H := by
  have h : (QuotientGroup.mk (g • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have := QuotientGroup.eq.mp h
  simpa [mul_assoc] using this

theorem exists_corestriction_cocycle : ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X] (ρ : Representation R G X) (H : Subgroup G) [H.Normal] [H.FiniteIndex], IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → (∀ x, Continuous fun g => ρ g x) → ∀ f : G → X, ContinuousOn f H → (∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + ρ g (f h)) → ∃ F : G → X, Continuous F ∧ (∀ g h, F (g * h) = F g + ρ g (F h)) ∧ (∃ x, ∀ h ∈ H, F h = (∑ᶠ q : G ⧸ H, ρ q.out (f (q.out⁻¹ * h * q.out))) + (ρ h x - x)) ∧ ∀ (Y : Submodule R X), (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) → ∀ (f₀ : G → X) (x : X), (∀ g h, f₀ (g * h) - (f₀ g + ρ g (f₀ h)) ∈ Y) → (∀ h ∈ H, f h - f₀ h - (ρ h x - x) ∈ Y) → ∃ x', ∀ g, F g - H.index • f₀ g - (ρ g x' - x') ∈ Y := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ _ hH hρ _ f hf hc
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hmul : ∀ (a b : G) (x : X), ρ a (ρ b x) = ρ (a * b) x := by
    intro a b x
    rw [map_mul]; rfl
  refine ⟨fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)), ?_, ?_, ?_, ?_⟩
  · refine continuous_finsetSum _ fun q _ => ?_
    rw [continuous_iff_continuousAt]
    intro g₀
    have hk : Continuous fun g : G => (g₀ • q).out⁻¹ * g * q.out := by fun_prop
    have hn : ∀ᶠ g in nhds g₀, (g₀ • q).out⁻¹ * g * q.out ∈ H :=
      hk.continuousAt.preimage_mem_nhds (hH.mem_nhds (corCoc_mem H g₀ q))
    have h1 : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀ := by
      refine (hρ _).continuousAt.comp ?_
      exact ContinuousAt.comp (g := f) (hf.continuousAt (hH.mem_nhds (corCoc_mem H g₀ q)))
        hk.continuousAt
    refine h1.congr ?_
    filter_upwards [hn] with g hg
    have : g • q = g₀ • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' (g₀ • q)]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk (g₀ • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out)
      exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hg)
    rw [this]
  · intro g h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    rw [← Equiv.sum_comp (MulAction.toPerm h)
      (fun q : G ⧸ H => ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply, mul_smul]
    have e : (g • h • q).out⁻¹ * (g * h) * q.out =
        ((g • h • q).out⁻¹ * g * (h • q).out) * ((h • q).out⁻¹ * h * q.out) := by group
    rw [e, hc _ (corCoc_mem H g (h • q)) _ (corCoc_mem H h q), map_add (f := _), hmul, hmul]
    congr 3
    group
  · refine ⟨0, fun h hh => ?_⟩
    rw [finsum_eq_sum_of_fintype]
    simp only [map_zero, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : h • q = q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk q.out : G ⧸ H) = QuotientGroup.mk (h * q.out)
      refine QuotientGroup.eq.mpr ?_
      have := Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out
      simpa [mul_assoc] using this
    rw [this]
  · intro Y hY f₀ x h₀ hx
    refine ⟨∑ q : G ⧸ H, (f₀ q.out + ρ q.out x), fun g => ?_⟩
    have hidx : H.index • f₀ g = ∑ _q : G ⧸ H, f₀ g := by
      rw [Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    have hre : ∑ q : G ⧸ H, (f₀ q.out + ρ q.out x) =
        ∑ q : G ⧸ H, (f₀ (g • q).out + ρ (g • q).out x) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f₀ q.out + ρ q.out x)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hidx, map_sum, hre, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Y.sum_mem fun q _ => ?_
    set s' := (g • q).out
    set s := q.out
    have e : s' * (s'⁻¹ * g * s) = g * s := by group
    have a1 := hY s' _ (hx _ (corCoc_mem H g q))
    have a2 := h₀ s' (s'⁻¹ * g * s)
    have a3 := h₀ g s
    rw [e] at a2
    change ρ s' (f (s'⁻¹ * g * s) - f₀ (s'⁻¹ * g * s) - (ρ (s'⁻¹ * g * s) x - x)) ∈ Y at a1
    rw [map_sub, map_sub, map_sub, hmul, e] at a1
    have := Y.add_mem (Y.sub_mem a1 a2) a3
    convert this using 1
    rw [map_add (f := _), hmul]
    abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicI
section
open PowerSeries

namespace GlobalTheory

theorem padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (δ : ℤ_[l]) {n : ℕ} (hn : n ≠ 0) (hδ : δ ^ n = 1) (h1 : PadicInt.toZMod δ = 1) : δ = 1 := by
  have key : ∀ p : ℕ, p.Prime → ∀ ε : ℤ_[l], ε ^ p = 1 → PadicInt.toZMod ε = 1 → ε = 1 := by
    intro p hp ε hε he1
    by_contra hne
    have hsum : ∑ i ∈ Finset.range p, ε ^ i = 0 := by
      have := geom_sum_mul ε p
      rw [hε, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    have hp0 : (p : ZMod l) = 0 := by
      have := congrArg PadicInt.toZMod hsum
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_pow, he1] using this
    have hpl : l = p := (Nat.prime_dvd_prime_iff_eq hl.out hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp hp0)
    subst hpl
    have hmem : ∀ z : ℤ_[l], (l : ℤ_[l]) ∣ z ↔ PadicInt.toZMod z = 0 := by
      intro z
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton]
    have h := emultiplicity_geom_sum₂_eq_one (p := l) (x := ε) (y := 1) PadicInt.prime_p
      (hl.out.odd_of_ne_two h2) ((hmem _).mpr (by simp [he1])) (by rw [hmem, he1]; exact one_ne_zero)
    simp [hsum] at h
  induction n using Nat.recOnMul generalizing δ with
  | zero => exact absurd rfl hn
  | one => simpa using hδ
  | prime p hp => exact key p hp δ hδ h1
  | mul a b iha ihb =>
    have ha : a ≠ 0 := left_ne_zero_of_mul hn
    have hb : b ≠ 0 := right_ne_zero_of_mul hn
    refine iha δ ha (ihb (δ ^ a) hb (by rw [← pow_mul, hδ]) (by rw [map_pow, h1, one_pow])) h1

theorem exists_coset_representatives_of_finite_subgroup_padicInt_units {l : ℕ} [hl : Fact l.Prime]
    (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (h2 : l ≠ 2) :
    ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧
      (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧
      ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ,
        x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  classical
  let g : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom).comp Δ.subtype
  have hg : ∀ d : Δ, (g d : ZMod l) = PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) := fun _ => rfl
  have hs : Nat.card Δ ≠ 0 := Nat.card_pos.ne'
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by rw [← hg, hd]; rfl
    have hp : ((d : ℤ_[l]ˣ) : ℤ_[l]) ^ Nat.card Δ = 1 := by
      have : d ^ Nat.card Δ = 1 := pow_card_eq_one'
      have := congrArg (fun z : Δ => ((z : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using this
    exact Subtype.ext (Units.ext (padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hs hp h1))
  let H : Subgroup (ZMod l)ˣ := g.range
  have hH : Nat.card H = Nat.card Δ := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hHmem : ∀ x : (ZMod l)ˣ, x ^ Nat.card Δ = 1 → x ∈ H := by
    intro x hx
    have hle : H ≤ (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker := by
      intro y hy
      have : (⟨y, hy⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
      rw [hH] at this
      simpa using congrArg Subtype.val this
    have hc : Nat.card (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker ≤ Nat.card H := by
      rw [IsCyclic.card_powMonoidHom_ker, hH]
      exact Nat.gcd_le_right _ (Nat.pos_of_ne_zero hs)
    rw [Subgroup.eq_of_le_of_card_ge hle hc]
    simpa using hx
  let φ : ((ZMod l)ˣ ⧸ H) ≃ Fin (Nat.card ((ZMod l)ˣ ⧸ H)) := Finite.equivFin _
  let r : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) → (ZMod l)ˣ := fun τ => (φ.symm τ).out
  have hr : ∀ τ, ((r τ : (ZMod l)ˣ) : (ZMod l)ˣ ⧸ H) = φ.symm τ := fun τ => Quotient.out_eq _
  have hcast : ∀ τ, (((r τ : ZMod l).val : ℕ) : ZMod l) = r τ := fun τ => ZMod.natCast_zmod_val _
  have hreq : ∀ τ τ', (r τ)⁻¹ * r τ' ∈ H → τ = τ' := by
    intro τ τ' h
    have := QuotientGroup.eq.mpr h
    rw [hr, hr] at this
    exact φ.symm.injective this
  refine ⟨_, fun τ => (r τ : ZMod l).val, ?_, ?_, ?_, ?_⟩
  · rw [← hH, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card,
      ZMod.card_units]
  · intro τ h
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [hcast] at this
    exact (r τ).ne_zero this
  · intro τ τ' hne h
    simp only [hcast] at h
    have h' : r τ ^ Nat.card Δ = r τ' ^ Nat.card Δ := Units.ext (by simpa using h)
    exact hne (hreq _ _ (hHmem _ (by rw [mul_pow, inv_pow, h', inv_mul_cancel])))
  · intro x hx
    let u : (ZMod l)ˣ := Units.mk0 x hx
    have hu : (r (φ u))⁻¹ * u ∈ H := by
      rw [← QuotientGroup.eq, hr, Equiv.symm_apply_apply]
    obtain ⟨d, hd⟩ := hu
    have hform : ∀ p : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) × Δ,
        x = (((r p.1 : ZMod l).val : ℕ) : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) ↔
          u = r p.1 * g p.2 := by
      intro p
      rw [hcast, ← hg, Units.ext_iff]
      rfl
    have hd' : u = r (φ u) * g d := by rw [hd, mul_inv_cancel_left]
    refine ⟨(φ u, d), (hform _).mpr hd', ?_⟩
    rintro ⟨τ, d'⟩ hp
    have hp' : u = r τ * g d' := (hform _).mp hp
    have hτ : τ = φ u := by
      apply hreq
      refine ⟨d' * d⁻¹, ?_⟩
      rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hp', mul_inv_eq_iff_eq_mul]
      exact hd'
    rw [hτ] at hp'
    have : g d' = g d := mul_left_cancel (hp'.symm.trans hd')
    rw [hτ, hinj this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDenNotMemOfCountEqZero
section
open IsDedekindDomain

namespace GlobalTheory

theorem exists_den_not_mem_of_count_eq_zero {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (P : IsDedekindDomain.HeightOneSpectrum R)
    (I : FractionalIdeal (nonZeroDivisors R) K) (hI : FractionalIdeal.count K P I = 0)
    {a : K} (ha : a ∈ I) :
    ∃ b c : R, c ∉ P.asIdeal ∧ algebraMap R K c * a = algebraMap R K b := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp [ha0]⟩
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ I :=
    FractionalIdeal.spanSingleton_le_iff_mem.2 ha
  have hne : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0
  have hc : 0 ≤ FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) a) :=
    hI ▸ FractionalIdeal.count_mono K P hne hle
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap R K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ha0
  have hcoe : ∀ r : R, r ≠ 0 → FractionalIdeal.count K P
      (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K r)) =
      ((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) := by
    intro r hr
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K P]
    simpa using hr
  have hmul : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x / algebraMap R K y)
      * FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K y) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hyK]
  have hcnt := congrArg (FractionalIdeal.count K P) hmul
  rw [FractionalIdeal.count_mul K P hne (FractionalIdeal.spanSingleton_ne_zero_iff.2 hyK),
    hcoe x hx0, hcoe y hy0] at hcnt
  have hval : P.valuation K (algebraMap R K x / algebraMap R K y) ≤ 1 := by
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hx0,
      HeightOneSpectrum.intValuation_if_neg _ hy0, div_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero),
      WithZero.exp_le_exp]
    omega
  have hmem : algebraMap R K x / algebraMap R K y ∈ P.valuationSubringAtPrime K := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hval
  obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj P.asIdeal.primeCompl
    (⟨_, hmem⟩ : P.valuationSubringAtPrime K)
  refine ⟨b, c, c.2, ?_⟩
  have := congrArg (algebraMap (P.valuationSubringAtPrime K) K) hbc
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  rw [mul_comm]; exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivDvrFgModuleStructure
section
namespace GlobalTheory


open IsDiscreteValuationRing in
theorem dvr_fg_module_structure : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M], ∃ (n m : ℕ) (e : Fin m → ℕ),
    Nonempty (M ≃ₗ[O] (Fin n → O) × ((i : Fin m) → O ⧸ IsLocalRing.maximalIdeal O ^ e i)) := by
  intro O _ _ _ M _ _ _
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := O) (M := M)
  have hid : ∀ i, (Submodule.span O {p i ^ e i} : Submodule O O) =
      (IsLocalRing.maximalIdeal O ^ e i : Ideal O) := by
    intro i
    rw [(irreducible_iff_uniformizer _).1 (hp i), Ideal.span_singleton_pow]
  classical
  let σ := Fintype.equivFin ι
  refine ⟨n, Fintype.card ι, fun j => e (σ.symm j), ⟨?_⟩⟩
  exact f ≪≫ₗ LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite O O (Fin n))
    (DirectSum.linearEquivFunOnFintype O ι (fun i => O ⧸ O ∙ p i ^ e i) ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => Submodule.quotEquivOfEq _ _ (hid i)) ≪≫ₗ
      (LinearEquiv.piCongrLeft O (fun i : ι => O ⧸ IsLocalRing.maximalIdeal O ^ e i) σ.symm).symm)

end GlobalTheory
end

