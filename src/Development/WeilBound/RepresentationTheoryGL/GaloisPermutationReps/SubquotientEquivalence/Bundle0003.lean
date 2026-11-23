module

public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.HasCentralCharOfEquiv
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace CentralCharacterTransfer

theorem equiv_apply {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ (ρ g v) = σ g (φ v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  change (∀ h : H, ρ h v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro hv h hh
    exact hv ⟨h, hh⟩
  · intro hv h
    exact hv h h.2

theorem map_fixed {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (H : Subgroup G) :
    (fixed ρ H).map φ.toLinearEquiv.toLinearMap = fixed σ H := by
  ext w
  simp only [Submodule.mem_map, mem_fixed_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ h hh
    change σ h (φ v) = φ v
    rw [← equiv_apply, hv h hh]
  · intro hw
    have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
    refine ⟨φ.toLinearEquiv.symm w, fun h hh => ?_, e2⟩
    apply φ.toLinearEquiv.injective
    change φ _ = φ _
    rw [equiv_apply, e2, hw h hh]

theorem hasCentralChar_of_equiv {k V W : Type} [Field k] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv σ)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) : HasCentralChar σ ω := by
  intro z w
  have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
  rw [← e2, ← equiv_apply, h z]
  exact φ.toLinearEquiv.map_smul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem transfer {W W' V V' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
    {τ : Representation ℂ (GL (Fin n) 𝓀[k]) W} {τ' : Representation ℂ (GL (Fin n) 𝓀[k]) W'}
    {π : Representation ℂ (GL (Fin n) k) V} {π' : Representation ℂ (GL (Fin n) k) V'}
    {j : W →ₗ[ℂ] V} {j' : W' →ₗ[ℂ] V'} (hj : IsTypeMap τ π j) (hj' : IsTypeMap τ' π' j')
    (hf : fixed π (KOne k (Fin n)) = LinearMap.range j) (hf' : fixed π' (KOne k (Fin n)) = LinearMap.range j')
    (φ : π.Equiv π') : ∃ e : W ≃ₗ[ℂ] W', ∀ g v, e (τ g v) = τ' g (e v) := by
  have hm := map_fixed φ (KOne k (Fin n))
  rw [hf, hf'] at hm
  let e : W ≃ₗ[ℂ] W' := (LinearEquiv.ofInjective j hj.1).trans
    ((φ.toLinearEquiv.submoduleMap (LinearMap.range j)).trans
      ((LinearEquiv.ofEq _ _ hm).trans (LinearEquiv.ofInjective j' hj'.1).symm))
  have key : ∀ w, j' (e w) = φ (j w) := by
    intro w
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective j' hj'.1).apply_symm_apply
      ((LinearEquiv.ofEq _ _ hm) ((φ.toLinearEquiv.submoduleMap _) ((LinearEquiv.ofInjective j hj.1) w))))
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  refine ⟨e, fun g v => ?_⟩
  obtain ⟨g', rfl⟩ := GlobalTheory.LocGL.redK_surjective g
  apply hj'.1
  rw [key, hj.2, hj'.2, key]
  exact equiv_apply φ _ _

end CentralCharacterTransfer

open CentralCharacterTransfer in
theorem st8a : St4 → St5 → St6 → St7 → St8a := by
  classical
  intro h4 h5 h6 h7 k _ _ _ _ n hn ϖ hϖ c
  obtain ⟨τ, hτ, hinj⟩ := h7 𝓀[k] n hn
  have hdata : ∀ P ∈ Lab 𝓀[k] n, ∃ (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (j : (τ P).V →ₗ[ℂ] π.V),
      HasCentralChar π.ρ ω ∧ ω ϖ = c ∧ IsTypeMap (τ P).ρ π.ρ j :=
    fun P hP => h4 k (τ P).V n hn (τ P).ρ (hτ P hP).1 ϖ hϖ c
  choose π ω j hω hc hj using hdata
  have hirr : (1 : Representation ℂ (GL (Fin n) k) ℂ).IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun s => ?_ }
    · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)
    · rcases Ideal.eq_bot_or_top s.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  let d : IrrRep (GL (Fin n) k) := ⟨ℂ, 1, fun v => by simp, hirr⟩
  let F : 𝓀[k][X] → IrrGL (k := k) := fun P =>
    if hP : P ∈ Lab 𝓀[k] n then ⟨n, Quotient.mk _ (π P hP)⟩ else ⟨n, Quotient.mk _ d⟩
  have hF : ∀ P (hP : P ∈ Lab 𝓀[k] n), F P = ⟨n, Quotient.mk _ (π P hP)⟩ := by
    intro P hP
    simp only [F, dif_pos hP]
  have hfix : ∀ P (hP : P ∈ Lab 𝓀[k] n),
      fixed (π P hP).ρ (KOne k (Fin n)) = LinearMap.range (j P hP) := by
    intro P hP
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    exact h6 k (τ P).V n (τ P).ρ (hτ P hP).2 (π P hP) (ω P hP) (hω P hP) (j P hP) (hj P hP)
  refine ⟨F, fun P hP => ?_, fun P hP P' hP' hPP => ?_⟩
  · haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    rw [hF P hP]
    obtain ⟨ψ⟩ : Nonempty ((π P hP).ρ.Equiv
        (IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).ρ) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).symm
    set π₀ := IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))
    let j₀ : (τ P).V →ₗ[ℂ] π₀.V := ψ.toLinearEquiv.toLinearMap ∘ₗ j P hP
    have hj₀ : IsTypeMap (τ P).ρ π₀.ρ j₀ := by
      refine ⟨ψ.toLinearEquiv.injective.comp (hj P hP).1, fun g v => ?_⟩
      change ψ (j P hP _) = π₀.ρ g (ψ (j P hP v))
      rw [(hj P hP).2, equiv_apply]
    have hcc := hasCentralChar_of_equiv ψ (hω P hP)
    refine ⟨rfl, ⟨hn, h5 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ j₀ hj₀⟩, ?_, ω P hP, hcc, hc P hP⟩
    change fixed π₀.ρ (KOne k (Fin n)) ≠ ⊥
    rw [h6 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ (ω P hP) hcc j₀ hj₀]
    obtain ⟨w, hw⟩ := exists_ne (0 : (τ P).V)
    intro hb
    apply hw
    apply hj₀.1
    rw [map_zero]
    have hm : j₀ w ∈ LinearMap.range j₀ := LinearMap.mem_range_self j₀ w
    rw [hb] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · rw [hF P hP, hF P' hP'] at hPP
    have hq := eq_of_heq (Sigma.mk.inj_iff.1 hPP).2
    obtain ⟨φ⟩ : Nonempty ((π P hP).ρ.Equiv (π P' hP').ρ) := Quotient.exact hq
    obtain ⟨e, he⟩ := transfer (hj P hP) (hj P' hP') (hfix P hP) (hfix P' hP') φ
    exact hinj P hP P' hP' ⟨e, he⟩

end PositivityTheory.Rg.DzCount

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.LeviInductionForms
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace PositivityTheory.Rg.DzCount

namespace LeviInductionForms

theorem pow_eq_pow_iff_mod {M : Type*} [CommMonoid M] {ζ : M} {N : ℕ} (h : IsPrimitiveRoot ζ N)
    (hN : 0 < N) (a b : ℕ) : ζ ^ a = ζ ^ b ↔ a % N = b % N := by
  have e : ∀ c, ζ ^ c = ζ ^ (c % N) := fun c => by
    conv_lhs => rw [← Nat.mod_add_div c N]
    rw [pow_add, pow_mul, h.pow_eq_one, one_pow, mul_one]
  rw [e a, e b]
  exact ⟨fun H => h.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) H, fun H => by rw [H]⟩

theorem natDegree_minpoly_eq {K F : Type*} [Field K] [Finite K] [Field F] [Algebra K F] (n : ℕ)
    (hn : 0 < n) (w : F) (hw : IsIntegral K w) (h1 : w ^ (Nat.card K) ^ n = w)
    (h2 : ∀ d, 0 < d → d < n → w ^ (Nat.card K) ^ d ≠ w) : (minpoly K w).natDegree = n := by
  have hirr := minpoly.irreducible hw
  have hdvd : minpoly K w ∣ (X ^ (Nat.card K) ^ n - X : K[X]) := by
    apply minpoly.dvd
    simp [h1]
  have hd : (minpoly K w).natDegree ∣ n := hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  have hpos : 0 < (minpoly K w).natDegree := minpoly.natDegree_pos hw
  have hself : w ^ (Nat.card K) ^ (minpoly K w).natDegree = w := by
    obtain ⟨r, hr⟩ := (hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).1 (dvd_refl _)
    have h3 : Polynomial.aeval w (X ^ (Nat.card K) ^ (minpoly K w).natDegree - X : K[X]) = 0 := by
      rw [hr, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h3
  by_contra hne
  exact h2 _ hpos (lt_of_le_of_ne (Nat.le_of_dvd hn hd) hne) hself

theorem exists_eq_pow_of_aeval {K F : Type*} [Field K] [Fintype K] [Field F] [Algebra K F] (n : ℕ)
    (hn : 0 < n) (w w' : F) (hw : IsIntegral K w) (h1 : w ^ (Nat.card K) ^ n = w)
    (h2 : ∀ d, 0 < d → d < n → w ^ (Nat.card K) ^ d ≠ w)
    (hP : Polynomial.aeval w' (minpoly K w) = 0) : ∃ i : ℕ, w' = w ^ (Nat.card K) ^ i := by
  classical
  have hq : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hφ : ∀ (i : ℕ) (x : F), (FiniteField.frobeniusAlgHom K F ^ i) x = x ^ (Nat.card K) ^ i := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ, AlgHom.mul_apply, ih]
      show (x ^ Fintype.card K) ^ (Nat.card K) ^ i = _
      rw [hq, ← pow_mul, ← pow_succ']
  have hroot : ∀ i : ℕ, Polynomial.aeval (w ^ (Nat.card K) ^ i) (minpoly K w) = 0 := by
    intro i
    rw [← hφ, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hpw : ∀ a b : ℕ, (w ^ (Nat.card K) ^ a) ^ (Nat.card K) ^ b = w ^ (Nat.card K) ^ (a + b) := by
    intro a b
    rw [← pow_mul, ← pow_add]
  have hlt : ∀ i j : ℕ, i < j → j < n → w ^ (Nat.card K) ^ i ≠ w ^ (Nat.card K) ^ j := by
    intro i j hij hjn H
    have H2 := congrArg (fun x : F => x ^ (Nat.card K) ^ (n - j)) H
    simp only [hpw] at H2
    have e : j + (n - j) = n := by omega
    rw [e, h1] at H2
    exact h2 (i + (n - j)) (by omega) (by omega) H2
  have hinj : Set.InjOn (fun i : ℕ => w ^ (Nat.card K) ^ i) (Finset.range n : Set ℕ) := by
    intro i hi j hj H
    simp only [Finset.mem_coe, Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd H (hlt i j h hj)
    · exact h
    · exact absurd H.symm (hlt j i h hi)
  by_contra hno
  push_neg at hno
  set S := (Finset.range n).image (fun i : ℕ => w ^ (Nat.card K) ^ i) with hS
  have hcardS : S.card = n := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hw'S : w' ∉ S := by
    rw [hS, Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact hno i hi.symm
  have hP0 : minpoly K w ≠ 0 := minpoly.ne_zero hw
  have hmap0 : (minpoly K w).map (algebraMap K F) ≠ 0 := Polynomial.map_ne_zero hP0
  have hsub : (insert w' S).val ⊆ ((minpoly K w).map (algebraMap K F)).roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_insert] at hx
    rw [Polynomial.mem_roots hmap0, Polynomial.IsRoot.def, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    rcases hx with rfl | hx
    · exact hP
    · rw [hS, Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact hroot i
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_insert_of_notMem hw'S, hcardS, Polynomial.natDegree_map,
    natDegree_minpoly_eq n hn w hw h1 h2] at hcard
  omega

end LeviInductionForms

open LeviInductionForms in
theorem st3a : St3a := by
  unfold St3a
  intro K _ _ n hn
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hqn : 1 < Nat.card K ^ n := Nat.one_lt_pow hn.ne' hq1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Nat.card K ^ n - 1 := ⟨_, rfl⟩
  have hNq : Nat.card K ^ n = N + 1 := by omega
  have hNpos : 0 < N := by omega
  haveI : NeZero N := ⟨hNpos.ne'⟩
  haveI : NeZero ((N : ℕ) : K) := ⟨by
    have hc : ((Nat.card K : ℕ) : K) = 0 := by
      rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero K
    have h4 : ((Nat.card K ^ n : ℕ) : K) = (N : K) + 1 := by
      rw [hNq, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_pow, hc, zero_pow hn.ne'] at h4
    intro h0
    rw [h0, zero_add] at h4
    exact zero_ne_one h4⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) N
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hNpos.ne'⟩
  have htr : ∀ a b : ℕ, ζ ^ a = ζ ^ b ↔ ω ^ a = ω ^ b := by
    intro a b
    rw [pow_eq_pow_iff_mod hζ hNpos, pow_eq_pow_iff_mod hω hNpos]
  let jOf : ℂ → ℕ := fun z => if h : ∃ j : ℕ, ζ ^ j = z then h.choose else 0
  have hj : ∀ z : ℂ, ExactPer (Nat.card K) n z → ζ ^ jOf z = z := by
    intro z hz
    unfold ExactPer at hz
    obtain ⟨hz0, hz1, -⟩ := hz
    have hzN : z ^ N = 1 := by
      rw [hNq, pow_succ'] at hz1
      exact mul_right_injective₀ hz0 (hz1.trans (mul_one z).symm)
    have hex : ∃ j : ℕ, ζ ^ j = z := by
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hzN
      exact ⟨i, hi⟩
    simp only [jOf, dif_pos hex]
    exact hex.choose_spec
  have hint : ∀ x : AlgebraicClosure K, IsIntegral K x := fun x => Algebra.IsIntegral.isIntegral x
  have hper : ∀ (j m : ℕ), (ζ ^ j) ^ (Nat.card K) ^ m = ζ ^ j ↔
      (ω ^ j) ^ (Nat.card K) ^ m = ω ^ j := by
    intro j m
    rw [← pow_mul, ← pow_mul]
    exact htr _ _
  have hω0 : ω ≠ 0 := hω.ne_zero hNpos.ne'
  refine ⟨fun z => minpoly K (ω ^ jOf z), ?_, ?_⟩
  · intro z hz
    have hzj := hj z hz
    unfold ExactPer at hz
    obtain ⟨-, hz1, hz2⟩ := hz
    rw [← hzj] at hz1 hz2
    have hw1 : (ω ^ jOf z) ^ (Nat.card K) ^ n = ω ^ jOf z := (hper _ _).1 hz1
    have hw2 : ∀ d, 0 < d → d < n → (ω ^ jOf z) ^ (Nat.card K) ^ d ≠ ω ^ jOf z :=
      fun d hd hdn H => hz2 d hd hdn ((hper _ _).2 H)
    have hw := hint (ω ^ jOf z)
    show (minpoly K (ω ^ jOf z)).Monic ∧ Irreducible (minpoly K (ω ^ jOf z)) ∧
      minpoly K (ω ^ jOf z) ≠ X ∧ (minpoly K (ω ^ jOf z)).natDegree = n
    refine ⟨minpoly.monic hw, minpoly.irreducible hw, ?_, natDegree_minpoly_eq n hn _ hw hw1 hw2⟩
    intro hX
    have h0 := minpoly.aeval K (ω ^ jOf z)
    rw [hX, Polynomial.aeval_X] at h0
    exact pow_ne_zero _ hω0 h0
  · intro z z' hz hz' hlab
    have hzj := hj z hz
    have hzj' := hj z' hz'
    unfold ExactPer at hz
    obtain ⟨-, hz1, hz2⟩ := hz
    rw [← hzj] at hz1 hz2
    have hw1 : (ω ^ jOf z) ^ (Nat.card K) ^ n = ω ^ jOf z := (hper _ _).1 hz1
    have hw2 : ∀ d, 0 < d → d < n → (ω ^ jOf z) ^ (Nat.card K) ^ d ≠ ω ^ jOf z :=
      fun d hd hdn H => hz2 d hd hdn ((hper _ _).2 H)
    have hw := hint (ω ^ jOf z)
    have hP : Polynomial.aeval (ω ^ jOf z') (minpoly K (ω ^ jOf z)) = 0 := by
      have hlab' : minpoly K (ω ^ jOf z) = minpoly K (ω ^ jOf z') := hlab
      rw [hlab']
      exact minpoly.aeval K _
    obtain ⟨i, hi⟩ := exists_eq_pow_of_aeval n hn _ _ hw hw1 hw2 hP
    refine ⟨i, ?_⟩
    rw [← hzj', ← hzj, ← pow_mul, htr, pow_mul]
    exact hi

end PositivityTheory.Rg.DzCount

end
end

