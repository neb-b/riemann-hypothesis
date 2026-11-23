module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentity
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.ArInt

namespace GlobalTheory.CompanionTheory.MixZ.PolarProof

theorem multilinear_eq_zero {V : Type} [AddCommGroup V] {N : ℕ}
    (M : (Fin N → V) →ₘₗ[ℤ] ℝ)
    (hs : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), M (a ∘ σ) = M a)
    (hd : ∀ x : V, M (fun _ => x) = 0) (a : Fin N → V) : M a = 0 := by
  classical
  have hsurj : ∀ f : Fin N → Fin N, Function.Surjective f → M (a ∘ f) = M a := fun f hf =>
    hs a (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hf, hf⟩)
  have expand : ∀ T : Finset (Fin N), M (fun _ => ∑ i, if i ∈ T then 0 else a i) =
      ∑ f : Fin N → Fin N, if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0 := by
    intro T
    set_option synthInstance.maxHeartbeats 100000 in
      rw [M.map_sum (fun _ i => if i ∈ T then 0 else a i)]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with h
    · congr 1
      funext j
      have : f j ∉ T := fun hj => Finset.mem_compl.1 (h hj) (Finset.mem_image_of_mem f (Finset.mem_univ j))
      simp [this]
    · obtain ⟨t, ht, hc⟩ := Finset.not_subset.1 h
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.notMem_compl.1 hc)
      exact M.map_coord_zero j (if_pos ht)
  have hinner : ∀ f : Fin N → Fin N, ∑ T : Finset (Fin N), (-1 : ℝ) ^ T.card *
      (if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0) =
      if Function.Surjective f then M a else 0 := by
    intro f
    have h1 : ∑ T : Finset (Fin N), (-1 : ℝ) ^ T.card *
        (if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0) =
        (∑ T ∈ ((Finset.univ.image f)ᶜ).powerset, (-1 : ℝ) ^ T.card) * M (a ∘ f) := by
      rw [Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun T : Finset (Fin N) => T ⊆ (Finset.univ.image f)ᶜ)]
      have h2 : Finset.univ.filter (fun T : Finset (Fin N) => T ⊆ (Finset.univ.image f)ᶜ) =
          ((Finset.univ.image f)ᶜ).powerset := by
        ext T; simp
      rw [h2, Finset.sum_eq_zero (s := Finset.univ.filter _) (fun T hT => by
        rw [if_neg (Finset.mem_filter.1 hT).2, mul_zero]), add_zero]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [if_pos (Finset.mem_powerset.1 hT)]
    have h3 : (∑ T ∈ ((Finset.univ.image f)ᶜ).powerset, (-1 : ℝ) ^ T.card) =
        if (Finset.univ.image f)ᶜ = ∅ then 1 else 0 := by
      have := congrArg (Int.cast : ℤ → ℝ)
        (Finset.sum_powerset_neg_one_pow_card (x := (Finset.univ.image f)ᶜ))
      push_cast at this
      exact this
    have h4 : (Finset.univ.image f)ᶜ = ∅ ↔ Function.Surjective f := by
      rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
      simp [Function.Surjective]
    rw [h1, h3]
    by_cases h : Function.Surjective f
    · rw [if_pos (h4.2 h), if_pos h, one_mul, hsurj f h]
    · rw [if_neg (fun e => h (h4.1 e)), if_neg h, zero_mul]
  have htot : ∑ f : Fin N → Fin N, (if Function.Surjective f then M a else 0) = 0 := by
    simp only [← hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun T _ => ?_
    rw [← Finset.mul_sum, ← expand, hd, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at htot
  rcases mul_eq_zero.1 htot with h | h
  · have hc : (Finset.univ.filter fun f : Fin N → Fin N => Function.Surjective f).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨id, by simp [Function.surjective_id]⟩
    exact absurd (by exact_mod_cast h) hc
  · exact h

theorem eq_of_diag {V : Type} [AddCommGroup V] {N : ℕ} (S T : (Fin N → V) → ℝ)
    (hS : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), S (a ∘ σ) = S a)
    (hT : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), T (a ∘ σ) = T a)
    (aS : ∀ (a : Fin N → V) (j : Fin N) (b c : V), S (Function.update a j (b + c)) =
      S (Function.update a j b) + S (Function.update a j c))
    (aT : ∀ (a : Fin N → V) (j : Fin N) (b c : V), T (Function.update a j (b + c)) =
      T (Function.update a j b) + T (Function.update a j c))
    (hd : ∀ x : V, S (fun _ => x) = T (fun _ => x)) (a : Fin N → V) : S a = T a := by
  have aG : ∀ (a : Fin N → V) (j : Fin N) (b c : V),
      (S - T) (Function.update a j (b + c)) =
        (S - T) (Function.update a j b) + (S - T) (Function.update a j c) := by
    intro a j b c
    simp only [Pi.sub_apply, aS, aT]
    ring
  let M : (Fin N → V) →ₘₗ[ℤ] ℝ :=
    { toFun := S - T
      map_update_add' := by
        intro inst m j b c
        rw [Subsingleton.elim inst (fun a b => instDecidableEqFin N a b)]
        exact aG m j b c
      map_update_smul' := by
        intro inst m j c x
        obtain rfl : inst = (fun a b => instDecidableEqFin N a b) := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun y => (S - T) (Function.update m j y)) (aG m j)) c x }
  have h := multilinear_eq_zero M
    (fun a σ => by
      change (S - T) (a ∘ σ) = (S - T) a
      simp only [Pi.sub_apply, hS, hT])
    (fun x => by
      change (S - T) (fun _ => x) = 0
      simp only [Pi.sub_apply, hd, sub_self]) a
  have h' : (S - T) a = 0 := h
  exact sub_eq_zero.1 h'

section Line

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hermLine_ext {A B : HermLine ι} (h₁ : A.a = B.a) (h₂ : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

theorem combLine_add {κ : Type} [Fintype κ] (A : κ → HermLine ι) (a b : κ → ℤ) :
    combLine A (a + b) = (combLine A a).tensor (combLine A b) := by
  refine hermLine_ext ?_ ?_
  · simp only [combLine, HermLine.tensor, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · funext z
    simp only [combLine, HermLine.tensor]
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · rw [if_pos hz, if_pos hz, if_pos hz, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun o _ => zpow_add₀ ((A o).pos z hz).ne' _ _
    · rw [if_neg hz, if_neg hz, if_neg hz, mul_zero]

theorem combLine_elim_zero {κ : Type} [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι) (n : κ → ℤ) :
    combLine (fun o : Option κ => o.elim A₀ A) (fun o => o.elim 0 n) = combLine A n := by
  refine hermLine_ext ?_ ?_
  · simp [combLine, Fintype.sum_option]
  · funext z
    simp [combLine, Fintype.prod_option]

theorem combLine_elim_one {κ : Type} [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι)
    (c₀ : ∀ z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A₀.h z = 0) :
    combLine (fun o : Option κ => o.elim A₀ A) (fun o => o.elim 1 fun _ => 0) = A₀ := by
  refine hermLine_ext ?_ ?_
  · simp [combLine, Fintype.sum_option]
  · funext z
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · simp only [combLine]
      rw [if_pos hz]
      simp [Fintype.prod_option]
    · simp only [combLine]
      rw [if_neg hz, c₀ z hz]

end Line

section Lin

variable {κ : Type} [Fintype κ]

theorem lin_add (a b : κ → ℤ) : lin (fun o => ((a + b) o : ℝ)) = lin (fun o => (a o : ℝ)) + lin (fun o => (b o : ℝ)) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem lin_elim_zero (n : κ → ℤ) :
    lin (fun o : Option κ => (((o.elim 0 n : ℤ)) : ℝ)) = rename some (lin fun i => (n i : ℝ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin, Fintype.sum_option, map_sum, rename_X]

theorem lin_elim_one :
    lin (fun o : Option κ => (((o.elim 1 fun _ => 0 : ℤ)) : ℝ)) = MvPolynomial.X none := by
  simp [lin, Fintype.sum_option]

end Lin

theorem polar : Polar := by
  classical
  intro K _ ι _ F D κ _ A₀ A s₀ sA c₀ cA hsym hadd Φ hΦ n
  let A' : Option κ → HermLine ι := fun o => o.elim A₀ A
  have sA' : ∀ o, IsSmoothHerm (A' o) := by
    rintro (_ | j)
    exacts [s₀, sA j]
  have sC : ∀ a, IsSmoothHerm (combLine A' a) := isSmoothHerm_combLine sA'
  let l : (Option κ → ℤ) → MvPolynomial (Option κ) ℝ := fun a => lin fun o => (a o : ℝ)
  let S : (Fin (D + 1) → Option κ → ℤ) → ℝ := fun a => Φ (∏ j, l (a j))
  let T : (Fin (D + 1) → Option κ → ℤ) → ℝ := fun a => F (D + 1) fun j => combLine A' (a j)
  have hST : ∀ a, S a = T a := by
    refine eq_of_diag S T ?_ ?_ ?_ ?_ ?_
    · intro a σ
      change Φ (∏ j, l (a (σ j))) = Φ (∏ j, l (a j))
      rw [Equiv.prod_comp σ fun j => l (a j)]
    · intro a σ
      exact hsym (fun j => combLine A' (a j)) σ fun j => sC _
    · intro a j b c
      change Φ (∏ i, l (Function.update a j (b + c) i)) =
        Φ (∏ i, l (Function.update a j b i)) + Φ (∏ i, l (Function.update a j c i))
      have e : ∀ x : Option κ → ℤ, ∏ i, l (Function.update a j x i) =
          l x * ∏ i ∈ Finset.univ \ {j}, l (a i) := by
        intro x
        have := Finset.prod_update_of_mem (Finset.mem_univ j) (fun i => l (a i)) (l x)
        rw [← this]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      rw [e, e, e, ← map_add (f := _), ← add_mul]
      congr 2
      exact lin_add b c
    · intro a j b c
      have e : ∀ x : Option κ → ℤ, T (Function.update a j x) =
          F (D + 1) (Function.update (fun i => combLine A' (a i)) j (combLine A' x)) := by
        intro x
        change F (D + 1) (fun i => combLine A' (Function.update a j x i)) = _
        congr 1
        funext i
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      rw [e, e, e, combLine_add]
      exact hadd _ j _ _ (fun _ => sC _) (sC _) (sC _)
    · intro x
      change Φ (∏ _j : Fin (D + 1), l x) = F (D + 1) fun _ => combLine A' x
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact hΦ x
  have key := hST (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0)
  have eS : S (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0) =
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) := by
    change Φ _ = _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h₁ := lin_elim_zero n
    have h₂ := lin_elim_one (κ := κ)
    simp only [l]
    rw [h₁, h₂, mul_comm]
  have eT : T (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0) =
      F (D + 1) (Fin.snoc (fun _ : Fin D => combLine A n) A₀) := by
    change F (D + 1) _ = _
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact combLine_elim_one A₀ A c₀
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact combLine_elim_zero A₀ A n
  rw [← eS, key, eT]

end GlobalTheory.CompanionTheory.MixZ.PolarProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WordProd.OneBlockProd

theorem exists_equiv_tensor {α : Type} [Fintype α] [DecidableEq α] (X : α → Type) [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (i₀ : α) (hx : ∀ i, i ≠ i₀ → ∃ v : X i, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w) :
    ∃ (x : ∀ i, X i) (ι : X i₀ ≃ₗ[ℂ] ⨂[ℂ] i, X i),
      ∀ v, ι v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := by
  have hx' : ∀ i, ∃ (x : X i) (c : Module.Dual ℂ (X i)), i ≠ i₀ → c x = 1 ∧ ∀ w, c w • x = w := by
    intro i
    by_cases hi : i = i₀
    · exact ⟨0, 0, fun h => absurd hi h⟩
    · obtain ⟨v, hv, hs⟩ := hx i hi
      obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (X i), f v ≠ 0 := by
        by_contra h
        push Not at h
        exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
      refine ⟨v, (f v)⁻¹ • f, fun _ => ⟨by simp [hf], fun w => ?_⟩⟩
      obtain ⟨a, rfl⟩ := hs w
      simp [hf, mul_comm]
  choose x c hc using hx'
  let T : X i₀ →ₗ[ℂ] ⨂[ℂ] i, X i := (PiTensorProduct.tprod ℂ).toLinearMap x i₀
  have hT : ∀ v, T v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := fun v => rfl
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun v hv => ?_
    refine (Module.forall_dual_apply_eq_zero_iff ℂ v).1 fun l => ?_
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap
      (Function.update c i₀ l))) hv
    rw [hT, PiTensorProduct.lift.tprod, map_zero] at h1
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
    rw [Finset.prod_eq_single_of_mem i₀ (Finset.mem_univ _) (fun i _ hi => by
      rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact (hc i hi).1)] at h1
    simpa using h1
  have hsurj : Function.Surjective T := by
    intro y
    refine PiTensorProduct.induction_on y (fun r f => ?_) (fun y z hy hz => ?_)
    · let d : α → ℂ := fun i => if h : i = i₀ then 1 else c i (f i)
      have e1 : f = fun i => d i • Function.update x i₀ (f i₀) i := by
        funext i
        by_cases h : i₀ = i
        · subst h
          simp [d]
        · have h' : i ≠ i₀ := fun e => h e.symm
          simp only [d, dif_neg h', Function.update_of_ne h']
          exact ((hc i h').2 (f i)).symm
      have e2 : PiTensorProduct.tprod ℂ f =
          (∏ i, d i) • PiTensorProduct.tprod ℂ (Function.update x i₀ (f i₀)) := by
        calc
          _ = PiTensorProduct.tprod ℂ (fun i => d i • Function.update x i₀ (f i₀) i) := congrArg _ e1
          _ = _ := by simpa using (PiTensorProduct.tprod ℂ).map_smul_univ d (Function.update x i₀ (f i₀))
      exact ⟨r • (∏ i, d i) • f i₀, by rw [map_smul, map_smul, hT, e2]⟩
    · obtain ⟨u, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := hz
      exact ⟨u + v, map_add _ _ _⟩
  exact ⟨x, LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hirr : π.IsIrreducible) : ∃ v : V, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w := by
  have hg : ∀ g : G, g = 1 := fun g => Subsingleton.elim _ _
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊥ : Subrepresentation π) = ⊤ := by
      ext v; rw [h v]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by simpa [hg g] using hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  refine ⟨v, hv, fun w => ?_⟩
  have : w ∈ S := by rw [hS]; trivial
  exact Submodule.mem_span_singleton.1 this

theorem exists_conj_perm {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (e : n ≃ n) :
    ∃ w : GL n R, ∀ y : GL n R,
      ((w * y * w⁻¹ : GL n R) : Matrix n n R) = (y : Matrix n n R).submatrix e e := by
  let P : Matrix n n R := (1 : Matrix n n R).submatrix e (Equiv.refl n)
  let Q : Matrix n n R := (1 : Matrix n n R).submatrix (Equiv.refl n) e
  have hP : ∀ y : Matrix n n R, P * y = y.submatrix e (Equiv.refl n) := fun y => by
    ext s t
    simp [P, Matrix.mul_apply, Matrix.one_apply]
  have hQ : ∀ y : Matrix n n R, y * Q = y.submatrix (Equiv.refl n) e := fun y => by
    ext s t
    simp [Q, Matrix.mul_apply, Matrix.one_apply]
  have h1 : P * Q = 1 := by
    rw [hQ]
    ext s t
    simp [P, Matrix.one_apply]
  have h2 : Q * P = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨P, Q, h1, h2⟩, fun y => ?_⟩
  show P * (y : Matrix n n R) * Q = _
  rw [hQ, hP]
  rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_parInd {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W}
    {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (hP : ∀ g : GL n k, g ∈ parab k e)
    (hd : ∀ z, deltaHalf k m z = 1) (L : V ≃ₗ[ℂ] W)
    (law0 : ∀ (p : parab k e) v, ρ (leviProj k e p) (L v) = L (π p v)) :
    Nonempty (π.Equiv (parInd e ρ)) := by
  have law : ∀ (p : parab k e) v, twist ρ (deltaHalf k m) (leviProj k e p) (L v) = L (π p v) := fun p v => by
    simp only [twist_apply, hd, Units.val_one, one_smul, law0]
  let f : π.IntertwiningMap (parInd e ρ) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          refine Eq.trans ?_ (law p _).symm
          simp⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          simp [hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        simp)) }
  refine ⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩⟩
  · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) h
    simpa using h1
  · have h1 := φ.1.2 ⟨x, hP x⟩ 1
    rw [mul_one] at h1
    refine (law ⟨x, hP x⟩ _).symm.trans ?_
    rw [L.apply_symm_apply]
    exact h1.symm

theorem multiProd_single {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α)
    (h0 : ∀ i, i ≠ i₀ → b i = 0) (σ : ∀ i, IrrRep (GL (Fin (b i)) k))
    (g : (Σ i, Fin (b i)) ≃ Fin (b i₀)) :
    Nonempty ((multiProd g fun i => (σ i).ρ).Equiv (σ i₀).ρ) := by
  have hP : ∀ x : GL (Fin (b i₀)) k, x ∈ parab k g := fun x =>
    OneBlockCell.mem_parab_of_single g i₀ h0 x
  have hsub : ∀ i, i ≠ i₀ → Subsingleton (GL (Fin (b i)) k) := by
    intro i hi
    haveI : IsEmpty (Fin (b i)) := by rw [h0 i hi]; infer_instance
    exact ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨x, ι, hι⟩ := exists_equiv_tensor (fun i => (σ i).V) i₀ (fun i hi =>
    haveI := hsub i hi
    exists_line (σ i).ρ (σ i).irr)
  let E : Fin (b i₀) ≃ Fin (b i₀) := (OneBlockCell.valEquiv i₀ rfl h0).symm.trans g
  obtain ⟨w, hw⟩ := exists_conj_perm (R := k) E
  have hwp : ∀ p : parab k g, leviProj k g p i₀ = w * (p : GL (Fin (b i₀)) k) * w⁻¹ := fun p =>
    Units.ext (Matrix.ext fun s t => by
      rw [hw]
      rfl)
  let A : (σ i₀).V ≃ₗ[ℂ] (σ i₀).V := LinearEquiv.ofLinear ((σ i₀).ρ w) ((σ i₀).ρ w⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  obtain ⟨φ⟩ := nonempty_equiv_parInd (ρ := piTensor fun i => (σ i).ρ) (π := (σ i₀).ρ) g (σ i₀).smooth hP
    (OneBlockCell.deltaHalf_eq_one_of_single i₀ h0) (A.trans ι) (fun p v => by
      show (piTensor fun i => (σ i).ρ) (leviProj k g p) (ι ((σ i₀).ρ w v)) = ι ((σ i₀).ρ w ((σ i₀).ρ p v))
      rw [hι, hι, piTensor_tprod]
      refine congrArg _ (funext fun i => ?_)
      rw [Function.apply_update (fun i u => (σ i).ρ (leviProj k g p i) u)]
      by_cases h : i₀ = i
      · subst h
        rw [Function.update_self, Function.update_self, hwp, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel_right, map_mul, Module.End.mul_apply]
      · have h' : i ≠ i₀ := fun e => h e.symm
        haveI := hsub i h'
        rw [Function.update_of_ne h', Function.update_of_ne h',
          Subsingleton.elim (leviProj k g p i) 1, map_one]
        rfl)
  exact ⟨φ.symm⟩

theorem multiProd_clOf_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : IrrGL (k := k)) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α), b i₀ = a.1 → (∀ i, i ≠ i₀ → b i = 0) → ∀ (g : (Σ i, Fin (b i)) ≃ Fin a.1), Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) := by
  intro k _ _ _ _ a α _ _ b i₀ hb h0 g
  obtain ⟨N, c⟩ := a
  dsimp only at hb g ⊢
  subst hb
  obtain ⟨φ⟩ := multiProd_single b i₀ h0 (fun i => (clOf ⟨b i₀, c⟩ (b i)).rep) g
  have key : ∀ d : IrrCl (GL (Fin (b i₀)) k), d = c → Nonempty (d.rep.ρ.Equiv c.rep.ρ) := by
    rintro _ rfl
    exact ⟨.refl _⟩
  obtain ⟨ψ⟩ := key _ (clOf_self ⟨b i₀, c⟩)
  exact ⟨φ.trans ψ⟩

end GlobalTheory.CompanionTheory.WordProd.OneBlockProd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairEmbedding
section
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairEmb_of_steps : PairSlices → PairStep₁ → PairStep₂ → PairEmb := by
  intro hS h₁ h₂ E _ _ _ a b ι _ K₁ K₂ W₁ W₂ X₁ Y₁ X₂ Y₂ G hW₁ hW₂ hX₁ hX₂ hE₁ hE₂ hG hGp hGt
  obtain ⟨e₁, he₁Y, he₁i, he₁q⟩ := hE₁
  obtain ⟨e₂, he₂Y, he₂i, he₂q⟩ := hE₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hi
  obtain ⟨hmem, hval⟩ := (hS E a b X₁ X₂ (G i) (hGp i)).1 x.2
  have hφ : sl₁ (G i) x.2 ≠ 0 := by
    intro h0
    apply hx
    have h := congrFun hval x.1
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₁, p₁, t₁, c₁⟩ := h₁ E a b ι K₁ K₂ W₁ W₂ X₁ Y₁ X₂ e₁ G hW₁ hW₂ hX₁ he₁q he₁Y hGp hGt
    ⟨i, x.2, sl₁ (G i) x.2, hval, fun h0 => hφ (he₁i _ hmem h0)⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp n₁
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hj
  obtain ⟨hmem₂, hval₂⟩ := (hS E a b Y₁ X₂ (ap₁ e₁ (G j)) (p₁ j)).2 y.1
  have hψ : sl₂ (ap₁ e₁ (G j)) y.1 ≠ 0 := by
    intro h0
    apply hy
    have h := congrFun hval₂ y.2
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₂, p₂, t₂, c₂⟩ := h₂ E a b ι K₁ K₂ W₁ W₂ Y₁ X₂ Y₂ e₂ (fun i => ap₁ e₁ (G i)) hW₁ hW₂ hX₂ he₂q he₂Y p₁ t₁
    ⟨j, y.1, sl₂ (ap₁ e₁ (G j)) y.1, hval₂, fun h0 => hψ (he₂i _ hmem₂ h0)⟩
  exact ⟨fun i => ap₂ e₂ (ap₁ e₁ (G i)), n₂, p₂, t₂, fun h c hc => c₂ h c (c₁ h c hc)⟩

end GlobalTheory.CompanionTheory.EGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalElementIntegralAlmostAllStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_element_integral_almost_all : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E), ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually | exact GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually | (intros; apply GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually <;> assumption)
end

