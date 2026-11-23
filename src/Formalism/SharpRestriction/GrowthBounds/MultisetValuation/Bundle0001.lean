module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen

open Finset

def fac {σ : Type} (κ : σ →₀ ℕ) : ℕ := ∏ x ∈ κ.support, (κ x).factorial

def jp {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A) (f : MvPowerSeries σ K) : A :=
  ∑ κ ∈ P.support, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • AddMonoidAlgebra.coeff P κ

theorem jp_eq_sum {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A)
    (f : MvPowerSeries σ K) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jp P f = ∑ κ ∈ S, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • AddMonoidAlgebra.coeff P κ := by
  unfold jp
  refine Finset.sum_subset hS ?_
  intro κ _ hκ
  have h0 : AddMonoidAlgebra.coeff P κ = 0 := by simpa [MvPolynomial.mem_support_iff] using hκ
  rw [h0, smul_zero]

section Alg

variable {K Pl : Type} [CommRing K] {ι : Pl → Type}

def atP (v : Pl) (f : MvPowerSeries (ι v) K) : MvPowerSeries (Σ v, ι v) K :=
  MvPowerSeries.rename (Function.Embedding.sigmaMk v) f

variable [Fintype Pl]

abbrev eqv : ((Σ v, ι v) →₀ ℕ) ≃+ (∀ v, ι v →₀ ℕ) := Finsupp.sigmaFinsuppAddEquivPiFinsupp

variable [DecidableEq Pl]

theorem eqv_embDomain (v : Pl) (m : ι v →₀ ℕ) :
    eqv (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) = Pi.single v m := by
  funext w
  ext i
  rw [Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
  by_cases h : w = v
  · subst h
    rw [Pi.single_eq_same]
    exact Finsupp.embDomain_apply_self (Function.Embedding.sigmaMk w) m i
  · rw [Pi.single_eq_of_ne h, Finsupp.coe_zero, Pi.zero_apply, Finsupp.embDomain_notin_range]
    rintro ⟨j, hj⟩
    exact h (congrArg Sigma.fst hj).symm

theorem coeff_atP_single (v : Pl) (f : MvPowerSeries (ι v) K) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff (eqv.symm (Pi.single v m)) (atP v f) = MvPowerSeries.coeff m f := by
  have h : eqv.symm (Pi.single v m) = Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
    rw [AddEquiv.symm_apply_eq, eqv_embDomain]
  rw [h]
  exact MvPowerSeries.coeff_embDomain_rename _ _ _

theorem coeff_atP_eq_zero (v : Pl) (f : MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ)
    (h : ∀ m, n ≠ eqv.symm (Pi.single v m)) : MvPowerSeries.coeff n (atP v f) = 0 := by
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨u, hu⟩
  refine h u ?_
  rw [← hu, eq_comm, AddEquiv.symm_apply_eq, ← eqv_embDomain v u]
  exact congrArg eqv (Finsupp.embDomain_eq_mapDomain (Function.Embedding.sigmaMk v) u)

theorem coeff_prod_atP (g : ∀ v, MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPowerSeries.coeff n (∏ v, atP v (g v)) = ∏ v, MvPowerSeries.coeff (eqv n v) (g v) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  let l0 : Pl →₀ ((Σ v, ι v) →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm fun v => eqv.symm (Pi.single v (eqv n v))
  have hl0 : ∀ v, l0 v = eqv.symm (Pi.single v (eqv n v)) := fun v => rfl
  have hmem : l0 ∈ Finset.finsuppAntidiag Finset.univ n := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    calc ∑ v ∈ Finset.univ, l0 v = ∑ v, eqv.symm (Pi.single v (eqv n v)) :=
          Finset.sum_congr rfl fun v _ => hl0 v
      _ = n := by rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]
  rw [Finset.sum_eq_single_of_mem l0 hmem]
  · exact Finset.prod_congr rfl fun v _ => by rw [hl0]; exact coeff_atP_single v (g v) (eqv n v)
  · intro l hl hne
    rw [Finset.mem_finsuppAntidiag] at hl
    by_contra hprod
    apply hne
    have hall : ∀ v, ∃ m, l v = eqv.symm (Pi.single v m) := by
      intro v
      by_contra hv
      push_neg at hv
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ v) (coeff_atP_eq_zero v (g v) (l v) hv))
    choose m hm using hall
    have hn : n = eqv.symm m := by
      rw [← hl.1]
      calc ∑ v ∈ Finset.univ, l v = ∑ v, eqv.symm (Pi.single v (m v)) :=
            Finset.sum_congr rfl fun v _ => hm v
        _ = eqv.symm m := by rw [← map_sum, Finset.univ_sum_single]
    ext1 v
    rw [hm v, hl0, hn, AddEquiv.apply_symm_apply]

private theorem coe_rename_sigma_mk_eq_atP (v : Pl) (p : MvPolynomial (ι v) K) :
    ((MvPolynomial.rename (Sigma.mk v) p : MvPolynomial (Σ v, ι v) K) : MvPowerSeries (Σ v, ι v) K) =
      atP v (p : MvPowerSeries (ι v) K) := by
  ext d
  rw [MvPolynomial.coeff_coe]
  by_cases h : ∃ m, d = eqv.symm (Pi.single v m)
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_atP_single, MvPolynomial.coeff_coe]
    have h2 : eqv.symm (Pi.single v m) = Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
      rw [AddEquiv.symm_apply_eq, eqv_embDomain]
    rw [h2]
    exact MvPolynomial.coeff_rename_embDomain (Function.Embedding.sigmaMk v) p m
  · push_neg at h
    rw [coeff_atP_eq_zero v _ d h]
    apply MvPolynomial.coeff_rename_eq_zero
    intro u hu
    exfalso
    refine h u ?_
    rw [← hu, eq_comm, AddEquiv.symm_apply_eq, ← eqv_embDomain v u]
    exact congrArg eqv (Finsupp.embDomain_eq_mapDomain (Function.Embedding.sigmaMk v) u)

theorem coeff_prod_rename (P : ∀ v, MvPolynomial (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    AddMonoidAlgebra.coeff (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) n =
      ∏ v, AddMonoidAlgebra.coeff (P v) (eqv n v) := by
  have h1 : ((∏ v, MvPolynomial.rename (Sigma.mk v) (P v) : MvPolynomial (Σ v, ι v) K) :
      MvPowerSeries (Σ v, ι v) K) = ∏ v, atP v (P v : MvPowerSeries (ι v) K) := by
    rw [← Finset.prod_congr rfl fun v _ => coe_rename_sigma_mk_eq_atP v (P v)]
    exact map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (R := K)) _ _
  rw [← MvPolynomial.coeff_coe, h1, coeff_prod_atP]
  simp only [MvPolynomial.coeff_coe]

theorem fac_eq [∀ v, Fintype (ι v)] (n : (Σ v, ι v) →₀ ℕ) : fac n = ∏ v, fac (eqv n v) := by
  classical
  have h1 : ∀ {τ : Type} [Fintype τ] (m : τ →₀ ℕ), fac m = ∏ x, (m x).factorial := by
    intro τ _ m
    unfold fac
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have h0 : m x = 0 := by simpa using hx
    rw [h0, Nat.factorial_zero]
  rw [h1, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [h1]
  exact Finset.prod_congr rfl fun i _ => by rw [Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]

end Alg

theorem jp_prod {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] [Fintype Pl] [DecidableEq Pl] {ι : Pl → Type}
    [∀ v, Fintype (ι v)] (P : ∀ v, MvPolynomial (ι v) A) (g : ∀ v, MvPowerSeries (ι v) K) :
    jp (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) (∏ v, atP v (g v)) = ∏ v, jp (P v) (g v) := by
  classical
  have hsub : (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)).support ⊆
      (Fintype.piFinset fun v => (P v).support).image eqv.symm := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, coeff_prod_rename] at hn
    rw [Finset.mem_image]
    refine ⟨eqv n, ?_, AddEquiv.symm_apply_apply _ _⟩
    rw [Fintype.mem_piFinset]
    intro v
    rw [MvPolynomial.mem_support_iff]
    exact fun h0 => hn (Finset.prod_eq_zero (Finset.mem_univ v) h0)
  rw [jp_eq_sum _ _ _ hsub, Finset.sum_image (fun x _ y _ h => eqv.symm.injective h)]
  unfold jp
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_prod_atP, coeff_prod_rename, fac_eq]
  simp only [AddEquiv.apply_symm_apply, Algebra.smul_def, Nat.cast_prod, map_mul, map_prod,
    Finset.prod_mul_distrib]

end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore
section
namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem pivot {K κ : Type*} [Field K] (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (f : κ → K) (s : Finset κ) :
    (∃ k ∈ s, f k ≠ 0) → ∃ k0 ∈ s, f k0 ≠ 0 ∧ ∀ k ∈ s, f k / f k0 ∈ R := by
  classical
  induction s using Finset.induction_on with
  | empty => intro h; simp at h
  | insert a s ha ih =>
    intro h
    by_cases hs : ∃ k ∈ s, f k ≠ 0
    · obtain ⟨k0, hk0, hfk0, hR0⟩ := ih hs
      by_cases hfa : f a / f k0 ∈ R
      · refine ⟨k0, Finset.mem_insert_of_mem hk0, hfk0, ?_⟩
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hfa
        · exact hR0 k hk
      · have hinv : f k0 / f a ∈ R := by
          have := (hR (f a / f k0)).resolve_left hfa
          rwa [inv_div] at this
        have hfa0 : f a ≠ 0 := by
          intro h0; apply hfa; rw [h0, zero_div]; exact R.zero_mem
        refine ⟨a, Finset.mem_insert_self a s, hfa0, ?_⟩
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · rw [div_self hfa0]; exact R.one_mem
        · have : f k / f a = (f k / f k0) * (f k0 / f a) := by field_simp
          rw [this]; exact R.mul_mem (hR0 k hk) hinv
    · push_neg at hs
      have hfa0 : f a ≠ 0 := by
        obtain ⟨k, hk, hfk⟩ := h
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hfk
        · exact absurd (hs k hk) hfk
      refine ⟨a, Finset.mem_insert_self a s, hfa0, ?_⟩
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · rw [div_self hfa0]; exact R.one_mem
      · rw [hs k hk, zero_div]; exact R.zero_mem

private theorem coeff_mem_range_algebraMap_of_linearIndependent {K Kc V Vc M : Type*} [Field K] [Field Kc] [Algebra K Kc]
    [AddCommGroup V] [Module K V] [AddCommGroup Vc] [Module Kc Vc]
    (ι : V →+ Vc) (hιs : ∀ (c : K) (v : V), ι (c • v) = algebraMap K Kc c • ι v)
    (π : M → V →ₗ[K] K) (πc : M → Vc →ₗ[Kc] Kc) (hπ : ∀ m v, πc m (ι v) = algebraMap K Kc (π m v))
    (hsep : ∀ v : V, (∀ m, π m v = 0) → v = 0) {κ : Type*} (s : Finset κ) (z : κ → V)
    (hind : ∀ w : s → K, ∑ k : s, w k • z k = 0 → w = 0)
    (a : κ → Kc) (y : V) (hy : ι y = ∑ k ∈ s, a k • ι (z k)) (k0 : s) :
    a k0 ∈ Set.range (algebraMap K Kc) := by
  classical
  let T : (s → K) →ₗ[K] V :=
    { toFun := fun w => ∑ k : s, w k • z k
      map_add' := fun w w' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c w => by simp [Finset.smul_sum, smul_smul] }
  let φ : M → Module.Dual K (s → K) := fun m => (π m).comp T
  have hspan : Submodule.span K (Set.range φ) = ⊤ := by
    have h1 : (Submodule.span K (Set.range φ)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      have hT : T w = 0 := hsep _ (fun m => hw (φ m) (Submodule.subset_span ⟨m, rfl⟩))
      simpa using hind w hT
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K (Set.range φ))
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hmem : (LinearMap.proj k0 : (s → K) →ₗ[K] K) ∈ Submodule.span K (Set.range φ) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  have hz : ∀ k : s, (∑ m ∈ l.support, l m * π m (z k)) = if k = k0 then 1 else 0 := by
    intro k
    have h3 := congrArg (fun f : Module.Dual K (s → K) => f (Pi.single k 1)) hl
    have hT : ∀ m, φ m (Pi.single k 1) = π m (z k) := by
      intro m; simp [φ, T, Pi.single_apply, ite_smul]
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, hT, smul_eq_mul] at h3
    rw [h3, Pi.single_apply]
    simp [eq_comm]
  have hy' : ι y = ∑ k : s, a k • ι (z k) := by
    rw [hy]; exact (Finset.sum_coe_sort s (fun k => a k • ι (z k))).symm
  have e1 : ∀ m, algebraMap K Kc (π m y) = ∑ k : s, a k * algebraMap K Kc (π m (z k)) := by
    intro m; rw [← hπ, hy', map_sum]; simp [hπ]
  refine ⟨∑ m ∈ l.support, l m * π m y, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h4 : ∀ k : s, ∑ m ∈ l.support, algebraMap K Kc (l m) * (a k * algebraMap K Kc (π m (z k))) =
      a k * algebraMap K Kc (if k = k0 then 1 else 0) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hz k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]; ring
  rw [Finset.sum_congr rfl (fun k _ => h4 k)]
  simp

theorem descent_core {K Kc V Vc M : Type*} [Field K] [Field Kc] [Algebra K Kc]
    [AddCommGroup V] [Module K V] [AddCommGroup Vc] [Module Kc Vc]
    (ι : V →+ Vc) (hιs : ∀ (c : K) (v : V), ι (c • v) = algebraMap K Kc c • ι v)
    (π : M → V →ₗ[K] K) (πc : M → Vc →ₗ[Kc] Kc) (hπ : ∀ m v, πc m (ι v) = algebraMap K Kc (π m v))
    (hsep : ∀ v : V, (∀ m, π m v = 0) → v = 0)
    (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R)
    (A : AddSubgroup Kc) (hA : ∀ r ∈ R, ∀ a ∈ A, algebraMap K Kc r * a ∈ A) {κ : Type*} [DecidableEq κ] :
    ∀ (n : ℕ) (s : Finset κ), s.card = n → ∀ (z : κ → V) (a : κ → Kc), (∀ k ∈ s, a k ∈ A) → ∀ y : V,
      ι y = ∑ k ∈ s, a k • ι (z k) →
      ∃ c : κ → K, (∀ k ∈ s, algebraMap K Kc (c k) ∈ A) ∧ y = ∑ k ∈ s, c k • z k := by
  classical
  have hιinj : ∀ v : V, ι v = 0 → v = 0 := fun v hv => hsep v (fun m => by
    have h0 := hπ m v
    rw [hv, map_zero] at h0
    exact (algebraMap K Kc).injective (h0.symm.trans (map_zero _).symm))
  intro n
  induction n with
  | zero =>
    intro s hs z a _ y hy
    rw [Finset.card_eq_zero] at hs
    subst hs
    refine ⟨0, by simp, ?_⟩
    simp only [Finset.sum_empty] at hy ⊢
    exact hιinj y hy
  | succ n ih =>
    intro s hs z a ha y hy
    by_cases hdep : ∃ b : κ → K, ∑ k ∈ s, b k • z k = 0 ∧ ∃ k ∈ s, b k ≠ 0
    · obtain ⟨b, hb0, hbne⟩ := hdep
      obtain ⟨k0, hk0, hbk0, hbR⟩ := pivot R hR b s hbne
      have hzk0 : ι (z k0) = - ∑ k ∈ s.erase k0, algebraMap K Kc (b k / b k0) • ι (z k) := by
        have h1 : ∑ k ∈ s, (b k / b k0) • z k = 0 := by
          simp_rw [div_eq_mul_inv, mul_comm _ (b k0)⁻¹, mul_smul, ← Finset.smul_sum, hb0, smul_zero]
        rw [← Finset.add_sum_erase s _ hk0, div_self hbk0, one_smul] at h1
        set_option synthInstance.maxHeartbeats 100000 in
          rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_sum]
        simp only [hιs]
      have hy' : ι y = ∑ k ∈ s.erase k0,
          (a k - algebraMap K Kc (b k / b k0) * a k0) • ι (z k) := by
        rw [hy, ← Finset.add_sum_erase s _ hk0, hzk0, smul_neg, Finset.smul_sum,
          ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, sub_smul, mul_comm (a k0)]
        abel
      have hcard : (s.erase k0).card = n := by
        rw [Finset.card_erase_of_mem hk0, hs]; rfl
      obtain ⟨c, hcA, hyc⟩ := ih (s.erase k0) hcard z
        (fun k => a k - algebraMap K Kc (b k / b k0) * a k0)
        (fun k hk => A.sub_mem (ha k (Finset.mem_of_mem_erase hk))
          (hA _ (hbR k (Finset.mem_of_mem_erase hk)) _ (ha k0 hk0))) y hy'
      refine ⟨fun k => if k = k0 then 0 else c k, fun k hk => ?_, ?_⟩
      · by_cases hkk : k = k0
        · simp only [hkk, if_true, map_zero]; exact A.zero_mem
        · simp only [hkk, if_false]; exact hcA k (Finset.mem_erase.2 ⟨hkk, hk⟩)
      · rw [← Finset.add_sum_erase s _ hk0, hyc]
        simp only [if_true, zero_smul, zero_add]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [if_neg (Finset.ne_of_mem_erase hk)]
    · push_neg at hdep
      have hind : ∀ w : s → K, ∑ k : s, w k • z k = 0 → w = 0 := by
        intro w hw
        have h5 := hdep (fun k => if h : k ∈ s then w ⟨k, h⟩ else 0) (by
          rw [← Finset.sum_coe_sort]; simpa using hw)
        funext k
        simpa using h5 k k.2
      have hr : ∀ k (hk : k ∈ s), a k ∈ Set.range (algebraMap K Kc) := fun k hk =>
        coeff_mem_range_algebraMap_of_linearIndependent ι hιs π πc hπ hsep s z hind a y hy ⟨k, hk⟩
      let c : κ → K := fun k => if hk : k ∈ s then (hr k hk).choose else 0
      have hc : ∀ k ∈ s, algebraMap K Kc (c k) = a k := fun k hk => by
        simp only [c, dif_pos hk]; exact (hr k hk).choose_spec
      refine ⟨c, fun k hk => ?_, ?_⟩
      · rw [hc k hk]; exact ha k hk
      · have h6 : ι (y - ∑ k ∈ s, c k • z k) = 0 := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sub, map_sum, hy, sub_eq_zero]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hιs, hc k hk]
        exact sub_eq_zero.1 (hιinj _ h6)

end Formalism.MainNotions.FormalGroupSystem.Pf
end

