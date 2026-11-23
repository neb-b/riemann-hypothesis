module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartFree
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_intertwiner_decomp_of_kernel_intertwines {σ O : Type} [Fintype σ] [CommRing O] (g : MvPowerSeries σ O)
    (hg : constantCoeff g = 0) :
    ∃ h : σ → MvPowerSeries σ O, g = ∑ i, monomial (Finsupp.single i 1) 1 * h i ∧
      ∀ i, constantCoeff (h i) = coeff (Finsupp.single i 1) g := by
  classical
  let sel : (σ →₀ ℕ) → Option σ := fun n =>
    if hn : n.support.Nonempty then some hn.choose else none
  let H : σ → MvPowerSeries σ O := fun i k =>
    if sel (k + Finsupp.single i 1) = some i then coeff (k + Finsupp.single i 1) g else 0
  have hc : ∀ i m, coeff m (H i) =
      if sel (m + Finsupp.single i 1) = some i then coeff (m + Finsupp.single i 1) g else 0 :=
    fun _ _ => rfl
  refine ⟨H, ?_, ?_⟩
  · ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [coeff_monomial_mul, one_mul]
    by_cases hn : n.support.Nonempty
    · have hi0 : hn.choose ∈ n.support := hn.choose_spec
      have hsel : sel n = some hn.choose := dif_pos hn
      have hle0 : Finsupp.single hn.choose 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi0)
      rw [Finset.sum_eq_single hn.choose]
      · rw [if_pos hle0, hc, tsub_add_cancel_of_le hle0, if_pos hsel]
      · intro i _ hi
        by_cases hle : Finsupp.single i 1 ≤ n
        · rw [if_pos hle, hc, tsub_add_cancel_of_le hle, if_neg]
          rw [hsel]
          intro heq
          exact hi (Option.some_injective _ heq).symm
        · rw [if_neg hle]
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    · have hn0 : n = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hn
        exact hn
      subst hn0
      rw [Finset.sum_eq_zero]
      · rw [coeff_zero_eq_constantCoeff_apply]
        exact hg
      · intro i _
        rw [if_neg]
        intro hle
        have h1 := Finsupp.single_le_iff.1 hle
        simp at h1
  · intro i
    rw [← coeff_zero_eq_constantCoeff_apply, hc, zero_add, if_pos]
    have hn : (Finsupp.single i 1 : σ →₀ ℕ).support.Nonempty := ⟨i, by simp⟩
    show (if hn : (Finsupp.single i 1 : σ →₀ ℕ).support.Nonempty then some hn.choose else none) = some i
    rw [dif_pos hn]
    have hs : hn.choose ∈ ({i} : Finset σ) := by
      rw [← Finsupp.support_single_ne_zero i (one_ne_zero : (1 : ℕ) ≠ 0)]
      exact hn.choose_spec
    rw [Finset.mem_singleton.1 hs]

private lemma π_mem_sq {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    (W : WPres O X R) (h : W.HasOrigin) (f : MvPowerSeries W.σ O) (h0 : constantCoeff f = 0)
    (h1 : ∀ i, coeff (Finsupp.single i 1) f = 0) : W.π f ∈ RingHom.ker (W.origin h) ^ 2 := by
  classical
  obtain ⟨g, hf, hg⟩ := exists_intertwiner_decomp_of_kernel_intertwines f h0
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i => (hg i).trans (h1 i)
  choose k hk _ using fun i => exists_intertwiner_decomp_of_kernel_intertwines (g i) (hg0 i)
  have hz : ∀ i, W.π (monomial (Finsupp.single i 1) 1) ∈ RingHom.ker (W.origin h) := by
    intro i
    rw [RingHom.mem_ker]
    erw [WPres.origin_π]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]
    exact (Finsupp.single_ne_zero.2 one_ne_zero).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hk i, Finset.mul_sum, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [← mul_assoc, map_mul, map_mul, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (hz i) (hz j))

theorem UpperTheory.V.Alg.chart_free :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin), Function.Injective W.π → ∃ φ : R →ₐ[O] MvPowerSeries W.σ (FractionRing O), IsChart W.part (W.origin h) W.wt φ ∧ ∀ s, φ (W.z s) = MvPowerSeries.X s := by
  intro O X R _ _ _ _ _ _ W h hinj
  classical
  let e : MvPowerSeries W.σ O ≃ₐ[O] R := AlgEquiv.ofBijective W.π ⟨hinj, W.surj⟩
  let μ : MvPowerSeries W.σ O →ₐ[O] MvPowerSeries W.σ (FractionRing O) :=
    { MvPowerSeries.map (algebraMap O (FractionRing O)) with
      commutes' := fun r => by
        ext n
        simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C] }
  let φ : R →ₐ[O] MvPowerSeries W.σ (FractionRing O) := μ.comp e.symm.toAlgHom
  have hφ : ∀ g, φ (W.π g) = MvPowerSeries.map (algebraMap O (FractionRing O)) g := by
    intro g
    show μ (e.symm (e g)) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨φ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j f hf
    have hf' : f ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j) := hf
    obtain ⟨g, hg, rfl⟩ := hf'
    have hg' : ∀ n, Finsupp.weight W.wt n ≠ j → coeff n g = 0 := hg
    show ∀ n, Finsupp.weight W.wt n ≠ j → coeff n (φ (W.π g)) = 0
    intro n hn
    rw [hφ, MvPowerSeries.coeff_map, hg' n hn, map_zero]
  · intro f
    obtain ⟨g, rfl⟩ := W.surj f
    rw [hφ, WPres.origin_π, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map]
  · intro i
    refine ⟨W.π (MvPowerSeries.X i), ?_, ?_⟩
    · rw [hφ, MvPowerSeries.map_X, MvPowerSeries.coeff_X, if_pos rfl]
      exact one_ne_zero
    · intro i' hi'
      rw [hφ, MvPowerSeries.map_X, MvPowerSeries.coeff_X, if_neg]
      intro heq
      exact hi' (Finsupp.single_left_injective one_ne_zero heq)
  · intro f hf0 hlin
    obtain ⟨g, rfl⟩ := W.surj f
    unfold satSq
    show ∃ c : O, c ≠ 0 ∧ c • W.π g ∈ RingHom.ker (W.origin h) ^ 2
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul]
    apply π_mem_sq W h g
    · rw [← WPres.origin_π W h]
      exact hf0
    · intro i
      have hi := hlin i
      rw [hφ, MvPowerSeries.coeff_map] at hi
      exact IsFractionRing.injective O (FractionRing O) (hi.trans (map_zero _).symm)
  · intro s
    show φ (W.π (MvPowerSeries.X s)) = MvPowerSeries.X s
    rw [hφ, MvPowerSeries.map_X]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartKer
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private lemma prod_pow_mem {S σ : Type} [CommRing S] (I : Ideal S) (z : σ → S) (hz : ∀ i, z i ∈ I)
    (m : σ →₀ ℕ) {n : ℕ} (hn : n ≤ m.degree) : (m.prod fun i k => z i ^ k) ∈ I ^ n := by
  refine Ideal.pow_le_pow_right hn ?_
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

private lemma order_of_mem {K τ : Type} [CommRing K] (n : ℕ) :
    ∀ g ∈ RingHom.ker (constantCoeff : MvPowerSeries τ K →+* K) ^ n, (n : ℕ∞) ≤ g.order := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
    · refine le_trans ?_ le_order_mul
      push_cast
      exact add_le_add (ih a ha) (one_le_order_iff_constCoeff_eq_zero.2 hb)
    · intro a b ha hb
      exact le_trans (le_min ha hb) min_order_le_add

private lemma coeff_map_zero {O K σ τ : Type} [CommRing O] [CommRing K] [Algebra O K] [Fintype σ]
    (ψ : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ K)
    (hψ : ∀ i, constantCoeff (ψ (MvPowerSeries.X i)) = 0) (N : ℕ) (f : MvPowerSeries σ O)
    (hf : ∀ m : σ →₀ ℕ, m.degree < N → coeff m f = 0) (n : τ →₀ ℕ) (hn : n.degree < N) :
    coeff n (ψ f) = 0 := by
  classical
  have key : ∃ μ : Finset (σ →₀ ℕ), (μ : Set _) ⊆ {m : σ →₀ ℕ | N ≤ m.degree} ∧
      ∀ f : MvPowerSeries σ O, (∀ m, m ∉ {m : σ →₀ ℕ | N ≤ m.degree} → coeff m f = 0) →
      ∃ b : (σ →₀ ℕ) → MvPowerSeries σ O, (∀ m, b m ∈ wtPart O (fun _ : σ => (0 : ℤ)) 0) ∧
        f = ∑ m ∈ μ, b m * monomial m 1 :=
    part_span O (MvPowerSeries σ O) ℤ (WPres.free O fun _ : σ => (0 : ℤ))
      {m : σ →₀ ℕ | N ≤ m.degree} 0 (fun (m : σ →₀ ℕ) _ => by
        show Finsupp.weight (fun _ : σ => (0 : ℤ)) m = 0
        simp [Finsupp.weight_apply, Finsupp.sum])
  obtain ⟨μ, hμ, hs⟩ := key
  obtain ⟨b, -, hb⟩ := hs f (fun m hm => hf m (not_le.1 hm))
  have h1 : ψ f ∈ RingHom.ker (constantCoeff : MvPowerSeries τ K →+* K) ^ N := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hb, map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hπ : ψ (monomial m 1) = m.prod fun i k => ψ (MvPowerSeries.X i) ^ k := by
      rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
      simp
    rw [map_mul, hπ]
    exact Ideal.mul_mem_left _ _ (prod_pow_mem _ _ hψ m (hμ hm))
  refine coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem N _ h1))
  exact_mod_cast hn

private lemma homog_ker {O K σ τ X : Type} [CommRing O] [CommRing K] [Algebra O K] [Fintype σ] [AddCommGroup X]
    (w : σ → X) (wt : τ → X) (ψ : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ K)
    (hψ : ∀ i, constantCoeff (ψ (MvPowerSeries.X i)) = 0)
    (hg : ∀ j, ∀ f ∈ wtPart O w j, ψ f ∈ wtPart K wt j) : IsHomog O w (RingHom.ker ψ) := by
  classical
  intro f hf j
  rw [RingHom.mem_ker] at hf ⊢
  ext n
  rw [map_zero]
  by_cases hn : Finsupp.weight wt n = j
  swap
  · exact hg j _ (wcomp_mem O w j f) n hn
  have hfin : {m : σ →₀ ℕ | m.degree ≤ n.degree}.Finite := Finsupp.finite_of_degree_le _
  set T : Finset X := insert j (hfin.toFinset.image (Finsupp.weight w)) with hT
  have h1 := coeff_map_zero ψ hψ (n.degree + 1) (f - ∑ i ∈ T, wcomp O w i f) (fun m hm => by
    have hm' : Finsupp.weight w m ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 (Nat.lt_succ_iff.1 hm)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq, if_pos hm', sub_self]) n (Nat.lt_succ_self _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, hf, zero_sub, map_neg, neg_eq_zero, map_sum, map_sum,
    Finset.sum_eq_single_of_mem j (Finset.mem_insert_self _ _)] at h1
  · exact h1
  · intro i _ hi
    exact hg i _ (wcomp_mem O w i f) n (fun h => hi (h.symm.trans hn))

theorem UpperTheory.V.Alg.chart_ker :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (τ : Type) [Fintype τ] (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ →
      (RingHom.ker φ).IsPrime ∧ IsHomog O W.wt (RingHom.ker (φ.comp W.π)) ∧ RingHom.ker φ ≤ RingHom.ker (W.origin h) ∧
      (∀ D ∈ PtDer (W.origin h) O, ∀ f, φ f = 0 → D f = 0) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R') (x' : R' →ₐ[O] O) (φ' : R' →ₐ[O] MvPowerSeries τ (FractionRing O)), Function.Surjective p → x'.comp p = W.origin h → φ'.comp p = φ →
        IsChart (fun j => (W.part j).map p.toLinearMap) x' wt φ' := by
  intro O X R _ _ _ _ _ _ W h τ _ wt φ H
  have hle : ∀ f, φ f = 0 → W.origin h f = 0 := fun f hf => by
    have := H.const f
    rw [hf, map_zero] at this
    exact IsFractionRing.injective O (FractionRing O) (by rw [← this, map_zero])
  haveI : IsDomain (MvPowerSeries τ (FractionRing O)) := NoZeroDivisors.to_isDomain _
  refine ⟨RingHom.ker_isPrime _, ?_, hle, ?_, ?_⟩
  · refine homog_ker W.wt wt _ (fun i => ?_) (fun j f hf => H.graded j _ ⟨f, hf, rfl⟩)
    rw [AlgHom.comp_apply, H.const, W.origin_π]
    simp
  · intro D hD f hf
    obtain ⟨c, hc, hcf⟩ := H.inj f (hle f hf) (fun i => by rw [hf, map_zero])
    have key : ∀ g ∈ RingHom.ker (W.origin h) ^ 2, D g = 0 := by
      intro g hg
      rw [pow_two] at hg
      refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
      · rw [RingHom.mem_ker] at ha hb
        rw [hD a b, ha, hb, zero_smul, zero_smul, add_zero]
      · intro a b ha hb
        rw [map_add (f := _), ha, hb, add_zero]
    have := key _ hcf
    rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  · intro R' _ _ p x' φ' hp hx hφ
    have hx1 : ∀ f, x' (p f) = W.origin h f := fun f => by rw [← hx]; rfl
    have hφ1 : ∀ f, φ' (p f) = φ f := fun f => by rw [← hφ]; rfl
    refine ⟨?_, fun f => ?_, fun i => ?_, fun f hf hl => ?_⟩
    · rintro j _ ⟨f, hf, rfl⟩
      show φ' (p f) ∈ _
      rw [hφ1]
      exact H.graded j f hf
    · obtain ⟨f, rfl⟩ := hp f
      rw [hφ1, hx1, H.const]
    · obtain ⟨f, hf⟩ := H.onto i
      exact ⟨p f, by rw [hφ1]; exact hf⟩
    · obtain ⟨f, rfl⟩ := hp f
      rw [hx1] at hf
      rw [hφ1] at hl
      obtain ⟨c, hc, hcf⟩ := H.inj f hf hl
      refine ⟨c, hc, ?_⟩
      rw [← map_smul]
      have h1 : RingHom.ker (W.origin h) ≤ (RingHom.ker x').comap p := fun g hg => by
        rw [Ideal.mem_comap, RingHom.mem_ker, hx1]
        exact hg
      exact Ideal.le_comap_pow (K := RingHom.ker x') p 2 (Ideal.pow_right_mono h1 2 hcf)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartRank
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
  {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X} {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)}

private noncomputable def crLin (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) :
    A →ₗ[O] FractionRing O :=
  ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap

private theorem crLin_apply (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (f : A) :
    crLin φ i f = MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := rfl

private theorem crLin_sat (h : IsChart 𝒜 x wt φ) (i : τ) : ∀ f ∈ satSq x, crLin φ i f = 0 := by
  classical
  have h2 : ∀ f ∈ RingHom.ker x ^ 2, crLin φ i f = 0 := by
    intro f hf
    rw [sq] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
    have ha' : MvPowerSeries.coeff 0 (φ a) = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const, show x a = 0 from ha, map_zero]
    have hb' : MvPowerSeries.coeff 0 (φ b) = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const, show x b = 0 from hb, map_zero]
    rw [crLin_apply, map_mul, MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
    simp [Finset.Nat.antidiagonal_succ, ha', hb']
  rintro f ⟨c, hc, hf⟩
  have := h2 _ hf
  rw [map_smul] at this
  exact (smul_eq_zero.1 this).resolve_left hc

private theorem crLin_wt (h : IsChart 𝒜 x wt φ) (i : τ) {j : X} (hij : wt i ≠ j)
    {f : A} (hf : f ∈ 𝒜 j) : crLin φ i f = 0 :=
  h.graded j f hf _ (by simpa [Finsupp.weight_single] using hij)

private theorem crLin_const (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (c : O) :
    crLin φ i (algebraMap O A c) = 0 := by
  classical
  rw [crLin_apply, AlgHom.commutes, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, if_neg (by simp)]

private theorem cr_fixed (h : IsChart 𝒜 x wt φ) {j : X} (hj : j ≠ 0) {f : A} (hf : f ∈ 𝒜 j) : x f = 0 := by
  have h1 := h.graded j f hf 0 (by simpa using hj.symm)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const] at h1
  exact IsFractionRing.injective O (FractionRing O) (by rw [h1, map_zero])

private theorem crLin_proj [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) (i : τ) {j : X}
    (hij : wt i = j) (f : A) : crLin φ i (DirectSum.decompose 𝒜 f j) = crLin φ i f := by
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k f =>
    by_cases hk : k = j
    · subst hk
      rw [DirectSum.decompose_of_mem_same 𝒜 f.2]
    · rw [DirectSum.decompose_of_mem_ne 𝒜 f.2 hk, map_zero, crLin_wt h i (fun h' => hk (h'.symm.trans hij)) f.2]
  | add f g hf hg => simp [hf, hg]

private theorem cr_comp [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) (j : X) (f : A) :
    ∃ g : A, g ∈ 𝒜 j ∧ x g = 0 ∧ ∀ i, wt i = j → crLin φ i g = crLin φ i f := by
  have hm : (DirectSum.decompose 𝒜 f j : A) ∈ 𝒜 j := (DirectSum.decompose 𝒜 f j).2
  by_cases hj : j = 0
  · subst hj
    refine ⟨(DirectSum.decompose 𝒜 f 0 : A) - algebraMap O A (x (DirectSum.decompose 𝒜 f 0 : A)),
      sub_mem hm (SetLike.algebraMap_mem_graded 𝒜 _), by simp, fun i hi => ?_⟩
    rw [map_sub, crLin_const, sub_zero, crLin_proj h i hi]
  · exact ⟨_, hm, cr_fixed h hj hm, fun i hi => crLin_proj h i hi f⟩

end

theorem UpperTheory.V.Alg.chart_rank :
    ∀ (O A X : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (τ : Type) [Fintype τ] (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart 𝒜 x wt φ →
      ∀ j, Module.finrank O (cotLat x 𝒜 j) = Nat.card {i // wt i = j} := by
  intro O A X _ _ _ _ _ _ 𝒜 _ x τ _ wt φ h j
  classical
  rw [Nat.card_eq_fintype_card]
  let ψ : cotLat x 𝒜 j →ₗ[O] ({i // wt i = j} → FractionRing O) :=
    LinearMap.pi fun i => ((satSq x).liftQ (crLin φ i.1) (crLin_sat h i.1)) ∘ₗ (cotLat x 𝒜 j).subtype
  have hψ : ∀ (f : A) (hf : (satSq x).mkQ f ∈ cotLat x 𝒜 j) i, ψ ⟨_, hf⟩ i = crLin φ i.1 f := fun f hf i => rfl
  apply Module.finrank_eq_of_rank_eq
  apply le_antisymm
  · have hinj : Function.Injective ψ := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      rintro ⟨_, f, hf, rfl⟩ h0
      apply Subtype.ext
      refine (Submodule.Quotient.mk_eq_zero _).2 (h.inj f hf.2 fun i => ?_)
      by_cases hi : wt i = j
      · exact congrFun h0 ⟨i, hi⟩
      · exact crLin_wt h i hi hf.1
    have h1 := LinearMap.rank_le_of_injective ψ hinj
    rwa [← IsLocalization.rank_eq (FractionRing O) (nonZeroDivisors O) le_rfl (N := {i // wt i = j} → FractionRing O),
      rank_fun'] at h1
  · choose g hg hg' using h.onto
    choose p hp hpx hpl using cr_comp h j
    have hm : ∀ i, (satSq x).mkQ (p (g i)) ∈ cotLat x 𝒜 j := fun i => ⟨_, ⟨hp _, hpx _⟩, rfl⟩
    have hli : LinearIndependent O fun i : {i // wt i = j} => (⟨_, hm i.1⟩ : cotLat x 𝒜 j) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h1 := congrFun (congrArg ψ hc) i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i, map_zero, map_smul, Pi.smul_apply, hψ,
        hpl _ _ i.2] at h1
      · exact (smul_eq_zero.1 h1).resolve_right (hg i.1)
      · intro k _ hk
        rw [map_smul, Pi.smul_apply, hψ, hpl _ _ i.2, crLin_apply,
          hg' k.1 i.1 (fun h' => hk (Subtype.ext h').symm), smul_zero]
      · simp
    have h2 := hli.cardinal_le_rank
    rwa [Cardinal.mk_fintype] at h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_mvps_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsAdicComplete (maximalIdeal A) A) :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

private theorem co_mvps_fin (R : Type) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact co_mvps_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm inferInstance
  | succ n ih =>
    exact co_mvps_equiv (finSuccEquiv R n).toRingEquiv.symm
      (UpperTheory.V.abelian₂.adicComplete (MvPowerSeries (Fin n) R))

theorem UpperTheory.V.Alg.co_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : Type) [Finite σ], IsCO O (MvPowerSeries σ R) := by
  intro O _ _ R _ _ hR σ _
  have hc : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  refine
    { toIsLocalRing := inferInstance
      toIsNoetherian := MvPowerSeries.isNoetherianRing R
      complete := co_mvps_equiv (renameEquiv R e.symm).toRingEquiv (co_mvps_fin R n)
      isLocalHom := ⟨fun a ha => ?_⟩
      res_surj := fun x => ?_ }
  · have h := isUnit_constantCoeff _ ha
    rw [MvPowerSeries.algebraMap_apply, constantCoeff_C] at h
    exact IsLocalHom.map_nonunit a h
  · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (constantCoeff x)
    refine ⟨a, fun h => ha ?_⟩
    have h2 := isUnit_constantCoeff _ h
    rwa [map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C] at h2
end

