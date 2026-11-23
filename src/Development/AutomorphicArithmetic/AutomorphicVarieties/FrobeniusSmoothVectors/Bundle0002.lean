module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EqIdempotentCutOfComplementKills
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem list_forall_eq_zero_of_nonpos_of_sum_eq_zero (L : List ℤ) (h : ∀ x ∈ L, x ≤ 0) (hs : L.sum = 0) : ∀ x ∈ L, x = 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    intro x hx
    simp only [List.sum_cons] at hs
    have ha : a ≤ 0 := h a (by simp)
    have hL : ∀ x ∈ L, x ≤ 0 := fun x hx => h x (by simp [hx])
    have hsL : L.sum ≤ 0 := by
      clear ih hs hx
      induction L with
      | nil => simp
      | cons b L ih2 =>
        simp only [List.sum_cons]
        have hb : b ≤ 0 := hL b (by simp)
        have := ih2 (fun x hx => h x (by rcases List.mem_cons.mp hx with rfl | hx <;> simp [hx])) (fun x hx => hL x (by simp [hx]))
        linarith
    rcases List.mem_cons.mp hx with rfl | hx
    · linarith
    · exact ih hL (by linarith) x hx

private theorem w_sub_w_nonpos_of_le (n : ℕ) (i j : Fin n) (hji : j ≤ i) : w n i - w n j ≤ 0 := by
  rw [Fin.le_def] at hji
  unfold w
  split_ifs <;> omega

private theorem eq_of_w_sub_w_eq_zero (n : ℕ) (i j : Fin n) (h : w n i - w n j = 0) : i = j := by
  unfold w at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem UpperTheory.V.Fr.adjoin_image_in_residue_range :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) {Q : Type} [CommRing Q] (f : ResidueField O →+* Q) (φ : S.A →+* Q), (∀ a : O, φ (algebraMap O S.A a) = f (residue O a)) → (S.u.map φ).triM = ⊥ → (S.u.map φ).IsBar f → ∀ z : S.A, (z : S.R) ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) → φ z ∈ f.range := by
  intro l _ O _ _ F n S Q _ f φ hφ htri hbar z hz
  have hrA : ∀ g i j, S.ρ.r g i j ∈ S.A := fun g i j =>
    Algebra.subset_adjoin (Or.inr ⟨g, i, j, rfl⟩)
  have hψA : ∀ v i g, ((S.ρ.ψ v i g : S.Rˣ) : S.R) ∈ S.A := by
    intro v i g
    apply Algebra.subset_adjoin
    left
    show _ ∈ adicClosure _
    intro N
    exact ⟨_, Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩), by simp⟩
  have hr' : ∀ g i j, (S.u.map φ).r g i j = φ ⟨S.ρ.r g i j, hrA g i j⟩ := fun g i j => rfl
  have hψ' : ∀ v i g, (((S.u.map φ).ψ v i g : Qˣ) : Q) = φ ⟨_, hψA v i g⟩ := fun v i g => rfl
  have hzero : ∀ g i j, i < j → φ ⟨S.ρ.r g i j, hrA g i j⟩ = 0 := by
    intro g i j hij
    have hm : (S.u.map φ).r g i j ∈ (S.u.map φ).triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [htri, Ideal.mem_bot] at hm
    rw [← hr']
    exact hm
  have hdiag : ∀ g i j, i = j → φ ⟨S.ρ.r g i j, hrA g i j⟩ ∈ f.range := by
    rintro g i j rfl
    rw [← hr', hbar.1 g i]
    exact ⟨_, rfl⟩
  have hψr : ∀ v i g, φ ⟨_, hψA v i g⟩ ∈ f.range := by
    intro v i g
    rw [← hψ', hbar.2 v i g]
    exact ⟨_, rfl⟩
  have hDA : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ S.A := by
    apply Algebra.adjoin_le
    rintro x (⟨L, -, rfl⟩ | ⟨v, i, g, rfl⟩)
    · apply list_prod_mem
      intro y hy
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp hy
      exact hrA _ _ _
    · exact hψA v i g
  have key : ∀ x (hx : x ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})),
      φ ⟨x, hDA hx⟩ ∈ f.range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨L, hsum, rfl⟩ | ⟨v, i, g, rfl⟩
      · have e : (⟨(L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod, hDA (Algebra.subset_adjoin (Or.inl ⟨L, hsum, rfl⟩))⟩ : S.A) =
            (L.map fun s => (⟨S.ρ.r s.1 s.2.1 s.2.2, hrA _ _ _⟩ : S.A)).prod := by
          apply Subtype.ext
          simp [List.map_map, Function.comp_def]
        rw [e, map_list_prod, List.map_map]
        by_cases hex : ∃ s ∈ L, s.2.1 < s.2.2
        · obtain ⟨s, hs, hlt⟩ := hex
          rw [List.prod_eq_zero]
          · exact zero_mem _
          · exact List.mem_map.mpr ⟨s, hs, hzero _ _ _ hlt⟩
        · push_neg at hex
          have hterm := list_forall_eq_zero_of_nonpos_of_sum_eq_zero _ (fun x hx => by
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
            exact w_sub_w_nonpos_of_le n _ _ (hex s hs)) hsum
          apply list_prod_mem
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
          exact hdiag _ _ _ (eq_of_w_sub_w_eq_zero n _ _ (hterm _ (List.mem_map_of_mem hs)))
      · exact hψr v i g
    | algebraMap r =>
      show φ (algebraMap O S.A r) ∈ f.range
      rw [hφ]
      exact ⟨_, rfl⟩
    | add x y hx hy ihx ihy =>
      show φ (⟨x, hDA hx⟩ + ⟨y, hDA hy⟩) ∈ f.range
      rw [map_add (f := _)]
      exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      show φ (⟨x, hDA hx⟩ * ⟨y, hDA hy⟩) ∈ f.range
      rw [map_mul]
      exact mul_mem ihx ihy
  exact key z hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.star :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → (∀ g : F.G0, F.star (F.star g) = g) ∧ (∀ g h : F.G0, F.star (g * h) = F.star h * F.star g) ∧ (∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹) ∧ Continuous F.star ∧ ∀ {n : ℕ} {K : Type} [CommRing K] (ρ : NRep F n K) (g : F.G0) (i j : Fin n), ρ.r (F.star g) i j = ρ.r g j.rev i.rev := by
  intro l _ k _ _ F C₀ hF
  have hs : ∀ g : F.G0, ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := fun g => by
    simp [Frame.star, Frame.conj, MulAut.conjNormal_apply, mul_assoc]
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  refine ⟨fun g => ?_, fun g h => ?_, fun g => ?_, ?_, fun {n} {K} _ ρ g i j => ?_⟩
  · apply Subtype.ext
    rw [hs, hs, hc]
    simp only [_root_.mul_inv_rev, inv_inv, hc]
    calc F.c * (F.c * ((g : F.Γ) * F.c)) * F.c = (F.c * F.c) * (g : F.Γ) * (F.c * F.c) := by group
      _ = g := by rw [hF.c_sq]; group
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hs, _root_.mul_inv_rev, hc]
    calc F.c * ((h : F.Γ)⁻¹ * (g : F.Γ)⁻¹) * F.c
        = F.c * (h : F.Γ)⁻¹ * (F.c * F.c) * (g : F.Γ)⁻¹ * F.c := by rw [hF.c_sq]; group
      _ = F.c * (h : F.Γ)⁻¹ * F.c * (F.c * (g : F.Γ)⁻¹ * F.c) := by group
  · rw [hs, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  · refine continuous_induced_rng.2 ?_
    have : (fun g : F.G0 => ((F.star g : F.G0) : F.Γ)) = fun g : F.G0 => F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := funext hs
    change Continuous (fun g : F.G0 => ((F.star g : F.G0) : F.Γ))
    rw [this]
    exact (continuous_const.mul continuous_subtype_val.inv).mul continuous_const
  · rw [ρ.pol]
    simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    have h : ∀ a : Fin n, (j = a.rev) ↔ (a = j.rev) := fun a => by
      constructor <;> rintro rfl <;> simp
    simp [h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimQuotientBound
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.krull_dim_quotient_bound :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I K : Ideal R) {ι : Type} [Fintype ι] (t : ι → R), (∀ a, t a ∈ maximalIdeal R) → (∀ P : Ideal R, P.IsPrime → I ≤ P → (∀ a, t a ∈ P) → K ≤ P) → ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ K) + (Fintype.card ι : ℕ) := by
  intro R _ _ _ I K ι _ t ht hP
  classical
  have hjac : (Set.range fun a => Ideal.Quotient.mk I (t a)) ⊆ Ring.jacobson (R ⧸ I) := by
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Ring.jacobson_eq_sInf_isMaximal, Ideal.mem_sInf]
    intro m hm
    have hm' : m.IsMaximal := hm
    have h1 : (m.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 := IsLocalRing.eq_maximalIdeal h1
    have h3 : t a ∈ m.comap (Ideal.Quotient.mk I) := h2 ▸ ht a
    exact h3
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_encard _ hjac
  have hspan : Ideal.span (Set.range fun a => Ideal.Quotient.mk I (t a))
      = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have h2 : ringKrullDim ((R ⧸ I) ⧸ Ideal.span (Set.range fun a => Ideal.Quotient.mk I (t a)))
      = ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) := by
    rw [hspan]
    exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)
  have h3 : ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) ≤ ringKrullDim (R ⧸ K) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient]
    have hsub : PrimeSpectrum.zeroLocus (R := R) ((I ⊔ Ideal.span (Set.range t) : Ideal R) : Set R)
        ⊆ PrimeSpectrum.zeroLocus (R := R) (K : Set R) := by
      intro p hp
      have hp' : I ⊔ Ideal.span (Set.range t) ≤ p.asIdeal := hp
      refine hP p.asIdeal p.isPrime (le_sup_left.trans hp') fun a => ?_
      exact (le_sup_right.trans hp') (Ideal.subset_span ⟨a, rfl⟩)
    exact Order.krullDim_le_of_strictMono (Set.inclusion hsub) fun _ _ h => h
  have h4 : (Set.range fun a => Ideal.Quotient.mk I (t a)).encard ≤ (Fintype.card ι : ℕ) := by
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    simp
  refine h1.trans ?_
  rw [h2]
  refine add_le_add h3 ?_
  exact_mod_cast h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Oddm
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.oddm :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (a g : ℕ) (G : MvPowerSeries (Fin a ⊕ Fin g) O), G ∈ wtPart O (Space.Loc.par a g) 1 → (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) G ∈ maximalIdeal O) → ∃ M : Fin g → MvPowerSeries (Fin a ⊕ Fin g) O, (∀ j, MvPowerSeries.constantCoeff (M j) ∈ maximalIdeal O) ∧ G = ∑ j, M j * MvPowerSeries.X (.inr j) := by
  classical
  intro O _ _ a g G hG hlin
  let M : Fin g → MvPowerSeries (Fin a ⊕ Fin g) O := fun j m =>
    if ∀ k : Fin g, k < j → m (Sum.inr k) = 0 then
      MvPowerSeries.coeff (m + Finsupp.single (Sum.inr j) 1) G else 0
  have hM : ∀ j m, MvPowerSeries.coeff m (M j) =
      if ∀ k : Fin g, k < j → m (Sum.inr k) = 0 then
        MvPowerSeries.coeff (m + Finsupp.single (Sum.inr j) 1) G else 0 := fun _ _ => rfl
  refine ⟨M, ?_, ?_⟩
  · intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hM]
    simpa using hlin (Sum.inr j)
  · ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one, hM]
    by_cases hex : ∃ j : Fin g, n (Sum.inr j) ≠ 0
    · let S := Finset.univ.filter (fun j : Fin g => n (Sum.inr j) ≠ 0)
      have hS : S.Nonempty := by
        obtain ⟨j, hj⟩ := hex
        exact ⟨j, by simp [S, hj]⟩
      have hj0 : n (Sum.inr (S.min' hS)) ≠ 0 := by
        have := S.min'_mem hS
        simpa [S] using this
      have hmin : ∀ k : Fin g, n (Sum.inr k) ≠ 0 → S.min' hS ≤ k := fun k hk =>
        S.min'_le k (by simp [S, hk])
      have hle : ∀ j : Fin g, n (Sum.inr j) ≠ 0 → Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n := by
        intro j hj
        rw [Finsupp.single_le_iff]
        omega
      rw [Finset.sum_eq_single (S.min' hS)]
      · rw [if_pos (hle _ hj0), if_pos, tsub_add_cancel_of_le (hle _ hj0)]
        intro k hk
        by_contra hne
        have := hmin k (by simpa [Finsupp.tsub_apply, Finsupp.single_apply, ne_of_gt hk] using hne)
        exact absurd hk (not_lt.mpr this)
      · intro j _ hj
        by_cases hjl : Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n
        · rw [if_pos hjl]
          have hnj : n (Sum.inr j) ≠ 0 := by
            have := hjl (Sum.inr j)
            simp at this
            omega
          have hlt : S.min' hS < j := lt_of_le_of_ne (hmin j hnj) (Ne.symm hj)
          rw [if_neg]
          intro hall
          have := hall _ hlt
          simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm (ne_of_lt hlt)] at this
          exact hj0 this
        · rw [if_neg hjl]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hex
      have hz : ∀ j : Fin g, ¬ Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n := by
        intro j hj
        have := hj (Sum.inr j)
        simp [hex j] at this
      simp only [hz, if_false, Finset.sum_const_zero]
      apply hG
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero]
      · decide
      · intro i _
        rcases i with i | i
        · simp [Space.Loc.par]
        · simp [hex i]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OrdOfFlag
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prod_tri {C : Type} [CommRing C] {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) C)
    (h1 : ∀ k i j, j < i → M k i j = 0) (h2 : ∀ k, M k k k = 0) : (List.ofFn M).prod = 0 := by
  have main : ∀ k, k ≤ n → ∀ i j : Fin n, (j : ℕ) < k → ((List.ofFn M).take k).prod i j = 0 := by
    intro k
    induction k with
    | zero => intro _ i j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk i j hj
      have htake : (List.ofFn M).take (k + 1) = (List.ofFn M).take k ++ [M ⟨k, hk⟩] := by
        rw [List.take_succ]
        simp [show k < n by omega]
      rw [htake, List.prod_append, List.prod_singleton, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm : (m : ℕ) < k
      · rw [ih (Nat.le_of_succ_le hk) i m hm, zero_mul]
      · by_cases hmj : j < m
        · rw [h1 ⟨k, hk⟩ m j hmj, mul_zero]
        · have e1 : m = ⟨k, hk⟩ := Fin.ext (by simp only [not_lt, Fin.le_def] at hm hmj ⊢; omega)
          have e2 : j = ⟨k, hk⟩ := Fin.ext (by simp only [not_lt, Fin.le_def] at hm hmj ⊢; omega)
          rw [e1, e2, h2, mul_zero]
  have hall : (List.ofFn M).take n = List.ofFn M := List.take_of_length_le (by simp)
  ext i j
  rw [← hall]
  exact main n le_rfl i j j.2

private theorem prod_conj {R : Type} [Monoid R] (g : Rˣ) (L : List R) :
    (L.map fun x => (g : R) * x * ((g⁻¹ : Rˣ) : R)).prod = g * L.prod * ((g⁻¹ : Rˣ) : R) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    simp [mul_assoc]

theorem UpperTheory.V.Fr.ord_of_flag :
    ∀ {H C : Type} [Group H] [CommRing C] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) C) (ψ : Fin n → H →* Cˣ), UpperTheory.V.W.HasFlag r.toHomUnits ψ → (∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0) ∧ ∀ g, (r g).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ψ i g : C)) := by
  intro H C _ _ n r ψ hf
  obtain ⟨g, hg⟩ := hf
  have hconj : ∀ s, ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      (g : Matrix (Fin n) (Fin n) C) * r s * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := by
    intro s
    simp [Units.val_mul]
  constructor
  · intro gs
    show (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod = 0
    let M : Fin n → Matrix (Fin n) (Fin n) C := fun i =>
      (g : Matrix (Fin n) (Fin n) C) * (r (gs i) - (ψ i (gs i) : C) • 1) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)
    have hM : ∀ i, M i = ((g * r.toHomUnits (gs i) * g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) -
        (ψ i (gs i) : C) • 1 := by
      intro i
      rw [hconj]
      simp only [M]
      rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]
    have h0 : (List.ofFn M).prod = 0 := by
      refine prod_tri M (fun k i j hij => ?_) (fun k => ?_)
      · rw [hM, Matrix.sub_apply, Matrix.smul_apply, one_apply_ne (ne_of_lt hij).symm, smul_zero, sub_zero]
        exact (hg (gs k)).1 i j hij
      · rw [hM, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, (hg (gs k)).2 k, sub_self]
    have hmap : List.ofFn M = (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).map
        (fun x => (g : Matrix (Fin n) (Fin n) C) * x * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [List.map_ofFn]
      rfl
    rw [hmap, prod_conj g] at h0
    calc (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod
        = ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) *
          ((g : Matrix (Fin n) (Fin n) C) *
            (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod *
            ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) * (g : Matrix (Fin n) (Fin n) C) := by
          simp [mul_assoc]
      _ = 0 := by rw [h0, mul_zero, zero_mul]
  · intro s
    rw [← Matrix.charpoly_units_conj g (r s), ← Matrix.coe_units_inv, ← hconj,
      Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => by rw [(hg s).2 i]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.RbarProd
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem rbar_J {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * Xᵀ * Jmat (R := K) n) i j = X j.rev i.rev := by
  have h : ∀ x : Fin n, j = x.rev ↔ x = j.rev := fun x => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [Matrix.mul_apply, Jmat, h]

private theorem rbar_w {n : ℕ} (i : Fin n) : w n i.rev = - w n i := by
  have hi := i.2
  unfold w
  rw [Fin.val_rev]
  split_ifs with h <;> omega

private theorem rbar_prod {K : Type} [CommRing K] {n : ℕ} (L : List (Fin n → K)) :
    (L.map fun d => Matrix.diagonal d).prod = Matrix.diagonal L.prod := by
  induction L with
  | nil => simp [← Matrix.diagonal_one]
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal, List.prod_cons]; rfl

private theorem rbar_ord {H K : Type} [CommRing K] {n : ℕ} (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => Matrix.diagonal fun j => ψ j s) ψ g = 0 := by
  unfold ordProd
  have e : (List.ofFn fun i => (Matrix.diagonal fun j => ψ j (g i)) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) K)) =
      (List.ofFn fun i => fun j => ψ j (g i) - ψ i (g i)).map fun d => Matrix.diagonal d := by
    rw [List.map_ofFn]
    congr 1
    funext i
    ext a b
    by_cases h : a = b <;> simp [h, Matrix.one_apply]
  rw [e, rbar_prod, List.prod_ofFn, ← Matrix.diagonal_zero]
  congr 1
  funext j
  rw [Finset.prod_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)

theorem UpperTheory.V.Fr.rbar :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → ∃ ρ : NRep F n k, ρ.IsBar (RingHom.id k) ∧ ρ.IsDiag := by
  intro l _ k _ _ F C₀ n _
  have hs : ∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹ := fun g => by
    have : ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm]
  refine ⟨{ r := { toFun := fun g => Matrix.diagonal fun i => ((F.Ψ g ^ w n i : kˣ) : k)
                   map_one' := by simp
                   map_mul' := fun g h => by simp [Matrix.diagonal_mul_diagonal, mul_zpow] }
            ψ := fun v i => (zpowGroupHom (w n i)).comp (F.Ψ.comp (F.loc v))
            pol := fun g => ?_
            diag := fun i j h => ?_
            ord := fun v g => ?_ }, ⟨fun g i => ?_, fun v i g => rfl⟩, fun g i j h => ?_⟩
  · ext i j
    rw [rbar_J]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, hs]
    by_cases h : i = j
    · subst h
      simp [rbar_w]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne]
      exact fun e => h (Fin.rev_injective e).symm
  · simp [Matrix.diagonal_apply_ne _ h]
  · exact rbar_ord (fun i s => ((F.Ψ (F.loc v s) ^ w n i : kˣ) : k)) g
  · simp
  · exact Matrix.diagonal_apply_ne _ h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResiduallyDiagonalRepresentation
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.residually_diagonal_representation :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] (f : k →+* Q) (ρ : NRep F n Q), (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → (∀ v g, (ρ.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ρ.ψ v i g : Q))) → (∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k)) → ρ.IsBar f := by
  intro l _ k _ F n Q _ _ _ f ρ hbar htri hchar hdiag
  refine ⟨hdiag, ?_⟩
  intro v i g
  have hz : ∀ (s : F.G0) (a b : Fin n), a < b → ρ.r s a b = 0 := fun s a b hab => by
    have : ρ.r s a b ∈ ρ.triM := Ideal.subset_span ⟨s, a, b, hab, rfl⟩
    rw [htri] at this
    exact (Submodule.mem_bot Q).1 this
  have hT : (ρ.r (F.loc0 v g))ᵀ.BlockTriangular id := fun a b hab => hz _ b a hab
  have h1 := Matrix.charpoly_of_upperTriangular _ hT
  rw [Matrix.charpoly_transpose, hchar] at h1
  have h2 := congrArg (Polynomial.eval (ρ.ψ v i g : Q)) h1
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)] at h2
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [sub_eq_zero, Matrix.transpose_apply, hdiag] at hj
  have h3 := hbar.2 v i g
  rw [NRep.map_ψ, hj] at h3
  have h4 := ((residue Q).comp f).injective h3
  rw [hj, h4]
end

