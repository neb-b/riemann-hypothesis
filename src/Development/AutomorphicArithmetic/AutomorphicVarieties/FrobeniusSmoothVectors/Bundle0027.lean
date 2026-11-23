module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankFrameSpaceEq
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem dim_gen (k Q : Type) [Field k] [CommRing Q] [Algebra k Q] (T : Finset Q) (m : ℕ) (h : T.card ≤ m)
    (ht : Algebra.adjoin k (T : Set Q) = ⊤) : ringKrullDim Q ≤ (m : ℕ) := by
  have hs : Function.Surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    simpa using ht
  refine (ringKrullDim_le_of_surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))).toRingHom hs).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
  exact_mod_cast h

private theorem point {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F n Q)
    (hb : ρ.IsBar (algebraMap k Q)) (ht : ρ.triM = ⊥) (hc : ∀ i j, IsLocallyConstant fun g => ρ.r g i j) :
    ∃ T : Finset Q, T.card ≤ 2 * C₀ ∧ ∀ g i j, ρ.r g i j ∈ Algebra.adjoin k (T : Set Q) := by
  classical
  have up : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j h => by
    have : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, h, rfl⟩
    rwa [ht, Ideal.mem_bot] at this
  have red : ∀ U : Subalgebra k Q, (∀ g i j, j < i → ρ.r g i j ∈ U) → ∀ g i j, ρ.r g i j ∈ U := fun U h g i j => by
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [up g i j h1]; exact zero_mem _
    · rw [hb.1]; exact U.algebraMap_mem _
    · exact h g i j h1
  rcases hn with rfl | rfl
  · obtain ⟨T, h1, h2⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF)
      fun f => Frame.strS_map f (framePoint_fiber_nonempty hF Q ρ hb ht hc)
    refine ⟨T, by omega, red _ fun g i j h => ?_⟩
    obtain ⟨rfl, rfl⟩ : i = 1 ∧ j = 0 := by omega
    exact Algebra.span_le_adjoin k _ (h2 g)
  · obtain ⟨T, h1, h2⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strY k) C₀ _ (finrank_structMapY_range hF)
      fun f => Frame.strY_map f (framePoint_y_coord_eq hF Q ρ hb ht hc)
    have hy : ∀ g, ρ.r g 1 0 ∈ Algebra.adjoin k (T : Set Q) := fun g => Algebra.span_le_adjoin k _ (h2 g)
    obtain ⟨T', h3, h4⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF)
      fun f => Frame.strS_map f (framePoint_alg_coord_eq hF Q ρ hb ht hc _ hy)
    obtain ⟨σ, hσ⟩ := (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ_surjective.hasRightInverse
    have hle : Algebra.adjoin k (T : Set Q) ≤ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) :=
      Algebra.adjoin_mono (by simp)
    refine ⟨T ∪ T'.image σ, (Finset.card_union_le _ _).trans ?_, red _ fun g i j h => ?_⟩
    · have := Finset.card_image_le (s := T') (f := σ)
      omega
    have hij : (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 0) := by omega
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hle (hy g)
    · have h5 : ρ.r (F.star g) 1 0 = ρ.r g 2 1 := (UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0
      rw [← h5]
      exact hle (hy _)
    · have h5 : Submodule.span k (T' : Set _) ≤ (Subalgebra.toSubmodule (Algebra.adjoin k
          ((T ∪ T'.image σ : Finset Q) : Set Q))).map (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ :=
        Submodule.span_le.2 fun t ht' => ⟨σ t, Algebra.subset_adjoin (by
          simp only [Finset.coe_union, Finset.coe_image]
          exact Or.inr ⟨t, ht', rfl⟩), hσ t⟩
      obtain ⟨x, hx, hx'⟩ := h5 (h4 g)
      have h6 : x - ρ.r g 2 0 ∈ Algebra.adjoin k (T : Set Q) := (Submodule.Quotient.eq _).1 hx'
      have h7 := sub_mem (show x ∈ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) from hx) (hle h6)
      rwa [sub_sub_cancel] at h7

theorem UpperTheory.V.Fr.finrank_frameSpace_eq :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ringKrullDim (S.A ⧸ (S.x0 ⊔ S.u.triM)) ≤ (2 * C₀ : ℕ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨f, h1, h2, h3⟩ := frame_fiber_eq hF hn S (S.x0 ⊔ S.u.triM) le_sup_left
  letI : Algebra (ResidueField O) (S.A ⧸ (S.x0 ⊔ S.u.triM)) := f.toAlgebra
  have ht : (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).triM = ⊥ := by
    refine Ideal.span_eq_bot.2 ?_
    rintro _ ⟨g, i, j, h, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
  obtain ⟨T, h4, h5⟩ := point hF hn _ _ h1 ht h2
  refine dim_gen (ResidueField O) _ T _ h4 (eq_top_iff.2 fun x _ => ?_)
  have h6 : Subring.closure (Set.range f ∪ {x | ∃ g i j, x = (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).r g i j}) ≤
      (Algebra.adjoin (ResidueField O) (T : Set (S.A ⧸ (S.x0 ⊔ S.u.triM)))).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨g, i, j, rfl⟩)
    · exact Subalgebra.algebraMap_mem _ a
    · exact h5 g i j
  exact h6 (h3 ▸ Subring.mem_top x)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem irr_coord {G K : Type} [Group G] [Field K] {n : ℕ} {a : G → Matrix (Fin n) (Fin n) K}
    (h : MatIrr ⊤ a) (p q : Fin n) (hpq : q ≠ p) : ¬ ∀ g i, i ≠ p → a g i p = 0 := by
  intro hz
  rcases h (Submodule.span K {Pi.single p 1}) (fun g _ v hv => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    refine Submodule.mem_span_singleton.2 ⟨c * a g p p, ?_⟩
    ext i
    by_cases hi : i = p
    · subst hi; simp [Matrix.mulVec_smul]
    · simp [Matrix.mulVec_smul, hi, hz g i hi]) with h | h
  · have := Submodule.span_singleton_eq_bot.1 h
    simpa using congrFun this p
  · have : (Pi.single q 1 : Fin n → K) ∈ Submodule.span K {(Pi.single p 1 : Fin n → K)} := h ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    simpa [hpq] using congrFun hc q

private theorem irr_of_conn {G K : Type} [Group G] [Field K] {n : ℕ} {a : G → Matrix (Fin n) (Fin n) K}
    (hE : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, a g *ᵥ v ∈ W) → ∀ i, ∀ v ∈ W, single i i (1 : K) *ᵥ v ∈ W)
    (hc : ∀ P : Fin n → Prop, (∀ i j, (¬ ∀ g, a g i j = 0) → P j → P i) → ∀ i j, P j → P i) : MatIrr ⊤ a := by
  intro W hW
  have hW' : ∀ g, ∀ v ∈ W, a g *ᵥ v ∈ W := fun g => hW g (Subgroup.mem_top g)
  have h1 : ∀ v ∈ W, ∀ i, v i ≠ 0 → (Pi.single i 1 : Fin n → K) ∈ W := fun v hv i h => by
    convert W.smul_mem (v i)⁻¹ (hE W hW' i v hv) using 1
    ext k
    by_cases hk : k = i
    · subst hk; simp [Matrix.single_mulVec, h]
    · simp [Matrix.single_mulVec, hk]
  have h2 := hc (fun i => (Pi.single i 1 : Fin n → K) ∈ W) fun i j hn hj => by
    obtain ⟨g, hg⟩ := not_forall.1 hn
    exact h1 _ (hW' g _ hj) i (by simpa using hg)
  rw [or_iff_not_imp_left]
  intro h0
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 h0
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine W.sum_mem fun i _ => ?_
  convert W.smul_mem (x i) (h2 i j (h1 v hv j hj)) using 1
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

private theorem jtj {K : Type} [CommRing K] {n : ℕ} (m : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * mᵀ * Jmat (R := K) n) i j = m j.rev i.rev := by
  have h : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => propext ⟨fun e => by simp [e], fun e => by simp [e]⟩
  simp [Matrix.mul_apply, Jmat, h]

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

private theorem conn2 (Z : Fin 2 → Fin 2 → Prop) (hP : ¬ ∀ i j, j < i → Z i j) (hM : ¬ ∀ i j, i < j → Z i j)
    (P : Fin 2 → Prop) (h : ∀ i j, ¬ Z i j → P j → P i) : ∀ i j, P j → P i := by
  have h10 := h 1 0
  have h01 := h 0 1
  simp only [Fin.forall_fin_two] at hP hM ⊢
  simp at hP hM
  tauto

private theorem conn3 (Z : Fin 3 → Fin 3 → Prop) (hs : ∀ i j, Z i j → Z j.rev i.rev)
    (hP : ¬ ∀ i j, j < i → Z i j) (hM : ¬ ∀ i j, i < j → Z i j) (hE : ¬ ∀ i j, Odd (w 3 i - w 3 j) → Z i j)
    (P : Fin 3 → Prop) (h : ∀ i j, ¬ Z i j → P j → P i) : ∀ i j, P j → P i := by
  have s1 : Z 1 0 → Z 2 1 := hs 1 0
  have s2 : Z 2 1 → Z 1 0 := hs 2 1
  have s3 : Z 0 1 → Z 1 2 := hs 0 1
  have s4 : Z 1 2 → Z 0 1 := hs 1 2
  have hP' : ¬ (Z 1 0 ∧ Z 2 0) := fun ⟨x, y⟩ => hP fun i j hij => by
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact x | exact y | exact s1 x
  have hM' : ¬ (Z 0 1 ∧ Z 0 2) := fun ⟨x, y⟩ => hM fun i j hij => by
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact x | exact y | exact s3 x
  have hE' : ¬ (Z 0 1 ∧ Z 1 0) := fun ⟨x, y⟩ => hE fun i j hij => by
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact x | exact y | exact s3 x | exact s1 y
  have h10 := h 1 0
  have h01 := h 0 1
  have h20 := h 2 0
  have h02 := h 0 2
  have h12 := h 1 2
  have h21 := h 2 1
  have key : (P 0 → P 1) ∧ (P 1 → P 2) ∧ (P 2 → P 0) := by
    by_cases a : Z 1 0 <;> by_cases b : Z 0 1
    · exact absurd ⟨b, a⟩ hE'
    · have x := h20 fun y => hP' ⟨a, y⟩
      have y := h12 (mt s4 b)
      have z := h01 b
      exact ⟨y ∘ x, x ∘ z, z ∘ y⟩
    · exact ⟨h10 a, h21 (mt s2 a), h02 fun y => hM' ⟨b, y⟩⟩
    · exact ⟨h10 a, h21 (mt s2 a), h01 b ∘ h12 (mt s4 b)⟩
  obtain ⟨k1, k2, k3⟩ := key
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
  exact ⟨⟨id, k3 ∘ k2, k3⟩, ⟨k1, id, k1 ∘ k3⟩, k2 ∘ k1, k2, id⟩

theorem UpperTheory.V.Fr.types :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (K : Type) [Field K] (f : S.A →+* K), (MatIrr ⊤ (S.u.map f).r ↔ S.u.TI (RingHom.ker f)) ∧ (S.mB ≤ S.π (RingHom.ker f) → S.u.triP ≤ RingHom.ker f ∨ S.u.triM ≤ RingHom.ker f) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S K _ f
  obtain ⟨hco, hm⟩ := co_B hF hn S
  obtain ⟨hcone, hint⟩ := cone_u hF hn S
  have hle : ∀ Q : Fin n → Fin n → Prop,
      Ideal.span {x | ∃ g i j, Q i j ∧ x = S.u.r g i j} ≤ RingHom.ker f ↔
        ∀ i j, Q i j → ∀ g, (S.u.map f).r g i j = 0 := fun Q =>
    ⟨fun h i j hq g => h (Ideal.subset_span ⟨g, i, j, hq, rfl⟩), fun h => Ideal.span_le.2 (by
      rintro x ⟨g, i, j, hq, rfl⟩
      exact h i j hq g)⟩
  have hP := hle fun i j => j < i
  have hM := hle fun i j => i < j
  have hE := hle fun i j => Odd (w n i - w n j)
  refine ⟨⟨fun h => ⟨⟨fun h' => ?_, fun h' => ?_⟩, fun h3 h' => ?_⟩, fun h => ?_⟩, fun h => ?_⟩
  · have h2 : 1 < n := by omega
    refine irr_coord h ⟨0, by omega⟩ ⟨1, h2⟩ (by simp) fun g i hi => hP.1 h' _ _ ?_ g
    have : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext e)
    exact Fin.lt_def.2 (by show 0 < (i : ℕ); omega)
  · have h2 : 1 < n := by omega
    refine irr_coord h ⟨n - 1, by omega⟩ ⟨0, by omega⟩ (by simp; omega) fun g i hi => hM.1 h' _ _ ?_ g
    have : (i : ℕ) ≠ n - 1 := fun e => hi (Fin.ext e)
    have := i.2
    exact Fin.lt_def.2 (by show (i : ℕ) < n - 1; omega)
  · subst h3
    refine irr_coord h 1 0 (by decide) fun g i hi => hE.1 h' _ _ ?_ g
    revert i
    decide
  · refine irr_of_conn (fun W hW i => ?_) ?_
    · have hspan : ∀ M ∈ Submodule.span S.B (Set.range S.u.r), ∀ v ∈ W, M.map f *ᵥ v ∈ W := by
        intro M hM
        induction hM using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨g, rfl⟩ := hx
          exact hW g
        | zero =>
          intro v _
          rw [Matrix.map_zero _ (map_zero f)]
          simp
        | add x y _ _ hx hy =>
          intro v hv
          convert W.add_mem (hx v hv) (hy v hv) using 1
          rw [← Matrix.add_mulVec]
          congr 1
          ext i j
          exact map_add f _ _
        | smul c x _ hx =>
          intro v hv
          convert W.smul_mem (f (algebraMap S.B S.A c)) (hx v hv) using 1
          rw [← Matrix.smul_mulVec]
          congr 1
          ext i j
          exact map_mul f (algebraMap S.B S.A c) _
      intro v hv
      convert hspan _ (idem hF hn S.B S.A S.u hint i) v hv using 2
      ext a b
      simp only [Matrix.single, Matrix.map_apply, Matrix.of_apply]
      split_ifs <;> simp
    · obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rcases hn with rfl | rfl
      · exact conn2 (fun i j => ∀ g, (S.u.map f).r g i j = 0) (mt hP.2 h1) (mt hM.2 h2)
      · refine conn3 (fun i j => ∀ g, (S.u.map f).r g i j = 0) (fun i j hz g => ?_) (mt hP.2 h1) (mt hM.2 h2)
          (mt hE.2 (h3 rfl))
        have := hz (F.star g)
        rwa [(S.u.map f).pol, jtj] at this
  · by_contra hc
    obtain ⟨h1, h2⟩ := not_or.1 hc
    have h1' := mt hP.2 h1
    have h2' := mt hM.2 h2
    push Not at h1' h2'
    obtain ⟨i, j, hij, g, hg⟩ := h1'
    obtain ⟨i', j', hij', g', hg'⟩ := h2'
    obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (sub_pos.2 (w_lt hij)).le
    obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (sub_pos.2 (w_lt hij')).le
    have hq0 : q ≠ 0 := by
      have := w_lt hij'
      omega
    obtain ⟨c, hc1, hc2⟩ := hcone.cyc (List.replicate q (g, i, j) ++ List.replicate p (g', i', j'))
      (by
        simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, nsmul_eq_mul]
        rw [hq, ← neg_sub, hp]
        ring)
      ⟨(g, i, j), List.mem_append_left _ (List.mem_replicate.2 ⟨hq0, rfl⟩), hij.ne'⟩
    rw [hm] at hc1
    have h0 : f (algebraMap S.B S.A c) = 0 := h hc1
    rw [hc2] at h0
    simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, map_mul, map_pow] at h0
    exact mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hg') h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LieTMem
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prp_coe {K : Type} [CommRing K] (j : ZMod 2) (X : adp K j) :
    prp K j (X : Matrix (Fin 3) (Fin 3) K) = X := by
  apply Subtype.ext
  ext a b
  simp only [prp, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  split_ifs with h
  · rfl
  · exact (X.2 a b h).symm

private theorem lieT_mem (K : Type) [CommRing K] : lieT K 3 ∈ adp K 0 := by
  show ∀ a b, pw a b ≠ 0 → lieT K 3 a b = 0
  intro a b h
  by_cases hab : a = b
  · subst hab
    exact absurd (by simp [pw]) h
  · exact Matrix.diagonal_apply_ne _ hab

theorem UpperTheory.V.Fr.ep_tan :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (ρ : NRep F 3 R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → B.Gr σ π → ∀ h : (B.bar O).Ev π, lieT (ResidueField O) 3 ≠ 0 → thetaLie (lieT (ResidueField O) 3) = lieT (ResidueField O) 3 → (∀ j, Module.finrank (ResidueField O) (H1C F.loc (h.ad j) ((B.bar O).bp j)) ≤ Module.finrank (ResidueField O) (derp O σ j)) ∧ Module.finrank (ResidueField O) (H1C F.loc (h.ad 0) ((B.bar O).bp 0)) + 1 ≤ Module.finrank (ResidueField O) (derp O σ 0) + Module.finrank (ResidueField O) (coneH0 (h.ad 0) ((B.bar O).bp 0)) := by
  intro l _ k _ _ F C₀ hOk O _ _ _ _ h2 R _ _ _ σ hσ ρ B π hU hOf hCont hGood hGr h hT0 hθ
  have h2K : (2 : ResidueField O) ≠ 0 := hGood.two
  have hP := (ep_prp (K := ResidueField O) h2K (B.bar O) π h).1
  obtain ⟨hfinTan, -⟩ := pr_tan O R
  have hfin : ∀ j, Module.Finite (ResidueField O) (derp O σ j) := fun j =>
    Module.Finite.of_injective (Submodule.inclusion (fun D hD => hD.1 : derp O σ j ≤ Tan O R))
      (Submodule.inclusion_injective _)
  let φ : ∀ j, derp O σ j →ₗ[ResidueField O] F.Γ → adp (ResidueField O) j := fun j =>
    (LinearMap.compLeft (prp (ResidueField O) j) F.Γ) ∘ₗ (Box.tanCo O B) ∘ₗ (derp O σ j).subtype
  have hbrig : ∀ j (v : F.V) (Y : adp (ResidueField O) j),
      (∀ s, (h.ad j (F.loc v s)) Y - Y ∈ (B.bar O).bp j v) → Y ∈ (B.bar O).bp j v := by
    intro j v Y hY
    have hbar : (B.bar O).Of (ρ.bar O) := by
      let f : R →+* ResidueField O := res O R
      refine ⟨?_, ?_, ?_⟩
      · show ((B.r F.c).mat).map f = 1
        rw [hOf.atc]
        exact Matrix.map_one _ (map_zero f) (map_one f)
      · intro s
        show ((B.r s).mat).map f = _
        rw [hOf.res]
        rfl
      · intro v i s
        have e : (((B.map f).g v : GL (Fin 3) (ResidueField O)) : Matrix (Fin 3) (Fin 3) (ResidueField O)) * (ρ.map f).r (F.loc0 v s) *
            ((((B.map f).g v)⁻¹ : GL (Fin 3) (ResidueField O)) : Matrix (Fin 3) (Fin 3) (ResidueField O)) =
            f.mapMatrix ((B.g v : Matrix (Fin 3) (Fin 3) R) * ρ.r (F.loc0 v s) *
              (((B.g v)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) := by
          rw [map_mul, map_mul]
          rfl
        rw [e]
        exact congrArg f (hOf.psi v i s)
    exact pr_brig (ResidueField O) (ρ.bar O) (B.bar O) hbar hGood v Y hY
  have hsurj : ∀ j, ∀ x ∈ Z1C F.loc (h.ad j) ((B.bar O).bp j),
      ∃ D : derp O σ j, ∃ X, ∀ s, φ j D s = x.1 s + ((h.ad j s) X - X) := by
    intro j x hx
    obtain ⟨hlc, hco, hloc⟩ := hx
    have hy : ((fun s => (x.1 s : Matrix (Fin 3) (Fin 3) (ResidueField O))),
        (fun v => (x.2 v : Matrix (Fin 3) (Fin 3) (ResidueField O)))) ∈
        Z1C F.loc (B.bar O).ad (B.bar O).b := by
      refine ⟨?_, ?_, ?_⟩
      · show IsLocallyConstant (fun s => (x.1 s : Matrix (Fin 3) (Fin 3) (ResidueField O)))
        exact hlc.comp Subtype.val
      · intro s t
        exact congrArg Subtype.val (hco s t)
      · intro v s
        exact hloc v s
    obtain ⟨D, hD, X, hX⟩ := pr_tsurj hOk O R ρ B hU hOf hCont hGood _ hy
    obtain ⟨D', hD', hD'e⟩ := ep_dproj O h2 R σ hσ B π hGr j D hD
    refine ⟨⟨D', hD'⟩, prp _ j X, fun s => ?_⟩
    show prp _ j (Box.tanCo O B D' s) = _
    rw [hD'e s, prp_coe, hX s, map_add (f := _), map_sub, hP, prp_coe]
  haveI := hfin 0
  refine ⟨fun j => ?_, ?_⟩
  · haveI := hfin j
    exact (pr_count F.loc (h.ad j) ((B.bar O).bp j) (φ j) (hbrig j) (hsurj j)).1
  have hc := (pr_count F.loc (h.ad 0) ((B.bar O).bp 0) (φ 0) (hbrig 0) (hsurj 0)).2
  obtain ⟨D, hD, hDe⟩ := pr_tor hOk O R ρ B hU hOf hCont hGood hθ
  obtain ⟨D', hD', hD'e⟩ := ep_dproj O h2 R σ hσ B π hGr 0 D hD
  have e0 : prp (ResidueField O) 0 (lieT (ResidueField O) 3) = ⟨lieT (ResidueField O) 3, lieT_mem _⟩ :=
    prp_coe 0 ⟨_, lieT_mem _⟩
  refine hc ⟨lieT _ 3, lieT_mem _⟩ ⟨D', hD'⟩ ?_ ?_
  · intro h0
    exact hT0 (congrArg Subtype.val h0)
  · intro s
    show prp _ 0 (Box.tanCo O B D' s) = _
    rw [hD'e s, prp_coe, hDe s, map_sub, hP, e0]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem max_of_fin {O D R : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing D]
    [CommRing R] [Algebra O R] [IsCO O R] (f : D →+* R) : ((maximalIdeal R).comap f).IsMaximal := by
  have hk : (maximalIdeal R).comap f = RingHom.ker ((res O R).toRingHom.comp f) := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← res_eq_zero_iff O R]
    rfl
  have hp : ((maximalIdeal R).comap f).IsPrime := Ideal.IsPrime.comap _
  rw [hk] at hp ⊢
  haveI : Finite (D ⧸ RingHom.ker ((res O R).toRingHom.comp f)) :=
    Finite.of_injective _ (RingHom.kerLift_injective _)
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

private theorem flat_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    (h : (maximalIdeal O).map (algebraMap O O') = maximalIdeal O') : Module.Flat O O' := by
  have hinj : Function.Injective (algebraMap O O') := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    have hp : (RingHom.ker (algebraMap O O')).IsPrime := RingHom.ker_isPrime _
    have hm := eq_maximalIdeal (hp.isMaximal hne)
    refine IsDiscreteValuationRing.not_a_field O' ?_
    rw [← h, ← hm, Ideal.map_eq_bot_iff_le_ker]
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro z ⟨⟨a, ha⟩, hz⟩
  have h1 : algebraMap O O' a * z = 0 := by rw [← Algebra.smul_def]; exact hz
  refine (mul_eq_zero.1 h1).resolve_left fun h2 => nonZeroDivisors.ne_zero ha (hinj ?_)
  rw [h2, map_zero]

theorem UpperTheory.V.Fr.loc_flat :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (L.ι : S.A →+* L.R).Flat ∧ x.IsMaximal ∧ S.mB ≤ S.π x := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  refine ⟨?_, ?_, ?_⟩
  · have hA : IsNoetherianRing S.A := (gr_A hF hn S).2.2.2.2.2.1
    have hD : IsNoetherianRing (TensorProduct O L.O' S.A) := by
      have h1 : IsNoetherianRing (TensorProduct O S.A L.O') :=
        Algebra.FiniteType.isNoetherianRing S.A _
      exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv
    let ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) L.ι fun _ _ => Commute.all _ _
    have hι : ∀ a, ι' (1 ⊗ₜ a) = L.ι a := fun a => by simp [ι']
    have hc := loc_cpl hF hn S x L ι' hι
    haveI := max_of_fin (O := L.O') ι'.toRingHom
    have h1 : ι'.toRingHom.Flat := (@UpperTheory.V.CA.c3a _ _ _ _ _ ι'.toRingHom.toAlgebra _ _ _ hc).1
    haveI : Module.Flat O L.O' := flat_dvr L.unr
    have h2 : (Algebra.TensorProduct.includeRight (R := O) (A := L.O') (B := S.A)).toRingHom.Flat := by
      have h3 : (algebraMap S.A (TensorProduct O S.A L.O')).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
      have h4 := h3.comp (RingHom.Flat.of_bijective (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv.toRingHom)
        (Algebra.TensorProduct.comm O S.A L.O').bijective)
      exact h4
    have e : (L.ι : S.A →+* L.R) = ι'.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := O) (A := L.O') (B := S.A)).toRingHom :=
      RingHom.ext fun a => (hι a).symm
    rw [e]
    exact h2.comp h1
  · rw [← L.lies]
    exact max_of_fin (O := L.O') _
  · obtain ⟨h, hm⟩ := co_B hF hn S
    have h1 := max_of_fin (O := L.O') ((L.ι : S.A →+* L.R).comp (S.inc : S.B →+* S.A))
    rw [← Ideal.comap_comap, L.lies] at h1
    rw [← hm]
    exact (eq_maximalIdeal h1).ge
end

