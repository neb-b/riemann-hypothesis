module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestBis
section
namespace CommutingFamilyCommonEigenvector

private lemma key {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] {I : Type}
    (T : I → Module.End ℂ E) (hc : ∀ (a b : I), Commute (T a) (T b))
    (W : Submodule ℂ E) (hW : W ≠ ⊥) (hinv : ∀ i, ∀ x ∈ W, T i x ∈ W)
    (hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') →
      Module.finrank ℂ W ≤ Module.finrank ℂ W')
    (i : I) (w : E) (hw : w ∈ W) : ∃ μ : ℂ, T i w = μ • w := by
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let f : Module.End ℂ W := (T i).restrict (fun x hx => hinv i x hx)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, ?_⟩
  let W' : Submodule ℂ E := W ⊓ (T i).eigenspace μ
  have hW'le : W' ≤ W := inf_le_left
  have hvW' : (v : E) ∈ W' := by
    refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
    rw [Module.End.mem_eigenspace_iff]
    have := hv.apply_eq_smul
    have h2 := congrArg Subtype.val this
    simpa [f] using h2
  have hvne : (v : E) ≠ 0 := by
    intro h; apply hv.2; exact Subtype.ext h
  have hW'ne : W' ≠ ⊥ := by
    intro h; rw [h] at hvW'; exact hvne ((Submodule.mem_bot ℂ).mp hvW')
  have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
    intro j x hx
    have hx' := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hinv j x hx'.1, ?_⟩
    have hx2 : T i x = μ • x := Module.End.mem_eigenspace_iff.mp hx'.2
    rw [Module.End.mem_eigenspace_iff]
    have hcom : T i (T j x) = T j (T i x) := by
      have := hc i j
      exact congrArg (fun g : Module.End ℂ E => g x) this.eq
    rw [hcom, hx2, map_smul]
  have heq : W' = W :=
    Submodule.eq_of_le_of_finrank_le hW'le (hmin W' hW'ne hW'inv)
  have : w ∈ W' := heq ▸ hw
  exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp this).2

end CommutingFamilyCommonEigenvector

theorem UpperTheory.Reformulated.B.Ygb8.main :
    ∀ (d : ℕ) (E : Type) [inst : AddCommGroup E] [inst_1 : _root_.Module ℂ E] [FiniteDimensional ℂ E] {I : Type}
      (T : I → Module.End ℂ E),
      (∀ (a b : I), Commute (T a) (T b)) →
        Module.finrank ℂ E = d → (0 : ℕ) < d → ∃ (w : E), w ≠ (0 : E) ∧ ∃ (c : I → ℂ), ∀ (i : I), (T i : E → E) w = c i • w := by
  intro d E _ _ _ I T hc hd hpos
  classical
  let P : ℕ → Prop := fun n => ∃ W : Submodule ℂ E, W ≠ ⊥ ∧ (∀ i, ∀ x ∈ W, T i x ∈ W) ∧
    Module.finrank ℂ W = n
  have hex : ∃ n, P n := by
    refine ⟨Module.finrank ℂ (⊤ : Submodule ℂ E), ⊤, ?_, fun i x _ => Submodule.mem_top, rfl⟩
    intro h
    have : Module.finrank ℂ (⊤ : Submodule ℂ E) = 0 := by rw [h]; simp
    rw [finrank_top] at this
    omega
  obtain ⟨W, hW, hinv, hWr⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2
    rw [hWr]
    exact Nat.find_min' hex ⟨W', h1, h2, rfl⟩
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  refine ⟨w, hw0, fun i => Classical.choose (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW), ?_⟩
  intro i
  exact Classical.choose_spec (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideAlt
section
theorem UpperTheory.Reformulated.B.Yhd5.main :
    ∀ {n : ℕ} {U : Set (Fin n → ℂ)} {ι : Type} (u : Finset ι) {f : ι → (Fin n → ℂ) → ℂ},
      (∀ i ∈ u, DifferentiableOn ℂ (f i) U) → DifferentiableOn ℂ (fun (t : Fin n → ℂ) ↦ ∏ i ∈ u, f i t) U := by
  intro n U ι u f h
  classical
  induction u using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    have h1 : DifferentiableOn ℂ (f a) U := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha]
    exact h1.mul h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideExtra
section
namespace MeasureEqCardCosetsMul
end MeasureEqCardCosetsMul

theorem UpperTheory.Reformulated.B.Yla7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]
      [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] {I : Subgroup G},
      IsOpen (↑I : Set G) →
        ∀ {D : Set G},
          (∀ g ∈ D, ∀ i ∈ I, g * i ∈ D) →
            ∀ (S : Finset (G ⧸ I)),
              (∀ (q : G ⧸ I), q ∈ S ↔ Quotient.out q ∈ D) →
                (μ : Set G → ENNReal) D = (↑S.card : ENNReal) * (μ : Set G → ENNReal) (↑I : Set G) := by
  intro G _ _ _ _ _ μ _ I hI D hD S hS
  classical
  set f : G ⧸ I → Set G := fun q => (fun h => (Quotient.out q)⁻¹ * h) ⁻¹' (I : Set G) with hf
  have hmem : ∀ q x, x ∈ f q ↔ (Quotient.out q)⁻¹ * x ∈ I := fun q x => Iff.rfl
  have hmk : ∀ q x, x ∈ f q → (QuotientGroup.mk x : G ⧸ I) = q := by
    intro q x hx
    rw [hmem] at hx
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ I) = QuotientGroup.mk x :=
      QuotientGroup.eq.mpr hx
    rw [← this]
    exact Quotient.out_eq' q
  have hDeq : D = ⋃ q ∈ S, f q := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk x : G ⧸ I), ?_, ?_⟩
      · rw [hS]
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I x
        rw [hh]
        exact hD x hx h h.2
      · rw [hmem]
        have : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ I)) : G ⧸ I) = QuotientGroup.mk x :=
          Quotient.out_eq' _
        exact QuotientGroup.eq.mp this
    · rintro ⟨q, hq, hx⟩
      rw [hmem] at hx
      have h1 := hD _ ((hS q).mp hq) _ hx
      simpa using h1
  have hdisj : (S : Set (G ⧸ I)).PairwiseDisjoint f := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    exact hab ((hmk a x hxa).symm.trans (hmk b x hxb))
  have hmeas : ∀ q ∈ S, MeasurableSet (f q) := by
    intro q _
    exact (hI.preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hDeq, MeasureTheory.measure_biUnion_finset hdisj hmeas]
  have : ∀ q ∈ S, μ (f q) = μ (I : Set G) := by
    intro q _
    exact MeasureTheory.measure_preimage_mul μ _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther
section
theorem UpperTheory.Reformulated.B.Yla6.main :
    ∀ {a b c d : Type} [inst : Fintype b] [inst_1 : Fintype c] (A : Matrix a b ℂ) (M : Matrix b c ℂ) (B : Matrix c d ℂ)
      {α μ β : ℝ},
      (∀ (i : a) (j : b), ‖A i j‖ ≤ α) →
        (∀ (i : b) (j : c), ‖M i j‖ ≤ μ) →
          (∀ (i : c) (j : d), ‖B i j‖ ≤ β) →
            ∀ (i : a) (j : d), ‖(A * M * B) i j‖ ≤ (↑(Fintype.card b) : ℝ) * (↑(Fintype.card c) : ℝ) * (α * μ * β) := by
  intro a b c d _ _ A M B α μ β hA hM hB i j
  have h1 : ‖(A * M * B) i j‖ ≤ ∑ l : c, ∑ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ := by
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans ?_)
    simp [norm_mul]
  have h2 : ∀ l : c, ∀ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ ≤ α * μ * β := by
    intro l k
    have ha : 0 ≤ α := (norm_nonneg _).trans (hA i k)
    have hm : 0 ≤ μ := (norm_nonneg _).trans (hM k l)
    exact mul_le_mul (mul_le_mul (hA i k) (hM k l) (norm_nonneg _) ha) (hB l j) (norm_nonneg _)
      (mul_nonneg ha hm)
  calc ‖(A * M * B) i j‖ ≤ ∑ l : c, ∑ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ := h1
    _ ≤ ∑ _l : c, ∑ _k : b, α * μ * β :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => h2 l k
    _ = (↑(Fintype.card b) : ℝ) * (↑(Fintype.card c) : ℝ) * (α * μ * β) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideLast
section
theorem UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq :
    ∀ {n : ℕ} {z z' : Fin n → ℂˣ},
      Multiset.map (fun (i : Fin n) ↦ (↑(z i) : ℂ)) Finset.univ.val =
          Multiset.map (fun (i : Fin n) ↦ (↑(z' i) : ℂ)) Finset.univ.val →
        ∃ (σ : Equiv.Perm (Fin n)), z' = z ∘ (⇑σ : Fin n → Fin n) := by
  classical
  intro n z z' h
  have key : ∀ (w : Fin n → ℂˣ) (c : ℂ),
      Fintype.card {i : Fin n // (w i : ℂ) = c} =
        Multiset.count c (Multiset.map (fun (i : Fin n) ↦ (↑(w i) : ℂ)) Finset.univ.val) := by
    intro w c
    rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i : Fin n // (z' i : ℂ) = c} =
      Fintype.card {i : Fin n // (z i : ℂ) = c} := by
    intro c
    rw [key, key, h]
  let e : ∀ c : ℂ, {i : Fin n // (z' i : ℂ) = c} ≃ {i : Fin n // (z i : ℂ) = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e, ?_⟩
  funext i
  apply Units.ext
  exact (Equiv.ofFiberEquiv_map (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e i).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideRest
section
theorem UpperTheory.Reformulated.B.Yla8.main :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {T : Type} [Finite T] (y : T → Ω),
      (∃ (x : T), y x ≠ (0 : Ω)) → ∃ (x₀ : T), y x₀ ≠ (0 : Ω) ∧ ∀ (x : T), y x / y x₀ ∈ A := by
  intro Ω _ A T _ y ⟨x1, hx1⟩
  have : Nonempty {x : T // y x ≠ 0} := ⟨⟨x1, hx1⟩⟩
  obtain ⟨⟨x₀, h0⟩, hmax⟩ := Finite.exists_max (fun z : {x : T // y x ≠ 0} => A.valuation (y z.1))
  refine ⟨x₀, h0, fun x => ?_⟩
  by_cases hx : y x = 0
  · rw [hx, zero_div]; exact A.zero_mem
  · rw [← A.valuation_le_one_iff, map_div₀]
    have hpos : (0 : A.ValueGroup) < A.valuation (y x₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr h0
    exact (div_le_one₀ hpos).mpr (hmax ⟨x, hx⟩)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideSide
section
theorem UpperTheory.Reformulated.B.Ylb4.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] {N : ℕ} {P Q B : Matrix (Fin N) (Fin N) k}
      {C : ValuativeRel.ValueGroupWithZero k},
      (∀ (i j : Fin N),
          (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (P i j) ≤
            (1 : ValuativeRel.ValueGroupWithZero k)) →
        (∀ (i j : Fin N),
            (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (Q i j) ≤
              (1 : ValuativeRel.ValueGroupWithZero k)) →
          (∀ (i j : Fin N), (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) (B i j) ≤ C) →
            ∀ (i j : Fin N), (ValuativeRel.valuation k : k → ValuativeRel.ValueGroupWithZero k) ((P * B * Q) i j) ≤ C := by
  intro k _ _ N P Q B C hP hQ hB i j
  have hPB : ∀ a b : Fin N, ValuativeRel.valuation k ((P * B) a b) ≤ C := by
    intro a b
    rw [Matrix.mul_apply]
    apply Valuation.map_sum_le
    intro m _
    rw [Valuation.map_mul]
    calc ValuativeRel.valuation k (P a m) * ValuativeRel.valuation k (B m b)
        ≤ 1 * C := mul_le_mul' (hP a m) (hB m b)
      _ = C := one_mul C
  rw [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [Valuation.map_mul]
  calc ValuativeRel.valuation k ((P * B) i l) * ValuativeRel.valuation k (Q l j)
      ≤ C * 1 := mul_le_mul' (hPB i l) (hQ l j)
    _ = C := mul_one C
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideTail
section
theorem UpperTheory.Reformulated.B.Ylb7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] {C : Set G},
      IsCompact C →
        ∀ {n : Set (G × G)}, IsOpen n → (∀ c ∈ C, (c, (1 : G)) ∈ n) → ∃ O ∈ nhds (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n := by
  intro G _ _ C hC n hn h
  have hsub : C ×ˢ ({1} : Set G) ⊆ n := by
    rintro ⟨c, u⟩ ⟨hc, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    exact h c hc
  obtain ⟨U, V, _, hV, _, hV1, hUV⟩ := generalized_tube_lemma hC isCompact_singleton hn hsub
  refine ⟨V, hV.mem_nhds (hV1 rfl), ?_⟩
  intro c hc u hu
  exact hUV ⟨‹C ⊆ U› hc, hu⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideTer
section
theorem UpperTheory.Reformulated.B.Yhd8.main :
    ∀ {n : ℕ} (g g' D : Matrix (Fin n) (Fin n) ℂ),
      g' * g = (1 : Matrix (Fin n) (Fin n) ℂ) →
        g * g' = (1 : Matrix (Fin n) (Fin n) ℂ) → ∀ (k : ℕ), (g' * D * g) ^ k = g' * D ^ k * g := by
  intro n g g' D h1 h2 k
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc g' * D ^ k * g * (g' * D * g) = g' * D ^ k * (g * g') * D * g := by
          simp only [Matrix.mul_assoc]
      _ = g' * (D ^ k * D) * g := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTail
section
theorem UpperTheory.Reformulated.B.DYha5.main :
    ∀ {Ω Ω₀ F F₀ : Type} [inst : Field Ω] [inst_1 : Field Ω₀] [inst_2 : AddCommGroup F] [inst_3 : _root_.Module Ω F]
      [inst_4 : AddCommGroup F₀] [inst_5 : _root_.Module Ω₀ F₀] (i : Ω₀ →+* Ω) (ι : F₀ →+ F),
      (∀ (a : Ω₀) (e : F₀), (ι : F₀ → F) (a • e) = (i : Ω₀ → Ω) a • (ι : F₀ → F) e) →
        ∀ (W : Subring Ω) (A : Subring Ω₀),
          (∀ a ∈ A, (i : Ω₀ → Ω) a ∈ W) →
            ∀ (T : Set F₀),
              Submodule.span (↥W) ((⇑ι : F₀ → F) '' (↑(Submodule.span (↥A) T) : Set F₀)) =
                Submodule.span (↥W) ((⇑ι : F₀ → F) '' T) := by
  intro Ω Ω₀ F F₀ _ _ _ _ _ _ i ι hι W A hA T
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span (↥A) T := hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hy ‹_›) (hz ‹_›)
    | smul a y _ hy =>
      have h1 : ι (a • y) = (⟨i a, hA a a.2⟩ : ↥W) • ι y := hι (a : Ω₀) y
      rw [h1]
      exact Submodule.smul_mem _ _ (hy ‹_›)
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailAlt
section
theorem UpperTheory.Reformulated.B.Yra1.main.{u_1} :
    ∀ {F : Type u_1} [inst : Field F] {r a : ℕ} (M : Matrix (Fin r) (Fin a) F),
      (∀ (z : Fin a → F), M.mulVec z = (0 : Fin r → F) → z = (0 : Fin a → F)) →
        ∃ (e : Fin a → Fin r), (M.submatrix e id).det ≠ (0 : F) := by
  intro F _ r a M hM
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    exact hM
  have hrank : M.rank = a := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  obtain ⟨κ, f, hf, hsp, hli⟩ := exists_linearIndependent' F M.row
  haveI : Finite κ := Finite.of_injective f hf
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = a := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrank]
  let eqv : κ ≃ Fin a := Fintype.equivFinOfCardEq hcard
  refine ⟨f ∘ eqv.symm, ?_⟩
  have hli2 : LinearIndependent F (M.submatrix (f ∘ eqv.symm) id).row := by
    have := hli.comp eqv.symm eqv.symm.injective
    have h : (M.submatrix (f ∘ eqv.symm) id).row = (M.row ∘ f) ∘ eqv.symm := by
      ext i j; rfl
    rw [h]; exact this
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hli2
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailExtra
section
theorem UpperTheory.Reformulated.B.Yvb3.main :
    ∀ (g : ℤ → ENNReal) (n : ℕ), ∑' (m : Fin n → ℤ), ∏ i : Fin n, g (m i) = (∑' (k : ℤ), g k) ^ n := by
  intro g n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).tsum_eq]
    have h : ∀ p : ℤ × (Fin n → ℤ),
        (∏ i : Fin (n+1), g ((Fin.consEquiv (fun _ : Fin (n+1) => ℤ)) p i)) = g p.1 * ∏ i : Fin n, g (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.consEquiv]
    simp_rw [h]
    rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin n → ℤ) => g a * ∏ i : Fin n, g (b i))]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right, pow_succ']
end

