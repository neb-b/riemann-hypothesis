module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AOpRightInvariant
section
noncomputable def UpperTheory.Reformulated.B.Qf37.aOp :
    {G : Type} → [Group G] → Finset G → G → (G → ℂ) → G → ℂ :=
    fun {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) (g : G) ↦ ∑ r ∈ R, φ (g * r * t)

theorem UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant :
    ∀ {G : Type} [inst : Group G] {I : Subgroup G} {t : G} {R : Finset G},
      (∀ r ∈ R, r ∈ I) →
        (∀ i ∈ I, ∃! r : G, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) →
          ∀ {φ : G → ℂ},
            (∀ (g i : G), i ∈ I → φ (g * i) = φ g) →
              ∀ (g i : G), i ∈ I → UpperTheory.Reformulated.B.Qf37.aOp R t φ (g * i) = UpperTheory.Reformulated.B.Qf37.aOp R t φ g := by
  intro G inst I t R hR hU φ hφ g i hi
  have hex : ∀ r ∈ R, ∃ s, s ∈ R ∧ t⁻¹ * (s⁻¹ * (i * r)) * t ∈ I := fun r hr =>
    (hU (i * r) (I.mul_mem hi (hR r hr))).exists
  choose σ hσR hσ using hex
  have hinj : ∀ a (ha : a ∈ R) b (hb : b ∈ R), σ a ha = σ b hb → a = b := by
    intro a ha b hb hab
    have h1 := hσ a ha
    have h2 := hσ b hb
    rw [← hab] at h2
    have h3 := I.mul_mem (I.inv_mem h1) h2
    have h4 : t⁻¹ * (a⁻¹ * b) * t ∈ I := by
      convert h3 using 1
      group
    have h5 : t⁻¹ * (b⁻¹ * b) * t ∈ I := by
      simp
    exact (hU b (hR b hb)).unique ⟨ha, h4⟩ ⟨hb, h5⟩
  unfold UpperTheory.Reformulated.B.Qf37.aOp
  refine Finset.sum_bij σ hσR hinj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le σ hσR
      (fun a b ha hb h => hinj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, hab.symm⟩
  · intro a ha
    rw [← hφ (g * σ a ha * t) _ (hσ a ha)]
    congr 1
    group
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbEval
section
theorem UpperTheory.Reformulated.B.Ra1.ab_eval :
    ∀ {k X : Type} [inst : Field k] [Inhabited X] (r : ℕ)
    (H : Submodule k (X → k)),
    Module.Finite k ↥H →
      Module.finrank k ↥H ≤ r → ∃ (t : Fin r → X), ∀ φ ∈ H, (∀ (a : Fin r), φ (t a) = (0 : k)) → φ = (0 : X → k) := by
  intro k X inst _ r
  induction r with
  | zero =>
    intro H hfin hr
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    refine ⟨fun _ => default, fun φ hφ _ => ?_⟩
    rw [hH] at hφ
    exact (Submodule.mem_bot k).mp hφ
  | succ n ih =>
    intro H hfin hr
    by_cases h : ∀ φ ∈ H, φ = 0
    · exact ⟨fun _ => default, fun φ hφ _ => h φ hφ⟩
    · have h' : ∃ ψ ∈ H, ∃ x, ψ x ≠ 0 := by
        by_contra hc
        apply h
        intro φ hφ
        funext x
        by_contra hx
        exact hc ⟨φ, hφ, x, hx⟩
      obtain ⟨ψ, hψ, x, hx⟩ := h'
      let K : Submodule k (X → k) :=
        H ⊓ LinearMap.ker (LinearMap.proj (R := k) (φ := fun _ : X => k) x)
      have hle : K ≤ H := inf_le_left
      have hlt : K < H := by
        refine lt_of_le_of_ne hle ?_
        intro he
        have hK : ψ ∈ K := he ▸ hψ
        exact hx hK.2
      have hKfin : Module.Finite k ↥K := Submodule.finiteDimensional_of_le hle
      have hrank : Module.finrank k ↥K < Module.finrank k ↥H :=
        Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨t, ht⟩ := ih K hKfin (by omega)
      refine ⟨Fin.cons x t, fun φ hφ h0 => ?_⟩
      exact ht φ ⟨hφ, h0 0⟩ (fun a => h0 a.succ)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsolutelyIrreducibleSpan
section
noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr.{u_1, u_2, u_3} :
    {k : Type u_1} → [Field k] → {n : Type u_2} → [Fintype n] → [DecidableEq n] → {G : Type u_3} → (G → Matrix n n k) → Prop :=
    fun {k : Type u_1} [Field k] {n : Type u_2} [Fintype n] [DecidableEq n] {G : Type u_3} (ρ : G → Matrix n n k) ↦
      (∀ (W : Submodule k (n → k)), (∀ (g : G), ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        ∀ (M : Matrix n n k), (∀ (g : G), M * ρ g = ρ g * M) → ∃ (c : k), M = c • (1 : Matrix n n k)

noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan :
    Prop :=
    ∀ (O : Type) [inst : CommRing O] [inst_1 : IsLocalRing O] (n : Type) [inst_2 : Fintype n] [inst_3 : DecidableEq n]
      (G : Type) [inst_4 : Monoid G] (ρ : G →* Matrix n n O),
      (UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr fun (g : G) ↦
          ((ρ : G → Matrix n n O) g).map (⇑(IsLocalRing.residue O) : O → IsLocalRing.ResidueField O)) →
        Submodule.span O (Set.range (⇑ρ : G → Matrix n n O)) = ⊤

private theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {G : Type} (ρ : G → Matrix n n k) (h : UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr ρ) :
    Algebra.adjoin k (Set.range ρ) = ⊤ := by
  classical
  obtain ⟨h1, h2⟩ := h
  set A : Subalgebra k (Module.End k (n → k)) :=
    (Algebra.adjoin k (Set.range ρ)).map (Matrix.toLinAlgEquiv' (R := k) (n := n)).toAlgHom with hA
  have hmem : ∀ g, Matrix.toLin' (ρ g) ∈ A := fun g =>
    ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩
  have hsm : ∀ (a : A) (v : n → k), a • v = (a : Module.End k (n → k)) v := fun _ _ => rfl
  have hk : ∀ (c : k) (v : n → k), (algebraMap k A c) • v = c • v := fun c v => by
    rw [hsm]; simp
  haveI : IsSemisimpleModule A (n → k) := by
    rw [isSemisimpleModule_iff]
    constructor
    intro W
    let W' : Submodule k (n → k) :=
      { carrier := W
        add_mem' := fun ha hb => W.add_mem ha hb
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          rw [← hk]; exact W.smul_mem _ hv }
    have hW := h1 W' (fun g v hv => by
      have := W.smul_mem (⟨_, hmem g⟩ : A) hv
      rw [hsm] at this
      exact this)
    rcases hW with hW | hW
    · have : W = ⊥ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊥ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊤, this ▸ isCompl_bot_top⟩
    · have : W = ⊤ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊤ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊥, this ▸ isCompl_top_bot⟩
  have hsc : ∀ φ : Module.End A (n → k), ∃ c : k, ∀ v, φ v = c • v := by
    intro φ
    let ψ : Module.End k (n → k) :=
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun c v => by
          rw [← hk, φ.map_smul, hk]; rfl }
    obtain ⟨c, hc⟩ := h2 (LinearMap.toMatrix' ψ) (fun g => by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      refine LinearMap.ext fun v => ?_
      exact φ.map_smul (⟨_, hmem g⟩ : A) v)
    refine ⟨c, fun v => ?_⟩
    have h3 : ψ = Matrix.toLin' (c • (1 : Matrix n n k)) := by
      rw [← hc, Matrix.toLin'_toMatrix']
    have h4 : φ v = ψ v := rfl
    rw [h4, h3]
    simp
  rw [eq_top_iff]
  intro M _
  let f : Module.End (Module.End A (n → k)) (n → k) :=
    { toFun := Matrix.toLin' M
      map_add' := (Matrix.toLin' M).map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        change Matrix.toLin' M (φ v) = φ (Matrix.toLin' M v)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f
    (Finset.univ.image fun i : n => (Pi.single i 1 : n → k))
  obtain ⟨r, N, hN, rfl⟩ := r
  have : M = N := by
    apply Matrix.toLin'.injective
    apply (Pi.basisFun k n).ext
    intro i
    rw [Pi.basisFun_apply]
    exact hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this ▸ hN

theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan :
    UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan := by
  intro O _ _ n _ _ G _ ρ h
  have h1 := UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top _ h
  let π : Matrix n n O →+* Matrix n n (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  have h2 : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => π (ρ g)) = ⊤ := by
    rw [← Algebra.adjoin_eq_span_of_subset]
    · exact (congrArg Subalgebra.toSubmodule h1).trans rfl
    · intro x hx
      apply Submodule.subset_span
      have : x ∈ MonoidHom.mrange (π.toMonoidHom.comp ρ) :=
        (Submonoid.closure_le (S := MonoidHom.mrange (π.toMonoidHom.comp ρ))).mpr
          (by rintro _ ⟨g, rfl⟩; exact ⟨g, rfl⟩) hx
      exact this
  have h3 : ∀ X : Matrix n n (IsLocalRing.ResidueField O),
      ∃ Y ∈ Submodule.span O (Set.range (ρ : G → Matrix n n O)), π Y = X := by
    intro X
    have hX : X ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => π (ρ g)) := h2 ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, map_add _ _ _⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨d • a, Submodule.smul_mem _ _ ha, ?_⟩
      ext i j
      simp [π]
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro M _
  obtain ⟨Y, hY, hYM⟩ := h3 (π M)
  have h4 : M - Y ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Matrix n n O)) := by
    rw [Matrix.matrix_eq_sum_single (M - Y)]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have h5 : (M - Y) i j ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      have h6 : π (M - Y) = 0 := by rw [map_sub, hYM, sub_self]
      exact congrFun (congrFun h6 i) j
    have h7 : Matrix.single i j ((M - Y) i j) = (M - Y) i j • Matrix.single i j (1 : O) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h7]
    exact Submodule.smul_mem_smul h5 Submodule.mem_top
  have h8 : M = Y + (M - Y) := by abel
  rw [h8]
  exact Submodule.add_mem_sup hY h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AddGapLe
section
theorem UpperTheory.Reformulated.B.Yoa4.add_gap_le :
    ∀ {r : ℕ} {d : Fin r → ℕ}, StrictAnti d → ∀ (k : ℕ) (i j : Fin r), (↑j : ℕ) = (↑i : ℕ) + k → d j + k ≤ d i := by
  intro r d hd k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hm : (i : ℕ) + k < r := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hm⟩ rfl
    have h2 : d j < d ⟨(i : ℕ) + k, hm⟩ := hd (by
      rw [Fin.lt_def]
      simp only
      omega)
    omega
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AddPowNsmul
section
theorem UpperTheory.Reformulated.B.Qf49.add_pow_nsmul :
    ∀ {Γ W : Type} [inst : Group Γ] [inst_1 : AddCommGroup W]
    (U : Subgroup Γ) (f : Γ → W),
    (∀ u ∈ U, ∀ v ∈ U, f (u * v) = f u + f v) → f (1 : Γ) = (0 : W) ∧ ∀ u ∈ U, ∀ (k : ℕ), f (u ^ k) = k • f u := by
  intro Γ W _ _ U f h
  have h1 : f 1 = 0 := by
    have h11 := h 1 U.one_mem 1 U.one_mem
    rw [one_mul] at h11
    exact left_eq_add.mp h11
  refine ⟨h1, fun u hu k => ?_⟩
  induction k with
  | zero => rw [pow_zero, zero_nsmul, h1]
  | succ k ih => rw [pow_succ, h _ (U.pow_mem hu k) u hu, ih, succ_nsmul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdjoinForm
section
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.AdjoinForm.adjoin_form :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    {d : ℕ},
    (0 : ℕ) < d → ∀ {x : E}, x ^ (2 : ℕ) = -(↑d : E) → ∀ y ∈ ℚ⟮x⟯, ∃ (s : ℚ) (t : ℚ), y = (↑s : E) + (↑t : E) * x := by
  intro E _ _ d _ x hx y hy
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have h : y ∈ (ℚ⟮x⟯).toSubalgebra := hy
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at h
  clear hy
  induction h using Algebra.adjoin_induction with
  | mem a ha =>
    rw [Set.mem_singleton_iff] at ha
    exact ⟨0, 1, by simp [ha]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ iha ihb =>
    obtain ⟨s, t, rfl⟩ := iha
    obtain ⟨s', t', rfl⟩ := ihb
    exact ⟨s + s', t + t', by push_cast; ring⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨s, t, rfl⟩ := iha
    obtain ⟨s', t', rfl⟩ := ihb
    exact ⟨s * s' - t * t' * d, s * t' + t * s', by push_cast; linear_combination (t * t' : E) * hx⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdjoinSqrtEqRatSpan
section
theorem UpperTheory.adjoin_sqrt_eq_rat_span :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), s ^ 2 = -(d : E) → ∀ x : E, x ∈ IntermediateField.adjoin ℚ ({s} : Set E) → ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  intro E _ _ d s hs x hx
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    have h : (-(d : E)) = algebraMap ℚ E (-(d : ℚ)) := by simp
    rw [h]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * (e : E) * hs
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSchurLemma
section
noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux3 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.AdmissibleSchurLemma.eig ρ H (1 : ↥H →* kˣ)

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsAdmissible :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsSmooth ρ ∧
        ∀ (K : Subgroup G), IsOpen (↑K : Set G) → IsCompact (↑K : Set G) → FiniteDimensional k ↥(UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed ρ K)

private theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff {k G V : Type} [Field k] [Group G] [AddCommGroup V]
    [_root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (v : V) :
    v ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed ρ H ↔ ∀ g ∈ H, ρ g v = v := by
  change (∀ h : H, ρ (h : G) v = (((1 : H →* kˣ) h : kˣ) : k) • v) ↔ _
  simp

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm :
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          ∀ (N : Type) [inst_3 : AddCommGroup N] [inst_4 : _root_.Module ℂ N] (π : Representation ℂ G N),
            π.IsIrreducible →
              UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsAdmissible π →
                ∀ (φ : N →ₗ[ℂ] N),
                  (∀ (g : G) (x : N),
                      (φ : N → N) (((π : G → N →ₗ[ℂ] N) g : N → N) x) = ((π : G → N →ₗ[ℂ] N) g : N → N) ((φ : N → N) x)) →
                    ∃ (c : ℂ), φ = c • LinearMap.id := by
  intro G _ _ _ K hKo hKc N _ _ π hirr hadm φ hφ
  obtain ⟨hsm, hfd⟩ := hadm
  rcases subsingleton_or_nontrivial N with hN | hN
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : N)
  let S : Subgroup G :=
    { carrier := {g | π g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        change π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : π a v = v := ha
        change π a⁻¹ v = v
        calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha']
          _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hsm v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hfin : FiniteDimensional ℂ (UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S)) :=
    hfd (K ⊓ S) (hKo.inter hSo) (hKc.inter_right hSc)
  have hvU : v ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S) :=
    (UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff π _ v).2 fun g hg => hg.2
  have hnt : Nontrivial (UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvU⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ x ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S), φ x ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S) := by
    intro x hx
    rw [UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff] at hx ⊢
    intro g hg
    rw [← hφ, hx g hg]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let E : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top E with hE | hE
  · have h1 : Module.End.eigenspace φ c = ⊥ := congrArg Subrepresentation.toSubmodule hE
    have h2 : (w : N) ∈ Module.End.eigenspace φ c := Module.End.mem_eigenspace_iff.2 hwc
    rw [h1] at h2
    exact absurd ((Submodule.mem_bot ℂ).1 h2) hw0
  · have h1 : Module.End.eigenspace φ c = ⊤ := congrArg Subrepresentation.toSubmodule hE
    ext x
    have h2 : x ∈ Module.End.eigenspace φ c := h1 ▸ Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.1 h2
end

