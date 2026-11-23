module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleProjectionExists
section
private lemma sepCore {R S N ι : Type} [Ring R] [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    [AddCommGroup N] [Module R N] (f : ι → S →ₗ[R] N)
    (h : ⨆ i, LinearMap.range (f i) = ⊤) {x : N} (hx : x ≠ 0) :
    ∃ p : N →ₗ[R] S, p x ≠ 0 := by
  have hss : ∀ i, IsSemisimpleModule R (LinearMap.range (f i)) := fun i => .range (f i)
  have : IsSemisimpleModule R N := isSemisimpleModule_of_isSemisimpleModule_submodule' hss h
  have hiso : IsIsotypicOfType R N S := by
    apply IsIsotypicOfType.of_isotypicComponent_eq_top
    rw [eq_top_iff, ← h]
    refine iSup_le fun i => ?_
    rcases (f i).injective_or_eq_zero with hi | hi
    · exact le_sSup ⟨(LinearEquiv.ofInjective (f i) hi).symm⟩
    · rw [hi, LinearMap.range_zero]
      exact bot_le
  obtain ⟨κ, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  have hne : e x ≠ 0 := (LinearEquiv.map_ne_zero_iff e).mpr hx
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  exact ⟨(Finsupp.lapply i) ∘ₗ e.toLinearMap, by simpa using hi⟩

theorem UpperTheory.irreducible_projection_exists :
    ∀ {H V M : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
        (σ : Representation ℂ H V) (ρ : Representation ℂ H M), σ.IsIrreducible →
        ∀ (Y : Submodule ℂ M),
          Y ≤ ⨆ (f : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y }),
            LinearMap.range f.1 →
          ∀ {F : M}, F ∈ Y → F ≠ 0 →
            ∃ p : M →ₗ[ℂ] V, (∀ (g : H), ∀ y ∈ Y, p (ρ g y) = σ g (p y)) ∧ p F ≠ 0 := by
  intro H V M _ _ _ _ _ σ ρ hσ Y hY F hF hF0
  have hinv : ∀ (g : H) {y : M}, y ∈ Y → ρ g y ∈ Y := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => ρ g y ∈ Y) (hY hy) ?_ ?_ ?_
    · rintro ⟨f, hf, hr⟩ x ⟨v, rfl⟩
      rw [← hf g v]
      exact hr ⟨_, rfl⟩
    · simp
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Y.add_mem ha hb
  let Ys : Subrepresentation ρ := ⟨Y, hinv⟩
  let τ : Representation ℂ H Y := Ys.toRepresentation
  let φ : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y } →
      Representation.IntertwiningMap σ τ := fun f =>
    (f.1.codRestrict Y (fun v => f.2.2 ⟨v, rfl⟩)).intertwiningMap_of_isIntertwiningMap σ τ
      (fun g v => Subtype.ext (f.2.1 g v))
  let ψ := fun i => Representation.IntertwiningMap.equivLinearMapAsModule σ τ (φ i)
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  have hall : ∀ y ∈ (⨆ (f : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y }),
      LinearMap.range f.1), ∃ hy : y ∈ Y,
      (show τ.asModule from (⟨y, hy⟩ : Y)) ∈ ⨆ i, LinearMap.range (ψ i) := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => ∃ hy : y ∈ Y,
      (show τ.asModule from (⟨y, hy⟩ : Y)) ∈ ⨆ i, LinearMap.range (ψ i)) hy ?_ ?_ ?_
    · rintro f x ⟨v, rfl⟩
      exact ⟨f.2.2 ⟨v, rfl⟩, Submodule.mem_iSup_of_mem f ⟨v, rfl⟩⟩
    · exact ⟨Y.zero_mem, Submodule.zero_mem _⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨Y.add_mem ha hb, Submodule.add_mem _ ha' hb'⟩
  have htop : ⨆ i, LinearMap.range (ψ i) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨_, hx⟩ := hall (x : Y).1 (hY (x : Y).2)
    exact hx
  obtain ⟨p, hp⟩ := sepCore ψ htop (x := (show τ.asModule from (⟨F, hF⟩ : Y)))
    (fun h => hF0 (congrArg Subtype.val (show (⟨F, hF⟩ : Y) = 0 from h)))
  let p' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm p
  obtain ⟨q, hq⟩ := LinearMap.exists_extend p'.toLinearMap
  have hqy : ∀ (y : M) (hy : y ∈ Y), q y = p' ⟨y, hy⟩ := fun y hy =>
    congrArg (fun l => l (⟨y, hy⟩ : Y)) hq
  refine ⟨q, fun g y hy => ?_, ?_⟩
  · rw [hqy _ (hinv g hy), hqy _ hy]
    exact Representation.IntertwiningMap.isIntertwining τ σ p' g ⟨y, hy⟩
  · rw [hqy _ hF]
    exact hp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleSubrep
section
noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.IrreducibleSubrep.irr_of_iso :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k},
      UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr r → UpperTheory.Reformulated.B.IrreducibleSubrep.RepIso r r' → UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr r' := by
  intro Γ k _ _ n r r' hr hiso
  obtain ⟨hne, -, hmin⟩ := hr
  obtain ⟨g, hg⟩ := hiso
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => ?_⟩
  have hcomm : ∀ s : Γ, (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
      = (r' s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
    intro s
    rw [← Units.val_mul, ← Units.val_mul, hg s, inv_mul_cancel_right]
  have hsec : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec
      (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv r
      (W'.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) := by
    intro s v hv
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    exact hW' s _ hv
  rcases hmin _ le_top hinv with h | h
  · left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have h0 := h (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w) (by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hsec]; exact hw)
    rw [← hsec w, h0, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro w
    have h0 := h (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, hsec] at h0
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsCMOfConj
section
theorem UpperTheory.Reformulated.B.Qh8.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  obtain ⟨x, hx⟩ : ∃ x : K, starRingEnd ℂ (φ₀ x) ≠ φ₀ x := by
    by_contra hne
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext z
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    by_contra hz
    exact hne ⟨z, hz⟩
  have hanti : ∀ (z : K) (φ : K →+* ℂ), starRingEnd ℂ (φ (z - c z)) = -φ (z - c z) := by
    intro z φ
    simp [hc]
  obtain ⟨d, hd0, hd⟩ : ∃ d : K, d ≠ 0 ∧ ∀ φ : K →+* ℂ, starRingEnd ℂ (φ d) = -φ d := by
    refine ⟨x - c x, fun h0 => hx ?_, hanti x⟩
    rw [← hc, ← sub_eq_zero.mp h0]
  have hli : LinearIndependent (NumberField.maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    have h1 : s * 1 + t * d = 0 := hst
    have h2 := congrArg φ₀ h1
    have h3 := congrArg (starRingEnd ℂ) h2
    have hs' : starRingEnd ℂ (φ₀ s) = φ₀ s := hs φ₀
    have ht' : starRingEnd ℂ (φ₀ t) = φ₀ t := ht φ₀
    simp only [map_add (f := _), map_mul, map_one, map_zero, hs', ht', hd] at h2 h3
    have hs0 : s = 0 := by
      apply φ₀.injective
      rw [map_zero]
      linear_combination (h2 + h3) / 2
    have ht0 : t = 0 := by
      rw [hs0, zero_mul, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_right hd0
    exact ⟨Subtype.ext hs0, Subtype.ext ht0⟩
  have hsp : ⊤ ≤ Submodule.span (NumberField.maximalRealSubfield K)
      (Set.range ![(1 : K), d]) := by
    intro z _
    have ha : (z + c z) / 2 ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      simp [hc, add_comm, map_ofNat]
    have hb : (z - c z) / (2 * d) ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      rw [map_div₀, map_div₀, hanti, map_mul, map_mul, hd, map_ofNat, map_ofNat, mul_neg,
        neg_div_neg_eq]
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
    change (z + c z) / 2 * 1 + (z - c z) / (2 * d) * d = z
    field_simp
    ring
  have hfin : Module.finrank (NumberField.maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]
  haveI : Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K :=
    { finrank_eq_two' := hfin }
  exact ⟨⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsCMOfConjAlt
section
open NumberField

theorem UpperTheory.Reformulated.B.Qh9.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice inferInstance
  have hfix : ∀ x : K, c x = x ↔ x ∈ maximalRealSubfield K := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx φ
      have := hc x φ
      rw [hx] at this
      exact this.symm
    · intro hx
      apply φ₀.injective
      rw [hc]
      exact hx φ₀
  have hinv : ∀ x : K, c (c x) = x := by
    intro x
    apply φ₀.injective
    simp [hc]
  let σ : K ≃ₐ[maximalRealSubfield K] K :=
    { toFun := c
      invFun := c
      left_inv := hinv
      right_inv := hinv
      map_mul' := fun x y => φ₀.injective (by simp [hc])
      map_add' := fun x y => φ₀.injective (by simp [hc])
      commutes' := fun x => (hfix _).mpr x.2 }
  have hσ : ∀ x, σ x = c x := fun _ => rfl
  have hne : σ ≠ 1 := by
    intro h1
    apply IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x = x := by rw [← hσ, h1]; rfl
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, hx]
  have hord : orderOf σ = 2 :=
    orderOf_eq_prime (by ext x; simp [pow_two, hσ, hinv]) hne
  have hbot : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.mpr
      ⟨⟨x, (hfix x).mp (hx σ (Subgroup.mem_zpowers σ))⟩, rfl⟩
  have hrank := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers, hord] at hrank
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := ⟨hrank⟩
  exact ⟨⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsClosedEmbeddingToM
section
noncomputable def UpperTheory.Reformulated.B.Qk16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk16.inUJ :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) ↦
      g.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * g = UpperTheory.Reformulated.B.Qk16.Jm ε

theorem UpperTheory.Reformulated.B.Qk16.aux3 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
          g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g h hg hh
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk16.inUJ] at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        UpperTheory.Reformulated.B.Qk16.Jm ε * ((g : Matrix (Fin n) (Fin n) ℂ) * (h : Matrix (Fin n) (Fin n) ℂ))
      = (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        UpperTheory.Reformulated.B.Qk16.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)) * (h : Matrix (Fin n) (Fin n) ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Qk16.Jm ε := by rw [hg, hh]

theorem UpperTheory.Reformulated.B.Qk16.aux4 :
    ∀ {n : ℕ} (ε : Fin n → Bool),
      (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε *
          (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        UpperTheory.Reformulated.B.Qk16.Jm ε := by
  intro n ε
  simp

theorem UpperTheory.Reformulated.B.Qk16.aux5 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g hg
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk16.inUJ] at hg ⊢
  have h1 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv g
  generalize ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = B at h1 ⊢
  generalize (g : Matrix (Fin n) (Fin n) ℂ) = A at h1 hg
  calc B.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * B
      = B.conjTranspose * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) * B := by rw [hg]
    _ = (A * B).conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * (A * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Qk16.Jm ε := by rw [h1]; simp

noncomputable def UpperTheory.Reformulated.B.Qk16.UJ :
    {n : ℕ} → (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦
      { carrier := {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)},
        mul_mem' := @UpperTheory.Reformulated.B.Qk16.aux3 n ε, one_mem' := UpperTheory.Reformulated.B.Qk16.aux4 ε,
        inv_mem' := @UpperTheory.Reformulated.B.Qk16.aux5 n ε : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ }

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk16.toM :
    {n : ℕ} → {ε : Fin n → Bool} → ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} {ε : Fin n → Bool} (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦
      (↑(↑g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

private theorem UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm {n : ℕ} (ε : Fin n → Bool) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * UpperTheory.Reformulated.B.Qk16.Jm ε = 1 := by
  unfold UpperTheory.Reformulated.B.Qk16.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

private theorem UpperTheory.Reformulated.B.Qk16.left_inv {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : UpperTheory.Reformulated.B.Qk16.inUJ ε A) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = 1 := by
  have h : A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε := hA
  calc UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A
      = UpperTheory.Reformulated.B.Qk16.Jm ε * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm]

theorem UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM :
    ∀ {n : ℕ} (ε : Fin n → Bool), Topology.IsClosedEmbedding fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g := by
  intro n ε
  have hc : Continuous fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g :=
    Units.continuous_val.comp continuous_subtype_val
  refine ⟨?_, ?_⟩
  · let F : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
      fun A ↦ (A, MulOpposite.op (UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε))
    have hF : Continuous F :=
      continuous_id.prodMk (MulOpposite.continuous_op.comp
        ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
    refine Topology.IsEmbedding.of_comp hc hF ?_
    have he : Topology.IsEmbedding
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) :=
      Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
    have heq : (F ∘ fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
      funext g
      have hg : UpperTheory.Reformulated.B.Qk16.inUJ ε (g.1 : Matrix (Fin n) (Fin n) ℂ) := g.2
      have h := Units.inv_eq_of_mul_eq_one_left (UpperTheory.Reformulated.B.Qk16.left_inv ε hg)
      rw [Function.comp_apply, Function.comp_apply, Units.embedProduct_apply, h]
    rw [heq]
    exact he
  · have hr : Set.range (fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        {A | A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε} := by
      ext A
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hA
        have h := UpperTheory.Reformulated.B.Qk16.left_inv ε (A := A) hA
        exact ⟨⟨⟨A, _, mul_eq_one_comm.mp h, h⟩, hA⟩, rfl⟩
    rw [hr]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsDiscreteValuationRingIntegralClosure
section
open Polynomial

private theorem isIntegral_of_spectralNorm_le_one (l : ℕ) [Fact l.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L]
    [IsScalarTower ℤ_[l] ℚ_[l] L] (x : L) (hx : spectralNorm ℚ_[l] L x ≤ 1) :
    IsIntegral ℤ_[l] x := by
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).mp hx
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

private theorem isIntegral_or_isIntegral_inv (l : ℕ) [Fact l.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L]
    [IsScalarTower ℤ_[l] ℚ_[l] L] (x : L) :
    IsIntegral ℤ_[l] x ∨ IsIntegral ℤ_[l] x⁻¹ := by
  by_cases hx : spectralNorm ℚ_[l] L x ≤ 1
  · exact Or.inl (isIntegral_of_spectralNorm_le_one l L x hx)
  · refine Or.inr (isIntegral_of_spectralNorm_le_one l L x⁻¹ ?_)
    have hx1 : 1 < spectralNorm ℚ_[l] L x := not_le.mp hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [spectralNorm_zero] at hx1
      exact absurd hx1 (by norm_num)
    have hmul : spectralNorm ℚ_[l] L x * spectralNorm ℚ_[l] L x⁻¹ = 1 := by
      have h := spectralAlgNorm_mul (K := ℚ_[l]) (L := L) x x⁻¹
      rw [mul_inv_cancel₀ hx0, spectralAlgNorm_one] at h
      exact h.symm
    have h0 : 0 ≤ spectralNorm ℚ_[l] L x⁻¹ := spectralNorm_nonneg _
    nlinarith

private theorem isDiscreteValuationRing_integralClosure (l : ℕ) [Fact l.Prime] (L : Type*) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L] [IsScalarTower ℤ_[l] ℚ_[l] L] :
    IsDiscreteValuationRing (integralClosure ℤ_[l] L) := by
  have hD : IsDedekindDomain (integralClosure ℤ_[l] L) :=
    integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] L
  have hF : IsFractionRing (integralClosure ℤ_[l] L) L :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] L
  have hV : ValuationRing (integralClosure ℤ_[l] L) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ L]
    intro x
    rcases isIntegral_or_isIntegral_inv l L x with h | h
    · exact Or.inl ⟨⟨x, h⟩, rfl⟩
    · exact Or.inr ⟨⟨x⁻¹, h⟩, rfl⟩
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] L)) := by
    intro a b hab
    have h : algebraMap ℤ_[l] L a = algebraMap ℤ_[l] L b :=
      congrArg (fun z : integralClosure ℤ_[l] L => (z : L)) hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L b]
      at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] L).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] L) := fun h =>
    IsDiscreteValuationRing.not_isField ℤ_[l] (isField_of_isIntegral_of_isField hinj h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] L) hnf).out 1 2).mpr hV

theorem UpperTheory.integralClosure_isDVR :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] ↥K], IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥K) := by
  intro l _ K _
  exact isDiscreteValuationRing_integralClosure l K
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralOfNormLe
section
namespace UpperTheory.Reformulated.B.S4

theorem isIntegral_of_norm_le {l : ℕ} [Fact l.Prime] {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z := by
  have hi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hm : (minpoly ℚ_[l] z).Monic := minpoly.monic hi
  have hv : spectralValue (minpoly ℚ_[l] z) ≤ 1 := hz
  have hc : ∀ n, ‖(minpoly ℚ_[l] z).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hv
  have hl : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  have h0 : Polynomial.aeval z (q.map (algebraMap ℤ_[l] ℚ_[l])) = 0 := by
    rw [hq]
    exact minpoly.aeval _ _
  rw [Polynomial.aeval_map_algebraMap] at h0
  exact h0

end UpperTheory.Reformulated.B.S4
end

