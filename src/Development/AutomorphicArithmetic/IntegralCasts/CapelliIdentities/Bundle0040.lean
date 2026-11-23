module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmooth
section
noncomputable def UpperTheory.Reformulated.B.DYka2.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.DYka2.main :
    ∀ {Γ V W : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : _root_.Module ℂ W] {ρ : Representation ℂ Γ V}
      {σ : Representation ℂ Γ W},
      UpperTheory.Reformulated.B.DYka2.IsSmooth ρ →
        ∀ (f : ρ.IntertwiningMap σ) {L : Subgroup Γ},
          IsCompact (↑L : Set Γ) →
            ∀ (χ : Γ → ℂ) (u : V),
              (f : V → W) u ≠ (0 : W) →
                (∀ g ∈ L, ((σ : Γ → W →ₗ[ℂ] W) g : W → W) ((f : V → W) u) = χ g • (f : V → W) u) →
                  ∃ (v : V), v ≠ (0 : V) ∧ ∀ g ∈ L, ((ρ : Γ → V →ₗ[ℂ] V) g : V → V) v = χ g • v := by
  intro Γ V W _ _ _ _ _ _ _ ρ σ hρ f L hL χ u hu hχ
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hint : ∀ (g : Γ) (v : V), f (ρ g v) = σ g (f v) := fun g v => Representation.IntertwiningMap.isIntertwining ρ σ f g v
  have hmul : ∀ g ∈ L, ∀ h ∈ L, χ (g * h) = χ g * χ h := by
    intro g hg h hh
    have key : χ (g * h) • f u = (χ g * χ h) • f u := by
      rw [← hχ (g * h) (L.mul_mem hg hh), map_mul, Module.End.mul_apply, hχ h hh, map_smul,
        hχ g hg, smul_smul, mul_comm]
    exact smul_left_injective ℂ hu key
  have h1 : χ 1 = 1 := by
    have key : χ 1 • f u = (1 : ℂ) • f u := by
      rw [← hχ 1 L.one_mem, map_one, one_smul]; rfl
    exact smul_left_injective ℂ hu key
  have hne : ∀ g ∈ L, χ g ≠ 0 := by
    intro g hg h0
    have := hmul g hg g⁻¹ (L.inv_mem hg)
    rw [mul_inv_cancel, h1, h0, zero_mul] at this
    exact one_ne_zero this
  let H : Subgroup L :=
    { carrier := {g | ρ (g : Γ) u = u}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : ρ ((a : Γ)⁻¹) (ρ (a : Γ) u) = u := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rw [ha] at this
        simpa using this }
  have hHopen : IsOpen (H : Set L) := (hρ u).preimage continuous_subtype_val
  haveI : Finite (L ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  haveI : Fintype (L ⧸ H) := Fintype.ofFinite _
  have hχH : ∀ h : L, h ∈ H → χ (h : Γ) = 1 := by
    intro h hh
    have e : ρ (h : Γ) u = u := hh
    have key : χ (h : Γ) • f u = (1 : ℂ) • f u := by
      rw [← hχ h h.2, ← hint, e, one_smul]
    exact smul_left_injective ℂ hu key
  let φ : L → V := fun g => (χ (g : Γ))⁻¹ • ρ (g : Γ) u
  have hφ : ∀ a b : L, QuotientGroup.leftRel H a b → φ a = φ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hb : (b : Γ) = a * ((a⁻¹ * b : L) : Γ) := by simp
    have e : ρ ((a⁻¹ * b : L) : Γ) u = u := hab
    have c := hχH _ hab
    simp only [φ]
    rw [hb, hmul _ a.2 _ (a⁻¹ * b).2, c, mul_one, map_mul, Module.End.mul_apply, e]
  let ψ : L ⧸ H → V := Quotient.lift φ hφ
  have hψ : ∀ g : L, ψ (g : L ⧸ H) = φ g := fun g => rfl
  have hfψ : ∀ q : L ⧸ H, f (ψ q) = f u := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [hψ]
      simp only [φ]
      rw [map_smul, hint, hχ g g.2, smul_smul, inv_mul_cancel₀ (hne g g.2), one_smul]
  have hact : ∀ (l : L) (q : L ⧸ H), ρ (l : Γ) (ψ q) = χ (l : Γ) • ψ (l • q) := by
    intro l q
    induction q using QuotientGroup.induction_on with
    | H g =>
      have : l • (g : L ⧸ H) = ((l * g : L) : L ⧸ H) := rfl
      rw [this, hψ, hψ]
      simp only [φ]
      rw [map_smul, Subgroup.coe_mul, hmul _ l.2 _ g.2, map_mul, Module.End.mul_apply, smul_smul,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ (hne l l.2), one_mul]
  refine ⟨∑ q : L ⧸ H, ψ q, ?_, ?_⟩
  · intro h0
    have e : f (∑ q : L ⧸ H, ψ q) = (Fintype.card (L ⧸ H) : ℂ) • f u := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [hfψ]
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [h0, map_zero] at e
    have hc : (Fintype.card (L ⧸ H) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (smul_ne_zero hc hu) e.symm
  · intro g hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    simp only [hact ⟨g, hg⟩]
    exact (Equiv.sum_comp (MulAction.toPerm (⟨g, hg⟩ : L)) (fun q => χ g • ψ q))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmoothTwAct
section
noncomputable def UpperTheory.Reformulated.B.Gwa2.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

noncomputable def UpperTheory.Reformulated.B.Gwa2.twKer :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      Submodule.span k
        {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[k] V) (↑n : G) : V → V) v - (↑((ψ : ↥N → kˣ) n) : k) • v}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gwa2.TwJacquet :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Type :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      V ⧸ UpperTheory.Reformulated.B.Gwa2.twKer ρ N ψ

theorem UpperTheory.Reformulated.B.Gwa2.aux4 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (m : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m)) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs m
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  obtain ⟨h, hθ⟩ := hs m n
  refine Submodule.subset_span ⟨⟨_, h⟩, ρ (s m) v, ?_⟩
  have key : ρ (s m * (n : G) * (s m)⁻¹) (ρ (s m) v) = ρ (s m) (ρ (n : G) v) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]
  rw [hθ, map_sub, map_smul, ← key]

theorem UpperTheory.Reformulated.B.Gwa2.aux5 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        Submodule.span ℂ
            {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
          Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M))) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  exact UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs 1

theorem UpperTheory.Reformulated.B.Gwa2.aux6 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M)))
          (UpperTheory.Reformulated.B.Gwa2.aux5 ρ N θ s hs) =
        (1 : UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s 1) v) = Submodule.Quotient.mk v
  rw [map_one, map_one, Module.End.one_apply]

theorem UpperTheory.Reformulated.B.Gwa2.aux7 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (a b : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b))) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  exact UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs (a * b)

theorem UpperTheory.Reformulated.B.Gwa2.aux8 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n)
      (a b : M),
      (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b)))
          (UpperTheory.Reformulated.B.Gwa2.aux7 ρ N θ s hs a b) =
        (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) a))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs a) *
          (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) b))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs b) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s (a * b)) v) = Submodule.Quotient.mk (ρ (s a) (ρ (s b) v))
  rw [map_mul, map_mul, Module.End.mul_apply]

noncomputable def UpperTheory.Reformulated.B.Gwa2.twAct :
    {G V : Type} →
      [inst : Group G] →
        [inst_1 : AddCommGroup V] →
          [inst_2 : _root_.Module ℂ V] →
            (ρ : Representation ℂ G V) →
              (N : Subgroup G) →
                (θ : ↥N →* ℂˣ) →
                  {M : Type} →
                    [inst_3 : Group M] →
                      (s : M →* G) →
                        (∀ (m : M) (n : ↥N),
                            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
                              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
                          Representation ℂ M (UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ) :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (N : Subgroup G)
        (θ : ↥N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
        (hs :
          ∀ (m : M) (n : ↥N),
            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) ↦
      {
        toFun := fun (m : M) ↦
          (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs m),
        map_one' := UpperTheory.Reformulated.B.Gwa2.aux6 ρ N θ s hs, map_mul' := UpperTheory.Reformulated.B.Gwa2.aux8 ρ N θ s hs :
        M →* UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ }

private theorem UpperTheory.Reformulated.B.Gwa2.isOpen_fixer {M W : Type} [Group M] [AddCommGroup W] [_root_.Module ℂ W]
    [TopologicalSpace M] [IsTopologicalGroup M] (τ : Representation ℂ M W) (x : W)
    (h : {m : M | τ m x = x} ∈ nhds (1 : M)) : IsOpen {m : M | τ m x = x} := by
  let H : Subgroup M :=
    { carrier := {m : M | τ m x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} (ha : τ a x = x) (hb : τ b x = x) ↦ show τ (a * b) x = x by
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} (ha : τ a x = x) ↦ show τ a⁻¹ x = x by
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact H.isOpen_of_mem_nhds h

theorem UpperTheory.Reformulated.B.Gwa2.isSmooth_twAct :
    ∀ {G M V : Type} [inst : Group G] [inst_1 : Group M] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module ℂ V]
      [inst_4 : TopologicalSpace G] [inst_5 : TopologicalSpace M] [IsTopologicalGroup M] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      Continuous (⇑s : M → G) → UpperTheory.Reformulated.B.Gwa2.IsSmooth ρ → UpperTheory.Reformulated.B.Gwa2.IsSmooth (UpperTheory.Reformulated.B.Gwa2.twAct ρ N θ s hs) := by
  intro G M V _ _ _ _ _ _ _ ρ N θ s hs hc hρ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine UpperTheory.Reformulated.B.Gwa2.isOpen_fixer _ _ ?_
  have hU : IsOpen {m : M | ρ (s m) v = v} := (hρ v).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds (by simp)) fun m (hm : ρ (s m) v = v) ↦ ?_
  change Submodule.Quotient.mk (ρ (s m) v) = Submodule.Quotient.mk v
  rw [hm]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsUnitOfInvIntegral
section
open Polynomial

private lemma integral_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) :
    IsIntegral ℤ_[l] x := by
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hx
  have hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  have h0 := minpoly.aeval ℚ_[l] x
  rw [← hq, aeval_def, eval₂_map] at h0
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact h0

private lemma norm_of_integral {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l)
    (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hc : spectralValue (minpoly ℚ_[l] x) ≤ 1 := by
    rw [spectralValue_le_one_iff (minpoly.monic h.tower_top)]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  exact hc

private lemma isUnit_of_inv_integral {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (a : R) (ha : algebraMap R K a ≠ 0)
    (h : IsIntegral R (algebraMap R K a)⁻¹) : IsUnit a := by
  obtain ⟨p, hp, he⟩ := h
  letI := invertibleOfNonzero (inv_ne_zero ha)
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) ((algebraMap R K a)⁻¹) p
  rw [he, invOf_eq_inv, inv_inv] at h1
  have h2 : eval₂ (algebraMap R K) (algebraMap R K a) p.reverse = 0 := by
    simpa [ha] using h1
  have h3 : eval a p.reverse = 0 := by
    apply hinj
    rw [map_zero, ← h2, eval₂_at_apply]
  have h5 : p.reverse.coeff 0 = 1 := by
    simp [coeff_zero_reverse, hp.leadingCoeff]
  have h4 := divX_mul_X_add p.reverse
  rw [← h4, h5] at h3
  simp only [eval_add, eval_mul, eval_X, eval_C] at h3
  exact isUnit_iff_exists_inv.2 ⟨-(eval a p.reverse.divX), by linear_combination -h3⟩

theorem UpperTheory.integral_dvr_norm :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O]
        [Module.Finite ℤ_[l] O],
        (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral O x) ∧ (∀ a : O, ‖(a : PadicAlgCl l)‖ ≤ 1) ∧
          ∀ a : O, ¬ IsUnit a → ‖(a : PadicAlgCl l)‖ < 1 := by
  intro l _ O _ _
  have hfin : ∀ a : O, IsIntegral ℤ_[l] (a : PadicAlgCl l) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map O.val
  refine ⟨fun x hx => (integral_of_norm x hx).tower_top, fun a => norm_of_integral _ (hfin a),
    fun a ha => lt_of_le_of_ne (norm_of_integral _ (hfin a)) fun h1 => ha ?_⟩
  have ha0 : (a : PadicAlgCl l) ≠ 0 := by
    intro h
    simp [h] at h1
  have hinv : IsIntegral O (a : PadicAlgCl l)⁻¹ :=
    (integral_of_norm _ (by rw [norm_inv, h1, inv_one])).tower_top
  exact isUnit_of_inv_integral (K := PadicAlgCl l) Subtype.val_injective a ha0 hinv
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsotypicStableGlOperator
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe29.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qe29.Umon.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qe29.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) ↦
      Submonoid.closure (Set.range fun (ab : Fin n × Fin n) ↦ E ab.1 ab.2)

noncomputable def UpperTheory.Reformulated.B.Qe29.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qe29.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

noncomputable def UpperTheory.Reformulated.B.Qe29.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qe29.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qe29.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)

noncomputable def UpperTheory.Reformulated.B.Qe29.isoSub.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qe29.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (lam : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qe29.Umon E, ∃ (v : V), UpperTheory.Reformulated.B.Qe29.IsHWV E lam v ∧ x = (u : V → V) v}

theorem UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n),
      ∀ x ∈ UpperTheory.Reformulated.B.Qe29.isoSub E mu, (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qe29.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  have hE : E a b ∈ UpperTheory.Reformulated.B.Qe29.Umon E := Submonoid.subset_closure ⟨(a, b), rfl⟩
  have hle : UpperTheory.Reformulated.B.Qe29.isoSub E mu ≤ (UpperTheory.Reformulated.B.Qe29.isoSub E mu).comap (E a b) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, v, hv, rfl⟩
    exact Submodule.subset_span ⟨E a b * u, Submonoid.mul_mem _ hE hu, v, hv, rfl⟩
  exact hle hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsotypicStableOperator
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh28.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qh28.Umon.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qh28.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) ↦
      Submonoid.closure (Set.range fun (ab : Fin n × Fin n) ↦ E ab.1 ab.2)

noncomputable def UpperTheory.Reformulated.B.Qh28.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qh28.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

noncomputable def UpperTheory.Reformulated.B.Qh28.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qh28.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qh28.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)

noncomputable def UpperTheory.Reformulated.B.Qh28.isoSub.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qh28.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (lam : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qh28.Umon E, ∃ (v : V), UpperTheory.Reformulated.B.Qh28.IsHWV E lam v ∧ x = (u : V → V) v}

theorem UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V},
      x ∈ UpperTheory.Reformulated.B.Qh28.isoSub E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qh28.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  unfold UpperTheory.Reformulated.B.Qh28.isoSub at hx ⊢
  refine (Submodule.span_le (p := Submodule.comap (E a b) (Submodule.span K _))).2 ?_ hx
  rintro _ ⟨u, hu, v, hv, rfl⟩
  refine Submodule.subset_span ⟨E a b * u, ?_, v, hv, rfl⟩
  exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
end

