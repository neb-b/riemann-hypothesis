module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFactor
section
theorem UpperTheory.Reformulated.B.ExistsFactor.exists_factor :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (e : Matrix (Fin n) (Fin n) K),
    e * e = e →
      ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) K) (N : Matrix (Fin r) (Fin n) K),
        N * M = (1 : Matrix (Fin r) (Fin r) K) ∧ M * N = e := by
  intro K _ n e he
  let f : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' e
  have hf : ∀ v, f (f v) = f v := by
    intro v
    have h : f.comp f = f := by
      show (Matrix.toLin' e).comp (Matrix.toLin' e) = Matrix.toLin' e
      rw [← Matrix.toLin'_mul, he]
    exact LinearMap.congr_fun h v
  let b := Module.finBasis K (LinearMap.range f)
  let c := Pi.basisFun K (Fin n)
  refine ⟨Module.finrank K (LinearMap.range f),
    LinearMap.toMatrix b c (LinearMap.range f).subtype,
    LinearMap.toMatrix c b f.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]
    have h : f.rangeRestrict.comp (LinearMap.range f).subtype = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨x, v, rfl⟩
      apply Subtype.ext
      exact hf v
    rw [h, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp]
    have h : (LinearMap.range f).subtype.comp f.rangeRestrict = f := by
      apply LinearMap.ext
      intro v
      rfl
    rw [h]
    show LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) (Matrix.toLin' e) = e
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFinsetSeparating
section
private theorem UpperTheory.Reformulated.B.Qp2.aux {X : Type} (n : ℕ) :
    ∀ (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V], Module.finrank ℂ V = n →
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hn
    by_cases hV : ∀ v ∈ V, v = 0
    · exact ⟨∅, fun v hv _ => hV v hv⟩
    · obtain ⟨w, hw⟩ := not_forall.mp hV
      obtain ⟨hwV, hw0⟩ := Classical.not_imp.mp hw
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hw0
      let U : Submodule ℂ (X → ℂ) := V ⊓ LinearMap.ker (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)
      have hle : U ≤ V := inf_le_left
      have hlt : U < V := by
        refine lt_of_le_of_ne hle ?_
        intro h
        have hwU : w ∈ U := h ▸ hwV
        exact hx (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwU).2)
      haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hle
      have hr : Module.finrank ℂ U < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT⟩ := ih _ hr U rfl
      refine ⟨insert x T, fun v hv h => hT v ?_ fun y hy => h y (Finset.mem_insert_of_mem hy)⟩
      exact Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr (h x (Finset.mem_insert_self x T))⟩

theorem UpperTheory.Reformulated.B.Qp2.exists_finset_separating :
    ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V],
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  intro X V _
  exact UpperTheory.Reformulated.B.Qp2.aux _ V rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFixedLift
section
noncomputable def UpperTheory.Reformulated.B.Gwa5.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.Gwa5.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), smul_add, ha h, hb h]

theorem UpperTheory.Reformulated.B.Gwa5.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.Gwa5.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.Gwa5.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.Gwa5.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.Gwa5.aux3 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.Gwa5.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.Gwa5.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.Gwa5.eig ρ H (1 : ↥H →* kˣ)

theorem UpperTheory.Reformulated.B.Gwa5.exists_fixed_lift :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (J L A : Subgroup G),
      IsOpen (↑J : Set G) →
        IsCompact (↑J : Set G) →
          ∀ (π : Representation ℂ G V),
            UpperTheory.Reformulated.B.Gwa5.IsSmooth π →
              ∀ (q : Submodule ℂ V) (u : V),
                L ≤ J →
                  (∀ y ∈ L, ((π : G → V →ₗ[ℂ] V) y : V → V) u = u) →
                    A ≤ J →
                      (∀ x ∈ A, ((π : G → V →ₗ[ℂ] V) x : V → V) u - u ∈ q) →
                        (∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ L) → ∃ v ∈ UpperTheory.Reformulated.B.Gwa5.fixed π J, v - u ∈ q := by
  intro G V _ _ _ _ _ J L A _ hJc π hπ q u _ hL hAJ hA hdec
  classical
  have hmul : ∀ (x y : G) (w : V), π x (π y w) = π (x * y) w := by
    intro x y w
    rw [map_mul, Module.End.mul_apply]

  have hq : ∀ y ∈ J, π y u - u ∈ q := by
    intro y hy
    obtain ⟨a, ha, hl⟩ := hdec y hy
    have h1 : π y u = π a u := by
      conv_rhs => rw [← hL _ hl, hmul, mul_inv_cancel_left]
    rw [h1]
    exact hA a ha

  have hfin : ((fun g : G => π g u) '' (J : Set G)).Finite := by
    have hU : ∀ x ∈ (J : Set G), {g : G | π g u = π x u} ∈ nhds x := by
      intro x _
      have ho : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g u = u}) :=
        (hπ u).preimage (continuous_const.mul continuous_id)
      refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
      · simp
      · intro g hg
        have hg' : π (x⁻¹ * g) u = u := hg
        show π g u = π x u
        conv_rhs => rw [← hg', hmul, mul_inv_cancel_left]
    obtain ⟨t, -, ht⟩ := hJc.elim_nhds_subcover _ hU
    refine (t.finite_toSet.image (fun g : G => π g u)).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨x, hx, hgx.symm⟩
  set O : Finset V := hfin.toFinset with hO
  have hmem : ∀ w, w ∈ O ↔ ∃ g ∈ J, π g u = w := by
    intro w
    rw [hO, Set.Finite.mem_toFinset]
    rfl
  have hstab : ∀ h ∈ J, ∀ w ∈ O, π h w ∈ O := by
    intro h hh w hw
    obtain ⟨g, hg, rfl⟩ := (hmem w).1 hw
    exact (hmem _).2 ⟨h * g, J.mul_mem hh hg, (hmul h g u).symm⟩
  have hne : (O.card : ℂ) ≠ 0 := by
    have : O.Nonempty := ⟨π 1 u, (hmem _).2 ⟨1, J.one_mem, rfl⟩⟩
    exact_mod_cast this.card_pos.ne'
  refine ⟨(O.card : ℂ)⁻¹ • ∑ w ∈ O, w, ?_, ?_⟩
  · intro h
    have hs : ∑ w ∈ O, π (h : G) w = ∑ w ∈ O, w := by
      refine Finset.sum_nbij' (fun w => π (h : G) w) (fun w => π (h : G)⁻¹ w)
        (fun w hw => hstab _ h.2 w hw) (fun w hw => hstab _ (J.inv_mem h.2) w hw) ?_ ?_
        (fun _ _ => rfl)
      · intro w _
        simp only [hmul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro w _
        simp only [hmul, mul_inv_cancel, map_one, Module.End.one_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, hs, MonoidHom.one_apply, Units.val_one, one_smul]
  · have h2 : (O.card : ℂ)⁻¹ • ∑ w ∈ O, w - u = (O.card : ℂ)⁻¹ • ∑ w ∈ O, (w - u) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h2]
    refine q.smul_mem _ (q.sum_mem ?_)
    intro w hw
    obtain ⟨g, hg, rfl⟩ := (hmem w).1 hw
    exact hq g hg
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsGoodWithoutBad
section
theorem UpperTheory.exists_good_without_bad :
    ∀ {P : Type} [DecidableEq P] (Good : Finset P → Prop) (bad : P → Prop), (∀ (S : Finset P) (w : P), Good S → w ∈ S → bad w → Good (S.erase w)) → ∀ S : Finset P, Good S → ∃ T : Finset P, Good T ∧ ∀ w ∈ T, ¬ bad w := by
  intro P _ Good bad h S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    by_cases hb : ∃ w ∈ S, bad w
    · obtain ⟨w, hw, hbw⟩ := hb
      exact ih (S.erase w) (Finset.erase_ssubset hw) (h S w hS hw hbw)
    · exact ⟨S, hS, fun w hw hbw => hb ⟨w, hw, hbw⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsIndepOfSat
section
theorem UpperTheory.Reformulated.B.Ud9.exists_indep_of_sat :
    ∀ {R E : Type} [inst : CommRing R] [IsDomain R] [IsNoetherianRing R]
    [inst_3 : AddCommGroup E] [inst_4 : _root_.Module R E] [Module.Finite R E] [Module.IsTorsionFree R E] (T : Set E)
    (F : Submodule R E),
    (∀ (x : E), x ∈ F ↔ ∃ (a : R), a ≠ (0 : R) ∧ a • x ∈ Submodule.span R T) →
      ∃ (f : Fin (Module.finrank R ↥F) → E), (∀ (j : Fin (Module.finrank R ↥F)), f j ∈ T) ∧ LinearIndependent R f := by
  intro R E _ _ _ _ _ _ _ T F hF
  obtain ⟨I, hI, hmax⟩ := exists_maximal_linearIndepOn R (Subtype.val : T → E)
  set S : Submodule R E := Submodule.span R ((Subtype.val : T → E) '' I) with hS
  have hT : ∀ y ∈ Submodule.span R T, ∃ b : R, b ≠ 0 ∧ b • y ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      by_cases h : (⟨x, hx⟩ : T) ∈ I
      · exact ⟨1, one_ne_zero, by
          rw [one_smul]; exact Submodule.subset_span ⟨⟨x, hx⟩, h, rfl⟩⟩
      · exact hmax ⟨x, hx⟩ h
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine S.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact S.smul_mem _ hax
      · rw [mul_smul]; exact S.smul_mem _ hby
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [smul_comm]; exact S.smul_mem _ hax
  let N : Submodule R F := S.comap F.subtype
  have h0 : Module.rank R (F ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    obtain ⟨a, ha, hax⟩ := (hF x).1 x.2
    obtain ⟨b, hb, hbx⟩ := hT _ hax
    refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change (b * a) • (x : E) ∈ S
    rwa [mul_smul]
  have h1 : Module.rank R F = Module.rank R N := by
    rw [← rank_quotient_add_rank_of_isDomain N, h0, zero_add]
  have h2 : Module.rank R N ≤ Module.rank R S := by
    let g : N →ₗ[R] S := (F.subtype.comp N.subtype).codRestrict S (fun x => x.2)
    refine LinearMap.rank_le_of_injective g ?_
    intro x y hxy
    have h : ((g x : S) : E) = ((g y : S) : E) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have h3 : Module.rank R S ≤ Cardinal.mk I :=
    (rank_span_le _).trans Cardinal.mk_image_le
  have h4 : Cardinal.mk (Fin (Module.finrank R F)) ≤ Cardinal.mk I := by
    rw [Cardinal.mk_fin, Module.finrank_eq_rank, h1]
    exact h2.trans h3
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 h4
  exact ⟨fun j => ((e j : T) : E), fun j => (e j : T).2, LinearIndependent.comp hI e e.injective⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInjectiveCharacter
section
theorem UpperTheory.Reformulated.B.ExistsInjectiveCharacter.exists_injective_char :
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)],
    ∃ (lam0 : (ZMod p)ˣ →* ℂˣ), Function.Injective (⇑lam0 : (ZMod p)ˣ → ℂˣ) := by
  intro p inst
  haveI : NeZero (Nat.card (ZMod p)ˣ) := ⟨Nat.card_pos.ne'⟩
  have hcard : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ) :=
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ (Nat.card (ZMod p)ˣ)).symm
  let e : (ZMod p)ˣ ≃* rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ := mulEquivOfCyclicCardEq hcard
  exact ⟨(rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ).subtype.comp e.toMonoidHom,
    (Subgroup.subtype_injective _).comp e.injective⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInvariantSubspace
section
theorem UpperTheory.exists_invariant_subspace :
    ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (G ι : Type) [Fintype ι] (K : Set G)
        (σ : G → H →ₗ[ℂ] H) (S : Submodule ℂ H) (E : ι → Module.End ℂ S) (c : G → ι → ι → ℂ),
        (∀ g ∈ K, ∀ v ∈ S, σ g v ∈ S) →
        (∀ g ∈ K, ∀ (i : ι) (v w : S), (w : H) = σ g (v : H) →
          σ g ((E i v : S) : H) = ∑ j, c g i j • ((E j w : S) : H)) →
        ∃ V₀ : Submodule ℂ S,
          (∀ x : S, x ∈ V₀ ↔ ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
            ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T) ∧
          ∀ i, ∀ x ∈ V₀, E i x ∈ V₀ := by
  intro H _ _ G ι _ K σ S E c hS hE
  refine ⟨{ carrier := {x : S | ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
              ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, fun x => Iff.rfl, ?_⟩
  · rintro a b ⟨T₁, f₁, ha, h₁⟩ ⟨T₂, f₂, hb, h₂⟩
    refine ⟨T₁ ⊔ T₂, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
    intro g hg v hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h₁ g hg y hy) (h₂ g hg z hz)
  · refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
    intro g _ v hv
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]
    exact Submodule.zero_mem _
  · rintro r x ⟨T, f, hx, h⟩
    exact ⟨T, f, T.smul_mem r hx, h⟩
  · rintro i x ⟨T, f, hx, h⟩
    have fU : FiniteDimensional ℂ (T.comap S.subtype) :=
      FiniteDimensional.of_injective (S.subtype.submoduleComap T) (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : T => (t : H)) hab)
    have hmem : ∀ (j : ι) (u : S), (u : H) ∈ T →
        ((E j u : S) : H) ∈ ⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k) := fun j u hu =>
      Submodule.mem_iSup_of_mem j ⟨u, hu, rfl⟩
    refine ⟨⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k), inferInstance, hmem i x hx, ?_⟩
    intro g hg v hv
    have hle : (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)) ≤
        (⨆ k, (T.comap S.subtype).map (S.subtype ∘ₗ E k)).comap (σ g) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hE g hg j u ⟨σ g u, hS g hg u u.2⟩ rfl]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (hmem k _ (h g hg u hu))
    exact hle hv
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsKill
section
theorem UpperTheory.Reformulated.B.Qk55.exists_kill.{u_1} :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {H : Type u_1}
    [inst_1 : AddCommGroup H] [inst_2 : _root_.Module ℤ_[l] H] (h : H),
    (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h = (0 : TensorProduct ℤ_[l] ℚ_[l] H) → ∃ (b : ℕ), l ^ b • h = (0 : H) := by
  intro l _ H _ _ h hh
  have h0 : TensorProduct.mk ℤ_[l] ℚ_[l] H 1 h = 0 := hh
  obtain ⟨s, hs⟩ :=
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] H 1)).1 h0
  have hs0 : (s : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hs' : (s : ℤ_[l]) • h = 0 := hs
  refine ⟨(s : ℤ_[l]).valuation, ?_⟩
  rw [PadicInt.unitCoeff_spec hs0, mul_smul] at hs'
  have h2 : ((l : ℤ_[l]) ^ (s : ℤ_[l]).valuation) • h = 0 :=
    (IsUnit.smul_eq_zero (Units.isUnit _)).1 hs'
  rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLimitOfApprox
section
theorem UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (P : ℕ → R → Prop),
    (∀ (n : ℕ) (x : R), P n x → ∃ (y : R), y - x ∈ I ^ n ∧ P (n + (1 : ℕ)) y) →
      ∀ {x₀ : R}, P (0 : ℕ) x₀ → ∃ (x : R), ∀ (n : ℕ), ∃ (y : R), P n y ∧ x - y ∈ I ^ n := by
  intro R _ I hI P h x₀ h₀
  choose g hg hP using h
  let f : (n : ℕ) → {x : R // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : R // P n x}) ⟨x₀, h₀⟩
      (fun n x => ⟨g n x.1 x.2, hP n x.1 x.2⟩) n
  have hstep : ∀ n, (f (n + 1)).1 - (f n).1 ∈ I ^ n := fun n => hg n (f n).1 (f n).2
  have hdiff : ∀ m n, m ≤ n → (f n).1 - (f m).1 ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : (f (n + 1)).1 - (f n).1 ∈ I ^ m := Ideal.pow_le_pow_right hmn (hstep n)
      have h2 := (I ^ m).add_mem h1 ih
      rwa [sub_add_sub_cancel] at h2
  have htop : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun n => (f n).1) (by
    intro m n hmn
    refine SModEq.symm ?_
    rw [SModEq.sub_mem, htop]
    exact hdiff m n hmn)
  refine ⟨L, fun n => ⟨(f n).1, (f n).2, ?_⟩⟩
  have h3 := (hL n).symm
  rwa [SModEq.sub_mem, htop] at h3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocalGenerator
section
theorem UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator :
    ∀ {B : Type} [inst : CommRing B] [IsDedekindDomain B] (I p : Ideal B) [hp : p.IsPrime],
      ∃ π ∈ I, ∃ s ∉ p, ∀ x ∈ I, s * x ∈ Ideal.span {π} := by
  intro B _ _ I p hp
  by_cases hI : I = ⊥
  · refine ⟨0, I.zero_mem, 1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun x hx => ?_⟩
    rw [hI, Ideal.mem_bot] at hx
    simp [hx]
  have hne : ¬ I ≤ I * p := by
    intro h
    have h1 : I * p = I * 1 := by
      rw [mul_one]
      exact le_antisymm Ideal.mul_le_left h
    have h2 : p = 1 := mul_left_cancel₀ (show I ≠ 0 from hI) h1
    exact hp.ne_top (by rw [h2, Ideal.one_eq_top])
  obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.mp hne
  have hle : Ideal.span {π} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJp : ¬ J ≤ p := by
    intro h
    apply hπ'
    have : π ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self π
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨π, hπ, s, hs', fun x hx => ?_⟩
  rw [hJ, mul_comm s x]
  exact Ideal.mul_mem_mul hx hs
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNatMulMem
section
theorem UpperTheory.Reformulated.B.ExistsNatMulMem.exists_nat_mul_mem :
    ∀ (F : Type) [inst : Field F] [NumberField F] (x : F),
    ∃ (m : ℕ), (0 : ℕ) < m ∧ ∃ (r : NumberField.RingOfIntegers F), (↑r : F) = (↑m : F) * x := by
  intro F _ _ x
  have hx : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hint⟩ := hx.exists_integral_multiple
  have h2 : IsIntegral ℤ (((y.natAbs : ℕ) : F) * x) := by
    rcases Int.natAbs_eq y with h | h
    · have e : ((y.natAbs : ℕ) : F) * x = y • x := by
        rw [zsmul_eq_mul]
        congr 1
        have := congrArg (Int.cast : ℤ → F) h
        rw [Int.cast_natCast] at this
        exact this.symm
      rw [e]; exact hint
    · have e : ((y.natAbs : ℕ) : F) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        have := congrArg (Int.cast : ℤ → F) h
        rw [Int.cast_neg, Int.cast_natCast] at this
        rw [this, neg_neg]
      rw [e]; exact hint.neg
  exact ⟨y.natAbs, Int.natAbs_pos.mpr hy, ⟨_, h2⟩, rfl⟩
end

