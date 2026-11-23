module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSmoothRepresentations
section
noncomputable def UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ,
        zero_mem' := UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux3 ρ H χ, smul_mem' := UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.eig ρ H (1 : ↥H →* kˣ)

noncomputable def UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsAdmissible :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsSmooth ρ ∧
        ∀ (K : Subgroup G),
          IsOpen (↑K : Set G) → IsCompact (↑K : Set G) → FiniteDimensional k ↥(UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K)

private theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed {H V : Type} [Group H] [AddCommGroup V]
    [_root_.Module ℂ V] {ρ : Representation ℂ H V} {K : Subgroup H} {v : V} :
    v ∈ UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have h' := (show ∀ h : ↥K, ρ (h : H) v = (↑((1 : ↥K →* ℂˣ) h) : ℂ) • v from h) ⟨k, hk⟩
    simpa using h'
  · intro h
    show ∀ h : ↥K, ρ (h : H) v = (↑((1 : ↥K →* ℂˣ) h) : ℂ) • v
    intro k
    simpa using h k k.2

private theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.inner_eq_zero_of_fixed {H V : Type} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ρ : Representation ℂ H V} (hsm : UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsSmooth ρ)
    (hun : ∀ (g : H) (x y : V), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    {K : Subgroup H} (hK : IsCompact (K : Set H)) (W : Subrepresentation ρ) {u : V}
    (hu : ∀ k ∈ K, ρ k u = u)
    (hperp : ∀ s ∈ W.toSubmodule, (∀ k ∈ K, ρ k s = s) → inner ℂ s u = 0)
    {w : V} (hw : w ∈ W.toSubmodule) : inner ℂ w u = 0 := by
  have hopen : ∀ x : H, IsOpen {g : H | ρ g w = ρ x w} := by
    intro x
    have h1 : IsOpen ((fun g : H => x⁻¹ * g) ⁻¹' {g : H | ρ g w = w}) :=
      (hsm w).preimage (continuous_const.mul continuous_id)
    convert h1 using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
    constructor
    · intro h
      rw [h, ← Module.End.mul_apply, ← map_mul]
      simp
    · intro h
      have h2 := congrArg (ρ x) h
      rw [← Module.End.mul_apply (ρ x), ← map_mul] at h2
      simpa using h2
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x : H => {g : H | ρ g w = ρ x w})
    (fun x _ => (hopen x).mem_nhds rfl)
  classical
  have hfin : {y : V | ∃ k ∈ K, ρ k w = y}.Finite := by
    refine (t.image (fun x => ρ x w)).finite_toSet.subset ?_
    rintro y ⟨k, hk, rfl⟩
    obtain ⟨x, hx, hkx⟩ := Set.mem_iUnion₂.mp (ht hk)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, hkx.symm⟩)
  have hO : ∀ y, y ∈ hfin.toFinset ↔ ∃ k ∈ K, ρ k w = y := by
    intro y
    simp
  have hsW : (∑ y ∈ hfin.toFinset, y) ∈ W.toSubmodule := by
    refine Submodule.sum_mem _ ?_
    intro y hy
    obtain ⟨k, -, rfl⟩ := (hO y).mp hy
    exact W.apply_mem_toSubmodule k hw
  have hsfix : ∀ k ∈ K, ρ k (∑ y ∈ hfin.toFinset, y) = ∑ y ∈ hfin.toFinset, y := by
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_nbij' (fun y => ρ k y) (fun y => ρ k⁻¹ y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := (hO y).mp hy
      refine (hO _).mpr ⟨k * l, K.mul_mem hk hl, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := (hO y).mp hy
      refine (hO _).mpr ⟨k⁻¹ * l, K.mul_mem (K.inv_mem hk) hl, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    · intro y _
      show ρ k⁻¹ (ρ k y) = y
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    · intro y _
      show ρ k (ρ k⁻¹ y) = y
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    · intro y _
      rfl
  have hsum := hperp _ hsW hsfix
  rw [sum_inner] at hsum
  have hconst : ∀ y ∈ hfin.toFinset, inner ℂ y u = inner ℂ w u := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (hO y).mp hy
    rw [← hun k w u, hu k hk]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨w, (hO w).mpr ⟨1, K.one_mem, ?_⟩⟩)
    simp
  exact (mul_eq_zero.mp hsum).resolve_left hcard

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple :
    ∀ {H : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [IsTopologicalGroup H] {V : Type}
      [inst_3 : NormedAddCommGroup V] [inst_4 : InnerProductSpace ℂ V] {ρ : Representation ℂ H V},
      UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsAdmissible ρ →
        (∀ (g : H) (x y : V),
            Inner.inner ℂ (((ρ : H → V →ₗ[ℂ] V) g : V → V) x) (((ρ : H → V →ₗ[ℂ] V) g : V → V) y) = Inner.inner ℂ x y) →
          ∀ {K₀ : Subgroup H}, IsOpen (↑K₀ : Set H) → IsCompact (↑K₀ : Set H) → ρ.IsSemisimpleRepresentation := by
  intro H _ _ _ V _ _ ρ hadm hun K₀ hK₀o hK₀c
  refine ⟨fun W => ?_⟩
  have hinv : ∀ (g : H) ⦃v : V⦄, v ∈ W.toSubmoduleᗮ → ρ g v ∈ W.toSubmoduleᗮ := by
    intro g v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro w hw
    have h1 : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [← h1, hun]
    exact hv _ (W.apply_mem_toSubmodule g⁻¹ hw)
  refine ⟨⟨W.toSubmoduleᗮ, hinv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact W.toSubmodule.inf_orthogonal_eq_bot
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule ⊔ W.toSubmoduleᗮ = ⊤
    rw [eq_top_iff]
    intro v _
    let S : Subgroup H :=
      { carrier := {g : H | ρ g v = v}
        mul_mem' := by
          intro a b ha hb
          show ρ (a * b) v = v
          rw [map_mul, Module.End.mul_apply, show ρ b v = v from hb, show ρ a v = v from ha]
        one_mem' := by
          show ρ 1 v = v
          simp
        inv_mem' := by
          intro a ha
          show ρ a⁻¹ v = v
          have h2 : ρ a⁻¹ (ρ a v) = v := by
            rw [← Module.End.mul_apply, ← map_mul]
            simp
          rwa [show ρ a v = v from ha] at h2 }
    let K : Subgroup H := K₀ ⊓ S
    have hKo : IsOpen (K : Set H) := hK₀o.inter (hadm.1 v)
    have hKc : IsCompact (K : Set H) :=
      hK₀c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
    haveI : FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K) := hadm.2 K hKo hKc
    let A : Submodule ℂ V := W.toSubmodule ⊓ UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K
    haveI : FiniteDimensional ℂ ↥A := Submodule.finiteDimensional_inf_right _ _
    haveI : CompleteSpace ↥A := FiniteDimensional.complete ℂ ↥A
    obtain ⟨a, ha, u, hu, hv⟩ := A.exists_add_mem_mem_orthogonal v
    have hafix : ∀ k ∈ K, ρ k a = a := UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed.mp ha.2
    have hufix : ∀ k ∈ K, ρ k u = u := by
      intro k hk
      have hvk : ρ k v = v := hk.2
      rw [hv, map_add (f := _), hafix k hk] at hvk
      exact add_left_cancel hvk
    have huW : u ∈ W.toSubmoduleᗮ := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      exact UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.inner_eq_zero_of_fixed hadm.1 hun hKc W hufix
        (fun s hs hsf => (Submodule.mem_orthogonal _ _).mp hu s
          ⟨hs, UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed.mpr hsf⟩) hw
    rw [hv]
    exact Submodule.add_mem_sup ha.1 huW
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AeFundamentalDomain
section
theorem UpperTheory.ae_fundamental_domain :
    ∀ {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace Q]
        (Γ : Subgroup G) [Countable Γ] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] (D : Set G) (π : G → Q),
        Measurable π → (∀ (γ : Γ) (g : G), π ((γ : G) * g) = π g) → (∀ g : G, ∃ γ : Γ, (γ : G) * g ∈ D) →
        ∀ p : Q → Prop, (∀ᵐ q ∂(MeasureTheory.Measure.map π (μ.restrict D)), p q) → ∀ᵐ y ∂μ, p (π y) := by
  intro G Q _ _ _ _ Γ _ μ _ D π hπ hinv hcov p hp
  rw [MeasureTheory.ae_iff] at hp ⊢
  obtain ⟨N, hsub, hNm, hN0⟩ := MeasureTheory.exists_measurable_superset_of_null hp
  rw [MeasureTheory.Measure.map_apply hπ hNm,
    MeasureTheory.Measure.restrict_apply (hπ hNm)] at hN0
  have hcover : {y | ¬ p (π y)} ⊆
      ⋃ γ : Γ, (fun g : G => (γ : G) * g) ⁻¹' (π ⁻¹' N ∩ D) := by
    intro y hy
    obtain ⟨γ, hγ⟩ := hcov y
    refine Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩
    show π ((γ : G) * y) ∈ N
    rw [hinv]
    exact hsub hy
  refine MeasureTheory.measure_mono_null hcover (MeasureTheory.measure_iUnion_null fun γ => ?_)
  rw [MeasureTheory.measure_preimage_mul]
  exact hN0
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AeTranslateEq
section
theorem UpperTheory.ae_translate_eq :
    ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace X]
        (μ : MeasureTheory.Measure G) [μ.IsMulRightInvariant] (ν : MeasureTheory.Measure X) (q : G → X) (ρ : X → X) (g : G)
        (v v' : X → ℂ) (φ : G → ℂ), MeasureTheory.Measure.QuasiMeasurePreserving q μ ν → (∀ y, ρ (q y) = q (y * g)) →
        (v' =ᵐ[ν] fun x => v (ρ x)) → (∀ᵐ y ∂μ, v (q y) = φ y) → ∀ᵐ y ∂μ, v' (q y) = φ (y * g) := by
  intro G X _ _ _ _ μ _ ν q ρ g v v' φ hq hρ hv hφ
  have h1 : ∀ᵐ y ∂μ, v' (q y) = v (ρ (q y)) := MeasureTheory.Measure.QuasiMeasurePreserving.ae hq hv
  have h2 : ∀ᵐ y ∂μ, v (q (y * g)) = φ (y * g) :=
    (MeasureTheory.measurePreserving_mul_right μ g).quasiMeasurePreserving.ae hφ
  filter_upwards [h1, h2] with y a b
  rw [a, hρ, b]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalComm
section
theorem UpperTheory.Reformulated.B.Qk66.aeval_comm :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (φ : M →ₗ[L] N) (A : Module.End L M) (A' : Module.End L N),
    (∀ (y : M), (φ : M → N) ((A : M → M) y) = (A' : N → N) ((φ : M → N) y)) →
      ∀ (Q : Polynomial L) (y : M),
        (φ : M → N) (((Polynomial.aeval A : Polynomial L → Module.End L M) Q : M → M) y) =
          ((Polynomial.aeval A' : Polynomial L → Module.End L N) Q : N → N) ((φ : M → N) y) := by
  intro L M N _ _ _ _ _ φ A A' h Q
  induction Q using Polynomial.induction_on with
  | C a =>
    intro y
    simp [Module.algebraMap_end_apply]
  | add p q hp hq =>
    intro y
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a ih =>
    intro y
    rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval A), map_mul (Polynomial.aeval A'),
      Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalEig
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp10.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

theorem UpperTheory.Reformulated.B.Qp10.aeval_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp10.Mat C N) (μ : C) (v : Fin N → C),
      Matrix.mulVec y v = μ • v →
        ∀ (Q : Polynomial C),
          Matrix.mulVec ((Polynomial.aeval y : Polynomial C → UpperTheory.Reformulated.B.Qp10.Mat C N) Q) v = Polynomial.eval μ Q • v := by
  intro C _ N y μ v h Q
  have hpow : ∀ n : ℕ, Matrix.mulVec (y ^ n) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ← Algebra.smul_def,
      Matrix.smul_mulVec, hpow, smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalInter
section
theorem UpperTheory.Reformulated.B.Qe22.aeval_inter :
    ∀ {M N : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M]
    [inst_2 : AddCommGroup N] [inst_3 : _root_.Module ℂ N] (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N),
    (∀ (x : M), (f : M → N) ((T : M → M) x) = (T' : N → N) ((f : M → N) x)) →
      ∀ (p : Polynomial ℂ) (x : M),
        (f : M → N) (((Polynomial.aeval T : Polynomial ℂ → Module.End ℂ M) p : M → M) x) =
          ((Polynomial.aeval T' : Polynomial ℂ → Module.End ℂ N) p : N → N) ((f : M → N) x) := by
  intro M N _ _ _ _ f T T' h p
  have hpow : ∀ (n : ℕ) (x : M), f ((T ^ n) x) = (T' ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | monomial n a =>
    intro x
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hpow]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalInterAlt
section
theorem UpperTheory.Reformulated.B.Qi58.aeval_inter :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (c : M →ₗ[L] N) (f : Module.End L M) (g : Module.End L N),
    (∀ (x : M), (c : M → N) ((f : M → M) x) = (g : N → N) ((c : M → N) x)) →
      ∀ (Q : Polynomial L) (x : M),
        (c : M → N) (((Polynomial.aeval f : Polynomial L → Module.End L M) Q : M → M) x) =
          ((Polynomial.aeval g : Polynomial L → Module.End L N) Q : N → N) ((c : M → N) x) := by
  intro L M N _ _ _ _ _ c f g h Q x
  have hp : ∀ (n : ℕ) (y : M), c ((f ^ n) y) = (g ^ n) (c y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction Q using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add (f := _), LinearMap.add_apply, hp', hq']
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hp]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalIntertwining
section
theorem UpperTheory.Reformulated.B.AevalIntertwining.aeval_intertwine :
    ∀ {K : Type} [inst : Field K] {M N : Type} [inst_1 : AddCommGroup M]
    [inst_2 : _root_.Module K M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module K N] (φ : M →ₗ[K] N)
    (f : Module.End K M) (f' : Module.End K N),
    (∀ (x : M), (φ : M → N) ((f : M → M) x) = (f' : N → N) ((φ : M → N) x)) →
      ∀ (p : Polynomial K) (x : M),
        (φ : M → N) (((Polynomial.aeval f : Polynomial K → Module.End K M) p : M → M) x) =
          ((Polynomial.aeval f' : Polynomial K → Module.End K N) p : N → N) ((φ : M → N) x) := by
  intro K _ M N _ _ _ _ φ f f' h p
  have hpow : ∀ (n : ℕ) (x : M), φ ((f ^ n) x) = (f' ^ n) (φ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    intro x
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMemInvariantSubmodule
section
theorem UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule.{u_1} :
    ∀ {Y : Type u_1} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y]
    (A : Module.End ℂ Y) (p : Submodule ℂ Y),
    (∀ y ∈ p, (A : Y → Y) y ∈ p) →
      ∀ (q : Polynomial ℂ), ∀ y ∈ p, ((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) q : Y → Y) y ∈ p := by
  intro Y _ _ A p hA q y hy
  have hpow : ∀ n : ℕ, (A ^ n) y ∈ p := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hA _ ih
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine p.sum_mem fun i _ => ?_
  rw [LinearMap.smul_apply]
  exact p.smul_mem _ (hpow i)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMulHomog
section
theorem UpperTheory.Reformulated.B.Qk4.aeval_mul_homog :
    ∀ {n : ℕ} {A G S : Type} [inst : CommRing A]
    [inst_1 : CommRing S] [inst_2 : Algebra A S] {P : MvPolynomial G A},
    P.IsHomogeneous n →
      ∀ (b : S) (x : G → S),
        (MvPolynomial.aeval fun (g : G) ↦ b * x g : MvPolynomial G A → S) P =
          b ^ n * (MvPolynomial.aeval x : MvPolynomial G A → S) P := by
  intro n A G S _ _ _ P hP b x
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hP (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMulOfIsHomogeneous
section
theorem UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous :
    ∀ {σ R : Type} [Fintype σ]
    [inst : CommRing R] [inst_1 : Algebra ℚ R] {P : MvPolynomial σ ℚ} {d : ℕ},
    P.IsHomogeneous d →
      ∀ (y : R) (g : σ → R),
        (MvPolynomial.aeval fun (k : σ) ↦ y * g k : MvPolynomial σ ℚ → R) P =
          y ^ d * (MvPolynomial.aeval g : MvPolynomial σ ℚ → R) P := by
  intro σ R _ _ _ P d hP y g
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : s.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 hs) (hP.coeff_eq_zero h)
  have h2 : ∑ i, s i = d := by
    rw [← h1, Finsupp.degree_eq_sum]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h2]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPF
section
noncomputable def UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF :
    {A : Type} → [inst : Ring A] → [Algebra ℂ A] → (ℂ → A) → Prop :=
  fun {A} _ _ f => ∃ p : Polynomial A, ∀ Y : ℂ, f Y = Polynomial.eval (algebraMap ℂ A Y) p
end

