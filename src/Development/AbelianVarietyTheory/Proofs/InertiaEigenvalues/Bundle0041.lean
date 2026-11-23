module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqTopOfIrreducibleOverAlgClosed
section
open IsLocalRing Matrix

namespace GlobalTheory.BurnsideMonoid

open scoped MonoidAlgebra

theorem span_range_eq_top_of_isIrreducible {G K V : Type} [Monoid G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  classical
  have hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  have hsurj : Function.Surjective τ.asAlgebraHom := by
    intro f
    let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
      { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
        map_add' := fun x y => by simp
        map_smul' := fun φ m => by
          obtain ⟨c, hc⟩ := hscal φ
          simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F
      (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
    refine ⟨r, b.ext fun i => ?_⟩
    have := congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact this.symm
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single g c =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem span_matrix_eq_top_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Monoid Γ] (σ : Γ →* Matrix ι ι K)
    (h : ∀ W : Submodule K (ι → K), (∀ g, ∀ w ∈ W, σ g *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Submodule.span K (Set.range σ) = ⊤ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
  let τ : Representation K Γ (ι → K) :=
    { toFun := fun g => Matrix.toLin' (σ g)
      map_one' := by simp; rfl
      map_mul' := fun g g' => by simp [Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => ?_⟩
      have h1 : (⊥ : Submodule K (ι → K)) = ⊤ := congrArg Subrepresentation.toSubmodule hbt
      exact bot_ne_top h1
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isIrreducible τ hirr
  have hm : Set.range σ =
      (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

end GlobalTheory.BurnsideMonoid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOrbitEqTop
section
namespace GlobalTheory.SpanOrbitTop

theorem span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : Representation.IsIrreducible π) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G ↦ π g v) = ⊤ := by
  have hinv : ∀ (h : G) ⦃x : V⦄, x ∈ Submodule.span ℂ (Set.range fun g : G ↦ π g v) →
      π h x ∈ Submodule.span ℂ (Set.range fun g : G ↦ π g v) := by
    intro h x hx
    have hle : (Submodule.span ℂ (Set.range fun g : G ↦ π g v)).map (π h) ≤
        Submodule.span ℂ (Set.range fun g : G ↦ π g v) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span ⟨h * g, by simp [map_mul]⟩
    exact hle (Submodule.mem_map_of_mem hx)
  let S : Subrepresentation π := ⟨Submodule.span ℂ (Set.range fun g : G ↦ π g v), hinv⟩
  have hvS : v ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have := hπ
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    have hb : v ∈ (⊥ : Subrepresentation π).toSubmodule := h ▸ hvS
    exact hv ((Submodule.mem_bot ℂ).mp hb)
  · exact congrArg Subrepresentation.toSubmodule h

end GlobalTheory.SpanOrbitTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowersOfUniformizerOfNilpotent
section
open Polynomial

namespace GlobalTheory

theorem span_powers_of_uniformizer_of_nilpotent :
    ∀ (C B : Type) [CommRing C] [CommRing B] (φ : C →+* B) (π : B) (L : C) (e m : ℕ),
      (∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π}) → π ^ e ∈ Ideal.span {φ L} → φ L ^ m = 0 →
      ∀ x : B, ∃ c : Fin e → C, x = ∑ j, φ (c j) * π ^ (j : ℕ) := by
  intro C B _ _ φ π L e m hsurj he hm
  have step1 : ∀ k : ℕ, ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range k, φ (c j) * π ^ j + π ^ k * w := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, x, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨c, w, hx⟩ := ih x
      obtain ⟨y, hy⟩ := hsurj w
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy
      refine ⟨fun j => if j = k then y else c j, z, ?_⟩
      rw [Finset.sum_range_succ]
      beta_reduce
      rw [if_pos rfl]
      have hsum : ∑ j ∈ Finset.range k, φ (if j = k then y else c j) * π ^ j
          = ∑ j ∈ Finset.range k, φ (c j) * π ^ j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_neg (Finset.mem_range.mp hj).ne]
      rw [hsum, hx]
      have hw : w = φ y + z * π := by rw [hz]; ring
      rw [hw]; ring
  have step1' : ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L * w := by
    intro x
    obtain ⟨c, w, hx⟩ := step1 e x
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp he
    exact ⟨c, u * w, by rw [hx, ← hu]; ring⟩
  have step2 : ∀ n : ℕ, ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L ^ n * w := by
    intro n
    induction n with
    | zero => intro x; exact ⟨0, x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨c, w, hx⟩ := ih x
      obtain ⟨d, w', hw⟩ := step1' w
      refine ⟨fun j => c j + L ^ n * d j, w', ?_⟩
      have key : ∑ j ∈ Finset.range e, φ (c j + L ^ n * d j) * π ^ j
          = ∑ j ∈ Finset.range e, φ (c j) * π ^ j
            + φ L ^ n * ∑ j ∈ Finset.range e, φ (d j) * π ^ j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_add (f := _), map_mul, map_pow]
        ring
      rw [key, hx, hw]
      ring
  intro x
  obtain ⟨c, w, hx⟩ := step2 m x
  refine ⟨fun j => c j, ?_⟩
  rw [hx, hm, zero_mul, add_zero]
  exact (Fin.sum_univ_eq_sum_range (fun j => φ (c j) * π ^ j) e).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl
section
open Filter Topology

namespace GlobalTheory

theorem spectralNorm_closedBall_isOpen_isCompact_nhds_basis : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by
  intro F _ _ _ _ L _ _ _ τ _
  have hcs : ContinuousSMul F L := IsModuleTopology.toContinuousSMul F L
  have hca : ContinuousAdd L := IsModuleTopology.toContinuousAdd F L
  have htg : IsTopologicalAddGroup L :=
    { continuous_neg := by
        have : (fun x : L => -x) = fun x => (-1 : F) • x := by funext x; simp
        rw [this]; exact continuous_const.smul continuous_id }
  let N : NormedAddCommGroup L := spectralNorm.normedAddCommGroup F L
  let NS : NormedSpace F L := spectralNorm.normedSpace F L
  let τ' : TopologicalSpace L := N.toUniformSpace.toTopologicalSpace
  have h1 : τ ≤ τ' := by
    rw [← continuous_id_iff_le]
    exact @IsModuleTopology.continuous_of_linearMap F _ _ L _ _ τ _ L _ _ τ' inferInstance inferInstance LinearMap.id
  have h2 : τ' ≤ τ := by
    rw [← continuous_id_iff_le]
    exact @LinearMap.continuous_of_finiteDimensional F _ L _ _ τ' inferInstance inferInstance L _ _ τ htg hcs _ inferInstance _ (LinearMap.id)
  have hτ : τ = τ' := le_antisymm h1 h2
  subst hτ
  have hU : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean_spectralNorm (K := F) (L := L))
  have hPF : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hPL : ProperSpace L := FiniteDimensional.proper F L
  have hd : ∀ y : L, dist y 0 = spectralNorm F L y := fun y => by
    rw [dist_zero_right]; rfl
  have hS : {y : L | spectralNorm F L y ≤ 1} = Metric.closedBall (0 : L) 1 := by
    ext y; simp only [Set.mem_setOf_eq, Metric.mem_closedBall, hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  · rw [hS]; exact isCompact_closedBall _ _
  · intro U hU0
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hU0
    exact ⟨ε, hε, fun y hy => hb (by rw [Metric.mem_ball, hd]; exact hy)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpeiserDescentSpan
section
namespace GlobalTheory

open Finset

theorem ringHom_evalVectors_span_eq_top {L Ω : Type} [Field L] [Field Ω]
    (S : Set (L →+* Ω)) [Fintype S] :
    Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  have hli : LinearIndependent Ω (fun h : S => ((h : L →+* Ω) : L → Ω)) := by
    have := (linearIndependent_monoidHom L Ω).comp
      (fun h : S => ((h : L →+* Ω) : L →* Ω)) (by
        intro x y hxy
        apply Subtype.ext
        apply RingHom.ext
        intro c
        exact DFunLike.congr_fun hxy c)
    exact this
  rw [Fintype.linearIndependent_iff] at hli
  apply hf0
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  have hc : ∀ h : S, f (fun j => if h = j then (1 : Ω) else 0) = 0 := by
    apply hli
    funext c
    have hmem : (fun h : S => (h : L →+* Ω) c) ∈
        Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) :=
      Submodule.subset_span ⟨c, rfl⟩
    have h0 : f (fun h : S => (h : L →+* Ω) c) = 0 := by
      have : f (fun h : S => (h : L →+* Ω) c) ∈ Submodule.map f
          (Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c)) :=
        Submodule.mem_map_of_mem hmem
      rw [hf] at this
      exact (Submodule.mem_bot Ω).mp this
    rw [LinearMap.pi_apply_eq_sum_univ f] at h0
    simpa [Finset.sum_apply, mul_comm] using h0
  simp [hc]

theorem speiser_descent_span :
    ∀ {G L Ω M : Type} [Group G] [Field L] [Field Ω] [Algebra L Ω] [AddCommGroup M] [Module Ω M]
      [Module L M] [IsScalarTower L Ω M] (b : G → Ω → Ω) (a : G → L →+* Ω) (σ : G → M →+ M)
      (W : Submodule L M), (∀ g h c, a (g * h) c = b g (a h c)) →
      (∀ c, a 1 c = algebraMap L Ω c) → (∀ m, σ 1 m = m) →
      (∀ g h m, σ (g * h) m = σ g (σ h m)) → (∀ g (c : L) m, σ g (c • m) = a g c • σ g m) →
      (Set.range a).Finite → (∀ g, ∀ m ∈ W, σ g m ∈ W) →
      (∀ g, (∀ c, a g c = algebraMap L Ω c) → ∀ m ∈ W, σ g m = m) →
      ∀ m ∈ W, m ∈ Submodule.span Ω {m | m ∈ W ∧ ∀ g, σ g m = m} := by
  intro G L Ω M _ _ _ _ _ _ _ _ b a σ W hb ha1 _hσ1 hσmul hσsmul hfin hstab hker m hm
  classical
  let S : Set (L →+* Ω) := Set.range a
  haveI : Fintype S := hfin.fintype
  have hrep : ∀ h : S, ∃ g, a g = h := fun h => h.2
  choose gs hgs using hrep
  have hleft : ∀ g x c, a x c = b g⁻¹ (a (g * x) c) := by
    intro g x c; rw [← hb, inv_mul_cancel_left]
  let δ : S → Ω := fun h => if (h : L →+* Ω) = a 1 then 1 else 0
  have hδ : δ ∈ Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) := by
    rw [ringHom_evalVectors_span_eq_top S]; trivial
  obtain ⟨β, hβ⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hδ
  have hβh : ∀ h : S, ∑ c ∈ β.support, β c * (h : L →+* Ω) c = δ h := by
    intro h
    have := congrFun hβ h
    simpa [Finsupp.sum, Finset.sum_apply] using this
  let t : L → M := fun c => ∑ h : S, σ (gs h) (c • m)
  have htW : ∀ c, t c ∈ W := fun c => W.sum_mem fun h _ => hstab _ _ (W.smul_mem c hm)
  have hperm : ∀ g : G, ∀ y ∈ W, σ g (∑ h : S, σ (gs h) y) = ∑ h : S, σ (gs h) y := by
    intro g y hy
    let π : S → S := fun h => ⟨a (g * gs h), Set.mem_range_self _⟩
    have hπ : Function.Injective π := by
      intro h1 h2 e
      have e' : a (g * gs h1) = a (g * gs h2) := congrArg Subtype.val e
      have : a (gs h1) = a (gs h2) := by
        ext c; rw [hleft g (gs h1) c, hleft g (gs h2) c, e']
      apply Subtype.ext
      rw [← hgs h1, ← hgs h2, this]
    have hbij : Function.Bijective π := Finite.injective_iff_bijective.1 hπ
    have hsw : ∀ h, σ (g * gs h) y = σ (gs (π h)) y := by
      intro h
      have hk : a (gs (π h)) = a (g * gs h) := hgs (π h)
      have hu : ∀ c, a ((gs (π h))⁻¹ * (g * gs h)) c = algebraMap L Ω c := by
        intro c
        rw [hb, ← hk, ← hb, inv_mul_cancel, ha1]
      calc σ (g * gs h) y = σ (gs (π h) * ((gs (π h))⁻¹ * (g * gs h))) y := by
            rw [mul_inv_cancel_left]
        _ = σ (gs (π h)) (σ ((gs (π h))⁻¹ * (g * gs h)) y) := hσmul _ _ _
        _ = σ (gs (π h)) y := by rw [hker _ hu y hy]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [← hσmul, hsw]
    exact Function.Bijective.sum_comp hbij (fun h => σ (gs h) y)
  have htinv : ∀ c g, σ g (t c) = t c := fun c g => hperm g _ (W.smul_mem c hm)
  have h1S : a 1 ∈ S := Set.mem_range_self 1
  have hrec : ∑ c ∈ β.support, β c • t c = m := by
    have e1 : ∑ c ∈ β.support, β c • t c = ∑ h : S, δ h • σ (gs h) m := by
      simp only [t, Finset.smul_sum, hσsmul, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Finset.sum_smul, hgs h, hβh h]
    rw [e1, Fintype.sum_eq_single ⟨a 1, h1S⟩]
    · have hg1 : ∀ c, a (gs ⟨a 1, h1S⟩) c = algebraMap L Ω c := by
        intro c; rw [hgs]; exact ha1 c
      simp only [δ, if_pos rfl, one_smul]
      exact hker _ hg1 m hm
    · intro h hne
      have : (h : L →+* Ω) ≠ a 1 := fun e => hne (Subtype.ext e)
      simp [δ, this]
  rw [← hrec]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨htW c, htinv c⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubOneBijectiveQuotientOfTopNilpotent
section
namespace GlobalTheory

theorem sub_one_bijective_quotient_of_topNilpotent :
    ∀ (N : Type) [AddCommGroup N] (p : ℕ) (Φ : N →+ N) (M D : AddSubgroup N) (F : ℕ → AddSubgroup N), D ≤ M → (∀ x ∈ M, Φ x ∈ M) → (∀ x ∈ D, Φ x ∈ D) → (∀ m, ∀ x ∈ F m, Φ x ∈ F (m + 1)) → (∀ m, F (m + 1) ≤ F m) → (∀ x, p • x ∈ M → x ∈ M) → (∀ x, p • x ∈ D → x ∈ D) → (∀ f : ℕ → N, (∀ i, f i ∈ M) → (∀ i, f i ∈ F i) → ∃ s ∈ M, ∀ m, s - ∑ i ∈ Finset.range m, f i ∈ F m) → (∀ x, (∀ m, ∃ d ∈ D, x - d ∈ F m) → ∃ d ∈ D, ∃ r, x - d = p • r) → (∀ y ∈ M, ∃ j : ℕ, ∃ d ∈ D, Φ^[j] y - d ∈ F 0) → (∀ x : ℕ → N, (∀ i, x i ∈ M) → ∃ s ∈ M, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, p ^ i • x i = p ^ k • r) → (∀ x, (∀ k : ℕ, ∃ d ∈ D, ∃ r, x - d = p ^ k • r) → x ∈ D) → (∀ y ∈ M, ∃ z ∈ M, y - (Φ z - z) ∈ D) ∧ (∀ z ∈ M, Φ z - z ∈ D → z ∈ D) := by
  intro N _ p Φ M D F hDM hΦM hΦD hΦF hFmono hpM hpD hFcomp hFclosed hnil hpcomp hpclosed
  have hiterM : ∀ (i : ℕ) (x : N), x ∈ M → Φ^[i] x ∈ M := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih => intro x hx; rw [Function.iterate_succ_apply']; exact hΦM _ (ih x hx)
  have htel : ∀ (x : N) (m : ℕ), Φ (∑ i ∈ Finset.range m, Φ^[i] x) - ∑ i ∈ Finset.range m, Φ^[i] x = Φ^[m] x - x := by
    intro x m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, map_add (f := _), Function.iterate_succ_apply']
      have hsplit : ∀ a b : N, Φ a + Φ b - (a + b) = (Φ a - a) + (Φ b - b) := fun a b => by abel
      rw [hsplit, ih]
      abel
  have step : ∀ z ∈ M, Φ z - z ∈ D → ∃ d ∈ D, ∃ r, z - d = p • r ∧ r ∈ M ∧ Φ r - r ∈ D := by
    intro z hzM hzD
    have hiter : ∀ j : ℕ, Φ^[j] z - z ∈ D := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        have h : Φ (Φ^[j] z) - z = Φ (Φ^[j] z - z) + (Φ z - z) := by rw [map_sub]; abel
        rw [h]
        exact D.add_mem (hΦD _ ih) hzD
    have happrox : ∀ m, ∃ d ∈ D, z - d ∈ F m := by
      intro m
      induction m with
      | zero =>
        obtain ⟨j, d, hd, hj⟩ := hnil z hzM
        refine ⟨d - (Φ^[j] z - z), D.sub_mem hd (hiter j), ?_⟩
        have h : z - (d - (Φ^[j] z - z)) = Φ^[j] z - d := by abel
        rw [h]
        exact hj
      | succ m ih =>
        obtain ⟨d, hd, hm⟩ := ih
        refine ⟨Φ d - (Φ z - z), D.sub_mem (hΦD d hd) hzD, ?_⟩
        have h : z - (Φ d - (Φ z - z)) = Φ (z - d) := by rw [map_sub]; abel
        rw [h]
        exact hΦF m _ hm
    obtain ⟨d, hd, r, hr⟩ := hFclosed z happrox
    have hpr : p • r ∈ M := by rw [← hr]; exact M.sub_mem hzM (hDM hd)
    refine ⟨d, hd, r, hr, hpM r hpr, hpD _ ?_⟩
    have h : p • (Φ r - r) = (Φ z - z) - (Φ d - d) := by
      rw [smul_sub, ← map_nsmul, ← hr, map_sub]
      abel
    rw [h]
    exact D.sub_mem hzD (D.sub_mem (hΦD d hd) hd)
  have hinj : ∀ z ∈ M, Φ z - z ∈ D → z ∈ D := by
    intro z hzM hzD
    have key : ∀ k : ℕ, ∃ d ∈ D, ∃ r, z - d = p ^ k • r ∧ r ∈ M ∧ Φ r - r ∈ D := by
      intro k
      induction k with
      | zero => exact ⟨0, D.zero_mem, z, by simp, hzM, hzD⟩
      | succ k ih =>
        obtain ⟨d, hd, r, hr, hrM, hrD⟩ := ih
        obtain ⟨d', hd', r', hr', hr'M, hr'D⟩ := step r hrM hrD
        refine ⟨d + p ^ k • d', D.add_mem hd (nsmul_mem hd' _), r', ?_, hr'M, hr'D⟩
        calc z - (d + p ^ k • d') = p ^ k • (r - d') := by rw [smul_sub, ← hr]; abel
          _ = p ^ (k + 1) • r' := by rw [hr', pow_succ, mul_smul]
    apply hpclosed
    intro k
    obtain ⟨d, hd, r, hr, -, -⟩ := key k
    exact ⟨d, hd, r, hr⟩
  have step1 : ∀ y ∈ M, ∃ z ∈ M, ∃ d ∈ D, ∃ r, y - (Φ z - z) - d = p • r := by
    intro y hyM
    obtain ⟨j, d, hd, hj⟩ := hnil y hyM
    obtain ⟨e, he⟩ : ∃ e, e = Φ^[j] y - d := ⟨_, rfl⟩
    rw [← he] at hj
    have heM : e ∈ M := by rw [he]; exact M.sub_mem (hiterM j y hyM) (hDM hd)
    have hfF : ∀ i, Φ^[i] e ∈ F i := by
      intro i
      induction i with
      | zero => simpa using hj
      | succ i ih => rw [Function.iterate_succ_apply']; exact hΦF i _ ih
    obtain ⟨s, hsM, hs⟩ := hFcomp (fun i => Φ^[i] e) (fun i => hiterM i e heM) hfF
    have hx : ∀ m, Φ s - s + e ∈ F m := by
      intro m
      have hsm : s - ∑ i ∈ Finset.range m, Φ^[i] e ∈ F m := hs m
      have ht := htel e m
      generalize ∑ i ∈ Finset.range m, Φ^[i] e = S at hsm ht
      have h : Φ s - s + e = (Φ (s - S) - (s - S)) + Φ^[m] e := by
        rw [map_sub, ← sub_add_cancel (Φ^[m] e) e, ← ht]
        abel
      rw [h]
      exact add_mem (sub_mem (hFmono m (hΦF m _ hsm)) hsm) (hfF m)
    obtain ⟨d', hd', r, hr⟩ := hFclosed (Φ s - s + e) (fun m => ⟨0, D.zero_mem, by rw [sub_zero]; exact hx m⟩)
    refine ⟨-(∑ i ∈ Finset.range j, Φ^[i] y + s),
      M.neg_mem (M.add_mem (sum_mem fun i _ => hiterM i y hyM) hsM), d + d', D.add_mem hd hd', r, ?_⟩
    have hT := htel y j
    generalize ∑ i ∈ Finset.range j, Φ^[i] y = T at hT ⊢
    rw [← hr, map_neg, map_add (f := _), he, show Φ^[j] y = Φ T - T + y by rw [hT]; abel]
    abel
  choose! Z hZM Dd hDd R hR using step1
  have hRM : ∀ y ∈ M, R y ∈ M := by
    intro y hy
    apply hpM
    rw [← hR y hy]
    exact M.sub_mem (M.sub_mem hy (M.sub_mem (hΦM _ (hZM y hy)) (hZM y hy))) (hDM (hDd y hy))
  have hsurj : ∀ y ∈ M, ∃ z ∈ M, y - (Φ z - z) ∈ D := by
    intro y hyM
    have hys : ∀ k, R^[k] y ∈ M := by
      intro k
      induction k with
      | zero => simpa using hyM
      | succ k ih => rw [Function.iterate_succ_apply']; exact hRM _ ih
    have hexp : ∀ k, y - ∑ i ∈ Finset.range k, p ^ i • (Φ (Z (R^[i] y)) - Z (R^[i] y))
        - ∑ i ∈ Finset.range k, p ^ i • Dd (R^[i] y) = p ^ k • R^[k] y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Function.iterate_succ_apply', pow_succ,
          mul_smul, ← hR _ (hys k), smul_sub (p ^ k) (R^[k] y - _), smul_sub (p ^ k) (R^[k] y), ← ih]
        abel
    obtain ⟨W, hWM, hW⟩ := hpcomp (fun i => Z (R^[i] y)) (fun i => hZM _ (hys i))
    refine ⟨W, hWM, hpclosed _ ?_⟩
    intro k
    obtain ⟨r, hr⟩ := hW k
    refine ⟨∑ i ∈ Finset.range k, p ^ i • Dd (R^[i] y),
      sum_mem fun i _ => nsmul_mem (hDd _ (hys i)) _, R^[k] y - (Φ r - r), ?_⟩
    have hsum : Φ (∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y)) - ∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y)
        = ∑ i ∈ Finset.range k, p ^ i • (Φ (Z (R^[i] y)) - Z (R^[i] y)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_nsmul, smul_sub]
    have hWe : W = ∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y) + p ^ k • r := by rw [← hr]; abel
    rw [hWe, map_add (f := _), map_nsmul, smul_sub (p ^ k) (R^[k] y), smul_sub (p ^ k) (Φ r), ← hexp k, ← hsum]
    abel
  exact ⟨hsurj, hinj⟩

end GlobalTheory
end

