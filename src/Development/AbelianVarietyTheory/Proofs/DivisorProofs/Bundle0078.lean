module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationSubalgebraFrac
section
open IsLocalRing

namespace GlobalTheory

theorem localization_subalgebra_frac :
  ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (C : Subalgebra R B), (∀ c ∈ C, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C, s ∉ Q ∧ s * c = 0) → ∃ V : Subalgebra R (Localization.AtPrime Q), (∀ x : Localization.AtPrime Q, x ∈ V ↔ ∃ a ∈ C, ∃ s ∈ C, s ∉ Q ∧ x * algebraMap B (Localization.AtPrime Q) s = algebraMap B (Localization.AtPrime Q) a) ∧ Nonempty (Localization.AtPrime (Q.comap (C.val : C →ₐ[R] B)) ≃ₐ[R] V) := by
  intro R B _ _ _ Q _ C hann
  set P : Ideal C := Q.comap (C.val : C →ₐ[R] B) with hP
  let φ0 : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (C.val : C →+* B) rfl
  have hmk : ∀ (c : C) (s : P.primeCompl), φ0 (IsLocalization.mk' _ c s) =
      IsLocalization.mk' (Localization.AtPrime Q) (c : B) (⟨(s : C), s.2⟩ : Q.primeCompl) := by
    intro c s
    exact Localization.localRingHom_mk' P Q (C.val : C →+* B) rfl c s
  let φ : Localization.AtPrime P →ₐ[R] Localization.AtPrime Q :=
    { φ0 with
      commutes' := by
        intro r
        have h1 : algebraMap R (Localization.AtPrime P) r = algebraMap C (Localization.AtPrime P) (algebraMap R C r) :=
          IsScalarTower.algebraMap_apply R C _ r
        have h2 := Localization.localRingHom_to_map P Q (C.val : C →+* B) rfl (algebraMap R C r)
        show φ0 (algebraMap R (Localization.AtPrime P) r) = _
        rw [h1, h2, IsScalarTower.algebraMap_apply R B (Localization.AtPrime Q) r]
        rfl }
  have hφ : ∀ x, φ x = φ0 x := fun _ => rfl
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [hφ, hmk, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htc⟩ := hx
    obtain ⟨s', hs'C, hs'Q, hs'c⟩ := hann c c.2 t ht htc
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨⟨s', hs'C⟩, hs'Q⟩, ?_⟩
    apply Subtype.ext
    simpa using hs'c
  refine ⟨φ.range, ?_, ⟨(AlgEquiv.ofInjective φ hinj)⟩⟩
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    refine ⟨c, c.2, (s : C), (s : C).2, s.2, ?_⟩
    show φ0 (IsLocalization.mk' (Localization.AtPrime P) c s) * _ = _
    rw [hmk]
    exact IsLocalization.mk'_spec (Localization.AtPrime Q) (c : B) (⟨(s : C), s.2⟩ : Q.primeCompl)
  · rintro ⟨a, ha, s, hs, hsQ, hx⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) (⟨a, ha⟩ : C) (⟨⟨s, hs⟩, hsQ⟩ : P.primeCompl), ?_⟩
    show φ0 _ = x
    rw [hmk]
    symm
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorMapInjectiveCokerKilled
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem localization_map_injective_coker_killed (R A B : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B) :
    Function.Injective ψ → ∀ s : R, s ≠ 0 → (∀ b : B, s • b ∈ ψ.range) →
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) ∧
      algebraMap R (Localization.AtPrime p) s ≠ 0 ∧
      ∀ y : Localization.AtPrime p ⊗[R] B, algebraMap R (Localization.AtPrime p) s • y ∈
        (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ).range := by
  intro hψ s hs hrange
  set L := Localization.AtPrime p
  refine ⟨?_, ?_, ?_⟩
  · have heq : ((Algebra.TensorProduct.map (AlgHom.id L L) ψ).toLinearMap.restrictScalars R) =
        LinearMap.lTensor L ψ.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      simp
    have : Function.Injective (LinearMap.lTensor L ψ.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hψ
    rw [← heq] at this
    exact this
  · intro h0
    apply hs
    have hinj : Function.Injective (algebraMap R L) :=
      IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors p)
    exact hinj (by rw [h0, map_zero])
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      obtain ⟨a, ha⟩ := hrange b
      refine ⟨t ⊗ₜ a, ?_⟩
      have ha' : ψ a = s • b := ha
      change Algebra.TensorProduct.map (AlgHom.id L L) ψ (t ⊗ₜ a) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ha', TensorProduct.smul_tmul', algebraMap_smul,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      rw [smul_add]
      exact Subalgebra.add_mem _ hx hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedModuleMemAnnSpanSmulTop
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem localizedModule_mem_annSpan_smul_top (D : Type) [CommRing D] (S : Submonoid D) (x : D)
    (N : Type 1) [AddCommGroup N] [Module D N]
    (h : ∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) :
    ∀ n : LocalizedModule S N, algebraMap D (Localization S) x • n = 0 →
      n ∈ Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} •
        (⊤ : Submodule (Localization S) (LocalizedModule S N)) := by
  intro n hn
  set J : Ideal (Localization S) :=
    Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} with hJ
  have hIJ : Ideal.span {a : D | x * a = 0} ≤ J.comap (algebraMap D (Localization S)) := by
    rw [Ideal.span_le]
    intro a ha
    show algebraMap D (Localization S) a ∈ J
    apply Ideal.subset_span
    show algebraMap D (Localization S) x * algebraMap D (Localization S) a = 0
    rw [← map_mul, show x * a = 0 from ha, map_zero]
  have key : Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N) ≤
      ((J • (⊤ : Submodule (Localization S) (LocalizedModule S N))).restrictScalars D).comap
        (LocalizedModule.mkLinearMap S N) := by
    rw [Submodule.smul_le]
    intro r hr m _
    show LocalizedModule.mk (r • m) 1 ∈ J • (⊤ : Submodule (Localization S) (LocalizedModule S N))
    rw [← LocalizedModule.smul'_mk, ← algebraMap_smul (Localization S) r]
    exact Submodule.smul_mem_smul (hIJ hr) trivial
  induction n using LocalizedModule.induction_on with
  | _ m s =>
    rw [algebraMap_smul (Localization S) x, LocalizedModule.smul'_mk,
      ← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq] at hn
    obtain ⟨u, hu⟩ := hn
    simp only [one_smul, smul_zero] at hu
    have hxu : x • (u • m) = 0 := by rw [smul_comm]; exact hu
    have hmem := key (h _ hxu)
    have he : LocalizedModule.mk m s =
        (Localization.mk 1 (u * s) : Localization S) • LocalizedModule.mk (u • m) 1 := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one, LocalizedModule.mk_cancel_common_left]
    rw [he]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedPresentationEvalQuotientFraction
section
namespace GlobalTheory

open MvPolynomial

theorem exists_eval₂_fraction_of_exists_mod_nilpotent : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  intro R B _ _ c J n hn m r hgen
  let S : Subring B :=
    { carrier := {g | ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P}
      mul_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * P₂, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      one_mem' := ⟨1, 1, by simp, by simp⟩
      add_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      neg_mem' := by
        rintro a ⟨P, Q, hQ, h⟩
        refine ⟨-P, Q, hQ, ?_⟩
        rw [eval₂_neg, ← h]; ring }
  have hS : ∀ g, g ∈ S ↔ ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P := fun g => Iff.rfl
  have hcS : ∀ a : R, c a ∈ S := fun a => (hS _).2 ⟨C a, 1, by simp, by simp⟩
  set I := Ideal.map c J with hI
  have hdec : ∀ b : B, ∃ s ∈ S, b - s ∈ I := by
    intro b
    obtain ⟨P, Q, hQ, hb⟩ := hgen b
    obtain ⟨u, hu⟩ := hQ
    refine ⟨eval₂ c r P * ↑u⁻¹, (hS _).2 ⟨P, Q, ⟨u, hu⟩, ?_⟩, ?_⟩
    · rw [← hu, mul_assoc, Units.inv_mul, mul_one]
    · have h1 : (↑u⁻¹ : B) * ↑u = 1 := Units.inv_mul u
      have : b - eval₂ c r P * ↑u⁻¹ = ↑u⁻¹ * (b * eval₂ c r Q - eval₂ c r P) := by
        rw [← hu]; linear_combination (-b) * h1
      rw [this]; exact I.mul_mem_left _ hb
  have hstep : ∀ k : ℕ, ∀ x ∈ I ^ k, ∃ s ∈ S, x - s ∈ I ^ (k + 1) := by
    intro k x hx
    have hIk : I ^ k = Ideal.span (c '' ↑(J ^ k)) := by rw [hI, ← Ideal.map_pow]; rfl
    rw [hIk] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, -, rfl⟩ := hy
      exact ⟨c j, hcS j, by simp⟩
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hys⟩ := hy
      obtain ⟨t, ht, hzt⟩ := hz
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      have := Ideal.add_mem _ hys hzt
      convert this using 1; ring
    | smul b y hy ih =>
      obtain ⟨s, hs, hys⟩ := ih
      obtain ⟨t, ht, hbt⟩ := hdec b
      refine ⟨t * s, S.mul_mem ht hs, ?_⟩
      have hy' : y ∈ I ^ k := hIk ▸ hy
      have h1 : (b - t) * y ∈ I ^ (k + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hbt hy'
      have h2 : t * (y - s) ∈ I ^ (k + 1) := Ideal.mul_mem_left _ _ hys
      have := Ideal.add_mem _ h1 h2
      rw [smul_eq_mul]
      convert this using 1; ring
  have hall : ∀ k : ℕ, ∀ g : B, ∃ s ∈ S, g - s ∈ I ^ k := by
    intro k
    induction k with
    | zero => intro g; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro g
      obtain ⟨s, hs, hgs⟩ := ih g
      obtain ⟨t, ht, hxt⟩ := hstep k _ hgs
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      convert hxt using 1; ring
  have hIn : I ^ n = ⊥ := by
    rw [hI, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker]
    exact hn x hx
  intro g
  obtain ⟨s, hs, hgs⟩ := hall n g
  rw [hIn, Ideal.mem_bot, sub_eq_zero] at hgs
  exact (hS g).1 (hgs ▸ hs)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantCompactSupportInvariantOpenAddSub
section
namespace GlobalTheory

open Filter Topology

theorem locallyConstant_compactSupport_invariant_openAddSubgroup :
    ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
      [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g →
      ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by
  intro X _ _ _ _ g hg hc
  have key : ∀ z : X, ∃ V : OpenAddSubgroup X, ∀ h ∈ V, g (z + h) = g z := by
    intro z
    have hT : Tendsto (fun h : X => z + h) (𝓝 0) (𝓝 z) := by
      have := (continuous_const_add z).tendsto (0 : X)
      simpa using this
    have hn : {h : X | g (z + h) = g z} ∈ 𝓝 (0 : X) := hT.eventually (hg.eventually_eq z)
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hn
    exact ⟨V, fun h hh => hV hh⟩
  choose H hH using key
  have hU : ∀ j y, y - j ∈ H j → g y = g j := by
    intro j y h
    have := hH j (y - j) h
    have e : j + (y - j) = y := by abel
    rwa [e] at this
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun z : X => {y : X | y - z ∈ H z})
    (fun z => (H z).isOpen.preimage (continuous_id.sub continuous_const))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine ⟨t.inf H, fun z a ha => ?_⟩
  have hle : ∀ j ∈ t, a ∈ H j := fun j hj => Finset.inf_le (f := H) hj ha
  by_cases hz : z ∈ tsupport g
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 (ht hz)
    have h1 : z - j ∈ H j := hzj
    have h2 : z + a - j ∈ H j := by
      have := (H j).add_mem h1 (hle j hj)
      have e : z - j + a = z + a - j := by abel
      rwa [e] at this
    rw [hU j _ h2, hU j _ h1]
  by_cases hza : z + a ∈ tsupport g
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 (ht hza)
    have h1 : z + a - j ∈ H j := hzj
    have h2 : z - j ∈ H j := by
      have := (H j).sub_mem h1 (hle j hj)
      have e : z + a - j - a = z - j := by abel
      rwa [e] at this
    rw [hU j _ h2, hU j _ h1]
  rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hza]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegrableRep
section
open MeasureTheory

namespace GlobalTheory.LocRep

variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_zero (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) :
    ι 0 =ᵐ[μ] fun _ => 0 := by
  filter_upwards [hlin 1 0 0] with x hx
  simpa using hx

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_add (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v + w) =ᵐ[μ] fun x => ι v x + ι w x := by
  filter_upwards [hlin 1 v w] with x hx
  simpa using hx

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_smul (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (a : ℂ) (v : K) :
    ι (a • v) =ᵐ[μ] fun x => a * ι v x := by
  filter_upwards [hlin a v 0, _root_.GlobalTheory.LocRep.rep_zero hlin] with x hx h0
  simp only [add_zero] at hx
  rw [hx, h0, add_zero]

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_sub (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v - w) =ᵐ[μ] fun x => ι v x - ι w x := by
  filter_upwards [hlin (-1) w v] with x hx
  rw [show v - w = (-1 : ℂ) • w + v by rw [neg_one_smul]; abel, hx]
  ring

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_sum (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) {J : Type} (s : Finset J)
    (v : J → K) : ι (∑ j ∈ s, v j) =ᵐ[μ] fun x => ∑ j ∈ s, ι (v j) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using _root_.GlobalTheory.LocRep.rep_zero hlin
  · intro j s hj ih
    filter_upwards [_root_.GlobalTheory.LocRep.rep_add hlin (v j) (∑ i ∈ s, v i), ih] with x h1 h2
    rw [Finset.sum_insert hj, h1, h2, Finset.sum_insert hj]


open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.exists_pairing
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) {C : Set G} (hC : IsCompact C) :
    ∃ Λ : K →L[ℂ] ℂ, ∀ v, Λ v = ∫ x in C, ι v x ∂μ := by
  obtain ⟨M, hM⟩ := hloc C hC
  have hint : ∀ (a : ℂ) v w, ∫ x in C, ι (a • v + w) x ∂μ =
      a * ∫ x in C, ι v x ∂μ + ∫ x in C, ι w x ∂μ := by
    intro a v w
    rw [integral_congr_ae (ae_restrict_of_ae (hlin a v w)),
      integral_add ((hM v).1.const_mul a) (hM w).1, integral_const_mul]
  have hz : ∫ x in C, ι 0 x ∂μ = 0 := by
    rw [integral_congr_ae (ae_restrict_of_ae (_root_.GlobalTheory.LocRep.rep_zero hlin))]
    simp
  let L : K →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ x in C, ι v x ∂μ
      map_add' := fun v w => by simpa using hint 1 v w
      map_smul' := fun a v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        simpa [hz] using hint a v 0 }
  refine ⟨L.mkContinuous M fun v => ?_, fun v => rfl⟩
  exact (norm_integral_le_integral_norm _).trans (hM v).2

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.locallyIntegrable_rep [LocallyCompactSpace G]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) (v : K) :
    LocallyIntegrable (ι v) μ := by
  intro x
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x
  obtain ⟨M, hM⟩ := hloc C hC
  exact ⟨C, hCx, (hM v).1⟩


open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_of_pairing [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [BorelSpace G]
    [IsLocallyFiniteMeasure μ]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    {v : K} {φ : G → ℂ} (hφ : LocallyIntegrable φ μ)
    (h : ∀ C, IsCompact C → ∫ x in C, ι v x ∂μ = ∫ x in C, φ x ∂μ) : ι v =ᵐ[μ] φ := by
  have hv : LocallyIntegrable (ι v) μ := _root_.GlobalTheory.LocRep.locallyIntegrable_rep hloc v
  have hdiff : (ι v - φ) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' (hv.sub hφ) fun C hC => ?_
    simp only [Pi.sub_apply]
    rw [integral_sub (hv.integrableOn_isCompact hC) (hφ.integrableOn_isCompact hC), h C hC, sub_self]
  filter_upwards [hdiff] with x hx
  simpa [sub_eq_zero] using hx

end GlobalTheory.LocRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogThetaWeightSizeLe
section
open Real

namespace GlobalTheory

theorem log_theta_weight_size_le (f r Lb S sz : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ Lb)
    (hlog : Real.log (f * r) ≤ Lb) (hS : ∃ N : ℕ, S = N) (hlogS : Real.log S ≤ 10 * Lb)
    (hsz0 : 0 ≤ sz) (hsz : sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1)) :
    Real.log sz ≤ 20 * Lb := by
  obtain ⟨N, rfl⟩ := hS
  have hx : 0 < f * r := by positivity
  have hE : 2 ≤ Real.exp Lb := by have := Real.add_one_le_exp Lb; linarith
  have hxE : f * r ≤ Real.exp Lb := by
    rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr hlog
  have hpow : ∀ n : ℕ, Real.exp Lb ^ n = Real.exp (n * Lb) := fun n => (Real.exp_nat_mul Lb n).symm
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hSE : (N:ℝ) ≤ Real.exp Lb ^ 10 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp; positivity
    · have hNp : (0:ℝ) < N := by exact_mod_cast h
      rw [hpow, ← Real.exp_log hNp]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
  set E := Real.exp Lb with hEdef
  set x := f * r with hxdef
  have hE1 : 1 ≤ E := by linarith
  have hr1 : 1 + r ≤ 2 * x := by rw [hxdef]; nlinarith
  have h1 : (1 + r) * (N:ℝ) ≤ 2 * E ^ 11 := by
    calc (1 + r) * (N:ℝ) ≤ (2 * x) * N := mul_le_mul_of_nonneg_right hr1 hN0
      _ ≤ (2 * E) * E ^ 10 := by
          apply mul_le_mul (by linarith) hSE hN0 (by positivity)
      _ = 2 * E ^ 11 := by ring
  have h2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * E ^ 2 := by
    have : r * f * (4 * (f * r + 1) + 1) = x * (4 * x + 5) := by rw [hxdef]; ring
    rw [this]
    have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith
    nlinarith
  have h3 : E ^ 2 ≤ E ^ 11 := pow_le_pow_right₀ hE1 (by norm_num)
  have h4 : (2:ℝ) ^ 9 ≤ E ^ 9 := pow_le_pow_left₀ (by norm_num) hE 9
  have h5 : 11 * E ^ 11 ≤ E ^ 20 := by
    have : E ^ 20 = E ^ 9 * E ^ 11 := by ring
    rw [this]
    have : (0:ℝ) ≤ E ^ 11 := by positivity
    nlinarith
  have key : sz ≤ Real.exp (20 * Lb) := by
    have : Real.exp (20 * Lb) = E ^ 20 := by rw [hEdef, hpow]; norm_num
    rw [this]; linarith
  rcases hsz0.eq_or_lt with h | h
  · subst h; simp; linarith
  · exact (Real.log_le_iff_le_exp h).mpr key

end GlobalTheory
end

