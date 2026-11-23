module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargeCompactOpenSubgroupWithSmallDual
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.LargeLattice

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ C : Set A.L, IsCompact C → ∀ V ∈ 𝓝 (0 : A.L), ∃ Λ : AddSubgroup A.L,
      IsOpen (Λ : Set A.L) ∧ IsCompact (Λ : Set A.L) ∧ C ⊆ Λ ∧
      {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ ∧
      {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ V := by
  intro F E _ _ _ _ _ A ψ x μ ω h C hC V hV
  obtain ⟨hK, hL, hψ, -, -⟩ := h
  haveI := FourierTest.finite_F_L A
  haveI : IsUltrametricDist F := Unram.ultraF (F := F) (E := E)
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  have hcond := ((_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).2.2.1
  let β := FourierTest.beta A (x : A.K)
  have hker : ∀ w y, A.kerL ψ x w y = ψ (β w y) := fun _ _ => rfl
  let e := Module.finBasis F A.L
  let Φ : A.L →ₗ[F] (Fin (Module.finrank F A.L) → F) := LinearMap.pi (fun i => β (e i))
  have hΦ : ∀ y i, Φ y i = β (e i) y := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply FourierTest.beta_sepLeft A hK hL x y
    intro w
    have h0 : β.flip y = 0 := e.ext (fun i => by
      simpa [hΦ] using congrFun hy i)
    rw [FourierTest.beta_symm A hK hL]
    simpa using LinearMap.congr_fun h0 w
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  let Φe := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦe : ∀ y, Φe y = Φ y := fun _ => rfl
  have hΦc : Continuous Φ := IsModuleTopology.continuous_of_linearMap Φ
  have hΨc : Continuous Φe.symm :=
    IsModuleTopology.continuous_of_linearMap (Φe.symm : (Fin (Module.finrank F A.L) → F) →ₗ[F] A.L)

  have hV' : Φe.symm ⁻¹' V ∈ 𝓝 (0 : Fin (Module.finrank F A.L) → F) :=
    hΨc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨ε, hε0, hεV⟩ := Metric.mem_nhds_iff.1 hV'
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm F (1 / ε)
  have ht0 : 0 < ‖t‖ := lt_trans (by positivity) ht
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hΦc.continuousOn
  let Km : ℝ := ∑ i, ‖Φ (e i)‖
  have hKm : ∀ i j, ‖Φ (e i) j‖ ≤ Km := fun i j =>
    (norm_le_pi_norm (Φ (e i)) j).trans
      (Finset.single_le_sum (f := fun i => ‖Φ (e i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  let R : ℝ := max (max b (‖t‖ * Km)) (max ε 1)
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRε : ε ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRb : b ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRt : ‖t‖ * Km ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  let Λ : AddSubgroup A.L :=
    { carrier := {y | ∀ i, ‖Φ y i‖ ≤ R}
      add_mem' := by
        intro a c ha hc i
        simp only [Set.mem_setOf_eq, map_add (f := _), Pi.add_apply] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hc i))
      zero_mem' := by intro i; simp [hR0.le]
      neg_mem' := by
        intro a ha i
        simp only [Set.mem_setOf_eq, map_neg, Pi.neg_apply, norm_neg] at *
        exact ha i }
  have hmem : ∀ y, y ∈ Λ ↔ ∀ i, ‖Φ y i‖ ≤ R := fun _ => Iff.rfl

  have hperp : ∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, ∀ i, ‖Φ y i‖ < ε := by
    intro y hy i
    have h1 : ‖t * Φ y i‖ ≤ 1 := by
      refine (hcond (t * Φ y i)).1 fun e' he' => ?_
      have hw : (e' * t) • e i ∈ Λ := by
        rw [hmem]; intro j
        rw [map_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul]
        calc ‖e'‖ * ‖t‖ * ‖Φ (e i) j‖ ≤ 1 * ‖t‖ * Km := by gcongr; exact hKm i j
          _ ≤ R := by rw [one_mul]; exact hRt
      have := hy _ hw
      rw [hker, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      rw [← hΦ] at this
      rwa [← mul_assoc]
    rw [norm_mul] at h1
    have h2 : ‖Φ y i‖ ≤ 1 / ‖t‖ := by rw [le_div_iff₀ ht0]; linarith
    have h3 : 1 / ‖t‖ < ε := by
      rw [div_lt_iff₀ ht0]
      rw [div_lt_iff₀ hε0] at ht
      linarith
    exact lt_of_le_of_lt h2 h3
  refine ⟨Λ, ?_, ?_, ?_, ?_, ?_⟩
  · have : (Λ : Set A.L) = ⋂ i, (fun y => Φ y i) ⁻¹' Metric.closedBall 0 R := by
      ext y; simp [hmem, mem_closedBall_zero_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (IsUltrametricDist.isOpen_closedBall 0 hR0.ne').preimage ((continuous_apply i).comp hΦc)
  · have : (Λ : Set A.L) = Φe.symm '' Metric.closedBall 0 R := by
      ext y
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · intro hy
        refine ⟨Φe y, ?_, by simp⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le, hΦe]; exact hy
      · rintro ⟨z, hz, rfl⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le] at hz
        intro i
        have : Φ (Φe.symm z) = z := by rw [← hΦe]; simp
        rw [this]; exact hz i
    rw [this]
    exact (isCompact_closedBall 0 R).image hΨc
  · intro y hy
    rw [SetLike.mem_coe, hmem]
    intro i
    exact ((norm_le_pi_norm (Φ y) i).trans (hb y hy)).trans hRb
  · intro y hy
    rw [SetLike.mem_coe, hmem]
    intro i
    exact (hperp y hy i).le.trans hRε
  · intro y hy
    have hb' : Φe y ∈ Metric.ball (0 : Fin (Module.finrank F A.L) → F) ε := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε0, hΦe]; exact hperp y hy
    have := hεV hb'
    simpa using this

end GlobalTheory.JR.WeilQuad.LargeLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodPowCoboundaryOfRationalCoboundary
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem exists_addHom_zmod_pow_extend (O : Type) [CommRing O] (l n : ℕ) [Fact l.Prime]
    (hinj : Function.Injective (fun o : O => (l : O) ^ n * o)) (β : O →+ ZMod (l ^ 1)) :
    ∃ A : O →+ ZMod (l ^ (n + 1)), ∀ o : O,
      A ((l : O) ^ n * o) = ((l ^ n * (β o).val : ℕ) : ZMod (l ^ (n + 1))) := by
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  have : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl0⟩

  have hcong : ∀ x : ℕ, ((l ^ n * (x % l ^ 1) : ℕ) : ZMod (l ^ (n + 1)))
      = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by
    intro x
    rw [ZMod.natCast_eq_natCast_iff, pow_one, pow_succ]
    exact Nat.ModEq.mul_left' _ (Nat.mod_modEq x l)
  let g : O →+ ZMod (l ^ (n + 1)) :=
    { toFun := fun o => ((l ^ n * (β o).val : ℕ) : ZMod (l ^ (n + 1)))
      map_zero' := by simp
      map_add' := by
        intro a b
        rw [map_add (f := _), ZMod.val_add, hcong, mul_add, Nat.cast_add] }

  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    (AddMonoidHom.mulLeft ((l : O) ^ n)) hinj ((ZMod.toAddCircle).comp g)
  have hh' : ∀ o, h ((l : O) ^ n * o) = ZMod.toAddCircle (g o) := fun o =>
    DFunLike.congr_fun hh o

  have htors : ∀ o, (l ^ (n + 1)) • h o = 0 := by
    intro o
    have hlo : β ((l : O) * o) = 0 := by
      have hz : ((l : ℕ) : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [pow_one])
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, hz, zero_mul]
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, pow_succ, mul_assoc, hh']
    simp [g, hlo]

  have hdesc : ∀ o, ∃ k : ZMod (l ^ (n + 1)), ZMod.toAddCircle k = h o := by
    intro o
    have ht := htors o
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (h o)
    rw [← hx] at ht ⊢
    rw [← QuotientAddGroup.mk_nsmul, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨m, hm⟩ := ht
    refine ⟨(m : ZMod (l ^ (n + 1))), ?_⟩
    rw [ZMod.toAddCircle_intCast]
    congr 1
    have hN : ((l ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hl0
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hm
    rw [hm, mul_div_cancel_left₀ _ hN]
  choose A hA using hdesc
  have hAadd : ∀ a b, A (a + b) = A a + A b := by
    intro a b
    apply ZMod.toAddCircle_injective (l ^ (n + 1))
    rw [map_add (f := _), hA, hA, hA, map_add (f := _)]
  refine ⟨⟨⟨A, ?_⟩, hAadd⟩, ?_⟩
  · apply ZMod.toAddCircle_injective (l ^ (n + 1))
    rw [hA, map_zero, map_zero]
  · intro o
    apply ZMod.toAddCircle_injective (l ^ (n + 1))
    show ZMod.toAddCircle (A _) = _
    rw [hA, hh']
    rfl

theorem addHom_zmod_pow_algebraMap_mul (O : Type) [CommRing O] (l m : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (A : O →+ ZMod (l ^ m)) (u : ℤ_[l]) (o : O) :
    A (algebraMap ℤ_[l] O u * o) = PadicInt.toZModPow m u * A o := by
  set v : ℕ := (PadicInt.toZModPow m u).val with hv

  have hk : u - (v : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨w, hw⟩ := hk
  have hu : u = (v : ℤ_[l]) + w * (l : ℤ_[l]) ^ m := by rw [hw]; ring
  have hkill : ∀ x : O, A ((l : O) ^ m * x) = 0 := by
    intro x
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hsplit : algebraMap ℤ_[l] O u * o
      = v • o + (l : O) ^ m * (algebraMap ℤ_[l] O w * o) := by
    rw [hu, map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, nsmul_eq_mul]
    ring
  rw [hsplit, map_add (f := _), hkill, add_zero, map_nsmul, nsmul_eq_mul, hv, ZMod.natCast_zmod_val]

theorem exists_zmod_pow_coboundary_of_rational_coboundary :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (ε : Γ → ℤ_[l]) (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L] [TopologicalSpace L] [IsTopologicalRing L] (ι : O →+* L), Function.Injective ι → IsOpen (Set.range ι) → (l : L) ≠ 0 → (∀ x : L, ∃ n : ℕ, (l : L) ^ n * x ∈ Set.range ι) → ∀ (β : O →+ ZMod (l ^ 1)) (z : Γ → Γ → O) (f : Γ → L), Continuous f → (∀ g h, ι (z g h) = ι (algebraMap ℤ_[l] O (ε g)) * f h - f (g * h) + f g) → ∃ (n : ℕ) (a : Γ → ZMod (l ^ (n + 1))), Continuous a ∧ ∀ g h, PadicInt.toZModPow (n + 1) (ε g) * a h - a (g * h) + a g = ((l ^ n * (β (z g h)).val : ℕ) : ZMod (l ^ (n + 1))) := by
  intro Γ _ _ _ l _ ε O L _ _ _ _ _ ι hι hopen hl hcov β z f hf hz

  have hstep : ∀ k x, (l : L) ^ k * x ∈ Set.range ι → (l : L) ^ (k + 1) * x ∈ Set.range ι := by
    rintro k x ⟨o, ho⟩
    exact ⟨(l : O) * o, by rw [map_mul, map_natCast, ho, pow_succ]; ring⟩
  have hmono : Monotone (fun k : ℕ => {x : L | (l : L) ^ k * x ∈ Set.range ι}) :=
    monotone_nat_of_le_succ (fun k x hx => hstep k x hx)
  obtain ⟨N, hN⟩ := (isCompact_range hf).elim_directed_cover
    (fun k : ℕ => {x : L | (l : L) ^ k * x ∈ Set.range ι})
    (fun k => hopen.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.mpr (hcov x)) hmono.directed_le
  have hN' : ∀ g, ∃ o : O, ι o = (l : L) ^ N * f g := fun g => hN ⟨g, rfl⟩
  choose F hF using hN'
  have hlN : ∀ k, (l : L) ^ k ≠ 0 := fun k => pow_ne_zero _ hl
  have hinjO : Function.Injective (fun o : O => (l : O) ^ N * o) := by
    intro a b hab
    apply hι
    have := congrArg ι hab
    simp only [map_mul, map_pow, map_natCast] at this
    exact mul_left_cancel₀ (hlN N) this
  obtain ⟨A, hA⟩ := exists_addHom_zmod_pow_extend O l N hinjO β

  have hrel : ∀ g h, (l : O) ^ N * z g h
      = algebraMap ℤ_[l] O (ε g) * F h - F (g * h) + F g := by
    intro g h
    apply hι
    rw [map_mul, map_pow, map_natCast, hz, map_add (f := _), map_sub, map_mul, hF, hF, hF]
    ring
  have hkill : ∀ x : O, A ((l : O) ^ (N + 1) * x) = 0 := by
    intro x
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine ⟨N, fun g => A (F g), ?_, ?_⟩
  ·
    refine ((IsLocallyConstant.iff_eventually_eq _).mpr fun g₁ => ?_).continuous
    have hPo : IsOpen {g : Γ | ((l : L) ^ (N + 1))⁻¹ * ((l : L) ^ N * f g - (l : L) ^ N * f g₁)
        ∈ Set.range ι} :=
      hopen.preimage (continuous_const.mul ((continuous_const.mul hf).sub continuous_const))
    have hmem : g₁ ∈ {g : Γ | ((l : L) ^ (N + 1))⁻¹ * ((l : L) ^ N * f g - (l : L) ^ N * f g₁)
        ∈ Set.range ι} := ⟨0, by simp⟩
    filter_upwards [hPo.mem_nhds hmem] with g hg
    obtain ⟨o, ho⟩ := hg
    have hFg : F g = F g₁ + (l : O) ^ (N + 1) * o := by
      apply hι
      rw [map_add (f := _), map_mul, map_pow, map_natCast, ho, mul_inv_cancel_left₀ (hlN _), hF, hF]
      ring
    show A (F g) = A (F g₁)
    rw [hFg, map_add (f := _), hkill, add_zero]
  · intro g h
    rw [← addHom_zmod_pow_algebraMap_mul O l (N + 1) A (ε g) (F h), ← map_sub, ← map_add (f := _),
      ← hrel, hA]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussIntegralOneMulGaussIntegralNegOneEqOne
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.GaussProd

open GlobalTheory.JR.WeilQuad.FourierTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem NL_add [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (t u : A.L) :
    A.NL (t + u) = A.NL t + A.NL u + Algebra.trace A.K A.L (star t * u) := by
  apply algMap_inj A hK hL
  rw [map_add (f := _), map_add (f := _), (_root_.GlobalTheory.JR.EtFacts.main F E A).1, (_root_.GlobalTheory.JR.EtFacts.main F E A).1, (_root_.GlobalTheory.JR.EtFacts.main F E A).1,
    (_root_.GlobalTheory.JR.EtFacts.main F E A).2.1, star_add, star_mul, star_star]
  ring

theorem two_trace_NL [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) (y : A.L) :
    2 * Algebra.trace F A.K (x * A.NL y) = beta A x y y := by
  rw [beta_apply]
  have h : Algebra.trace A.K A.L (star y * y) = A.NL y + A.NL y := by
    apply algMap_inj A hK hL
    rw [(_root_.GlobalTheory.JR.EtFacts.main F E A).2.1, map_add (f := _), (_root_.GlobalTheory.JR.EtFacts.main F E A).1, star_mul, star_star]
    ring
  rw [h, mul_add, map_add (f := _), two_mul]

theorem trace_NL_add [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) (t u : A.L) :
    Algebra.trace F A.K (x * A.NL (t + u)) =
      Algebra.trace F A.K (x * A.NL t) + Algebra.trace F A.K (x * A.NL u) + beta A x t u := by
  rw [NL_add A hK hL, mul_add, mul_add, map_add (f := _), map_add (f := _), beta_apply]

theorem continuous_trace_NL [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    Continuous fun y : A.L => Algebra.trace F A.K (x * A.NL y) := by
  haveI := finite_F_L A
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hβc : Continuous (fun p : A.L × A.L => beta A x p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left (beta A x)
  have hdiag : Continuous (fun y : A.L => (y, y)) := continuous_id.prodMk continuous_id
  have hcomp : Continuous ((fun p : A.L × A.L => beta A x p.1 p.2) ∘ (fun y : A.L => (y, y))) :=
    hβc.comp hdiag
  have hd : Continuous (fun y : A.L => (2 : F)⁻¹ * beta A x y y) := continuous_const.mul hcomp
  refine hd.congr (fun y => ?_)
  show (2 : F)⁻¹ * beta A x y y = Algebra.trace F A.K (x * A.NL y)
  rw [← two_trace_NL A hK hL x y, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

end GlobalTheory.JR.WeilQuad.GaussProd


open GlobalTheory.JR.WeilQuad.FourierTest GlobalTheory.JR.WeilQuad.GaussProd in
theorem GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one : ∀ (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ)
    (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) →
    IsCompact (Λ : Set A.L) → {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ →
    (∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, A.psiK ψ ((x : A.K) * A.NL y) = 1) →
    gaussInt A ψ x μ 1 Λ * gaussInt A ψ x μ (-1) Λ = 1 := by
  intro F E _ _ _ _ _ A ψ x μ ω h Λ hΛo hΛc hPS hQ
  obtain ⟨hK, hL, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI := finite_F_L A
  obtain ⟨hLC, hSC, hT2, hTG⟩ := GlobalTheory.JR.SelfDualLat.topo F E A.L
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hψ' := (_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ
  have hψc : Continuous (fun t : F => ψ t) := cont_psi hψ
  set β := beta A (x : A.K) with hβdef
  have hβc : Continuous (fun p : A.L × A.L => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  set q : A.L → F := fun y => Algebra.trace F A.K ((x : A.K) * A.NL y) with hqdef
  have hqc : Continuous q := continuous_trace_NL A hK hL (x : A.K)
  have hqa : ∀ t u, q (t + u) = q t + q u + β t u := fun t u => trace_NL_add A hK hL (x : A.K) t u
  set S : Set A.L := (Λ : Set A.L) with hSdef
  set P : Set A.L := {y : A.L | ∀ w ∈ S, ψ (β w y) = 1} with hPdef
  have hSm : MeasurableSet S := hΛo.measurableSet
  have hPc : IsClosed P := by
    have : P = ⋂ w ∈ S, (fun y => ψ (β w y)) ⁻¹' {1} := by ext y; simp [hPdef]
    rw [this]
    exact isClosed_biInter fun w _ =>
      isClosed_singleton.preimage (hψc.comp (hβc.comp (continuous_const.prodMk continuous_id)))
  have hPm : MeasurableSet P := hPc.measurableSet
  have hI := _root_.GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel F E ψ hψ A.L β (beta_isSymm A hK hL (x : A.K)) (beta_nondeg A hK hL x) μ hsd.1
  have hvol : μ S * μ P = 1 := ((hI.1 Λ hΛo hΛc).1).1 hsd
  have horth : ∀ u, ∫ t in S, ψ (β t u) ∂μ = P.indicator (fun _ => ((μ S).toReal : ℂ)) u :=
    (hI.1 Λ hΛo hΛc).2
  have hPS' : P ⊆ S := hPS
  have hQ' : ∀ y ∈ P, ψ (q y) = 1 := hQ
  have hG1 : gaussInt A ψ x μ 1 Λ = ∫ y in S, ψ (q y) ∂μ := by
    unfold gaussInt
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (Algebra.trace F A.K (1 * (x : A.K) * A.NL y)) = ψ (Algebra.trace F A.K ((x : A.K) * A.NL y))
    rw [one_mul]
  have hG2 : gaussInt A ψ x μ (-1) Λ = ∫ y in S, ψ (-q y) ∂μ := by
    unfold gaussInt
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (Algebra.trace F A.K (-1 * (x : A.K) * A.NL y)) = ψ (-Algebra.trace F A.K ((x : A.K) * A.NL y))
    rw [neg_one_mul, neg_mul, map_neg]
  have hne : ∀ a : F, ψ (-a) * ψ a = 1 := by
    intro a; rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have htr : ∀ t ∈ S, (∫ u in S, ψ (q u) ∂μ) = ψ (q t) * ∫ u in S, ψ (q u) * ψ (β t u) ∂μ := by
    intro t ht
    rw [← integral_indicator hSm, ← integral_add_left_eq_self (S.indicator fun u => ψ (q u)) t,
      ← integral_const_mul, ← integral_indicator hSm]
    congr 1; ext u
    by_cases hu : u ∈ S
    · have htu : t + u ∈ S := Λ.add_mem ht hu
      rw [Set.indicator_of_mem htu, Set.indicator_of_mem hu, hqa, AddChar.map_add_eq_mul,
        AddChar.map_add_eq_mul]
      ring
    · have htu : t + u ∉ S := fun h' => hu (by
        have := Λ.sub_mem h' ht
        rwa [add_sub_cancel_left] at this)
      simp [Set.indicator_of_notMem htu, Set.indicator_of_notMem hu]
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hΛc.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun t u => ψ (q u) * ψ (β t u))
      ((μ.restrict S).prod (μ.restrict S)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact ((hψc.comp (hqc.comp continuous_snd)).mul (hψc.comp hβc)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, le_refl]
  rw [hG1, hG2]
  calc (∫ y in S, ψ (q y) ∂μ) * ∫ y in S, ψ (-q y) ∂μ
      = ∫ t in S, (∫ y in S, ψ (q y) ∂μ) * ψ (-q t) ∂μ := (integral_const_mul _ _).symm
    _ = ∫ t in S, ∫ u in S, ψ (q u) * ψ (β t u) ∂μ ∂μ := by
        refine setIntegral_congr_fun hSm (fun t ht => ?_)
        rw [htr t ht, mul_comm, ← mul_assoc, hne, one_mul]
    _ = ∫ u in S, ∫ t in S, ψ (q u) * ψ (β t u) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ u in S, ψ (q u) * P.indicator (fun _ => ((μ S).toReal : ℂ)) u ∂μ := by
        congr 1; ext u
        rw [integral_const_mul, horth u]
    _ = ∫ u in S, P.indicator (fun _ => ((μ S).toReal : ℂ)) u ∂μ := by
        refine setIntegral_congr_fun hSm (fun u _ => ?_)
        by_cases hp : u ∈ P
        · simp only [Set.indicator_of_mem hp, hQ' u hp, one_mul]
        · simp only [Set.indicator_of_notMem hp, mul_zero]
    _ = (μ P).toReal * (μ S).toReal := by
        rw [setIntegral_indicator hPm, Set.inter_eq_right.2 hPS', setIntegral_const]
        simp [Measure.real]
    _ = 1 := by
        have h1 : (μ S).toReal * (μ P).toReal = 1 := by
          rw [← ENNReal.toReal_mul, hvol, ENNReal.toReal_one]
        rw [mul_comm]; exact_mod_cast h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchingAdd
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.MatchAdd.integrable_of_isTest {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : IsTest f) :
    Integrable f μ :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

theorem GlobalTheory.JR.match_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by
  intro F E _ _ _ _ _ r M f₁' f₂' f₁ f₂ h₁' h₂' h₁ h₂ m₁ m₂ a ha
  obtain ⟨hG, hU⟩ := _root_.GlobalTheory.JR.orb_integrand_isTest F E r M
  obtain ⟨-, hsec, -⟩ := _root_.GlobalTheory.JR.normalForm_invariants F r
  have ha' : Delta (inv (sec a)) ≠ 0 := by rw [hsec]; exact ha
  have eG : orbG M (f₁' + f₂') (sec a) = orbG M f₁' (sec a) + orbG M f₂' (sec a) := by
    letI := M.mG
    haveI := M.bG
    haveI := M.haarG
    unfold orbG
    simp only [Pi.add_apply, add_mul]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hG _ h₁' _ ha'))
      (MatchAdd.integrable_of_isTest _ (hG _ h₂' _ ha'))
  have eU : ∀ X : Hn r F E, HasInv X a → orbU M (f₁ + f₂) X = orbU M f₁ X + orbU M f₂ X := by
    intro X hX
    letI := M.mU
    haveI := M.bU
    haveI := M.haarU
    unfold orbU
    simp only [Pi.add_apply]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hU _ h₁ a X ha hX))
      (MatchAdd.integrable_of_isTest _ (hU _ h₂ a X ha hX))
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · rw [eG, eU X hX, (m₁ a ha).1 X hX, (m₂ a ha).1 X hX]
  · rw [eG, (m₁ a ha).2 hn, (m₂ a ha).2 hn, add_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurentStatement
section
open GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesTwistedScaling_triangular_laurent : ∀ {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M] (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M), Monotone Sub → ∀ (y : ℕ) (f : ℤ → M), (∃ m : ℤ, ∀ j < m, f j = 0) → (∀ j, f j ∈ Sub j) → ∀ k : ℤ, (∀ j < k, f j ∈ Sub (j - y)) → (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧ (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧ (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧ conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  first | exact @GlobalTheory.NL.Twist.tri | exact GlobalTheory.NL.Twist.tri | (intros; apply GlobalTheory.NL.Twist.tri <;> assumption)
end

