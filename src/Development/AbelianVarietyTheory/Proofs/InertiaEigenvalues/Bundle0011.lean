module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlternatingFormLeftCorankLeOne
section
namespace GlobalTheory.AltCorank

open Module

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def Good (S₁ S₂ : Submodule K V) : Prop :=
  ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
    (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x

theorem good_step (S₁ S₂ T₁ T₂ : Submodule K V) (u v : V) (φ ψ : V →ₗ[K] K)
    (hφu : φ u = 1) (hφv : φ v = 0) (hψu : ψ u = 0) (hψv : ψ v = 1) (hv : v ∈ S₂)
    (hu : u ∈ S₂ ∨ ∀ x ∈ S₁, ψ x = 0)
    (h₁ : ∀ x ∈ S₁, φ x = 0 → ψ x = 0 → x ∈ T₁)
    (h₂ : ∀ y ∈ T₂, y ∈ S₂ ∧ φ y = 0 ∧ ψ y = 0) (h : Good T₁ T₂) : Good S₁ S₂ := by
  obtain ⟨ω, hω, hk⟩ := h
  let π : V →ₗ[K] V := LinearMap.id - φ.smulRight u - ψ.smulRight v
  have hπ : ∀ x, π x = x - φ x • u - ψ x • v := fun x => rfl
  let Ω : V →ₗ[K] V →ₗ[K] K :=
    ω.compl₁₂ π π + (LinearMap.mul K K).compl₁₂ φ ψ - (LinearMap.mul K K).compl₁₂ ψ φ
  have hΩ : ∀ x y, Ω x y = ω (π x) (π y) + φ x * ψ y - ψ x * φ y := fun x y => rfl
  have hπu : π u = 0 := by simp [hπ, hφu, hψu]
  have hπv : π v = 0 := by simp [hπ, hφv, hψv]
  refine ⟨Ω, fun x => by rw [hΩ, hω]; ring, fun x hx hz => ?_⟩
  have e1 : ∀ a, φ (x a) = 0 := fun a => by
    have := hz a v hv
    rw [hΩ, hπv, hφv, hψv] at this
    simpa using this
  have e2 : ∀ a, ψ (x a) = 0 := fun a => by
    rcases hu with hu | hu
    · have := hz a u hu
      rw [hΩ, hπu, hφu, hψu] at this
      simpa using this
    · exact hu _ (hx a)
  refine hk x (fun a => h₁ _ (hx a) (e1 a) (e2 a)) fun a y hy => ?_
  obtain ⟨hy, f1, f2⟩ := h₂ y hy
  have := hz a y hy
  rw [hΩ, hπ, hπ, e1, e2, f1, f2] at this
  simpa using this

theorem finrank_inf_ker [Module.Finite K V] (S : Submodule K V) (φ : V →ₗ[K] K) (u : V)
    (hu : u ∈ S) (hφ : φ u = 1) :
    finrank K (S ⊓ LinearMap.ker φ : Submodule K V) + 1 = finrank K S := by
  have hne : (φ.domRestrict S : Module.Dual K S) ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h ⟨u, hu⟩
    simp [hφ] at this
  rw [← Module.Dual.finrank_ker_add_one_of_ne_zero hne, LinearMap.ker_domRestrict,
    ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem exists_dual (S : Submodule K V) (u : V) (hu : u ∉ S) :
    ∃ φ : V →ₗ[K] K, φ u = 1 ∧ ∀ x ∈ S, φ x = 0 := by
  obtain ⟨f, hf, hS⟩ := S.exists_dual_map_eq_bot_of_notMem hu inferInstance
  refine ⟨(f u)⁻¹ • f, by simp [hf], fun x hx => ?_⟩
  have : f x ∈ S.map f := ⟨x, hx, rfl⟩
  rw [hS] at this
  simp [(Submodule.mem_bot K).1 this]

theorem good_of_finrank_eq [Module.Finite K V] (n : ℕ) :
    ∀ S₁ S₂ : Submodule K V, finrank K S₁ = n → finrank K S₂ = n → Good S₁ S₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S₁ S₂ h₁ h₂
  by_cases hE : S₁ = S₂
  · subst hE
    by_cases hx : ∃ x : Fin 2 → V, (∀ a, x a ∈ S₁) ∧ LinearIndependent K x
    · obtain ⟨x, hx, hli⟩ := hx
      have n0 : x 0 ∉ Submodule.span K {x 1} := by
        have := hli.notMem_span_image (s := {1}) (x := 0) (by simp)
        simpa using this
      have n1 : x 1 ∉ Submodule.span K {x 0} := by
        have := hli.notMem_span_image (s := {0}) (x := 1) (by simp)
        simpa using this
      obtain ⟨φ, a1, a2⟩ := exists_dual _ _ n0
      obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ n1
      have a3 := a2 _ (Submodule.mem_span_singleton_self _)
      have b3 := b2 _ (Submodule.mem_span_singleton_self _)
      have hlt : finrank K (S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule K V) < n := by
        have := finrank_inf_ker S₁ φ _ (hx 0) a1
        have := Submodule.finrank_mono
          (inf_le_left : S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ ≤ S₁ ⊓ LinearMap.ker φ)
        omega
      refine good_step S₁ S₁ _ _ (x 0) (x 1) φ ψ a1 a3 b3 b1 (hx 1) (Or.inl (hx 0)) ?_ ?_
        (ih _ hlt _ _ rfl rfl)
      · intro y h1 h2 h3
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro y ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    · exact ⟨0, fun _ => rfl, fun x h1 _ h2 => hx ⟨x, h1, h2⟩⟩
  · have l1 : ¬ S₁ ≤ S₂ := fun h => hE (Submodule.eq_of_le_of_finrank_eq h (h₁.trans h₂.symm))
    have l2 : ¬ S₂ ≤ S₁ := fun h =>
      hE (Submodule.eq_of_le_of_finrank_eq h (h₂.trans h₁.symm)).symm
    obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.1 l1
    obtain ⟨v, hv2, hv1⟩ := SetLike.not_le_iff_exists.1 l2
    obtain ⟨φ, a1, a2⟩ := exists_dual _ _ hu2
    obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ hv1
    have c1 := finrank_inf_ker S₁ φ u hu1 a1
    have c2 := finrank_inf_ker S₂ ψ v hv2 b1
    refine good_step S₁ S₂ (S₁ ⊓ LinearMap.ker φ) (S₂ ⊓ LinearMap.ker ψ) u v φ ψ a1 (a2 _ hv2)
      (b2 _ hu1) b1 hv2 (Or.inr b2) ?_ ?_ (ih (n - 1) (by omega) _ _ (by omega) (by omega))
    · intro y h1 h2 _
      exact ⟨h1, h2⟩
    · rintro y ⟨h1, h2⟩
      exact ⟨h1, a2 _ h1, h2⟩

theorem exists_alt_corank_le_one :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
      (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ →
      ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
        (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x :=
  fun _ _ _ _ _ _ S₁ S₂ h => good_of_finrank_eq _ S₁ S₂ h rfl

end GlobalTheory.AltCorank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPi
section
open IsDedekindDomain NumberField

namespace GlobalTheory

theorem locBasis_of_bounded {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (d : ℕ) (M : Set (Fin d → F)) (h0 : (0 : Fin d → F) ∈ M)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M)
    (hsmul : ∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hstd : ∀ i, Pi.single i 1 ∈ M)
    (hbd : ∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) :
    ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧
      (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧
      LinearIndependent F b := by
  obtain ⟨D, hD, hDM⟩ := hbd
  set A : ValuationSubring F := p.valuationSubringAtPrime F with hA
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) p.ne_bot _
  have memA : ∀ a : F, a ∈ A ↔ p.valuation F a ≤ 1 := by
    intro a
    rw [hA, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  let M' : Submodule A (Fin d → F) :=
    { carrier := M
      add_mem' := fun {x y} hx hy => hadd x hx y hy
      zero_mem' := h0
      smul_mem' := fun c x hx => by
        have : c • x = (c : F) • x := rfl
        rw [this]
        exact hsmul _ ((memA _).1 c.2) x hx }
  let e : Fin d → Fin d → F := fun i => D⁻¹ • Pi.single i 1
  have heF : LinearIndependent F e := by
    have h1 := (Pi.basisFun F (Fin d)).linearIndependent.units_smul
      (fun _ => Units.mk0 D⁻¹ (inv_ne_zero hD))
    convert h1 using 1
    ext i j
    simp [e, Pi.basisFun_apply]
  have heA : LinearIndependent A e := (LinearIndependent.iff_fractionRing A F).2 heF
  have hle : M' ≤ Submodule.span A (Set.range e) := by
    intro x hx
    have hx' : x = ∑ i, (D * x i) • e i := by
      ext j
      simp [e, Finset.sum_apply, Pi.single_apply]
      rw [mul_comm D, mul_assoc, mul_inv_cancel₀ hD, mul_one]
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : D * x i ∈ A := (memA _).2 (hDM x hx i)
    have : (D * x i) • e i = (⟨D * x i, hc⟩ : A) • e i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨n, bas⟩ := Submodule.basisOfPidOfLE hle (Module.Basis.span heA)
  refine ⟨n, fun k => (bas k : Fin d → F), fun k => (bas k).2, ?_, ?_⟩
  · intro x hx
    refine ⟨fun k => (bas.repr ⟨x, hx⟩ k : F), fun k => (memA _).1 (bas.repr ⟨x, hx⟩ k).2, ?_⟩
    have h := congrArg (fun y : M' => (y : Fin d → F)) (bas.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · have h1 : LinearIndependent A (M'.subtype ∘ bas) :=
      bas.linearIndependent.map' M'.subtype (Submodule.ker_subtype M')
    exact (LinearIndependent.iff_fractionRing A F).1 h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisMemIffNormLeOne
section
namespace GlobalTheory.UnitBallBasis

theorem exists_basis_mem_iff_norm_le_one {l : ℕ} [inst : Fact (Nat.Prime l)] {L O V : Type}
    [inst_1 : Field L] [inst_2 : Algebra ℚ_[l] L] [inst_3 : CommRing O] [inst_4 : Algebra O L]
    [inst_5 : Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hc : ∀ (a : ℤ_[l]), algebraMap O L (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] L (a : ℚ_[l]))
    (hd : ∀ (a : L), ∃ (y : ℤ_[l]), y ≠ 0 ∧ ∃ (o : O),
      algebraMap O L o = algebraMap ℚ_[l] L (y : ℚ_[l]) * a)
    [inst_8 : AddCommGroup V] [inst_9 : Module L V] [inst_10 : Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] L V] [inst_12 : Module O V] [IsScalarTower O L V]
    (S : Submodule O V) (hfg : S.FG) (hfree : Module.Free O S)
    (hspan : Submodule.span L (S : Set V) = ⊤) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ (x : V),
      x ∈ S ↔ ∀ (i : Fin n), ‖w.repr x i‖ ≤ (1 : ℝ) := by
  classical
  have := hfree
  have : Module.Finite O S := Module.Finite.iff_fg.mpr hfg
  let b := Module.Free.chooseBasis O S
  let c := Module.Free.chooseBasis ℤ_[l] O

  have hsm : ∀ (a : ℤ_[l]) (v : V), (algebraMap ℤ_[l] O a) • v = (a : ℚ_[l]) • v := by
    intro a v
    rw [← algebraMap_smul L (algebraMap ℤ_[l] O a) v, hc, algebraMap_smul]

  let J := Module.Free.ChooseBasisIndex ℤ_[l] O × Module.Free.ChooseBasisIndex O S
  let e : J → V := fun j => c j.1 • (b j.2 : V)
  have he : ∀ j, e j ∈ S := fun j => S.smul_mem _ (b j.2).2
  have hin : ∀ a : J → ℤ_[l], ∑ j, (a j : ℚ_[l]) • e j ∈ S := by
    intro a
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← hsm]
    exact S.smul_mem _ (he j)

  have hrep : ∀ s : S, ∃ a : J → ℤ_[l], (s : V) = ∑ j, (a j : ℚ_[l]) • e j := by
    intro s
    refine ⟨fun j => c.repr (b.repr s j.2) j.1, ?_⟩
    rw [Fintype.sum_prod_type_right]
    conv_lhs => rw [← b.sum_repr s]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul]
    conv_lhs => rw [← c.sum_repr (b.repr s i)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_smul, hsm]

  have hind : ∀ a : J → ℤ_[l], ∑ j, (a j : ℚ_[l]) • e j = 0 → a = 0 := by
    intro a ha
    have h1 : ((∑ i, (∑ k, a (k, i) • c k) • b i : S) : V) = 0 := by
      rw [← ha, Fintype.sum_prod_type_right, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, mul_smul, hsm]
    have h3 := Fintype.linearIndependent_iff.mp b.linearIndependent _ (Submodule.coe_eq_zero.mp h1)
    funext j
    exact Fintype.linearIndependent_iff.mp c.linearIndependent _ (h3 j.2) j.1

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hli : LinearIndependent ℚ_[l] e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ j, ‖g j‖) hl1
    have hsmall : ∀ j, ‖(l : ℚ_[l]) ^ N * g j‖ ≤ 1 := by
      intro j
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
      exact (Finset.single_le_sum (fun j _ => norm_nonneg (g j)) (Finset.mem_univ j)).trans hN.le
    have h0 := hind (fun j => ⟨(l : ℚ_[l]) ^ N * g j, hsmall j⟩) (by
      change ∑ j, ((l : ℚ_[l]) ^ N * g j) • e j = 0
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, hg, smul_zero])
    intro j
    have hj : (l : ℚ_[l]) ^ N * g j = 0 := congrArg Subtype.val (congrFun h0 j)
    exact (mul_eq_zero.mp hj).resolve_left (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))

  let P := Submodule.span ℚ_[l] (Set.range e)
  have hSP : ∀ s : S, (s : V) ∈ P := by
    intro s
    obtain ⟨a, ha⟩ := hrep s
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => P.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hLS : ∀ (x : L) (s : V), s ∈ S → x • s ∈ P := by
    intro x s hs
    obtain ⟨y, hy, o, ho⟩ := hd x
    have hy' : (y : ℚ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
    have ho' : o • s = (y : ℚ_[l]) • (x • s) := by
      rw [← algebraMap_smul L o s, ho, mul_smul, algebraMap_smul]
    have hx : x • s = ((y : ℚ_[l]))⁻¹ • (o • s) := by
      rw [ho', inv_smul_smul₀ hy']
    rw [hx]
    exact P.smul_mem _ (hSP ⟨_, S.smul_mem o hs⟩)
  have hLP : ∀ (x : L) (v : V), v ∈ P → x • v ∈ P := by
    intro x v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact hLS x _ (he j)
    | zero => rw [smul_zero]; exact P.zero_mem
    | add u w _ _ hu hw => rw [smul_add]; exact P.add_mem hu hw
    | smul q u _ hu => rw [smul_comm]; exact P.smul_mem q hu
  have hsp : ⊤ ≤ P := by
    rintro v -
    have hv : v ∈ Submodule.span L (S : Set V) := by rw [hspan]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem v hv => exact hSP ⟨v, hv⟩
    | zero => exact P.zero_mem
    | add u w _ _ hu hw => exact P.add_mem hu hw
    | smul x u _ hu => exact hLP x u hu
  let b0 : Module.Basis J ℚ_[l] V := Module.Basis.mk hli hsp
  have hb0 : ∀ j, b0 j = e j := fun j => Module.Basis.mk_apply hli hsp j
  refine ⟨Fintype.card J, b0.reindex (Fintype.equivFin J), fun x => ?_⟩
  simp only [Module.Basis.repr_reindex_apply]
  constructor
  · intro hx i
    obtain ⟨a, ha⟩ := hrep ⟨x, hx⟩
    have hx0 : x = ∑ j, (a j : ℚ_[l]) • b0 j := by simpa only [hb0] using ha
    rw [hx0, congrFun (b0.repr_sum_self fun j => (a j : ℚ_[l]))]
    exact PadicInt.norm_le_one _
  · intro hx
    have hx' : ∀ j, ‖b0.repr x j‖ ≤ 1 := fun j => by simpa using hx (Fintype.equivFin J j)
    have hxs := hin fun j => ⟨b0.repr x j, hx' j⟩
    have hsum : ∑ j, ((⟨b0.repr x j, hx' j⟩ : ℤ_[l]) : ℚ_[l]) • e j = x := by
      simp_rw [← hb0]
      exact b0.sum_repr x
    rwa [hsum] at hxs

end GlobalTheory.UnitBallBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommonDenominatorAevalOfFg
section
open Polynomial

namespace GlobalTheory

theorem exists_denominator_aeval_elem (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A)
    (h : ∀ x : A, ∃ p : E[X], aeval g p = x) (x : A) :
    ∃ c : O, c ≠ 0 ∧ ∃ p : O[X], aeval g p = c • x := by
  obtain ⟨q, rfl⟩ := h x
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors O) q, ?_⟩
  rw [← aeval_map_algebraMap E, hq, ← algebraMap_smul E b q, map_smul, algebraMap_smul]

theorem exists_common_denominator_aeval_of_fg (O E A : Type) [CommRing O] [IsDomain O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] (g : A) (h : ∀ x : A, ∃ p : E[X], aeval g p = x)
    (S : Submodule O A) (hS : S.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  classical
  obtain ⟨s, rfl⟩ := hS
  have key : ∃ c : O, c ≠ 0 ∧ ∀ x ∈ s, ∃ p : O[X], aeval g p = c • x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a s _ ih =>
      obtain ⟨c, hc, hs⟩ := ih
      obtain ⟨d, hd, p, hp⟩ := exists_denominator_aeval_elem O E A g h a
      refine ⟨c * d, mul_ne_zero hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨c • p, by rw [map_smul, hp, mul_smul]⟩
      · obtain ⟨q, hq⟩ := hs x hx
        exact ⟨d • q, by rw [map_smul, hq, mul_comm, mul_smul]⟩
  obtain ⟨c, hc, hs⟩ := key
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add (f := _), hp, hq, smul_add]⟩
  | smul a x _ hx =>
    obtain ⟨p, hp⟩ := hx
    exact ⟨a • p, by rw [map_smul, hp, smul_comm]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleGeneratorsTowerLocalRing
section
open scoped TensorProduct

namespace GlobalTheory

private theorem tower_minimal_presentation (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (A : Type)
    [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] :
    ∃ (d : ℕ) (p : (Fin d → Λ) →ₗ[Λ] A), Function.Surjective p ∧
      ∀ x, p x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  classical
  let k := IsLocalRing.ResidueField Λ
  let b := Module.finBasis k (k ⊗[Λ] A)
  have hs : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k IsLocalRing.residue_surjective
  choose v hv using fun i => hs (b i)
  have hv' : ∀ i, (1 : k) ⊗ₜ[Λ] v i = b i := hv
  have hspan : Submodule.span Λ (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv'
  refine ⟨_, Fintype.linearCombination Λ v, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  · intro x hx i
    have h1 : ∑ j, algebraMap Λ k (x j) • b j = 0 := by
      have h2 := congrArg (TensorProduct.mk Λ k A 1) hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fintype.linearCombination_apply, map_sum, map_zero] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hv, algebraMap_smul]
    have h3 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 i
    exact (IsLocalRing.residue_eq_zero_iff _).1 h3

theorem exists_surjective_lift_of_ker_le_maximalIdeal_smul {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
    {A B : Type} [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] [AddCommGroup B] [Module Λ B]
    (t : A →ₗ[Λ] B) (ht : Function.Surjective t)
    (hk : LinearMap.ker t ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ A))
    {a : ℕ} (p : (Fin a → Λ) →ₗ[Λ] B) (hp : Function.Surjective p) :
    ∃ q : (Fin a → Λ) →ₗ[Λ] A, Function.Surjective q ∧ t ∘ₗ q = p := by
  obtain ⟨q, hq⟩ := Module.projective_lifting_property t p ht
  refine ⟨q, ?_, hq⟩
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal Λ)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) fun y _ => ?_
  obtain ⟨x, hx⟩ := hp (t y)
  have h1 : y - q x ∈ LinearMap.ker t := by
    rw [LinearMap.mem_ker, map_sub, ← hx, ← hq, LinearMap.comp_apply, sub_self]
  have h2 : y = q x + (y - q x) := by abel
  rw [h2]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self q x) (hk h1)

theorem exists_compatible_generators_tower :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (M : ℕ → Type) [∀ n, AddCommGroup (M n)] [∀ n, Module Λ (M n)] [∀ n, Module.Finite Λ (M n)]
  (t : ∀ n, M (n + 1) →ₗ[Λ] M n), (∀ n, Function.Surjective (t n)) →
  (∀ n, LinearMap.ker (t n) ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ (M (n + 1)))) →
  ∃ (a : ℕ) (p : ∀ n, (Fin a → Λ) →ₗ[Λ] M n), (∀ n, Function.Surjective (p n)) ∧ (∀ n, (t n) ∘ₗ (p (n + 1)) = p n) ∧
    ∀ x, p 0 x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  intro Λ _ _ M _ _ _ t ht hk
  obtain ⟨a, p0, hp0, hmin⟩ := tower_minimal_presentation Λ (M 0)
  choose q hq hq' using fun (n : ℕ) (p : (Fin a → Λ) →ₗ[Λ] M n) (hp : Function.Surjective p) =>
    exists_surjective_lift_of_ker_le_maximalIdeal_smul (t n) (ht n) (hk n) p hp
  let P : ∀ n, {p : (Fin a → Λ) →ₗ[Λ] M n // Function.Surjective p} := fun n =>
    Nat.rec (motive := fun n => {p : (Fin a → Λ) →ₗ[Λ] M n // Function.Surjective p})
      ⟨p0, hp0⟩ (fun n p => ⟨q n p.1 p.2, hq n p.1 p.2⟩) n
  exact ⟨a, fun n => (P n).1, fun n => (P n).2, fun n => hq' n (P n).1 (P n).2, hmin⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonempty
section
open CategoryTheory

namespace GlobalTheory

theorem exists_compatible_seq_of_finite_nonempty
    (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n))
    (hfin : ∀ n, (Y n).Finite) (hne : ∀ n, (Y n).Nonempty)
    (hmap : ∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) :
    ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  classical
  let g : ∀ n, ((Y (n + 1) : Set (X (n + 1))) : Type) ⟶ ((Y n : Set (X n)) : Type) :=
    fun n => TypeCat.ofHom (fun x => ⟨f n x.1, hmap n x.1 x.2⟩)
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun n => ((Y n : Set (X n)) : Type)) g
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => (u (Opposite.op n)).1, fun n => ⟨(u (Opposite.op n)).2, ?_⟩⟩
  have h := hu (homOfLE (Nat.le_add_right n 1)).op
  have hm : F.map (homOfLE (Nat.le_add_right n 1)).op = g n :=
    Functor.ofOpSequence_map_homOfLE_succ (X := fun n => ((Y n : Set (X n)) : Type)) g n
  rw [hm] at h
  exact congrArg Subtype.val h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTer
section
namespace GlobalTheory.SingleStatement

theorem main : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → ℂ_[p]) {r : ℝ},
    (0 : ℝ) ≤ r → (∀ k ∈ s, ‖g k‖ ≤ r) → ‖∑ k ∈ s, g k‖ ≤ r := by
  intro p _ ι s g r hr hg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖g a‖ ≤ r := hg a (Finset.mem_insert_self a s)
    have h2 : ‖∑ k ∈ s, g k‖ ≤ r := ih (fun k hk => hg k (Finset.mem_insert_of_mem hk))
    exact (PadicComplex.isNonarchimedean p (g a) (∑ k ∈ s, g k)).trans (max_le h1 h2)

end GlobalTheory.SingleStatement
end

