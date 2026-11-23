module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

noncomputable section

variable {κ ι : Type}

def rep (R : ℕ) (n : κ → ι → Fin (R * R)) : Matrix κ ι ℚ :=
  Matrix.of fun k i => ((n k i : ℕ) : ℚ) / R

def zm (m : κ → ι → ℤ) : Matrix κ ι ℚ := Matrix.of fun k i => (m k i : ℚ)

def zv (m : ι → ℤ) : ι → ℚ := fun i => (m i : ℚ)

def ech (t : ℚ) : ℂ := cexp (2 * π * I * (t : ℂ))

def gs [Fintype ι] (τ : Matrix ι ι ℂ) (ζ : ι → ℂ) (v : ι → ℚ) : ℂ :=
  cexp (π * I * (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)))

theorem ech_add (s t : ℚ) : ech (s + t) = ech s * ech t := by
  unfold ech
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ech_zero : ech 0 = 1 := by
  simp [ech]

theorem ech_eq_one_iff (t : ℚ) : ech t = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ech
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (t : ℂ) = ((n : ℚ) : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]
      push_cast
      ring
    exact_mod_cast h
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

theorem norm_ech (t : ℚ) : ‖ech t‖ = 1 := by
  unfold ech
  rw [show (2 : ℂ) * π * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_ech (t : ℚ) : conj (ech t) = ech (-t) := by
  unfold ech
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
  push_cast
  ring

theorem ech_sum {α : Type} (s : Finset α) (f : α → ℚ) : ech (∑ a ∈ s, f a) = ∏ a ∈ s, ech (f a) := by
  unfold ech
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

theorem intM_iff [Fintype κ] [Fintype ι] (x : Matrix κ ι ℚ) : IntM x ↔ ∃ m : κ → ι → ℤ, x = zm m := by
  constructor
  · intro h
    choose m hm using fun k i => (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp (h k i)
    refine ⟨m, Matrix.ext fun k i => ?_⟩
    rw [← hm k i]
    simp [zm]
  · rintro ⟨m, rfl⟩ k i
    simpa [zm] using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℚ (m k i)))

end

end GlobalTheory.SW.FourierJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticActionOfPeriodLatticeMap
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SymplecticPeriods

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_symplectic_rows (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ j,
      F (fun i => σ j (Sum.inr i), fun i => σ j (Sum.inl i)) =
        (fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i),
          fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i)) := by
  classical

  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 : ∀ v : (ι → ℚ) × (ι → ℚ), u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 = 0 := fun v => by
      rw [← hF, hu]; simp
    ext i
    · simpa using h0 (0, Pi.single i 1)
    · simpa using h0 (Pi.single i 1, 0)
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.mp hinj

  choose r hr using fun j : ι ⊕ ι => hsurj
    ((fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i)), fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i))
  let σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ := Matrix.of fun j => Sum.elim (fun i => (r j).2 i) (fun i => (r j).1 i)
  have hrow : ∀ j, ((fun i => σ j (Sum.inr i)), (fun i => σ j (Sum.inl i))) = r j := fun j => rfl
  refine ⟨σ, ?_, fun j => by rw [hrow]; exact hr j⟩
  rw [SymplecticGroup.mem_iff]
  ext a b

  have e1 : (σ * Matrix.J ι ℚ * σᵀ) a b = (r a).1 ⬝ᵥ (r b).2 - (r a).2 ⬝ᵥ (r b).1 := by
    simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, σ, dotProduct, Matrix.one_apply,
      Finset.sum_neg_distrib, sub_eq_add_neg, add_comm, Function.swap]
  rw [e1, ← hF, hr, hr]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.J, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem exists_symplectic_action (ι : Type) [Fintype ι] [DecidableEq ι]
    (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm →
      (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) →
      τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  obtain ⟨σ, hσ, hrows⟩ := exists_symplectic_rows F hF
  refine ⟨σ, hσ, fun τ hτ τ' M hτ' hM => ?_⟩
  have hτs : τ.IsSymm := hτ.1
  set X := spDen σ τ with hX
  set Y := qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ with hY

  have colX : ∀ k, (fun l => Xᵀ l k) =
      qv (fun i => σ (Sum.inr k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inr k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hX, spDen, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]
  have columnBlock : ∀ k, (fun l => Yᵀ l k) =
      qv (fun i => σ (Sum.inl k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inl k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hY, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]

  have hA : M * Xᵀ = 1 := by
    ext i k
    have h := hM (fun i => σ (Sum.inr k) (Sum.inr i), fun i => σ (Sum.inr k) (Sum.inl i))
    rw [hrows (Sum.inr k), ← colX k] at h
    rw [show (M * Xᵀ) i k = (M *ᵥ fun l => Xᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.one_apply, Matrix.mulVec, dotProduct]
    split_ifs <;> simp
  have hB : τ' = M * Yᵀ := by
    ext i k
    have h := hM (fun i => σ (Sum.inl k) (Sum.inr i), fun i => σ (Sum.inl k) (Sum.inl i))
    rw [hrows (Sum.inl k), ← columnBlock k] at h
    rw [show (M * Yᵀ) i k = (M *ᵥ fun l => Yᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hMeq : M = (X⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv hA]
  refine ⟨?_, hMeq⟩
  calc τ' = τ'ᵀ := hτ'.eq.symm
    _ = (M * Yᵀ)ᵀ := by rw [← hB]
    _ = Y * Mᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = spAct σ τ := by rw [hMeq, Matrix.transpose_transpose]; rfl

end GlobalTheory.SymplecticPeriods
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.HaarLevel

noncomputable section

open NumberField

theorem finsum_quotient_of_le {A : Type} [AddCommGroup A] {s t : AddSubgroup A} (h : s ≤ t)
    (hn : s.relIndex t ≠ 0) (φ : A → ℂ) (hφ : ∀ x, ∀ y ∈ t, φ (x + y) = φ x)
    (hf : (Function.support fun q : A ⧸ t => φ q.out).Finite) :
    ∑ᶠ q : A ⧸ s, φ q.out = (s.relIndex t : ℂ) * ∑ᶠ q : A ⧸ t, φ q.out := by
  classical
  set e := AddSubgroup.quotientEquivProdOfLE h
  haveI : Finite (t ⧸ s.addSubgroupOf t) := Nat.finite_of_card_ne_zero hn
  haveI : Fintype (t ⧸ s.addSubgroupOf t) := Fintype.ofFinite _
  have h1 : ∀ q : A ⧸ s, φ q.out = φ (e q).1.out := by
    intro q
    have h2 : (e q).1 = (q.out : A ⧸ t) := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    have h3 : ((e q).1.out : A ⧸ t) = (q.out : A ⧸ t) := by
      rw [QuotientAddGroup.out_eq', h2]
    have := hφ (e q).1.out _ (QuotientAddGroup.eq.1 h3)
    rw [← this]; congr 1; abel
  simp_rw [h1]
  rw [finsum_comp_equiv e (f := fun p => φ p.1.out),
    finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ Finset.univ), finsum_eq_sum _ hf,
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  · intro p hp
    simpa using hp

variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

def incl (K κ ι : Type) [Field K] : Matrix κ ι (𝓞 K) →+ Matrix κ ι K :=
  (algebraMap (𝓞 K) K).toAddMonoidHom.mapMatrix

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem intM_iff (x : Matrix κ ι K) : IntM x ↔ ∃ y, incl K κ ι y = x := by
  constructor
  · intro h
    exact ⟨fun k i => ⟨x k i, h k i⟩, rfl⟩
  · rintro ⟨y, rfl⟩ k i
    exact (y k i).2

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem incl_inj : Function.Injective (incl K κ ι) := fun a b h => by
  ext k i
  exact congrFun (congrFun h k) i

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem perSub_eq_range (R : ℕ) :
    perSub K κ ι R = ((incl K κ ι).comp (nsmulAddMonoidHom R)).range := by
  have : {x | ∃ y : Matrix κ ι K, IntM y ∧ x = (R : K) • y} =
      (((incl K κ ι).comp (nsmulAddMonoidHom R)).range : Set (Matrix κ ι K)) := by
    ext z
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
      nsmulAddMonoidHom_apply, map_nsmul, intM_iff, Nat.cast_smul_eq_nsmul]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [perSub, this, AddSubgroup.closure_eq]

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem mem_perSub (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, R • incl K κ ι y = x := by
  rw [perSub_eq_range]
  simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply, nsmulAddMonoidHom_apply, map_nsmul]

theorem index_nsmul (R : ℕ) : (nsmulAddMonoidHom R : Matrix κ ι (𝓞 K) →+ _).range.index =
    R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  rw [AddSubgroup.index_range_nsmul, Module.finrank_matrix, RingOfIntegers.rank]
  ring

omit [Fintype κ] [Fintype ι] in
theorem nsmul_cancel {R : ℕ} (hR : 0 < R) {x y : Matrix κ ι K} : R • x = R • y ↔ x = y := by
  rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K]
  exact (smul_right_injective _ (by exact_mod_cast hR.ne')).eq_iff

theorem relIndex_perSub (R S : ℕ) (hR : 0 < R) :
    (perSub K κ ι (R * S)).relIndex (perSub K κ ι R) =
      S ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  rw [perSub_eq_range R, ← AddSubgroup.index_comap, ← index_nsmul]
  congr 1
  ext y
  simp only [AddSubgroup.mem_comap, mem_perSub, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
    nsmulAddMonoidHom_apply]
  refine exists_congr fun z => ?_
  rw [mul_smul, map_nsmul, nsmul_cancel hR, ← map_nsmul, incl_inj.eq_iff]

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem perSub_le (R S : ℕ) : perSub K κ ι (R * S) ≤ perSub K κ ι R := by
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_perSub _ _).1 hx
  exact (mem_perSub _ _).2 ⟨S • y, by rw [map_nsmul, mul_smul]⟩

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem periodic {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    ∀ y ∈ perSub K κ ι R, φ (x + y) = φ x := by
  intro y hy
  obtain ⟨z, rfl⟩ := (mem_perSub _ _).1 hy
  rw [← Nat.cast_smul_eq_nsmul K]
  exact h.2 x _ ((intM_iff _).2 ⟨z, rfl⟩)

theorem finite_support {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) :
    (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by
  have hK : (R : K) ≠ 0 := by exact_mod_cast hR.ne'
  set f : Matrix κ ι (𝓞 K) →+ Matrix κ ι K ⧸ perSub K κ ι R :=
    (QuotientAddGroup.mk' (perSub K κ ι R)).comp
      ((DistribSMul.toAddMonoidHom (Matrix κ ι K) (R : K)⁻¹).comp (incl K κ ι)) with hf
  have hfa : ∀ y, f y = (((R : K)⁻¹ • incl K κ ι y : Matrix κ ι K) :
    Matrix κ ι K ⧸ perSub K κ ι R) := fun _ => rfl
  have hker : (nsmulAddMonoidHom (R * R) : Matrix κ ι (𝓞 K) →+ _).range ≤ f.ker := by
    rintro _ ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker, hfa, QuotientAddGroup.eq_zero_iff, mem_perSub]
    refine ⟨y, ?_⟩
    rw [nsmulAddMonoidHom_apply, map_nsmul, mul_smul, ← Nat.cast_smul_eq_nsmul K R (R • _),
      smul_smul, inv_mul_cancel₀ hK, one_smul]
  have hcard : Nat.card f.range ≠ 0 := by
    rw [← AddSubgroup.index_ker]
    refine ne_zero_of_dvd_ne_zero ?_ (AddSubgroup.index_dvd_of_le hker)
    rw [index_nsmul]
    positivity
  have hfin : Finite f.range := Nat.finite_of_card_ne_zero hcard
  refine (Set.toFinite (f.range : Set (Matrix κ ι K ⧸ perSub K κ ι R))).subset fun q hq => ?_
  obtain ⟨y, hy⟩ := (intM_iff _).1 (h.1 _ hq)
  refine ⟨y, ?_⟩
  rw [hfa, hy, smul_smul, inv_mul_cancel₀ hK, one_smul, QuotientAddGroup.out_eq']

theorem haarAt_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) {S : ℕ}
    (hS : 0 < S) : haarAt (R * S) φ = haarAt R φ := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [haarAt, haarAt, finsum_quotient_of_le (perSub_le R S)
    (by rw [relIndex_perSub R S hR]; positivity) φ (periodic h) (finite_support hR h),
    relIndex_perSub R S hR]
  push_cast
  rw [mul_pow]
  field_simp

end

end GlobalTheory.SW.HaarLevel

namespace GlobalTheory.SW

theorem haar_eq_haarAt : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → haar φ = haarAt R φ ∧ (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by
  intro K κ ι _ _ _ _ R φ hR h
  refine ⟨?_, HaarLevel.finite_support hR h⟩
  have hs : IsSB φ := ⟨R, hR, h⟩
  rw [haar, dite_eq_left hs, ← HaarLevel.haarAt_mul hR h hs.choose_spec.1,
    ← HaarLevel.haarAt_mul hs.choose_spec.1 hs.choose_spec.2 hR, mul_comm]

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticEqParabolicJParabolicJParabolic
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem unip_mem_symplecticGroup {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℚ}
    (hX : X.IsSymm) : (fromBlocks 1 X 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) ∈ symplecticGroup ι ℚ := by
  simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]

theorem symplectic_eq_parabolic_J_parabolic_J_parabolic :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∃ p₁ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₂ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₃ ∈ Matrix.symplecticGroup ι ℚ, p₁.toBlocks₂₁ = 0 ∧ p₂.toBlocks₂₁ = 0 ∧ p₃.toBlocks₂₁ = 0 ∧ σ = p₁ * Matrix.J ι ℚ * p₂ * Matrix.J ι ℚ * p₃ := by
  intro ι _ _ σ hσ
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, σ = fromBlocks A B C D :=
    ⟨_, _, _, _, σ.fromBlocks_toBlocks.symm⟩
  have hb := (SymplecticGroup.fromBlocks_mem_iff.1 hσ).1
  have hex : ∃ X : Matrix ι ι ℚ, X.IsSymm ∧ IsUnit (A + X * C).det := by
    have hker (x : ι → ℚ) (hAx : A *ᵥ x = 0) (hCx : C *ᵥ x = 0) : x = 0 := by
      have h :
          fromBlocks A B C D *ᵥ Sum.elim x 0 = fromBlocks A B C D *ᵥ Sum.elim 0 0 := by
        simp [fromBlocks_mulVec, hAx, hCx]
      have hu := (isUnit_iff_isUnit_det _).2 (SymplecticGroup.symplectic_det hσ)
      exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hu h)).1
    -- Adapt the field construction in Mathlib.LinearAlgebra.SymplecticGroup.
    obtain ⟨V, U, s, hV, hU, hP⟩ := exists_rank_normal_form C
    set P := V * C * U with P_def
    set Q := Vᵀ⁻¹ * A * U with Q_def
    let f (M : Matrix ι ι ℚ) := M.submatrix s.symm s.symm
    have hf (M : Matrix ι ι ℚ) : f M = M.submatrix s.symm s.symm := rfl
    have f_unit {M} : IsUnit M → IsUnit (f M) := (isUnit_submatrix_equiv ..).2
    have f_mul (M N : Matrix ι ι ℚ) : f (M * N) = f M * f N :=
      submatrix_mul _ _ _ _ _ s.symm.bijective
    have _ : Invertible V := hV.invertible
    have _ : Invertible U := hU.invertible
    have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
    have hker' (x : Fin C.rank ⊕ Fin (Fintype.card ι - C.rank) → ℚ)
        (hQx : f Q • x = 0) (hPx : f P • x = 0) : x = 0 := by
      refine (f_unit hU).smul_left_cancel.1 ?_
      rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
        smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at hQx hPx
      · rw [Equiv.comp_symm_eq, Pi.zero_comp] at hQx hPx
        exact s.surjective.injective_comp_right <| by simpa using hker _ hQx hPx
      · exact f_unit hV
      · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
    have hsymm : Qᵀ * P = Pᵀ * Q := by
      simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose,
        Q_def, inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
      rw [← mul_assoc Aᵀ, hb, mul_assoc]
    have hblocks : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
      apply_fun reindex s s at hsymm
      rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ, hP, hf,
        ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf (_)ᵀ, hf
        ((fromBlocks 1 0 0 0).submatrix _ _)] at hsymm
      simp [fromBlocks_transpose, fromBlocks_multiply] at hsymm
      tauto
    have hunit : IsUnit (f Q).toBlocks₂₂ := by
      refine mulVec_injective_iff_isUnit.1 ?_
      rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
      refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
        (hker' _ ?_ ?_).trans Sum.elim_zero_zero.symm
      · rw [← (f Q).fromBlocks_toBlocks]
        simp [hx, hblocks.2, fromBlocks_mulVec]
      · simp [hf, hP, fromBlocks_mulVec]
    set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card ι - C.rank))
        (Fin C.rank ⊕ Fin (Fintype.card ι - C.rank)) ℚ :=
      fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
    have hY : Y.IsSymm := by
      rw [Y_def, isSymm_fromBlocks_iff]
      exact ⟨IsSymm.sub isSymm_one hblocks.1, by simp⟩
    set X := f Vᵀ * Y * f V with X_def
    refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_iff_isUnit_det _).1
      ((isUnit_submatrix_equiv s.symm s.symm).1 ?_)⟩
    · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY.eq, hf, transpose_submatrix,
        transpose_transpose, mul_assoc]
    · have heq : f (A + X.submatrix s s * C) = f Vᵀ * (f Q + Y * f P) * f U⁻¹ := by
        simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add,
          ← mul_assoc, ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _),
          mul_inv_of_invertible]
        simp [X_def]
        rfl
      rw [← hf, heq, IsUnit.mul_iff, IsUnit.mul_iff]
      refine ⟨⟨isUnit_of_invertible _, ?_⟩, f_unit (isUnit_nonsing_inv_iff.2 hU)⟩
      nth_rw 1 [Y_def, hP, ← (f Q).fromBlocks_toBlocks, hblocks.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
  obtain ⟨X, hX, hu⟩ := hex
  have h1 : (A + X * C)ᵀ * C = Cᵀ * (A + X * C) := by
    rw [transpose_add, transpose_mul, hX.eq, add_mul, mul_add, hb, Matrix.mul_assoc]
  generalize hc : A + X * C = c at hu h1
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hY : (C * c⁻¹).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_nonsing_inv]
    calc cᵀ⁻¹ * Cᵀ = cᵀ⁻¹ * (Cᵀ * c) * c⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = C * c⁻¹ := by rw [← h1, nonsing_inv_mul_cancel_left _ _ hcT]
  have hY' : C * c⁻¹ * c = C := nonsing_inv_mul_cancel_right _ _ hu
  generalize C * c⁻¹ = Y at hY hY'
  have hJ := SymplecticGroup.J_mem ι ℚ
  refine ⟨fromBlocks 1 (-X) 0 1, unip_mem_symplecticGroup hX.neg,
    fromBlocks 1 (-Y) 0 1, unip_mem_symplecticGroup hY.neg,
    J ι ℚ * fromBlocks 1 Y 0 1 * J ι ℚ * fromBlocks 1 X 0 1 * fromBlocks A B C D,
    mul_mem (mul_mem (mul_mem (mul_mem hJ (unip_mem_symplecticGroup hY)) hJ)
      (unip_mem_symplecticGroup hX)) hσ, by simp, by simp, ?_, ?_⟩
  · rw [Matrix.mul_assoc _ _ (fromBlocks A B C D), fromBlocks_multiply]
    simp only [Matrix.one_mul, hc]
    simp [J, fromBlocks_multiply, hY']
  · have e1 : (fromBlocks 1 (-Y) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) * fromBlocks 1 Y 0 1 = 1 := by
      simp [fromBlocks_multiply]
    have e2 : (fromBlocks 1 (-X) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) * fromBlocks 1 X 0 1 = 1 := by
      simp [fromBlocks_multiply]
    have e3 := J_squared ι ℚ
    generalize (fromBlocks 1 (-Y) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = y' at e1 ⊢
    generalize (fromBlocks 1 Y 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = y at e1 ⊢
    generalize (fromBlocks 1 (-X) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = x' at e2 ⊢
    generalize (fromBlocks 1 X 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = x at e2 ⊢
    generalize fromBlocks A B C D = s
    generalize J ι ℚ = j at e3 ⊢
    have e4 : ∀ m, j * (j * m) = -m := fun m => by rw [← mul_assoc, e3, neg_one_mul]
    have e5 : ∀ m, y' * (y * m) = m := fun m => by rw [← mul_assoc, e1, one_mul]
    have e6 : ∀ m, x' * (x * m) = m := fun m => by rw [← mul_assoc, e2, one_mul]
    simp only [mul_assoc, e4, mul_neg, e5, neg_neg, e6]

end GlobalTheory.SW
end

