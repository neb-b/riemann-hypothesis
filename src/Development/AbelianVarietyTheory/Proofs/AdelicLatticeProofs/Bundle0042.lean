module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AevalSumElimEqZeroOfMemPts
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem tensor_eq_zero_of_forall_contract {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (t : V ⊗[ℚ] W)
    (h : ∀ m : W →ₗ[ℚ] ℚ, TensorProduct.rid ℚ V (LinearMap.lTensor V m t) = 0) : t = 0 := by
  first
  | exact @_root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions
  | exact _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions
  | (apply _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions ..)

theorem aeval_sum_elim_eq_zero_of_tensor {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (hΓ : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ)
    (t : MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ)
    (ht : ∀ g ∈ Γ, ∀ h ∈ Γ, Algebra.TensorProduct.productMap
      (MvPolynomial.aeval (fun ij : ι × ι => g ij.1 ij.2))
      (MvPolynomial.aeval (fun ij : ι × ι => h ij.1 ij.2)) t = (0 : ℂ))
    (R : Type) [CommRing R] [Algebra ℚ R] (x : Matrix ι ι R) (hx : x ∈ pts Γ R)
    (y : Matrix ι ι R) (hy : y ∈ pts Γ R) :
    Algebra.TensorProduct.productMap
      (MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2))
      (MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2)) t = (0 : R) := by
  set ex : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R := MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) with hex
  set ey : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R := MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2) with hey
  have key : TensorProduct.map ex.toLinearMap ey.toLinearMap t = 0 := by
    apply tensor_eq_zero_of_forall_contract
    intro m
    have h1 : TensorProduct.rid ℚ _ (LinearMap.lTensor _ (m ∘ₗ ey.toLinearMap) t) ∈ vanI Γ := by
      intro g hg
      set eg : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] ℂ := MvPolynomial.aeval (fun ij : ι × ι => g ij.1 ij.2) with heg
      refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun l => ?_
      let φ : MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ →ₐ[ℚ] MvPolynomial (ι × ι) ℂ :=
        Algebra.TensorProduct.productMap
          (((Algebra.ofId ℂ (MvPolynomial (ι × ι) ℂ)).restrictScalars ℚ).comp eg)
          (MvPolynomial.mapAlgHom (Algebra.ofId ℚ ℂ))
      have h2 : TensorProduct.lid ℚ _ (LinearMap.rTensor _ (l ∘ₗ eg.toLinearMap) t) ∈ vanI Γ := by
        refine _root_.GlobalTheory.ClassFin.component_mem_vanI ι Γ hΓ (φ t) ?_ l _ ?_
        · intro h hh
          rw [← ht g hg h hh]
          clear ht
          induction t using TensorProduct.induction_on with
          | zero => simp [evC]
          | tmul a b =>
            simp [evC, φ, ← heg, MvPolynomial.eval_map, MvPolynomial.aeval_def, Algebra.ofId_apply]
          | add s t hs ht =>
            simp only [evC] at hs ht
            simp only [evC, map_add (f := _), hs, ht]
        · intro k
          clear ht
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul a b =>
            simp [φ, MvPolynomial.coeff_map, Algebra.ofId_apply]
            rw [mul_comm (eg a), ← eq_ratCast (algebraMap ℚ ℂ), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
          | add s t hs ht => simp only [map_add (f := _), MvPolynomial.coeff_add, hs, ht]
      have h3 : ey _ = 0 := hy _ h2
      have h4 := congrArg m h3
      rw [map_zero] at h4
      rw [← h4]
      change l (eg _) = _
      clear ht h2 h3 h4
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [mul_comm]
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    have h5 : ex _ = 0 := hx _ h1
    rw [← h5]
    clear ht h1 h5
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have h6 := congrArg (LinearMap.mul' ℚ R) key
  rw [map_zero] at h6
  rw [← h6]
  clear ht key h6
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

theorem aeval_sum_elim_eq_zero_of_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ F : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ, (∀ g ∈ Γ, ∀ h ∈ Γ, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => g ij.1 ij.2) (fun ij : ι × ι => h ij.1 ij.2)) F = (0 : ℂ)) → ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2)) F = (0 : R) := by
  intro ι _ _ Γ hΓ F hF R _ _ x hx y hy
  let T : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ →ₐ[ℚ]
      MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ :=
    MvPolynomial.aeval (Sum.elim (fun ij => MvPolynomial.X ij ⊗ₜ 1) (fun ij => 1 ⊗ₜ MvPolynomial.X ij))
  have hT : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (a b : ι × ι → S),
      Algebra.TensorProduct.productMap (MvPolynomial.aeval a) (MvPolynomial.aeval b) (T F) =
        MvPolynomial.aeval (Sum.elim a b) F := by
    intro S _ _ a b
    have : (Algebra.TensorProduct.productMap (MvPolynomial.aeval a) (MvPolynomial.aeval b)).comp T =
        MvPolynomial.aeval (Sum.elim a b) := by
      ext (i | i) <;> simp [T]
    exact DFunLike.congr_fun this F
  rw [← hT]
  refine aeval_sum_elim_eq_zero_of_tensor Γ hΓ _ (fun g hg h hh => ?_) R x hx y hy
  rw [hT]
  exact hF g hg h hh

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentBlockDiagPartKillsSpan
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_blk_eq_zero : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨W, hWinv, hWσ, a, ha_span, ha0, ha_into, ha_kill⟩ := _root_.GlobalTheory.ClassFin.exists_socle_radical_of_not_ss ι Γ hΓ hss
  obtain ⟨e, hee, hW⟩ := GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace ι W hWσ

  have hEE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, hee]
  have hEmem : ∀ v, e.map (algebraMap ℚ ℂ) *ᵥ v ∈ W := fun v => by
    rw [hW, Matrix.mulVec_mulVec, hEE]
  have hfix : ∀ w ∈ W, e.map (algebraMap ℚ ℂ) *ᵥ w = w := fun w hw => (hW w).1 hw
  refine ⟨e, hee, ?_, a, ha_span, ha0, ?_⟩
  ·
    intro g hg
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      hfix _ (hWinv g hg _ (hEmem v)), sub_self, Matrix.zero_mulVec]
  ·
    rw [Matrix.ext_iff_mulVec]
    intro v
    unfold blk
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha_kill _ (hEmem v),
      Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, hfix _ (ha_into _), sub_self, Matrix.zero_mulVec]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitNotLocalKummerNormOfNotPow
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem nonnorm_pIdx_map (p : ℕ) {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Injective f) (U : Subgroup G) : pIdx p (U.map f) = pIdx p U := by
  have h : pows p (U.map f) = (pows p U).map f := by
    unfold pows
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  unfold pIdx
  rw [h, Subgroup.relIndex_map_map_of_injective _ _ hf]

theorem nonnorm_pTor_map (p : ℕ) {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Injective f) (U : Subgroup G) : pTor p (U.map f) = pTor p U := by
  unfold pTor
  symm
  refine Nat.card_eq_of_bijective
    (fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2.1, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    refine ⟨⟨x, hx, hf ?_⟩, rfl⟩
    rw [map_pow, h, map_one]

theorem exists_local_nonnorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ δ : F)
    (v : HeightOneSpectrum (𝓞 F)), p.Prime → IsPrimitiveRoot ζ p →
    (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ) →
    ∃ c : (v.adicCompletion F)ˣ, c ∉ kNorm p (RingHom.id (v.adicCompletion F))
      (algebraMap F (v.adicCompletion F) δ) := by
  intro p F _ _ ζ δ v hp hζ hδ
  by_contra hall
  push_neg at hall
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hζ' : IsPrimitiveRoot (algebraMap F (v.adicCompletion F) ζ) p :=
    hζ.map_of_injective (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨L, _, _, θ, σ, hK⟩ := exists_isKum p (v.adicCompletion F) _ _ hp hζ' hδ
  obtain ⟨hfd, hrk, hσp, hfix, -, -, hnorm⟩ := _root_.GlobalTheory.CNorm.kummer_basic p _ L _ _ θ σ hK
  obtain ⟨e, he⟩ : ∃ e : ℕ, v.valuation F (p : F) = WithZero.exp (-(e : ℤ)) := by
    have h0 : v.valuation F (p : F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact_mod_cast hp.ne_zero
    have h1 : v.valuation F (p : F) ≤ 1 := by
      have := v.valuation_le_one (K := F) (p : 𝓞 F)
      simpa using this
    have h2 : WithZero.log (v.valuation F (p : F)) ≤ 0 := by
      rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      exact h1
    refine ⟨(-WithZero.log (v.valuation F (p : F))).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
  obtain ⟨htL, hiL⟩ := GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e L hp.pos he
  obtain ⟨htK, hiK⟩ := GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e (v.adicCompletion F) hp.pos he
  rw [hrk] at hiL
  rw [Module.finrank_self, pow_one] at hiK
  have hQ : Ideal.absNorm v.asIdeal ^ e ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  generalize Ideal.absNorm v.asIdeal ^ e = Q at hiL hiK hQ
  let s : Lˣ →* Lˣ := Units.map (σ : L →* L)
  have hs : ∀ (n : ℕ) (a : Lˣ), ((s^[n] a : Lˣ) : L) = σ^[n] (a : L) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  let f : (v.adicCompletion F)ˣ →* Lˣ :=
    Units.map (algebraMap (v.adicCompletion F) L : v.adicCompletion F →* L)
  have hf : Function.Injective f :=
    Units.map_injective (algebraMap (v.adicCompletion F) L).injective
  have hfx : fix s = (⊤ : Subgroup (v.adicCompletion F)ˣ).map f := by
    ext a
    rw [mem_fix]
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := hfix a (congrArg Units.val ha)
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact a.ne_zero (by rw [hb, map_zero])
      exact ⟨Units.mk0 b hb0, trivial, Units.ext hb.symm⟩
    · rintro ⟨b, -, rfl⟩
      exact Units.ext (σ.commutes (b : v.adicCompletion F))
  have hiL0 : pIdx p (⊤ : Subgroup Lˣ) ≠ 0 := by
    rw [hiL]
    exact mul_ne_zero (mul_ne_zero hp.ne_zero (pow_ne_zero _ hQ)) htL
  obtain ⟨-, h1, -, -, hH⟩ := _root_.GlobalTheory.CNorm.herbrand_prime_order p Lˣ s hp
    (fun a => Units.ext (by rw [hs, hσp])) hiL0 htL
  have h0 : (nrm s p).range.relIndex (fix s) = 1 := by
    rw [Subgroup.relIndex_eq_one, hfx]
    rintro _ ⟨c, -, rfl⟩
    obtain ⟨y, hy⟩ := (hnorm c).1 (hall c)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ∏ i ∈ Finset.range p, σ^[i] (0 : L) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 hp.pos) rfl
      rw [this] at hy
      exact c.ne_zero ((map_eq_zero _).1 hy.symm)
    refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
    rw [nrm_apply, Units.coe_prod]
    simp only [hs, Units.val_mk0]
    exact hy
  rw [h0, hfx, nonnorm_pIdx_map p f hf, nonnorm_pTor_map p f hf, hiL, hiK, one_pow] at hH
  generalize pTor p (⊤ : Subgroup Lˣ) = tL at hH htL
  generalize pTor p (⊤ : Subgroup (v.adicCompletion F)ˣ) = tK at hH htK
  generalize (dif s).range.relIndex (nrm s p).ker = h at hH h1
  have hc : Q ^ p * tL * tK ^ p ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hQ) htL) (pow_ne_zero _ htK)
  have key : p = h ^ (p - 1) * p ^ p := by
    apply mul_right_cancel₀ hc
    rw [mul_pow, mul_pow] at hH
    linear_combination hH
  have hle : p ^ p ≤ p := by
    calc p ^ p ≤ h ^ (p - 1) * p ^ p := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (pow_ne_zero _ h1))
      _ = p := key.symm
  have hlt : p ^ 1 < p ^ p := Nat.pow_lt_pow_right hp.one_lt hp.one_lt
  rw [pow_one] at hlt
  omega

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

section
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} in
theorem _root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom (σ : Subrepresentation ρ) (h : IsAtom σ) :
    σ.toRepresentation.IsIrreducible := by
  let F : Subrepresentation σ.toRepresentation → Subrepresentation ρ := fun τ =>
    ⟨τ.toSubmodule.map σ.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨σ.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hinj : Function.Injective (Submodule.map σ.toSubmodule.subtype) :=
    Submodule.map_injective_of_injective σ.toSubmodule.injective_subtype
  have hle : ∀ τ, F τ ≤ σ := by
    intro τ
    show τ.toSubmodule.map σ.toSubmodule.subtype ≤ σ.toSubmodule
    rw [Submodule.map_le_iff_le_comap]
    intro w _
    exact w.2
  have hF : ∀ τ, F τ = ⊥ ∨ F τ = σ := fun τ => h.le_iff.mp (hle τ)
  have hbot : ∀ τ, F τ = ⊥ → τ = ⊥ := by
    intro τ hτ
    apply Subrepresentation.ext
    apply hinj
    have := congrArg Subrepresentation.toSubmodule hτ
    change _ = Submodule.map _ ⊥
    rw [Submodule.map_bot]
    exact this
  have htop : ∀ τ, F τ = σ → τ = ⊤ := by
    intro τ hτ
    apply Subrepresentation.ext
    apply hinj
    have := congrArg Subrepresentation.toSubmodule hτ
    simp only [F] at this
    rw [this]
    exact (Submodule.map_subtype_top σ.toSubmodule).symm
  have hne : (⊥ : Subrepresentation σ.toRepresentation) ≠ ⊤ := by
    intro he
    apply h.1
    have h1 : F ⊤ = σ := by
      apply Subrepresentation.ext
      exact Submodule.map_subtype_top σ.toSubmodule
    have h2 : F ⊥ = ⊥ := by
      apply Subrepresentation.ext
      exact Submodule.map_bot _
    rw [← h1, ← he, h2]
  haveI : Nontrivial (Subrepresentation σ.toRepresentation) := ⟨⟨⊥, ⊤, hne⟩⟩
  exact ⟨fun τ => (hF τ).imp (hbot τ) (htop τ)⟩

end

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private theorem iSup_atoms_toSubmodule_eq_whole_of_semisimple {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsSemisimpleRepresentation) :
    ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule = ⊤ := by
  haveI : ComplementedLattice (Subrepresentation ρ) := hρ
  haveI : WellFoundedLT (Subrepresentation ρ) :=
    StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule) fun a b hab =>
      lt_of_le_of_ne hab.le fun he => hab.ne (Subrepresentation.toSubmodule_injective he)
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  set A := ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule with hA
  let α : Subrepresentation ρ := ⟨A, by
    intro g v hv
    refine Submodule.iSup_induction _ (motive := fun v => ρ g v ∈ A) hv ?_ ?_ ?_
    · intro σ w hw
      exact (le_iSup (fun σ : {σ : Subrepresentation ρ // IsAtom σ} => σ.1.toSubmodule) σ)
        (σ.1.apply_mem_toSubmodule g hw)
    · simp
    · intro x y hx hy
      simpa using A.add_mem hx hy⟩
  obtain ⟨β, hβ⟩ := exists_isCompl α
  have hβbot : β = ⊥ := by
    rcases eq_bot_or_exists_atom_le β with h | ⟨τ, hτ, hτβ⟩
    · exact h
    · exfalso
      have hτα : τ ≤ α := fun v hv =>
        (le_iSup (fun σ : {σ : Subrepresentation ρ // IsAtom σ} => σ.1.toSubmodule) ⟨τ, hτ⟩) hv
      exact hτ.1 (le_bot_iff.mp (hβ.1 hτα hτβ))
  have hαtop : α = ⊤ := by
    have := hβ.2.eq_top
    rwa [hβbot, sup_bot_eq] at this
  exact congrArg Subrepresentation.toSubmodule hαtop


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsSemisimpleRepresentation → ρ'.IsSemisimpleRepresentation → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  intro G _ V _ _ ρ W _ _ ρ' _ _ hρ hρ'
  let J := {σ : Subrepresentation ρ // IsAtom σ} × {τ : Subrepresentation ρ' // IsAtom τ}
  let p : (j : J) → j.1.1.toSubmodule ⊗[ℂ] j.2.1.toSubmodule →ₗ[ℂ] V ⊗[ℂ] W := fun j =>
    TensorProduct.map j.1.1.toSubmodule.subtype j.2.1.toSubmodule.subtype
  refine _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range G (V ⊗[ℂ] W) (ρ.tprod ρ') J
    (fun j => j.1.1.toSubmodule ⊗[ℂ] j.2.1.toSubmodule)
    (fun j => j.1.1.toRepresentation.tprod j.2.1.toRepresentation) p ?_ ?_ ?_
  · intro j
    exact _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod_of_isIrreducible G _ _ _ _
      (_root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom j.1.1 j.1.2)
      (_root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom j.2.1 j.2.2)
  · intro j g v
    simp only [p]
    rw [Representation.tprod_apply, Representation.tprod_apply, ← LinearMap.comp_apply,
      ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
    rfl
  · rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨v, w, rfl⟩
    have hv : v ∈ ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule := by
      rw [iSup_atoms_toSubmodule_eq_whole_of_semisimple ρ hρ]; trivial
    have hw : w ∈ ⨆ τ : {τ : Subrepresentation ρ' // IsAtom τ}, τ.1.toSubmodule := by
      rw [iSup_atoms_toSubmodule_eq_whole_of_semisimple ρ' hρ']; trivial
    refine Submodule.iSup_induction _ (motive := fun v => ∀ w,
      w ∈ ⨆ τ : {τ : Subrepresentation ρ' // IsAtom τ}, τ.1.toSubmodule →
        v ⊗ₜ[ℂ] w ∈ ⨆ j, LinearMap.range (p j)) hv ?_ ?_ ?_ w hw
    · intro σ x hx w hw
      refine Submodule.iSup_induction _
        (motive := fun w => x ⊗ₜ[ℂ] w ∈ ⨆ j, LinearMap.range (p j)) hw ?_ ?_ ?_
      · intro τ y hy
        exact (le_iSup (fun j => LinearMap.range (p j)) (σ, τ))
          ⟨(⟨x, hx⟩ : σ.1.toSubmodule) ⊗ₜ[ℂ] (⟨y, hy⟩ : τ.1.toSubmodule), rfl⟩
      · simp
      · intro a b ha hb
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
    · intro w _
      simp
    · intro a b ha hb w hw
      rw [TensorProduct.add_tmul]
      exact Submodule.add_mem _ (ha w hw) (hb w hw)

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTop
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem normSub_id_le_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) :
    normSub (RingHom.id F) δ ≤ normSub φ δ := by
  intro x hx
  obtain ⟨a, b, hab⟩ := (mem_normSub _ _ x).1 hx
  refine (mem_normSub _ _ x).2 ⟨φ a, φ b, ?_⟩
  have hab' : (x : F) = a ^ 2 - δ * b ^ 2 := hab
  rw [hab']
  simp [map_sub, map_mul, map_pow]

theorem normSub_id_le_locNorm (F : Type) [Field F] [NumberField F] (δ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    normSub (RingHom.id F) δ ≤ locNorm F δ S :=
  le_inf (le_iInf₂ fun _ _ => normSub_id_le_normSub _ δ)
    (le_iInf fun _ => normSub_id_le_normSub _ δ)

theorem sUnits_sup_locNorm_ne_top : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by
  intro F _ _ δ S hS hδ hsq htop
  obtain ⟨hne, hle⟩ := _root_.GlobalTheory.QNorm.first_inequality_sUnits F δ S hS hδ hsq
  obtain ⟨-, hge⟩ := _root_.GlobalTheory.QNorm.two_pow_le_index_locNorm F (δ : F) S δ.ne_zero
  have h1 : (locNorm F δ S).index = (locNorm F δ S).relIndex (sUnits F S) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h2 : (locNorm F δ S).relIndex (sUnits F S) ≤
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) :=
    Subgroup.relIndex_le_of_le_left (normSub_id_le_locNorm F δ S) hne
  omega

end GlobalTheory.QNorm
end

