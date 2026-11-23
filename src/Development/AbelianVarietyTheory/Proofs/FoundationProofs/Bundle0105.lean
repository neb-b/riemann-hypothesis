module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationTrivialEqZero
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem relTriv_gamma_of_dvd {N M : ℕ} (h : N ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

theorem toZModPow_eval_mulVec {l : ℕ} [Fact l.Prime] (n : ℕ) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n)) (u : Fin 2 → ℤ_[l]) (q : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval
      (((δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℤ_[l]) *ᵥ u) q) =
      PadicInt.toZModPow n (MvPolynomial.eval u q) := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ
  obtain ⟨a, b, c, d⟩ := hδ
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval]
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  have e : ∀ x : ℤ, PadicInt.toZModPow n ((x : ℤ_[l])) = (x : ZMod (l ^ n)) := fun x => map_intCast _ x
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e, a, b, c, d]

theorem rel_triv_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ →
      ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  intro Ω _ _ ε X l _ w Γ M₀ hM₀ hΓ b F hR hF
  obtain ⟨ψ, p, hψ, hFψ⟩ := hF
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, hK, M₁, hM₁, hχ⟩ := hR u n
  change AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n ((0 : X.Fn l) u)
  rw [Pi.zero_apply, map_zero]
  refine _root_.GlobalTheory.KZ.H3.kum_near_zero_eval Ω ε X l n (b u) χ hK ⟨M₁ * M₀ * l ^ n, ?_, fun δ hδ => ?_⟩
  · have : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    positivity
  have h1 : δ ∈ CongruenceSubgroup.Gamma M₁ := relTriv_gamma_of_dvd ⟨M₀ * l ^ n, by ring⟩ hδ
  have h0 : δ ∈ Γ := hΓ (relTriv_gamma_of_dvd ⟨M₁ * l ^ n, by ring⟩ hδ)
  have hl : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := relTriv_gamma_of_dvd ⟨M₁ * M₀, by ring⟩ hδ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hδI : mob (ofSL δ) Complex.I ∈ Hs := (_root_.GlobalTheory.KZ.mob_laws).1 _ _ hI
  have key := hχ δ h1 Complex.I hI
  beta_reduce at key
  rw [← key, hFψ _ hδI, hFψ _ hI, ← hψ δ h0 Complex.I hI]
  simp only [map_add (f := _), GlobalTheory.KZ.Betti.eval_slP, add_sub_add_right_eq_sub, map_sub,
    toZModPow_eval_mulVec n hl, sub_self, Pi.zero_apply]

end GlobalTheory.KZ.H3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOver
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem dd_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ) :=
  (CuspForm.discriminant).holo'

theorem inR_mdifferentiable : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro E f ⟨N, w, hN, _, hq⟩
  obtain ⟨a, ha, _⟩ := hq 1
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) :=
    ha.mdifferentiable hN
  have hD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w) := fun τ => (dd_mdifferentiable τ).pow w
  have hdiv := hg.div hD (fun τ => pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ))
  have heq : ((fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) / fun τ : ℍ => DD τ ^ w) = f := by
    funext τ
    have h0 : DD τ ^ w ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    simp only [Pi.div_apply, one_smul]
    field_simp
  rwa [heq] at hdiv

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemClosureOfFixed
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ArtinFix

variable {K G : Type} [Field K] [Group G] (ρ : G →* RingAut K)

lemma rho_mul_apply (a b : G) (x : K) : ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul]; rfl

lemma rho_inv_apply_apply (g : G) (x : K) : ρ g⁻¹ (ρ g x) = x := by
  rw [← rho_mul_apply, inv_mul_cancel, map_one]; rfl

lemma rho_apply_inv_apply (g : G) (x : K) : ρ g (ρ g⁻¹ x) = x := by
  rw [← rho_mul_apply, mul_inv_cancel, map_one]; rfl

variable (Δ : Subgroup G)

def fixSub : Subfield K where
  carrier := {x | ∀ δ ∈ Δ, ρ δ x = x}
  mul_mem' := by
    intro a b ha hb δ hδ
    simp [map_mul, ha δ hδ, hb δ hδ]
  one_mem' := by intro δ _; simp
  add_mem' := by
    intro a b ha hb δ hδ
    simp [map_add (f := _), ha δ hδ, hb δ hδ]
  zero_mem' := by intro δ _; simp
  neg_mem' := by
    intro a ha δ hδ
    simp [map_neg, ha δ hδ]
  inv_mem' := by
    intro a ha δ hδ
    simp [map_inv₀, ha δ hδ]

lemma map_mem_fixSub [hN : Δ.Normal] (g : G) {x : K} (hx : x ∈ fixSub ρ Δ) :
    ρ g x ∈ fixSub ρ Δ := by
  intro δ hδ
  have hm : g⁻¹ * δ * g ∈ Δ := by simpa using hN.conj_mem δ hδ g⁻¹
  have h := hx _ hm
  calc ρ δ (ρ g x) = ρ g (ρ (g⁻¹ * δ * g) x) := by
        rw [← rho_mul_apply, ← rho_mul_apply]; congr 1; group
    _ = ρ g x := by rw [h]

def restr [Δ.Normal] : G →* RingAut (fixSub ρ Δ) where
  toFun g :=
    { toFun := fun x => ⟨ρ g x, map_mem_fixSub ρ Δ g x.2⟩
      invFun := fun x => ⟨ρ g⁻¹ x, map_mem_fixSub ρ Δ g⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (rho_inv_apply_apply ρ g (x : K))
      right_inv := fun x => Subtype.ext (rho_apply_inv_apply ρ g (x : K))
      map_mul' := fun x y => Subtype.ext (map_mul (ρ g) (x : K) (y : K))
      map_add' := fun x y => Subtype.ext (map_add (ρ g) (x : K) (y : K)) }
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro a b
    ext x
    exact rho_mul_apply ρ a b x

lemma le_ker_restr [Δ.Normal] : Δ ≤ (restr ρ Δ).ker := by
  intro δ hδ
  rw [MonoidHom.mem_ker]
  ext x
  exact x.2 δ hδ

theorem mem_closure_of_fixed (K G : Type) [Field K] [Group G] (ρ : G →* RingAut K)
    (Δ : Subgroup G) (hN : Δ.Normal) (hfi : Δ.FiniteIndex) (Y : Set K) (f : K)
    (hY : ∀ y ∈ Y, ∀ δ ∈ Δ, ρ δ y = y) (hf : ∀ δ ∈ Δ, ρ δ f = f)
    (hfix : ∀ g : G, (∀ y ∈ Y, ρ g y = y) → ρ g f = f) :
    f ∈ Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y) := by
  let L := fixSub ρ Δ
  let act : G ⧸ Δ →* RingAut L := QuotientGroup.lift Δ (restr ρ Δ) (le_ker_restr ρ Δ)
  letI : MulSemiringAction (G ⧸ Δ) L := MulSemiringAction.compHom L act
  have hsmul : ∀ (g : G) (x : L), (((QuotientGroup.mk g : G ⧸ Δ) • x : L) : K) = ρ g x :=
    fun g x => rfl
  let F := FixedPoints.subfield (G ⧸ Δ) L
  let Y' : Set L := {y | (y : K) ∈ Y}
  let E : IntermediateField F L := IntermediateField.adjoin F Y'
  have hfE : (⟨f, hf⟩ : L) ∈ E := by
    rw [← IsGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    obtain ⟨q, rfl⟩ := FixedPoints.toAlgAut_surjective (G ⧸ Δ) L σ
    induction q using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk g : G ⧸ Δ) • (⟨f, hf⟩ : L) = ⟨f, hf⟩
      apply Subtype.ext
      rw [hsmul]
      apply hfix g
      intro y hy
      have h1 := hσ ⟨y, hY y hy⟩ (IntermediateField.subset_adjoin F Y' hy)
      have h2 := congrArg Subtype.val h1
      exact (hsmul g ⟨y, hY y hy⟩).symm.trans h2
  have hle : E.toSubfield ≤ (Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y)).comap L.subtype := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · apply Subfield.subset_closure
      left
      intro g
      have h1 := c.2 (QuotientGroup.mk g : G ⧸ Δ)
      exact (hsmul g _).symm.trans (congrArg Subtype.val h1)
    · exact Subfield.subset_closure (Or.inr hx)
  exact hle (show (⟨f, hf⟩ : L) ∈ E.toSubfield from hfE)

end GlobalTheory.ArtinFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemGammaOfMul
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.HeckeLev

def rep (M q : ℕ) (γ : SL(2, ℤ)) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]
  | some j => !![1, ((j : ℕ) : ℤ) * (M : ℤ); 0, (q : ℤ)]

theorem det_rep (M q : ℕ) (γ : SL(2, ℤ)) (o : Option (Fin q)) : (rep M q γ o).det = q := by
  cases o with
  | none => simp [rep, Matrix.det_mul, Matrix.det_fin_two]
  | some j => simp [rep, Matrix.det_fin_two]

abbrev red (M : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  (Int.castRingHom (ZMod M)).mapMatrix m

theorem red_mul (M : ℕ) (m m' : Matrix (Fin 2) (Fin 2) ℤ) : red M (m * m') = red M m * red M m' :=
  RingHom.map_mul _ _ _

theorem red_rep {M q : ℕ} {γ : SL(2, ℤ)} (hγ : DiagMod M q γ) (o : Option (Fin q)) :
    red M (rep M q γ o) = !![1, 0; 0, (q : ZMod M)] := by
  obtain ⟨h01, h10, h11⟩ := hγ
  simp only [en] at h01 h10 h11
  cases o with
  | some j =>
    ext i k; fin_cases i <;> fin_cases k <;> simp [rep, red]
  | none =>
    have hdet : (γ 0 0 : ZMod M) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this
      have := congrArg (fun z : ℤ => (z : ZMod M)) this; push_cast at this; exact this
    rw [h01, h10, h11] at hdet
    ext i k; fin_cases i <;> fin_cases k <;>
      simp [rep, red, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h11] <;> linear_combination hdet

theorem mem_Gamma_of_mul {M q : ℕ} (hqM : Nat.Coprime q M) (δ : SL(2, ℤ)) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (hm : red M m = !![1, 0; 0, (q : ZMod M)]) (h : red M ((δ : Matrix (Fin 2) (Fin 2) ℤ) * m) = !![1, 0; 0, (q : ZMod M)]) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  have hu : IsUnit (!![1, 0; 0, (q : ZMod M)] : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    simpa using (ZMod.unitOfCoprime q hqM).isUnit
  have h2 : red M (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (q : ZMod M)] = !![1, 0; 0, (q : ZMod M)] := by
    rw [← hm]; exact (RingHom.map_mul _ _ _).symm.trans (h.trans hm.symm)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  exact hu.mul_right_cancel (h2.trans (one_mul _).symm)

theorem map_rep {M q : ℕ} (hq : q.Prime) (hqM : Nat.Coprime q M) {γ : SL(2, ℤ)} (hγ : DiagMod M q γ)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma M) (o : Option (Fin q)) :
    ∃ o', ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma M ∧
      rep M q γ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o' := by
  set m := rep M q γ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) with hmdef
  have hm : m.det = q := by
    rw [hmdef, Matrix.det_mul, det_rep, Matrix.SpecialLinearGroup.det_coe, mul_one]
  have hδ1 : red M (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [CongruenceSubgroup.Gamma_mem'] at hδ
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod M) => (x : Matrix (Fin 2) (Fin 2) (ZMod M))) hδ
    simpa using this
  have hred : red M m = !![1, 0; 0, (q : ZMod M)] := by
    rw [hmdef, red_mul, hδ1, Matrix.mul_one, red_rep hγ]

  have fin : ∀ o' (g : Matrix (Fin 2) (Fin 2) ℤ), g * rep M q γ o' = m →
      ∃ g' : SL(2, ℤ), g' ∈ CongruenceSubgroup.Gamma M ∧ m = (g' : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o' := by
    intro o' g he
    have hd : g.det = 1 := by
      have := congrArg Matrix.det he
      rw [Matrix.det_mul, det_rep, hm] at this
      have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      exact mul_right_cancel₀ hq' (this.trans (one_mul _).symm)
    refine ⟨⟨g, hd⟩, ?_, he.symm⟩
    exact mem_Gamma_of_mul hqM _ (rep M q γ o') (red_rep hγ o') (by rw [show ((⟨g, hd⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = g from rfl, he, hred])
  rcases GlobalTheory.cosetPrimeDet q hq m hm with ⟨g, hg⟩ | ⟨k, hk, g, hg⟩
  · have hs : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨g', hg', he⟩ := fin none (g * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) (by
      rw [← hg]; show _ * ((γ : Matrix (Fin 2) (Fin 2) ℤ) * _) = _
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hs, Matrix.one_mul])
    exact ⟨none, g', hg', he⟩
  ·
    have hMq : IsCoprime (M : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM.symm
    obtain ⟨u, v, huv⟩ := hMq
    haveI := Fact.mk hq
    set j : ℕ := ((k : ZMod q) * (u : ZMod q)).val with hj
    have hjq : j < q := ZMod.val_lt _
    have hdiv : (q : ℤ) ∣ (j : ℤ) * M - k := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hj, ZMod.natCast_zmod_val]
      have := congrArg (fun z : ℤ => (z : ZMod q)) huv
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, add_zero] at this
      linear_combination (k : ZMod q) * this
    obtain ⟨t, ht⟩ := hdiv
    obtain ⟨g', hg', he⟩ := fin (some ⟨j, hjq⟩) (g * !![1, -t; 0, 1]) (by
      rw [← hg, Matrix.mul_assoc]; congr 1
      ext a b; fin_cases a <;> fin_cases b <;> simp [rep] <;> linear_combination ht)
    exact ⟨some ⟨j, hjq⟩, g', hg', he⟩

theorem rep_distinct {M q : ℕ} (hq : q.Prime) (hqM : Nat.Coprime q M) (γ : SL(2, ℤ)) (o o' : Option (Fin q))
    (h : SL(2, ℤ)) (H : (h : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o = rep M q γ o') : o = o' := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2; rw [Matrix.det_fin_two] at this; exact this
  have nd : ¬ (q : ℤ) ∣ 1 := by
    intro hd
    have : q ∣ 1 := by exact_mod_cast hd
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some k =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00
      exact nd ⟨h 0 0 * γ 0 0 + h 0 1 * γ 1 0, by linear_combination -e00⟩
  | some j =>
    cases o' with
    | none =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      have e10 := congrFun (congrFun H 1) 0
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
      exact nd ⟨γ 0 0 * h 1 1 - h 0 1 * γ 1 0, by rw [e00, e10] at hdet; linear_combination -hdet⟩
    | some k =>
      have e00 := congrFun (congrFun H 0) 0
      have e01 := congrFun (congrFun H 0) 1
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
      rw [e00] at e01
      have hdv : (q : ℤ) ∣ ((k : ℕ) - (j : ℕ) : ℤ) * M := ⟨h 0 1, by linear_combination -e01⟩
      have hc : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM
      have h2 := hc.dvd_of_dvd_mul_right hdv
      have hj := j.2
      have hk := k.2
      congr 1
      apply Fin.ext
      obtain ⟨c, hc⟩ := h2
      have hj' : ((j : ℕ) : ℤ) < q := by exact_mod_cast hj
      have hk' : ((k : ℕ) : ℤ) < q := by exact_mod_cast hk
      have hj0 : (0 : ℤ) ≤ (j : ℕ) := by positivity
      have hk0 : (0 : ℤ) ≤ (k : ℕ) := by positivity
      have hc0 : c = 0 := by
        rcases lt_trichotomy c 0 with hlt | heq | hgt
        · nlinarith
        · exact heq
        · nlinarith
      rw [hc0, mul_zero] at hc
      exact_mod_cast (by linarith : ((j : ℕ) : ℤ) = (k : ℕ))

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem prod_sl_inv (X : Tower Ω ε) (M : ℕ) {ι : Type} [Fintype ι]
    (r : ι → Matrix (Fin 2) (Fin 2) ℤ) (hr : ∀ i, 0 < (r i).det) (δ : SL(2, ℤ))
    (hmap : ∀ i, ∃ i', ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma M ∧
      r i * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * r i')
    (hdis : ∀ i i' (h : SL(2, ℤ)), (h : Matrix (Fin 2) (Fin 2) ℤ) * r i = r i' → i = i')
    (f : X.K) (hf : Lev X M f) :
    X.sl (ofSL δ) (∏ i, X.sl (toGQ (r i)) f) = ∏ i, X.sl (toGQ (r i)) f := by
  choose s g hg he using hmap
  have hdet1 : ∀ h : SL(2, ℤ), 0 < (h : Matrix (Fin 2) (Fin 2) ℤ).det := fun h => by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  have hinj : Function.Injective s := by
    intro i1 i2 h12
    have hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hg2 : (((g i2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g i2 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    symm
    apply hdis i2 i1 (g i1 * (g i2)⁻¹)
    have e1 := he i1
    have e2 := he i2
    rw [h12] at e1
    have a1 : r i1 = (g i1 : Matrix (Fin 2) (Fin 2) ℤ) * r (s i2) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← e1, Matrix.mul_assoc, hδ, Matrix.mul_one]
    have a2 : r i2 = (g i2 : Matrix (Fin 2) (Fin 2) ℤ) * r (s i2) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← e2, Matrix.mul_assoc, hδ, Matrix.mul_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, a1]
    conv_lhs => rw [a2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ (g i2 : Matrix (Fin 2) (Fin 2) ℤ), hg2, Matrix.one_mul]
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  rw [map_prod]
  have step : ∀ i, X.sl (ofSL δ) (X.sl (toGQ (r i)) f) = X.sl (toGQ (r (s i))) f := by
    intro i
    rw [← X.sl_mul, ← MobLaws.toGQ_SL, ← MobLaws.toGQ_mul _ _ (hr i) (hdet1 δ), he i,
      MobLaws.toGQ_mul _ _ (hdet1 (g i)) (hr (s i)), X.sl_mul, MobLaws.toGQ_SL, hf _ (hg i)]
  simp only [step]
  exact Equiv.prod_comp (Equiv.ofBijective s hbij) (fun i => X.sl (toGQ (r i)) f)

end GlobalTheory.KZ.ES.HeckeLev

namespace GlobalTheory.KZ.ES

theorem lev_heckeProd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ) (f : X.K) (γ : SL(2, ℤ)), 0 < M → q.Prime → Nat.Coprime q M → Lev X M f → DiagMod M q γ →
    Lev X M (Nq X M q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  intro Ω _ _ _ ε X M q f γ _ hq hqM hf hγ δ hδ
  have e : Nq X M q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f =
      ∏ o : Option (Fin q), X.sl (toGQ (HeckeLev.rep M q γ o)) f := by
    rw [Fintype.prod_option, mul_comm, Nq, Finset.prod_range]
    rfl
  rw [e]
  exact HeckeLev.prod_sl_inv X M (HeckeLev.rep M q γ)
    (fun o => by rw [HeckeLev.det_rep]; exact_mod_cast hq.pos) δ
    (HeckeLev.map_rep hq hqM hγ δ hδ) (HeckeLev.rep_distinct hq hqM γ) f hf

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMul
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem disc_pow_mul_slash : ∀ (w : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * f (γ • τ) := by
  intro w f γ
  funext τ
  rw [ModularForm.SL_slash_apply]
  have hd : (UpperHalfPlane.denom γ τ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ReciprocityTheory.ChartRestriction.L1.DD_smul, mul_pow, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongr
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

theorem normOp_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r →
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  intro R _ p hp σ hF h₁ h₂ r k hk hu he
  obtain ⟨b, hb⟩ := exists_basis_one_add_X_pow R p hF.complete
  exact normOp_congr_of_basis R p b hb h₁ h₂ r k hk hu he

end GlobalTheory.Col
end

