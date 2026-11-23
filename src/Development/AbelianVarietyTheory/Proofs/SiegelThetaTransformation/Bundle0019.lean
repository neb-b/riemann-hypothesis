module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.QuadCocycle
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HermComp

variable {N : ℕ}


open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {N : ℕ} in
theorem _root_.GlobalTheory.SW.HermComp.row_rel (g : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)
    (h : gᴴ * Matrix.J (Fin N) ℂ * g = Matrix.J (Fin N) ℂ) :
    g.toBlocks₁₁ * g.toBlocks₂₂ᴴ - g.toBlocks₁₂ * g.toBlocks₂₁ᴴ = 1 ∧
      g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = g.toBlocks₂₁ * g.toBlocks₂₂ᴴ := by
  set J := Matrix.J (Fin N) ℂ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hleft : (-(J * gᴴ * J)) * g = 1 := by
    have : J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, this, h, hJJ, neg_neg]
  have hright : g * (-(J * gᴴ * J)) = 1 := mul_eq_one_comm.mp hleft
  have hgJ : g * J * gᴴ = J := by
    have h1 : g * J * gᴴ * J = -1 := by
      have := congrArg Neg.neg hright
      simpa [Matrix.mul_neg, Matrix.mul_assoc] using this
    calc g * J * gᴴ = g * J * gᴴ * J * (-J) := by
            rw [Matrix.mul_assoc (g * J * gᴴ), Matrix.mul_neg, hJJ, neg_neg, Matrix.mul_one]
      _ = J := by rw [h1, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  rw [← Matrix.fromBlocks_toBlocks g] at hgJ
  simp only [J, Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hgJ
  obtain ⟨-, h12, -, h22⟩ := hgJ
  simp only [Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul] at h12 h22
  constructor
  · rw [← neg_inj, neg_sub, ← h12]; abel
  · rw [← sub_eq_zero, ← h22]; abel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.SW.HermComp

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem inv_denominator_mul_lower_left_cocycle {N : ℕ}
    {A B C D C' D' Z : Matrix (Fin N) (Fin N) ℂ}
    (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hdet0 : (C * Z + D).det ≠ 0)
    (hdet1 : (C' * ((A * Z + B) * (C * Z + D)⁻¹) + D').det ≠ 0) :
    ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D') * (C * Z + D))⁻¹ * (C' * A + D' * C) =
      (C * Z + D)⁻¹ * ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D')⁻¹ * C') * (Z * Cᴴ + Dᴴ)⁻¹ +
        (C * Z + D)⁻¹ * C := by
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have hadj : (Z * Cᴴ + Dᴴ) * W = Z * Aᴴ + Bᴴ :=
    _root_.GlobalTheory.SW.HAct.den'_act h1 h2 h3 h4 hdet0
  have hinv : (Z * Cᴴ + Dᴴ)⁻¹ = A - W * C := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hadj]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3]
    abel
  have hunit : IsUnit (C' * W + D').det := isUnit_iff_ne_zero.mpr hdet1
  have hC : (C * Z + D)⁻¹ * C = (C * Z + D)⁻¹ * (C' * W + D')⁻¹ * ((C' * W + D') * C) := by
    rw [Matrix.mul_assoc ((C * Z + D)⁻¹), ← Matrix.mul_assoc ((C' * W + D')⁻¹),
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  rw [hinv, Matrix.mul_inv_rev, hC]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem matrix_of_apply_row {m r : Type} {α : Type} (f : m → r → α) (k : m) :
    Matrix.of f k = f k := rfl


open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
theorem _root_.GlobalTheory.SW.transH_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (γ γ' : _root_.GlobalTheory.SW.M2 E N), γ ∈ _root_.GlobalTheory.SW.UU E N → γ' ∈ _root_.GlobalTheory.SW.UU E N → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' = _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) * _root_.GlobalTheory.SW.hFac Ψ γ Z z z') ∧ ∀ φ ψ χ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.TransH Ψ γ φ ψ → _root_.GlobalTheory.SW.TransH Ψ γ' ψ χ → _root_.GlobalTheory.SW.TransH Ψ (γ' * γ) φ χ := by
  intro E _ _ _ Ψ n N γ γ' hγ hγ'
  have key : ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N,
      _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' =
        _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z)
          (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
          (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) *
        _root_.GlobalTheory.SW.hFac Ψ γ Z z z' := by
    intro Z hZ z z'
    obtain ⟨hτ, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
    obtain ⟨-, hden, -⟩ := hcomp γ' hγ'
    have hτ' := ((_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ' hγ').2 _ hmem).1
    unfold _root_.GlobalTheory.SW.hFac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hlow := (_root_.GlobalTheory.SW.HAct.mul_blocks (E := E) (τ : E →+* ℂ) γ γ').2.2.1
    obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.SW.HAct.blocks (by
      rw [← _root_.GlobalTheory.SW.HAct.map_blocks (E := E) (τ : E →+* ℂ) γ]
      exact _root_.GlobalTheory.SW.HAct.map_mem (τ : E →+* ℂ) hγ)
    have hM := inv_denominator_mul_lower_left_cocycle (C' := (toBlocks₂₁ γ').map (τ : E →+* ℂ))
      (D' := (toBlocks₂₂ γ').map (τ : E →+* ℂ)) (Z := Z τ) h1 h2 h3 h4 (hτ τ).1 (hτ' τ).1
    rw [hden τ, Matrix.det_mul, mul_pow, hlow]
    simp only [_root_.GlobalTheory.SW.hDen, _root_.GlobalTheory.SW.hDen',
      _root_.GlobalTheory.SW.hAct] at hM ⊢
    rw [hM]
    simp only [matrix_of_apply_row, Matrix.add_mulVec, dotProduct_add, Finset.sum_add_distrib,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_add,
      Complex.exp_add]
    ring
  refine ⟨key, fun φ ψ χ hφ hψ Z hZ z z' => ?_⟩
  obtain ⟨-, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hact, hden, hadj⟩ := hcomp γ' hγ'
  have hvar : (fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ (γ' * γ) Z τ)⁻¹ *ᵥ z τ k) =
      fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ *ᵥ
          (Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) k := by
    funext τ
    congr 1
    funext k
    rw [hadj τ, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    rfl
  have hvar' : (fun τ => Matrix.of fun k =>
        z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ (γ' * γ) Z τ)⁻¹) =
      fun τ => Matrix.of fun k =>
        (Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) k ᵥ*
          (_root_.GlobalTheory.SW.hDen Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ := by
    funext τ
    congr 1
    funext k
    rw [hden τ, Matrix.mul_inv_rev, ← Matrix.vecMul_vecMul]
    rfl
  rw [hact, hvar, hvar', hψ _ hmem, hφ Z hZ z z', key Z hZ z z', mul_assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatRationalCoordsIntegralProportional
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HaarProp

open HaarLevel

theorem mem_perSub' {K κ ι : Type} [Field K] (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, IntM y ∧ R • y = x := by
  rw [mem_perSub]
  simp only [intM_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩

theorem transport {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (t : AddSubgroup B)
    (φ : B → ℂ) (hφ : ∀ x, ∀ y ∈ t, φ (x + y) = φ x) :
    ∃ g : (A ⧸ t.comap e.toAddMonoidHom) ≃ (B ⧸ t), ∀ q, φ (e q.out) = φ (g q).out := by
  refine ⟨(QuotientAddGroup.congr (t.comap e.toAddMonoidHom) t e
    (AddSubgroup.map_comap_eq_self_of_surjective e.surjective t)).toEquiv, fun q => ?_⟩
  set g := QuotientAddGroup.congr (t.comap e.toAddMonoidHom) t e
    (AddSubgroup.map_comap_eq_self_of_surjective e.surjective t)
  have h2 : g q = (e q.out : B ⧸ t) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' q]
    rfl
  have h3 : ((g q).out : B ⧸ t) = (e q.out : B ⧸ t) := by
    rw [QuotientAddGroup.out_eq', h2]
  have := hφ (g q).out _ (QuotientAddGroup.eq.1 h3)
  change _ = φ (g q).out
  rw [← this]; congr 1; abel

variable {K K' κ ι κ' ι' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
  [Fintype κ] [Fintype ι] [Fintype κ'] [Fintype ι']

theorem haar_comp (e : Matrix κ ι K ≃+ Matrix κ' ι' K') (D D' : ℕ) (hD : 0 < D) (hD' : 0 < D')
    (h1 : ∀ x, IntM x → IntM (D • e x)) (h2 : ∀ x, IntM x → IntM (D' • e.symm x))
    (hd : Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) =
      Module.finrank ℚ K' * (Fintype.card κ' * Fintype.card ι')) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix κ' ι' K' → ℂ, IsSB φ → haar (fun m => φ (e m)) = c * haar φ := by
  set d := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) with hdd
  let t : ℕ → AddSubgroup (Matrix κ ι K) := fun R => (perSub K' κ' ι' R).comap e.toAddMonoidHom
  have ht : ∀ R x, x ∈ t R ↔ ∃ y, IntM y ∧ R • y = e x := fun R x => mem_perSub' R (e x)
  have hle : ∀ R, perSub K κ ι (R * D) ≤ t R := by
    intro R x hx
    obtain ⟨y, hy, rfl⟩ := (mem_perSub' _ _).1 hx
    exact (ht _ _).2 ⟨_, h1 y hy, by rw [map_nsmul, mul_smul]⟩
  have hne : (perSub K κ ι D).relIndex (t 1) ≠ 0 := by
    have hle' : t (1 * (D * D')) ≤ perSub K κ ι D := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := (ht _ _).1 hx
      refine (mem_perSub' _ _).2 ⟨_, h2 y hy, ?_⟩
      rw [← mul_smul, ← map_nsmul, ← one_mul (D * D'), hxy, e.symm_apply_apply]
    have h0 : (t (1 * (D * D'))).relIndex (t 1) ≠ 0 := by
      rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective e.surjective,
        relIndex_perSub _ _ one_pos]
      positivity
    exact fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle' h)
  have hsc : ∀ R, 0 < R → (perSub K κ ι (R * D)).relIndex (t R) =
      (perSub K κ ι D).relIndex (t 1) := by
    intro R hR
    have ha : (perSub K κ ι (R * D)).comap (nsmulAddMonoidHom R) = perSub K κ ι D := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_perSub', nsmulAddMonoidHom_apply, mul_smul,
        nsmul_cancel hR]
    have hb : (t 1).map (nsmulAddMonoidHom R) = t R := by
      ext x
      simp only [AddSubgroup.mem_map, ht, nsmulAddMonoidHom_apply, one_smul]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨_, hz, by rw [map_nsmul]⟩
      · rintro ⟨y, hy, hxy⟩
        refine ⟨e.symm y, ⟨y, hy, by simp⟩, ?_⟩
        rw [← map_nsmul, hxy, e.symm_apply_apply]
    rw [← ha, AddSubgroup.relIndex_comap, hb]
  refine ⟨((perSub K κ ι D).relIndex (t 1) : ℝ) / (D : ℝ) ^ d, by positivity, fun φ hφ => ?_⟩
  obtain ⟨S, hS, hψ⟩ : IsSB (fun m => φ (e m)) :=
    Dict.isSB_comp e.toAddMonoidHom D D' hD hD' h1 (fun x hx => by simpa using h2 _ hx) hφ
  obtain ⟨R, hR, hφ⟩ := hφ
  obtain ⟨g, hg⟩ := transport e (perSub K' κ' ι' R) φ (periodic hφ)
  have hidx : (perSub K κ ι (R * D * S)).relIndex (t R) =
      S ^ d * (perSub K κ ι D).relIndex (t 1) := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (perSub_le (R * D) S) (hle R), hsc R hR,
      relIndex_perSub _ _ (by positivity)]
  have hfin : (Function.support fun q : Matrix κ ι K ⧸ t R => φ (e q.out)).Finite := by
    have := (finite_support hR hφ).preimage (f := g) g.injective.injOn
    refine this.subset fun q hq => ?_
    simp only [Set.mem_preimage, Function.mem_support] at hq ⊢
    rwa [← hg]
  have hsum := finsum_quotient_of_le ((perSub_le (R * D) S).trans (hle R))
    (by rw [hidx]; positivity) (fun m => φ (e m))
    (fun x y hy => by rw [map_add (f := _)]; exact periodic hφ _ _ hy) hfin
  have hsum2 : ∑ᶠ q : Matrix κ ι K ⧸ t R, φ (e q.out) =
      ∑ᶠ q : Matrix κ' ι' K' ⧸ perSub K' κ' ι' R, φ q.out := by
    rw [← finsum_comp_equiv g]
    exact finsum_congr hg
  rw [(haar_eq_haarAt _ _ _ S _ hS hψ).1, (haar_eq_haarAt _ _ _ R _ hR hφ).1,
    ← haarAt_mul hS hψ (S := R * D) (by positivity), mul_comm S, haarAt, haarAt, hsum, hsum2, hidx,
    ← hd, ← hdd]
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hD'' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  rw [mul_pow, mul_pow]
  field_simp

end GlobalTheory.SW.HaarProp

theorem GlobalTheory.SW.haar_ofQ_proportional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by
  intro E _ _ _ n N
  obtain ⟨D, hD, h⟩ := Dict.exists_den_ofQ (E := E) (n := n) (N := N)
  obtain ⟨D', hD', h'⟩ := Dict.exists_den_symm (E := E) (n := n) (N := N)
  exact HaarProp.haar_comp (Dict.ofQEquiv E n N) D D' hD hD' h h' (by simp; ring)
end

