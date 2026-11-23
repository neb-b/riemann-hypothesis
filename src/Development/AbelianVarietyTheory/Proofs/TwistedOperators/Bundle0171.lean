module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMove

open GlobalTheory.SplitHecke

variable {D : D7} {S T : HSp D}

theorem act_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := map_add (actAdd S T g h) x y

theorem act_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := map_nsmul (actAdd S T g h) k x

theorem act_act_inv (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  have := actO_inv_actO g⁻¹ h⁻¹ u
  rwa [inv_inv, inv_inv] at this

theorem isHalf_of_act {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e (actO S T g h u)) :
    IsHalf e u := by
  have := isHalf_actO g⁻¹ h⁻¹ hu
  rwa [actO_inv_actO] at this

theorem isSBHalf_comp {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΨ
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k, hk, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · show Ψ _ = Ψ _
    rw [act_add, act_nsmul]
    exact h2 _ ((hΛ u).1 hu) (isHalf_actO g h hu') _
  · rw [hΛ, act_nsmul]
    exact h3 _ ht

theorem halfInd_act {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (t : WO S T) :
    halfInd e Λ (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  have : (actO S T g h t ∈ Λ ∧ IsHalf e (actO S T g h t)) ↔ (t ∈ Λ ∧ IsHalf e t) :=
    and_congr (hΛ t).symm ⟨isHalf_of_act g h, isHalf_actO g h⟩
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos ht, if_pos (this.2 ht)]
  · rw [if_neg ht, if_neg (fun hh => ht (this.1 hh))]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_theta_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ), (∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → ∀ (g : GA D S) (h : GA D T), (∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) → ∀ c c' : ℂ, c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g⁻¹ h⁻¹ x) = c' * Φ x) → om (g, h) f = (c * c') • f := by
  intro D ψ S T χS χT om hom e Λ f₀ Φ f hth hΘ g h hΛ c c' hc hf₀ hΦ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hΘ
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))
  have hT' : ∀ Ψ, Tm' Ψ = c⁻¹ • om (g, h) (Tm fun t => Ψ (actO S T g h t)) := fun Ψ => rfl
  have hP : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.trans _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hx)
      simp only [act_add, act_act_inv] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.modul _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hy)
      have h2 : ∀ t, symplO S T t (actO S T g⁻¹ h⁻¹ y) = symplO S T (actO S T g h t) y := fun t => by
        rw [← symplO_actO S T g h, act_act_inv]
      simp only [h2] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have h1 := hTm.vac
      rw [one_smul] at h1 ⊢
      have h2 : (fun t => halfInd e Λ (actO S T g h t)) = halfInd e Λ := funext (halfInd_act g h hΛ)
      rw [hT', h2, h1, hf₀, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have e1 : f = Tm Φ := hall Tm hTm
  have e2 : f = Tm' Φ := hall Tm' hP
  have e3 : Φ = c' • fun t => Φ (actO S T g h t) := by
    funext t
    have := hΦ (actO S T g h t)
    rw [actO_inv_actO] at this
    exact this
  rw [hT'] at e2
  have e4 : om (g, h) (Tm fun t => Φ (actO S T g h t)) = c • f := by
    rw [e2, smul_smul, mul_inv_cancel₀ hc, one_smul]
  calc om (g, h) f = om (g, h) (Tm (c' • fun t => Φ (actO S T g h t))) := by rw [← e3, ← e1]
    _ = (c * c') • f := by rw [map_smul, map_smul, e4, smul_smul, mul_comm]

end GlobalTheory.ThetaMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacProj

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem coords {m : ℕ} (v : Mx D S.rank m) :
    v = d.jX ⬝ (d.pX ⬝ v) + d.j0 ⬝ (d.p0 ⬝ v) + d.jY ⬝ (d.pY ⬝ v) := by
  conv_lhs => rw [← Matrix.one_mul v, ← d.sum_eq_one]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

theorem pY_inv (g : GA D S) : d.pY ⬝ mt S g⁻¹ = adj (mt S g ⬝ d.jX) ⬝ gA S := by
  rw [mt_inv, d.pY_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

theorem witt_anisotropic_projection_unitary_inv_eq (g : GA D S) : d.p0 ⬝ mt S g⁻¹ = giA S₀ ⬝ (adj (mt S g ⬝ d.j0) ⬝ gA S) := by
  rw [mt_inv, d.p0_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

def Keeps (g : GA D S) : Prop :=
  d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.j0) = 0

theorem expand {k m : ℕ} (Q : Mx D k S.rank) (A B : Mx D S.rank S.rank) (v : Mx D S.rank m) :
    Q ⬝ ((A * B) ⬝ v) = Q ⬝ (A ⬝ d.jX) ⬝ (d.pX ⬝ (B ⬝ v)) + Q ⬝ (A ⬝ d.j0) ⬝ (d.p0 ⬝ (B ⬝ v)) +
      Q ⬝ (A ⬝ d.jY) ⬝ (d.pY ⬝ (B ⬝ v)) := by
  conv_lhs => rw [← Matrix.mul_one A, ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem keeps_jX {g : GA D S} (h : Keeps d g) : mt S g ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.jX)) := by
  have e := coords d (mt S g ⬝ d.jX)
  rw [h.1, h.2.1] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem preserves_flag_anisotropic_action {g : GA D S} (h : Keeps d g) :
    mt S g ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0)) := by
  have e := coords d (mt S g ⬝ d.j0)
  rw [h.2.2] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem keeps_unitary {g : GA D S} (h : Keeps d g) :
    adj (d.p0 ⬝ (mt S g ⬝ d.j0)) ⬝ (gA S₀ ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0))) = gA S₀ := by
  have hXX : ∀ {k : ℕ} (M : Mx D ρ k), adj d.jX ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_XX, Matrix.zero_mul]
  have hX0 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.jX ⬝ (gA S ⬝ (d.j0 ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mul]
  have h0X : ∀ {k : ℕ} (M : Mx D ρ k), adj d.j0 ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_0X, Matrix.zero_mul]
  have h00 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.j0 ⬝ (gA S ⬝ (d.j0 ⬝ M)) = gA S₀ ⬝ M := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_00]
  have hu : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
    calc adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0))
        = adj d.j0 ⬝ ((adj (mt S g) * (gA S * mt S g)) ⬝ d.j0) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = gA S₀ := by rw [mt_unitary, d.gram_00]
  rw [preserves_flag_anisotropic_action d h] at hu
  generalize d.pX ⬝ (mt S g ⬝ d.j0) = P at hu
  generalize d.p0 ⬝ (mt S g ⬝ d.j0) = C at hu ⊢
  simpa only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, hX0, h0X, h00,
    Matrix.mul_zero, zero_add, add_zero] using hu

theorem keeps_mul {g g' : GA D S} (h : Keeps d g) (h' : Keeps d g') : Keeps d (g * g') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mt_mul, expand, h.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h.2.2, h'.2.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem keeps_inv {g : GA D S} (h : Keeps d g) : Keeps d g⁻¹ := by
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ ρ, mt S g ⬝ d.jX = d.jX ⬝ P := ⟨_, keeps_jX d h⟩
  obtain ⟨P', C, hC⟩ : ∃ (P' : Mx D ρ S₀.rank) (C : Mx D S₀.rank S₀.rank), mt S g ⬝ d.j0 = d.jX ⬝ P' + d.j0 ⬝ C := ⟨_, _, preserves_flag_anisotropic_action d h⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hC]
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.gram_XX, d.gram_0X,
      Matrix.mul_zero, add_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.gram_XX, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.mul_zero]

theorem preserves_flag_anisotropic_block_one_inv {g : GA D S} (h : Keeps d g) (h1 : d.p0 ⬝ (mt S g ⬝ d.j0) = 1) : d.p0 ⬝ (mt S g⁻¹ ⬝ d.j0) = 1 := by
  have e := preserves_flag_anisotropic_action d h
  rw [h1, Matrix.mul_one] at e
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ S₀.rank, mt S g ⬝ d.j0 = d.jX ⬝ P + d.j0 := ⟨_, e⟩
  rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hP]
  simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, d.gram_00,
    Matrix.mul_zero, zero_add]
  exact giA_mul_gA S₀

theorem keeps_one : Keeps d 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [mt_one, Matrix.one_mul]
  · exact d.p0_jX
  · exact d.pY_jX
  · exact d.pY_j0

def keepSub : Subgroup (GA D S) where
  carrier := {g | Keeps d g}
  one_mem' := keeps_one d
  mul_mem' := keeps_mul d
  inv_mem' := keeps_inv d

def keepSub1 : Subgroup (GA D S) where
  carrier := {g | Keeps d g ∧ d.p0 ⬝ (mt S g ⬝ d.j0) = 1}
  one_mem' := ⟨keeps_one d, by rw [mt_one, Matrix.one_mul, HypDec.p0_j0]⟩
  mul_mem' := fun {a b} ha hb => ⟨keeps_mul d ha.1 hb.1, by
    rw [mt_mul, expand, ha.1.1, ha.2, hb.1.2.2, hb.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul]⟩
  inv_mem' := fun {a} ha => ⟨keeps_inv d ha.1, preserves_flag_anisotropic_block_one_inv d ha.1 ha.2⟩

theorem flag_le : flagN d ≤ keepSub1 d := by
  intro n hn
  obtain ⟨T, b, -, hX, h0⟩ := exists_blocks d hn
  have eX : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.jX) = Q ⬝ d.jX + Q ⬝ d.jX ⬝ T := fun Q => by
    rw [hX, Matrix.mul_add, Matrix.mul_assoc]
  have e0 : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.j0) = Q ⬝ d.j0 + Q ⬝ d.jX ⬝ b := fun Q => by
    rw [h0, Matrix.mul_add, Matrix.mul_assoc]
  show (_ ∧ _ ∧ _) ∧ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [eX, d.p0_jX, Matrix.zero_mul, add_zero]
  · rw [eX, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.pY_j0, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.p0_j0, d.p0_jX, Matrix.zero_mul, add_zero]

theorem range_le : d.emb0.range ≤ keepSub d := by
  rintro _ ⟨h, rfl⟩
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.p0_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.pY_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.pY_j0, Matrix.zero_mul]

theorem jac_le : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) ≤ keepSub d :=
  sup_le (fun _ hg => (flag_le d hg).1) (range_le d)

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 h) ⬝ d.j0) = mt S₀ h := by
  have h1 : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := (flag_le d hn).2
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, h1,
    Matrix.one_mul]

def proj (g : (flagN d ⊔ d.emb0.range : Subgroup (GA D S))) : GA D S₀ :=
  ofMat S₀ (d.p0 ⬝ (mt S g.1 ⬝ d.j0)) (keeps_unitary d (jac_le d g.2))

theorem continuous_proj : Continuous (proj d) := by
  apply continuous_of_mt
  simp only [proj, mt_ofMat]
  exact continuous_const.matrix_mul (((continuous_mt S).comp continuous_subtype_val).matrix_mul continuous_const)

theorem proj_mul (h : GA D S₀) (n : flagN d) :
    proj d ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  apply mt_injective S₀
  simp only [proj, mt_ofMat]
  exact witt_anisotropic_block_flag_mul_embedded d n.2 h

theorem exists_continuous_proj : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ p : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) → GA D S₀, Continuous p ∧
      ∀ (h : GA D S₀) (n : flagN d),
        p ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ ρ d
  exact ⟨proj d, continuous_proj d, proj_mul d⟩

end GlobalTheory.JacProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionHomMulEmbeddedAnisotropic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacHom

variable {D : D7}

section Inv

variable {S T : HSp D}

theorem symplOH_mul_mt (a b : WO S T) (g : GA D S) :
    symplOH S T (a ⬝ mt S g) (b ⬝ mt S g) = symplOH S T a b := by
  have h1 : mt S g ⬝ mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  rw [mt_inv] at h1
  have key : mt S g ⬝ (giA S ⬝ adj (mt S g)) = giA S := by
    have e : mt S g ⬝ (giA S ⬝ adj (mt S g)) = mt S g ⬝ (giA S ⬝ (adj (mt S g) ⬝ gA S)) ⬝ giA S := by
      simp only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]
    rw [e, h1, Matrix.one_mul]
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul]
  have e2 : giA S ⬝ (adj (mt S g) ⬝ adj b ⬝ (gA T ⬝ (a ⬝ mt S g))) =
      (giA S ⬝ adj (mt S g) ⬝ adj b ⬝ gA T ⬝ a) ⬝ mt S g := by simp only [Matrix.mul_assoc]
  have e3 : mt S g ⬝ (giA S ⬝ adj (mt S g) ⬝ adj b ⬝ gA T ⬝ a) =
      (mt S g ⬝ (giA S ⬝ adj (mt S g))) ⬝ (adj b ⬝ (gA T ⬝ a)) := by simp only [Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_comm, e3, key]

theorem symplOH_mul_mt_right (a b : WO S T) (g : GA D S) :
    symplOH S T a (b ⬝ mt S g) = symplOH S T (a ⬝ mt S g⁻¹) b := by
  conv_lhs => rw [← symplOH_mul_mt a (b ⬝ mt S g) g⁻¹]
  rw [Matrix.mul_assoc b, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

end Inv

section FinalTheorems

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ)

theorem extX_mul (n : GA D S) : d.extX T x ⬝ mt S n =
    d.extX T (d.extX T x ⬝ mt S n ⬝ d.jX) + d.ext0 T (ptS d T x n) + d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) := by
  rw [HypDec.extX_apply, HypDec.matrixExtendByZero_apply, HypDec.extY_apply, HypDec.extX_apply, ptS, HypDec.extX_apply]
  conv_lhs => rw [← Matrix.mul_one (x ⬝ d.pX ⬝ mt S n), ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.mul_assoc]

variable {T x}

theorem extX_mul_jX (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x) {n : GA D S} (hn : n ∈ flagN d) :
    d.extX T x ⬝ mt S n ⬝ d.jX = x := by
  obtain ⟨M, b, hM, h1, -⟩ := exists_blocks d hn
  have htri : (1 + M).BlockTriangular id := fun i j (h : j < i) => by
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt h), hM i j (le_of_lt h), add_zero]
  have hdiag : ∀ i, (1 + M) i i = 1 := fun i => by rw [Matrix.add_apply, Matrix.one_apply_eq, hM i i le_rfl, add_zero]
  have hu : IsUnit (1 + M) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_of_upperTriangular htri]; simp only [hdiag, Finset.prod_const_one]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := fun i j => by
    refine ⟨fun h => ?_, ?_⟩
    · change (1 + M) i j = 0; exact htri h
    · change (1 + M) i i = 1; exact hdiag i
  have e : d.extX T x ⬝ mt S n ⬝ d.jX = x ⬝ (1 + M) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_add, ← Matrix.mul_assoc d.pX, d.pX_jX,
      Matrix.one_mul]
  rw [e]
  exact hx _ hmem

end FinalTheorems

section Flag

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} {x : Mx D T.rank ρ}
  (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x)
include hx

theorem extX_mul_flag {n : GA D S} (hn : n ∈ flagN d) : d.extX T x ⬝ mt S n =
    d.extX T x + d.ext0 T (ptS d T x n) + d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) := by
  have h := extX_mul d T x n
  rwa [extX_mul_jX d hx hn] at h

theorem ptS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    ptS d T x (n * n') = ptS d T x n + ptS d T x n' := by
  obtain ⟨M, b, -, -, h2⟩ := exists_blocks d hn'
  have e : ptS d T x (n * n') = d.extX T x ⬝ mt S n ⬝ (mt S n' ⬝ d.j0) := by
    rw [ptS, mt_mul, Matrix.mul_assoc (d.extX T x), Matrix.mul_assoc (d.extX T x), Matrix.mul_assoc]
  rw [e, extX_mul_flag d hx hn, h2]
  have e' : ptS d T x n' = d.extX T x ⬝ (d.j0 + d.jX ⬝ b) := by rw [ptS, Matrix.mul_assoc, h2]
  rw [e']
  simp only [HypDec.extX_apply, HypDec.matrixExtendByZero_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    d.pX_j0, d.p0_j0, d.pY_j0, d.p0_jX, d.pY_jX, cancel₂ d.p0_jX, cancel₂ d.pY_jX, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, add_zero, zero_add]

end Flag

section Flag2

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} {x : Mx D T.rank ρ}

theorem symplOH_neg_left' {A B : HSp D} (a b : WO A B) : symplOH A B (-a) b = -symplOH A B a b := by
  rw [eq_neg_iff_add_eq_zero, ← GlobalTheory.OrientedHeis.symplOH_add_left, neg_add_cancel, symplOH_zero_left]

theorem ptS_one : ptS d T x 1 = 0 := by
  rw [ptS, mt_one, Matrix.mul_one, HypDec.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero]

variable (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x)
include hx

theorem ptS_inv {n : GA D S} (hn : n ∈ flagN d) : ptS d T x n⁻¹ = -ptS d T x n := by
  have h := ptS_mul d hx (inv_mem hn) hn
  rw [inv_mul_cancel, ptS_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem cenS_flag {n : GA D S} (hn : n ∈ flagN d) :
    cenS d T x n = symplOH S T (d.extX T x) (d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY)) := by
  conv_lhs => rw [cenS, extX_mul_flag d hx hn]
  rw [GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_self, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, zero_add, zero_add]

theorem cenS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    cenS d T x (n * n') = cenS d T x n + cenS d T x n' + symplOH S₀ T (ptS d T x n) (ptS d T x n') := by
  have hi : n'⁻¹ ∈ flagN d := inv_mem hn'
  have h0 : symplOH S T (d.extX T x) (d.ext0 T (ptS d T x n) ⬝ mt S n') =
      symplOH S₀ T (ptS d T x n) (ptS d T x n') := by
    rw [symplOH_mul_mt_right, extX_mul_flag d hx hi, GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_extDual_extAnisotropic,
      ptS_inv d hx hn', symplOH_neg_left', symplOH_skew S₀ T (ptS d T x n), neg_neg, zero_add, add_zero]
  have hY : symplOH S T (d.extX T x) (d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) ⬝ mt S n') = cenS d T x n := by
    rw [symplOH_mul_mt_right, extX_mul_flag d hx hi, GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, symplOH_skew S T (d.extY T _) (d.ext0 T _), HypDec.wittDecomp_sympl_extDual_extAnisotropic,
      HypDec.symplOH_extY_extY, neg_zero, add_zero, add_zero, cenS_flag d hx hn]
  have e : cenS d T x (n * n') = symplOH S T (d.extX T x) (d.extX T x ⬝ mt S n ⬝ mt S n') := by
    rw [cenS, mt_mul, Matrix.mul_assoc]
  rw [e, extX_mul_flag d hx hn, Matrix.add_mul, Matrix.add_mul, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, h0, hY, ← cenS]
  ring

variable (ψ : AddChar (AF D.host.F) ℂ)

theorem jacS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) (f : WO S₀ T → ℂ) :
    jacS ψ d T x (n * n') f = jacS ψ d T x n (jacS ψ d T x n' f) := by
  funext w
  simp only [jacS, ptS_mul d hx hn hn', cenS_mul d hx hn hn', Pi.smul_apply, smul_eq_mul, heisO,
    GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem jacS_mul_levi (n : GA D S) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    jacS ψ d T x (n * d.levi u) = jacS ψ d T x n := by
  have hL : d.extX T x ⬝ mt S (d.levi u)⁻¹ = d.extX T x := by
    rw [← map_inv, HypDec.extX_levi, hx _ (inv_mem hu)]
  have hpt : ptS d T x (n * d.levi u) = ptS d T x n := by
    rw [ptS, ptS, mt_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (mt S (d.levi u)), d.wittDecomp_levi_inclAnisotropic]
  have hcen : cenS d T x (n * d.levi u) = cenS d T x n := by
    rw [cenS, cenS, mt_mul, ← Matrix.mul_assoc, symplOH_mul_mt_right, hL]
  funext f
  simp only [jacS, hpt, hcen]

end Flag2

section Conj

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} (x : Mx D T.rank ρ)

theorem witt_extension_hom_mul_embedded_anisotropic (g : GA D S₀) : d.extX T x ⬝ mt S (d.emb0 g) = d.extX T x := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding]

theorem extX_conj (n : GA D S) (g : GA D S₀) :
    d.extX T x ⬝ mt S (d.emb0 g * n * (d.emb0 g)⁻¹) = d.extX T x ⬝ mt S n ⬝ mt S (d.emb0 g⁻¹) := by
  rw [← map_inv, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, witt_extension_hom_mul_embedded_anisotropic]

theorem ptS_conj (n : GA D S) (g : GA D S₀) :
    ptS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S₀ T g 1 (ptS d T x n) := by
  rw [ptS, ptS, extX_conj, actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc (d.extX T x ⬝ mt S n), d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  exact (Matrix.mul_assoc _ _ _).symm

theorem cenS_conj (n : GA D S) (g : GA D S₀) :
    cenS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = cenS d T x n := by
  rw [cenS, cenS, extX_conj, symplOH_mul_mt_right, ← map_inv, inv_inv, witt_extension_hom_mul_embedded_anisotropic]

end Conj

theorem jacS_hom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (x : Mx D T.rank ρ), (∀ u ∈ UX D ρ, x ⬝ u.1 = x) → (∀ b c, cenS d T x (d.nB b * d.nC c) = d.qS T c x) ∧
    (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptS d T x (n * n') = ptS d T x n + ptS d T x n' ∧
      cenS d T x (n * n') = cenS d T x n + cenS d T x n' + symplOH S₀ T (ptS d T x n) (ptS d T x n') ∧
      ∀ f, jacS ψ d T x (n * n') f = jacS ψ d T x n (jacS ψ d T x n' f)) ∧
    (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacS ψ d T x (n * d.levi u) = jacS ψ d T x n) ∧
    ∀ n g, ptS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S₀ T g 1 (ptS d T x n) ∧
      cenS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = cenS d T x n := by
  intro D ψ S S₀ T ρ d x hx
  refine ⟨fun b c => ?_, fun n hn n' hn' => ⟨ptS_mul d hx hn hn', cenS_mul d hx hn hn', jacS_mul d hx ψ hn hn'⟩,
    fun n _ u hu => jacS_mul_levi d hx ψ n hu, fun n g => ⟨ptS_conj d x n g, cenS_conj d x n g⟩⟩
  have hB : d.nB b ∈ flagN d := d.nB_mem_NFlag b
  have hC : d.nC c ∈ flagN d := d.nC_mem_NFlag c
  have hpC : ptS d T x (d.nC c) = 0 := by
    rw [ptS, Matrix.mul_assoc, d.nC_j0, HypDec.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero]
  have e : pairS T x (x ⬝ (half D • (b ⬝ plus S₀ b))) = half D * hO S₀ T (x ⬝ b) (x ⬝ b) := by
    rw [← pairS_plus]
    simp only [pairS, Matrix.mul_smul, adj_smul, cA_half, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have h2 : symplOH S T (d.extX T x) (d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b)))) = 0 := by
    refine eq_of_add_self (F := D.host.F) ?_
    rw [HypDec.symplOH_extX_extY, e, trHalf_half, ← symplOH_eq, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
  have hcB : cenS d T x (d.nB b) = 0 := by
    have h1 : symplOH S T (d.extX T x) (d.extX T x ⬝ mt S (d.nB b)) +
        symplOH S T (d.extX T x) (d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b)))) = 0 := by
      rw [← GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.extX_nB, sub_add_cancel, GlobalTheory.OrientedHeis.symplOH_add_right,
        GlobalTheory.OrientedHeis.symplOH_self, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero]
    rw [h2, add_zero] at h1
    exact h1
  rw [cenS_mul d hx hB hC, hcB, cenS_nC, hpC, symplOH_zero_right, zero_add, add_zero]

end GlobalTheory.JacHom

end
end

