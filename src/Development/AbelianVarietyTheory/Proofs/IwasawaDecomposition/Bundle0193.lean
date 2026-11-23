module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Formalism.LocalRingCardinality.DataIdx
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActio
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_factor_of_bound {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : V →ₗ[ℂ] E) (ℓ : V →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖ℓ w‖ ≤ C * ‖Φ w‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ w, Λ (Φ w) = ℓ w := by
  have hk : LinearMap.ker Φ ≤ LinearMap.ker ℓ := fun w hw => by
    have := h w
    rw [LinearMap.mem_ker.1 hw, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let f₀ : LinearMap.range Φ →ₗ[ℂ] ℂ := (LinearMap.ker Φ).liftQ ℓ hk ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ w, f₀ ⟨Φ w, LinearMap.mem_range_self Φ w⟩ = ℓ w := fun w => by
    simp only [f₀, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ x, ‖f₀ x‖ ≤ C * ‖x‖ := by
    rintro ⟨_, w, rfl⟩
    exact (congrArg norm (hf w)).le.trans (h w)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) (f₀.mkContinuous C hb)
  exact ⟨g, fun w => (hg ⟨Φ w, LinearMap.mem_range_self Φ w⟩).trans (hf w)⟩

theorem exists_inner_of_pi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}
    (Λ : (Fin m → H) →L[ℂ] ℂ) : ∃ a : Fin m → H, ∀ x, Λ x = ∑ i, ⟪a i, x i⟫_ℂ := by
  refine ⟨fun i => (InnerProductSpace.toDual ℂ H).symm (Λ.comp (ContinuousLinearMap.single ℂ (fun _ => H) i)),
    fun x => ?_⟩
  simp only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, Finset.univ_sum_single]

theorem sobCont_repr : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∃ (m : ℕ) (ls : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (a : Fin m → H), (∀ i, ∀ X ∈ ls i, X ∈ lieG G) ∧ ∀ w ∈ smSub G (trRep σ P), ℓ w = ∑ i, ⟪a i, word (trRep σ P) (ls i) w⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ ⟨S, C, hS, hC⟩
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hl : ∀ i : Fin S.length, ∀ X ∈ S.get i, X ∈ lieG G := fun i => hS _ (List.get_mem S i)
  let Φ : smSub G (trRep σ P) →ₗ[ℂ] (Fin S.length → H) :=
    { toFun := fun w i => word (trRep σ P) (S.get i) w
      map_add' := fun v w => funext fun i => word_add hG hπ (hl i) v.2 w.2
      map_smul' := fun c w => funext fun i => word_smul hG hπ (hl i) c w.2 }
  have hb : ∀ w, ‖(ℓ ∘ₗ (smSub G (trRep σ P)).subtype) w‖ ≤ (|C| * S.length) * ‖Φ w‖ := fun w => by
    refine (hC w w.2).trans ?_
    have h1 : (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum ≤ S.length * ‖Φ w‖ := by
      have := List.sum_le_card_nsmul (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖) ‖Φ w‖ (by
        intro x hx
        obtain ⟨l, hl', rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hl'
        exact norm_le_pi_norm (Φ w) i)
      simpa using this
    have h0 : 0 ≤ (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    rw [mul_assoc]
    exact mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
  obtain ⟨Λ, hΛ⟩ := exists_factor_of_bound Φ _ _ hb
  obtain ⟨a, ha⟩ := exists_inner_of_pi Λ
  exact ⟨S.length, S.get, a, hl, fun w hw => (hΛ ⟨w, hw⟩).symm.trans (ha _)⟩

end GlobalTheory.SmVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Core

variable {K V M : Type} [Field K] {σ : K →+* ℂ} [AddCommGroup V] [Module K V]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]


omit [FiniteDimensional ℂ M] in
theorem inner_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) (x y : M) : inner ℂ (f x) (f y) = (n : ℂ) * inner ℂ x y := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have h1 : ∀ x, ‖((((Real.sqrt n)⁻¹ : ℝ) : ℂ) • f) x‖ = ‖x‖ := by
    intro x
    have h2 : ‖f x‖ = Real.sqrt n * ‖x‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), h, mul_pow, Real.sq_sqrt hn.le]
    rw [LinearMap.smul_apply, norm_smul, h2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  have h3 := (LinearMap.norm_map_iff_inner_map_map _).1 h1 x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hn.le] at h3
  rw [← h3, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne']
  simp

omit [FiniteDimensional ℂ M] in
theorem inj_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) : Function.Injective f := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have := h x
  rw [hx, norm_zero] at this
  have h2 : ‖x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 (show n * ‖x‖ ^ 2 = 0 by rw [← this]; simp) with h | h
    · exact absurd h hn.ne'
    · exact h
  simpa using h2

end Core

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : hform H x y = star x ⬝ᵥ H *ᵥ y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mulVec {n a b : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin a) K) (E' : Matrix (Fin n) (Fin b) K)
    (x : Fin a → K) (y : Fin b → K) : hform H (E *ᵥ x) (E' *ᵥ y) = star x ⬝ᵥ (Eᴴ * H * E') *ᵥ y := by
  rw [hform_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem hform_orth {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K}
    (h : IsOrthProj H E Pr) (z : Fin d → K) (x : Fin n → K) : hform H (E *ᵥ z) (E *ᵥ (Pr *ᵥ x)) = hform H (E *ᵥ z) x := by
  have h1 := hform_mulVec H E (1 - E * Pr) z x
  rw [h.2, Matrix.zero_mulVec, dotProduct_zero, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, sub_eq_zero,
    ← Matrix.mulVec_mulVec] at h1
  exact h1.symm

variable (S : CSD K) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

theorem csum_hform (x y : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm x : S.Forms) (S.basis.equivFun.symm y : S.Forms) = hform S.H x y :=
  (S.isClassSum x y).symm

theorem act_coord (t : G) (x : Fin S.dim → K) :
    r t (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.actMat r t *ᵥ x) :=
  Subtype.ext (S.I_actMat r t x).symm

theorem gaOp_coord (a : MonoidAlgebra K G) (x : Fin S.dim → K) :
    S.gaOp r a (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.gaMat r a *ᵥ x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [CSD.gaOp, CSD.gaMat, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, map_sum,
    map_smul, act_coord]

def lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : (Fin (S.lvlDim r P ψ) → K) →ₗ[K] S.Forms :=
  (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms) ∘ₗ (S.lvlE r P ψ).mulVecLin

theorem lvlForm_apply (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    lvlForm S r P ψ x = S.basis.equivFun.symm (S.lvlE r P ψ *ᵥ x) := rfl

theorem lvlForm_injective (P : Subgroup G) (ψ : P →* Kˣ) : Function.Injective (lvlForm S r P ψ) :=
  S.basis.equivFun.symm.injective.comp (image_idempotent_spec K _ _).1

theorem range_lvlE (P : Subgroup G) (ψ : P →* Kˣ) : LinearMap.range (S.lvlE r P ψ).mulVecLin = S.lvlPart r P ψ :=
  (image_idempotent_spec K _ _).2.trans (level_part_spec K S G r P ψ)

theorem range_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : Set.range (lvlForm S r P ψ) = lvlForms S r P ψ := by
  ext f
  obtain ⟨u, rfl⟩ := S.basis.equivFun.symm.surjective f
  have key : S.basis.equivFun.symm u ∈ lvlForms S r P ψ ↔ u ∈ S.lvlPart r P ψ := by
    refine forall_congr' fun h => ?_
    rw [act_coord, ← map_smul, S.basis.equivFun.symm.injective.eq_iff]
  rw [key, ← range_lvlE]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, S.basis.equivFun.symm.injective hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem csum_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) (x y : Fin (S.lvlDim r P ψ) → K) :
    S.csum (lvlForm S r P ψ x) (lvlForm S r P ψ y) = (Nat.card P : K) * hform (S.lvlH r P ψ) x y := by
  have hc : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  rw [lvlForm_apply, lvlForm_apply, csum_hform, hform_mulVec, hform_dot, CSD.lvlH, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rfl

theorem mem_lvlNab (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    x ∈ S.lvlNab r P ψ ↔ lvlForm S r P ψ x ∈ intForms S := by
  unfold CSD.lvlNab CSD.cutNab CSD.nabLat
  rw [exponent_index_lattice.mem_cutLat, mem_valLatF]
  rfl

end Coord

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lvlE_lvlOp (h : BlockHyp B ℓ v0 s) (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x) =
      B.S.gaMat B.r (idemOf ℓ.X) *ᵥ (B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ x) := by
  have hc := (idempotent_spec K v0 h.conj G ℓ.X h.irr).2 (lvlIdem ℓ.P ℓ.ψ)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ _ hc.symm).1]

theorem lvlE_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.lE ℓ Z *ᵥ z) = B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, BlockDat.lf_lvlE_lE h]
  rfl

theorem lvlForm_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    lvlForm B.S B.r ℓ.P ℓ.ψ (B.lE ℓ Z *ᵥ z) = B.toF ℓ Z z := by
  rw [lvlForm_apply, lvlE_lE h]
  rfl

theorem range_vE (h : BlockHyp B ℓ v0 s) : LinearMap.range (B.vE ℓ).mulVecLin =
    LinearMap.range (B.S.gaMat B.r (idemOf ℓ.X)).mulVecLin ⊓ B.S.lvlPart B.r ℓ.P ℓ.ψ :=
  good_part_spec K B.S G B.r ℓ.X h.irr ℓ.P ℓ.ψ

theorem lvlOp_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ (B.lE ℓ Z *ᵥ z) = B.lE ℓ Z *ᵥ z := by
  apply BlockDat.lf_lvlE_inj
  show B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _ = B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _
  rw [lvlE_lvlOp h, lvlE_lE h]
  have hm : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
  rw [range_vE h] at hm
  obtain ⟨⟨u, hu⟩, -⟩ := hm
  rw [← hu, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← (group_action_matrix_hom K B.S G B.r).2,
    (idempotent_spec K v0 h.conj G ℓ.X h.irr).1.idem]

theorem span_range_mulVec {σ : K →+* ℂ} {M : Type} [AddCommGroup M] [Module ℂ M] {n d : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (E : Matrix (Fin n) (Fin d) K) :
    Submodule.span ℂ (J '' Set.range fun z => E *ᵥ z) = Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    have hz : z = ∑ k, z k • (Pi.single k 1 : Fin d → K) := by
      ext i; simp [Pi.single_apply]
    rw [SetLike.mem_coe]
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, Matrix.mulVec_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Matrix.mulVec_smul, map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, rfl⟩

variable {σ : K →+* ℂ} {H M ML : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M] [AddCommGroup ML] [Module K ML]



end Block

end GlobalTheory.Mem.LiftForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharLocal

theorem psiV_ne_one_of_trace {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra hn
  push Not at hn
  have hs := GlobalTheory.SnMass.Inhab.stdAt_of_psiInf h hinf v
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have h1 := (hs (z * (algebraMap F (Fv F v) (d : F))⁻¹)).1 (fun y _ => hn _) d hd
  rw [inv_mul_cancel_right₀ hd1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  omega

theorem psiV_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1 := by
  intro D ψ hψ v
  have h := GlobalTheory.StdAdelicChar.isStdChar_inv hψ
  obtain ⟨θ, hθ⟩ := h.2.1
  obtain ⟨y, hy⟩ := psiV_ne_one_of_trace h.1 (fun a => by
    rw [h.2.2 θ hθ, GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _,
      GlobalTheory.StdRat.sum_tauE_eq_trace]
    simp) v
  refine ⟨y, fun h1 => hy ?_⟩
  rw [psiV] at h1 ⊢
  rw [AddChar.inv_apply', h1, inv_one]

end GlobalTheory.StdCharLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonz
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.StdProp

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_sigR [TopologicalSpace R] [IsTopologicalRing R] : Continuous (sigR R σ) := by
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  exact this

theorem continuous_qR [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 := continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem measurableSet_fibre [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [SecondCountableTopology R] (c : R) :
    MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E | qR R σ J (X 0) = c} :=
  (isClosed_eq (continuous_qR R σ J) continuous_const).measurableSet

omit [FiniteDimensional F E] in
theorem smul_eq_lrAct {n : ℕ} (g : HA R σ J) :
    (fun X : Fin n → Fin M → R ⊗[F] E => g • X) = lrAct (HA.mat R σ J g).val 1 := by
  funext X a
  show (HA.mat R σ J g).val.mulVec (X a) = _
  simp [lrAct, Matrix.one_apply]

end Local

theorem stdX_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → IsStdX s σ J β ν → ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 ∧ IsInvTup (AF F) σ J ν ∧ OnOrbit (AF F) σ J x ν ∧ IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b s M J x β ν hJ hβ hx ⟨mi, mv, hi, hv, hP⟩
  obtain ⟨nI, nV⟩ := nice_ainf_fv F
  obtain ⟨qloc, gloc⟩ := q_and_unitary_local_components F E σ M J
  have hβu : IsUnit β := Ne.isUnit hβ
  have bI := _root_.GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Ainf F) nI M J _ _ _ mi s.haar_nuI (hβu.map _) hi
  have bV := fun v => _root_.GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Fv F v) (nV v) M J _ _ _ (mv v) (s.haar_nuV v)
    (hβu.map _) (hv v)
  have pI := _root_.GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero F E σ hCM (Ainf F) nI M J x β _ _ mi hJ hβ hx s.haar_lamI s.haar_nuI hi
  have pV := fun v => _root_.GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero F E σ hCM (Fv F v) (nV v) M J x β _ _ (mv v) hJ hβ hx
    (s.haar_lamV v) (s.haar_nuV v) (hv v)
  obtain ⟨hfin, hne, huniq, hsupp⟩ := _root_.GlobalTheory.GaugeEx.isProd_basic F E d b 1 M ν mi mv hP
  have h1 : ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 := by
    have := hsupp {X | qR (Ainf F) σ J (X 0) = algebraMap F _ β}
      (fun v => {X | qR (Fv F v) σ J (X 0) = algebraMap F _ β})
      (measurableSet_fibre _ σ J _) (fun v => measurableSet_fibre _ σ J _) bI.1 (fun v => (bV v).1)
    refine measure_mono_null (fun X hX => ?_) this
    exact fun h => hX ((qloc (X 0) β).2 h)
  refine ⟨h1, ?_, ?_, hfin, hne pI.2.2 fun v => (pV v).2.2⟩
  · intro g
    obtain ⟨⟨gi, hgi⟩, hgv⟩ := gloc g
    have hT := _root_.GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct F E d b 1 M ν mi mv (HA.mat (AF F) σ J g) 1 hP
    have e1 : mi.map (lrAct ((HA.mat (AF F) σ J g).val.map prInf)
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map prInf)) = mi := by
      rw [← hgi, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact pI.1 gi
    have e2 : (fun v => (mv v).map (lrAct ((HA.mat (AF F) σ J g).val.map (prV v))
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map (prV v)))) = mv := by
      funext v
      obtain ⟨gv, hgv⟩ := hgv v
      rw [← hgv, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact (pV v).1 gv
    rw [e1, e2, Units.val_one, ← smul_eq_lrAct] at hT
    exact huniq _ hT
  · refine measure_mono_null (fun X hX => ?_) h1
    exact fun h => hX (GlobalTheory.T.witt_theorem_adelic_one_vector F E σ hCM M J x β hJ hβ hx X h)

end GlobalTheory.GaugeEx.StdProp
end

