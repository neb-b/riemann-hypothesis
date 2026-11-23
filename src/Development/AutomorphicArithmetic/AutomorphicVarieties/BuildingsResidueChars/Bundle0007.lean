module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsHermitianFormOfUnitaryRotationBasis
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

namespace UpperTheory.V.Z.Sym.Glob

variable {K : Type} [Field K] {Δ τ : K}

private def hh (x y : Fin 3 → Lsq K Δ) : Lsq K Δ := ∑ i, x i * star (y i)

private theorem hh_star (x y : Fin 3 → Lsq K Δ) : star (hh x y) = hh y x := by
  simp only [hh, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem hh_unitary {N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (hN : N ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ))
    (x y : Fin 3 → Lsq K Δ) : hh (N *ᵥ x) (N *ᵥ y) = hh x y := by
  change (N *ᵥ x) ⬝ᵥ star (N *ᵥ y) = x ⬝ᵥ star y
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    (Matrix.mem_unitaryGroup_iff').1 hN, Matrix.one_mulVec, dotProduct_comm]

private theorem hh_right (x y z : Fin 3 → Lsq K Δ) (r : Lsq K Δ) :
    hh x (r • y - z) = star r * hh x y - hh x z := by
  simp only [hh, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul']
  ring

private theorem hh_left (x y z : Fin 3 → Lsq K Δ) (r : Lsq K Δ) :
    hh (r • y - z) x = r * hh y x - hh z x := by
  simp only [hh, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem hh_expand (e v w : Fin 3 → Lsq K Δ) (x0 p q y0 r s : Lsq K Δ) :
    hh (x0 • e + p • v + q • w) (y0 • e + r • v + s • w) =
      x0 * star y0 * hh e e + x0 * star r * hh e v + x0 * star s * hh e w +
      p * star y0 * hh v e + p * star r * hh v v + p * star s * hh v w +
      q * star y0 * hh w e + q * star r * hh w v + q * star s * hh w w := by
  simp only [hh, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul']
  ring

private theorem trace_form (m x y : EL Δ τ) :
    QuadraticAlgebra.trace (m * x * star (sigL y)) =
      x.re * star y.re * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) +
      x.re * star y.im * (algebraMap K (Lsq K Δ) τ * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im)
        - (algebraMap K (Lsq K Δ) τ * m.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * m.im)) +
      x.im * star y.re * (algebraMap K (Lsq K Δ) τ * m.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * m.im) +
      x.im * star y.im * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) := by
  simp only [QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL]
  ring

private theorem gram_unit {M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : IsUnit M.det) :
    IsUnit (M * Mᴴ).det := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  exact h.mul (h.star)

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.exists_hermitian_form_of_unitary_rotation_basis :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K), τ ^ 2 - 4 ≠ 0 → ∀ N : Matrix (Fin 3) (Fin 3) (Lsq K Δ), N ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) →
        ∀ e v : Fin 3 → Lsq K Δ, N *ᵥ e = e → N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v →
        IsUnit (Matrix.of ![e, v, N *ᵥ v]).det →
        ∃ (c : Kˣ) (m : EL Δ τ), IsUnit m ∧ star (sigL m) = m ∧ ∀ x y : Sp Δ τ,
          herm (c : K) m x y = ∑ i, (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) i * star ((y.1 • e + y.2.re • v + y.2.im • (N *ᵥ v)) i) := by
  intro K _ _ Δ τ hτ N hN e v hNe hNv hdet
  obtain ⟨w, hw⟩ : ∃ w, w = N *ᵥ v := ⟨_, rfl⟩
  rw [← hw] at hNv hdet ⊢
  obtain ⟨t, ht⟩ : ∃ t, t = algebraMap K (Lsq K Δ) τ := ⟨_, rfl⟩
  have hst : star t = t := by
    rw [ht]; ext <;> simp
  obtain ⟨u, hu⟩ : ∃ u, u = algebraMap K (Lsq K Δ) (τ ^ 2 - 4)⁻¹ := ⟨_, rfl⟩
  have hsu : star u = u := by
    rw [hu]; ext <;> simp
  have hut : u * (t ^ 2 - 4) = 1 := by
    have : algebraMap K (Lsq K Δ) ((τ ^ 2 - 4)⁻¹ * (τ ^ 2 - 4)) = 1 := by
      rw [inv_mul_cancel₀ hτ, map_one]
    rw [map_mul, map_sub, map_pow, map_ofNat] at this
    rw [hu, ht]; exact this
  have h2t : IsUnit (2 - t) := by
    refine IsUnit.of_mul_eq_one (-(2 + t) * u) ?_
    linear_combination hut

  have hvw : hh e v = hh e w := by
    conv_lhs => rw [← hh_unitary hN e v, hNe, ← hw]
  have hew0 : hh e w = hh e (t • w - v) := by
    conv_lhs => rw [← hh_unitary hN e w, hNe, hNv, ← ht]
  rw [hh_right, hst] at hew0
  have hew : hh e w = 0 := by
    have : (2 - t) * hh e w = 0 := by linear_combination hew0 - hvw
    exact (h2t.mul_right_eq_zero).1 this
  have hev : hh e v = 0 := hvw.trans hew
  have hwe : hh w e = 0 := by rw [← hh_star, hew, star_zero]
  have hve : hh v e = 0 := by rw [← hh_star, hev, star_zero]
  have hww : hh w w = hh v v := by rw [hw, hh_unitary hN]
  have hsa : star (hh v v) = hh v v := hh_star _ _
  have hsc : star (hh e e) = hh e e := hh_star _ _
  have hb : hh w v = t * hh w w - hh v w := by
    have h := hh_unitary hN w v
    rw [← hw, hNv, ← ht, hh_left] at h
    exact h.symm

  have hG : IsUnit (hh e e * (hh v v * hh v v - hh v w * hh w v)) := by
    have h := gram_unit hdet
    have e1 : (Matrix.of ![e, v, w] * (Matrix.of ![e, v, w])ᴴ) =
        !![hh e e, hh e v, hh e w; hh v e, hh v v, hh v w; hh w e, hh w v, hh w w] := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, hh, Fin.sum_univ_three, Matrix.conjTranspose_apply]
    rw [e1, Matrix.det_fin_three] at h
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.cons_val_fin_one, hev, hew, hve, hwe, hww] at h
    convert h using 1
    ring
  have hc : IsUnit (hh e e) := isUnit_of_mul_isUnit_left hG
  have hq : IsUnit (hh v v * hh v v - hh v w * hh w v) := isUnit_of_mul_isUnit_right hG

  have him : (hh e e).im = 0 := by
    have h := congrArg QuadraticAlgebra.im hsc
    rw [QuadraticAlgebra.im_star] at h
    have h2 : (2 : K) * (hh e e).im = 0 := by linear_combination -h
    simpa using h2
  have hce : hh e e = algebraMap K (Lsq K Δ) (hh e e).re := by
    ext <;> simp [him]
  have hc0 : (hh e e).re ≠ 0 := by
    intro h0
    rw [hce, h0, map_zero] at hc
    exact not_isUnit_zero hc
  obtain ⟨a, ha⟩ : ∃ a, a = hh v v := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b, b = hh w v := ⟨_, rfl⟩
  have hvw' : hh v w = t * a - b := by
    rw [hww, ← ha, ← hb'] at hb
    linear_combination hb
  have hsb : star b = t * a - b := by
    rw [hb', hh_star, ← hb', hvw']
  have hsa' : star a = a := by rw [ha, hsa]
  obtain ⟨m, hm⟩ : ∃ m : EL Δ τ, m = ⟨u * ((t ^ 2 - 2) * a - t * b), u * (2 * b - t * a)⟩ := by
    rw [ht]; exact ⟨_, rfl⟩
  subst ht
  have hm0 : m.re = u * (((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * a - algebraMap K (Lsq K Δ) τ * b) := by rw [hm]
  have hm1 : m.im = u * (2 * b - algebraMap K (Lsq K Δ) τ * a) := by rw [hm]
  have hT0 : 2 * m.re + algebraMap K (Lsq K Δ) τ * m.im = a := by
    rw [hm0, hm1]; linear_combination a * hut
  have hT1 : algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im = b := by
    rw [hm0, hm1]; linear_combination b * hut
  have hs0 : star m.re = u * (algebraMap K (Lsq K Δ) τ * b - 2 * a) := by
    rw [hm0]
    simp only [star_mul', star_sub, star_pow, hsu, hst, hsa', hsb, star_ofNat]
    ring
  have hs1 : star m.im = u * (algebraMap K (Lsq K Δ) τ * a - 2 * b) := by
    rw [hm1]
    simp only [star_mul', star_sub, hsu, hst, hsa', hsb, star_ofNat]
    ring
  refine ⟨Units.mk0 _ hc0, m, ?_, ?_, ?_⟩
  · rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    have hn : (4 - (algebraMap K (Lsq K Δ) τ) ^ 2) * QuadraticAlgebra.norm m = a * a - (algebraMap K (Lsq K Δ) τ * a - b) * b := by
      rw [QuadraticAlgebra.norm_def, hm0, hm1]
      linear_combination (u * ((algebraMap K (Lsq K Δ) τ) ^ 2 - 4) + 1) * (a * a - (algebraMap K (Lsq K Δ) τ * a - b) * b) * hut
    rw [hvw', ← hb', ← ha] at hq
    rw [← hn] at hq
    exact isUnit_of_mul_isUnit_right hq
  · refine QuadraticAlgebra.ext ?_ ?_
    · rw [QuadraticAlgebra.re_star]
      change star m.re + algebraMap K (Lsq K Δ) τ * star m.im = m.re
      rw [hs0, hs1, hm0]
      ring
    · rw [QuadraticAlgebra.im_star]
      change -star m.im = m.im
      rw [hs1, hm1]
      ring
  · intro x y
    change herm _ m x y = hh _ _
    rw [hh_expand, herm, trace_form, hT0, hT1, hev, hew, hve, hwe, hww, hvw', ← ha, ← hb', Units.val_mk0, ← hce]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIsUnitDetMulMapStarEqOfUnitary
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

namespace UpperTheory.V.T.UnitaryGeneratorRelations

variable {K : Type} [Field K] [CharZero K] {Δ : K}

private def om (K : Type) [Field K] (Δ : K) : Lsq K Δ := ⟨0, 1⟩

private theorem star_om : star (om K Δ) = - om K Δ := by
  ext <;> simp [om]

private theorem om_om (v : Fin 3 → Lsq K Δ) : om K Δ • om K Δ • v = Δ • v := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ext <;> simp [om]

private theorem star_smulK (r : K) (z : Lsq K Δ) : star (r • z) = r • star z := by
  ext <;> simp

private def S (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) : (Fin 3 → Lsq K Δ) →ₗ[K] (Fin 3 → Lsq K Δ) where
  toFun v := B *ᵥ star v
  map_add' x y := by rw [star_add, mulVec_add]
  map_smul' r x := by
    have : star (r • x) = r • star x := by
      funext i
      exact star_smulK r (x i)
    rw [this, RingHom.id_apply, mulVec_smul]

private theorem S_apply (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v) : S B v = B *ᵥ star v := rfl

private theorem star_mulVec' (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ) :
    star (M *ᵥ v) = M.map star *ᵥ star v := by
  funext i
  simp [mulVec, dotProduct, star_sum, mul_comm]

private theorem S_S {B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : B * B.map star = 1) (v) : S B (S B v) = v := by
  rw [S_apply, S_apply, star_mulVec', star_star, mulVec_mulVec, h, one_mulVec]

private theorem S_om (B : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v) : S B (om K Δ • v) = - (om K Δ • S B v) := by
  have e : star (om K Δ • v) = -(om K Δ • star v) := by
    funext i
    simp only [Pi.star_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, star_mul', star_om]
    ring
  rw [S_apply, S_apply, e, mulVec_neg, mulVec_smul]

end UpperTheory.V.T.UnitaryGeneratorRelations

open UpperTheory.V.T.UnitaryGeneratorRelations in
theorem UpperTheory.exists_isUnit_det_mul_map_star_eq_of_unitary :
    ∀ (K : Type) [Field K] [CharZero K] (Δ : K), Δ ≠ 0 → ∀ B : Matrix (Fin 3) (Fin 3) (Lsq K Δ), B * B.map star = 1 →
        ∃ Q : Matrix (Fin 3) (Fin 3) (Lsq K Δ), IsUnit Q.det ∧ B * Q.map star = Q := by
  intro K _ _ Δ hΔ B hB
  have dec : ∀ v : Fin 3 → Lsq K Δ, ∃ w1 w2, S B w1 = w1 ∧ S B w2 = w2 ∧ v = w1 + om K Δ • w2 := by
    intro v
    refine ⟨(1/2 : K) • (v + S B v), (1/(2*Δ) : K) • om K Δ • (v - S B v), ?_, ?_, ?_⟩
    · rw [map_smul, map_add (f := _), S_S hB, add_comm]
    · rw [map_smul, S_om, map_sub, S_S hB, ← smul_neg, neg_sub]
    · rw [smul_comm (om K Δ) (1/(2*Δ) : K), om_om, smul_smul]
      have h2 : 1/(2*Δ) * Δ = (1/2 : K) := by field_simp
      rw [h2, ← smul_add]
      module
  have uniq : ∀ w1 w2 : Fin 3 → Lsq K Δ, S B w1 = w1 → S B w2 = w2 → w1 + om K Δ • w2 = 0 → w1 = 0 ∧ w2 = 0 := by
    intro w1 w2 h1 h2 h
    have hs : w1 - om K Δ • w2 = 0 := by
      have := congrArg (S B) h
      rwa [map_add, S_om, h1, h2, map_zero, ← sub_eq_add_neg] at this
    have e1 : w1 = 0 := by
      have : (2 : K) • w1 = 0 := by rw [two_smul]; linear_combination (exp := 1) h + hs
      simpa using this
    refine ⟨e1, ?_⟩
    rw [e1, zero_add] at h
    have : Δ • w2 = 0 := by rw [← om_om, h, smul_zero]
    exact (smul_eq_zero.mp this).resolve_left hΔ
  have hV : Module.finrank K (Fin 3 → Lsq K Δ) = 6 := by
    rw [Module.finrank_pi_fintype, Module.finrank_eq_card_basis (QuadraticAlgebra.basis Δ 0)]
    simp
  let W : Submodule K (Fin 3 → Lsq K Δ) := LinearMap.ker (S B - LinearMap.id)
  have memW : ∀ w, w ∈ W ↔ S B w = w := by
    intro w
    simp [W, sub_eq_zero]
  let f : (W × W) →ₗ[K] (Fin 3 → Lsq K Δ) := W.subtype.coprod (om K Δ • W.subtype)
  have fapp : ∀ p : W × W, f p = (p.1 : Fin 3 → Lsq K Δ) + om K Δ • (p.2 : Fin 3 → Lsq K Δ) := fun p => rfl
  have fbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      rw [fapp] at hp
      obtain ⟨a, b⟩ := uniq _ _ ((memW _).mp p.1.2) ((memW _).mp p.2.2) hp
      exact Prod.ext (Subtype.ext a) (Subtype.ext b)
    · intro v
      obtain ⟨w1, w2, h1, h2, rfl⟩ := dec v
      exact ⟨(⟨w1, (memW _).mpr h1⟩, ⟨w2, (memW _).mpr h2⟩), rfl⟩
  have h3 : Module.finrank K W = 3 := by
    have := (LinearEquiv.ofBijective f fbij).finrank_eq
    rw [Module.finrank_prod, hV] at this
    omega
  let bW := Module.finBasisOfFinrankEq K W h3
  have inW : ∀ j, S B (bW j : Fin 3 → Lsq K Δ) = bW j := fun j => (memW _).mp (bW j).2
  let Q : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of fun i j => (bW j : Fin 3 → Lsq K Δ) i
  have span : ∀ w (hw : w ∈ W), w = ∑ j, (bW.repr ⟨w, hw⟩ j) • (bW j : Fin 3 → Lsq K Δ) := by
    intro w hw
    have := congrArg Subtype.val (bW.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at this
    simpa using this.symm
  refine ⟨Q, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨w1, w2, h1, h2, rfl⟩ := dec v
    have s1 := span w1 ((memW _).mpr h1)
    have s2 := span w2 ((memW _).mpr h2)
    set c := bW.repr ⟨w1, (memW _).mpr h1⟩
    set d := bW.repr ⟨w2, (memW _).mpr h2⟩
    refine ⟨fun j => algebraMap K (Lsq K Δ) (c j) + om K Δ * algebraMap K (Lsq K Δ) (d j), ?_⟩
    rw [s1, s2]
    funext i
    simp only [mulVec, dotProduct, Q, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      Algebra.smul_def, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun j _ => by simp only [Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]; ring
  · refine Matrix.ext fun i j => ?_
    have := congrFun (inW j) i
    rw [S_apply] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct, Q] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearEquivSpOfIsUnitDetBasis
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem vecMul_of_three {R : Type} [CommRing R] (a b c : R) (e v w : Fin 3 → R) :
    ![a, b, c] ᵥ* (Matrix.of ![e, v, w]) = a • e + b • v + c • w := by
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem UpperTheory.exists_linearEquiv_sp_of_isUnit_det_basis :
    ∀ (K : Type) [Field K] (Δ τ : K) (e v w : Fin 3 → Lsq K Δ), IsUnit (Matrix.of ![e, v, w]).det →
        ∃ P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ), ∀ x : Sp Δ τ, P x = x.1 • e + x.2.re • v + x.2.im • w := by
  intro K _ Δ τ e v w h
  set M : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of ![e, v, w] with hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M h
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M h
  refine ⟨{ toFun := fun x => x.1 • e + x.2.re • v + x.2.im • w
            map_add' := ?_
            map_smul' := ?_
            invFun := fun y => ((y ᵥ* M⁻¹) 0, ⟨(y ᵥ* M⁻¹) 1, (y ᵥ* M⁻¹) 2⟩)
            left_inv := ?_
            right_inv := ?_ }, fun x => rfl⟩
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, add_smul]
    abel
  · intro r x
    simp [mul_smul, smul_add]
  · intro x
    have : (x.1 • e + x.2.re • v + x.2.im • w) ᵥ* M⁻¹ = ![x.1, x.2.re, x.2.im] := by
      rw [← vecMul_of_three, ← hM, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    simp only [this]
    ext <;> simp
  · intro y
    have : ((y ᵥ* M⁻¹) 0) • e + ((y ᵥ* M⁻¹) 1) • v + ((y ᵥ* M⁻¹) 2) • w = (y ᵥ* M⁻¹) ᵥ* M := by
      rw [hM, ← vecMul_of_three]
      congr 1
      funext i; fin_cases i <;> rfl
    simp only [this]
    rw [Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HermitianDatumUniqueUpToScalar
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem star_alg {K : Type} [Field K] {Δ : K} (x : K) :
    star (algebraMap K (Lsq K Δ) x) = algebraMap K (Lsq K Δ) x := by
  ext <;> simp

private theorem sigL_mul' {K : Type} [Field K] {Δ τ : K} (a b : EL Δ τ) :
    sigL (a * b) = sigL a * sigL b := by
  ext <;> simp [sigL, star_alg] <;> ring

private theorem sigL_one' {K : Type} [Field K] {Δ τ : K} : sigL (1 : EL Δ τ) = 1 := by
  apply QuadraticAlgebra.ext
  · exact star_one (Lsq K Δ)
  · exact star_zero (Lsq K Δ)

private theorem fixed_scalar {K : Type} [Field K] [CharZero K] {Δ τ : K} (r : EL Δ τ)
    (h1 : sigL r = r) (h2 : star r = r) : ∃ p : K, ∀ x : EL Δ τ, r * x = p • x := by
  have z : ∀ y : K, -y = y → y = 0 := fun y h => by
    have h' : (2 : K) * y = 0 := by linear_combination -h
    simpa using h'
  have e1 := congrArg (fun w : EL Δ τ => w.re.im) h1
  have e2 := congrArg (fun w : EL Δ τ => w.im.re) h2
  have e3 := congrArg (fun w : EL Δ τ => w.im.im) h2
  simp [sigL] at e1 e2 e3
  have hr : algebraMap K (EL Δ τ) r.re.re = r := by
    rw [show algebraMap K (EL Δ τ) r.re.re = ⟨⟨r.re.re, 0⟩, 0⟩ from rfl]
    ext <;> simp [z _ e1, z _ e2, z _ e3]
  refine ⟨r.re.re, fun x => ?_⟩
  calc r * x = algebraMap K (EL Δ τ) r.re.re * x := by rw [hr]
    _ = r.re.re • x := (Algebra.smul_def _ _).symm

theorem UpperTheory.hermitian_datum_unique_up_to_scalar :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ c c' : K) (d m m' : EL Δ τ), IsDat c d m → IsDat c' d m' → ∃ t : Kˣ, m' = (t : K) • m := by
  intro K _ _ Δ τ c c' d m m' hm hm'
  obtain ⟨u, hu⟩ := hm.m_unit
  set r : EL Δ τ := m' * ↑u⁻¹ with hrdef
  have hrm : r * m = m' := by
    rw [hrdef, ← hu, mul_assoc, Units.inv_mul, mul_one]
  have hsu : IsUnit (sigL m) := by
    refine IsUnit.of_mul_eq_one (sigL (↑u⁻¹ : EL Δ τ)) ?_
    rw [← sigL_mul', ← hu, Units.mul_inv, sigL_one']
  have hs : sigL r = r := by
    have e : sigL r * sigL m = r * sigL m := by
      rw [← sigL_mul', hrm, hm'.m_sig, hm.m_sig, ← mul_assoc, ← mul_assoc, hrm]
    exact hsu.mul_left_injective e
  have hsm : star m = sigL m := by
    conv_lhs => rw [← hm.m_star]
    exact star_star _
  have hsm' : star m' = sigL m' := by
    conv_lhs => rw [← hm'.m_star]
    exact star_star _
  have hst : star r = r := by
    have e : star r * sigL m = r * sigL m :=
      calc star r * sigL m = star r * star m := by rw [hsm]
        _ = star (r * m) := (star_mul' r m).symm
        _ = star m' := by rw [hrm]
        _ = sigL m' := hsm'
        _ = sigL r * sigL m := by rw [← sigL_mul', hrm]
        _ = r * sigL m := by rw [hs]
    exact hsu.mul_left_injective e
  obtain ⟨p, hp⟩ := fixed_scalar r hs hst
  have hm'p : m' = p • m := by rw [← hp, hrm]
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hm'p
    exact hm'.m_unit.ne_zero hm'p
  exact ⟨Units.mk0 p hp0, hm'p⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemilinearCoordsEqMulVecStar
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private lemma star_mulVec_fin_three {L : Type} [CommRing L] [StarRing L] (N : Matrix (Fin 3) (Fin 3) L) (v : Fin 3 → L) :
    star (N *ᵥ v) = N.map star *ᵥ star v := by
  funext i
  have h := RingHom.map_mulVec (starRingEnd L) N v i
  exact h

theorem UpperTheory.semilinear_coords_eq_mulVec_star :
    ∀ (K : Type) [Field K] (Δ τ : K) (d : EL Δ τ) (A N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (e v : Fin 3 → Lsq K Δ),
        A * N.map star = N * A → A *ᵥ star e = e → A *ᵥ star v = d.re • v + d.im • (N *ᵥ v) →
        N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v → ∀ x : Sp Δ τ,
        (semi d x).1 • e + (semi d x).2.re • v + (semi d x).2.im • (N *ᵥ v) = A *ᵥ star (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) := by
  intro K _ Δ τ d A N e v hAN he hv hN x
  have hNv : A *ᵥ star (N *ᵥ v) = d.re • (N *ᵥ v) + d.im • (algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v) := by
    rw [star_mulVec_fin_three, Matrix.mulVec_mulVec, hAN, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hN]
  have hs : star (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) =
      star x.1 • star e + star x.2.re • star v + star x.2.im • star (N *ᵥ v) := by
    funext i
    simp [mul_comm]
  rw [hs, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, he, hv, hNv]
  funext i
  simp only [semi, sigL, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  simp
  ring
end

