module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominator
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.FinSupp

theorem finDiv_finPart_mul {F : Type} [Field F] [NumberField F] {N m : ℕ} {T : AF F} (hT : GlobalTheory.FinSupp.FinDiv F N ((m : AF F) * T))
    (a : 𝓞 F) : GlobalTheory.FinSupp.FinDiv F N (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) * T) := by
  intro v
  obtain ⟨b, hb, e⟩ := hT v
  have ha : algebraMap F (Fv F v) (a : F) ∈ v.adicCompletionIntegers F := HeightOneSpectrum.coe_mem_adicCompletionIntegers v a
  refine ⟨algebraMap F (Fv F v) (a : F) * b, mul_mem ha hb, ?_⟩
  have e1 : evFin F v (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F)))) =
      evFin F v (algebraMap F (AF F) ((m : F) * (a : F))) := rfl
  rw [map_mul, e1, AlgHom.commutes, map_mul, map_natCast]
  simp only [map_mul, map_natCast] at e
  rw [mul_comm ((m : Fv F v)) _, mul_assoc, e]
  ring

theorem finPart_mul {F : Type} [Field F] [NumberField F] (x y : AF F) :
    GlobalTheory.FinSupp.finPart F x * y = GlobalTheory.FinSupp.finPart F (x * y) :=
  Prod.ext (zero_mul _) rfl

theorem exists_common_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨N, hN1, hinv⟩ := _root_.GlobalTheory.FinSuppHeis.heis_fix_finDiv F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C, k, hC⟩ := _root_.GlobalTheory.MovedLat.exists_scale F E n d (Fin n × Fin d) M.co.e N hN1
  obtain ⟨D, hD1, hD⟩ := _root_.GlobalTheory.FinSupp.DenStd.exists_den F
  refine ⟨D * C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hmT⟩ := hC g.1 h.1
  refine ⟨D * m, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC (by positivity)
  · intro ξ hξ i
    have key : ∀ a : 𝓞 F, B.ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * ((m : F) * ξ i)))) = 1 := by
      intro a
      set c : AF F := GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) with hc
      set y : Fin n × Fin d → AF F := c • Pi.single i 1 with hy
      set w' := M.co.e.symm (0, y) with hw'
      set p : UA σ X.J × UA σ W.J := (g, h) with hp
      set w := actAB (cA σ) p⁻¹ w' with hw
      have hwe : M.co.e w = c • M.co.e ((((g.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          M.co.e.symm (0, Pi.single i 1) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ) := by
        rw [hw, hw', hy, hp]
        rw [show ((0 : Fin n × Fin d → AF F), c • Pi.single i (1 : AF F)) = c • ((0 : Fin n × Fin d → AF F), Pi.single i (1 : AF F)) by simp]
        rw [LinearEquiv.map_smul, ← LinearEquiv.map_smul M.co.e]
        congr 1
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hrho : M.co.rho B.ψ w Φ = Φ := by
        unfold Darboux.rho
        apply hinv
        intro l
        rw [hwe]
        obtain ⟨h1, h2⟩ := hmT i l
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul h1 a
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul h2 a
      have himpl := S.impl p w Φ hΦ
      rw [hrho] at himpl
      have hact : actAB (cA σ) p w = w' := by
        rw [hw]
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, hp]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      have hx := congrFun himpl (fun j => algebraMap F (AF F) (ξ j))
      simp only [Darboux.rho, hw', LinearEquiv.apply_symm_apply, schr, zero_dotProduct, mul_zero, add_zero] at hx
      have h1 : B.ψ ((fun j => algebraMap F (AF F) (ξ j)) ⬝ᵥ y) = 1 := by
        have hne : om p Φ (fun j => algebraMap F (AF F) (ξ j)) ≠ 0 := hξ
        exact (mul_eq_right₀ hne).1 hx.symm
      rw [hy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hc, finPart_mul, ← map_mul] at h1
      convert h1 using 3
      ring
    have := hD B.ψ hstd _ key
    convert this using 1
    push_cast
    ring

end GlobalTheory.FinSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinates
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
noncomputable section

namespace GlobalTheory.TorusAdapted

section Coords

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n₀ r₀ d : ℕ}

def top (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A) : Matrix (Fin n₀) (Fin d) A :=
  Matrix.of fun i l => u (Sum.inl i) l

def blockCo (e₀ : Matrix (Fin n₀) (Fin d) A ≃ₗ[R] (Fin n₀ × Fin d → R) × (Fin n₀ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) :
    Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A ≃ₗ[R]
      ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → R) × ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → R) where
  toFun u := (Sum.elim (e₀ (top u)).1 (fun k => q (u (Sum.inr (Sum.inr k.1))) k.2),
    Sum.elim (e₀ (top u)).2 (fun k => p (u (Sum.inr (Sum.inl k.1))) k.2))
  invFun fg := Matrix.of fun r l => Sum.elim (fun i => e₀.symm (fg.1 ∘ Sum.inl, fg.2 ∘ Sum.inl) i l)
    (Sum.elim (fun i => p.symm (fun k => fg.2 (Sum.inr (i, k))) l) (fun i => q.symm (fun k => fg.1 (Sum.inr (i, k))) l)) r
  map_add' u u' := by
    have ht : top (u + u') = top u + top u' := rfl
    have hr : ∀ r, (u + u') r = u r + u' r := fun _ => rfl
    rw [ht]
    ext (k | k) <;> simp [hr]
  map_smul' a u := by
    have ht : top (a • u) = a • top u := rfl
    have hr : ∀ r, (a • u) r = a • u r := fun _ => rfl
    rw [ht]
    ext (k | k) <;> simp [hr]
  left_inv u := by
    ext (i | i | i) l
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_comp_inl]
      rw [show ((e₀ (top u)).1, (e₀ (top u)).2) = e₀ (top u) from rfl, LinearEquiv.symm_apply_apply]
      rfl
    · simp
    · simp
  right_inv fg := by
    rcases fg with ⟨f, g⟩
    set U : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A := Matrix.of fun r l => Sum.elim
      (fun i => e₀.symm (f ∘ Sum.inl, g ∘ Sum.inl) i l) (Sum.elim (fun i => p.symm (fun k => g (Sum.inr (i, k))) l)
        (fun i => q.symm (fun k => f (Sum.inr (i, k))) l)) r with hU
    have ht : top U = e₀.symm (f ∘ Sum.inl, g ∘ Sum.inl) := by ext i l; simp [top, hU]
    have hx : ∀ i, U (Sum.inr (Sum.inl i)) = p.symm (fun k => g (Sum.inr (i, k))) := fun i => by funext l; simp [hU]
    have hy : ∀ i, U (Sum.inr (Sum.inr i)) = q.symm (fun k => f (Sum.inr (i, k))) := fun i => by funext l; simp [hU]
    show (Sum.elim (e₀ (top U)).1 (fun k => q (U (Sum.inr (Sum.inr k.1))) k.2),
      Sum.elim (e₀ (top U)).2 (fun k => p (U (Sum.inr (Sum.inl k.1))) k.2)) = (f, g)
    simp only [ht, hx, hy, LinearEquiv.apply_symm_apply]
    ext (k | ⟨i, k⟩) <;> simp

theorem blockCo_apply (e₀ : Matrix (Fin n₀) (Fin d) A ≃ₗ[R] (Fin n₀ × Fin d → R) × (Fin n₀ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A) :
    blockCo e₀ p q u = (Sum.elim (e₀ (top u)).1 (fun k => q (u (Sum.inr (Sum.inr k.1))) k.2),
      Sum.elim (e₀ (top u)).2 (fun k => p (u (Sum.inr (Sum.inl k.1))) k.2)) := rfl

def mulLeftE {m m' : Type} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] (Q : Matrix m' m A)
    (P : Matrix m m' A) (h1 : P * Q = 1) (h2 : Q * P = 1) : Matrix m (Fin d) A ≃ₗ[R] Matrix m' (Fin d) A where
  toFun w := Q * w
  invFun z := P * z
  map_add' := Matrix.mul_add Q
  map_smul' a w := Matrix.mul_smul Q a w
  left_inv w := by
    show P * (Q * w) = w
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  right_inv z := by
    show Q * (P * z) = z
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

end Coords

theorem infScale_one (F : Type) [Field F] [NumberField F] : GlobalTheory.TorusTheta.infScale F 1 = 1 := by
  unfold GlobalTheory.TorusTheta.infScale
  rw [map_one, map_one]
  rfl

end GlobalTheory.TorusAdapted

namespace GlobalTheory.TorusAdapted

theorem adapted_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∃ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
      (blk : Fin n × Fin d → Option (Fin r₀)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ i : Fin r₀, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) ∧
      ∀ t : Fin r₀ → ℝ, (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ a' : UA σ X.J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a →
        ∀ z : Matrix (Fin n) (Fin d) (AE F E), co.e (mat a' * z) =
          (fun j => GlobalTheory.TorusTheta.infScale F (((blk j).elim 1 t)⁻¹) * (co.e z).1 j,
           fun j => GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t) * (co.e z).2 j) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWF
  have hB := hP.base
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX' : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hP.herm.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hW' : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hP.skew.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  obtain ⟨n₀, Z₀, Q, hn, hQP, hPQ, hG, hJ₀, hJ₀h, hZx, hZy⟩ := _root_.GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis F E σ hB.cm n X.J hP.herm.herm hX' r₀ Xf Yf hWF
  set P := Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) with hPdef
  obtain ⟨co₀, hco₀⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hJ₀h hP.skew.skew hJ₀ hW'
  obtain ⟨p, q, hpq, hpq', hpr, hqr⟩ := GlobalTheory.T.quadratic_extension_symplectic_coordinates σ d W.J hσ h2 hP.skew.skew hW'
  have hinc : ∀ {a b c : Type} [Fintype b] (U : Matrix a b E) (V : Matrix b c E),
      incM F (U * V) = incM F U * incM F V := fun U V => Matrix.map_mul
  have h1 : incM F P * incM F Q = 1 := by
    rw [← hinc, hPQ]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F Q * incM F P = 1 := by
    rw [← hinc, hQP]; exact Matrix.map_one _ (map_zero _) (map_one _)
  let eb := blockCo (R := AF F) (r₀ := r₀) co₀.e p q
  let mQ : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E) :=
    mulLeftE (incM F Q) (incM F P) h1 h1'
  have hcard : Fintype.card ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d))) = Fintype.card (Fin n × Fin d) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [← hn]; ring
  let ε := Fintype.equivOfCardEq hcard
  let e := mQ.trans (eb.trans (LinearEquiv.prodCongr (LinearEquiv.funCongrLeft (AF F) (AF F) ε.symm)
    (LinearEquiv.funCongrLeft (AF F) (AF F) ε.symm)))
  have he : ∀ z, e z = ((eb (incM F Q * z)).1 ∘ ε.symm, (eb (incM F Q * z)).2 ∘ ε.symm) := fun z => rfl

  have hGinc : (incM F P)ᵀ * incM F X.J * (incM F P).map (cA σ) =
      Matrix.fromBlocks (incM F (Z₀ᵀ * X.J * Z₀.map σ)) 0 0 (Matrix.fromBlocks 0 1 1 0) := by
    rw [show (incM F P)ᵀ * incM F X.J * (incM F P).map (cA σ) = incM F (Pᵀ * X.J * P.map σ) by rw [hinc, hinc]; rfl, hG]
    simp [incM, Matrix.fromBlocks_map]
  have hform₀ : ∀ x y, symp (R := AF F) (cA σ) (-1) (incM F (Z₀ᵀ * X.J * Z₀.map σ)) (incM F W.J) x y =
      (co₀.e x).1 ⬝ᵥ (co₀.e y).2 - (co₀.e y).1 ⬝ᵥ (co₀.e x).2 := co₀.form
  have hdot : ∀ f g : (Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → AF F, (f ∘ ε.symm) ⬝ᵥ (g ∘ ε.symm) = f ⬝ᵥ g :=
    fun f g => by
      simp only [dotProduct, Function.comp]
      exact Equiv.sum_comp ε.symm (fun k => f k * g k)
  have hform : ∀ w₁ w₂, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w₁ w₂ =
      (e w₁).1 ⬝ᵥ (e w₂).2 - (e w₂).1 ⬝ᵥ (e w₁).2 := by
    intro w₁ w₂
    have e1 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w₁ w₂ =
        symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F P * (incM F Q * w₁)) (incM F P * (incM F Q * w₂)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.one_mul]
    have key : ∀ i, Algebra.trace (AF F) (AE F E) (-1 * ∑ j, ∑ l, (incM F Q * w₁) (Sum.inr (Sum.inl i)) j *
          incM F W.J j l * cA σ ((incM F Q * w₂) (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace (AF F) (AE F E) (-1 * ∑ j, ∑ l, (incM F Q * w₁) (Sum.inr (Sum.inr i)) j *
          incM F W.J j l * cA σ ((incM F Q * w₂) (Sum.inr (Sum.inl i)) l)) =
        q ((incM F Q * w₁) (Sum.inr (Sum.inr i))) ⬝ᵥ p ((incM F Q * w₂) (Sum.inr (Sum.inl i))) -
          q ((incM F Q * w₂) (Sum.inr (Sum.inr i))) ⬝ᵥ p ((incM F Q * w₁) (Sum.inr (Sum.inl i))) := fun i => by
      rw [neg_one_mul, neg_one_mul, map_neg, ← hpq', ← hpq]; ring
    rw [e1, _root_.GlobalTheory.symp_mul_left, hGinc, _root_.GlobalTheory.WeilM.symp_fromBlocks_hyperbolic, hform₀, he, he, hdot, hdot, blockCo_apply, blockCo_apply]
    simp only [key, sumElim_dotProduct_sumElim, top]
    simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_sub_distrib]
    ring

  refine ⟨⟨e, hform⟩, fun j => Sum.elim (fun _ => (none : Option (Fin r₀))) (fun k => some k.1) (ε.symm j), ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y₀, z₀, h₀⟩ := hco₀ (top (Q * x))
    choose yq hyq using fun i => hqr ((Q * x) (Sum.inr (Sum.inr i)))
    choose yp hyp using fun i => hpr ((Q * x) (Sum.inr (Sum.inl i)))
    refine ⟨Sum.elim y₀ (fun k => yq k.1 k.2) ∘ ε.symm, Sum.elim z₀ (fun k => yp k.1 k.2) ∘ ε.symm, ?_⟩
    have ht : top (incM F (Q * x)) = (top (Q * x)).map (inclR (F := F) (AF F)) := rfl
    have hr : ∀ r, incM F (Q * x) r = incV F ((Q * x) r) := fun _ => rfl
    rw [he, ← hinc, blockCo_apply, ht, h₀]
    simp only [hr, hyq, hyp]
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> simp only [Function.comp_apply] <;>
      generalize ε.symm j = k' <;> rcases k' with k | ⟨i, k⟩ <;> simp
  · intro i
    rw [Finset.card_filter, ← Equiv.sum_comp ε]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
      Option.some.injEq, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp
  · intro t ht a hT a' ha' z
    have hm : mat a' = ((HA.mat (AF F) σ ((1 : E) • X.J.map σ) a : GL (Fin n) (AE F E)) :
        Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [show mat a' = ((a' : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) from rfl, ha']
    obtain ⟨hx, hy, h0⟩ := GlobalTheory.T.torus_element_acts_on_frame_columns F E σ hB.cm n ((1 : E) • X.J.map σ) r₀ Xf Yf t ht a hT
    generalize ((HA.mat (AF F) σ ((1 : E) • X.J.map σ) a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = m
      at hx hy h0 hm
    have hc : ∀ C : Matrix (Fin n) (Fin r₀) E, Formalism.UG.cT (σ : E →+* E) C * ((1 : E) • X.J.map σ) * Z₀ = 0 → ∀ c,
        (Formalism.UG.cT (σ : E →+* E) C * ((1 : E) • X.J.map σ)) *ᵥ (fun k => Z₀ k c) = 0 := fun C hC c => by
      funext i; exact congrFun (congrFun hC i) c
    have hZ : m * incM F Z₀ = incM F Z₀ := by
      ext r c
      exact congrFun (h0 (fun k => Z₀ k c) (hc Xf hZx c) (hc Yf hZy c)) r
    have hPc : incM F P = Matrix.fromCols (incM F Z₀) (Matrix.fromCols (incM F Xf) (incM F Yf)) := by
      ext r (c | c | c) <;> rfl
    set Dm : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (AE F E) := Matrix.fromBlocks 1 0 0
      (Matrix.fromBlocks (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) 0 0
        (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹))) with hDm
    have hMP : m * incM F P = incM F P * Dm := by
      rw [hPc, Matrix.mul_fromCols, Matrix.mul_fromCols, hZ, hx, hy, hDm, Matrix.fromCols_mul_fromBlocks,
        Matrix.fromCols_mul_fromBlocks]
      simp
    have hQm : incM F Q * (m * z) = Dm * (incM F Q * z) := by
      calc incM F Q * (m * z) = incM F Q * (m * (incM F P * (incM F Q * z))) := by
            rw [← Matrix.mul_assoc (incM F P), h1, Matrix.one_mul]
        _ = incM F Q * (m * incM F P) * (incM F Q * z) := by simp only [Matrix.mul_assoc]
        _ = Dm * (incM F Q * z) := by rw [hMP, ← Matrix.mul_assoc (incM F Q) (incM F P) Dm, h1', Matrix.one_mul]
    have hD1 : ∀ u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E), top (Dm * u) = top u := fun u => by
      ext i l; simp [top, hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    have hD2 : ∀ (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E)) i,
        (Dm * u) (Sum.inr (Sum.inl i)) = GlobalTheory.TorusTheta.infScale F (t i) • u (Sum.inr (Sum.inl i)) := fun u i => by
      funext l; simp [hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply, Algebra.smul_def]
    have hD3 : ∀ (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E)) i,
        (Dm * u) (Sum.inr (Sum.inr i)) = GlobalTheory.TorusTheta.infScale F (t i)⁻¹ • u (Sum.inr (Sum.inr i)) := fun u i => by
      funext l; simp [hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply, Algebra.smul_def]
    rw [hm, he, he, hQm, blockCo_apply, blockCo_apply, hD1]
    simp only [hD2, hD3, map_smul]
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> simp only [Function.comp_apply] <;>
      generalize ε.symm j = k' <;> rcases k' with k | ⟨i, k⟩ <;> simp [infScale_one]

end GlobalTheory.TorusAdapted
end
end

