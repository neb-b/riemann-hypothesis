module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0102
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlaceBoundedMatrixFromConjugateHalfHomL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfOnto

open GlobalTheory.SplitHecke GlobalTheory.SplitHomLattice Formalism.L2.NTheta GlobalTheory.LatticeStable GlobalTheory.SplitScalar

variable {D : D7}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := GlobalTheory.SplitDualLat.cA_cA z

theorem cA_algebraMap (y : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) y) = algebraMap (AF D.host.F) (AE D) y := by
  change y ⊗ₜ[D.host.F] star (1 : D.host.E) = y ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [star_one]

theorem chart_conj {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hπ : Chart e v π) : Chart (cA D e) v (π.comp (cA D)) := by
  refine ⟨fun x => ?_, fun a => ?_, fun y => ?_, fun a => ?_⟩
  · obtain ⟨z, rfl⟩ := hπ.1 x
    exact ⟨cA D z, by simp only [RingHom.comp_apply, cA_cA']⟩
  · rw [RingHom.comp_apply, hπ.2.1]
    constructor
    · intro h
      have := congrArg (cA D) h
      rwa [RingHom.map_mul, cA_cA', RingHom.map_zero] at this
    · intro h
      rw [← cA_cA' e, ← RingHom.map_mul, h, RingHom.map_zero]
  · rw [RingHom.comp_apply, cA_algebraMap, hπ.2.2.1]
  · rw [RingHom.comp_apply, ← hπ.2.2.2]
    have h1 : finPart D (cA D e * a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (e * cA D a)) := by
      rw [← GlobalTheory.SplitDualLat.finPart_cA]; congr 1; rw [map_mul, cA_cA']
    have h2 : finPart D (e * cA D a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (cA D e * a)) := by
      rw [← GlobalTheory.SplitDualLat.finPart_cA]; congr 1; rw [map_mul, cA_cA']
    constructor
    · intro h; rw [h2]; exact GlobalTheory.SplitDualLat.sigR_mem_intAE h
    · intro h; rw [h1]; exact GlobalTheory.SplitDualLat.sigR_mem_intAE h

theorem rk_mem_lat (S T : HSp D) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hs : s ∈ latHat D.host.F D.host.E ΛS)
    {t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E} (ht : t ∈ latHat D.host.F D.host.E ΛT) :
    rk S T a s t ∈ latO S T ΛS ΛT fun _ => True := by
  change rkHom S T a s t ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun _ h => absurd trivial h, a, ha, x, hx, y, hy, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · ext i j
        change liftFin D (_ * _ * ∑ k, (α ⊗ₜ[D.host.F] star (x k)) * _) = _
        rw [Matrix.of_apply, ← liftFin_tmul]
        congr 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [← TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem conj_rk {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (he : IsSplitIdem D e) (hπ : Chart e v π) (S T : HSp D) (a : D.host.E) (s : Fin S.rank → AE D)
    (t : Fin T.rank → AE D) (p : Fin T.rank) (q : Fin S.rank) :
    π (cA D (rk S T a (fun k => finPart D (e * s k)) (fun k => finPart D (cA D e * t k)) p q)) =
      π (cA D (incA D a)) * π (cA D (t p)) * ∑ k, π (s k) * π (cA D (incA D (S.gram k q))) := by
  have h := pi_rk (isSplitIdem_conj he) (chart_conj hπ) S T a s t p q
  simp only [RingHom.comp_apply, cA_cA'] at h
  exact h

theorem frame_cancel {K : Type} [Field K] {m n : ℕ} (B : GL (Fin m) K) (C : GL (Fin n) K) {c : K} (hc : c ≠ 0)
    (y : Matrix (Fin m) (Fin n) K) : (B⁻¹).1 * (c • (B.1 * ((c⁻¹ • y) * (C⁻¹).1))) * C.1 = y := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
    Units.inv_mul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem map_cA_sum_apply {K : Type} [CommRing K] (π : AE D →+* K) {S T : HSp D} {n : ℕ} (M : Fin n → WO S T)
    (p : Fin T.rank) (q : Fin S.rank) :
    π (cA D ((∑ l, M l : Matrix (Fin T.rank) (Fin S.rank) (AE D)) p q)) = ∑ l, π (cA D (M l p q)) := by
  rw [Matrix.sum_apply, GlobalTheory.SplitDualLat.ringHom_sum (cA D), GlobalTheory.SplitDualLat.ringHom_sum π]

theorem adjCo_eq_map {v : FinPl D} (φ : SplitProj D v) (hQ : ∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x)
    (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (u : WO S T) :
    adjCo φ S T BS BT u = (BS⁻¹).1 * ((S.gram⁻¹).map (rdQ φ) *
      ((u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map fun x => rdA φ (cA D x))ᵀ * T.gram.map (rdQ φ)) * BT.1 := by
  unfold adjCo
  congr 2
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  simp only [Function.comp_def, hQ]

end GlobalTheory.ConjHalfOnto

namespace GlobalTheory.ConjHalfOnto

open GlobalTheory.SplitHecke GlobalTheory.SplitHomLattice Formalism.L2.NTheta GlobalTheory.LatticeStable GlobalTheory.SplitScalar


set_option maxHeartbeats 1000000 in
theorem conj_half_onto : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ (star a))) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf (cA D e) u ∧ adjCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a haA ha0 y hy
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hsi : IsSplitIdem D e := he.1
  have hsc : IsSplitIdem D (cA D e) := isSplitIdem_conj hsi
  have hπc := chart_conj hπ
  have hc0 : rdQ φ (star a) ≠ 0 := by
    rw [← hQ]
    intro h
    have h1 : ((rdA φ).comp (incA D)) (star a) = 0 := h
    exact ha0 (star_eq_zero.1 ((map_eq_zero_iff _ ((rdA φ).comp (incA D)).injective).1 h1))
  set c : Fv D.host.F v := rdQ φ (star a) with hcdef
  set BS := frCo φ βS with hBS
  set BT := frCo φ βT with hBT
  have hGmap : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), M.map (rdQ φ) = M.map ((rdA φ).comp (incA D)) := by
    intro m n M; ext i j; simp only [Matrix.map_apply, RingHom.comp_apply, hQ]
  set Gs : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := S.gram.map (rdQ φ) with hGs
  set Gt : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v) := T.gram.map (rdQ φ) with hGt
  have hGtu : IsUnit Gt.det := by
    have := (GlobalTheory.LatVac.gram_det_isUnit T).map ((rdA φ).comp (incA D))
    rw [RingHom.map_det] at this
    rw [hGt, hGmap]
    exact this
  have hGsi : (S.gram⁻¹).map (rdQ φ) * Gs = 1 := by
    rw [hGs, hGmap, hGmap, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  set Z : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v) := (BT⁻¹).1 * Gt⁻¹ with hZ
  have hZ1 : Z * (Gt * BT.1) = 1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hGtu, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hZG : Z * Gt = (BT⁻¹).1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGtu, Matrix.mul_one]
  set Y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) := c⁻¹ • y with hY
  have hYint : ∀ l m, Valued.v (Y l m) ≤ 1 := by
    intro l m
    rw [hY, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul, map_inv₀,
      inv_mul_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc0))]
    exact hy l m
  choose σ hσ using hπ.1
  clear_value Y Z Gt Gs BT BS c
  obtain ⟨s', hs'⟩ : ∃ s' : Fin S.rank → Fin S.rank → AE D, ∀ l k, s' l k = σ (BS.1 k l) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : Fin S.rank → Fin T.rank → AE D, ∀ l k, t' l k = cA D (σ (((fun m => Y l m) ᵥ* Z) k)) :=
    ⟨_, fun _ _ => rfl⟩
  have hs : ∀ l, (fun k => finPart D (e * s' l k)) ∈ latHat D.host.F D.host.E (ΛS : Set _) := by
    intro l
    refine (_root_.GlobalTheory.SplitFrameColumn.frame_column D S ΛS βS hS hfS v φ e he (s' l)).2 fun i => ?_
    have h1 : (fun k => rdA φ (s' l k)) = BS.1 *ᵥ Pi.single l 1 := by
      funext k
      rw [hs', hσ, Matrix.mulVec_single_one]
      rfl
    rw [← hBS, h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hi : i = l
    · subst hi; rw [Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne hi, map_zero]; exact zero_le_one
  have ht : ∀ l, (fun k => finPart D (cA D e * t' l k)) ∈ latHat D.host.F D.host.E (ΛT : Set _) := by
    intro l
    refine (_root_.GlobalTheory.SplitRowLat.conj_mem_latHat_iff D T ΛT βT hT hfT v φ e he (t' l)).2 fun j => ?_
    have h1 : (fun k => rdA φ (cA D (t' l k))) = (fun m => Y l m) ᵥ* Z := by
      funext k
      rw [ht', cA_cA', hσ]
    rw [← hGt, ← hBT, h1, Matrix.vecMul_vecMul, hZ1, Matrix.vecMul_one]
    exact hYint l j
  obtain ⟨U, hU⟩ : ∃ U : WO S T,
      U = ∑ l, rk S T a (fun k => finPart D (e * s' l k)) (fun k => finPart D (cA D e * t' l k)) := ⟨_, rfl⟩
  have hUmem : U ∈ latO S T ΛS ΛT fun _ => True := by
    rw [hU]; exact sum_mem fun l _ => rk_mem_lat S T _ _ haA (hs l) (ht l)
  refine ⟨cA D e • U, smul_mem_latO D S T _ _ _ (cA D e) (idem_int hsc) _ hUmem, fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsc.1]
  · have hentry : ∀ p q, rdA φ (cA D ((cA D e • U) p q)) =
        c * ∑ l, (Y * Z) l p * ∑ k, BS.1 k l * Gs q k := by
      intro p q
      have h0 : (cA D e • U) p q = cA D e * U p q := rfl
      rw [h0, map_mul (cA D), cA_cA', map_mul (rdA φ), he.2.2, one_mul, hU, map_cA_sum_apply]
      refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) (Finset.mul_sum _ _ _).symm
      rw [conj_rk hsi hπ S T a (s' l) (t' l) p q]
      have hYZ : ((fun m => Y l m) ᵥ* Z) p = (Y * Z) l p := rfl
      have hk : ∀ k, rdA φ (s' l k) * rdA φ (cA D (incA D (S.gram k q))) = BS.1 k l * Gs q k := by
        intro k
        rw [hs', hσ, GlobalTheory.SplitDualLat.cA_incA, hQ, GlobalTheory.LatVac.gram_star, hGs, Matrix.map_apply]
      rw [GlobalTheory.SplitDualLat.cA_incA, hQ, ← hcdef, ht', cA_cA', hσ, hYZ, Finset.sum_congr rfl fun k _ => hk k, mul_assoc]
    have hT' : (((cA D e • U : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map fun x => rdA φ (cA D x))ᵀ =
        c • (Gs * (BS.1 * (Y * Z))) := by
      ext q p
      rw [Matrix.transpose_apply, Matrix.map_apply, hentry, Matrix.smul_apply, smul_eq_mul]
      congr 1
      generalize Y * Z = W
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have key : (S.gram⁻¹).map (rdQ φ) * (c • (Gs * (BS.1 * (Y * Z)))) * Gt = c • (BS.1 * (Y * (BT⁻¹).1)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc _ Gs, hGsi, Matrix.one_mul, Matrix.mul_assoc BS.1,
        Matrix.mul_assoc Y, hZG]
    rw [adjCo_eq_map φ hQ, hT', ← hGt, key, hY]
    exact frame_cancel BS BT hc0 y

end GlobalTheory.ConjHalfOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantPairingUniqueUpToScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairingLine

open GlobalTheory.PairingTensor

theorem exists_tensor {V A B H₁ H₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂) (h₁ : Function.Injective i₁)
    (h₂ : Function.Injective i₂) (φ : B → V →ₗ[ℂ] A)
    (hadj : ∀ P x, ∃ b, ∀ y, ⟪i₁ x, i₁ (φ y P)⟫_ℂ = ⟪i₂ y, i₂ b⟫_ℂ)
    (hE : ∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) :
    ∃ f : V →ₗ[ℂ] A ⊗[ℂ] B, (∀ P y, contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) (f P) = φ y P) ∧
      ∀ z w : A ⊗[ℂ] B,
        (∀ y, contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) z = contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) w) → z = w := by
  let m : B → B →ₗ[ℂ] ℂ := fun y => (innerₛₗ ℂ (i₂ y)) ∘ₗ i₂
  have hm : ∀ y b, m y b = inner ℂ (i₂ y) (i₂ b) := fun _ _ => rfl
  have sepm : ∀ b, (∀ y, m y b = 0) → b = 0 := fun b h => by
    apply h₂
    rw [map_zero]
    exact inner_self_eq_zero.mp (h b)
  have sepR : ∀ z w : A ⊗[ℂ] B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w := by
    intro z w h
    rw [← sub_eq_zero]
    exact eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])
  choose ψ hψ using hadj
  have ex : ∀ P, ∃ z : A ⊗[ℂ] B, ∀ y, contrR (m y) z = φ y P := by
    intro P
    obtain ⟨E, hfin, hmem⟩ := hE P
    let e := stdOrthonormalBasis ℂ (E.map i₁)
    have ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁) := fun j => by
      obtain ⟨a, -, ha⟩ := (e j).2
      exact ⟨a, ha⟩
    choose a ha using ha
    refine ⟨∑ j, a j ⊗ₜ[ℂ] ψ P (a j), fun y => ?_⟩
    apply h₁
    have := congrArg (fun v : E.map i₁ => (v : H₁))
      (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [contrR_tmul, map_smul, hm, ← hψ, ha]
  choose g hg using ex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sepR _ _ fun y => by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]
           map_smul' := fun s P => sepR _ _ fun y => by
             rw [map_smul, hg, hg, map_smul, RingHom.id_apply] }, hg, sepR⟩

theorem contrR_map_right {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (m : B →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : A ⊗[ℂ] B) :
    contrR m (TensorProduct.map LinearMap.id b z) = contrR (m ∘ₗ b) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem contrR_neg {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (m : B →ₗ[ℂ] ℂ) (z : A ⊗[ℂ] B) : contrR (-m) z = -contrR m z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]

theorem linear_eq_of_upq {p q : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (F G : Mat p q →ₗ[ℂ] N)
    (h : ∀ Z ∈ upq p q, F Z = G Z) (Z : Mat p q) : F Z = G Z := by
  have e1 := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have e2 := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hd := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = X at e1 hd
  generalize Complex.I • (Z - conjR Z) = Y at e2 hd
  subst hd
  simp only [map_add (f := _), map_smul, e1, e2]

theorem skew {p q : ℕ} {T : GrpData p q} (R : DSRep T) {Y : Mat p q} (hY : Y ∈ upq p q) (x y : R.HK.V) :
    ⟪R.ι (R.HK.act Y x), R.ι y⟫_ℂ = -⟪R.ι x, R.ι (R.HK.act Y y)⟫_ℂ := by
  have h1 := (R.der Y hY x).inner ℂ (R.der Y hY y)
  simp only [GlobalTheory.RealPar.DerivedAdjoint.inner_map, zero_smul, T.expt_zero, map_one,
    ContinuousLinearMap.one_apply] at h1
  have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (R.ι x) (R.ι y)))
  linear_combination h2

theorem exists_intw {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (hA : Formalism.MainNotions.SchurIrreducible.AdmGK R₁.HK) (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V)
    (hB : CoverW R₁ R₂ B) :
    ∃ f : Pol p q r s →ₗ[ℂ] R₁.HK.V ⊗[ℂ] R₂.HK.V,
      (∀ Z, f ∘ₗ fockAct1 p q r s Z = TensorProduct.map (R₁.HK.act Z) LinearMap.id ∘ₗ f) ∧
      (∀ Z, f ∘ₗ fockAct2 p q r s Z = TensorProduct.map LinearMap.id (R₂.HK.act Z) ∘ₗ f) ∧
      ∀ P y, contrR (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) (f P) = B P y := by
  have hsrc : ∀ Z P y, B (fockAct1 p q r s Z P) y = R₁.HK.act Z (B P y) := fun Z P y =>
    linear_eq_of_upq (B.flip y ∘ₗ (fockAct1 p q r s).flip P) (R₁.HK.act.flip (B P y))
      (fun Z hZ => hB.src Z hZ P y) Z
  have hlie := (_root_.GlobalTheory.FockAlg.fock_lie_and_commute p q r s).2.1
  obtain ⟨f, hf, sep⟩ := exists_tensor R₁.ι R₂.ι R₁.ι_inj R₂.ι_inj (fun y => B.flip y) hB.adj (fun P => by
    obtain ⟨W, hW, hP, hst⟩ := ((_root_.GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1
    obtain ⟨E, hE, hE'⟩ := _root_.GlobalTheory.KHomFinite.exists_finiteDimensional_forall_map_mem p q R₁.HK hA _ (fockAct1 p q r s) (fun Y Z _ _ => hlie Y Z) W hW hst
      (fun v _ => ((_root_.GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 v).2)
    exact ⟨E, hE, fun y => hE' (B.flip y) (fun Z _ v => hsrc Z v y) P hP⟩)
  simp only [LinearMap.flip_apply] at hf
  refine ⟨f, fun Z => ?_, fun Z => ?_, hf⟩
  · refine LinearMap.ext fun P => sep _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, hsrc]
  · refine LinearMap.ext fun P => ?_
    refine linear_eq_of_upq (f ∘ₗ (fockAct2 p q r s).flip P)
      (((LinearMap.lTensorHom R₁.HK.V).comp R₂.HK.act).flip (f P)) (fun Z hZ => ?_) Z
    refine sep _ _ fun y => ?_
    change contrR _ (f (fockAct2 p q r s Z P)) = contrR _ (TensorProduct.map LinearMap.id (R₂.HK.act Z) (f P))
    have e : (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) ∘ₗ R₂.HK.act Z = -(innerₛₗ ℂ (R₂.ι (R₂.HK.act Z y)) ∘ₗ R₂.ι) := by
      refine LinearMap.ext fun b => ?_
      change ⟪R₂.ι y, R₂.ι (R₂.HK.act Z b)⟫_ℂ = -⟪R₂.ι (R₂.HK.act Z y), R₂.ι b⟫_ℂ
      rw [skew R₂ hZ, neg_neg]
    rw [contrR_map_right, e, contrR_neg, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB.tgt Z hZ P y)

theorem pairing_line : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds p q lam).HK → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → ∃ B₀ : Pol p q r s → (X.ds r s lam').HK.V → (X.ds p q lam).HK.V, ∀ B : Pol p q r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] (X.ds p q lam).HK.V, CoverW (X.ds p q lam) (X.ds r s lam') B → ∃ c : ℂ, ∀ P y, B P y = c • B₀ P y := by
  intro X p q r s lam lam' hA hL
  obtain ⟨f₀, -, -, hf₀⟩ := hL
  refine ⟨fun P y => contrR (innerₛₗ ℂ ((X.ds r s lam').ι y) ∘ₗ (X.ds r s lam').ι) (f₀ P), fun B hB => ?_⟩
  obtain ⟨f, h1, h2, hf⟩ := exists_intw _ _ hA B hB
  obtain ⟨c, hc⟩ := hf₀ f ⟨h1, h2⟩
  refine ⟨c, fun P y => ?_⟩
  rw [← hf, hc, LinearMap.smul_apply, map_smul]

end GlobalTheory.PairingLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverHaarPushforwardSignatureUnitaryGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec

theorem haar_of_proper {p q n : ℕ} (T : GrpData p q) (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε))
    [μ.IsHaarMeasure] (π : T.G →* Formalism.REAL.UJ ε) (hp : IsProperMap π) (hs : Function.Surjective π) :
    ∃ c : NNReal, c ≠ 0 ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  have hc : Continuous π := hp.continuous
  have ht : Filter.Tendsto π (Filter.cocompact T.G) (Filter.cocompact (Formalism.REAL.UJ ε)) := by
    refine Filter.hasBasis_cocompact.tendsto_right_iff.2 fun K hK => ?_
    have hK' : IsCompact (π ⁻¹' K) := hp.isCompact_preimage hK
    exact hK'.compl_mem_cocompact
  haveI hν : (Measure.map π T.haar).IsHaarMeasure := Measure.isHaarMeasure_map T.haar π hc hs ht
  refine ⟨Measure.haarScalarFactor (Measure.map π T.haar) μ,
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', hp.isClosedMap.isQuotientMap hc hs,
    hc.measurable, ?_⟩
  exact Measure.isMulLeftInvariant_eq_smul _ μ


open GlobalTheory.RealPar.SqInt (reixHom continuous_reixHom) in
noncomputable def reixUJ {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Formalism.UG.Upq p q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨Units.map (reixHom e) g.1, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat_mem h g.2⟩
  invFun g := ⟨Units.map (reixHom e.symm) g.1, by
    have hg : (umat g)ᴴ * Formalism.REAL.Jm ε * umat g = Formalism.REAL.Jm ε := g.2
    change (Matrix.reindex e.symm e.symm (umat g))ᴴ * Formalism.UG.Jpq p q * Matrix.reindex e.symm e.symm (umat g) =
      Formalism.UG.Jpq p q
    have hJ : Formalism.UG.Jpq p q = Matrix.reindex e.symm e.symm (Formalism.REAL.Jm ε) := by
      rw [← GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.reindex_form h]; simp
    rw [hJ]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]⟩
  left_inv g := Subtype.ext (Units.ext (by
    change Matrix.reindex e.symm e.symm (Matrix.reindex e e _) = _
    simp))
  right_inv g := Subtype.ext (Units.ext (by
    change Matrix.reindex e e (Matrix.reindex e.symm e.symm _) = _
    simp))
  map_mul' a b := Subtype.ext (map_mul (Units.map (reixHom e)) a.1 b.1)
  continuous_toFun := Continuous.subtype_mk (((continuous_reixHom e).units_map _).comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (((continuous_reixHom e.symm).units_map _).comp continuous_subtype_val) _

theorem cover_haar_map : ∀ (p q n : ℕ) (T : GrpData p q) (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) (br : Bool) (μ : Measure (Formalism.REAL.UJ ε)), SignCompat ε e → μ.IsHaarMeasure → ∃ (π : T.G →* Formalism.REAL.UJ ε) (c : NNReal), c ≠ 0 ∧ (∀ g, umat (π g) = phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  intro p q n T ε e br μ h hμ
  obtain ⟨C, hC, -⟩ := GlobalTheory.LeviIso.exists_conj_gauge_invariant n ε
    (if br then starRingEnd ℂ else RingHom.id ℂ) (by cases br <;> simp)
  let π : T.G →* Formalism.REAL.UJ ε :=
    (C.toMonoidHom.comp (reixUJ h).toMonoidHom).comp (GlobalTheory.DetSqrtCover.covHom T)
  have hcov : IsProperMap (GlobalTheory.DetSqrtCover.covHom T) := GlobalTheory.DetSqrtCover.isProperMap_covU T
  have hp : IsProperMap π :=
    (C.toHomeomorph.isProperMap.comp (reixUJ h).toHomeomorph.isProperMap).comp hcov
  have hs : Function.Surjective π :=
    (C.surjective.comp (reixUJ h).surjective).comp (GlobalTheory.DetSqrtCover.surjective_covU T)
  obtain ⟨c, hc0, hq, hm, hmap⟩ := haar_of_proper T ε μ π hp hs
  refine ⟨π, c, hc0, fun g => ?_, hq, hm, hmap⟩
  have hre : umat (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g)) =
      Matrix.reindex e e ((T.cov g : GL (Ix p q) ℂ) : Mat p q) :=
    GlobalTheory.RealPar.SqInt.reixHom_apply e _
  have hconj := hC (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))
  change umat (C (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))) = _
  refine hconj.trans ?_
  change (umat (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))).map _ = _
  rw [hre]
  cases br
  · ext i j
    simp [phi, plainMat]
  · ext i j
    simp [phi, barMat]

end GlobalTheory.ArchRec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugatePlaceCmField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlace

theorem conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (P : Ideal (𝓞 E)) :
    GlobalTheory.SW.conjI P = P.map (IsCMField.ringOfIntegersComplexConj E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map, Set.image]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [IsCMField.coe_ringOfIntegersComplexConj]; rfl⟩

theorem exists_conj_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E), ∃ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.asIdeal = conjI PP.asIdeal ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D PP
  let σ := IsCMField.ringOfIntegersComplexConj D.host.E
  haveI : (PP.asIdeal.map σ).IsPrime := Ideal.map_isPrime_of_equiv σ
  have hne : PP.asIdeal.map σ ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective σ.injective]
    exact PP.ne_bot
  refine ⟨⟨PP.asIdeal.map σ, this, hne⟩, (conjI_eq_map PP.asIdeal).symm, ?_⟩
  intro c hc
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_of_equiv σ c).1 hc
  refine ⟨b, hb, ?_⟩
  show ((b : 𝓞 D.host.E) : D.host.E) = star (((σ b : 𝓞 D.host.E)) : D.host.E)
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact (IsCMField.complexConj_apply_apply D.host.E _).symm

end GlobalTheory.ConjPlace
end

