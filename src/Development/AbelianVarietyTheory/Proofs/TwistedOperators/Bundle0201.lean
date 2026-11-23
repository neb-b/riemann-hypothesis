module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixHomLatticeBoundedConjugat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitAdjBound

variable {D : D7}

theorem cA_tmul_pair (α : Af D.host.F) (m : D.host.E) :
    cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star m := rfl

theorem tmul_eq_mul (x : AF D.host.F) (m : D.host.E) :
    (x ⊗ₜ[D.host.F] m : AE D) = algebraMap (AF D.host.F) (AE D) x * incA D m := by
  change _ = (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] m)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gen_conj {v : FinPl D} (π : AE D →+* Fv D.host.F v)
    (hA : ∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y))
    (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    ((Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) :
        Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose.map π =
      (evalV D.host.F v α * π (incA D (star a))) •
        ((S.gram.map fun x => π (incA D x)) * vecMulVec (fun k => π (incA D (s k))) (fun l => π (incA D (star (t l))))) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, cA_tmul_pair]
  rw [tmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, hA, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, vecMulVec_apply, star_mul', star_sum,
    star_star, GlobalTheory.LatVac.gram_star, map_sum]
  rw [show sndA D.host.F (pairA D.host.F 0 α) = α from rfl]
  simp only [Matrix.map_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem adjCo_gen {v : FinPl D} (φ : SplitProj D v)
    (hA : ∀ y : AF D.host.F, rdA φ (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y))
    (hQ : ∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x)
    (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v))
    (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (i : Fin S.rank)
    (j : Fin T.rank) :
    adjCo φ S T BS BT (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j))
        i j =
      evalV D.host.F v α * rdQ φ (star a) * (((BS⁻¹).1 *ᵥ fun k => rdQ φ (s k)) i) *
        (((fun l => rdQ φ (star (t l))) ᵥ* (T.gram.map (rdQ φ) * BT.1)) j) := by
  set f : D.host.E →+* Fv D.host.F v := (rdA φ).comp (incA D) with hf
  have hGi : (S.gram⁻¹.map (incA D)).map (rdA φ) * S.gram.map (fun x => rdA φ (incA D x)) = 1 := by
    rw [Matrix.map_map]
    change S.gram⁻¹.map f * S.gram.map f = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  have hmid : ∀ (c : Fv D.host.F v) (V : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)),
      (S.gram⁻¹.map (incA D)).map (rdA φ) * (c • (S.gram.map (fun x => rdA φ (incA D x)) * V)) = c • V := by
    intro c V
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hT : (T.gram.map (incA D)).map (rdA φ) = T.gram.map (rdQ φ) := by
    rw [Matrix.map_map]; exact congrArg _ (funext hQ)
  unfold adjCo
  rw [Matrix.map_mul, Matrix.map_mul, gen_conj (rdA φ) hA, hmid, hT]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, hQ, Matrix.vecMul_vecMul, mul_assoc]

section Lin

variable {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
  (BT : GL (Fin T.rank) (Fv D.host.F v))

theorem adjCo_add (x y : WO S T) : adjCo φ S T BS BT (x + y) = adjCo φ S T BS BT x + adjCo φ S T BS BT y := by
  unfold adjCo
  rw [show ((x + y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) + (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) from rfl,
    Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _),
    Matrix.mul_add, Matrix.add_mul]

theorem adjCo_neg (x : WO S T) : adjCo φ S T BS BT (-x) = -adjCo φ S T BS BT x := by
  unfold adjCo
  rw [show ((-x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      -(x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) from rfl,
    Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.map_neg _ (map_neg _),
    Matrix.mul_neg, Matrix.neg_mul]

theorem adjCo_zero : adjCo φ S T BS BT 0 = 0 := by
  unfold adjCo
  rw [show ((0 : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = 0 from rfl,
    Matrix.map_zero _ (map_zero _), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _),
    Matrix.mul_zero, Matrix.zero_mul]

end Lin

theorem mul_latHat_mem {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) {y : Fin n → D.host.E} (hy : y ∈ Λ) :
    (fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] y i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β, hβ, o • y, Λ.smul_mem o hy, ?_⟩
    funext i
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => simp only [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => simp only [add_mul]; exact add_mem hx hz
  | neg x _ hx => simp only [neg_mul]; exact neg_mem hx

theorem adjCo_bound : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) → ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ∀ i j, Valued.v (adjCo φ S T (frCo φ βS) (frCo φ βT) u i j) ≤ Valued.v (rdQ φ (star a)) := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a hmax u hu
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a', ha', s, hs, t, ht, rfl⟩ := hw
    intro i j
    rw [adjCo_gen φ hπ.2.2.1 hQ]
    have h1 := (_root_.GlobalTheory.SplitFrameColumn.frame_column D S ΛS βS hS hfS v φ e he fun k => incA D (s k)).1 (by
      simp only [GlobalTheory.SplitHomLattice.finPart_mul_incA]
      exact mul_latHat_mem ΛS (GlobalTheory.SplitHomLattice.idem_int he.1) hs) i
    have h2 := (_root_.GlobalTheory.SplitRowLat.conj_mem_latHat_iff D T ΛT βT hT hfT v φ e he fun k => incA D (t k)).1 (by
      simp only [GlobalTheory.SplitHomLattice.finPart_mul_incA]
      exact mul_latHat_mem ΛT (GlobalTheory.SplitHomLattice.idem_int (GlobalTheory.SplitScalar.isSplitIdem_conj he.1)) ht) j
    simp only [hQ] at h1
    simp only [GlobalTheory.SplitDualLat.cA_incA, hQ] at h2
    have h3 := hmax a' ha'
    have h4 : Valued.v (evalV D.host.F v α) ≤ 1 := by
      have := hα v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_mul]
    calc _ ≤ 1 * Valued.v (rdQ φ (star a)) * 1 * 1 := mul_le_mul' (mul_le_mul' (mul_le_mul' h4 (hmax a' ha')) h1) h2
      _ = _ := by rw [one_mul, mul_one, mul_one]
  | zero =>
    intro i j
    rw [adjCo_zero, Matrix.zero_apply, map_zero]
    exact zero_le'
  | add x y _ _ hx hy =>
    intro i j
    rw [adjCo_add, Matrix.add_apply]
    exact Valuation.map_add_le _ (hx i j) (hy i j)
  | neg x _ hx =>
    intro i j
    rw [adjCo_neg, Matrix.neg_apply, Valuation.map_neg]
    exact hx i j

end GlobalTheory.SplitAdjBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBoundedMatrixFromHalfHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SplitHomOnto

open GlobalTheory.SplitHomLattice GlobalTheory.LatticeStable

variable {D : D7}

theorem rk_mem_latHat (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hs : s ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)))
    {t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (ht : t ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) :
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

theorem honto : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ a)) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u ∧ mapCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  intro D S T ΛS ΛT βS βT hSd hTd hfS hfT v φ e he a haA ha0 y hy
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hsi : IsSplitIdem D e := he.1
  set π : AE D →+* Fv D.host.F v := rdA φ with hπdef
  set c : Fv D.host.F v := π (incA D a) with hc
  have hc0 : c ≠ 0 := by
    intro h
    exact ha0 ((π.comp (incA D)).injective (by rw [RingHom.comp_apply, map_zero]; exact h))
  set BS : GL (Fin S.rank) (Fv D.host.F v) := frCo φ βS with hBS
  set BT : GL (Fin T.rank) (Fv D.host.F v) := frCo φ βT with hBT
  set G : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := S.gram.map (rdQ φ) with hG
  have hGπ : G = S.gram.map fun x => π (incA D x) := Matrix.ext fun i j => (hQ _).symm
  have hGu : IsUnit G.det := by
    have := (GlobalTheory.LatVac.gram_det_isUnit S).map (π.comp (incA D))
    rw [RingHom.map_det] at this
    rw [hGπ]; exact this
  choose σ hσ using hπ.1
  set Y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := c⁻¹ • y with hY
  have hYi : ∀ i j, Valued.v (Y i j) ≤ 1 := by
    intro i j
    have hy' := hy i j
    rw [← hQ] at hy'
    rw [hY, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul, map_inv₀, hc]
    exact inv_mul_le_one_of_le₀ hy' zero_le
  set X : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := BT.1 * Y with hX
  set Z : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := (BS⁻¹).1 * G⁻¹ with hZ
  have hZ1 : Z * (G * BS.1) = 1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hGu, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hs : ∀ j, (fun k => finPart D (cA D e * cA D (σ (Z j k)))) ∈
      latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) := by
    intro j
    refine (_root_.GlobalTheory.SplitRowLat.conj_mem_latHat_iff D S ΛS βS hSd hfS v φ e he fun k => cA D (σ (Z j k))).2 fun l => ?_
    have h1 : (fun i => rdA φ (cA D (cA D (σ (Z j i))))) = fun k => Z j k := by
      funext k; rw [GlobalTheory.DualPairCheck.cA_cA]; exact hσ _
    rw [h1]
    have : ((fun k => Z j k) ᵥ* (S.gram.map (rdQ φ) * (frCo φ βS).1)) l = (Z * (G * BS.1)) j l := rfl
    rw [this, hZ1, Matrix.one_apply]
    split_ifs <;> simp
  have ht : ∀ j, (fun k => finPart D (e * σ (X k j))) ∈
      latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := by
    intro j
    refine (_root_.GlobalTheory.SplitFrameColumn.frame_column D T ΛT βT hTd hfT v φ e he fun k => σ (X k j)).2 fun i => ?_
    have h1 : (fun k => rdA φ (σ (X k j))) = fun k => X k j := funext fun k => hσ _
    rw [h1]
    have : (((frCo φ βT)⁻¹ : GL (Fin T.rank) (Fv D.host.F v)).1 *ᵥ fun k => X k j) i = ((BT⁻¹).1 * X) i j := rfl
    rw [this, hX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    exact hYi i j
  set u₀ : WO S T := ∑ j, rk S T a (fun k => finPart D (cA D e * cA D (σ (Z j k))))
    (fun k => finPart D (e * σ (X k j))) with hu₀
  have hu₀m : u₀ ∈ latO S T ΛS ΛT fun _ => True :=
    sum_mem fun j _ => rk_mem_latHat S T ΛS ΛT haA (hs j) (ht j)
  refine ⟨e • u₀, smul_mem_latO D S T _ _ _ e (idem_int hsi) _ hu₀m, fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsi.1]
  · have hmap : (e • u₀).map π = c • (X * (Z * G)) := by
      refine Matrix.ext fun i l => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, pi_idem hsi hπ, one_mul, hu₀,
        Matrix.sum_apply, map_sum, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pi_rk hsi hπ S T a (fun k => cA D (σ (Z j k))) (fun k => σ (X k j)) i l]
      simp only [GlobalTheory.DualPairCheck.cA_cA, hσ]
      simp only [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hGπ, Matrix.map_apply]
      ring
    have hZG : Z * G = (BS⁻¹).1 := by rw [hZ, Matrix.nonsing_inv_mul_cancel_right _ _ hGu]
    have hXZG : c • (X * (Z * G)) = BT.1 * y * (BS⁻¹).1 := by
      rw [hZG, hX, hY, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0,
        one_smul]
    show (BT⁻¹).1 * ((e • u₀).map π) * BS.1 = y
    rw [hmap, hXZG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.SplitHomOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHomLatticeEntriesBoundedByIdealValuati
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitHomBound

variable {D : D7}

theorem mul_mem_latHat {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) {x : Fin n → D.host.E} (hx : x ∈ Λ) :
    (fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) ∈
      Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
  unfold Formalism.MainNotions.StandardLattice.latHat
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, o, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨b, hb, o • x, Λ.smul_mem o hx, ?_⟩
    funext i
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, Algebra.smul_def]
  | zero =>
    have h0 : (fun i => (0 : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) = 0 := by
      funext i; simp
    rw [h0]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ =>
    have h3 : (fun i => (w₁ + w₂) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) =
        (fun i => w₁ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) + (fun i => w₂ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) := by
      funext i; simp [add_mul]
    rw [h3]; exact add_mem h₁ h₂
  | neg w _ h =>
    have h3 : (fun i => (-w) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) =
        -(fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) := by
      funext i; simp [neg_mul]
    rw [h3]; exact neg_mem h

theorem rdA_pairA_tmul {v : FinPl D} (φ : SplitProj D v) (α : Af D.host.F) (m : D.host.E) :
    rdA φ (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = evalV D.host.F v α * rdQ φ m := by
  simp only [rdA, rdQ, GlobalTheory.AdelicU.compFin, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hev : GlobalTheory.AdelicU.evFin D.host.F v (pairA D.host.F 0 α) = evalV D.host.F v α := by
    simp only [GlobalTheory.AdelicU.evFin, pairA, sndA, ]
    rfl
  have hsm : (evalV D.host.F v α ⊗ₜ[D.host.F] m : Fv D.host.F v ⊗[D.host.F] D.host.E) =
      evalV D.host.F v α • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hev, hsm, map_smul, smul_eq_mul]

theorem mapCo_gen {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    mapCo φ S T BS BT (Matrix.of fun (i : Fin T.rank) (j : Fin S.rank) =>
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) i j =
      evalV D.host.F v α * rdQ φ a * (((BT⁻¹).1 *ᵥ fun k => rdQ φ (t k)) i) *
        (((fun k => rdQ φ (star (s k))) ᵥ* ((S.gram.map (rdQ φ)) * BS.1)) j) := by
  have hq : ∀ x y : D.host.E, rdQ φ (x * y) = rdQ φ x * rdQ φ y := by
    intro x y; simp only [← GlobalTheory.SplitProjChart.emb_apply, map_mul]
  have hqs : ∀ (f : Fin S.rank → D.host.E), rdQ φ (∑ k, f k) = ∑ k, rdQ φ (f k) := by
    intro f; simp only [← GlobalTheory.SplitProjChart.emb_apply, map_sum]
  simp only [mapCo, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, rdA_pairA_tmul, hq, hqs,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hbound : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) → ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ∀ i j, Valued.v (mapCo φ S T (frCo φ βS) (frCo φ βT) u i j) ≤ Valued.v (rdQ φ a) := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a ha u hu
  obtain ⟨hch, -, hrdinc, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hfi : ∀ x : D.host.E, finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
    intro x
    simp [finPart, incA, inclR]
  have he1 : finPart D e ∈ intAE D := by
    have h1 := (hch.2.2.2 1).2 ⟨1, by simp⟩
    simpa using h1
  have he2 : finPart D (cA D e) ∈ intAE D := by
    obtain ⟨-, -, w, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := he.1
    have hce : cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) - e := by
      rw [← hsum]; ring
    have hαint : α ∈ intAf D.host.F := by
      intro v'
      by_cases h : v' = w
      · subst h; rw [hα1]; exact one_mem _
      · rw [hα0 v' h]; exact zero_mem _
    have hfa : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
        α ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E) := by
      rw [show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]
      simp only [finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    rw [hce, map_sub, hfa]
    exact sub_mem (AddSubgroup.subset_closure ⟨α, hαint, 1, rfl⟩) he1
  have hcainc : ∀ x : D.host.E, cA D (incA D x) = incA D (star x) := by
    intro x
    rfl
  have h3 : ∀ t ∈ ΛT, ∀ i, Valued.v ((((frCo φ βT)⁻¹ : GL (Fin T.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdQ φ (t k)) i) ≤ 1 := by
    intro t ht i
    have hm : (fun k => finPart D (e * incA D (t k))) ∈
        Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := by
      simpa only [map_mul, hfi] using mul_mem_latHat ΛT he1 ht
    simpa only [hrdinc] using (_root_.GlobalTheory.SplitFrameColumn.frame_column D T ΛT βT hT hfT v φ e he (fun k => incA D (t k))).1 hm i
  have h4 : ∀ s ∈ ΛS, ∀ j, Valued.v (((fun k => rdQ φ (star (s k))) ᵥ* ((S.gram.map (rdQ φ)) * (frCo φ βS).1)) j) ≤ 1 := by
    intro s hs j
    have hm : (fun k => finPart D (cA D e * incA D (s k))) ∈
        Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) := by
      simpa only [map_mul, hfi] using mul_mem_latHat ΛS he2 hs
    simpa only [hcainc, hrdinc] using (_root_.GlobalTheory.SplitRowLat.conj_mem_latHat_iff D S ΛS βS hS hfS v φ e he (fun k => incA D (s k))).1 hm j
  unfold latO at hu
  simp only [not_true_eq_false, false_implies, implies_true, true_and] at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, c, hc, s, hs, t, ht, rfl⟩ := hw
    intro i j
    rw [mapCo_gen, Valuation.map_mul, Valuation.map_mul, Valuation.map_mul]
    have h1 : Valued.v (evalV D.host.F v α) ≤ 1 := by
      have h0 := hα v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h0
    calc _ ≤ 1 * Valued.v (rdQ φ a) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' h1 (ha c hc)) (h3 t ht i)) (h4 s hs j)
      _ = Valued.v (rdQ φ a) := by rw [one_mul, mul_one, mul_one]
  | zero =>
    intro i j
    simp [mapCo]
  | add x y _ _ hx hy =>
    intro i j
    have hxy : mapCo φ S T (frCo φ βS) (frCo φ βT) (x + y) =
        mapCo φ S T (frCo φ βS) (frCo φ βT) x + mapCo φ S T (frCo φ βS) (frCo φ βT) y := by
      simp [mapCo, Matrix.map_add (f := _), Matrix.mul_add, Matrix.add_mul]
    rw [hxy, Matrix.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (hx i j) (hy i j))
  | neg x _ hx =>
    intro i j
    have hxn : mapCo φ S T (frCo φ βS) (frCo φ βT) (-x) = -mapCo φ S T (frCo φ βS) (frCo φ βT) x := by
      simp [mapCo, Matrix.map_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [hxn, Matrix.neg_apply, Valuation.map_neg]
    exact hx i j

end GlobalTheory.SplitHomBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarStarOfInvol
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem star'_star'_of_invol {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {n : ℕ} (P : PPol σ n) (l : Fld P) : star' P (star' P l) = l := by
  have h : ((star' P : Fld P →+* Fld P).comp (star' P : Fld P →+* Fld P)) = RingHom.id (Fld P) := by
    refine AdjoinRoot.ringHom_ext (p := P.1) ?_ ?_
    · ext e
      change star' P (star' P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e
      rw [star'_algebraMap, star'_algebraMap, hσ]
    · change star' P (star' P (alpha P)) = alpha P
      rw [star'_alpha, map_inv₀, star'_alpha, inv_inv]
  exact RingHom.congr_fun h l

theorem trace_star'_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (l : Fld P), Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  intro F E _ _ _ σ hσ n P l
  let e₁ : E ≃+* E := RingEquiv.ofRingHom (σ : E →+* E) (σ : E →+* E) (RingHom.ext hσ) (RingHom.ext hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofRingHom (star' P : Fld P →+* Fld P) (star' P : Fld P →+* Fld P)
    (RingHom.ext (star'_star'_of_invol hσ P)) (RingHom.ext (star'_star'_of_invol hσ P))
  have he : RingHom.comp (algebraMap E (Fld P)) (e₁ : E →+* E) = RingHom.comp (e₂ : Fld P →+* Fld P) (algebraMap E (Fld P)) := by
    ext e
    exact (star'_algebraMap P e).symm
  have h := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he l
  change _ = σ (Algebra.trace E (Fld P) (star' P l)) at h
  rw [h, hσ]

end GlobalTheory.TrEll
end

