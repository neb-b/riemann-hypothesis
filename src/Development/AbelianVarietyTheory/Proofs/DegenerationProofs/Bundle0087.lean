module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValUnitNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormConstSec
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

theorem norm_const_gen : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (nH : H ⟶ H) (nK : HK ⟶ HK) (nX : X ⟶ X), nK ≫ j = j ≫ nH → nK ≫ ψ = ψ ≫ nX → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1])), α.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l l' : M.ι) (m : Fin 2 → L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (c ≫ nH) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) → ⊤ ≤ (x ≫ ψ ≫ nX) ⁻¹ᵁ L.U (m 1) → ‖valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x l (m 0) ^ n ^ 2 * (ω (x ≫ nK) l' (m 1))⁻¹‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω nH nK nX hnj hnψ n α hα
  have ej : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ j = (x ≫ j) ≫ nH := fun x => by
    rw [Category.assoc, hnj, Category.assoc]
  have eψ : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ ψ = (x ≫ ψ) ≫ nX := fun x => by
    rw [Category.assoc, hnψ, Category.assoc]
  have w₀ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ L.U (m 0) := fun m => LB.wchart_le L ![𝟙 X, nX] m 0
  have w₁ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ nX ⁻¹ᵁ L.U (m 1) := fun m => LB.wchart_le L ![𝟙 X, nX] m 1
  have l₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {a : M.ι × M.ι}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) →
      ⊤ ≤ ((x ≫ nK) ≫ j) ⁻¹ᵁ M.U a.2 := fun h => by
    rw [ej]
    exact fun _ hz => (h hz).2
  have m₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {m}, ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m →
      ⊤ ≤ ((x ≫ nK) ≫ ψ) ⁻¹ᵁ L.U (m 1) := fun h => by
    rw [eψ]
    exact fun _ hz => w₁ _ (h hz)
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (M.ι × M.ι) (Fin 2 → L.ι)
    (fun a => M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) (fun m => ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m)
    (fun a m x => valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x a.1 (m 0) ^ n ^ 2 *
      (ω (x ≫ nK) a.2 (m 1))⁻¹)
    (fun z => exists_chart (LB.isLB_linComb hL ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1]) (ψ z))
    (fun a m => ((Reg.pull ψ inf_le_right _).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) ⊓ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m) a.1 (m 0)
        (fun _ hz => hz.1.1) fun _ hz => w₀ _ hz.2).1).pow _)).mul
      (hω.reg nK _ a.2 (m 1) (by rw [hnj]; exact fun _ hz => hz.1.2) (by rw [hnψ]; exact fun _ hz => w₁ _ hz.2)).2)
    (fun a m x _ ha hm => mul_ne_zero (mul_ne_zero (val_unit_ne_zero (x ≫ ψ) (U := LB.wchart L ![𝟙 X, nX] m) hm _)
      (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => (ha hz).1) fun _ hz => w₀ _ (hm hz))))
      (inv_ne_zero (hω.ne _ _ _ (l₁ ha) (m₁ hm))))
    (fun a m m' x _ ha hm hm' => by
      have hm₀ : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) := fun _ hz => w₀ _ (hm hz)
      have hm₀' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m' 0) := fun _ hz => w₀ _ (hm' hz)
      have e := (gen_val hα (x := x ≫ ψ) hm hm').trans (congrArg (· * _) (tv_linComb L _ _
        (fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m k (hm hz)) fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m' k (hm' hz)))
      rw [Fin.prod_univ_two] at e
      change valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val =
        tv L ((x ≫ ψ) ≫ 𝟙 X) (m 0) (m' 0) ^ ((n : ℤ) ^ 2) * tv L ((x ≫ ψ) ≫ nX) (m 1) (m' 1) ^ (-1 : ℤ) *
        valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m') (α.s m').val at e
      rw [Category.comp_id, ← eψ, zpow_neg_one,
        show ∀ z : PadicAlgCl p, z ^ ((n : ℤ) ^ 2) = z ^ n ^ 2 from fun z => by rw [← zpow_natCast, Nat.cast_pow]] at e
      beta_reduce
      rw [e, ← hω.right x a.1 (m 0) (m' 0) (fun _ hz => (ha hz).1) hm₀ hm₀',
        ← hω.right (x ≫ nK) a.2 (m 1) (m' 1) (l₁ ha) (m₁ hm) (m₁ hm'), mul_pow, mul_inv]
      ring)
    (fun a a' => by
      have e₁ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ M.U a.1 ⊓ M.U a'.1 :=
        inf_le_inf inf_le_left inf_le_left
      have e₂ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ nH ⁻¹ᵁ (M.U a.2 ⊓ M.U a'.2) :=
        fun _ hz => ⟨hz.1.2, hz.2.2⟩
      refine ⟨res e₁ (M.g a.1 a'.1) ^ ((n ^ 2 : ℕ) : ℤ) * res e₂ (pullU nH _ (M.g a.2 a'.2)) ^ (-1 : ℤ),
        fun m x _ ha ha' hm => ?_⟩
      have hh : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2)) :=
        fun _ hz => ⟨ha hz, ha' hz⟩
      have v₁ : valR (x ≫ j) _ (res e₁ (M.g a.1 a'.1)).val = tv M (x ≫ j) a.1 a'.1 := valR_res _ e₁ hh _
      have v₂ : valR (x ≫ j) _ (res e₂ (pullU nH _ (M.g a.2 a'.2))).val = tv M ((x ≫ nK) ≫ j) a.2 a'.2 := by
        rw [ej]
        exact val_res_pull _ nH e₂ hh _
      beta_reduce
      rw [Units.val_mul, valR_mul _ _ hh, val_zpow _ hh, val_zpow _ hh, v₁, v₂, zpow_natCast, zpow_neg_one,
        hω.left x a.1 a'.1 (m 0) (fun _ hz => (ha hz).1) (fun _ hz => (ha' hz).1) fun _ hz => w₀ _ (hm hz),
        hω.left (x ≫ nK) a.2 a'.2 (m 1) (l₁ ha) (l₁ ha') (m₁ hm), mul_pow, mul_inv]
      ring)
  refine ⟨κ, hκ, fun c x l l' m hc hx hq hl hl' hm hm' => h (l, l') m c x hc hx hq (fun _ hz => ⟨hl hz, hl' hz⟩)
    fun _ hz => Set.mem_iInter.2 fun k => ?_⟩
  fin_cases k
  · exact hm hz
  · exact hm' hz

theorem norm_const_sec : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (Y : Scheme.{0}) (π : Y ⟶ X) (ψ' : HK ⟶ Y), ψ' ≫ π = ψ → ∀ (N : ℕ) (J : Type) [Fintype J] (s : J → (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (N : ℤ))).Sec) (t : J → (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 H) (fun _ => (N : ℤ))).Sec) (b : Matrix J J K), (∀ (x : Sp (PadicAlgCl p) ⟶ HK) v, x ≫ q = spMap σ → Crd _ s (x ≫ ψ') v → Crd _ t (x ≫ j) ((b.map σ).mulVec v)) → (∀ (c : Sp (OO p) ⟶ H) w, c ≫ f = spMap jV → Crd _ t c w → ∃ i, IsUnit (w i)) → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l : M.ι) (m : L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → IsGreatest (Set.range fun i => ‖(b.map σ).mulVec (fun i => valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) (fun _ => m)) ((s i).f fun _ => m)) i * ω x l m ^ N‖) κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω Y π ψ' hψ N J _ s t b hlink hprim
  subst hψ
  let v : (Sp (PadicAlgCl p) ⟶ HK) → L.ι → J → PadicAlgCl p := fun x m i =>
    valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) fun _ => m) ((s i).f fun _ => m)
  let w : (Sp (PadicAlgCl p) ⟶ H) → M.ι → J → PadicAlgCl p := fun x l i =>
    valR x (LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l) ((t i).f fun _ => l)
  have wl : ∀ l i, H.basicOpen ((t i).f fun _ => l) ≤ M.U l := fun l i =>
    (H.basicOpen_le _).trans (LB.wchart_le M (fun _ : Fin 1 => 𝟙 H) (fun _ => l) 0)
  have wne : ∀ {x : Sp (PadicAlgCl p) ⟶ H} {l i}, ⊤ ≤ x ⁻¹ᵁ H.basicOpen ((t i).f fun _ => l) → w x l i ≠ 0 :=
    fun h => ((isUnit_valR_iff _ _ (fun _ hz => H.basicOpen_le _ (h hz)) _).2 h).ne_zero
  have hv : ∀ x m m', ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m' → ∀ i,
      (b.map σ).mulVec (v x m) i = tv L (x ≫ ψ' ≫ π) m m' ^ N * (b.map σ).mulVec (v x m') i := by
    intro x m m' hm hm' i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e := (sec_val (s k) (x := x ≫ ψ') (i := fun _ => m) (j := fun _ => m') (le_wchart fun _ => hm)
      (le_wchart fun _ => hm')).trans (congrArg (· * _) (tv_linComb L _ _ (fun _ => hm) fun _ => hm'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.assoc] at e
    rw [mul_left_comm]
    exact congrArg _ e
  have hw : ∀ x l l', ⊤ ≤ x ⁻¹ᵁ M.U l → ⊤ ≤ x ⁻¹ᵁ M.U l' → ∀ i, w x l i = tv M x l l' ^ N * w x l' i := by
    intro x l l' hl hl' i
    have e := (sec_val (t i) (x := x) (i := fun _ => l) (j := fun _ => l') (le_wchart fun _ => hl)
      (le_wchart fun _ => hl')).trans (congrArg (· * _) (tv_linComb M _ _ (fun _ => hl) fun _ => hl'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.comp_id] at e
    exact e
  have key : ∀ x l m, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m →
      ∃ c : PadicAlgCl p, c ≠ 0 ∧ ∀ i, (b.map σ).mulVec (v x m) i = c * w (x ≫ j) l i := by
    intro x l m hx hl hm
    have h₁ := hlink x (v x m) hx ⟨fun _ => m, 1, le_wchart fun _ => hm, fun i => (_root_.one_mul _).symm⟩
    obtain ⟨c, hc⟩ := crd_unique (s := t) (x := x ≫ j) (v := w (x ≫ j) l)
      ⟨fun _ => l, 1, fun _ hz => Set.mem_iInter.2 fun _ => hl hz, fun i => (_root_.one_mul _).symm⟩ h₁
    exact ⟨c, c.ne_zero, hc⟩
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (J × M.ι) L.ι
    (fun a => H.basicOpen ((t a.1).f fun _ => a.2)) (fun m => (ψ' ≫ π) ⁻¹ᵁ L.U m)
    (fun a m x => (b.map σ).mulVec (v x m) a.1 * ω x a.2 m ^ N * (w (x ≫ j) a.2 a.1)⁻¹)
    (fun z => exists_chart hL _)
    (fun a m => ((Reg.sum fun k => (Reg.const (b a.1 k)).mul (Reg.pull ψ' (U := LB.wchart L (fun _ : Fin 1 => π) fun _ => m)
        (W := j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m)
        (fun _ hz => Set.mem_iInter.2 fun _ => hz.2) ((s k).f fun _ => m))).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m) a.2 m (fun _ hz => wl _ _ hz.1) fun _ hz => hz.2).1).pow _)).mul
      (Reg.inv_basicOpen j _ inf_le_left))
    (fun a m x hx ha hm => by
      obtain ⟨c, hc, e⟩ := key x a.2 m hx (fun _ hz => wl _ _ (ha hz)) hm
      exact mul_ne_zero (mul_ne_zero ((e _).trans_ne (mul_ne_zero hc (wne ha)))
        (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => wl _ _ (ha hz)) hm))) (inv_ne_zero (wne ha)))
    (fun a m m' x _ ha hm hm' => by
      beta_reduce
      rw [hv x m m' hm hm', ← hω.right x a.2 m m' (fun _ hz => wl _ _ (ha hz)) hm hm', mul_pow]
      ring)
    (fun a a' => ⟨1, fun m x hx ha ha' hm => by
      have hl : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a.2 := fun _ hz => wl _ _ (ha hz)
      have hl' : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a'.2 := fun _ hz => wl _ _ (ha' hz)
      obtain ⟨c, -, e⟩ := key x a.2 m hx hl hm
      have h₁ := wne ha
      have h₂ := wne ha'
      beta_reduce
      rw [valR_eq (x ≫ j) (H.basicOpen ((t a.1).f fun _ => a.2) ⊓ H.basicOpen ((t a'.1).f fun _ => a'.2))
        (le_inf ha ha'), Units.val_one, map_one, e, e,
        hw _ a.2 a'.2 hl hl' a'.1, hω.left x a.2 a'.2 m hl hl' hm, mul_pow]
      field_simp⟩)
  refine ⟨κ, hκ, fun c x l m hc hx hq hl hm => ?_⟩
  have hlw : ⊤ ≤ c ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l := fun _ hz => Set.mem_iInter.2 fun _ => hl hz
  obtain ⟨i₀, hi₀⟩ := hprim c _ hc ⟨fun _ => l, 1, hlw, fun i => (_root_.one_mul _).symm⟩
  have hwc : ∀ i, w (x ≫ j) l i = (valR c _ ((t i).f fun _ => l) : OO p) := fun i => by
    rw [hx]
    exact (valR_spMap (OO p).subtype c _ hlw).2 _
  have hle : ∀ i, ‖w (x ≫ j) l i‖ ≤ 1 := fun i => by
    rw [hwc]
    exact (mem_OO_iff _).1 (Subtype.prop _)
  have h1 : ‖w (x ≫ j) l i₀‖ = 1 := by
    obtain ⟨d, hd⟩ := hi₀.exists_right_inv
    have e : w (x ≫ j) l i₀ * (d : PadicAlgCl p) = 1 := by
      rw [hwc]
      exact congrArg Subtype.val hd
    have e' := congrArg norm e
    rw [norm_mul, norm_one] at e'
    exact le_antisymm (hle _) (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  obtain ⟨d, -, e⟩ := key x l m hq (by rw [hx]; exact fun _ _ => hl trivial) hm
  have h₀ := h (i₀, l) m c x hc hx hq ((isUnit_valR_iff _ _ hlw _).1 hi₀) hm
  have hd : ∀ i, ‖(b.map σ).mulVec (v x m) i * ω x l m ^ N‖ = κ * ‖w (x ≫ j) l i‖ := fun i => by
    rw [← h₀]
    simp only [e, norm_mul, norm_inv, h1]
    ring
  refine ⟨⟨i₀, (hd i₀).trans (by rw [h1, _root_.mul_one])⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (hd i).trans_le (mul_le_of_le_one_right hκ.le (hle i))

end GlobalTheory.ZH.FrameNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarMemOfPsiMemIdeal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem scalar_mem_of_psiIn : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → ∀ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), PsiScal D ga a → ∀ (x : D'.X) (J' : Ideal V), D'.PsiIn x J' → ∀ p q : R, algebraMap R (FractionRing R) q * (a (xe x)).val = algebraMap R (FractionRing R) p → ∃ m ∈ J', φ p = φ q * m := by
  intro R V _ _ _ _ _ φ D D' β v xe _ hv hc gam hgam hψ ga a hS x J' hJ' p q hpq
  obtain ⟨ga', a', hS'⟩ := exists_psiScal V D'
  obtain ⟨m₀, hm₀, em₀⟩ := (PsiScalIn.main_local D' ga' a' hS' x J').1 hJ'
  obtain ⟨t, ht, Ht⟩ := CubTransport.exists_pmaps ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => (D'.c x).left) (φ := fun _ => (D.c (xe x)).left) (ε := fun _ => -1) (spMap φ) (fun _ => hc x)
    (ga (xe x)) (hS (xe x)).1
  obtain ⟨c, hcu⟩ := exists_unit_val_eq_mul D'.P.isLB (hS' x).1 ht
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose I hI using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  choose I' hI' using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have gI : Good D.P.L (Z := (TK V).left) z I := hI
  have gI' : Good D'.P.L (Z := (TK V).left) z I' := hI'
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    change (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc x, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (D.c (xe x)).left) hgam.symm
  have e₁ := CubTransport.val_pmaps (fun _ => hx) (hψ x) (𝟙 _) gI gI'
  have e₂ := CubTransport.val_pmaps (fun _ => hc x) Ht (jK V) gI gI'
  have e₃ := (hS (xe x)).2 (Over.mk (gam ≫ jK R)) (Over.homMk gam rfl) z I gI
  have e₄ := (hS' x).2 (TK V) (𝟙 _) z I' gI'
  have e₅ := hcu _ (jK V) z I' gI'
  rw [Category.id_comp, Fintype.prod_unique, Category.id_comp] at e₁
  rw [Fintype.prod_unique, ← hgam] at e₂
  obtain ⟨Ω, f₁, f₂⟩ : ∃ Ω : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk z)ˣ,
      val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I' ∧
        val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) t (jK V) z I' := ⟨_, e₁, e₂⟩
  have f₃ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I).val =
      gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I).val := e₃
  have f₄ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I').val =
      PsiScalIn.sig z (a' x).val * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga' x) (jK V) z I').val :=
    e₄.trans (congrArg₂ (· * ·) (PsiScalIn.gs_scal_id z _) rfl)
  let u : V := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom c.val
  have hu : gs (jK V) z ⊤ c.val = PsiScalIn.sig z (algebraMap V _ u) := by
    refine Eq.trans (congrArg (gs (jK V) z ⊤) ?_) (PsiScalIn.gs_toOpen z ⊤ trivial u)
    simp [u, DegPre.toOpen]
  have key : gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) = PsiScalIn.sig z (algebraMap V _ (m₀ * u)) := by
    rw [f₁, f₂, Units.val_mul, Units.val_mul, f₄, mul_left_comm (gs _ _ _ _), Units.mul_right_inj] at f₃
    have f₅ := f₃.symm.trans (congrArg (PsiScalIn.sig z (a' x).val * ·) (e₅.trans (congrArg (· * _) hu)))
    rw [← _root_.mul_assoc, Units.mul_left_inj] at f₅
    rw [map_mul, map_mul, em₀]
    exact f₅
  have hs : ∀ r : R, gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (algebraMap R (FractionRing R) r)) =
      PsiScalIn.sig z (algebraMap V _ (φ r)) := fun r => by
    have k : ∀ {A : Type} [CommRing A] (w : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of A)) (s : A),
        gs (𝟙 _) z ⊤ (scal w s) = cst w z s := fun w s =>
      (gs_pull (𝟙 _) w z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
    refine (congrArg _ (PsiInt.scal_jK gam r).symm).trans ((k _ r).trans ?_)
    refine (congrArg (fun w => cst w z r) hgam).trans ((cst_comp (jK V) φ z r).trans ?_)
    refine Eq.trans ?_ (PsiScalIn.gs_toOpen z ⊤ trivial (φ r))
    exact (gs_res (jK V) z (U := ⊤) (V := ⊤) le_top trivial _).symm
  refine ⟨m₀ * u, J'.mul_mem_right u hm₀, IsFractionRing.injective V (FractionRing V) ((PsiScalIn.sig z).injective ?_)⟩
  rw [map_mul (algebraMap V _) (φ q), map_mul (PsiScalIn.sig z), ← hs, ← hs, ← key, ← hpq, ← gs_mul _ z ⊤ trivial]
  unfold scal
  rw [map_mul, map_mul]

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanTranslatesMultiplicationPullbackTheta
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory.ThetaReal

open GlobalTheory.VVRank

theorem span_translates_mulPull : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(S, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ (κ : Type) [Fintype κ] (b : κ → SecM P.A P.L N (baseOver S)), UnivBasis P N b → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver S)), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver S)) (t : I → LB.Sec (LPow P.A P.L N (baseOver S))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver S).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver S))) = ⊤ := by
  intro hL S _ _ P m N hN hm hunit th hth κ _ b₀ hb₀ α hα s₁ hs₁ I U t hU ht
  subst hN
  have hm0 : m ≠ 0 := by omega
  have hk : m ^ 2 = 1 ∨ 4 ≤ m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [show m = 1 by omega]; rfl
    · right; nlinarith
  have hsurj : Surjective (mulA P.A m).left := (hL.mulN S P m hm).2.2.1
  have haff : IsAffine (baseOver S).left := ‹IsAffine S›
  obtain ⟨b, hb⟩ := hb₀ (baseOver S) (𝟙 _)
  refine span_eq_top_of_functionals b _ fun 𝔪 h𝔪 l hl y => ?_
  obtain ⟨K, _, _, u, hu⟩ := exists_geomPoint (baseOver S).left 𝔪 h𝔪
  let w : Spec (CommRingCat.of K) ⟶ S := u
  let h : Over.mk w ⟶ baseOver S := Over.homMk w (Category.comp_id _)
  have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
  have hntK : Nontrivial Γ((Over.mk w).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  obtain ⟨b', hb'⟩ := hb₀ (Over.mk w) h
  obtain ⟨b₁', hb₁'⟩ := hth (Over.mk w) h
  refine (hu _).1 (functional_mem_of_span h.left.appTop.hom (pullM P.A P.L (m ^ 2 : ℕ) h) b b'
    (fun i => by rw [hb, hb', pullM_id P.A P.isLB]) _ ?_ l (fun c => (hu _).2 (hl c)) y)
  obtain ⟨ρ', k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns S P (m ^ 2 : ℕ) (Over.mk w)
  choose U' hU' using fun c => exists_theta_pull P.A P.isLB h (U c)
  have e : ∀ c, pullM P.A P.L (m ^ 2 : ℕ) h (SecM.ofSec P.A (t c)) =
      ρ' (U' c) (SecM.ofSec P.A (pullS P.A _ h s₁)) := fun c =>
    ((k₁ _ _ _).1 ((hU' c).2 _ _ (ht c))).symm
  simp only [e]
  have hI : Nonempty I := ⟨(hU K w 1 (by have := P.isAb.comm; exact one_pow _)).choose⟩
  refine span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred S P K w (m ^ 2) hk
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ (natCast_ne_zero w hunit))) ρ' k₁ k₃ k₄ U'
    (fun θ => ?_) _ fun h0 => ?_
  · obtain ⟨c, hc'⟩ := hU K w θ.pt ((hL.kerPow S P (m ^ 2) (Nat.one_le_pow _ _ hm) (Over.mk w) θ.pt).1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
    exact ⟨c, (hU' c).1.trans hc'⟩
  · obtain ⟨α', -, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A (baseOver S) m) (hm := lift_snd _ _)
      (b := 1) P.isLB hα h (ψ' := mulT P.A (Over.mk w) m) (lift_snd _ _) (mulT_comm P.A h m)
    have hint : IsIntegral (Over.mk w ⊗ P.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
        P.isAb.geomConnected).geometrically_isIntegral w _ _
        (IsPullback.of_hasPullback w P.A.hom).flip
    have hz := ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A m hsurj _) (k₂ _ _ hs₁) h0
    exact b₁'.ne_zero 0 ((hb₁' 0).trans hz)

end GlobalTheory.ThetaReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsReg
open GlobalTheory.Points

theorem valR_appIso_inv {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (U : X.Opens) (f : Γ(X, U))
    {C : Type} [CommRing C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    valR (y ≫ j) (j ''ᵁ U) ((j.appIso U).inv.hom f) = valR y U f := by
  rw [← valR_appLE y j (j.preimage_image_eq U).ge hy, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res y le_rfl hy f

theorem valR_valueAt {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ) [GrpObj A] {T : Over B}
    {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [CommRing K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) = valR x ⊤ v * valR x _ (τ.s fun _ => j).val := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  exact e

theorem range_subset {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) {U : X.Opens} (p : Sp K) (h : x p ∈ U) :
    Set.range x ⊆ U := by
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y p]
  exact h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_eq_mul_unit (hne : (U₀ : Set M.Z).Nonempty) {N : M.Z.Opens} {σ : Q.SecFam N} {c : Ω}
    (hσ : Q.ThMul c N σ) {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.left} {w : W.toScheme}
    (hE : Q.ExtPt a W h) (hF : Q.FrameUnit a W h w) (hw : W.ι w ∈ N) (jL : Q.L.L.ι) (hj : h w ∈ Q.L.L.U jL) :
    ∃ (T : M.Z.Opens) (f : Γ(M.Z, T)) (e : Ω), W.ι w ∈ T ∧ e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w) ∧
      c * S.th a = valF M.pt T f * e⁻¹ ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), Set.range y = {w} →
        valF (y ≫ W.ι) T f = valF (y ≫ h) _ (σ fun _ => jL) := by
  let V : W.toScheme.Opens := h ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL)
  have hwV : w ∈ V := by
    refine ⟨?_, Set.mem_iInter.2 fun _ => hj⟩
    change (h ≫ Q.G.hom) w ∈ N
    rw [hE.1]
    exact hw
  have hT : W.ι w ∈ W.ι ''ᵁ V := ⟨w, hwV, rfl⟩
  have hval : ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), ⊤ ≤ y ⁻¹ᵁ V →
      valF (y ≫ W.ι) (W.ι ''ᵁ V) ((W.ι.appIso V).inv.hom ((h.app _).hom (σ fun _ => jL))) =
        valF (y ≫ h) _ (σ fun _ => jL) := fun K _ y hy =>
    (valR_appIso_inv W.ι V _ y hy).trans (valR_comp y h _ _).symm
  have lift : ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι M.pt (by
      rw [Scheme.Opens.range_ι]
      exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hU)), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨x, hx⟩ := lift W ⟨w.1, w.2⟩
  obtain ⟨x₀, hx₀⟩ := lift U₀ hne
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  have hcond : (t₀ ≫ (ρ.pt a).left) ≫ ρ.P.A.hom = x₀ ≫ Q.u₀ := by
    rw [Q.u₀_gen x₀ hx₀, Category.assoc, Over.w (ρ.pt a)]
    exact Category.comp_id _
  let x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀ := pullback.lift _ _ hcond
  have h1 : x' ≫ pullback.fst _ _ = t₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have h2 : x' ≫ pullback.snd _ _ ≫ U₀.ι = M.pt := by
    rw [← Category.assoc, pullback.lift_snd, hx₀]
  have h3 : x' ≫ Q.φ ≫ Q.G.hom = M.pt := by
    rw [← h2]
    exact congrArg (x' ≫ ·) Q.cart.1.w
  have h4 : x ≫ h = x' ≫ Q.φ := hE.2 x x' hx h3 h1
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := by
    have h5 := M.top_le_preimage_pt ⟨_, hT⟩
    rw [← hx] at h5
    exact le_preimage_mono x (W.ι.preimage_image_eq V).le h5
  have hxh : Set.range (x' ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL : Q.G.left.Opens) := by
    rw [← h4]
    exact (top_le_preimage_iff _ _).1 hxV
  obtain ⟨jP, hjP⟩ : ∃ jP, Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U jP := by
    have h5 : (t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω) ∈ ⨆ i, ρ.P.L.U i := by
      rw [ρ.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    exact ⟨i, range_subset _ _ hi⟩
  obtain ⟨he0, he1, he2⟩ := hF jP jL x' _ hj h3 h1 (h1 ▸ hjP) rfl
  refine ⟨_, _, _, hT, he0, he1, he2, ?_, fun K _ y hy => hval K y fun p _ => ?_⟩
  · have hr : (t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        x' ≫ pullback.fst _ _ := by
      rw [h1, Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
    have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := Spec.map_id _
    have e := hσ Ω (RingHom.id Ω) x' _ jP jL (by rw [h2, hid, Category.id_comp]) hr (h1 ▸ hjP)
      (fun p hp => Set.mem_iInter.1 (hxh hp).2 0) (fun p hp => (hxh hp).1)
    have e2 := valR_valueAt ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ jP hjP
    have e3 : valR (X := (baseOver (Sp S.R)).left) t₀ ⊤ (fn (⟨S.th a, S.th_mem a⟩ : S.R)) = S.th a :=
      valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _
    rw [e3] at e2
    rw [Fintype.sum_unique, zpow_one, RingHom.id_apply, valF_eq_valR, e2, ← h4, ← hval Ω x hxV, hx] at e
    have hn := (div_ne_zero_iff.1 he0).1
    rw [inv_div, ← mul_div_assoc, eq_div_iff hn, _root_.mul_assoc, _root_.mul_comm (valF M.pt _ _)]
    exact e
  · have h5 : y p ∈ Set.range y := ⟨p, rfl⟩
    rw [hy] at h5
    change y p ∈ V
    rw [show y p = w from h5]
    exact hwV

end GlobalTheory.ZH.TorsReg


open GlobalTheory.Points GlobalTheory.ZH.TorsReg in
theorem GlobalTheory.ZH.mul_theta_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (c : Ω), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w → W.ι w ∈ N → c * S.th a ∈ M.O (W.ι w) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι), Set.range x = {w} → valF (x ≫ h) _ (σ j) ≠ 0 → c * S.th a ≠ 0 ∧ (c * S.th a)⁻¹ ∈ M.O (W.ι w) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N σ c _ hσ a W h w hE hF hw
  constructor
  · have h5 : h w ∈ ⨆ i, Q.L.L.U i := by
      rw [Q.L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    obtain ⟨T, f, e, hT, -, -, he, hc, -⟩ := GlobalTheory.ZH.TorsReg.exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [hc]
    exact mul_mem (RatModel.valF_mem_O hT f) he
  · intro K _ x j hx hv
    have hxw : x (IsLocalRing.closedPoint K) = w := by
      have h5 : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at h5
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
    have hi : h w ∈ Q.L.L.U i := by
      by_contra hi
      refine hv (dif_neg fun hle => hi ?_)
      rw [← hxw]
      exact Set.mem_iInter.1 (hle (x := IsLocalRing.closedPoint K) trivial).2 0
    obtain ⟨T, f, e, hT, he0, he1, -, hc, hK⟩ := GlobalTheory.ZH.TorsReg.exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [← hK K x hx] at hv
    have hxw' : (x ≫ W.ι) (IsLocalRing.closedPoint K) = W.ι w := by rw [← hxw]; rfl
    have hle : ⊤ ≤ (x ≫ W.ι) ⁻¹ᵁ T := (GlobalTheory.Points.le_preimage_iff _ _).2 (hxw' ▸ hT)
    have hb : W.ι w ∈ M.Z.basicOpen f :=
      hxw' ▸ (GlobalTheory.Points.le_preimage_iff _ _).1 ((GlobalTheory.Points.le_preimage_basicOpen_iff _ hle f).2 (isUnit_iff_ne_zero.2 hv))
    obtain ⟨hf0, hf1⟩ := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hT f).2 hb)
    rw [hc]
    refine ⟨mul_ne_zero hf0 (inv_ne_zero he0), ?_⟩
    rw [_root_.mul_inv, inv_inv]
    exact mul_mem hf1 he1

end
end

