module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
public import GroundTheory.GlobalFields.TateThesis.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BoundInf
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

private theorem entry_sq_le {ι : Type} [Fintype ι] {a : ℕ} (A : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin a) :
    ‖A i j‖ ≤ Real.sqrt ‖(A * star A) i i‖ := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => Real.le_sqrt_of_sq_le ?_
  refine le_trans ?_ (norm_le_pi_norm ((A * star A) i i) w)
  have h : (A * star A) i i w = ((∑ k, ‖A i k w‖ ^ 2 : ℝ) : ℂ) := by
    simp [Matrix.mul_apply, Finset.sum_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (Finset.single_le_sum (f := fun k => ‖A i k w‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)) (le_abs_self _)

theorem boundInf : BoundInf := by
  intro E _ _ a K hK hc
  obtain ⟨C₁, hC₁⟩ := hc.isBounded.exists_norm_le
  have hcont : ContinuousOn (fun p : HV E a => toL (Matrix.of p.1)⁻¹) K := by
    intro p hp
    obtain ⟨h, rfl⟩ := hK hp
    have hu : IsUnit (Matrix.of (sand h (hOne E a)).1).det := by
      rw [sand_val, hOne_val, mul_one, ← Matrix.isUnit_iff_isUnit_det]
      exact h.isUnit.mul h.isUnit.star
    have h1 : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (Matrix.of (sand h (hOne E a)).1) :=
      continuousAt_matrix_inv _ (by
        obtain ⟨u, hu⟩ := hu
        rw [← hu]
        exact NormedRing.inverse_continuousAt u)
    have h2 : Continuous (fun p : HV E a => (Matrix.of p.1 : Matrix (Fin a) (Fin a) (Cinf E))) :=
      continuous_subtype_val
    exact (ContinuousAt.comp (f := fun p : HV E a => (Matrix.of p.1 : Matrix (Fin a) (Fin a) (Cinf E))) h1
      h2.continuousAt).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨a * (Real.sqrt C₁ * Real.sqrt C₂), fun g p hp hgp => ?_⟩
  obtain ⟨h, rfl⟩ := hK hp
  have hA : ∀ i j, ‖(g * h).val i j‖ ≤ Real.sqrt C₁ := fun i j => by
    refine (entry_sq_le _ i j).trans (Real.sqrt_le_sqrt (le_trans ?_ (hC₁ _ hgp)))
    have e : (g * h).val * star (g * h).val = Matrix.of (sand g (sand h (hOne E a))).1 := by
      rw [sand_val, sand_val, hOne_val]; simp only [Units.val_mul, star_mul, mul_assoc, one_mul]
    rw [e]
    exact (norm_le_pi_norm _ i).trans (norm_le_pi_norm (sand g (sand h (hOne E a))).1 i)
  have hB : ∀ i j, ‖(h⁻¹).val i j‖ ≤ Real.sqrt C₂ := fun i j => by
    have e0 : ‖(h⁻¹).val i j‖ = ‖(star (h⁻¹).val) j i‖ := by rw [Matrix.star_apply, norm_star]
    rw [e0]
    refine (entry_sq_le _ j i).trans (Real.sqrt_le_sqrt (le_trans ?_ (hC₂ _ hp)))
    have e : star (h⁻¹).val * star (star (h⁻¹).val) = (Matrix.of (sand h (hOne E a)).1)⁻¹ := by
      rw [sand_val, hOne_val, mul_one, star_star]
      refine (Matrix.inv_eq_left_inv ?_).symm
      rw [mul_assoc, ← mul_assoc (h⁻¹).val, Units.inv_mul, one_mul, ← star_mul, Units.mul_inv, star_one]
    rw [e]
    exact (norm_le_pi_norm _ j).trans (norm_le_pi_norm (toL (Matrix.of (sand h (hOne E a)).1)⁻¹) j)
  have h0 : (0 : ℝ) ≤ a * (Real.sqrt C₁ * Real.sqrt C₂) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have e : g.val = (g * h).val * (h⁻¹).val := by rw [← Units.val_mul, mul_inv_cancel_right]
  change ‖g.val i j‖ ≤ _
  rw [e, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
    (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (Real.sqrt_nonneg _))).trans ?_
  simp

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CentralOf
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

theorem centralOf : CentralOf := by
  intro E _ _ a M _ _ _ _ L q η h1 h2 X
  let o : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have h := h2 (Fin.cons o X) 0 rfl
  rw [dCo_apply, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero] at h
  · have e : Fin.removeNth (α := fun _ => Herm E a) 0 (Fin.cons o X) = X := by
      funext j; simp [Fin.removeNth]
    rw [e, Fin.val_zero, pow_zero, one_smul] at h
    exact h
  · intro i _
    have hz : η (Fin.removeNth (α := fun _ => Herm E a) i.succ (Fin.cons o X)) = 0 := by
      cases q with
      | zero => exact i.elim0
      | succ q =>
        refine h1 _ 0 ?_
        simp only [Fin.removeNth, Fin.succ_succAbove_zero, Fin.cons_zero]
        rfl
    rw [hz, map_zero, smul_zero]

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ConePos
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped ComplexOrder MatrixOrder

namespace UpperTheory.V.Lit.Dr

private theorem posDef_iff_mul_star {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    M.PosDef ↔ ∃ B : Matrix n n ℂ, IsUnit B ∧ M = B * star B := by
  open scoped Matrix.Norms.L2Operator in
  rw [← Matrix.isStrictlyPositive_iff_posDef, CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self]

private theorem pi_iff {n ι : Type} [Fintype n] [DecidableEq n] (M : Matrix n n (ι → ℂ)) :
    (∃ g : GL n (ι → ℂ), g.val * 1 * star g.val = M) ↔ ∀ w, (Matrix.of fun i j => M i j w).PosDef := by
  simp only [posDef_iff_mul_star, mul_one]
  constructor
  · rintro ⟨g, rfl⟩ w
    refine ⟨g.val.map (Pi.evalRingHom (fun _ => ℂ) w), ?_, ?_⟩
    · exact g.isUnit.map (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix
    · ext i j
      simp [Matrix.mul_apply, Finset.sum_apply]
  · intro h
    choose B hB hM using h
    have hu : IsUnit (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
      intro w
      have := RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ))
      rw [Pi.evalRingHom_apply] at this
      rw [this, ← Matrix.isUnit_iff_isUnit_det]
      exact hB w
    refine ⟨hu.unit, ?_⟩
    ext i j w
    have := congrFun (congrFun (hM w) i) j
    simp only [Matrix.of_apply] at this
    rw [this]
    simp [Matrix.mul_apply, Finset.sum_apply]

theorem conePos : ConePos := by
  intro E _ _ a p
  refine Iff.trans ?_ (pi_iff (Matrix.of p.1))
  exact exists_congr fun g => Subtype.ext_iff

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrInv
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_mul_split (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    infGL E a (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) *
        finGL E a (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * (infGL E a g * finGL E a x) := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem split_ga (g : GA E a) :
    infGL E a (GeneralLinearGroup.map (pInf E) g) * finGL E a (GeneralLinearGroup.map (pFin E) g) = g := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]

private theorem act_corr (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ)
    (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (geo ho U Ξ).Om q) (h : Corr U Ξ α w.1)
    (γ : (⊤ : Subgroup (GL (Fin a) E))) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (X : Fin q → Herm E a) :
    ((geo ho U Ξ).act q γ w).1 (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a))
        (fun i => (2 : ℝ) • sand g (hv (X i))) =
      Ξ.mat g *ᵥ ev (α X) (ratGL E a (γ⁻¹).1 * (infGL E a g * finGL E a x)) := by
  have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ⁻¹ (sand g p) =
      sand (GeneralLinearGroup.map (pInf E) (ratGL E a (γ⁻¹).1) * g) p := fun p => by
    rw [geo_ρ, map_mul]; rfl
  have hσ : (geo ho U Ξ).σ γ⁻¹ (x : GL (Fin a) (Af E) ⧸ U) =
      ((GeneralLinearGroup.map (algebraMap E (Af E)) (γ⁻¹).1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
  rw [Geo.act_apply, hσ]
  simp only [map_smul, hs]
  rw [h, rat_mul_split, geo_ξ, Matrix.mulVec_mulVec, ← map_mul, ← mul_assoc, ← map_mul, ← map_mul]
  simp only [Subgroup.coe_inv, mul_inv_cancel, map_one, one_mul]

theorem corrInv : CorrInv := by
  intro E _ _ _ a ho U Ξ q α w h
  constructor
  · intro hL γ
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ cone E a
    · obtain ⟨g, rfl⟩ := hp
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
      ext1 v
      have hv' : v = fun i => (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i)))) := by
        funext i
        rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, ← ContinuousLinearMap.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        simp
      rw [hv', act_corr ho U Ξ q α w h, h, hL]
    · rw [(((geo ho U Ξ).act q γ w).2 s).2 p hp, (w.2 s).2 p hp]
  · intro hw X γ g
    have h1 := act_corr ho U Ξ q α w h (⟨γ, Subgroup.mem_top γ⟩ : (⊤ : Subgroup (GL (Fin a) E)))⁻¹
      (GeneralLinearGroup.map (pInf E) g) (GeneralLinearGroup.map (pFin E) g) X
    rw [hw, h, split_ga, inv_inv] at h1
    have h2 := congrArg (fun y => Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹ *ᵥ y) h1
    simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
    exact h2.symm

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DeRhamInjOf
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

theorem geo_main (h1 : AbsMain) (h2 : DEquiv) (h3 : InclFacts) (h4 : DExact) (h5 : Average) (h6 : Window) (h7 : Cutoff)
    {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ} (G : Geo Γ V S d)
    (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (hp : G.Proper) (q n : ℕ) (w : Fin n → G.Om q)
    (hi : ∀ i γ, G.act q γ (w i) = w i) (hd : ∀ i, G.dOm q (w i) = 0)
    (hx : ∀ c : Fin n → ℂ, InvExact (Ω := fun q => G.Om q) G.act G.dOm (∑ i, c i • w i) → c = 0) :
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of G.lev) q) := by
  obtain ⟨W, hW⟩ := h6 Γ V S d G hp
  obtain ⟨u, hu⟩ := h7 Γ V S d G W hW
  obtain ⟨a1, a2, a3⟩ := h3 Γ V S d G hc hn
  exact h1 q Γ _ (fun q => G.Om q) G.lev G.act G.incl G.dOm a1 (h2 Γ V S d G) a2 a3 (h4 Γ V S d G hc) (h5 Γ V S d G u hu)
    n w hi hd hx

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ}

private theorem alt_sum {V M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup M] [Module ℝ M] {n : ℕ}
    (f : Fin n → V [⋀^Fin q]→ₗ[ℝ] M) (X : Fin q → V) : (∑ i, f i) X = ∑ i, f i X :=
  map_sum (AddMonoidHom.mk' (fun g : V [⋀^Fin q]→ₗ[ℝ] M => g X) fun _ _ => rfl) f _

theorem corr_zero : Corr (q := q) U Ξ 0 0 := fun g x X => by simp

theorem corr_sum {n : ℕ} (c : Fin n → ℂ) {α : Fin n → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))}
    {w : Fin n → (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)} (h : ∀ i, Corr U Ξ (α i) (w i)) :
    Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i) := fun g x X => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [alt_sum, map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
    Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlternatingMap.smul_apply, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_smul, ← h i g x X]
  rfl

end

theorem deRhamInj_of (h1 : AbsMain) (h2 : DEquiv) (h3 : InclFacts) (h4 : DExact) (h5 : Average) (h6 : Window) (h7 : Cutoff)
    (h8 : Retract) (k1 : LocSec) (k2 : ConeConvex) (k3 : GeoProper) (k4 : Gauge) (k5 : LevelVal) (k6 : CentralOf)
    (k7 : CorrFwd) (k8 : CorrSmooth) (k9 : CorrBwd) (k10 : CorrCochain) (k11 : CorrUniq) (k12 : CorrInv) (k13 : CorrBasic)
    (k14 : CorrD) : DeRhamInj := by
  intro E _ _ _ a ha U _ hU Ξ q n α hα hind
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := k1 E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have hv : ∀ i X, LeftInv (α i X) ∧ RightInv U (α i X) := fun i X => (k5 E a U Ξ _).1 ((hα i).1.val X)
  have hw : ∀ i, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (α i) w.1 := fun i => by
    obtain ⟨w, hw, h0⟩ := k7 E a U Ξ q (α i) (hα i).1.equiv fun X => (hv i X).2
    exact ⟨⟨w, fun s => ⟨k8 E a U Ξ q _ w hw s, h0 s⟩⟩, hw⟩
  choose w hw using hw
  rw [← geo_lev ho U Ξ]
  refine geo_main h1 h2 h3 h4 h5 h6 h7 (geo ho U Ξ) (k2 E a).1 ⟨_, hOne_mem_cone⟩ (k3 E a ho U Ξ hU) q n w
    (fun i => (k12 E a ho U Ξ q _ _ (hw i)).1 fun X => (hv i X).1) (fun i => ?_) fun c hc => hind c ?_
  · have h := k14 E a ho U Ξ q _ _ (hw i)
    rw [(hα i).2] at h
    exact (k11 E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)
  · have hs : Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i).1 := by
      rw [Submodule.coe_sum]
      exact corr_sum U Ξ c hw
    have hb : ∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → (∑ i, c i • α i) X = 0 := fun X i hX => by
      rw [alt_sum]
      exact Finset.sum_eq_zero fun j _ => by rw [AlternatingMap.smul_apply, (hα j).1.basic X i hX, smul_zero]
    generalize ∑ i, c i • α i = β at hs hb
    generalize ∑ i, c i • w i = z at hs hc
    cases q with
    | zero =>
      obtain rfl : z = 0 := hc
      exact (k11 E a ho U Ξ 0).1 _ 0 _ hs (corr_zero U Ξ)
    | succ q =>
      obtain ⟨y, hy, rfl⟩ := hc
      obtain ⟨l, hl⟩ := k4 E a ha ho U Ξ hU
      obtain ⟨y', i1, i2, i3⟩ := h8 _ _ _ _ (geo ho U Ξ) (k2 E a).2 l hl q y hy ((k13 E a U Ξ _ _ _ hs).1 hb)
      obtain ⟨η, hη⟩ := k9 E a ho U Ξ q y'
      have e : dCo (smLie Ξ) η = β := (k11 E a ho U Ξ (q + 1)).1 _ _ _ (i3 ▸ k14 E a ho U Ξ q _ _ hη) hs
      have b := (k13 E a U Ξ _ _ _ hη).2 i2
      obtain ⟨c1, c2⟩ := k10 E a U Ξ q _ _ hη
      exact ⟨η, ⟨c1, b, fun X => (k5 E a U Ξ _).2 ((k12 E a ho U Ξ q _ _ hη).2 i1 X) (c2 X)
        (k6 E a _ (smLie Ξ) q η b (e ▸ hb) X)⟩, e⟩

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvDeriv
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem hasDerivAt_evaluation_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a)
    (X : Lie E a) (c : ℝ → GL (Fin a) (Cinf E)) (h0 : c 0 = 1) (hX : HasDerivAt (fun t => toL (c t).val) X 0)
    (h : GA E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    HasDerivAt (fun t => Ξ.mat (c t) *ᵥ ev m (h * infGL E a (c t))) (ev (smLie Ξ X m) h) 0 := by
  induction m using TensorProduct.induction_on with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : Fin Ξ.d → ℂ)
  | add x y hx hy =>
    simpa only [map_add (f := _), Pi.add_apply, Matrix.mulVec_add] using hx.fun_add hy
  | tmul φ v =>
    have h1 := GlobalTheory.CuspRep.hasDerivAt_curve φ h c X h0 hX
    have h2 : HasDerivAt (fun t => Ξ.mat (c t) *ᵥ v) (Ξ.dmat X *ᵥ v) 0 :=
      hasDerivAt_pi.2 fun j => HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        (Ξ.hasDerivAt_curve c X h0 hX j i).mul_const (v i)
    have h3 := h1.fun_smul h2
    simp only [h0, map_one, mul_one, Matrix.one_mulVec] at h3
    have h4 : ev (smLie Ξ X (φ ⊗ₜ[ℂ] v)) h = φ.1 h • Ξ.dmat X *ᵥ v + lieD X φ.1 h • v := by
      change ev ((lie E a X φ) ⊗ₜ[ℂ] v + φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v)) h = _
      rw [map_add (f := _), Pi.add_apply, ev_tmul, ev_tmul, add_comm]
      rfl
    rw [h4]
    simpa only [ev_tmul, Matrix.mulVec_smul] using h3

theorem evDeriv : EvDeriv := by
  intro E _ _ _ a Ξ m g x c X h0 hX
  have h1 := (mulVecL (Ξ.mat g)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_evaluation_lie Ξ X c h0 hX (infGL E a g * finGL E a x) m)
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e : infGL E a (g * c t) * finGL E a x = infGL E a g * finGL E a x * infGL E a (c t) := by
    rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
  simp only [Function.comp, mulVecL_apply, e, map_mul (Ξ.mat), Matrix.mulVec_mulVec]

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvFacts
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem ev_comp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    (fun g => ev m g j) = (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d) m j).1 := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [(ev (E := E) (a := a) (d := d)).map_zero,
      (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).map_zero]
    rfl
  | tmul φ v =>
    funext g
    simp [mul_comm]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), Pi.add_apply, Submodule.coe_add, ← hx, ← hy]
    rfl

theorem evFacts : EvFacts := by
  intro E _ _ _ a d
  refine ⟨fun m m' h => ?_, fun m j => ?_, fun f hf => ?_⟩
  · apply (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).injective
    funext j
    apply Subtype.ext
    rw [← ev_comp, ← ev_comp, h]
  · rw [ev_comp]
    exact Subtype.property _
  · refine ⟨(TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩, ?_⟩
    funext g j
    have := congrFun (ev_comp ((TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩) j) g
    rw [LinearEquiv.apply_symm_apply] at this
    exact this

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvK
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

theorem evK : EvK := by
  intro E _ _ _ a Ξ k m g
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    have h : ev (smK Ξ k (φ ⊗ₜ[ℂ] v)) g =
        φ.1 (g * infGL E a (Unitary.toUnits k)) • (Ξ.mat (Unitary.toUnits k) *ᵥ v) := rfl
    rw [h, ev_tmul, Matrix.mulVec_smul]
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, Matrix.mulVec_add]

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.FinField
section
open NumberField IsDedekindDomain

theorem UpperTheory.V.Lit.Dr.finField : UpperTheory.V.Lit.Dr.FinField := by
  intro E _ _ C T hT
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_mul_mem_integralFiniteAdeles_of_isCompact (K := E) hT
  have hdE : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ
    ((∑ w : InfinitePlace E, w (algebraMap (𝓞 E) E d)) * C)
  refine Set.Finite.of_finite_image (f := fun x => algebraMap (𝓞 E) E d * x) (hfin.subset ?_)
    (mul_right_injective₀ hdE).injOn
  rintro _ ⟨x, ⟨hx, hxT⟩, rfl⟩
  refine ⟨?_, fun φ => ?_⟩
  · have h := hd _ hxT
    rw [← map_mul] at h
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
      (algebraMap (𝓞 E) E d * x) fun v => by
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
        exact GroundTheory.Global.mem_integralFiniteAdeles.1 h v
    beta_reduce
    rw [← hz]
    exact RingOfIntegers.isIntegral_coe _
  · beta_reduce
    rw [← InfinitePlace.apply, map_mul]
    exact mul_le_mul
      (Finset.single_le_sum (f := fun w : InfinitePlace E => w (algebraMap (𝓞 E) E d))
        (fun w _ => apply_nonneg w _) (Finset.mem_univ _))
      (hx _) (apply_nonneg _ _) (Finset.sum_nonneg fun w _ => apply_nonneg w _)
end

