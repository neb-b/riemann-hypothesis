module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldBd
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def pol0 (A B : Matrix (Fin a) (Fin a) (Cinf E)) : HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨toL (A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A), by
        have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
        change star (A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A) =
          A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A
        simp only [star_add, star_mul, star_star, hv, mul_assoc]
        exact add_comm _ _⟩
      map_add' := fun p p' => Subtype.ext (by
        change A * (Matrix.of p.1 + Matrix.of p'.1) * star B + B * (Matrix.of p.1 + Matrix.of p'.1) * star A =
          (A * Matrix.of p.1 * star B + B * Matrix.of p.1 * star A) +
            (A * Matrix.of p'.1 * star B + B * Matrix.of p'.1 * star A)
        simp only [mul_add, add_mul]; abel)
      map_smul' := fun c p => Subtype.ext (by
        change A * (c • Matrix.of p.1) * star B + B * (c • Matrix.of p.1) * star A =
          c • (A * Matrix.of p.1 * star B + B * Matrix.of p.1 * star A)
        simp only [mul_smul_comm, smul_mul_assoc, smul_add]) }

private theorem polarization_val (A B : Matrix (Fin a) (Fin a) (Cinf E)) (v : HV E a) :
    Matrix.of (pol0 A B v).1 = A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A := rfl

private theorem hv_ext {v w : HV E a} (h : Matrix.of v.1 = Matrix.of w.1) : v = w := Subtype.ext h

private theorem polarization_comm (A B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 A B = pol0 B A :=
  ContinuousLinearMap.ext fun v => hv_ext (by rw [polarization_val, polarization_val, add_comm])

private theorem polarization_add (A A' B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 (A + A') B = pol0 A B + pol0 A' B :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change _ = Matrix.of (pol0 A B v).1 + Matrix.of (pol0 A' B v).1
    simp only [polarization_val, star_add, mul_add, add_mul]; abel)

private theorem polarization_smul (c : ℝ) (A B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 (c • A) B = c • pol0 A B :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change _ = c • Matrix.of (pol0 A B v).1
    simp only [polarization_val, star_smul, star_trivial c, mul_smul_comm, smul_mul_assoc, smul_add])


variable (E a) in
private def pol : Lie E a →L[ℝ] Lie E a →L[ℝ] HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    LinearMap.mk₂ ℝ (fun A B : Lie E a => pol0 (Matrix.of A) (Matrix.of B)) (fun A A' B => polarization_add _ _ _)
      (fun c A B => polarization_smul c _ _)
      (fun A B B' => (polarization_comm _ _).trans ((polarization_add _ _ _).trans (congrArg₂ (· + ·) (polarization_comm _ _) (polarization_comm _ _))))
      (fun c A B => (polarization_comm _ _).trans ((polarization_smul c _ _).trans (congrArg (c • ·) (polarization_comm _ _)))))

private theorem pol_sand (g : GL (Fin a) (Cinf E)) :
    sand g = (2⁻¹ : ℝ) • pol E a (toL g.val) (toL g.val) :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change g.val * Matrix.of v.1 * star g.val =
      (2⁻¹ : ℝ) • (g.val * Matrix.of v.1 * star g.val + g.val * Matrix.of v.1 * star g.val)
    rw [← two_smul ℝ, smul_smul]; norm_num)

private theorem sand_der (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hX : HasDerivAt (fun t => toL (c t).val) X 0) :
    HasDerivAt (fun t => sand (c t)) (pol E a X (toL 1)) 0 := by
  have h1 := (((pol E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hX).clm_apply hX).const_smul (2⁻¹ : ℝ)
  simp only [Function.comp, h0, Units.val_one] at h1
  have e : pol E a (toL 1) X = pol E a X (toL 1) := polarization_comm _ _
  rw [e, ← two_smul ℝ, smul_smul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, one_smul] at h1
  exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => pol_sand _)

private theorem pol_one (v : HV E a) : pol E a ((2⁻¹ : ℝ) • v.1) (toL 1) (hOne E a) = v := by
  rw [map_smul]
  refine hv_ext ?_
  have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
  change (2⁻¹ : ℝ) • (Matrix.of v.1 * 1 * star 1 + 1 * 1 * star (Matrix.of v.1)) = _
  rw [hv, star_one, mul_one, mul_one, one_mul, one_mul, ← two_smul ℝ, smul_smul]; norm_num

private theorem flow_der {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (h : DifferentiableAt ℝ W p) (t : ℝ) (v : V) : fderiv ℝ (flow W t) p v = v + t • fderiv ℝ W p v := by
  have h4 : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (h.hasFDerivAt.const_smul t)
  rw [h4.fderiv]
  rfl

theorem fieldBd : FieldBd := by
  intro E _ _ _ a U Y C hY W hW
  obtain ⟨B, hB, hD⟩ := fieldDer E a U Y C hY
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  set K : ℝ := ‖(pol E a).flip (toL 1)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨1 + (K * B + B), by positivity, fun g x t ht v => ?_⟩
  obtain ⟨c, h0, -, -, hX, -⟩ := oneParam E a ((2⁻¹ : ℝ) • v.1)
  obtain ⟨hb, hz⟩ := hD (infGL E a g * finGL E a x)
  obtain ⟨Z, hZ, hd⟩ := hz c _ h0 hX
  have hn : ‖(2⁻¹ : ℝ) • v.1‖ ≤ ‖v‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  have hs := sand_der c _ h0 hX
  set P := pol E a ((2⁻¹ : ℝ) • v.1) (toL 1) with hP
  set y := hv (Y (infGL E a g * finGL E a x)) with hy
  have hPn : ‖P‖ ≤ K * ‖v‖ :=
    (((pol E a).flip (toL 1)).le_opNorm _).trans (mul_le_mul_of_nonneg_left hn hK0)
  have hWd : DifferentiableAt ℝ (W (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) :=
    ((fieldSm E a U Y C hY W hW x).contDiffAt (ho.mem_nhds ⟨g, rfl⟩)).differentiableAt (by simp)
  have h1 : HasDerivAt (fun r => sand g (sand (c r) (hOne E a))) (sand g v) 0 := by
    have h := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs.clm_apply (hasDerivAt_const (0 : ℝ) (hOne E a)))
    rwa [map_zero, add_zero, hP, pol_one] at h
  have h2 : HasDerivAt (fun r => W (x : GL (Fin a) (Af E) ⧸ U) (sand g (sand (c r) (hOne E a)))) (sand g (P y + Z)) 0 := by
    have h := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs.clm_apply hd)
    simp only [h0, map_one, mul_one, ContinuousLinearMap.one_apply] at h
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have e : infGL E a (g * c r) * finGL E a x = infGL E a g * finGL E a x * infGL E a (c r) := by
      rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
    have e2 := hW (g * c r) x
    rw [e, map_mul] at e2
    exact e2
  have h3 : fderiv ℝ (W (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) (sand g v) = sand g (P y + Z) :=
    (hWd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [h0, map_one]; rfl)).unique h2
  refine ⟨v + t • (P y + Z), ?_, ?_⟩
  · have h4 : ‖P y‖ ≤ K * ‖v‖ * B :=
      (P.le_opNorm y).trans (mul_le_mul hPn hb (norm_nonneg _) (by positivity))
    have h5 : ‖Z‖ ≤ B * ‖v‖ := hZ.trans (mul_le_mul_of_nonneg_left hn hB)
    have h6 : ‖t • (P y + Z)‖ ≤ ‖P y‖ + ‖Z‖ := by
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (norm_add_le _ _)
    have h7 := norm_add_le v (t • (P y + Z))
    nlinarith
  · rw [flow_der hWd, h3, map_add (sand g) v, map_smul]

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_split (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    infGL E a (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) *
        finGL E a (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * (infGL E a g * finGL E a x) := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem centre_zero : splitCentre E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext w
    simp [expU]
  rw [splitCentre, h, map_one, map_one]

private theorem scal_ex (r : ℝ) (hr : 0 < r) : ∃ (t : ℝ) (c : GL (Fin a) (Cinf E)),
    infGL E a c = splitCentre E a t ∧ ∀ p : HV E a, sand c p = r • p := by
  refine ⟨Real.log r / 2, _, rfl, fun p => Subtype.ext ?_⟩
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((Real.log r / 2 : ℝ) : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp (Real.log r / 2) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  have e : Real.exp (Real.log r / 2) * Real.exp (Real.log r / 2) = r := by
    rw [← Real.exp_add, add_halves, Real.exp_log hr]
  change Matrix.of (sand _ p).1 = r • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, e]

private theorem flow_eq {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a}
    {W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a} (hW : FCorr U Y W) (g h : GL (Fin a) (Cinf E))
    (x : GL (Fin a) (Af E)) (t : ℝ) (hh : h.val * star h.val = 1 + t • (Y (infGL E a g * finGL E a x)).1) :
    flow (W (x : GL (Fin a) (Af E) ⧸ U)) t (sand g (hOne E a)) = sand (g * h) (hOne E a) := by
  rw [flow, hW, ← map_smul, ← map_add (f := _), map_mul, ContinuousLinearMap.mul_apply]
  congr 1
  refine Subtype.ext ?_
  change (1 : Matrix (Fin a) (Fin a) (Cinf E)) + t • (Y (infGL E a g * finGL E a x)).1 = h.val * 1 * star h.val
  rw [mul_one, hh]

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.fieldFlow :
    FieldFlow := by
  intro E _ _ _ a ho U Ξ Y C hY W hW
  refine ⟨⟨fun s => ⟨fieldSm E a U Y C hY W hW s, ?_⟩, ?_, ?_⟩, flow_eq hW⟩
  · rintro p ⟨g, rfl⟩ t ht
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨h, hh, -⟩ := hY.root (infGL E a g * finGL E a x) t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩)
    rw [flow_eq hW g h x t hh]
    exact ⟨_, rfl⟩
  · rintro γ s p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ (sand g p) =
        sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1) * g) p := fun p => by
      rw [geo_ρ, map_mul]; rfl
    have hσ : (geo ho U Ξ).σ γ (x : GL (Fin a) (Af E) ⧸ U) =
        ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
    have hl := hY.left γ.1 0 (infGL E a g * finGL E a x)
    rw [centre_zero, mul_one] at hl
    rw [hσ, hs, hW, hW, hs, rat_split, hl]
  · rintro s r hr p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨t, c, hc, hp⟩ := scal_ex (E := E) (a := a) r hr
    have hl := hY.left 1 t (infGL E a g * finGL E a x)
    rw [map_one, one_mul, ← hc, ← mul_assoc, ← map_mul] at hl
    have hs : ∀ p : HV E a, r • sand g p = sand (c * g) p := fun p => by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    rw [hs, hW, hW, hs, hl]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHomPt
section
noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Geo

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

private def tot (W : V → V) (z : V × ℝ) : V := flow W z.2 z.1

private theorem tot_diff {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) :
    DifferentiableAt ℝ (tot W) (x, r) := by
  have h : DifferentiableAt ℝ (fun z : V × ℝ => W z.1) (x, r) :=
    DifferentiableAt.comp (x, r) (g := W) (f := Prod.fst) hW differentiableAt_fst
  exact differentiableAt_fst.add (differentiableAt_snd.smul h)

private theorem tot_smooth {W : V → V} {x : V} (hW : ContDiffAt ℝ ∞ W x) (r : ℝ) :
    ContDiffAt ℝ ∞ (tot W) (x, r) := by
  unfold tot flow
  exact contDiffAt_fst.add (contDiffAt_snd.smul (hW.comp (x, r) contDiffAt_fst))

private theorem tot_inl {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) (v : V) :
    fderiv ℝ (tot W) (x, r) (v, 0) = fderiv ℝ (flow W r) x v := by
  have h1 := (tot_diff hW r).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x r)
  have h2 : flow W r = tot W ∘ fun y => (y, r) := rfl
  rw [h2, h1.fderiv]
  rfl

private theorem tot_inr {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) :
    fderiv ℝ (tot W) (x, r) (0, 1) = W x := by
  have h1 := (tot_diff hW r).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))
  have h2 : HasDerivAt (tot W ∘ fun s => (x, s)) ((1 : ℝ) • W x) r :=
    ((hasDerivAt_id r).smul_const (W x)).const_add x
  simpa using h1.unique h2

private theorem pb_tot {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) {q : ℕ}
    (w : V → V [⋀^Fin q]→L[ℝ] F) :
    (pb (tot W) w (x, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) = pb (flow W r) w x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, pb_apply, Function.comp_apply,
    ContinuousLinearMap.inl_apply, tot_inl hW]
  rfl

private theorem hk_tot {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) {q : ℕ}
    (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) :
    ((pb (tot W) w (x, r)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) = hk W r w x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    pb_apply, hk_apply]
  congr 1
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [tot_inr hW]
  · simp [tot_inl hW]

end

theorem homPt : HomPt := by
  intro V F _ _ _ _ _ _ W p t hW
  have hd : DifferentiableAt ℝ W p := hW.differentiableAt (by simp)
  have hfl : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), (fun r => pb (flow W r) w p) =
      fun r => (pb (tot W) w (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) :=
    fun q w => funext fun r => (pb_tot hd r w).symm
  have key : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), ContDiffAt ℝ ∞ w (flow W t p) →
      DifferentiableAt ℝ (pb (tot W) w) (p, t) ∧
        extDeriv (pb (tot W) w) (p, t) = pb (tot W) (extDeriv w) (p, t) := by
    intro q w hw
    obtain ⟨h1, h2⟩ := pbD (V × ℝ) V F q (tot W) w (p, t) (tot_smooth hW t) hw
    exact ⟨h1.differentiableAt (by simp), h2⟩
  refine ⟨fun w hw => ?_, fun q w hw => ?_⟩
  · obtain ⟨hD, hE⟩ := key 0 w hw
    rw [hfl, ← hk_tot hd t (extDeriv w), ← hE]
    exact (prodDer V F p t).1 _ hD
  · obtain ⟨hD, hE⟩ := key (q + 1) w hw
    have hev : (fun y => ((pb (tot W) w (y, t)).curryLeft (0, 1)).compContinuousLinearMap
        (ContinuousLinearMap.inl ℝ V ℝ)) =ᶠ[𝓝 p] hk W t w := by
      have h1 : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ 1 W y := (hW.of_le (by simp)).eventually (by simp)
      filter_upwards [h1] with y hy
      exact hk_tot (hy.differentiableAt (by simp)) t w
    rw [hfl, ← hk_tot hd t (extDeriv w), ← hE, ← hev.extDeriv_eq]
    exact (prodDer V F p t).2 q _ hD

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevGood
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem one_kills {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v}) : smLie Ξ (oneL E a) m = 0 := by
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  have hr' : Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := hr
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    change (lie E a (oneL E a)).rTensor _ (φ ⊗ₜ[ℂ] v) + (Matrix.toLin' (Ξ.dmat (oneL E a))).lTensor _ (φ ⊗ₜ[ℂ] v) = 0
    rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hφ.2.2 _ hr', hr', map_smul, Matrix.toLin'_one,
      LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.smul_tmul, ← TensorProduct.tmul_add, neg_smul, neg_add_cancel,
      TensorProduct.tmul_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private theorem d_basic {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} (α : Co Ξ q) (hα : IsLev U Ξ α)
    (X : Fin (q + 1) → Herm E a) (i : Fin (q + 1)) (hX : (X i).1 = 1) : dCo (smLie Ξ) α X = 0 := by
  rw [dCo_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i = j
  · subst hj
    have h := one_kills U Ξ _ (hα.val (i.removeNth X))
    have e : oneL E a = toL (X i).1 := by rw [hX]
    rw [e] at h
    rw [h, smul_zero]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    have hz : α (j.removeNth X) = 0 := hα.basic _ k (by rw [← hX, ← hk]; rfl)
    rw [hz, map_zero, smul_zero]

theorem UpperTheory.V.Lit.Geo.levGood :
    LevGood := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α hα => ?_, fun w hw => ?_⟩
  · have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, h0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, h0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    exact ⟨w', hw', (corrInv E a ho U Ξ q _ _ hw').1 fun X => (hv X).1, (corrBasic E a U Ξ q _ _ hw').1 hα.basic,
      (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hw')).1 (d_basic U Ξ α hα)⟩
  · obtain ⟨α, hα⟩ := corrBwd E a ho U Ξ q w
    have b := (corrBasic E a U Ξ q _ _ hα).2 hw.basic
    have b' := (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hα)).2 hw.dbasic
    obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hα
    exact ⟨α, hα, c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hα).2 hw.inv X) (c2 X)
      (centralOf E a _ (smLie Ξ) q α b b' X)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbNat
section
open UpperTheory.V.Lit.Geo
open scoped ContDiff

private theorem pbNat_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Set V} (hY : IsOpen Y)
    (ρ : V →L[ℝ] V) {W W' : V → V} (hW : IsField Y W) (hW' : IsField Y W') (hρ : ∀ p ∈ Y, ρ p ∈ Y)
    (he : ∀ p ∈ Y, W' (ρ p) = ρ (W p)) (t : ℝ) {p : V} (hp : p ∈ Y) :
    flow W' t (ρ p) = ρ (flow W t p) ∧ ∀ v, fderiv ℝ (flow W' t) (ρ p) (ρ v) = ρ (fderiv ℝ (flow W t) p v) := by
  have hd : ∀ (U : V → V) (x : V), DifferentiableAt ℝ U x → ∀ v : V,
      fderiv ℝ (flow U t) x v = v + t • fderiv ℝ U x v := by
    intro U x hU v
    have h := (hasFDerivAt_id x).add (hU.hasFDerivAt.const_smul t)
    have hfl : flow U t = id + t • U := by
      funext y
      simp [flow]
    rw [hfl, h.fderiv]
    simp
  constructor
  · simp only [flow]
    rw [he p hp]
    simp [map_add (f := _), map_smul]
  · intro v
    have hWd : DifferentiableAt ℝ W p :=
      (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
    have hW'd : DifferentiableAt ℝ W' (ρ p) :=
      (hW'.1.contDiffAt (hY.mem_nhds (hρ p hp))).differentiableAt (by simp)
    have heq : (fun x => W' (ρ x)) =ᶠ[nhds p] (fun x => ρ (W x)) := by
      filter_upwards [hY.mem_nhds hp] with x hx using he x hx
    have hder : fderiv ℝ W' (ρ p) (ρ v) = ρ (fderiv ℝ W p v) := by
      have h1 := heq.fderiv_eq (𝕜 := ℝ)
      have c1 : fderiv ℝ (fun x => W' (ρ x)) p = (fderiv ℝ W' (ρ p)).comp ρ :=
        (hW'd.hasFDerivAt.comp p ρ.hasFDerivAt).fderiv
      have c2 : fderiv ℝ (fun x => ρ (W x)) p = ρ.comp (fderiv ℝ W p) :=
        (ρ.hasFDerivAt.comp p hWd.hasFDerivAt).fderiv
      have h3 := congrArg (fun L => L v) (c1.symm.trans (h1.trans c2))
      simpa using h3
    rw [hd W' (ρ p) hW'd, hd W p hWd, hder]
    simp [map_add (f := _), map_smul]

theorem UpperTheory.V.Lit.Geo.pbNat :
    PbNat := by
  unfold PbNat
  intro V F _ _ _ _ _ _ Y hY ρ A W W' hW hW' hρ he q
  constructor
  · intro w w' hww t ht p hp v
    obtain ⟨h1, h2⟩ := pbNat_flow hY ρ hW hW' hρ he t hp
    rw [pb_apply, pb_apply, h1]
    simp only [h2]
    exact hww _ (hW.2 p hp t ht) _
  · intro w w' hww
    have hb1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Y, ∀ v : Fin q → V,
        (hk W' t w' (ρ p)) (fun i => ρ (v i)) = A ((hk W t w p) v) := by
      intro t ht p hp v
      obtain ⟨h1, h2⟩ := pbNat_flow hY ρ hW hW' hρ he t hp
      rw [hk_apply, hk_apply, h1, he p hp]
      simp only [h2]
      convert hww (flow W t p) (hW.2 p hp t ht)
        (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) using 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    refine ⟨hb1, fun hwc hw'c p hp v => ?_⟩
    have hk1 := (hkSmooth V F Y hY W hW q w hwc).2.2.1 p hp
    have hk2 := (hkSmooth V F Y hY W' hW' q w' hw'c).2.2.1 (ρ p) (hρ p hp)
    have i1 : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hk1
    have i2 : IntervalIntegrable (fun t => hk W' t w' (ρ p)) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hk2
    have i3 : IntervalIntegrable (fun t => (hk W t w p) v) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (ContinuousAlternatingMap.apply ℝ V F v).continuous.comp_continuousOn hk1
    have e1 : (∫ t in (0 : ℝ)..1, hk W' t w' (ρ p)) (fun i => ρ (v i)) =
        ∫ t in (0 : ℝ)..1, (hk W' t w' (ρ p)) (fun i => ρ (v i)) :=
      ((ContinuousAlternatingMap.apply ℝ V F (fun i => ρ (v i))).intervalIntegral_comp_comm i2).symm
    have e2 : (∫ t in (0 : ℝ)..1, hk W t w p) v = ∫ t in (0 : ℝ)..1, (hk W t w p) v :=
      ((ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm i1).symm
    unfold hom
    rw [e1, e2, ← A.intervalIntegral_comp_comm i3]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hb1 t ht p hp v
end

