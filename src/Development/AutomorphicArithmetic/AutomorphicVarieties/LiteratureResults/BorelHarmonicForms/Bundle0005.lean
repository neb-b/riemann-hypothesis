module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LevelOp
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem op_comm {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (k : GL (Fin a) (Af E)) (o : Op E a) (ho : ∀ k', o ≠ .fin k') : Commute (π.op o) (π.finPart k) := by
  have h : act o * act (.fin k) = act (.fin k) * act o := by
    cases o with
    | fin k' => exact (ho k' rfl).elim
    | cpt u =>
      change rt E a _ * rt E a _ = rt E a _ * rt E a _
      rw [← map_mul, ← map_mul]
      exact congrArg _ (infGL_comm _ _)
    | lie X => exact lie_rt_fin X k
  exact LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h x.1)

theorem UpperTheory.V.Lit.Bor.levelOp :
    UpperTheory.V.Lit.Bor.LevelOp := by
  intro E _ _ _ a U hU π hF φ hφ
  obtain ⟨p, hp1, hp2, hp3⟩ := UpperTheory.V.Lit.Bor.avgProj _ _ π.finPart U hU π.isSmooth_finPart
  have hc : ∀ (o : Op E a), (∀ k', o ≠ .fin k') → ∀ g, Commute (p * π.finPart g) (π.op o) := fun o ho g =>
    ((hp3 _ fun u _ => op_comm π u o ho).mul_right (op_comm π g o ho)).symm
  by_contra hne
  have hφ0 : ∀ g, (p * π.finPart g) φ = 0 := fun g => by
    by_contra h
    exact hne ⟨p * π.finPart g, h, fun k => hc _ (fun _ h => by cases h) g, fun ψ u hu => hp1 _ u hu⟩
  set N : Submodule ℂ π.V := ⨅ g, LinearMap.ker (p * π.finPart g) with hN
  have hm : ∀ x, x ∈ N ↔ ∀ g, (p * π.finPart g) x = 0 := fun x => by simp only [hN, Submodule.mem_iInf, LinearMap.mem_ker]
  have hs : ∀ o, ∀ x ∈ N, π.op o x ∈ N := fun o x hx => by
    rw [hm] at hx ⊢
    intro g
    by_cases ho : ∀ k', o ≠ .fin k'
    · have := LinearMap.congr_fun (hc o ho g).eq x
      rw [Module.End.mul_apply, Module.End.mul_apply (π.op o), hx g, map_zero] at this
      exact this
    · push Not at ho
      obtain ⟨k, rfl⟩ := ho
      have := hx (g * k)
      rw [map_mul] at this
      exact this
  rcases π.irred (N.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hs o x hx, rfl⟩) with e | e
  · have : φ.1 ∈ N.map π.V.subtype := ⟨φ, (hm φ).2 hφ0, rfl⟩
    rw [e, Submodule.mem_bot] at this
    exact hφ (Subtype.ext this)
  · obtain ⟨v, hv0, hv⟩ := hF
    have : v.1 ∈ N.map π.V.subtype := by rw [e]; exact v.2
    obtain ⟨w, hw, hwv⟩ := this
    obtain rfl : w = v := Subtype.ext hwv
    have h1 := (hm w).1 hw 1
    rw [map_one, mul_one, hp2 w hv] at h1
    exact hv0 h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem continuous_lie_of_level {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) : Continuous (lie E a X φ).1 := by
  refine ContAut.continuous_of_isOpen_stab E a _ ?_
  let S : Sm E a → Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) := fun θ =>
    { carrier := {k | finRep E a k θ = θ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => by
    have e : lie E a X (finRep E a k φ) = finRep E a k (lie E a X φ) :=
      LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : finRep E a k φ = φ := hk
    change finRep E a k (lie E a X φ) = lie E a X φ
    rw [← e, hk']
  exact Subgroup.isOpen_mono hle h

open scoped GlobalTheory.CuspRep.CuspidalL2GL in
theorem UpperTheory.V.Lit.Bor.skew_lie_action_L2 :
    UpperTheory.V.Lit.Bor.SkewLieActionL2 := by
  intro E _ _ _ a μ _ X φ ψ hφ hψ h1 h2 h3 h4
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨c, c0, cadd, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have g0 : infGL E a (c 0) = 1 := by rw [c0, map_one]
  have key : ∀ (θ : Sm E a), IsOpen {k | act (.fin k) θ = θ} →
      ∀ (p : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ θ.1)
        (q : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X θ).1),
      HasDerivAt (fun s => GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) p.toL2) q.toL2 0 :=
    fun θ hθ p q => UpperTheory.V.Lit.Bor.derivative_right_translate_L2 (GA E a) _ μ θ.1 _ p q (fun s => infGL E a (c s))
      (continuous_lie_of_level X θ hθ) ccont g0 (fun s t => by rw [cadd, map_mul])
      (fun g => hasDerivAt_curve θ g c X c0 cder)
  have d := (key φ hφ h1 h3).inner ℂ (key ψ hψ h2 h4)
  have hc : (fun s : ℝ => inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) h1.toL2)
      (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s)) h2.toL2)) = fun _ => inner ℂ h1.toL2 h2.toL2 :=
    funext fun s => (LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (GlobalTheory.UnitaryBC.latticeGL E a) μ (infGL E a (c s))).toLinearMap
      (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _
  rw [hc] at d
  have h := d.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [g0, map_one, ContinuousLinearMap.one_apply] at h
  exact (add_comm _ _).trans h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SmForm
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.smForm :
    UpperTheory.V.Lit.Bor.SmForm := by
  intro E _ _ _ a Ξ r H G hH hG X x hx y hy
  set c : ℂ := ((2 * r * ell E a (toL X.1) : ℝ) : ℂ) with hc
  have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
  obtain ⟨h1, h2⟩ := UpperTheory.V.Lit.Bor.tformAdj (Sm E a) Ξ.d H (sqSub E a r) G (Ξ.dmat (toL X.1)) (Ξ.dmat (toL X.1))
    (lie E a (toL X.1)) (-lie E a (toL X.1) - c • 1)
  have hX : star X.1 = X.1 := X.2
  have e1 := h1 (by have := hG.adj X.1; rwa [hX] at this) x y
  have e2 := h2 (fun φ hφ ψ hψ => by
    have := hH.skew (toL X.1) φ hφ ψ hψ
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg,
      LinearMap.map_smulₛₗ, hcc, smul_eq_mul]
    rw [← hc] at this
    linear_combination this) x hx y hy
  have e3 : smLie Ξ (toL X.1) y = smA Ξ (toL X.1) y + smB Ξ (toL X.1) y := by
    simp [smB]
  have e4 : smAdj Ξ r (toL X.1) x = smB Ξ (toL X.1) x +
      (-lie E a (toL X.1) - c • (1 : Module.End ℂ (Sm E a))).rTensor _ x := by
    rw [smAdj, adj_apply, smA_apply, LinearMap.rTensor_sub, LinearMap.rTensor_neg, LinearMap.rTensor_smul,
      Module.End.one_eq_id, LinearMap.rTensor_id, ← algebraMap_smul ℂ (2 * r * ell E a (toL X.1)) x]
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [show algebraMap ℝ ℂ (2 * r * ell E a (toL X.1)) = c from rfl]
    abel
  rw [e3, e4, map_add (f := _), map_add (f := _), LinearMap.add_apply, smA_apply, smB_apply, e1, e2, add_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SqUniq
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct
open Formalism.L2.Host GlobalTheory.UnitaryBC

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chi_split {χ : HChar E} {s : ℝ} (h : χ.IsAbsPow s) :
    ((chiDet a χ (splitCentre E a 1) : ℂˣ) : ℂ) = ((Real.exp ((a : ℝ) * s * Fintype.card (E →+* ℂ)) : ℝ) : ℂ) := by
  have e : chiDet a χ (splitCentre E a 1) = chiInf χ (GeneralLinearGroup.det
      (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ)))) :=
    congrArg χ.1 (det_infGL _)
  rw [e, GlobalTheory.CuspRep.InfType.chiInf_eq χ (fun σ => σ) (fun _ z => ((‖z‖ : ℝ) : ℂ) ^ (s : ℂ)) (fun σ z hz =>
    ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousAt continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz))) h.2.2]
  have d : ((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ))) : (Cinf E)ˣ) : Cinf E) =
      ((expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E) ^ a := by
    simp [Matrix.det_diagonal]
  have c : ∀ σ : E →+* ℂ, ‖coord σ (((expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E) ^ a)‖ =
      Real.exp a := fun σ => by
    have c1 : coord σ (fun _ : InfinitePlace E => ((1 : ℝ) : ℂ)) = 1 := map_one (coord σ)
    rw [map_pow, norm_pow, GlobalTheory.CuspRep.InfType.coord_expU, c1, Complex.norm_exp, Complex.one_re, Real.exp_one_pow]
  simp only [d, c]
  rw [← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul, Finset.prod_const, Finset.card_univ,
    ← Complex.ofReal_pow, ← Real.exp_nat_mul, mul_comm]

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem absPow_uniq {χ χ' : HChar E} {s : ℝ} (h : χ.IsAbsPow s) (h' : χ'.IsAbsPow s) : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine GlobalTheory.DiscSpec.Model.eq_one_of_isAbsPow ⟨fun v x hx => ?_, fun v => ?_, fun k => ?_⟩
  · have loc_mul (a b : HChar E) : (a * b).loc v x = a.loc v x * b.loc v x := rfl
    have loc_inv (a : HChar E) : (a⁻¹).loc v x = (a.loc v x)⁻¹ := rfl
    rw [loc_mul, loc_inv, h.1 v x hx, h'.1 v x hx, inv_one, mul_one]
  · have : χ.val v = χ'.val v := Units.ext ((h.2.1 v).trans (h'.2.1 v).symm)
    rw [HChar.val_mul, HChar.val_inv, this, mul_inv_cancel]; simp
  · have : χ.inf k = χ'.inf k := Units.ext ((h.2.2 k).trans (h'.2.2 k).symm)
    rw [HChar.inf_mul, HChar.inf_inv, this, mul_inv_cancel]; simp

end

theorem UpperTheory.V.Lit.Bor.sqUniq :
    UpperTheory.V.Lit.Bor.SqUniq := by
  rintro E _ _ _ a ha r χ ⟨⟨s, hs⟩, htw⟩ φ hφ ⟨s', χ', hs', hsq⟩
  have hfun : ∀ ν : HChar E, (mulChi a ν φ).1 = fun g => ((chiDet a ν g : ℂˣ) : ℂ) * φ.1 g := fun ν =>
    funext fun g => by rw [mulChi_apply, mul_comm]
  by_cases h0 : ∀ g, φ.1 g = 0
  · rw [hfun]
    simpa only [h0, mul_zero] using hsq
  obtain ⟨g, hg⟩ := not_forall.1 h0
  have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
    rw [htw, hφ, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
  have h1 := aInv E a _ _ hz 1 g
  have h2 := hsq.1 1 g
  have h3 := aInv E a _ _ hφ 1 g
  simp only [hfun, zero_mul, Complex.exp_zero, one_mul, map_mul, Units.val_mul, h3] at h1 h2
  have key : ∀ x y : ℂ, y ≠ 0 → x * y * (Complex.exp (-(r : ℂ) * (1 : ℝ)) * φ.1 g) = y * φ.1 g →
      x = (Complex.exp (-(r : ℂ) * (1 : ℝ)))⁻¹ := fun x y hy h =>
    eq_inv_of_mul_eq_one_left (mul_right_cancel₀ (mul_ne_zero hy hg) (by linear_combination h))
  have h4 := (key _ _ (Units.ne_zero _) h1).trans (key _ _ (Units.ne_zero _) h2).symm
  rw [chi_split hs, chi_split hs', Complex.ofReal_inj, Real.exp_eq_exp] at h4
  have hc : (Fintype.card (E →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain rfl : s = s' := mul_left_cancel₀ ha' (mul_right_cancel₀ hc h4)
  rw [hfun, absPow_uniq hs hs']
  exact hsq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem sum_coord_re {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : Cinf E) :
    ∑ τ : E →+* ℂ, coord τ z = ((2 * ∑ w : InfinitePlace E, (z w).re : ℝ) : ℂ) := by
  have h := congrArg Multiplicative.toAdd
    (GlobalTheory.GKCoh.Tests.prod_coord (M := Multiplicative ℂ) Multiplicative.ofAdd z)
  simp only [toAdd_prod, toAdd_mul, toAdd_ofAdd, Complex.add_conj] at h
  rw [h, Finset.mul_sum, Complex.ofReal_sum]

theorem UpperTheory.V.Lit.Bor.twEx :
    UpperTheory.V.Lit.Bor.TwEx := by
  intro E _ _ _ a _ r
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (r / (2 * ((a : ℝ) * Fintype.card (InfinitePlace E))))
  refine ⟨_, ⟨_, hν⟩, fun X φ => ?_⟩
  rw [lie_mulChi, GlobalTheory.CuspRep.AlgExpo.dchi_eq_sum]
  simp only [(GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 _ hν, ← Finset.mul_sum]
  rw [sum_coord_re, ← Complex.ofReal_mul]
  have e : ell E a X = (∑ w : InfinitePlace E, ((Matrix.of X).trace w).re) /
      ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp [ell, Matrix.trace]
  rw [e]
  congr 4
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.XiSchur
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.xiSchur :
    UpperTheory.V.Lit.Bor.XiSchur := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => GlobalTheory.AlgInfChar.dmat_bracket Ξ X Y, fun P hP => ?_⟩
  rcases subsingleton_or_nontrivial (Fin Ξ.d → ℂ) with h | h
  · exact ⟨0, Matrix.ext fun i => congrFun (Subsingleton.elim (α := Fin Ξ.d → ℂ) _ _)⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ))
  have hs : Stab (eEnd Ξ) (Module.End.eigenspace (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ)) c) := by
    intro τ i j w hw
    have hcm : Commute P (eL Ξ.dmat τ i j) := ((hP _).sub_right ((hP _).smul_right _)).smul_right _
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
    rw [eEnd, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcm.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have ht := ((algIrr E a Ξ).2 _ hs).resolve_left hc
  refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have hv : v ∈ Module.End.eigenspace (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ)) c := by
    rw [ht]; trivial
  rw [Module.End.mem_eigenspace_iff.1 hv, map_smul, Matrix.toLin'_one]
  rfl
end

