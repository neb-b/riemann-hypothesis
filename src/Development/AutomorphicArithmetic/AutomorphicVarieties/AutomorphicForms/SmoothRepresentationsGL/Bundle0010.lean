module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.OneScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0007
public import GroundTheory.GlobalFields.CompletionAtPlace.Inertia

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CenSame
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem infGL_scalar {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (u : (Rinf E)ˣ) :
    infGL E n (GeneralLinearGroup.scalar (Fin n) u) = GeneralLinearGroup.scalar (Fin n) (TR.infId E u) := by
  have h1 : pInf E (TR.infId E u).val = u.val := by
    change pInf E (1 - sInf E 1 + sInf E _) = _
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (TR.infEq E).symm_apply_apply x
    simp [h]
  have h2 : pFin E (TR.infId E u).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem deriv_centre {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (φ : TR.Sm E n)
    (g : GA E n) :
    HasDerivAt (fun t : ℝ => φ.1 (g * GeneralLinearGroup.scalar (Fin n) (TR.infId E (TR.expU (t • (1 : Rinf E))))))
      ((TR.lie E n (oneL E n) φ).1 g) 0 := by
  have h := TR.hasDerivAt_curve φ g (fun t : ℝ => GeneralLinearGroup.scalar (Fin n) (TR.expU (t • (1 : Rinf E))))
    (oneL E n) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        simpa using Real.hasDerivAt_exp 0
      · simpa [Matrix.diagonal_apply, Matrix.one_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simp only [infGL_scalar] at h
  exact h

theorem UpperTheory.V.Af.Smo.cenSame :
    UpperTheory.V.Af.Smo.CentEq → UpperTheory.V.Af.Smo.SetUp → UpperTheory.V.Af.Smo.EigOfSat → UpperTheory.V.Af.Smo.CenSame := by
  intro hC hS hE E _ _ _ n π π' hs hc φ' hφ'
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨S, B, hB, hk, hk'⟩ := hS E n π π' hs φ hφ φ' hφ'
  have key : ∀ ψ : TR.Sm E n, TR.IsCuspForm ψ → Continuous ψ.1 ∧ IsLeftInvariant ψ.1 := fun ψ hψ => by
    refine ⟨?_, hψ.1.left⟩
    have hp : Continuous (pInf E) := by
      have hc : Continuous (TR.infEq E).symm :=
        continuous_pi fun w =>
          (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
      exact hc.comp continuous_fst
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hm : Continuous fun x : GA E n => g⁻¹ * x := continuous_const.mul continuous_id
    have hI : Continuous (Matrix.GeneralLinearGroup.map (pInf E) : GA E n → GL (Fin n) (Rinf E)) :=
      Continuous.units_map _ (continuous_id.matrix_map hp)
    have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin E) : GA E n → GL (Fin n) (Af E)) :=
      Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
    have h1 : Continuous fun x : GA E n => toL (Matrix.GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val :=
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Rinf E))).comp (hI.comp hm)
    have h2 : ContinuousAt (fun x : GA E n => chart ψ.1 g (toL (Matrix.GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)) g :=
      ContinuousAt.comp (f := fun x : GA E n => toL (Matrix.GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)
        (TR.contDiffAt_chart ψ.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
    refine h2.congr ?_
    have h3 : {x : GA E n | TR.finRep E n (Matrix.GeneralLinearGroup.map (pFin E) (g⁻¹ * x)) ψ = ψ} ∈ 𝓝 g :=
      (hψ.1.level.preimage (hFn.comp hm)).mem_nhds (by simp)
    filter_upwards [h3] with x hx
    rw [TR.chart_val]
    conv_lhs => rw [← hx]
    change ψ.1 (g * infGL E n _ * finGL E n _) = _
    rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]
  have loc : ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), InKS S (locGL E n w k) := by
    intro w hw k hkk
    refine ⟨fun x hx => GlobalTheory.CuspRep.pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _, fun x => ?_⟩
    by_cases e : x = w
    · subst e
      rw [GlobalTheory.CuspRep.pLoc_locGL]
      exact hkk
    · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne e]
      exact one_mem _
  have e := hC E n S B φ.1 φ'.1 (key _ (π.cusp _ hφ)).1 (key _ (π'.cusp _ hφ')).1 (key _ (π.cusp _ hφ)).2
    (key _ (π'.cusp _ hφ')).2 (fun w hw => ⟨hE E n π w _ (hB w hw).2.1 φ hφ fun g k h => hk g _ (loc w hw k h),
      hE E n π' w _ (hB w hw).2.2 φ' hφ' fun g k h => hk' g _ (loc w hw k h)⟩) hk hk'
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  refine Subtype.ext (funext fun g' => ?_)
  have d1 := (deriv_centre φ g).mul_const (φ'.1 g')
  have d2 := (deriv_centre φ' g').const_mul (φ.1 g)
  simp only [e _ g g'] at d1
  have d := d1.unique d2
  rw [hc φ hφ] at d
  exact (mul_eq_zero.1 (d.symm.trans (zero_mul _))).resolve_left hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.MemIffLocal
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem lamS_perm {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), Spherical.lamS T ∘ σ = Spherical.lamS S := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ T} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, funext fun i => ?_⟩
  by_cases hi : i ∈ S
  · have := Equiv.extendSubtype_mem e i hi
    simp [Spherical.lamS, hi, this]
  · have := Equiv.extendSubtype_not_mem e i hi
    simp [Spherical.lamS, hi, this]

private theorem mem_iff_local {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F) :
    g ∈ Spherical.minusculeSet F n r ↔ ∃ a ∈ GLnLocal.integralGL F n, ∃ b ∈ GLnLocal.integralGL F n,
      (g : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) *
        Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r * (b : Matrix (Fin n) (Fin n) F) := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
  have hT : T.card = r := by
    simp [T, Fin.card_filter_val_lt, hr]
  have hD : ((Iwasawa.torusPow F n (Spherical.lamS T) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r := by
    rw [Iwasawa.coe_torusPow, Formalism.UG.diagJ]
    congr 1
    funext i
    by_cases hi : i.val < r <;> simp [Spherical.lamS, T, hi]
  have hU : ∀ (S : Finset (Fin n)) c, Spherical.unipC (F := F) S c ∈ GLnLocal.integralGL F n := by
    intro S c
    have := (Spherical.torusPow_conj_unipC_mem (l := 0) antitone_const S c).2
    have h0 : Iwasawa.torusPow F n 0 = 1 := Units.ext (by simp [Iwasawa.coe_torusPow])
    simpa [h0] using this
  rw [← hD]
  constructor
  · intro hg
    obtain ⟨S, hS, c, hc⟩ := Spherical.exists_gMat hg
    have hk := QuotientGroup.eq.1 hc
    obtain ⟨σ, hσ⟩ := lamS_perm S T (hS.trans hT.symm)
    have hp := GLnLocal.permGL_mem_integralGL F n σ
    refine ⟨_, mul_mem (hU S c) (inv_mem hp), _, mul_mem hp hk, ?_⟩
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    have h1 := Spherical.permGL_conj_torusPow (F := F) σ (Spherical.lamS T)
    rw [hσ] at h1
    rw [Spherical.gMat, ← h1]
    group
  · rintro ⟨a, ha, b, hb, e⟩
    rw [← Units.val_mul, ← Units.val_mul] at e
    have e' := Units.ext e
    have h0 := Spherical.gMat_mem_minusculeSet (F := F) T (fun _ => 0)
    rw [hT] at h0
    have := Spherical.mul_mem_minusculeSet h0 (mul_mem ha (inv_mem (hU T fun _ => 0))) hb
    rw [e']
    convert this using 1
    rw [Spherical.gMat]
    group

theorem UpperTheory.V.Af.Smo.tjSet :
    UpperTheory.V.Af.Smo.SphDict → UpperTheory.V.Af.Smo.TjSet := by
  intro hd E _ _ n w r hr
  have hK : GLnLocal.integralGL (w.adicCompletion E) n = Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) :=
    (hd E n w).1
  unfold Formalism.UG.Tj
  rw [← hK]
  congr 1
  ext g
  exact (mem_iff_local hr g).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem sqrt_pow (q r n : ℕ) (hq : q ≠ 0) (h : r ≤ n) :
    (((NNReal.sqrt (q : NNReal) : NNReal) : ℝ) : ℂ) ^ (r * (n - r)) =
      (q : ℂ) ^ (((r : ℂ) * ((n : ℂ) - r)) / 2) := by
  have e : ((r : ℂ) * ((n : ℂ) - r)) / 2 = (1 / 2 : ℂ) * ((r * (n - r) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub h]; ring
  rw [e, Complex.cpow_mul_nat]
  congr 1
  rw [Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  simp

theorem UpperTheory.V.Af.Smo.sphDict :
    UpperTheory.V.Af.Smo.SphDict := by
  intro E _ _ n w
  refine ⟨?_, ?_, fun r hr => ?_, fun u hu => ⟨fun i _ => ⟨hu.2 i, fun j hj => hu.1 hj⟩, fun ψ => ?_⟩⟩
  · have hO : Formalism.UG.Ov E w = (ValuativeRel.valuation (w.adicCompletion E)).integer :=
      Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm
    change _ = Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w)
    rw [hO]
    rfl
  · exact GroundTheory.Global.valued_of_irreducible_integer w (GLnLocal.irreducible_uniformizer _)
  · have hq : Spherical.qF (w.adicCompletion E) = Formalism.UG.qV E w := by
      unfold Spherical.qF Formalism.UG.qV
      rw [GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    unfold Spherical.sqrtQ
    rw [hq]
    exact sqrt_pow _ r n (by
      unfold Formalism.UG.qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot) hr
  · simp only [Whittaker.psiN, Whittaker.superdiagSum, supN, eq_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section General

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra
open scoped ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem esymm_eq (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) = ((Finset.univ.val.map z).map fun b : ℂˣ => (b : ℂ)).esymm r := by
  rw [evalAt_esymmL, Multiset.map_map, Finset.esymm_map_val]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomialChar_apply]
  simp only [lamS, Function.comp_apply]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [hi]

private theorem lamS_univ : lamS (Finset.univ : Finset (Fin n)) = fun _ => 1 := by
  funext i
  simp [lamS]

private theorem gMat_univ (c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) :
    gMat Finset.univ c = torusPow F n (fun _ => 1) := by
  have h : unipC (F := F) Finset.univ c = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_unipC, Matrix.add_apply, cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), add_zero]
    rfl
  rw [gMat, h, one_mul, lamS_univ]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

private theorem central_of_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : minusculeHecke μ n ∈ eigenSubalgebra μ z f hf) : centralHecke μ ∈ eigenSubalgebra μ z f hf := by
  classical
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have h1 : ∀ g, f (g * torusPow F n (fun _ => 1)) = monomialChar (fun _ : Fin n => 1) z * f g := by
    intro g
    have h := hT g
    haveI : IsEmpty (Pairs (Finset.univ : Finset (Fin n))) := ⟨fun p => p.2.2.1 (Finset.mem_univ _)⟩
    have hc (I : Fintype (Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F])) :
        (@Finset.univ _ I).card = 1 :=
      @Fintype.card_unique _ inferInstance I
    rw [integral_minusculeHecke_mul hf, evalAt_satakeTransform_minusculeHecke z le_rfl, evalAt_esymmL, hp,
      Finset.sum_singleton, Finset.sum_singleton, Finset.sum_congr rfl (fun c _ => by rw [gMat_univ c]),
      Finset.sum_const, hc, one_smul, lamS_univ, Nat.sub_self, mul_zero,
      pow_zero, mul_one, mul_assoc] at h
    exact mul_left_cancel₀ hK h
  have h2 : ∀ g, f (g * torusPow F n (fun _ => -1)) = monomialChar (fun _ : Fin n => -1) z * f g := by
    intro g
    have h := h1 (g * torusPow F n (fun _ => -1))
    have e : (fun _ : Fin n => (-1 : ℤ)) + (fun _ => 1) = 0 := by funext i; simp
    have e' : torusPow F n (fun _ => -1) * torusPow F n (fun _ => 1) = 1 := by
      have : (fun _ : Fin n => (-1 : ℤ)) = -(fun _ => 1) := rfl
      rw [this, torusPow_neg, inv_mul_cancel]
    rw [mul_assoc, e', mul_one] at h
    rw [h, ← mul_assoc, ← monomialChar_add, e, monomialChar_zero, one_mul]
  intro g
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * f (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) *
      f (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => f (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    have hiff : g₀ * y ∈ centralSet F n ↔ y ∈ (integralGL F n : Set (GL (Fin n) F)) := by
      rw [mem_centralSet, inv_mul_cancel_left]
      rfl
    by_cases hy : y ∈ (integralGL F n : Set (GL (Fin n) F))
    · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy, one_mul, ← mul_assoc, hf _ _ hy]
    · rw [Set.indicator_of_notMem (mt hiff.1 hy), Set.indicator_of_notMem hy, zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, h2, satakeTransform_centralHecke, map_smul,
    Spherical.monomial, evalAt_single, one_mul, smul_eq_mul]
  ring

private theorem minuscule_mem (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {r : ℕ} (hr : r ≤ n)
    (h : ∀ g, ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out * f (g * c.out) =
        sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f g) :
    minusculeHecke μ r ∈ eigenSubalgebra μ z f hf := by
  intro g
  have hcs : HasCompactSupport fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs (fun x k hk => by
      rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk]),
    Complex.real_smul, evalAt_satakeTransform_minusculeHecke z hr, mul_assoc, mul_assoc, ← mul_assoc (sqrtQ F ^ _), ← h g]
  rfl

end General

theorem UpperTheory.V.Af.Smo.sphZero :
    UpperTheory.V.Af.Smo.SphDict → UpperTheory.V.Af.Smo.TjSet → UpperTheory.V.Af.Smo.CentLoc → UpperTheory.V.Af.Smo.SphZero := by
  intro hD hTj _ E _ _ n w ψ hψ B W hW hE h1
  obtain ⟨hK, hu, hq, hN⟩ := hD E n w
  obtain ⟨z, rfl⟩ : ∃ z : Fin n → ℂˣ, Finset.univ.val.map z = B := by
    obtain ⟨l, rfl⟩ := Quotient.exists_rep B
    have hl : l.length = n := hE.card
    subst hl
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  borelize (GL (Fin n) (w.adicCompletion E))
  let μ : Measure (GL (Fin n) (w.adicCompletion E)) := Measure.haar
  have hf : ∀ g, ∀ k ∈ GLnLocal.integralGL (w.adicCompletion E) n, W (g * k) = W g := by
    rw [hK]
    exact hE.inv
  have hT : ∀ r ≤ n, Spherical.minusculeHecke μ r ∈ Spherical.eigenSubalgebra μ z W hf := by
    intro r hr
    refine minuscule_mem z hf hr fun g => ?_
    rw [hK, ← hTj E n w r hr, hE.eig _ hu r hr g, hq r hr, esymm_eq, GlobalTheory.LFun.satEig]
  have htop := Spherical.eigenSubalgebra_eq_top z hf hT (central_of_top z hf (hT n le_rfl))
  funext g
  have := Spherical.eq_smul_sphericalWhittaker (μ := μ) (ψ₀ := ψ)
    (fun x hx => hψ.1 x ((GroundTheory.Global.mem_valuationInteger_iff w x).1 hx))
    (by
      obtain ⟨x, hx, hx'⟩ := hψ.2 _ hu
      exact ⟨x, (GroundTheory.Global.mem_valuationInteger_iff w _).2 hx, hx'⟩) z
    (fun u hu g => by rw [(hN u hu).2 ψ, hW u (hN u hu).1 g]) hf
    (fun h => show h ∈ Spherical.eigenSubalgebra μ z W hf from htop ▸ Algebra.mem_top) g
  rw [this, h1, zero_mul]
  rfl
end

