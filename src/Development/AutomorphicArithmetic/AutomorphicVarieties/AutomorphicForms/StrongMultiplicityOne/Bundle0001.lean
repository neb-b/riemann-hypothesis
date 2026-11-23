module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ArchKir
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem lmul_lmul {E : Type} [Field E] [NumberField E] {n : ℕ} (a b : Matrix (Fin n) (Fin n) (Cinf E))
    (x : Lie E n) : lmul (toL a) (lmul (toL b) x) = lmul (toL (a * b)) x := by
  change toL (a * (b * Matrix.of x)) = toL (a * b * Matrix.of x)
  rw [Matrix.mul_assoc]

private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

theorem UpperTheory.V.Af.StrongMultiplicityOne.archKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.StrongMultiplicityOne.ArchStep → UpperTheory.V.Af.StrongMultiplicityOne.LinChange → UpperTheory.V.Af.StrongMultiplicityOne.ArchKir := by
  classical
  intro hC hR hA hL E _ _ n m
  induction m with
  | zero =>
    intro _
    refine ⟨fun p => psiR E (supN p.val), ?_, fun α => ⟨α, fun w _ _ hw p hp => ?_⟩⟩
    · have : supN (1 : GL (Fin n) (Cinf E)).val = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with h
        · exact Matrix.one_apply_ne (fun e => by subst e; omega)
        · rfl
      simp only [this]
      simp [psiR]
    · simp only [hw p hp, mul_assoc]
      exact integral_const_mul _ _
  | succ m ih =>
    intro hm
    obtain ⟨H, H1, hH⟩ := ih (by omega)
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨h, h1, hu, hh⟩ := hA E n m' hm
    obtain ⟨c, c1, hc⟩ := hL E n
    refine ⟨fun p => if hs : IsUnit (rowM m' (p.val m')) then h (p.val m') * (c hs.unit * H (p * hs.unit⁻¹)) else 0, ?_,
      fun α => ?_⟩
    · have hs : IsUnit (rowM m' ((1 : GL (Fin n) (Cinf E)).val m')) := by
        rw [Units.val_one, rowM_one]; exact isUnit_one
      have e : hs.unit = 1 := Units.ext (by rw [hs.unit_spec, Units.val_one, rowM_one])
      simp only [dif_pos hs, e]
      simp [h1, c1, H1]
    · obtain ⟨β₀, hβ₀⟩ := hH α
      obtain ⟨β, hβ⟩ := hh β₀
      refine ⟨β, fun w wm wb hw p hp => ?_⟩
      obtain ⟨C, hCb⟩ := wb
      have key := hβ (fun x => w (lmul (toL p.val) x)) (p.val m')
        (wm.comp (lmul (toL p.val)).continuous.measurable) ⟨C, fun x => hCb _⟩ (fun u x => by
          obtain ⟨ν, hν, hs, e⟩ := hC (Cinf E) n m' hm p hp u
          simp only [lmul_lmul]
          rw [e, ← lmul_lmul, hw ν hν, hs])
      rw [key]
      by_cases h0 : h (p.val m') = 0
      · simp [h0]
      have hs := hu _ h0
      simp only [dif_pos hs]
      have hy := hR (Cinf E) n m' p hs.unit hp hs.unit_spec
      have e1 := hβ₀ w wm ⟨C, hCb⟩ hw _ hy
      have e2 := hc hs.unit (fun y => w (lmul (toL (p * hs.unit⁻¹).val) y) * β₀ y)
      have e3 : (p * hs.unit⁻¹).val * hs.unit.val = p.val := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      simp only [lmul_lmul, e3] at e2
      rw [hs.unit_spec] at e2
      rw [e2, e1]
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ArchStep
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem of_lmul (a : Matrix (Fin n) (Fin n) (Cinf E)) (x : Lie E n) :
    lmul (toL a) x = toL (a * Matrix.of x) := rfl

private theorem lmul_one_add (a : Matrix (Fin n) (Fin n) (Cinf E)) (x : Lie E n) :
    lmul (toL (1 + a)) x = x + lmul (toL a) x := by
  rw [of_lmul, of_lmul, add_mul, one_mul]; rfl

private theorem exists_bil {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : V →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E)) :
    ∃ B : V →L[ℝ] Lie E n →L[ℝ] Lie E n, ∀ u x, B u x = lmul (toL (L u)) x := by
  let B0 : V →ₗ[ℝ] Lie E n →L[ℝ] Lie E n :=
    { toFun := fun u => lmul (toL (L u))
      map_add' := fun u v => by
        ext1 x
        rw [ContinuousLinearMap.add_apply, of_lmul, of_lmul, of_lmul, map_add (f := _), add_mul]; rfl
      map_smul' := fun c u => by
        ext1 x
        rw [ContinuousLinearMap.smul_apply, of_lmul, of_lmul, map_smul, smul_mul_assoc]; rfl }
  exact ⟨LinearMap.toContinuousLinearMap B0, fun _ _ => rfl⟩

private theorem isUnit_of_inj (a : Matrix (Fin n) (Fin n) (Cinf E)) (h : ∀ y : Lie E n, lmul (toL a) y = 0 → y = 0) :
    IsUnit a := by
  have hi : Function.Injective (LinearMap.mulLeft ℝ a) :=
    (injective_iff_map_eq_zero _).2 fun y hy => h (toL y) hy
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.1 hi 1
  exact IsUnit.of_mul_eq_one b hb

variable {d : ℕ} (b : Module.Basis (Fin d) ℝ (Cinf E))

private noncomputable def crd (i : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Cinf E where
  toFun u := b.equivFun.symm fun v => u (i, v)
  map_add' u v := map_add b.equivFun.symm (fun x => u (i, x)) fun x => v (i, x)
  map_smul' c u := map_smul b.equivFun.symm c fun x => u (i, x)

private noncomputable def colL (m : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E) where
  toFun u := Matrix.of fun i j => if i ≤ m ∧ j.val = m.val + 1 then crd b i u else 0
  map_add' u v := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def rowL (m : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E) where
  toFun u := Matrix.of fun i j => if i = m ∧ j ≤ m then -crd b j u else 0
  map_add' u v := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp [add_comm]
  map_smul' c u := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def eta (m : Fin n) (ξ : Fin n → Cinf E) : EuclideanSpace ℝ (Fin n × Fin d) :=
  WithLp.toLp 2 fun z => if z.1 ≤ m then -b.repr (ξ z.1) z.2 else 0

private theorem crd_eta (m : Fin n) (ξ : Fin n → Cinf E) {j : Fin n} (h : j ≤ m) : crd b j (eta b m ξ) = -ξ j := by
  change b.equivFun.symm _ = _
  rw [LinearEquiv.symm_apply_eq]
  funext v
  simp [eta, h]

private theorem repr_crd (j : Fin n) (u : EuclideanSpace ℝ (Fin n × Fin d)) (v : Fin d) :
    b.repr (crd b j u) v = u (j, v) :=
  congrFun (b.equivFun.apply_symm_apply fun v => u (j, v)) v

private theorem colL_sq (m : Fin n) (u : EuclideanSpace ℝ (Fin n × Fin d)) : colL b m u * colL b m u = 0 := by
  ext1 i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [colL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  by_cases h : k ≤ m
  · rw [if_neg, zero_mul]
    rintro ⟨-, h'⟩
    rw [Fin.le_def] at h
    omega
  · rw [if_neg (fun h' : k ≤ m ∧ _ => h h'.1), mul_zero]

private theorem rowM_eq (m : Fin n) (ξ : Fin n → Cinf E) :
    rowM m ξ = 1 + rowL b m (eta b m ξ - eta b m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m)) := by
  ext1 i j
  simp only [rowM, rowL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply]
  split_ifs with h
  · obtain ⟨rfl, h⟩ := h
    rw [map_sub, crd_eta b _ _ h, crd_eta b _ _ h]
    ring
  · simp

private theorem inner_eta (b' : Module.Basis (Fin d) ℝ (Cinf E))
    (H : ∀ x y, TG.tr E (x * y) = ∑ i, b'.repr x i * b.repr y i) (m : Fin n) (ξ : Fin n → Cinf E)
    (u : EuclideanSpace ℝ (Fin n × Fin d)) :
    ⟪eta b' m ξ, u⟫ = -TG.tr E (dotLe m ξ fun j => crd b j u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PiLp.inner_apply, Fintype.sum_prod_type, dotLe, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ≤ m
  · rw [if_pos h, H, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [eta, h, repr_crd, mul_comm]
  · simp [eta, h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.StrongMultiplicityOne.archStep :
    UpperTheory.V.Af.StrongMultiplicityOne.TrDual → UpperTheory.V.Af.Smo.SchTw → UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch → UpperTheory.V.Af.Smo.BetaInt → UpperTheory.V.Af.StrongMultiplicityOne.ArchStep := by
  intro h0 h1 h2 h3 h4 E _ _ n m _
  obtain ⟨d, b, b', H⟩ := h0 E
  obtain ⟨B, hB⟩ := exists_bil (colL b m)
  obtain ⟨A, hA⟩ := exists_bil (rowL b' m)
  have hBB : ∀ u x, B u (B u x) = 0 := fun u x => by
    rw [hB, hB, of_lmul, of_lmul]
    change toL (colL b m u * (colL b m u * Matrix.of x)) = 0
    rw [← mul_assoc, colL_sq, zero_mul]; rfl
  obtain ⟨h, he, hu, hG⟩ := h1 _ _ A (eta b' m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m))
  have hrow : ∀ ξ y, y + A (eta b' m ξ - eta b' m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m)) y = lmul (toL (rowM m ξ)) y :=
    fun ξ y => by rw [rowM_eq b', lmul_one_add, hA]
  refine ⟨fun ξ => h (eta b' m ξ), he, fun ξ hξ => isUnit_of_inj _ fun y hy => hu _ hξ y (by rw [hrow, hy]), fun α => ?_⟩
  obtain ⟨G, hG⟩ := hG α
  obtain ⟨K, hK⟩ := h2 _ _ G
  obtain ⟨K', β, hK', hβ⟩ := h3 _ _ B hBB K
  refine ⟨β, fun w ξ hw hb hw' => ?_⟩
  haveI : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := h4 _ _ (volume : Measure (Lie E n)) B hBB G K K' hK hK' w (eta b' m ξ) hw hb fun u x => by
    rw [hB, ← lmul_one_add, inner_eta b b' H]
    exact hw' (fun j => crd b j u) x
  simp only [hβ]
  rw [this, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hG, hrow]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Carrier
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.carrier :
    UpperTheory.V.Af.StrongMultiplicityOne.Carrier := by
  intro E _ _ _ n π
  refine ⟨Cm.carrier π, Cm.stab_carrier π, (Cm.stab_carrier π).isIrreducible_iff.1 (Cm.isIrreducible_toModule π),
    fun f => ⟨fun ⟨ψ, hψ, e⟩ => ⟨_, hψ, e⟩, fun ⟨φ, hφ, e⟩ => ?_⟩⟩
  rw [← Cm.map_carrier] at hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨ψ, hψ, e⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.CenSame
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.cenSame :
    UpperTheory.V.Af.Smo.CentEq → UpperTheory.V.Af.StrongMultiplicityOne.SetUp → UpperTheory.V.Af.StrongMultiplicityOne.CenSame := by
  intro hC hS E _ _ n U U' hU hs hc φ' hφ' s g'
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨S, B, hB, hk, hk'⟩ := hS E n U U' hs φ φ'
  have loc : ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), InKS S (locGL E n w k) := by
    intro w hw k hkk
    refine ⟨fun x hx => GlobalTheory.CuspRep.pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _, fun x => ?_⟩
    by_cases e : x = w
    · subst e
      rw [GlobalTheory.CuspRep.pLoc_locGL]
      exact hkk
    · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne e]
      exact one_mem _
  have e := hC E n S B φ.1 φ'.1 φ.2.1.continuous φ'.2.1.continuous φ.2.1.isLeftInvariant φ'.2.1.isLeftInvariant
    (fun w hw => ⟨(hB w hw).2.1 φ hφ fun g k h => hk g _ (loc w hw k h),
      (hB w hw).2.2 φ' hφ' fun g k h => hk' g _ (loc w hw k h)⟩) hk hk'
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  obtain ⟨z, hz⟩ : ∃ z : (Ad E)ˣ, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) z :=
    ⟨_, Units.ext rfl⟩
  have e1 := e z g g'
  rw [← hz, apply_mul_centralSection_of_mem (hc hφ)] at e1
  rw [Reduction.centralSection_mul_comm]
  exact (mul_left_cancel₀ hg e1).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ChartCont
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem cc_infGL (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (a : ℕ) :
    Continuous (infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf F : Cinf F → Ad F) := (GlobalTheory.CuspRep.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

private theorem cc_unit (E : Type) [Field E] [NumberField E] (n : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin n) (Cinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  have e : (fun x => ((u x)⁻¹).val) = fun x => ((u x).val)⁻¹ := funext fun x => Matrix.coe_units_inv _
  rw [e]
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hd : IsUnit ((u x).val).det := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  obtain ⟨d, hd⟩ := hd
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

theorem UpperTheory.V.Af.StrongMultiplicityOne.chartCont :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont := by
  intro E _ _ _ n f hf
  have h1 : ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n) := by
    rw [continuousOn_iff_continuous_restrict]
    let u : ↥((Set.univ : Set (GA E n)) ×ˢ invSet E n) → GL (Fin n) (Cinf E) :=
      fun z => (show IsUnit (Matrix.of z.1.2) from z.2.2).unit
    have hu : Continuous u := cc_unit E n u (continuous_snd.comp continuous_subtype_val)
    have e : ((Set.univ : Set (GA E n)) ×ˢ invSet E n).domRestrict (fun z : GA E n × Lie E n => chart f z.1 z.2) =
        fun z => f (z.1.1 * infGL E n (u z)) := by
      funext z
      have h : IsUnit (Matrix.of z.1.2) := z.2.2
      change chart f z.1.1 z.1.2 = _
      rw [chart, dite_eq_left h]
    rw [e]
    exact hf.comp ((continuous_fst.comp continuous_subtype_val).mul ((cc_infGL E n).comp hu))
  refine ⟨h1, fun g => ?_⟩
  classical
  have h2 : ContinuousOn (chart f g) (invSet E n) :=
    h1.comp (f := fun x => (g, x)) (continuous_const.prodMk continuous_id).continuousOn
      fun x hx => ⟨Set.mem_univ _, hx⟩
  have h3 := h2.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const GlobalTheory.CuspRep.isOpen_invSet.measurableSet
  convert h3 using 1
  funext x
  by_cases hx : x ∈ invSet E n
  · rw [Set.piecewise_eq_of_mem _ _ _ hx]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, chart, dite_eq_right (show ¬ IsUnit (Matrix.of x) from hx)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ChartSmul
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem isY_map {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ} (f : R →+* R') (p : GL (Fin n) R)
    (hp : IsY m p.val) : IsY m (GeneralLinearGroup.map f p).val := by
  intro i hi
  obtain ⟨h1, h2⟩ := hp i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (p.val i i) = 1
    rw [h1, map_one]
  · change f (p.val i j) = 0
    rw [h2 j hj, map_zero]

private theorem chart_smul {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (f f' : GA E n → ℂ)
    (g g' : GA E n) (a : ℂ) (h : ∀ y, f (g * infGL E n y) = a * f' (g' * infGL E n y)) (x : Lie E n) :
    chart f g x = a * chart f' g' x := by
  unfold chart
  split_ifs with hx
  · exact h _
  · simp

theorem UpperTheory.V.Af.StrongMultiplicityOne.killP :
    UpperTheory.V.Af.StrongMultiplicityOne.ArchKir → UpperTheory.V.Af.StrongMultiplicityOne.FinKir → UpperTheory.V.Af.StrongMultiplicityOne.EmbY → UpperTheory.V.Af.StrongMultiplicityOne.PsiInf → UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.KillP := by
  intro hA hF hE hP hC E _ _ _ n hn S U
  obtain ⟨c, Hf, hf1, hc, hf⟩ := hF E n hn S U
  obtain ⟨Hi, hi1, hi⟩ := hA E n (n - 1) (by omega)
  refine ⟨c, fun p => Hi (GeneralLinearGroup.map (pInf E) p) * Hf (GeneralLinearGroup.map (pFin E) p),
    by simp [hi1, hf1], hc, fun α => ?_⟩
  obtain ⟨β, hβ⟩ := hi α
  refine ⟨β, fun W hW hb hWh hU p hp => ?_⟩
  obtain ⟨C, hb⟩ := hb
  have hpi := isY_map (pInf E) p hp.1
  have hpf := isY_map (pFin E) p hp.1
  have hS := hp.2
  beta_reduce
  have e : p = finGL E n (GeneralLinearGroup.map (pFin E) p) * infGL E n (GeneralLinearGroup.map (pInf E) p) := by
    rw [← GlobalTheory.CuspRep.infGL_comm, GlobalTheory.CuspRep.infGL_mul_finGL]
  generalize GeneralLinearGroup.map (pInf E) p = a at *
  generalize GeneralLinearGroup.map (pFin E) p = b at *
  have h1 : ∀ x, chart (fop c W) (finGL E n b) x = Hf b * chart W 1 x := by
    refine chart_smul _ _ _ _ _ fun y => ?_
    have := hf (fun k => W (finGL E n k * infGL E n y)) (fun ν _ hν g _ => ?_) (fun g _ u hu _ => ?_) b hS hpf
    · simp only [map_one] at this
      rw [← this]
      unfold fop comb
      refine Finsupp.sum_congr fun x _ => ?_
      beta_reduce
      rw [map_mul, mul_assoc, mul_assoc, GlobalTheory.CuspRep.infGL_comm]
    · obtain ⟨k1, k2⟩ := (hE E n 0).2.1 ν hν
      rw [map_mul, mul_assoc, hWh _ k1, k2]
      rfl
    · rw [map_mul, mul_assoc, ← GlobalTheory.CuspRep.infGL_comm, ← mul_assoc, hU _ u hu]
  have h2 := hβ (chart W 1) ((hC E n W hW).2 1) ⟨max C 0, fun x => ?_⟩ (fun ν hν x => ?_) a hpi
  · unfold conv
    rw [e, GlobalTheory.CuspRep.chart_mul]
    simp only [Function.comp_apply, h1, mul_assoc]
    rw [integral_const_mul, h2]
    ring
  · unfold chart
    split_ifs
    · exact (hb _).trans (le_max_left _ _)
    · simp
  · obtain ⟨k1, k2⟩ := (hE E n 0).2.2.1 ν hν
    have := congrFun (GlobalTheory.CuspRep.chart_mul W 1 ν) x
    rw [Function.comp_apply] at this
    rw [← this]
    refine chart_smul _ _ _ _ _ (fun y => ?_) x
    rw [one_mul, one_mul, hWh _ k1, k2, hP]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Compl
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.compl :
    UpperTheory.V.Af.StrongMultiplicityOne.Compl := by
  intro E _ _ n μ _ U l hs
  have hStable : Fb.Stab (orthRel (CuspidalSpectrum.cuspToL2 μ) (centralCuspForms E n) U) := by
    refine ⟨fun X φ hφ => ?_, fun k φ hφ => ?_, fun g φ hφ => ?_⟩
    · refine map_mem_orthRel (A' := fun y => -(gkModuleCusp E n).ρ X y) (Fb.stab_central.ρ X)
        (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hs.ρ X u hu)) hφ
      rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
      exact petersson_inner_lieAlgebra_skewAdjoint μ X (l hx) hy
    · refine map_mem_orthRel (A' := (gkModuleCusp E n).σ k⁻¹) (Fb.stab_central.σ k)
        (fun x hx y hy => ?_) (hs.σ k⁻¹) hφ
      have hInv : (gkModuleCusp E n).σ k ((gkModuleCusp E n).σ k⁻¹ x) = x := by
        change ((gkModuleCusp E n).σ k * (gkModuleCusp E n).σ k⁻¹) x = x
        simp only [← map_mul (gkModuleCusp E n).σ k k⁻¹, mul_inv_cancel, map_one,
          one_apply_eq_self]
      exact (petersson_inner_maximalCompact_invariant μ k (l (hs.σ k⁻¹ x hx)) hy).symm.trans
        (congrArg (fun z => inner ℂ (CuspidalSpectrum.cuspToL2 μ z)
          (CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp E n).σ k y))) hInv)
    · refine map_mem_orthRel (A' := finRepCusp E n g⁻¹) (Fb.stab_central.τ g)
        (fun x hx y hy => ?_) (hs.τ g⁻¹) hφ
      have hInv : finRepCusp E n g (finRepCusp E n g⁻¹ x) = x := by
        change (finRepCusp E n g * finRepCusp E n g⁻¹) x = x
        simp only [← map_mul (finRepCusp E n) g g⁻¹, mul_inv_cancel, map_one,
          one_apply_eq_self]
      exact (petersson_inner_finiteAdelic_invariant μ g (l (hs.τ g⁻¹ x hx)) hy).symm.trans
        (congrArg (fun z => inner ℂ (CuspidalSpectrum.cuspToL2 μ z)
          (CuspidalSpectrum.cuspToL2 μ (finRepCusp E n g y))) hInv)
  exact ⟨orthRel (CuspidalSpectrum.cuspToL2 μ) (centralCuspForms E n) U,
    hStable, CuspidalSpectrum.sup_orthRel_centralCuspForms μ U l hs.ρ hs.τ,
    fun φ hφ φ' hφ' => hφ'.2 φ hφ⟩
end

