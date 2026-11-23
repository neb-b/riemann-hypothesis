module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.GlNegOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PetInv
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem tw_rt (χ : HChar E) (g : GA E a) (φ : Sm E a) :
    mulChi a χ (rt E a g φ) = ((chiDet a χ g : ℂˣ) : ℂ)⁻¹ • rt E a g (mulChi a χ φ) := by
  rw [rt_mulChi, map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

private theorem prod_fin (x : GL (Fin a) (Af E)) (φ : Sm E a) (l : List (Lie E a)) :
    (l.map (lie E a)).prod (act (.fin x) φ) = act (.fin x) ((l.map (lie E a)).prod φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, ih]
    exact LinearMap.congr_fun (lie_rt_fin X x) _

private theorem prod_sq {r : ℝ} {φ : Sm E a} (h : IsSq r φ) (l : List (Lie E a)) :
    IsSq r ((l.map (lie E a)).prod φ) := by
  induction l with
  | nil => exact h
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact (sqLie E a r).1 X _ ih

private theorem sqInt_fin (ha : 1 ≤ a) {r : ℝ} {φ : Sm E a} (h : IsSq r φ) (x : GL (Fin a) (Af E)) :
    IsSqIntMod (act (.fin x) φ) := by
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  obtain ⟨s, hs⟩ := hχ.1
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨h1, h2⟩ := sqMem E a ha μ r χ hχ φ (Submodule.subset_span h)
  have h3 := (sqUniq E a ha r χ hχ φ h.one (h.sq [])).1
  have hc : Continuous (mulChi a χ φ).1 := ContAut.continuous_of_isOpen_stab E a _ h1
  refine ⟨s, χ, hs, ?_⟩
  have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * (act (.fin x) φ).1 g) =
      ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ • fun g => (mulChi a χ φ).1 (g * finGL E a x) := by
    funext g
    exact (mul_comm _ _).trans (congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)
  rw [e]
  have h4 := h2.mul_right (finGL E a x)
  generalize ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ = c
  have hc' : Continuous fun g => (mulChi a χ φ).1 (g * finGL E a x) := hc.comp (continuous_id.mul continuous_const)
  refine (CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (hc'.const_smul c) (fun γ g => ?_)
    (fun t g => ?_)).1 ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩
  · simp only [Pi.smul_apply, mul_assoc]
    rw [mulChi_apply, mulChi_apply, map_mul (chiDet a χ) (ratGL E a γ), chiDet_ratGL, one_mul, h.left]
  · simp only [Pi.smul_apply, mul_assoc, h3]

private theorem isSq_fin (ha : 1 ≤ a) {r : ℝ} (x : GL (Fin a) (Af E)) (φ : Sm E a) (h : IsSq r φ) :
    IsSq r (act (.fin x) φ) := by
  refine { left := ?_, level := ?_, one := ?_, sq := ?_ }
  · intro γ g
    change φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)
    rw [mul_assoc, h.left]
  · have e : {k | act (.fin k) (act (.fin x) φ) = act (.fin x) φ} =
        (fun k => x⁻¹ * k * x) ⁻¹' {k | act (.fin k) φ = φ} := by
      ext k
      change finRep E a k (finRep E a x φ) = finRep E a x φ ↔ finRep E a (x⁻¹ * k * x) φ = φ
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      constructor
      · intro hk
        rw [hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro hk
        have := congrArg (finRep E a x) hk
        rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [e]
    exact h.level.preimage (by fun_prop)
  · have e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ) :=
      LinearMap.congr_fun (lie_rt_fin _ x) φ
    rw [e, h.one, map_smul]
  · intro l
    rw [prod_fin]
    exact sqInt_fin ha (prod_sq h l) x

end

theorem UpperTheory.V.Cj.H.petInv :
    UpperTheory.V.Cj.H.PetInv := by
  intro E _ _ _ a ha r
  refine ⟨isSq_fin ha, ?_⟩
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hs := sqMem E a ha μ r χ hχ
  have hm : ∀ φ ∈ (sqSub E a r).map (mulChi a χ).toLinearMap, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ φ.1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hs φ hφ).2
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (sqSub E a r).subtype (Submodule.ker_subtype _)
  obtain ⟨T, hT⟩ : ∃ T : Sm E a →ₗ[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 (latticeGL E a) μ, ∀ φ (hφ : φ ∈ sqSub E a r),
      T φ = (hs φ hφ).2.toL2 := by
    refine ⟨CuspidalL2GL.toL2ₗ μ _ hm ∘ₗ (mulChi a χ).toLinearMap.submoduleMap (sqSub E a r) ∘ₗ p, fun φ hφ => ?_⟩
    have e : p φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hp ⟨φ, hφ⟩
    simp only [LinearMap.comp_apply, e]
    rfl
  refine ⟨((innerₛₗ ℂ) ∘ₛₗ T).compl₂ T, ⟨fun x y => ?_, fun x _ => ?_, fun x hx h0 => ?_⟩, fun x => ?_⟩
  · exact (inner_conj_symm (T y) (T x)).symm
  · exact inner_self_nonneg (𝕜 := ℂ) (x := T x)
  · have h1 : T x = 0 := inner_self_eq_zero.1 (show inner ℂ (T x) (T x) = 0 from h0)
    rw [hT x hx] at h1
    by_contra hne
    refine CuspidalL2GL.toL2_ne_zero (hs x hx).2 (ContAut.continuous_of_isOpen_stab E a _ (hs x hx).1) (fun e => hne ?_) h1
    exact (mulChi a χ).map_eq_zero_iff.1 (Subtype.ext e)
  · set c : ℂ := ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ with hc
    have hst : sqSub E a r ≤ (sqSub E a r).comap (act (.fin x)) :=
      Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_fin ha x ψ hψ)
    have key : ∀ φ ∈ sqSub E a r,
        T (act (.fin x) φ) = c • GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ) := fun φ hφ => by
      rw [hT _ (hst hφ), hT φ hφ, GlobalTheory.AutomorphicL2Unitary.right_translate_toL2]
      have h4 := (hs φ hφ).2.mul_right (finGL E a x)
      have h5 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ (c • fun g => (mulChi a χ φ).1 (g * finGL E a x)) :=
        ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩
      refine Eq.trans ?_ (show h5.toL2 = c • h4.toL2 from MemLp.toLp_const_smul c h4.2)
      exact (GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.toL2_eq_iff_ae_eq _ h5).2
        (.of_forall fun g => congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)
    refine ⟨starRingEnd ℂ c * c, fun φ hφ ψ hψ => ?_⟩
    change inner ℂ (T (act (.fin x) φ)) (T (act (.fin x) ψ)) = _ * inner ℂ (T φ) (T ψ)
    have hi : inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ))
        (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T ψ)) = inner ℂ (T φ) (T ψ) :=
      (LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x)).toLinearMap
        (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _
    rw [key φ hφ, key ψ hψ, inner_smul_left, inner_smul_right, hi, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SmSepDer
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem sm_sepDer (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) :
    SepDer (smK Ξ) (smLie Ξ) := by
  intro k Z h0 hk m' hm
  have h1 : ∃ j, Bor.cmp j m' ≠ 0 := by
    by_contra h
    push Not at h
    apply hm
    rw [← sum_cmp m']
    simp [h]
  obtain ⟨j, hj⟩ := h1
  have h2 : (Bor.cmp j m').1 ≠ 0 := fun h => hj (Subtype.ext h)
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (Bor.cmp j m).1 g
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : Sm E a) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1 g * v j := fun φ v => by
    change (Bor.cmp j (φ ⊗ₜ v)).1 g = _
    rw [cmp_tmul, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    have h7 : smLie Ξ (toL Z) (φ ⊗ₜ v) = lie E a (toL Z) φ ⊗ₜ v + φ ⊗ₜ (Ξ.dmat (toL Z) *ᵥ v) := rfl
    simp only [smK, h7, TensorProduct.map_tmul, map_add (f := _), hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5

theorem UpperTheory.V.Cj.H.smAB :
    UpperTheory.V.Cj.H.SmAB := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun X Y => ?_, fun k X => ?_, fun k X => ?_,
    infAbs E a _ _ _ (sm_sepDer E a Ξ)⟩
  · simp only [smA_apply]
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_sub]
    congr 1
    exact (lie_comm (toL X) (toL Y)).trans (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm
  · simp only [smB_apply]
    rw [← GlobalTheory.AlgInfChar.dmat_bracket, map_sub, LinearMap.lTensor_sub, Matrix.toLin'_mul, Matrix.toLin'_mul,
      LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    rfl
  · rw [smA_apply, smB_apply]
    exact TensorProduct.ext' fun _ _ => rfl
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : act (.cpt k) (lie E a (toL X) φ) = lie E a (toL (k.1 * X * star k.1)) (act (.cpt k) φ) :=
      LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ
    simp only [Module.End.mul_apply, smK, smA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) =
        Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [Module.End.mul_apply, smK, smB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private def stab (ψ : Sm E a) : Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) where
  carrier := {k | rt E a (finGL E a k) ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

private theorem lev_lie (X : Lie E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (lie E a X ψ) := by
  have hle : stab ψ ≤ stab (lie E a X ψ) := fun k hk =>
    (LinearMap.congr_fun (lie_rt_fin X k) ψ).symm.trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem lev_rt (g : GA E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (rt E a g ψ) := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E a y * finGL E a l = g := ⟨_, _, infGL_mul_finGL g⟩
  have hc : Continuous fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l := by fun_prop
  have ho : IsOpen ((fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l) ⁻¹' (stab ψ : Set _)) :=
    IsOpen.preimage hc h
  refine Subgroup.isOpen_of_mem_nhds (stab (rt E a (infGL E a y * finGL E a l) ψ)) (g := 1)
    (mem_of_superset (ho.mem_nhds ?_) fun k hk => ?_)
  · simpa using (stab ψ).one_mem
  · have hk' : rt E a (finGL E a (l⁻¹ * k * l)) ψ = ψ := hk
    change rt E a (finGL E a k) (rt E a (infGL E a y * finGL E a l) ψ) = rt E a (infGL E a y * finGL E a l) ψ
    have e : finGL E a k * (infGL E a y * finGL E a l) = infGL E a y * finGL E a l * finGL E a (l⁻¹ * k * l) := by
      rw [← mul_assoc, ← infGL_comm, mul_assoc, mul_assoc (infGL E a y), ← map_mul, ← map_mul]
      congr 2
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']

private theorem supp_lie (X : Lie E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (lie E a X ψ).1 := by
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  set_option synthInstance.maxHeartbeats 200000 in
    refine HasCompactSupport.intro h fun g hg => ?_
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve ψ g c X c0 cder
  have hc : Continuous fun t : ℝ => g * infGL E a (c t) := continuous_const.mul ccont
  have ht : Tendsto (fun t : ℝ => g * infGL E a (c t)) (𝓝 0) (𝓝 g) := by
    set_option synthInstance.maxHeartbeats 200000 in
      simpa [c0] using hc.tendsto 0
  have hz : (fun t : ℝ => ψ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
    ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)

private theorem supp_rt (g : GA E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (rt E a g ψ).1 :=
  h.comp_homeomorph (Homeomorph.mulRight g)

end

theorem UpperTheory.V.Cj.H.testOps :
    UpperTheory.V.Cj.H.TestOps := by
  intro E _ _ _ a ψ
  exact ⟨fun h => ⟨ContAut.continuous_of_isOpen_stab E a ψ h, fun X => lev_lie X ψ h, fun g => lev_rt g ψ h⟩,
    fun h => ⟨fun X => ⟨supp_lie X ψ h.1, lev_lie X ψ h.2⟩, fun g => ⟨supp_rt g ψ h.1, lev_rt g ψ h.2⟩⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.UnitCont
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem inf_cont (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

private theorem unit_cont (E : Type) [Field E] [NumberField E] (a : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin a) (Cinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  simp only [Matrix.coe_units_inv]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨d, hd⟩ := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

theorem UpperTheory.V.Cj.H.smDiv :
    UpperTheory.V.Cj.H.SmDiv := by
  intro E _ _ _ a φ u w
  refine ⟨fun g => ?_, fun Z hZ h0 hw g x hx => ?_⟩
  · refine ((φ.2 g).mul (u.2 g)).congr fun x hx => ?_
    have h : IsUnit (Matrix.of x) := hx
    simp only [chart, dif_pos h]
  · have h : IsUnit (Matrix.of x) := hx
    have e : ∀ y ∈ invSet E a, chart (fun g => φ.1 g / w.1 g) g y = chart φ.1 g y * (chart w.1 g y)⁻¹ := by
      intro y hy
      have h' : IsUnit (Matrix.of y) := hy
      simp only [chart, dif_pos h', div_eq_mul_inv]
    by_cases hz : g * infGL E a h.unit ∈ Z
    · have hne : chart w.1 g x ≠ 0 := by
        rw [chart, dif_pos h]
        exact hw _ hz
      exact ((φ.2 g x hx).mul ((w.2 g x hx).inv hne)).congr e (e x hx)
    · let v : invSet E a → GL (Fin a) (Cinf E) := fun y => (show IsUnit (Matrix.of y.1) from y.2).unit
      have hv : Continuous v := unit_cont E a v continuous_subtype_val
      have hc : Continuous fun y : invSet E a => g * infGL E a (v y) :=
        continuous_const.mul ((inf_cont E a).comp hv)
      have ho : IsOpen {y : invSet E a | g * infGL E a (v y) ∉ Z} := hZ.isOpen_compl.preimage hc
      have hn : ∀ᶠ y : invSet E a in 𝓝 ⟨x, hx⟩, g * infGL E a (v y) ∉ Z := ho.mem_nhds hz
      have hv : ∀ᶠ y in 𝓝[invSet E a] x, chart (fun g => φ.1 g / w.1 g) g y = 0 := by
        rw [nhdsWithin_eq_map_subtype_coe hx, eventually_map]
        filter_upwards [hn] with y hy
        have h' : IsUnit (Matrix.of y.1) := y.2
        rw [chart, dif_pos h', h0 _ hy, zero_div]
      exact (contDiffWithinAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hv (hv.self_of_nhdsWithin hx)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.WigAlpha
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}
  {N : Type} [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  {N' : Type} [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N']

omit [NumberField E] [IsScalarTower ℝ ℂ N] [IsScalarTower ℝ ℂ N'] in
private theorem hol_nat (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' : Lie E a →ₗ[ℝ] N')
    (h : ∀ X, φ (L (toL X)) = L' (toL X)) (x : Matrix (Fin a) (Fin a) ℂ) : φ (hol τ L x) = hol τ L' x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hol_apply, eL, map_sum, map_smul, map_sub, h]

omit [NumberField E] [IsScalarTower ℝ ℂ N] in
private theorem hol_add (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N) : hol τ (L + L') = hol τ L + hol τ L' := by
  ext1 x
  simp only [hol_apply, eL, LinearMap.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

omit [NumberField E] in
private theorem hol_smul (τ : E →+* ℂ) (r : ℝ) (L : Lie E a →ₗ[ℝ] N) : hol τ (r • L) = (r : ℂ) • hol τ L := by
  ext1 x
  have e : ∀ v : N, r • v = (r : ℂ) • v := fun v => (algebraMap_smul ℂ r v).symm
  simp only [hol_apply, eL, LinearMap.smul_apply, Finset.smul_sum, e]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

variable [_root_.NumberField.IsTotallyComplex E]

private theorem hol_der (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' L'' : Lie E a →ₗ[ℝ] N')
    (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, φ (L (toL X)) = L' (toL X) + L'' (toL (Y * X - X * Y)))
    (x : Matrix (Fin a) (Fin a) ℂ) :
    φ (hol τ L x) = hol τ L' x + hol τ L'' (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  rw [hol_nat τ φ L (φ.restrictScalars ℝ ∘ₗ L) (fun _ => rfl),
    ← (holMul E a N' τ L'' (φ.restrictScalars ℝ ∘ₗ L - L')).2 Y (fun X => sub_eq_of_eq_add' (h X)) x,
    ← LinearMap.add_apply, ← hol_add, add_sub_cancel]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

private theorem hol_der_end (τ : E →+* ℂ) (u : Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)
    (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, u * L (toL X) - L (toL X) * u = L (toL (Y * X - X * Y)))
    (x : Matrix (Fin a) (Fin a) ℂ) :
    u * hol τ L x - hol τ L x * u = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  have h1 := hol_der τ (LinearMap.mulLeft ℂ u - LinearMap.mulRight ℂ u) L 0 L Y
    (fun X => (h X).trans (zero_add _).symm) x
  have h0 : hol τ (0 : Lie E a →ₗ[ℝ] Module.End ℂ M) x = 0 := by simp [hol_apply, eL]
  rw [h0, zero_add] at h1
  exact h1

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.H.wigAlpha :
    UpperTheory.V.Cj.H.WigAlpha := by
  intro E _ _ _ a M _ _ _ _ LA LB hA hB hc τ x
  have hcomm : ∀ y z, Commute (hol τ LA y) (hol τ LB z) := fun y z => by
    simp only [hol_apply, eL]
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
      Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
    exact (((((hc _ _).sub_right ((hc _ _).smul_right _)).sub_left
      (((hc _ _).sub_right ((hc _ _).smul_right _)).smul_left _)).smul_right _).smul_left _
      |>.smul_right _).smul_left _
  have hAlpha := UpperTheory.V.AlgRepEndIrreducible.alphaAbs M a (hol τ LA) (hol τ LB)
    (fun k : Fin a => x - (k.val : ℂ)) hcomm
  obtain ⟨α₀, h1, -, h3⟩ := hAlpha
  set s : ℂ := (a.factorial : ℂ)⁻¹ with hs
  have e : ∀ (r : ℝ) (v : M), r • v = (r : ℂ) • v := fun r v => (algebraMap_smul ℂ r v).symm
  let α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M :=
    { toFun := fun f => s • α₀ (hol τ f)
      map_add' := fun f g => by rw [hol_add, map_add (f := _), smul_add]
      map_smul' := fun r f => by rw [hol_smul, map_smul, RingHom.id_apply, e, smul_comm] }
  have hα : ∀ f, α f = s • α₀ (hol τ f) := fun _ => rfl
  refine ⟨α, fun Y f f' hf => ?_, fun m f hf => ?_⟩
  · rw [hα, hα, map_smul]
    congr 1
    refine h3 _ (Y.map (coord τ)) (hol_der_end τ _ LA Y fun X => ?_) (hol_der_end τ _ LB Y fun X => ?_) _ _
      (hol_der τ _ f f' f Y hf)
    · rw [LinearMap.add_apply, add_mul, mul_add, ← hA Y X, (hc (toL X) (toL Y)).eq]
      abel
    · rw [LinearMap.add_apply, add_mul, mul_add, ← hB Y X, (hc (toL Y) (toL X)).eq]
      abel
  · have hx : ∀ y, hol τ f y = hol τ LA y m + hol τ LB y m := fun y => by
      rw [← hol_nat τ (LinearMap.applyₗ m) (LA + LB) f (fun X => (hf _).symm), hol_add]
      rfl
    rw [hα, h1 m _ hx]
    simp only [hol_single]
    have gA := (eLRel E a _ LA hA).1 τ
    have gB := (glNegOp _ a _ ((eLRel E a _ LB hB).1 τ)).1
    rw [Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet _ gB, show (fun i j => eL LA τ i j) = eL LA τ from rfl,
      Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet _ gA]
    have hz : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
    simp only [MulOpposite.unop_smul, LinearMap.smul_apply, LinearMap.sub_apply, ← smul_sub, smul_smul]
    rw [hs, inv_mul_cancel₀ hz, one_smul]
end

