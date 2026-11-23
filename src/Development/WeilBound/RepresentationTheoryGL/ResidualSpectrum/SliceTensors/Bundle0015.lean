module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapE
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapF
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem F.hasDerivAt_line {a : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Lie E a → Y}
    (hf : ContDiffAt ℝ ∞ f (oneL E a)) (X : Lie E a) :
    HasDerivAt (fun t : ℝ => f (oneL E a + t • X)) (fderiv ℝ f (oneL E a) X) 0 := by
  have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)).congr_deriv (one_smul _ _)
  have hd : HasFDerivAt f (fderiv ℝ f (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℝ) hl

theorem lieD_of_expansion {H : GA E (r + s) → ℂ} (hH : H ∈ Sm E (r + s)) {n : ℕ} (K : Fin n → GA E r × GA E s → ℂ)
    (C : Fin n → Lie E (r + s) → ℂ) (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E))
    (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)) (hC : ∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s)))
    (h₁ : b₁ (oneL E (r + s)) = 1) (h₂ : b₂ (oneL E (r + s)) = 1) (m : GA E r × GA E s)
    (he : chart H (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * K j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)))
    (X : Lie E (r + s)) (D : Fin n → ℂ)
    (hD : ∀ j, HasDerivAt (fun t : ℝ => K j (m.1 * infGL E r (b₁ (oneL E (r + s) + t • X)),
      m.2 * infGL E s (b₂ (oneL E (r + s) + t • X)))) (D j) 0) :
    lieD X H (lev (Ad E) r s m) = ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X * K j m + C j (oneL E (r + s)) * D j) := by
  have l0 : oneL E (r + s) + (0 : ℝ) • X = oneL E (r + s) := by rw [zero_smul, add_zero]
  have hl : HasDerivAt (fun t : ℝ => oneL E (r + s) + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul _ _)
  have a1 := F.hasDerivAt_line (contDiffAt_chart hH (lev (Ad E) r s m) isUnit_one) X
  have a2 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F.hasDerivAt_line (hC j) X).mul (hD j)
  have ht : Filter.Tendsto (fun t : ℝ => oneL E (r + s) + t • X) (nhds 0) (nhds (oneL E (r + s))) := by
    have := hl.continuousAt.tendsto
    rwa [l0] at this
  have a3 := a2.congr_of_eventuallyEq (ht.eventually he)
  refine (a1.unique a3).trans (Finset.sum_congr rfl fun j _ => ?_)
  simp only [l0, h₁, h₂, map_one, mul_one]

theorem res_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) :
    res 1 (lieD X (ind f₁ f₂ F.1)) = tensOp f₁ f₂ (res 1 (lie E (r + s) X F).1) := by
  obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, h₁, h₂, e⟩ := exists_expansion hF hK
  have g₁ : (fun t : ℝ => b₁ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₁]
  have g₂ : (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₂]
  choose G' hd₁ hd₂ using fun j => tensOp_deriv H.hf₁ H.hf₂ (fun t : ℝ => b₁ (oneL E (r + s) + t • X))
    (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) _ _ g₁ g₂ (InducedTensorMap.F.hasDerivAt_line hb₁ X) (InducedTensorMap.F.hasDerivAt_line hb₂ X) (hG j)
  have hid : ∀ j, tensOp LinearMap.id LinearMap.id (G j) = G j := fun j => tensOp_id (hG j)
  have eF : ∀ m : GA E r × GA E s, chart F.1 (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * G j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
    intro m
    have := e (good_id H.hU₁ H.hU₂) m
    rw [ind_id H.hU₁ H.hU₂ hF] at this
    simpa only [hid] using this
  have eq1 : res 1 (lie E (r + s) X F).1 =
      ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X • G j + C j (oneL E (r + s)) • G' j) := by
    funext m
    rw [res_apply, mul_one, lie_apply,
      lieD_of_expansion F.2 G C b₁ b₂ hC h₁ h₂ m (eF m) X (fun j => G' j m) (fun j => hd₁ j m)]
    simp [Finset.sum_apply]
  funext m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [res_apply, mul_one, eq1, map_sum,
    lieD_of_expansion (ind_mem_Sm H hF hK) (fun j => tensOp f₁ f₂ (G j)) C b₁ b₂ hC h₁ h₂ m (e H m) X
      (fun j => tensOp f₁ f₂ (G' j) m) (fun j => hd₂ j m)]
  simp [Finset.sum_apply]

theorem ind_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) (hX : lie E (r + s) X F ∈ indSub U₁ U₂) :
    ind f₁ f₂ (lie E (r + s) X F).1 = lieD X (ind f₁ f₂ F.1) := by
  let Gs : Sm E (r + s) := ⟨ind f₁ f₂ F.1, ind_mem_Sm H hF hK⟩
  have hleft : ∀ (u : BlockIx (r + s) r → Ad E) x,
      lieD X (ind f₁ f₂ F.1) (unip u * x) = lieD X (ind f₁ f₂ F.1) x := by
    intro u x
    have e : chart (ind f₁ f₂ F.1) (unip u * x) = chart (ind f₁ f₂ F.1) x := by
      funext y
      unfold chart
      split_ifs with hy
      · rw [mul_assoc, ind_left H hF]
      · rfl
    simp only [lieD, e]
  refine ext_res (ind_left H hX) hleft fun k g => ?_
  obtain ⟨X', hX'⟩ : ∃ X', rt E (r + s) (cf (r + s) k g) * lie E (r + s) X =
      lie E (r + s) X' * rt E (r + s) (cf (r + s) k g) := by
    refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
    rw [cf, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
    exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  have ec : ∀ ψ : Sm E (r + s), res (cf (r + s) k g) (lie E (r + s) X ψ).1 =
      res 1 (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) ψ)).1 := fun ψ => funext fun m => by
    have := congrArg (fun f : Module.End ℂ (Sm E (r + s)) => (f ψ).1 (lev (Ad E) r s m * 1)) hX'
    simp only [Module.End.mul_apply, rt_apply, mul_one] at this
    rw [res_apply, res_apply, mul_one]
    exact this
  have hF' : rt E (r + s) (cf (r + s) k g) F ∈ indSub U₁ U₂ := isInd_rt hF k g
  have hK' := finVec_rt hK k g
  have hr : (rt E (r + s) (cf (r + s) k g) Gs).1 = ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 :=
    funext fun x => (ind_rt H hF k g x).symm
  have h1 : res (cf (r + s) k g) (lieD X (ind f₁ f₂ F.1)) = res (cf (r + s) k g) (lie E (r + s) X Gs).1 := rfl
  have h2 : (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) Gs)).1 =
      lieD X' (ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1) := by
    rw [← hr]
    rfl
  rw [ind_levi H hX k g, h1, ec Gs, ec F, h2, res_lie H hF' hK' X']

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAut
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspStab

namespace PositivityTheory.Rg.Rs.PrAut

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem isAutForm_act (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E N) {φ : Sm E N} (h : IsAutForm φ) :
    IsAutForm (act o φ) := by
  cases o with
  | fin k =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)
      rw [mul_assoc, h.left]
    · have e : {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ} =
          (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E N k' φ = φ} := by
        ext k'
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul]
        constructor
        · intro e
          rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply]
        · intro e
          have := congrArg (finRep E N k) e
          rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E N k), ← map_mul,
            mul_inv_cancel, map_one, Module.End.one_apply] at this
      change IsOpen {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ}
      rw [e]
      exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E N c φ)).map
        (finRep E N k)) (Submodule.span_le.2 ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
    · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) h.zfin
    · obtain ⟨C, M, h1⟩ := h.growth (g * finGL E N k)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * finGL E N k)‖ ≤ _
      rw [mul_assoc, infGL_comm, ← mul_assoc]
      exact h1 y
  | cpt c =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits c)) = φ.1 (g * infGL E N (Unitary.toUnits c))
      rw [mul_assoc, h.left]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (cptRep E N c φ) = cptRep E N c φ
        rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E N c φ))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨c', rfl⟩
      refine Submodule.subset_span ⟨c' * c, ?_⟩
      change _ = (cptRep E N c' * cptRep E N c) φ
      rw [← map_mul]
    · exact zfin_of_comm _ (fun z hz => GlobalTheory.ZalgCpt.zalg_comm_cptRep E N c z hz) h.zfin
    · obtain ⟨C, M, h1⟩ := growth_mul (Unitary.toUnits c) (h.growth g)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * infGL E N (Unitary.toUnits c))‖ ≤ _
      rw [mul_assoc, ← map_mul]
      exact h1 y
  | lie X =>
    refine ⟨fun γ g => ?_, ?_, GlobalTheory.CuspRep.KFin.kfin_lie E N X φ h.kfin,
      zfin_of_comm _ (fun z hz => GlobalTheory.CuspRep.Zalg_mul_lie E N X z hz) h.zfin,
      GlobalTheory.CuspStab.lie_growth hF E N X φ h⟩
    · change lieD X φ.1 (ratGL E N γ * g) = lieD X φ.1 g
      have e : chart φ.1 (ratGL E N γ * g) = chart φ.1 g := by
        funext x
        unfold chart
        split_ifs
        · rw [mul_assoc, h.left]
        · rfl
      unfold lieD
      rw [e]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (lie E N X φ) = lie E N X φ
        change (rt E N (finGL E N k) * lie E N X) φ = _
        rw [← lie_rt_fin, Module.End.mul_apply]
        exact congrArg (lie E N X) hk

end PositivityTheory.Rg.Rs.PrAut

end
end

