module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0015
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsStableSquareIntegrableForms
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL

namespace PositivityTheory.Rg.Rs.PrSt

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem splitInv_act (o : Op E N) {φ : Sm E N} (h : ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g) (t : ℝ)
    (g : GA E N) : (act o φ).1 (splitCentre E N t * g) = (act o φ).1 g := by
  cases o with
  | fin k =>
    change φ.1 (splitCentre E N t * g * finGL E N k) = φ.1 (g * finGL E N k)
    rw [mul_assoc, h]
  | cpt k =>
    change φ.1 (splitCentre E N t * g * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    rw [mul_assoc, h]
  | lie X =>
    change lieD X φ.1 (splitCentre E N t * g) = lieD X φ.1 g
    have e : chart φ.1 (splitCentre E N t * g) = chart φ.1 g := by
      funext x
      unfold chart
      split_ifs
      · rw [mul_assoc, h]
      · rfl
    unfold lieD
    rw [e]

theorem isSqInt_act (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E N) {φ : Sm E N} (h : IsAutForm φ)
    (h' : IsSqInt φ.1) : IsSqInt (act o φ).1 := by
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N μ
  have hA := PrAut.isAutForm_act hF o h
  rw [← memL2_iff_isSqInt (μ := μ) (ContAut.continuous_of_isOpen_stab E N _ hA.level) hA.left
    (splitInv_act o h'.1)]
  have hm : MemL2Quotient (latticeGL E N) μ φ.1 := memL2_of_isAutForm h h'
  cases o with
  | fin k => exact hm.mul_right (finGL E N k)
  | cpt k => exact hm.mul_right (infGL E N (Unitary.toUnits k))
  | lie X =>
    let ν : Measure (Lie E N) := Measure.addHaar
    obtain ⟨α, hα, e⟩ := GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self hF E N ν φ h
    have e' : (act (.lie X) φ).1 = GlobalTheory.CuspQuot.smoothing ν (GlobalTheory.AutGrowth.dens X α) φ.1 := by
      funext g
      change lieD X φ.1 g = _
      conv_lhs => rw [← e]
      exact GlobalTheory.AutGrowth.lieD_smoothing_eq_dens E N ν α hα φ.1 φ.2 X g
    rw [e']
    exact SmoothingSquareIntegrable.memL2_of_smoothing μ ν (GlobalTheory.AutGrowth.isTest_dens X hα)
      (ContAut.continuous_of_isOpen_stab E N φ h.level) hm


variable (E N) in
def ainv : Submodule ℂ (Sm E N) where
  carrier := {φ | ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g}
  add_mem' := fun {φ ψ} ha hb t g => by
    change φ.1 _ + ψ.1 _ = φ.1 g + ψ.1 g
    rw [ha t g, hb t g]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c φ ha t g => by
    change c * φ.1 _ = c * φ.1 g
    rw [ha t g]

theorem mem_square_integrable_forms {φ : Sm E N} (hφ : φ ∈ A2 E N) : IsAutForm φ ∧ IsSqInt φ.1 := by
  let μ : Measure (GA E N) := Measure.haar
  have hle : A2 E N ≤ GlobalTheory.DiscClosure.autSub E N ⊓ GlobalTheory.DiscClosure.squareIntegrableSmoothSubmoduleGL μ ⊓ ainv E N :=
    Submodule.span_le.2 fun ψ hψ => ⟨⟨hψ.1, memL2_of_isAutForm hψ.1 hψ.2⟩, hψ.2.1⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hle hφ
  exact ⟨h1, (memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E N φ h1.level) h1.left h3).1 h2⟩

theorem isStable_square_integrable_forms (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) : _root_.GlobalTheory.CuspRep.IsStable (A2 E N) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem ψ hψ => exact Submodule.subset_span ⟨PrAut.isAutForm_act hF o hψ.1, isSqInt_act hF o hψ.1 hψ.2⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

section Adj

open GlobalTheory.CapOrth

variable {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

theorem inner_rt {g : GA E N} (hg : ∀ φ ∈ W, rt E N g φ ∈ W) (hg' : ∀ φ ∈ W, rt E N g⁻¹ φ ∈ W) {φ ψ : Sm E N}
    (hφ : φ ∈ W) (hψ : ψ ∈ W) :
    inner ℂ (cls h (rt E N g φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (rt E N g⁻¹ ψ)) := by
  have hrr : rt E N g (rt E N g⁻¹ ψ) = ψ := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  have e : toL2ₗ μ W h ⟨ψ, hψ⟩ = R (latticeGL E N) μ g (toL2ₗ μ W h ⟨rt E N g⁻¹ ψ, hg' ψ hψ⟩) := by
    rw [R_toL2ₗ h ⟨_, hg' ψ hψ⟩ (by rw [hrr]; exact hψ)]
    exact congrArg _ (Subtype.ext hrr.symm)
  rw [cls_mk h (hg φ hφ), cls_mk h hψ, cls_mk h hφ, cls_mk h (hg' ψ hψ), ← R_toL2ₗ h ⟨φ, hφ⟩ (hg φ hφ), e]
  let Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ := ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  exact Ui.inner_map_map _ _

theorem exists_adj (hW : _root_.GlobalTheory.CuspRep.IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (o : Op E N) :
    ∃ B : Module.End ℂ (Sm E N), (∀ U : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable U → ∀ u ∈ U, B u ∈ U) ∧
      ∀ φ ∈ W, ∀ ψ ∈ W, inner ℂ (cls h (act o φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (B ψ)) := by
  cases o with
  | fin k =>
    refine ⟨act (.fin k⁻¹), fun U hU u hu => hU _ u hu, fun φ hφ ψ hψ => ?_⟩
    have e : (finGL E N k)⁻¹ = finGL E N k⁻¹ := (map_inv _ k).symm
    have := inner_rt h (g := finGL E N k) (fun x hx => hW (.fin k) x hx)
      (fun x hx => by rw [e]; exact hW (.fin k⁻¹) x hx) hφ hψ
    rw [e] at this
    exact this
  | cpt k =>
    refine ⟨act (.cpt k⁻¹), fun U hU u hu => hU _ u hu, fun φ hφ ψ hψ => ?_⟩
    have e : (infGL E N (Unitary.toUnits k))⁻¹ = infGL E N (Unitary.toUnits k⁻¹) := by
      rw [map_inv, map_inv]
    have := inner_rt h (g := infGL E N (Unitary.toUnits k)) (fun x hx => hW (.cpt k) x hx)
      (fun x hx => by rw [e]; exact hW (.cpt k⁻¹) x hx) hφ hψ
    rw [e] at this
    exact this
  | lie X =>
    refine ⟨-act (.lie X), fun U hU u hu => U.neg_mem (hU _ u hu), fun φ hφ ψ hψ => ?_⟩
    have e := GlobalTheory.LieSkew.lie_skew E N μ W h hW hA X ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    rw [LinearMap.neg_apply, show -(act (.lie X) ψ) = (-1 : ℂ) • act (.lie X) ψ by simp,
      cls_smul h (-1 : ℂ) (hW (.lie X) ψ hψ), inner_smul_right, cls_mk h (hW (.lie X) φ hφ), cls_mk h hψ,
      cls_mk h hφ, cls_mk h (hW (.lie X) ψ hψ), neg_one_mul]
    exact e

end Adj

end PositivityTheory.Rg.Rs.PrSt

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs

namespace InducedTensorMap.Main

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem act_fin_val {a : ℕ} (g : GL (Fin a) (Af E)) (F : Sm E a) :
    (act (.fin g) F).1 = fun y => F.1 (y * cf a 1 g) := by
  funext y
  simp [cf]
  rfl

theorem act_cpt_val {a : ℕ} (k : Kinf E a) (F : Sm E a) :
    (act (.cpt k) F).1 = fun y => F.1 (y * cf a k 1) := by
  funext y
  simp [cf]
  rfl

theorem finVec_of_equiv {N : ℕ} {V : Submodule ℂ (Sm E N)} {T : Sm E N →ₗ[ℂ] Sm E N}
    (hT : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) {φ : Sm E N} (hφ : φ ∈ V)
    (hK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k φ))) :
    T φ ∈ finVec (cptRep E N) := by
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k (T φ)))
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E N k φ)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨cptRep E N k φ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  exact hT (.cpt k) φ hφ

end InducedTensorMap.Main

open InducedTensorMap InducedTensorMap.Main in
theorem indMap_holds : IndMap := by
  intro E _ _ _ r s V U₁ U₂ T f₁ f₂ hV hVa hU₁ hU₂ hT hTi hf₁ hf₂
  have H : Good U₁ U₂ f₁ f₂ := ⟨hU₁, hU₂, hf₁, hf₂⟩
  have hI : ∀ φ ∈ V, T φ ∈ indSub U₁ U₂ := fun φ hφ => ⟨(hTi φ hφ).1, fun k g => (hTi φ hφ).2 k g⟩
  have hK : ∀ φ ∈ V, T φ ∈ finVec (cptRep E (r + s)) := fun φ hφ => finVec_of_equiv hT hφ (hVa φ hφ).kfin
  let L : V →ₗ[ℂ] Sm E (r + s) :=
    { toFun := fun φ => ⟨ind f₁ f₂ (T φ.1).1, ind_mem_Sm H (hI _ φ.2) (hK _ φ.2)⟩
      map_add' := fun φ ψ => Subtype.ext (by
        change ind f₁ f₂ (T (φ.1 + ψ.1)).1 = ind f₁ f₂ (T φ.1).1 + ind f₁ f₂ (T ψ.1).1
        rw [map_add (f := _), Submodule.coe_add, map_add (f := _)])
      map_smul' := fun c φ => Subtype.ext (by
        change ind f₁ f₂ (T (c • φ.1)).1 = c • ind f₁ f₂ (T φ.1).1
        rw [map_smul, Submodule.coe_smul, map_smul]) }
  obtain ⟨T', hT'⟩ := LinearMap.exists_extend L
  have e : ∀ φ (hφ : φ ∈ V), (T' φ).1 = ind f₁ f₂ (T φ).1 := fun φ hφ =>
    congrArg Subtype.val (LinearMap.congr_fun hT' ⟨φ, hφ⟩)
  refine ⟨T', fun o φ hφ => ?_, fun φ hφ x g => ?_, fun φ hφ k g n ψ₁ ψ₂ _ _ hs m => ?_⟩
  · have ho := hV o φ hφ
    apply Subtype.ext
    rw [e _ ho, hT o φ hφ]
    cases o with
    | fin g =>
      rw [act_fin_val, act_fin_val, e _ hφ]
      funext x
      exact ind_rt H (hI φ hφ) 1 g x
    | cpt k =>
      rw [act_cpt_val, act_cpt_val, e _ hφ]
      funext x
      exact ind_rt H (hI φ hφ) k 1 x
    | lie X =>
      have hX : lie E (r + s) X (T φ) ∈ indSub U₁ U₂ := by
        have := hT (.lie X) φ hφ
        change T (lie E (r + s) X φ) = lie E (r + s) X (T φ) at this
        rw [← this]
        exact hI _ (hV (.lie X) φ hφ)
      change ind f₁ f₂ (lie E (r + s) X (T φ)).1 = lieD X (T' φ).1
      rw [e _ hφ]
      exact ind_lie H (hI φ hφ) (hK φ hφ) X hX
  · rw [e φ hφ]
    exact ind_left H (hI φ hφ) x g
  · rw [e φ hφ]
    have hres : res (cf (r + s) k g) (T φ).1 = fun m => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := funext hs
    have h1 := congrFun (ind_levi H (hI φ hφ) k g) m
    rw [res_apply] at h1
    change ind f₁ f₂ (T φ).1 (lev (Ad E) r s m * cf (r + s) k g) = _
    rw [h1, hres, tensOp_sum]

end PositivityTheory.Rg.Rs

end
end

