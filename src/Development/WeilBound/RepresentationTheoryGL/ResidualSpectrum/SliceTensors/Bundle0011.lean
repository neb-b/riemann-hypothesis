module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsProj2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.PLsProj2

theorem proj_fun {Y Γ X : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] (act : Γ → Y → Y)
    (ρ : Representation ℂ Γ X) (hρ : ρ.IsIrreducible) (T : Submodule ℂ (Y → ℂ))
    (hle : T ≤ ⨆ Φ : {Φ : X →ₗ[ℂ] (Y → ℂ) // (∀ v, Φ v ∈ T) ∧ ∀ g v, Φ (ρ g v) = fun m => Φ v (act g m)},
      LinearMap.range Φ.1) (t : Y → ℂ) (ht : t ∈ T) (h0 : t ≠ 0) :
    ∃ p : (Y → ℂ) →ₗ[ℂ] X, p t ≠ 0 ∧ ∀ g, ∀ s ∈ T, p (fun m => s (act g m)) = ρ g (p s) := by
  have key := PLsAbs2.exists_proj (fun g => LinearMap.funLeft ℂ ℂ (act g)) ρ hρ
    (fun Φ : {Φ : X →ₗ[ℂ] (Y → ℂ) // (∀ v, Φ v ∈ T) ∧ ∀ g v, Φ (ρ g v) = fun m => Φ v (act g m)} => Φ.1)
    (fun Φ => Φ.2.2) (hle ht) h0
  obtain ⟨p, hp, he⟩ := key
  exact ⟨p, hp, fun g s hs => he g s (hle hs)⟩

theorem schur {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (τ : SmIrr (GL (Fin n) k)) (φ : τ.V →ₗ[ℂ] τ.V) (hφ : ∀ g x, φ (τ.ρ g x) = τ.ρ g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  obtain ⟨z, hz⟩ := GlobalTheory.LocGL.schur_GL τ.smooth τ.irred ⟨φ, fun g => LinearMap.ext (hφ g)⟩
  exact ⟨z, LinearMap.ext hz⟩

theorem irr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {c : ℕ}
    {n : Fin c → ℕ} (τ : ∀ i, SmIrr (GL (Fin (n i)) k)) : (piTensor fun i => (τ i).ρ).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun i => (τ i).irred) fun i => schur (τ i)

end PositivityTheory.Rg.Rs.PLsProj2

namespace PositivityTheory.Rg.Rs

theorem existsProj2 : PositivityTheory.RSHS.LS.ExistsProj := fun E _ _ _ _ n π w τ hτ =>
  PLsProj2.proj_fun (Γ := ∀ i, GL (Fin (n i)) (w.adicCompletion E))
    (fun g (m : ∀ i, GA E (n i)) i => m i * finGL E (n i) (locGL E (n i) w (g i)))
    (piTensor fun i => (τ i).ρ) (PLsProj2.irr τ) (tensorForms π) (PositivityTheory.RSHS.LocalComponentTwist.tensorForms_le_iSup π τ hτ)

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def cf (a : ℕ) (k : Kinf E a) (g : GL (Fin a) (Af E)) : GA E a := infGL E a (Unitary.toUnits k) * finGL E a g

theorem A.act_cf {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (ψ : Sm E a) (x : GA E a) :
    (act (.cpt k) (act (.fin g) ψ)).1 x = ψ.1 (x * cf a k g) := congrArg ψ.1 (mul_assoc _ _ _)

theorem A.sum_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {n : ℕ} {ψ₁ : Fin n → Sm E r}
    {ψ₂ : Fin n → Sm E s} (h₁ : ∀ i, ψ₁ i ∈ U₁) (h₂ : ∀ i, ψ₂ i ∈ U₂) :
    (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) ∈ tens2 U₁ U₂ := by
  have := Submodule.sum_mem (tens2 U₁ U₂) (t := Finset.univ)
    (f := fun i (m : GA E r × GA E s) => (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2)
    fun i _ => Submodule.subset_span ⟨_, h₁ i, _, h₂ i, rfl⟩
  convert this using 1
  funext m
  simp

theorem exists_extOp {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) :
    ∃ T : Module.End ℂ (GA E a → ℂ), ∀ ψ : Sm E a, T ψ.1 = (f ψ).1 := by
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((Sm E a).subtype ∘ₗ f)
  exact ⟨T, fun ψ => LinearMap.congr_fun hT ψ⟩

def extOp {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) : Module.End ℂ (GA E a → ℂ) := (exists_extOp f).choose

theorem extOp_apply {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) (ψ : Sm E a) : extOp f ψ.1 = (f ψ).1 :=
  (exists_extOp f).choose_spec ψ

def tensOp (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Module.End ℂ (GA E r × GA E s → ℂ) where
  toFun F m := extOp f₂ (fun b => extOp f₁ (fun a => F (a, b)) m.1) m.2
  map_add' F G := by
    funext m
    have e : (fun b => extOp f₁ (fun a => (F + G) (a, b)) m.1) =
        (fun b => extOp f₁ (fun a => F (a, b)) m.1) + fun b => extOp f₁ (fun a => G (a, b)) m.1 :=
      funext fun b => congrFun (map_add (extOp f₁) (fun a => F (a, b)) fun a => G (a, b)) m.1
    rw [e, map_add (f := _)]
    rfl
  map_smul' c F := by
    funext m
    have e : (fun b => extOp f₁ (fun a => (c • F) (a, b)) m.1) = c • fun b => extOp f₁ (fun a => F (a, b)) m.1 :=
      funext fun b => congrFun (map_smul (extOp f₁) c fun a => F (a, b)) m.1
    rw [e, map_smul]
    rfl

theorem tensOp_sum (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) {n : ℕ} (ψ₁ : Fin n → Sm E r)
    (ψ₂ : Fin n → Sm E s) :
    tensOp f₁ f₂ (fun m => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) = fun m => ∑ i, (f₁ (ψ₁ i)).1 m.1 * (f₂ (ψ₂ i)).1 m.2 := by
  funext m
  have e1 : ∀ b, (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) = ∑ i, (ψ₂ i).1 b • (ψ₁ i).1 := fun b => by
    funext a; simp [mul_comm]
  have e2 : (fun b => extOp f₁ (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) m.1) = ∑ i, (f₁ (ψ₁ i)).1 m.1 • (ψ₂ i).1 := by
    funext b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp [extOp_apply, mul_comm]
  change extOp f₂ (fun b => extOp f₁ (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) m.1) m.2 = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sum]
  simp [extOp_apply]

theorem tensor_pair_finite_sum {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 U₁ U₂) : ∃ (n : ℕ) (ψ₁ : Fin n → Sm E r) (ψ₂ : Fin n → Sm E s), (∀ i, ψ₁ i ∈ U₁) ∧ (∀ i, ψ₂ i ∈ U₂) ∧
      F = fun m => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hF
  choose φ₁ h₁ φ₂ h₂ e using fun i => (g i).2
  refine ⟨n, fun i => c i • φ₁ i, φ₂, fun i => U₁.smul_mem _ (h₁ i), h₂, funext fun m => ?_⟩
  simp [e, mul_assoc]

theorem tensOp_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 U₁ U₂) : tensOp LinearMap.id LinearMap.id F = F := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  rw [tensOp_sum]
  rfl

theorem tensOp_mem (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) {U₁ : Submodule ℂ (Sm E r)}
    {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) : tensOp f₁ f₂ F ∈ tens2 ⊤ ⊤ := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  rw [tensOp_sum]
  exact A.sum_mem (fun _ => trivial) fun _ => trivial

theorem tensOp_translate {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : _root_.GlobalTheory.CuspRep.IsStable U₁)
    (hU₂ : _root_.GlobalTheory.CuspRep.IsStable U₂) {f₁ : Sm E r →ₗ[ℂ] Sm E r} {f₂ : Sm E s →ₗ[ℂ] Sm E s}
    (hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)) (hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ))
    {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) (k₁ : Kinf E r) (g₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s)
    (g₂ : GL (Fin s) (Af E)) :
    tensOp f₁ f₂ (fun m => F (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂)) =
      fun m => tensOp f₁ f₂ F (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂) := by
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hF
  have e := tensOp_sum f₁ f₂ (fun i => act (.cpt k₁) (act (.fin g₁) (ψ₁ i))) fun i => act (.cpt k₂) (act (.fin g₂) (ψ₂ i))
  simp only [A.act_cf] at e
  rw [e, tensOp_sum]
  funext m
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf₁ _ _ (hU₁ _ _ (h₁ i)), hf₁ _ _ (h₁ i), hf₂ _ _ (hU₂ _ _ (h₂ i)), hf₂ _ _ (h₂ i), A.act_cf, A.act_cf]

theorem tensOp_deriv {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ))
    (hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)) (γ₁ : ℝ → GL (Fin r) (Cinf E)) (γ₂ : ℝ → GL (Fin s) (Cinf E))
    (Z₁ : Lie E r) (Z₂ : Lie E s) (h₁ : γ₁ 0 = 1) (h₂ : γ₂ 0 = 1) (hγ₁ : HasDerivAt (fun t => toL (γ₁ t).val) Z₁ 0)
    (hγ₂ : HasDerivAt (fun t => toL (γ₂ t).val) Z₂ 0) {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) :
    ∃ G : GA E r × GA E s → ℂ,
      (∀ m, HasDerivAt (fun t => F (m.1 * infGL E r (γ₁ t), m.2 * infGL E s (γ₂ t))) (G m) 0) ∧
      ∀ m, HasDerivAt (fun t => tensOp f₁ f₂ F (m.1 * infGL E r (γ₁ t), m.2 * infGL E s (γ₂ t))) (tensOp f₁ f₂ G m) 0 := by
  obtain ⟨n, ψ₁, ψ₂, u₁, u₂, rfl⟩ := tensor_pair_finite_sum hF
  have key : ∀ (χ₁ : Fin n → Sm E r) (χ₂ : Fin n → Sm E s) (m : GA E r × GA E s),
      HasDerivAt (fun t => ∑ i, (χ₁ i).1 (m.1 * infGL E r (γ₁ t)) * (χ₂ i).1 (m.2 * infGL E s (γ₂ t)))
        (∑ i, (lie E r Z₁ (χ₁ i)).1 m.1 * (χ₂ i).1 m.2 + ∑ i, (χ₁ i).1 m.1 * (lie E s Z₂ (χ₂ i)).1 m.2) 0 := by
    intro χ₁ χ₂ m
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have := (hasDerivAt_curve (χ₁ i) m.1 γ₁ Z₁ h₁ hγ₁).mul (hasDerivAt_curve (χ₂ i) m.2 γ₂ Z₂ h₂ hγ₂)
    simp only [h₁, h₂, map_one, mul_one] at this
    exact this
  refine ⟨(fun m => ∑ i, (lie E r Z₁ (ψ₁ i)).1 m.1 * (ψ₂ i).1 m.2) + fun m => ∑ i, (ψ₁ i).1 m.1 * (lie E s Z₂ (ψ₂ i)).1 m.2,
    key ψ₁ ψ₂, fun m => ?_⟩
  rw [map_add (f := _), tensOp_sum, tensOp_sum, tensOp_sum]
  have e₁ : ∀ i, f₁ (lie E r Z₁ (ψ₁ i)) = lie E r Z₁ (f₁ (ψ₁ i)) := fun i => hf₁ (.lie Z₁) _ (u₁ i)
  have e₂ : ∀ i, f₂ (lie E s Z₂ (ψ₂ i)) = lie E s Z₂ (f₂ (ψ₂ i)) := fun i => hf₂ (.lie Z₂) _ (u₂ i)
  simp only [e₁, e₂]
  exact key (fun i => f₁ (ψ₁ i)) (fun i => f₂ (ψ₂ i)) m

theorem contDiffAt_tens {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {y₀ : P} (b₁ : P → GL (Fin r) (Cinf E)) (b₂ : P → GL (Fin s) (Cinf E))
    (hb₁ : ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) y₀) (hb₂ : ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) y₀)
    {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) (m : GA E r × GA E s) :
    ContDiffAt ℝ ∞ (fun y => F (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y))) y₀ := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  refine ContDiffAt.sum fun i _ => ContDiffAt.mul ?_ ?_
  · have := (contDiffAt_chart (ψ₁ i).2 m.1 (val_mem_invSet (b₁ y₀))).comp y₀ hb₁
    simpa only [Function.comp_def, chart_val] using this
  · have := (contDiffAt_chart (ψ₂ i).2 m.2 (val_mem_invSet (b₂ y₀))).comp y₀ hb₂
    simpa only [Function.comp_def, chart_val] using this

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceE
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem exp_left (hD : Dict) (hT : FinTr) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (φ : Sm E (r + s)) (hφ : IsAutForm φ)
    (τs : Finset ℝ) (a : ℝ → ℂ) (F : GA E (r + s) → ℂ)
    (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : Sm E r) (hψ : IsAutForm ψ) (m₂ : GA E s) (h : GA E (r + s))
    (hψF : ∀ m₁, ψ.1 m₁ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    ∀ r₁, 0 < r₁ → r₁ < r → ∀ c₁ ∈ Exp r₁ ψ.1, c₁ ∈ Exp r₁ φ.1 := by
  intro r₁ h0 h1 c₁ hc₁
  obtain ⟨F', hF'span, hF'ne, hF'eig⟩ := (E_exp_iff hD ψ hψ h0 h1 c₁).1 hc₁
  refine (E_exp_iff hD φ hφ h0 (by omega) c₁).2 ?_
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr₁ : Continuous (An.ctn r₁ φ.1) := E_cont_ctn r₁ hφc hφ.left
  have hset : (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)) =
      Set.range fun t : ℝ => fun g => An.ctn r₁ φ.1 (aT E (r + s) r₁ t * g) := rfl
  have hfd := hT E (r + s) φ hφ r₁ h0 (by omega) _ ((hD E (r + s)).2.2.2 φ hφ r₁ h0 (by omega)).1
  rw [← hset] at hfd
  have := hfd
  have key := E_key_left h1 φ hφ τs a F hF ψ.1 m₂ h hψF
  have hP := E_cont_join (E := E) (n := r + s) (S := {r₁, r}) r₁
  set B := E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h))
      ((E_vol E r r₁)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) r₁)) τs a with hBdef
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), Continuous w := by
    rw [hset]; exact E_cont_span r₁ hcr₁
  have hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), B (v + w) = B v + B w :=
    fun v hv w hw => E_B_add hP _ _ _ _ (hcs v hv) (hcs w hw)
  have hsm : ∀ (c : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      B (c • w) = c • B w := fun c w _ => E_B_smul _ _ _ _ _ c w
  have hBL : ∀ (t : ℝ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      B (E_L E (r + s) r₁ t w) = Complex.exp (0 * t) • E_L E r r₁ t (B w) := fun t w _ => by
    rw [hBdef, E_hB_left h1, zero_mul, Complex.exp_zero, one_smul]
  have hF'2 : F' ∈ Submodule.span ℂ (Set.range fun t => E_L E r r₁ t (B (An.ctn r₁ φ.1))) := by
    rw [← key]; exact hF'span
  have hF'3 : ∀ t : ℝ, E_L E r r₁ t F' = Complex.exp (c₁ * t) • F' := fun t => by
    funext g; rw [E_L_apply, hF'eig t g]; rfl
  obtain ⟨G, hG, hGne, hGeig⟩ := E_lift (fun t => E_L E (r + s) r₁ t) (fun t => E_L E r r₁ t) constant_term_zero_eq E_LL
    (An.ctn r₁ φ.1) B hadd hsm c₁ 0 hBL F' hF'2 hF'ne hF'3
  refine ⟨G, hset ▸ hG, hGne, fun t g => ?_⟩
  have := congrFun (hGeig t) g
  rw [E_L_apply, add_zero] at this
  exact this

variable {r s : ℕ}

theorem E_G_base {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g) (t : ℝ) (z : GA E (r + s)) :
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) (aT E (r + s) r t * z) =
    Complex.exp (c * t) * E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) z := by
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_bot hpq x hx
    omega
  have hv : (E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (E_vol_ne _ _)) (E_vol_ne _ _)
  have key : ∀ z, ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
      ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂)) *
        E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) z := by
    intro z
    rw [E_int_right hr₂ φ hφ τs a F hF z]
    simp only [E_B]
    rw [one_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have eig : ∫ b, F (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z))
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
      Complex.exp (c * t) * ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) := by
    rw [← integral_const_mul]
    congr 1
    funext b
    rw [← mul_assoc, ← aT_comm_parGL _ _ _ _ hpos, mul_assoc, hc]
  apply mul_left_cancel₀ hv
  rw [← key, mul_left_comm, ← key, eig]

theorem eisenstein_constant_term_span {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g) (t : ℝ) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)), ∀ z,
      E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a w (aT E (r + s) r t * z) =
      Complex.exp (c * t) * E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a w z := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn (r + r₂) φ.1) := E_cont_ctn (r + r₂) hφc hφ.left
  have hset : (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)) =
      Set.range fun u : ℝ => fun g => An.ctn (r + r₂) φ.1 (aT E (r + s) (r + r₂) u * g) := rfl
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)),
      Continuous w := by
    rw [hset]; exact E_cont_span _ hcr
  have hP := E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) (r + r₂)
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    intro z
    rw [E_G_shift hr₂, E_G_shift hr₂, ← mul_assoc, aT_comm, mul_assoc, E_G_base hr₂ φ hφ τs a F hF c hc]
  | zero =>
    intro z
    simp [E_B]
  | add x y hx hy ihx ihy =>
    intro z
    rw [E_B_add hP _ _ _ _ (hcs x hx) (hcs y hy)]
    simp only [Pi.add_apply]
    rw [ihx, ihy, mul_add]
  | smul d x _ ih =>
    intro z
    rw [E_B_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ih]
    ring

theorem E_key_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : GA E s → ℂ) (m₁ : GA E r) (h : GA E (r + s)) (hψF : ∀ m₂, ψ m₂ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    An.ctn r₂ ψ = E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (m : GA E s) => aT E (r + s) r t * (lev (Ad E) r s (m₁, m) * h))
      ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) τs a (An.ctn (r + r₂) φ.1) := by
  funext m₂
  set y := lev (Ad E) r s (m₁, m₂) * h with hy
  have e2 : ∀ A : UPos s r₂ → Ad E, ψ (unipGL A * m₂) =
      F (parGL (joinPos (r := r) 0 fun q => A ((eR r s r₂ hr₂).symm q)) * y) := by
    intro A
    rw [hψF]
    congr 1
    have e : lev (Ad E) r s (m₁, unipGL A * m₂) = lev (Ad E) r s (1, unipGL A) * lev (Ad E) r s (m₁, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, lev_unipGL_right r s r₂ hr₂, mul_assoc]
  rw [E_ctn_eq, constantTerm_eq_integral]
  simp only [e2]
  rw [← integral_box_reindex (eR r s r₂ hr₂) (fun b => F (parGL (joinPos (r := r) 0 b) * y)),
    E_int_right hr₂ φ hφ τs a F hF y]
  simp only [E_B]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem exp_right (hD : Dict) (hT : FinTr) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (φ : Sm E (r + s)) (hφ : IsAutForm φ)
    (τs : Finset ℝ) (a : ℝ → ℂ) (F : GA E (r + s) → ℂ)
    (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g)
    (ψ : Sm E s) (hψ : IsAutForm ψ) (m₁ : GA E r) (h : GA E (r + s))
    (hψF : ∀ m₂, ψ.1 m₂ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    ∀ r₂, 0 < r₂ → r₂ < s → ∀ c₂ ∈ Exp r₂ ψ.1, c + c₂ ∈ Exp (r + r₂) φ.1 := by
  intro r₂ h0 h1 c₂ hc₂
  obtain ⟨F', hF'span, hF'ne, hF'eig⟩ := (E_exp_iff hD ψ hψ h0 h1 c₂).1 hc₂
  refine (E_exp_iff hD φ hφ (by omega) (by omega) (c + c₂)).2 ?_
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn (r + r₂) φ.1) := E_cont_ctn (r + r₂) hφc hφ.left
  have hset : (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)) =
      Set.range fun t : ℝ => fun g => An.ctn (r + r₂) φ.1 (aT E (r + s) (r + r₂) t * g) := rfl
  have hfd := hT E (r + s) φ hφ (r + r₂) (by omega) (by omega) _
    ((hD E (r + s)).2.2.2 φ hφ (r + r₂) (by omega) (by omega)).1
  rw [← hset] at hfd
  have := hfd
  have key := E_key_right h0 φ hφ τs a F hF ψ.1 m₁ h hψF
  have hP := E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) (r + r₂)
  set B := E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (m : GA E s) => aT E (r + s) r t * (lev (Ad E) r s (m₁, m) * h))
      ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) τs a with hBdef
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      Continuous w := by
    rw [hset]; exact E_cont_span (r + r₂) hcr
  have hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (v + w) = B v + B w :=
    fun v hv w hw => E_B_add hP _ _ _ _ (hcs v hv) (hcs w hw)
  have hsm : ∀ (d : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (d • w) = d • B w := fun d w _ => E_B_smul _ _ _ _ _ d w
  have hBL : ∀ (t : ℝ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (E_L E (r + s) (r + r₂) t w) = Complex.exp (c * t) • E_L E s r₂ t (B w) := fun t w hw => by
    funext m₂
    have eB : ∀ (f : GA E (r + s) → ℂ) (m : GA E s), B f m =
        ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) *
        E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
          (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a f (lev (Ad E) r s (m₁, m) * h) := by
      intro f m
      simp only [hBdef, E_B, one_mul]
    rw [Pi.smul_apply, E_L_apply, eB, eB, E_G_shift h0, E_aT_right h1.le, eisenstein_constant_term_span h0 φ hφ τs a F hF c hc t w hw,
      smul_eq_mul]
    ring
  have hF'2 : F' ∈ Submodule.span ℂ (Set.range fun t => E_L E s r₂ t (B (An.ctn (r + r₂) φ.1))) := by
    rw [← key]; exact hF'span
  have hF'3 : ∀ t : ℝ, E_L E s r₂ t F' = Complex.exp (c₂ * t) • F' := fun t => by
    funext g; rw [E_L_apply, hF'eig t g]; rfl
  obtain ⟨G, hG, hGne, hGeig⟩ := E_lift (fun t => E_L E (r + s) (r + r₂) t) (fun t => E_L E s r₂ t) constant_term_zero_eq E_LL
    (An.ctn (r + r₂) φ.1) B hadd hsm c₂ c hBL F' hF'2 hF'ne hF'3
  refine ⟨G, hset ▸ hG, hGne, fun t g => ?_⟩
  have := congrFun (hGeig t) g
  rw [E_L_apply, add_comm c₂ c] at this
  exact this

end PositivityTheory.Rg.Rs.SliceClasses

end
end

