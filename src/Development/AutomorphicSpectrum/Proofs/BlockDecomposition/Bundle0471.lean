module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0458
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0457
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0439
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0421
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0431
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import GroundTheory.AutomorphicForms.ReductionHeight
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationInduced
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.MemO

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_cont {a b : ℕ} (e : a = b) : Continuous (castM k e) ∧ Continuous (castM k e).symm := by
  subst e
  exact ⟨continuous_id, continuous_id⟩

theorem exists_compact_cell (i t : ℕ) (C : Set (Mir k ((i + 1) + t + 1))) (hC : IsCompact C) (hCl : ∀ c ∈ C, c ∉ Cl k i t) :
    ∃ N : Set (Mir k ((i + 1) + t)), IsCompact N ∧ ∀ c ∈ C, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k), ∃ m ∈ N,
      c = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m := by
  refine hC.induction_on (p := fun S => ∃ N : Set (Mir k ((i + 1) + t)), IsCompact N ∧ ∀ c ∈ S, ∃ h ∈ HPG k (i + 1) (t + 1),
    ∃ (d : Fin (t + 1) → k), ∃ m ∈ N, c = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, by simp⟩
  · rintro s t' hst ⟨N, hN, h⟩
    exact ⟨N, hN, fun c hc => h c (hst hc)⟩
  · rintro s t' ⟨N, hN, h⟩ ⟨N', hN', h'⟩
    refine ⟨N ∪ N', hN.union hN', ?_⟩
    rintro c (hc | hc)
    · obtain ⟨a, ha, d, m, hm, e⟩ := h c hc
      exact ⟨a, ha, d, m, Or.inl hm, e⟩
    · obtain ⟨a, ha, d, m, hm, e⟩ := h' c hc
      exact ⟨a, ha, d, m, Or.inr hm, e⟩
  · intro x hx
    obtain ⟨V, hV, μ, hμ, hs⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.Chart.chart k i t x (hCl x hx)
    obtain ⟨V', hV', hcl, hsub⟩ := exists_mem_nhds_isClosed_subset hV
    refine ⟨C ∩ V', Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV'), μ '' (C ∩ V'), ?_, ?_⟩
    · exact (hC.inter_right hcl).image_of_continuousOn (hμ.mono (fun y hy => hsub hy.2))
    · intro c hc
      obtain ⟨a, ha, d, e⟩ := hs c (hsub hc.2)
      exact ⟨a, ha, d, μ c, ⟨c, hc, rfl⟩, e⟩
end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_fin (n : ℕ) : @MeasureTheory.IsFiniteMeasureOnCompacts (Fin n → k) (borel _) _ (muD k n) := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem smInt_lin {n : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (T : W →ₗ[ℂ] W') {F : (Fin n → k) → W} (l : IsLocallyConstant F) (c : HasCompactSupport F) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (T ∘ F) = T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F) := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI := muD_fin (k := k) n
  exact GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear _ T l c

theorem smInt_zero' {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun _ => (0 : W)) = 0 := by
  unfold GlobalTheory.CompanionTheory.Rodier.smInt
  refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have : (fun _ : Fin n → k => (0 : W)) ⁻¹' {v} = ∅ := by
      ext x
      simp [Ne.symm hv]
    rw [this]
    simp

variable {i t : ℕ}

theorem eO_equiv (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (h : HPG k i (t + 1)) (m : Mir k (i + (t + 1))) :
    eO ψ f ((h : Mir k (i + (t + 1))) * m) = sigO τ σ ψ h (eO ψ f m) := by
  obtain ⟨hη, hproj⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj k i t h
  set a' := (pgProj k i (t + 1) h).1 with ha'
  set w' := (pgProj k i (t + 1) h).2 with hw'
  set y := wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) m) with hy
  set η := wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ with hηd
  have e1 : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) ((h : Mir k (i + (t + 1))) * m)) = η * y := by
    rw [map_mul, map_mul, hηd, hy]
    group
  let Tm : (phiN ψ τ).V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
    extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a', w')
  let sc : ℂ := ((dpowM i (1 / 2) a' : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w' : ℂˣ) : ℂ)
  let G : (Fin (t + 1) → k) → (phiN ψ τ).V ⊗[ℂ] σ.V := fun d => qO τ σ ψ (evX f (dEmb k i t d * y))
  have hpt : ∀ d, qO τ σ ψ (evX f (dEmb k i t d * (η * y))) = (sc • Tm) (G ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) := by
    intro d
    obtain ⟨c, u, hc, hu, he⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.Conj.dEmb_conj k ψ i t h d
    have e2 : dEmb k i t d * (η * y) =
        ((⟨η, hη⟩ : HPG k (i + 1) (t + 1)) : Mir k ((i + 1) + (t + 1))) * ((c : Mir k ((i + 1) + (t + 1))) *
          (dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) * y)) := by
      have he' : dEmb k i t d * η = η * (c : Mir k ((i + 1) + (t + 1))) * dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := he
      calc dEmb k i t d * (η * y) = (dEmb k i t d * η) * y := (mul_assoc _ _ _).symm
        _ = (η * (c : Mir k ((i + 1) + (t + 1))) * dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) * y := by rw [he']
        _ = _ := by rw [mul_assoc, mul_assoc]
    have e3 : ∀ (hh : HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + (t + 1))),
        evX f ((hh : Mir k ((i + 1) + (t + 1))) * x) = sigX τ σ hh (evX f x) := fun hh x =>
      (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 hh x
    rw [e2, e3, e3]
    have e4 : ∀ (hh : HPG k (i + 1) (t + 1)) (v), sigX τ σ hh v =
        extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) hh) v := fun _ _ => rfl
    rw [e4, hproj, _root_.GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine, e4, hc, _root_.GlobalTheory.CompanionTheory.BZPhiPG.qO_extTensor_unip k i t ψ τ σ u hu]
    rfl
  have hl := GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y
  have hl2 := GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f (η * y)
  have hG : IsLocallyConstant G := hl.1.comp (qO τ σ ψ)
  have hGc : HasCompactSupport G := hl.2.comp_left (map_zero (qO τ σ ψ))
  have key : qO τ σ ψ (intO f (η * y)) =
      ((dpow (t + 1) 1 w' : ℂˣ) : ℂ) • (sc • Tm) (qO τ σ ψ (intO f y)) := by
    have s1 : qO τ σ ψ (intO f (η * y)) = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
        (fun d => ((sc • Tm) ∘ G) ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) := by
      unfold intO
      rw [← smInt_lin (qO τ σ ψ) hl2.1 hl2.2]
      congr 1
      funext d
      exact hpt d
    have s2 : qO τ σ ψ (intO f y) = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) G := by
      unfold intO
      rw [← smInt_lin (qO τ σ ψ) hl.1 hl.2]
      rfl
    rw [s1, _root_.GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst k (t + 1) _ w' ((sc • Tm) ∘ G) (hG.comp _) (hGc.comp_left (map_zero _)),
      smInt_lin (sc • Tm) hG hGc, s2]
  have e5 : sigO τ σ ψ h = Tm := rfl
  unfold eO
  rw [e1, ← hy, key, e5, map_smul, map_mul]
  have h6 : ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 w' : ℂˣ) : ℂ) * sc = 1 := _root_.GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel k i t h
  rw [LinearMap.smul_apply, smul_smul, smul_smul, Units.val_mul]
  congr 1
  linear_combination ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) * h6

theorem eO_supp (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ C : Set (Mir k (i + (t + 1))), IsCompact C ∧
      ∀ g, eO ψ f g ≠ 0 → ∃ h ∈ HPG k i (t + 1), ∃ c ∈ C, g = h * c := by
  have ee : i + (t + 1) = (i + 1) + t := by omega
  obtain ⟨C, hC, hCl, hsupp⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl k i t τ σ f hf
  obtain ⟨N, hN, hcell⟩ := exists_compact_cell i t C hC hCl
  refine ⟨(castM k ee).symm '' N, hN.image (castM_cont ee).2, fun g hg => ?_⟩
  set y := wEl k i t * sEmb k ((i + 1) + t) (castM k ee g) with hy
  have hne : intO f y ≠ 0 := fun h0 => hg (by
    unfold eO
    rw [show wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) g) = y from rfl, h0, map_zero, smul_zero])
  obtain ⟨d, hd⟩ : ∃ d, evX f (dEmb k i t d * y) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold intO
    rw [show (fun d => evX f (dEmb k i t d * y)) = fun _ => 0 from funext hcon]
    exact smInt_zero'
  obtain ⟨h1, hh1, c, hc, e1⟩ := hsupp _ hd
  obtain ⟨h2, hh2, d2, m2, hm2, e2⟩ := hcell c hc
  have e3 : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (castM k ee g * m2⁻¹) =
      (h1 * h2) * dEmb k i t d2 * wEl k i t := by
    have e4 : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (castM k ee g) =
        h1 * (h2 * dEmb k i t d2 * wEl k i t * sEmb k ((i + 1) + t) m2) := by
      rw [← e2, ← e1, hy, mul_assoc]
    rw [map_mul, map_inv, ← mul_assoc, e4]
    group
  obtain ⟨h', hh', e5⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset k i t _ d d2 (h1 * h2) (mul_mem hh1 hh2) e3
  refine ⟨h', hh', (castM k ee).symm m2, ⟨m2, hm2, rfl⟩, ?_⟩
  apply (castM k ee).injective
  rw [map_mul, MulEquiv.apply_symm_apply, e5]
  group

theorem memOAlt (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  let F : indSpace (HPG k i (t + 1)) (sigO τ σ ψ) := ⟨eO ψ f, fun h g => eO_equiv ψ τ σ f h g⟩
  have hF : F ∈ smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ)) := by
    show IsOpen {g | ind (HPG k i (t + 1)) (sigO τ σ ψ) g F = F}
    convert _root_.GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods k i t ψ τ σ f using 1
    ext g
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h m
      exact congrFun (congrArg Subtype.val h) m
    · intro h
      exact Subtype.ext (funext h)
  obtain ⟨C, hC, hs⟩ := eO_supp ψ τ σ f hf
  exact ⟨⟨⟨F, hF⟩, C, hC, hs⟩, rfl⟩
end

theorem eO_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  intro k _ _ _ _ i t ψ _ τ σ _ _ f hf
  exact memOAlt i t ψ τ σ f hf

end GlobalTheory.CompanionTheory.BZPhiPG.MemO

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem trace_norm_local_sizes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl (F := F)) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  intro F E _ _ _ _ _ σ hCM x
  obtain ⟨_, hEc, hfin2, hconj⟩ := hCM
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ z, σ (σ z) = z := fun z => τ0.injective (by rw [hconj, hconj, star_star])
  have hσne : ∃ w, σ w ≠ w := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hreal : NumberField.ComplexEmbedding.IsReal τ0 := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun w => ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      have h1 := hconj τ0 w
      rw [hcon w] at h1
      exact h1.symm
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEc.isComplex (InfinitePlace.mk τ0)) ⟨τ0, hreal, rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ z : E, σ z = z → ∃ y : F, algebraMap F E y = z := by
    intro z hz
    have hSle : Submodule.span F {(1 : E)} ≤ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      simp
    have hker : LinearMap.ker (σ.toLinearMap - LinearMap.id) ≠ ⊤ := by
      intro htop
      obtain ⟨w, hw⟩ := hσne
      have hw' : w ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at hw'
      exact hw (sub_eq_zero.1 hw')
    have h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
    have hlt := Submodule.finrank_lt hker
    have hge := Submodule.finrank_mono hSle
    have heq := Submodule.eq_of_le_of_finrank_eq hSle (by omega)
    have hzk : z ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [LinearMap.mem_ker]
      simp [hz]
    rw [← heq] at hzk
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hzk
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨y₁, hy₁⟩ := hfix (x + σ x) (by rw [map_add (f := _), hσσ, add_comm])
  obtain ⟨y₂, hy₂⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
  refine ⟨y₁, y₂, by rw [hy₁, hy₂]; ring, fun v τ => ?_⟩
  have key : ∀ y : F, τ (algebraMap F E y) =
      algebraMap (Fv F v) (FvBar F v) (algebraMap F (Fv F v) y) := fun y => by
    rw [τ.commutes]
    exact IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v) y
  constructor
  · rw [← absBar_algebraMap F v, ← key, hy₁, map_add (f := _)]
    exact absBar_add_le F v _ _
  · rw [← absBar_algebraMap F v, ← key, hy₂, map_mul]
    exact absBar_mul F v _ _

end GlobalTheory.CompanionTheory.GodementH
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}


variable (F) in
def ratV (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def hv (ξ : Fin n → AF F ⊗[F] E) : ℝ :=
  GroundTheory.Automorphic.Reduction.adelicNorm
    (fun p : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) =>
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr
        (ξ ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
        ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2)

def hgt (g : GAd σ J) (v : Fin n → E) : ℝ := hv ((matHom _ σ J g⁻¹).1 *ᵥ ratV F v)

def Sends (γ : GAd σ J) (u v : Fin n → E) : Prop := (matHom _ σ J γ).1 *ᵥ ratV F u = ratV F v

def NearMin (g : GAd σ J) (v : Fin n → E) : Prop :=
  v ≠ 0 ∧ hE σ J v v = 0 ∧ ∀ u : Fin n → E, u ≠ 0 → hE σ J u u = 0 → hgt σ J g v ≤ 2 * hgt σ J g u

def HasRed (X Y : Matrix (Fin n) (Fin r) E) : Prop :=
  ∀ a, IsTorus σ J X Y a → ∃ (C : Set (GAd σ J)) (c : ℝ), IsCompact C ∧ 0 < c ∧
    ∀ g, ∃ γ ∈ ratPts σ J, ∃ q ∈ minParOne σ J X, ∃ s : Fin r → ℝ,
      (fun i => Real.exp (s i)) ∈ cone r c ∧ ∃ κ ∈ C, g = γ * q * a s * κ

theorem ratV_injective : Function.Injective (ratV F : (Fin n → E) → Fin n → AF F ⊗[F] E) := by
  intro u v h
  funext i
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w : AF F →+* w.Completion).domain_nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective (congrFun h i)

variable {σ J}

theorem Sends.inv {γ : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ u v) : Sends σ J γ⁻¹ v u := by
  unfold Sends at h ⊢
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem hgt_mul {γ g : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ⁻¹ v u) : hgt σ J (γ⁻¹ * g) u = hgt σ J g v := by
  unfold Sends at h
  unfold hgt
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  simp [_root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.RedCov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegral
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.StdInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_finOne_smul' (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) :
    compFin F E v (finOne F • z) = compFin F E v z := by
  have h1 : GlobalTheory.AdelicU.evFin F v (GlobalTheory.ThK.Dbl.finOne F) = 1 := by
    simp only [GlobalTheory.AdelicU.evFin, GlobalTheory.ThK.Dbl.finOne, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, LinearMap.inr_apply]
    change (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = 1
    exact map_one _
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul']
    simp [GlobalTheory.AdelicU.compFin, h1]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]

theorem absFin_compFin_le_one {z : AE F E} (hz : z ∈ intHat F E) (v : HeightOneSpectrum (𝓞 F)) :
    absFin F v (compFin F E v z) ≤ 1 := by
  let S : AddSubgroup (AE F E) :=
    { carrier := {z | GlobalTheory.AdelicU.absFin F v (GlobalTheory.AdelicU.compFin F E v z) ≤ 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [show GlobalTheory.AdelicU.compFin F E v (x + y) = GlobalTheory.AdelicU.compFin F E v x + GlobalTheory.AdelicU.compFin F E v y from map_add _ _ _]
        exact (GlobalTheory.AdelicU.absFin_add_le F v _ _).trans (max_le hx hy)
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        rw [show GlobalTheory.AdelicU.compFin F E v 0 = 0 from map_zero _, GlobalTheory.AdelicU.absFin_zero]
        exact zero_le_one
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [show GlobalTheory.AdelicU.compFin F E v (-x) = -GlobalTheory.AdelicU.compFin F E v x from map_neg _ _, GlobalTheory.AdelicU.absFin_neg]
        exact hx }
  have hle : intHat F E ≤ S := by
    rw [GlobalTheory.ThK.Dbl.intHat, AddSubgroup.closure_le]
    rintro z ⟨a, -, ha, o, rfl⟩
    show GlobalTheory.AdelicU.absFin F v (GlobalTheory.AdelicU.compFin F E v _) ≤ 1
    have h2 : GlobalTheory.AdelicU.compFin F E v (a • (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) (o : E)) =
        (GlobalTheory.AdelicU.evFin F v a) ⊗ₜ[F] (o : E) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, GlobalTheory.AdelicU.compFin, TensorProduct.smul_tmul']
    rw [h2]
    refine (GlobalTheory.AdelicU.absFin_tmul_le F v _ o).trans ?_
    exact nnnorm_le_one_iff_mem.mpr (ha v)
  exact hle hz

theorem absFin_inFrame_le_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)),
    IsStdK (σ := σ) (Y := Y) B b K → ∀ k ∈ K, ∀ (v : Pl (F := F)) (i j : Fin n ⊕ Fin n), absFin F v (compFin F E v (inFrame b k i j)) ≤ 1 := by
  intro F E _ _ _ _ _ σ n Y B b K hK k hk v i j
  have h : GlobalTheory.ThK.Dbl.finOne F • GlobalTheory.ThK.Dbl.inFrame b k i j ∈ GlobalTheory.ThK.Dbl.intHat F E :=
    ((hK k).1 hk).2 k (by simp) i j
  have h' := absFin_compFin_le_one h v
  rwa [compFin_finOne_smul'] at h'

end GlobalTheory.CompanionTheory.GodementH.StdInt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND

section Adelic

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def starN (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (b : HermR (AF F) σ n) : ℂ :=
  ∫ X, Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) ∂dx

def coefN (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E) : ℂ :=
  ∫ b, starN σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace (T.map (inclR (AF F)) * (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) ∂db

end Adelic

section Glue

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tupOf {D : D7} {m r : ℕ} (X : Fin r → Fin m → AE D) : Mx D m r := Matrix.of fun i a => X a i

def thetaPartD {D : D7} (V : HSp D) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) {r : ℕ}
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ∫ X, φ (tupOf X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram μH 𝓕
    {X : Fin r → Fin V.rank → D.host.E | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1})

end Glue

end GlobalTheory.CompanionTheory.SiegelND
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentityStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_box_integral_vanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ), Continuous ψ → HasConductor ψ c → ∀ (m : ℕ) (t : kˣ) (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ), IsCompact M → MeasurableSet M → Continuous f → (∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) → ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists | exact GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists | (intros; apply GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists <;> assumption)
end

