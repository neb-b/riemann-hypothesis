module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaResidue

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisedComparison
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RegCompare

variable {D : D7}

def wop {M X : HSp D} (ω : WRep M X) (z : GA D M →₀ ℂ) : Module.End ℂ (WO M X → ℂ) := z.sum fun k c => c • ω (k, 1)

section Lin

variable {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M))

theorem thetaKO_add (g : GA D M) (h : GA D X) (Φ Ψ : WO M X → ℂ) :
    thetaKO ω g h (Φ + Ψ) = thetaKO ω g h Φ + thetaKO ω g h Ψ := by
  simp [thetaKO, map_add (f := _)]

theorem thetaKO_smul (g : GA D M) (h : GA D X) (c : ℂ) (Φ : WO M X → ℂ) :
    thetaKO ω g h (c • Φ) = c * thetaKO ω g h Φ := by
  simp [thetaKO, map_smul]

theorem thetaKO_sum {ι : Type} (s : Finset ι) (g : GA D M) (h : GA D X) (Φ : ι → WO M X → ℂ) :
    thetaKO ω g h (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaKO ω g h (Φ i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [thetaKO, map_sum, Finset.sum_apply]

theorem thetaKO_right (g k : GA D M) (h : GA D X) (Φ : WO M X → ℂ) :
    thetaKO ω g h (ω (k, 1) Φ) = thetaKO ω (g * k) h Φ := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul]
  simp

def Intg (Φ : WO M X → ℂ) : Prop := ∀ h : GA D X, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν

variable {ω ν 𝓕}

theorem Intg.add {Φ Ψ : WO M X → ℂ} (hΦ : Intg ω ν 𝓕 Φ) (hΨ : Intg ω ν 𝓕 Ψ) : Intg ω ν 𝓕 (Φ + Ψ) := fun h => by
  simp only [thetaKO_add]; exact Integrable.add (hΦ h) (hΨ h)

theorem Intg.smul {Φ : WO M X → ℂ} (c : ℂ) (hΦ : Intg ω ν 𝓕 Φ) : Intg ω ν 𝓕 (c • Φ) := fun h => by
  simp only [thetaKO_smul]; exact Integrable.const_mul (hΦ h) c

theorem Intg.sub {Φ Ψ : WO M X → ℂ} (hΦ : Intg ω ν 𝓕 Φ) (hΨ : Intg ω ν 𝓕 Ψ) : Intg ω ν 𝓕 (Φ - Ψ) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ]; exact hΦ.add (hΨ.smul _)

theorem Intg.sum {ι : Type} (s : Finset ι) {Φ : ι → WO M X → ℂ} (hΦ : ∀ i ∈ s, Intg ω ν 𝓕 (Φ i)) :
    Intg ω ν 𝓕 (∑ i ∈ s, Φ i) := fun h => by
  simp only [thetaKO_sum]
  exact integrable_finsetSum s fun i hi => hΦ i hi h

theorem intg_of_modInt {θ : InfFam D} {Φ : WO M X → ℂ} (hΦ : ModInt θ ω ν 𝓕 Φ) : Intg ω ν 𝓕 Φ := by
  obtain ⟨N, C, hC⟩ := hΦ
  exact fun h => (hC h).1

variable (ω ν 𝓕)

theorem thetaInt_smul (c : ℂ) (Φ : WO M X → ℂ) : thetaInt ω ν 𝓕 (c • Φ) = c • thetaInt ω ν 𝓕 Φ := by
  funext h
  simp only [thetaInt, thetaKO_smul, integral_const_mul, Pi.smul_apply, smul_eq_mul]

variable {ω ν 𝓕}

theorem thetaInt_add {Φ Ψ : WO M X → ℂ} (hΦ : Intg ω ν 𝓕 Φ) (hΨ : Intg ω ν 𝓕 Ψ) :
    thetaInt ω ν 𝓕 (Φ + Ψ) = thetaInt ω ν 𝓕 Φ + thetaInt ω ν 𝓕 Ψ := by
  funext h
  simp only [thetaInt, thetaKO_add, Pi.add_apply]
  exact integral_add (hΦ h) (hΨ h)

theorem thetaInt_sub {Φ Ψ : WO M X → ℂ} (hΦ : Intg ω ν 𝓕 Φ) (hΨ : Intg ω ν 𝓕 Ψ) :
    thetaInt ω ν 𝓕 (Φ - Ψ) = thetaInt ω ν 𝓕 Φ - thetaInt ω ν 𝓕 Ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, thetaInt_add hΦ (hΨ.smul _), thetaInt_smul, neg_one_smul, sub_eq_add_neg]

theorem thetaInt_sum {ι : Type} (s : Finset ι) {Φ : ι → WO M X → ℂ} (hΦ : ∀ i ∈ s, Intg ω ν 𝓕 (Φ i)) :
    thetaInt ω ν 𝓕 (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaInt ω ν 𝓕 (Φ i) := by
  funext h
  simp only [thetaInt, thetaKO_sum, Finset.sum_apply]
  exact integral_finsetSum s fun i hi => hΦ i hi h

end Lin

theorem setIntegral_mul_right' (V : HSp D) (ν : Measure (GA D V)) [hH : ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (hint : IntegrableOn F fd ν) (k : GA D V) :
    IntegrableOn (fun u => F (u * k)) fd ν ∧ ∫ u in fd, F (u * k) ∂ν = ∫ u in fd, F u ∂ν := by
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V ν hH
  have hmp : MeasurePreserving (fun x : GA D V => x * k⁻¹) ν ν := measurePreserving_mul_right ν k⁻¹
  have ht : IsFundamentalDomain (GQ V) ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν :=
    hfd.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
  have hinv : ∀ (g : GQ V) (x : GA D V), F (g • x) = F x := fun g x => hF g g.2 x
  have hmp2 : MeasurePreserving (fun x : GA D V => x * k) ν ν := measurePreserving_mul_right ν k
  have hpre : (fun x : GA D V => x * k) ⁻¹' ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) = fd := by
    ext x; simp
  have hemb : MeasurableEmbedding (fun x : GA D V => x * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have h1 : IntegrableOn F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν := (hfd.integrableOn_iff ht hinv).1 hint
  have e1 : ∫ u in fd, F (u * k) ∂ν = ∫ u in (fun x : GA D V => x * k⁻¹) ⁻¹' fd, F u ∂ν := by
    have := hmp2.setIntegral_preimage_emb hemb F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd)
    rw [hpre] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [← hpre]
    exact (hmp2.integrableOn_comp_preimage hemb).2 h1
  · rw [e1]; exact (hfd.setIntegral_eq ht hinv).symm

theorem modInt_right {θ : InfFam D} {M X : HSp D} {ω : WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : ModInt θ ω ν 𝓕 Φ) (k : GA D M) :
    ModInt θ ω ν 𝓕 (ω (k, 1) Φ) ∧ thetaInt ω ν 𝓕 (ω (k, 1) Φ) = thetaInt ω ν 𝓕 Φ := by
  haveI := hν.1
  obtain ⟨N, C, hC⟩ := hΦ
  have key := fun h => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => thetaKO ω g h Φ)
    (fun γ hγ u => hL γ hγ u h) (hC h).1 k
  have keyn := fun h => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => ((‖thetaKO ω g h Φ‖ : ℝ) : ℂ))
    (fun γ hγ u => by simp only [hL γ hγ u h]) (hC h).1.norm.ofReal k
  refine ⟨⟨N, C, fun h => ⟨?_, ?_⟩⟩, ?_⟩
  · simpa only [thetaKO_right] using (key h).1
  · have e : ∫ g in 𝓕, ‖thetaKO ω g h (ω (k, 1) Φ)‖ ∂ν = ∫ g in 𝓕, ‖thetaKO ω g h Φ‖ ∂ν := by
      have := (keyn h).2
      simp only [integral_complex_ofReal] at this
      simpa only [thetaKO_right] using Complex.ofReal_injective this
    rw [e]; exact (hC h).2
  · funext h
    simp only [thetaInt, thetaKO_right]
    exact (key h).2

theorem wop_apply {M X : HSp D} (ω : WRep M X) (z : GA D M →₀ ℂ) (Φ : WO M X → ℂ) :
    wop ω z Φ = ∑ k ∈ z.support, z k • ω (k, 1) Φ := by
  simp [wop, Finsupp.sum, LinearMap.sum_apply]

theorem wop_mem {M X : HSp D} {ω : WRep M X} {S : Submodule ℂ (WO M X → ℂ)} (hS : ∀ g ∈ GfC M, ∀ Φ ∈ S, ω (g, 1) Φ ∈ S)
    {z : GA D M →₀ ℂ} (hz : ∀ k ∈ z.support, k ∈ GfC M) {Φ : WO M X → ℂ} (hΦ : Φ ∈ S) : wop ω z Φ ∈ S := by
  rw [wop_apply]
  exact S.sum_mem fun k hk => S.smul_mem _ (hS k (hz k hk) Φ hΦ)

theorem thetaInt_wop {θ : InfFam D} {M X : HSp D} {ω : WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : ModInt θ ω ν 𝓕 Φ) (z : GA D M →₀ ℂ) :
    Intg ω ν 𝓕 (wop ω z Φ) ∧ thetaInt ω ν 𝓕 (wop ω z Φ) = GlobalTheory.FunObj.zdeg z • thetaInt ω ν 𝓕 Φ := by
  have hk := fun k => modInt_right hν hL hΦ k
  rw [wop_apply]
  refine ⟨Intg.sum _ fun k _ => (intg_of_modInt (hk k).1).smul _, ?_⟩
  rw [thetaInt_sum _ fun k _ => (intg_of_modInt (hk k).1).smul _]
  simp only [thetaInt_smul, (hk _).2, GlobalTheory.FunObj.zdeg, Finsupp.sum, Finset.sum_smul]

end GlobalTheory.RegCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.EqFin

theorem liftPure_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hφv : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    GlobalTheory.TripleAssembly.liftPure M pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  have H := GlobalTheory.PureLift.exists_pureLift σ Y Z M ψ hM P pr N pv s hs
  unfold GlobalTheory.TripleAssembly.liftPure
  rw [dite_eq_left H]
  exact H.choose_spec f φ hφ hφv

theorem darbAlg_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) (hM : M.IsGood ψ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v)
    (O : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (T₀ : Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s))
    (hgen : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
        O (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ ∧
        GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ₁ v)) = T₀ (GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)))) :
    ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ, O Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ ∧
      GlobalTheory.TripleAssembly.liftPure M pr pv s (O Ψ) = LinearMap.lTensor P T₀ (GlobalTheory.TripleAssembly.liftPure M pr pv s Ψ) := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hφv, rfl⟩ := hx
    obtain ⟨φ₁, h1, h1v, hO, hT⟩ := hgen f φ hφ hφv
    refine ⟨?_, ?_⟩
    · rw [hO]; exact Submodule.subset_span ⟨f, φ₁, hf, h1, h1v, rfl⟩
    · rw [hO, liftPure_pure M ψ hM pr pv s hs f φ₁ h1 h1v, liftPure_pure M ψ hM pr pv s hs f φ hφ hφv,
        LinearMap.lTensor_tmul, hT]
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · rw [map_add (f := _)]; exact Submodule.add_mem _ hx.1 hy.1
    · simp only [map_add (f := _), hx.2, hy.2]
  | smul c x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [map_smul]; exact Submodule.smul_mem _ c hx.1
    · simp only [map_smul, hx.2]

end GlobalTheory.TripleAssembly.EqFin

namespace GlobalTheory.TripleAssembly.EqFin


end GlobalTheory.TripleAssembly.EqFin

end
end

