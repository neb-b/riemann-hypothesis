module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.LocalWeilOps

theorem comm_off_V {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : Pl (F := F)) (x : UA σ Γ.V.J) (hx : x ∈ UAt σ Γ.V (evFin F v)) :
    ∀ u : AF F, evFin F v u = 0 → ∀ p q : Fin a × Fin (a + a') → AF F,
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')),
      om (x, 1) (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (om (x, 1) Φ) := by
  intro u hu p q Φ hΦ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set w := Γ.M.co.e.symm (p, q) with hw
  have he : Γ.M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1) = 0 := hx u hu
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((x, 1) : UA σ Γ.V.J × UA σ Γ.W.J) (u • w) = u • w := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h0, Matrix.zero_mul, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] using h1
  have h2 := hW.impl (x, 1) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem locality_V {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : Pl (F := F)) (x : UA σ Γ.V.J) (hx : x ∈ UAt σ Γ.V (evFin F v)) :
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (x, 1)) φ φ₁ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set T := om (x, 1) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (x, 1) Φ hΦ
  have hcomm := comm_off_V Bs Γ X om om' hTr v x hx
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v Bs.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace Bs.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (x, 1) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, GlobalTheory.WeilLocality.schr_trans, GlobalTheory.WeilLocality.schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  intro φ hφ
  refine ⟨fun t => (R 0)⁻¹ * T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.WeilLocality.liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (_root_.GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef]
    field_simp

theorem read_off {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl (F := F)) (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i) : κ → AF F) := by
    intro u' hu'
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hR := hRi 0 _ hz
  rw [zero_add] at hR
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  exact read_off v R hR0 (hR φ hφ).1 φ₁ φ₂ ((h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ)))

theorem acts_comp {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₁ : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T₁ Φ ∈ GlobalTheory.WeilM.schA F κ)
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (h1 : Acts (evFin F v) T₁ φ φ₁) (h2 : Acts (evFin F v) T₂ φ₁ φ₂) :
    Acts (evFin F v) (T₂ * T₁) φ φ₂ := by
  intro r hr
  have e1 := h1 r hr
  have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, e1 ▸ hT₁ _ hr.2⟩
  rw [Module.End.mul_apply, e1, h2 r hr1]

theorem local_ops : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J),
      (∀ g, (j g).1 ∈ UAt σ G.V (evFin F v) ∧ (j g).2 ∈ UAt σ G.W (evFin F v)) →
      ∃ ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)), ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v))
        (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v Γ _ j hj
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  have hkeep : ∀ g, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om g Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun g Φ hΦ => hW.pres g Φ hΦ
  have hsplit : ∀ g, om (j g) = om ((j g).1, 1) * om (1, (j g).2) := by
    intro g
    rw [← map_mul]
    congr 1
    simp [Prod.mk_mul_mk]
  have hex : ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ := by
    intro g φ
    obtain ⟨φ₁, h₁, a₁⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hTr v (j g).2 (hj g).2 φ φ.2
    obtain ⟨φ₂, h₂, a₂⟩ := locality_V B G X om om' hTr v (j g).1 (hj g).1 φ₁ h₁
    refine ⟨φ₂, h₂, ?_⟩
    rw [hsplit g]
    exact acts_comp v _ _ (hkeep _) a₁ a₂
  choose S hS hA using hex
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  have hRi := (hR 0 (Submodule.zero_mem _)).1
  have hadd : ∀ g (φ φ' : SB (Fin a × Fin (a + a') → Fv F v)), S g (φ + φ') = S g φ + S g φ' := by
    intro g φ φ'
    apply read_off v R hR0 hRi
    have e1 := hA g (φ + φ') R (hR _ (φ + φ').2)
    have e2 := hA g φ R (hR _ φ.2)
    have e3 := hA g φ' R (hR _ φ'.2)
    have t1 : ∀ ψ₁ ψ₂ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
        tens (evFin F v) (ψ₁ + ψ₂) R = tens (evFin F v) ψ₁ R + tens (evFin F v) ψ₂ R := by
      intro ψ₁ ψ₂; funext x; simp [tens, add_mul]
    rw [← e1, Submodule.coe_add, t1, map_add (f := _), e2, e3, ← t1]
  have hsmul : ∀ g (c : ℂ) (φ : SB (Fin a × Fin (a + a') → Fv F v)), S g (c • φ) = c • S g φ := by
    intro g c φ
    apply read_off v R hR0 hRi
    have e1 := hA g (c • φ) R (hR _ (c • φ).2)
    have e2 := hA g φ R (hR _ φ.2)
    have t2 : ∀ ψ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
        tens (evFin F v) (c • ψ) R = c • tens (evFin F v) ψ R := by
      intro ψ; funext x; simp [tens, mul_assoc]
    rw [← e1, Submodule.coe_smul, t2, map_smul, e2, ← t2]
  let ωl : Γ → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)) := fun g =>
    { toFun := fun φ => ⟨S g φ, hS g φ⟩
      map_add' := fun φ φ' => Subtype.ext (hadd g φ φ')
      map_smul' := fun c φ => Subtype.ext (hsmul g c φ) }
  have hone : ∀ φ : SB (Fin a × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ
    refine acts_unique v _ φ.2 (hA 1 φ) ?_
    intro r hr
    rw [map_one, map_one]
    rfl
  have hmul : ∀ g h (φ : SB (Fin a × Fin (a + a') → Fv F v)), S (g * h) φ = S g ⟨S h φ, hS h φ⟩ := by
    intro g h φ
    refine acts_unique v _ φ.2 (hA (g * h) φ) ?_
    rw [map_mul, map_mul]
    exact acts_comp v _ _ (hkeep _) (hA h φ) (hA g ⟨S h φ, hS h φ⟩)
  refine ⟨{ toFun := ωl, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact LinearMap.ext fun φ => Subtype.ext (hone φ)
  · intro g h
    exact LinearMap.ext fun φ => Subtype.ext (hmul g h φ)
  · intro g φ φ₁
    constructor
    · intro hφ₁
      exact acts_unique v _ φ.2 hφ₁ (hA g φ)
    · rintro rfl
      exact hA g φ

end GlobalTheory.LocalWeilOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelic
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRead

def posSig {D : D7} (S : HSp D) : HSp D := {S with sig := fun _ => (S.rank, 0)}

theorem hasSignature_one (n : ℕ) : Formalism.UG.HasSignature (1 : Matrix (Fin n) (Fin n) ℂ) n 0 := by
  refine ⟨(Equiv.sumEmpty (Fin n) (Fin 0)).symm, 1, ?_⟩
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem sigOK_posSig {D : D7} (S : HSp D) (h : S.gram = 1) : (posSig S).SigOK := by
  intro τ
  show Formalism.UG.HasSignature (S.gram.map τ) S.rank 0
  rw [h, Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact hasSignature_one _

open scoped ComplexOrder in
theorem isCartanInv_one {D : D7} (S : HSp D) (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by
    show (HSpace.gram S).map (tauE D τ) = 1
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))⟩

theorem vac_exists_gram_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (S T : HSp D) (gS : S.gram = 1) (gT : T.gram = 1)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    ∃ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) ΛS ΛT f := by
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (posSig S) (posSig T) (fun _ => 1) (fun _ => 1)
    (sigOK_posSig S gS) (sigOK_posSig T gT) (isCartanInv_one S gS) (isCartanInv_one T gT) ΛS ΛT hS hT
  exact ⟨f, hf.1, ⟨hf.2.inf, ⟨hf.2.theta.quasi, hf.2.theta.level, hf.2.theta.cont, hf.2.theta.smooth⟩, hf.2.lat,
    hf.2.fock, hf.2.norm⟩⟩

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem Hf_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (z x : VC D a d) :
    Hf D (tor0 D D.host.ccK δ) (fun τ i j => z τ i j / embT D τ r) (fun τ i j => x τ i j / embT D τ r) =
      Hf D (tor0 D cc δ) z x := by
  have hr : r ≠ 0 := IsScale.ne_zero hc.1.1 h
  have hA := area_pos hc
  have hx := xiR_pos D
  have key : ∀ τ, Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ) = area (lamOf D cc δ) := by
    intro τ
    have h1 := normSq_scale hc.1.1 h δ τ
    have h2 := normSq_scale D.host.ccK_ne_bot (isScale_one D) δ τ
    rw [map_one, mul_one] at h2
    rw [Complex.normSq_mul, h2] at h1
    have h3 : (2 * Formalism.L2.Pj.xiR D) * (Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ)) =
        (2 * Formalism.L2.Pj.xiR D) * area (lamOf D cc δ) := by rw [← h1]; ring
    exact mul_left_cancel₀ (by positivity) h3
  have hL : ∀ c : Ideal (𝓞 D.host.K), (tor0 D c δ).abelian₂ = lamOf D c δ := fun _ => rfl
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, Formalism.MainNotions.TaylorLogMetric.Hf, hL, hL, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
  have htc : starRingEnd ℂ (embT D τ r) ≠ 0 := (map_ne_zero _).2 ht
  have hK : (area (lamOf D D.host.ccK δ) : ℂ) ≠ 0 := by
    have : 0 < area (lamOf D D.host.ccK δ) := by
      have := key τ
      have h0 : 0 < Complex.normSq (embT D τ r) := Complex.normSq_pos.2 ht
      nlinarith
    exact_mod_cast this.ne'
  rw [← key τ, map_div₀]
  push_cast
  rw [← Complex.mul_conj]
  field_simp

theorem th_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ}
    {L Ls : GlobalTheory.InertSign.Lat D a} {L' Lt : GlobalTheory.InertSign.Lat D d}
    (hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L',
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt)
    {Φ : VC D a d → ℂ} (hΦ : Φ ∈ Th D (tor0 D D.host.ccK δ) Ls Lt) :
    (fun Y => Φ (fun τ i j => Y τ i j / embT D τ r)) ∈ Th D (tor0 D cc δ) L L' := by
  refine ⟨?_, ?_⟩
  · have hl : Differentiable ℂ (fun Y : VC D a d => (fun τ i j => Y τ i j / embT D τ r : VC D a d)) := by
      fun_prop
    exact hΦ.1.comp hl
  · intro x hx z
    have e1 := hΦ.2 _ (hLa x hx) (fun τ i j => z τ i j / embT D τ r)
    have hal : Formalism.MainNotions.TaylorLogMetric.al D (tor0 D cc δ) x =
        Formalism.MainNotions.TaylorLogMetric.al D (tor0 D D.host.ccK δ) (fun τ i j => x τ i j / embT D τ r) := by
      simp only [Formalism.MainNotions.TaylorLogMetric.al, Hf_div_scale hc h]
    have hadd : (fun τ i j => (z + x) τ i j / embT D τ r) =
        (fun τ i j => z τ i j / embT D τ r) + (fun τ i j => x τ i j / embT D τ r) := by
      funext τ i j
      simp [add_div]
    show _ = Φ fun τ i j => z τ i j / embT D τ r
    rw [← e1, hal]
    simp only [Formalism.MainNotions.TaylorLogMetric.U]
    rw [Hf_div_scale hc h, Hf_div_scale hc h, hadd]

end GlobalTheory.VacRead

namespace GlobalTheory.VacRead

theorem exists_vac_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := by
  intro D ψ θ S T a d hS hT cc δ r hset
  subst hS hT
  obtain ⟨hψ, hθ, gS, gT, crv, sc⟩ := hset
  have hc : cc ≠ ⊥ := crv.1.1
  have hr : r ≠ 0 := IsScale.ne_zero hc sc
  have hδ : δ ≠ 0 := delta_ne_zero crv
  have hS1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin S.rank) D.host.E).1 * S.gram *
      (1 : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [gS]; simp [Formalism.UG.cT]
  have hT1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin T.rank) D.host.E).1 * T.gram *
      (1 : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [gT]; simp [Formalism.UG.cT]
  have hLs : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r S.rank) := _root_.GlobalTheory.VacRead.lsB_selfDual D cc r S.rank hc sc
  have hLt : Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D T.rank) := GlobalTheory.MovedVacuum.sd_stdL D T.rank
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S 1 hS1 _ hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T 1 hT1 _ hLt
  obtain ⟨f, hf⟩ := vac_exists_gram_one ψ θ hψ hθ S T gS gT ΛS ΛT hSd hTd
  rw [hΛS, hΛT] at hf
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ hS1 hT1 f hf
  have hth := theta_of_unit_vacuum ψ θ S T 1 1 hS1 hT1 δ hδ _ _ hLs hLt f hf Φ hΦd hΦ
  have hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank),
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (lsB D cc r S.rank) (stdL D T.rank) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
    have h2 := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (_root_.GlobalTheory.VacRead.rl_div_scale D cc r S.rank T.rank hc sc z hz) 1
    convert h2 using 1
    funext τ i j
    rw [one_smul, GlobalTheory.ThetaLatImage.pt_apply, GlobalTheory.ThetaLatImage.pt_apply]
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    field_simp
  have hG := th_div_scale crv sc hLa hth
  have hback : ∀ Z : VC D S.rank T.rank,
      (δ⁻¹ • fun τ i j => (δ * embT D τ r * Z τ i j) / embT D τ r : VC D S.rank T.rank) = Z := by
    intro Z
    funext τ i j
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨_, hG, ?_, f, (reads_iff crv sc _ f).2 ⟨hf.2.theta, fun w hw => ?_⟩⟩
  · intro h0
    apply GlobalTheory.StepMove.vacO_ne_zero hf
    refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf.2.theta fun w hw => ?_
    rw [hΦ w hw]
    have e := congrFun h0 (fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j)
    simp only [Pi.zero_apply, hback] at e
    rw [e, mul_zero]
  · rw [hΦ w hw]
    simp only [hback]

end GlobalTheory.VacRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpConjOfOne
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem conj_sum_zero (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (j : Fin D.R.m)
    (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _))
    (hK : (S.A ((j : ℕ) + 1)).IsKsForm) (τ : ℂ ≃+* ℂ) (hτ : ∀ y, τ (Formalism.L2.Host.embLL0 D y) = Formalism.L2.Host.embLL0 D y)
    (n : ℕ) (c : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h0 : ∑ k, c k • evW YS v₀ j (g k).val = 0) : ∑ k, τ (c k) • evW YS v₀ j (g k).val = 0 := by
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let σ : S.Ks → ℂ := fun r => D.what₂.embLL (algebraMap S.Ks D.what₂.LL r)
  have hσ : ∀ r, τ (σ r) = σ r := fun r => by
    have := hτ (S.kKs r)
    simp only [σ, ← S.kKs_spec]
    exact this
  have hg : ∀ k, evW YS v₀ j (g k).val = ∑ a, σ (bK.repr (g k) a) • φ a := fun k => by
    conv_lhs => rw [← bK.sum_repr (g k)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul D.what₂.LL, evW_smul, hbK]
  have hexp : ∀ d : Fin n → ℂ, ∑ k, d k • evW YS v₀ j (g k).val =
      ∑ a, (∑ k, d k * σ (bK.repr (g k) a)) • φ a := fun d => by
    simp only [hg, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hz : ∀ a, ∑ k, c k * σ (bK.repr (g k) a) = 0 := fun a =>
    Fintype.linearIndependent_iff.1 hφ _ ((hexp c).symm.trans h0) a
  rw [hexp]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : ∑ k, τ (c k) * σ (bK.repr (g k) a) = τ (∑ k, c k * σ (bK.repr (g k) a)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hσ]
  rw [this, hz a, map_zero, zero_smul]

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperatorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  first | exact @GlobalTheory.InertVacEquiv.heisInv_comp | exact GlobalTheory.InertVacEquiv.heisInv_comp | (intros; apply GlobalTheory.InertVacEquiv.heisInv_comp <;> assumption)
end

