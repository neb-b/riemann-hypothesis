module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Classical

namespace GlobalTheory.DefiniteDecomp

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem pairwise_commute {θ : InfFam D} {V : HSp D} {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ((Finset.univ : Finset D.what₂.Tau) : Set D.what₂.Tau).Pairwise
      (Function.onFun Commute fun τ => atTau θ V τ (g τ)) :=
  fun τ _ τ' _ hne => GlobalTheory.PointAtPlaceComm.atTau_comm D θ h.1 V τ τ' hne _ (h.2 τ) _ (h.2 τ')

def realProd (θ : InfFam D) (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  if h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then
    Finset.univ.noncommProd (fun τ => atTau θ V τ (g τ)) (pairwise_commute h)
  else 1

variable {θ : InfFam D} {V : HSp D}

theorem update_mem {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) (τ : D.what₂.Tau) :
    Function.update g τ₀ g' τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  by_cases h : τ = τ₀
  · subst h; rw [Function.update_self]; exact hg'
  · rw [Function.update_of_ne h]; exact hg τ

theorem realProd_update (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    realProd θ V (Function.update g τ₀ g') = atTau θ V τ₀ g' * realProd θ V (Function.update g τ₀ 1) := by
  classical
  have h1 := update_mem hg τ₀ hg'
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dite_eq_left ⟨hθ, h1⟩, dite_eq_left ⟨hθ, h2⟩, ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀),
    ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀) (fun τ => atTau θ V τ (Function.update g τ₀ 1 τ))]
  simp only [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ, one_mul]
  congr 1
  refine Finset.noncommProd_congr rfl (fun τ hτ => ?_) _
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ), Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem realProd_commute (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    Commute (atTau θ V τ₀ g') (realProd θ V (Function.update g τ₀ 1)) := by
  classical
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dite_eq_left ⟨hθ, h2⟩]
  refine Finset.noncommProd_commute _ _ _ _ fun τ _ => ?_
  by_cases h : τ = τ₀
  · subst h
    rw [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ]
    exact Commute.one_right _
  · exact GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ₀ τ (Ne.symm h) _ hg' _ (h2 τ)

theorem realProd_one (hθ : IsInfFam θ) : realProd θ V (fun _ => 1) = 1 := by
  unfold realProd
  rw [dite_eq_left ⟨hθ, fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _⟩]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun τ _ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ, one_pow]

theorem isAutFunSm_realProd (hθ : IsInfFam θ) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V (rTr V (realProd θ V g) φ) := by
  unfold realProd
  split_ifs with h
  · refine Finset.noncommProd_induction _ _ _ (fun x => ∀ ψ, IsAutFunSm θ V ψ → IsAutFunSm θ V (rTr V x ψ))
      (fun a b ha hb ψ hψ => ?_) (fun ψ hψ => ?_) (fun τ _ ψ hψ => ?_) φ hφ
    · have e : rTr V (a * b) ψ = rTr V a (rTr V b ψ) := funext fun x => by simp only [rTr, mul_assoc]
      rw [e]; exact ha _ (hb _ hψ)
    · have e : rTr V 1 ψ = ψ := funext fun x => by simp only [rTr, mul_one]
      rw [e]; exact hψ
    · exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V ψ hψ τ _ (h.2 τ)
  · have e : rTr V 1 φ = φ := funext fun x => by simp only [rTr, mul_one]
    rw [e]; exact hφ

theorem rep_mul {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (g * h) = (M.rep τ g).comp (M.rep τ h) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have e : M.fr τ * (g * h) * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * h * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  unfold DSModel.rep
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg) _
    (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hh)

theorem rep_one {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem sm_eq_top {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] :
    M.sm τ = ⊤ := by
  rw [GlobalTheory.SmVec.sm_eq]
  refine Submodule.orthogonal_eq_bot_iff.1 ((Submodule.eq_bot_iff _).2 fun y hy => ?_)
  exact GlobalTheory.SmVec.eq_zero_of_inner_smooth (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    fun u hu => (Submodule.mem_orthogonal _ _).1 hy u hu

theorem equiv_one {H G : Type} [AddCommGroup H] [Module ℂ H] [Module.Free ℂ H] [Module.Finite ℂ H] [Mul G]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    {m : ℕ} (k : Fin m → G) (hk : ∀ j, k j ∈ K) (B : Fin m → (H →ₗ[ℂ] H))
    (hB : ∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j)
    (f : G → ℂ) (hf : ∀ g ∈ K, f g = ∑ j, f (k j) * LinearMap.trace ℂ H (ρ g ∘ₗ B j))
    (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K) (e : H →ₗ[ℂ] ℂ) (v : H) {h : G} (hh : h ∈ K) :
    ∑ j, e (B j (ρ h v)) * f (k j) = ∑ j, e (B j v) * f (h * k j) := by
  have e1 : ∀ j, f (h * k j) = ∑ i, f (k i) * LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) := by
    intro j
    rw [hf _ (hmul _ hh _ (hk j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hρ _ hh _ (hk j), LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have e2 : ∀ i, e (B i (ρ h v)) = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) * e (B j v) := by
    intro i
    have := congrArg (fun L : H →ₗ[ℂ] H => e (L v)) (hB i h hh)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, smul_eq_mul] at this
    exact this
  simp only [e1, e2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.DefiniteDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOfMemGKModuleGeneratedBy
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKGenKFin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def kGrp : Subgroup (GA D V) :=
  Subgroup.closure {k | ∃ τ g, GlobalTheory.CuspGK.InK M τ g ∧ k = atTau θ V τ g}

theorem kGrp_le : kGrp θ M ≤ GinfC V :=
  (Subgroup.closure_le _).2 fun _ ⟨τ, g, _, e⟩ => e ▸ GlobalTheory.FinTranslate.atTau_mem θ V τ g

theorem rTr_mul (x y : GA D V) (f : GA D V → ℂ) : rTr V (x * y) f = rTr V x (rTr V y f) := by
  funext g
  simp only [rTr, mul_assoc]

theorem rTr_inv_rTr (x : GA D V) (f : GA D V → ℂ) : rTr V x⁻¹ (rTr V x f) = f := by
  funext g
  simp only [rTr, inv_mul_cancel_right]

theorem rTr_mem_of_kStable {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W)
    (hK : GlobalTheory.KTypeProj.KStable θ M W) {k : GA D V} (hk : k ∈ kGrp θ M) : ∀ f ∈ W, rTr V k f ∈ W := by
  refine Subgroup.closure_induction (p := fun k _ => ∀ f ∈ W, rTr V k f ∈ W) (fun x hx => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hk
  · obtain ⟨τ, g, hg, rfl⟩ := hx
    exact hK τ g hg
  · intro f hf
    have e : rTr V 1 f = f := funext fun g => by simp [rTr]
    rw [e]
    exact hf
  · intro f hf
    rw [rTr_mul]
    exact hx _ (hy f hf)
  · let T : W →ₗ[ℂ] W := ((GlobalTheory.KTypeProj.rTrL x).restrict (p := W) (q := W) fun f hf => hx f hf)
    have hinj : Function.Injective T := by
      intro a b hab
      apply Subtype.ext
      have h1 : rTr V x a.1 = rTr V x b.1 := congrArg Subtype.val hab
      have h2 := congrArg (rTr V x⁻¹) h1
      rwa [rTr_inv_rTr, rTr_inv_rTr] at h2
    have hsurj := LinearMap.injective_iff_surjective.1 hinj
    intro f hf
    obtain ⟨h, hh⟩ := hsurj ⟨f, hf⟩
    have e : rTr V x h.1 = f := congrArg Subtype.val hh
    rw [← e, rTr_inv_rTr]
    exact h.2

theorem isKFinite_smul {Φ : GA D V → ℂ} {K : Subgroup (GA D V)} (h : GlobalTheory.Doubling.IsKFinite K Φ) (c : ℂ) :
    GlobalTheory.Doubling.IsKFinite K (c • Φ) := by
  obtain ⟨W, hW, hm⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  exact GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => by
    exact W.smul_mem c (hm k hk)⟩

def kfinSm (hθ : IsInfFam θ) : Submodule ℂ (GA D V → ℂ) where
  carrier := {x | IsAutFunSm θ V x ∧ GlobalTheory.Doubling.IsKFinite (kGrp θ M) x}
  zero_mem' := ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add h.1 h'.1, h.2.add h'.2⟩
  smul_mem' := fun c _ h => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c h.1, isKFinite_smul h.2 c⟩

theorem exists_kStable {x : GA D V → ℂ} (h : GlobalTheory.Doubling.IsKFinite (kGrp θ M) x) :
    ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧ GlobalTheory.KTypeProj.KStable θ M Y := by
  refine ⟨GlobalTheory.Doubling.kSpan (kGrp θ M) x, h, Submodule.subset_span ⟨1, one_mem _, funext fun g => by simp⟩, ?_⟩
  intro τ g hg f hf
  have ha : atTau θ V τ g ∈ kGrp θ M := Subgroup.subset_closure ⟨τ, g, hg, rfl⟩
  have hle : GlobalTheory.Doubling.kSpan (kGrp θ M) x ≤
      (GlobalTheory.Doubling.kSpan (kGrp θ M) x).comap (GlobalTheory.KTypeProj.rTrL (atTau θ V τ g)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine Submodule.subset_span ⟨atTau θ V τ g * k, mul_mem ha hk, ?_⟩
    funext y
    simp only [GlobalTheory.KTypeProj.rTrL_apply, rTr, mul_assoc]
  exact hle hf

theorem isGKSub_kfinSm (hθ : IsInfFam θ) : GlobalTheory.CuspGK.IsGKSub θ M (kfinSm θ M hθ) := by
  constructor
  · intro τ g hg f hf
    exact ⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf.1 τ g hg.1,
      hf.2.translate (Subgroup.subset_closure ⟨τ, g, hg, rfl⟩)⟩
  · intro τ X hX f hf
    exact ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf.1,
      GlobalTheory.CuspLie.isKFinite_Rder hθ hX (kGrp_le θ M) hf.1.smooth hf.2⟩

theorem kFinite_of_mem_gkGen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ,
    IsAutFunSm θ V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ GlobalTheory.KTypeProj.KStable θ M W) →
    ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧
      GlobalTheory.KTypeProj.KStable θ M Y := by
  intro D θ V S M hθ ψ hψ ⟨W, hW, hψW, hK⟩ x hx
  have hm : ψ ∈ kfinSm θ M hθ :=
    ⟨hψ, GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => rTr_mem_of_kStable θ M hW hK hk ψ hψW⟩⟩
  exact exists_kStable θ M (GlobalTheory.CuspGK.gkGen_le θ M hm (isGKSub_kfinSm θ M hθ) hx).2

end GlobalTheory.GKGenKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem cartan_eq_one {k : ℕ} {A s : Matrix (Fin k) (Fin k) ℂ} (hA : A.PosDef) (h : IsCartanInv A s) : s = 1 := by
  obtain ⟨h1, -, h3⟩ := h
  have hs : ∀ v : Fin k → ℂ, (s - 1) *ᵥ v = 0 := by
    intro v
    by_contra hw
    have hsw : s *ᵥ ((s - 1) *ᵥ v) = -((s - 1) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, Matrix.mul_one, ← Matrix.neg_mulVec, neg_sub]
    have p1 := h3.dotProduct_mulVec_pos hw
    have p2 := hA.dotProduct_mulVec_pos hw
    rw [← Matrix.mulVec_mulVec, hsw, Matrix.mulVec_neg, dotProduct_neg] at p1
    have := add_pos p1 p2
    rw [neg_add_cancel] at this
    exact lt_irrefl _ this
  ext i j
  have := congrFun (hs (Pi.single j 1)) i
  simpa [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_apply] using this

theorem negGA_mem_GinfC (V : HSp D) {g : GA D V} (hg : g ∈ GinfC V) : negGA V g ∈ GinfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GinfC, MonoidHom.mem_ker, finHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

def sgnP : Pair T → ℚ
  | .chi _ _ => -1
  | .core _ => -1
  | _ => 1

def realChar (W : G.Weil) (p : Pair T) (e₁ e₂ : D.what₂.Tau → ℤ) (k : GA D (G.V p.small)) (k' : GA D (G.V p.big)) : ℂ :=
  ∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) (G.toPair p k k').1)).det ^ e₂ τ *
    (compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (G.toPair p k k').2)).det ^ e₁ τ

def realSubst (W : G.Weil) (B : VertexFrames G) (p : Pair T) (k : GA D (G.V p.small)) (k' : GA D (G.V p.big)) :
    PolF D (G.pT p).rank (G.pS p).rank →ₐ[ℂ] PolF D (G.pT p).rank (G.pS p).rank :=
  GlobalTheory.CompactHowe.substF
    (fun τ => ((G.onT B p τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (G.toPair p k k').2) * G.onT B p τ).map (opp p))
    (fun τ => ((((G.onS B p τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) (G.toPair p k k').1) * G.onS B p τ)⁻¹)ᵀ).map (opp p))

theorem ker_mul (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p F (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') F) g h := by
  have e : G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
    cases p <;> simp [GridData.toPair, map_mul, Prod.ext_iff]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem cart_def {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {X : Node} (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    W.cart X τ = 1 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨hi, rfl⟩ := hX
    exact cartan_eq_one (posDef_grid hL hi (tauE D τ)) (W.cart_is (.grid i D.R.m) (show i ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨hi, le_rfl⟩) τ)
  · exact hX.elim
  · exact cartan_eq_one (posDef_top G hX (tauE D τ)) (W.cart_is (.top j) (show j ≤ D.R.m from hX) τ)

theorem om_fockIn {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : VertexFrames G) {p : Pair T} (hp : DefPair D.R.m p)
    (hB : ∀ X, DefNode D.R.m X → ∀ τ, (B X τ)ᴴ * gramAt D (G.V X) τ * B X τ = 1)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f)
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.om p (G.toPair p k k') (fockIn W B p f Q) = realChar W p e₁ e₂ k k' • fockIn W B p f (realSubst W B p k k' Q) := by
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  cases p with
  | top t j =>
    have c1 : W.cart (.top j) = fun _ => 1 := funext (cart_def hL W hn.1)
    have c2 : W.cart (.top (j + 1)) = fun _ => 1 := funext (cart_def hL W hn.2)
    simp only [fockIn, GridData.cartS, GridData.onT, GridData.onS, c1, c2] at hv ⊢
    have := _root_.GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ _ _ _ _ (W.om (.top t j)) hom W.θ_is (B (.top j)) (B (.top (j + 1))) (hB _ hn.1)
      (hB _ hn.2) a b ha hb e₁ e₂ (fun τ => by rw [he₁]; simp [sgnP]) (fun τ => by rw [he₂]; simp [sgnP]) f hf hv k hk k' hk' Q
    simp only [GridData.toPair]
    rw [this]
    rfl
  | chi i j =>
    have c1 : W.cart (.grid (i + 1) j) = fun _ => 1 := funext (cart_def hL W hn.2)
    have c2 : W.cart (.grid i j) = fun _ => 1 := funext (cart_def hL W hn.1)
    simp only [fockIn, GridData.cartS, GridData.onT, GridData.onS, c1, c2] at hv ⊢
    have := _root_.GlobalTheory.FockRealNeg.om_pureTensorO_neg D W.ψ W.θ _ _ _ _ (W.om (.chi i j)) hom W.θ_is (B (.grid (i + 1) j)) (B (.grid i j)) (hB _ hn.2)
      (hB _ hn.1) a b ha hb e₁ e₂ (fun τ => by rw [he₁]; simp [sgnP]; ring) (fun τ => by rw [he₂]; simp [sgnP]; ring) f hf hv
      _ (negGA_mem_GinfC _ hk') k hk Q
    simp only [GridData.toPair]
    rw [this]
    rfl
  | mu t i j => exact hp.elim
  | core i => exact hp.elim

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem onb_def {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {X : Node} (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    (W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ = 1 := by
  have hR : X.InRange D.R.m := by
    rcases X with ⟨i, j⟩ | i | j
    · exact show i ≤ D.R.m ∧ j ≤ D.R.m from ⟨hX.1, hX.2.le⟩
    · exact hX.elim
    · exact hX
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hR τ
  rw [cart_def hL W hX, Matrix.one_mul] at h2
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  calc (W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ
      = (W.onb X τ)ᴴ * gramAt D (G.V X) τ * (W.onb X τ * Formalism.REAL.Jm ε) := by rw [← h2]
    _ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [← Matrix.mul_assoc, h1]
    _ = 1 := hJ

theorem ker_fockIn_real {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : VertexFrames G) {p : Pair T} (hp : DefPair D.R.m p)
    (hB : ∀ X, DefNode D.R.m X → ∀ τ, (B X τ)ᴴ * gramAt D (G.V X) τ * B X τ = 1)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f)
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p (fockIn W B p f Q) (g * k) (h * k') =
      realChar W p e₁ e₂ k k' * W.ker p (fockIn W B p f (realSubst W B p k k' Q)) g h := by
  rw [ker_mul, om_fockIn hL W B hp hB a b ha hb e₁ e₂ he₁ he₂ f hf hv k hk k' hk' Q]
  simp only [GridData.Weil.ker, thetaKO, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]

theorem ker_fock_moved_real {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) {p : Pair T}
    (hp : DefPair D.R.m p) (d : FinDatum G t p) (hd : S.Z.HasVec d)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p (W.fock p (GlobalTheory.RowClaim.movedVec t S d) Q) (g * k) (h * k') =
      realChar W p e₁ e₂ k k' * W.ker p (W.fock p (GlobalTheory.RowClaim.movedVec t S d) (realSubst W W.onb p k k' Q)) g h := by
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd
  have mem : (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).1 ∈ GfC (G.pS p) ∧
      (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | mu t i j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
    | core i => exact ⟨negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | top t j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.FockRealMove.om_fin_fockVac D W.ψ W.θ _ _ _ _ (W.om p) hom W.θ_is _ _ _ h1 h2 _ mem.1 _ mem.2
  exact ker_fockIn_real hL W W.onb hp (fun X hX τ => onb_def hL W hX τ) a b ha hb e₁ e₂ he₁ he₂ _ h3 h4 k hk k' hk' Q g h

end GlobalTheory.FockReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesCartanDoubleCosetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_integralMatrices_cartanDouble_coset : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) (ϖ : v.adicCompletion F), IsUnifV F v ϖ → ∀ (d : Fin m → ℤ) (t : GL (Fin m) (v.adicCompletion F)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL v (n := m), ∀ k₂ ∈ KGL v (n := m), (GlobalTheory.SplitIdx.intMat F v m n).relIndex ((GlobalTheory.SplitIdx.intMat F v m n).map (GlobalTheory.SplitIdx.mulL (n := n) (k₁ * t * k₂).1)) = qV F v ^ (n * (∑ i, max (-d i) 0).toNat) := by
  first | exact @GlobalTheory.SplitIdx.LocIndex.relIndex_intMat | exact GlobalTheory.SplitIdx.LocIndex.relIndex_intMat | (intros; apply GlobalTheory.SplitIdx.LocIndex.relIndex_intMat <;> assumption)
end

