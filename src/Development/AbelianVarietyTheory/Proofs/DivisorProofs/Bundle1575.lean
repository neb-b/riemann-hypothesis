module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.BotFormula

theorem toFinE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = GlobalTheory.CuspRep.conjFin (D.host.conj : D.host.E ≃+* D.host.E) (toFinE D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul x a =>
    change GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] D.host.conj x) =
      GlobalTheory.CuspRep.conjFin _ (GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] x))
    rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_mul,
      GlobalTheory.DefU.ClassFin.conjFin_adMap _ (fun q => D.host.conj.commutes q), GlobalTheory.CuspRep.conjFin_algebraMap]
    rfl

def toAfE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* TensorProduct D.host.F (Af D.host.F) D.host.E :=
  (toFinE D).trans (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm

theorem toAfE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toAfE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = sigR (Af D.host.F) D.sp.cm.sig (toAfE D y) := by
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun x => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D x)]
  simp only [toAfE, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact toFinE_sgA D y

theorem exists_isFinPt_of_gram_one : ∀ {D : D7} (WW : HSp D), WW.gram = 1 → ∀ {n : ℕ} (h : GA D n), WW.rank = n →
    ∃ g : GA D WW, GlobalTheory.BotFormula.IsFinPt WW g h := by
  intro D WW hG n h hr
  subst hr
  let x' : GL (Fin WW.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := Formalism.UG.bc (toAfE D).toRingHom h.1
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * h.1 = 1 := by
    have h2 := h.2
    change Formalism.UG.cT _ (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hx' : x' ∈ HR (Af D.host.F) D.sp.cm.sig WW.gram := by
    show Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) *
      JR (Af D.host.F) WW.gram * (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) = JR (Af D.host.F) WW.gram
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact GlobalTheory.DefU.ClassFin.unitary_map (toAfE D).toRingHom (Formalism.MainNotions.StandardLatticesGL3.sgA D) _ (toAfE_sgA D) _ hh
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue WW 1 x' (one_mem _) hx'
  refine ⟨k, k1, rfl, fun i j => ?_⟩
  rw [k2]
  exact (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _

end GlobalTheory.BotFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPlaceTranslateCombinationLatticeIndica
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

noncomputable section

namespace GlobalTheory.CombAtGood

theorem pure_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ f φ hSB hstd
  have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ := ⟨GlobalTheory.T.isLocallyConstant_finprod_schwartzBruhat_finiteAdeles φ hSB hstd, _root_.GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
  exact Submodule.subset_span ⟨f, _, hg, rfl⟩

theorem exists_translates_primFrame_conj {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {D : Type} [Fintype D] [DecidableEq D] (ν α : kˣ →* ℂˣ)
    (hν : ∀ x, ‖(ν x : ℂ)‖ = 1) {a' : ℕ} (hd : (a' : ℝ) - 1 < (Fintype.card D : ℝ) / 2)
    (Λ : Submodule 𝒪[k] (D → k)) (P : GL (Fin a') k) (c : ℂ) :
    ∃ z : GL (Fin a') k →₀ ℂ, zdeg z ≠ 0 ∧ ∀ Y : Matrix (Fin a') D k,
      (z.sum fun g c' => c' • omB ν α g 1 (fun Y => c * (matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1 (P.val * Y))) Y =
        c * {Y : Matrix (Fin a') D k | IsPrimFrame Λ Y}.indicator 1 (P.val * Y) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
  obtain ⟨z₀, h1, h2⟩ := exists_translates_eq_primFrame_lat hϖ ν α Λ a'
  let Q : GL (Fin a') k := Matrix.GeneralLinearGroup.mkOfDetNeZero P.valᵀ (by
    rw [Matrix.det_transpose]; exact P.isUnit.map Matrix.detMonoidHom |>.ne_zero)
  let cj : GL (Fin a') k → GL (Fin a') k := fun g => Q * g * Q⁻¹
  refine ⟨z₀.mapDomain cj, ?_, fun Y => ?_⟩
  · rw [zdeg, Finsupp.sum_mapDomain_index (by simp) (by simp), h2]
    exact prod_primFactor_ne_zero (hν ϖ) hd
  · have hdet : ∀ g, gdet (cj g) = gdet g := fun g => by
      simp only [cj, map_mul, map_inv]; exact mul_inv_cancel_comm _ _
    have hPQ : P.val * (Q⁻¹).valᵀ = 1 := by
      have h := congrArg Matrix.transpose (congrArg Units.val (inv_mul_cancel Q))
      rw [Units.val_mul, Matrix.transpose_mul, Units.val_one, Matrix.transpose_one] at h
      exact h
    have htr : ∀ (g : GL (Fin a') k) (Y : Matrix (Fin a') D k), P.val * ((cj g).valᵀ * Y * (1 : GL D k).val) = g.valᵀ * (P.val * Y) := by
      intro g Y
      simp only [cj, Units.val_mul, Matrix.transpose_mul, Units.val_one, Matrix.mul_one]
      have hQ : Q.valᵀ = P.val := Matrix.transpose_transpose _
      rw [hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_assoc]
    have key : ∀ g (Y : Matrix (Fin a') D k), omB ν α (cj g) 1 (fun Y => c * (matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1 (P.val * Y)) Y =
        c * omB ν α g 1 ((matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1) (P.val * Y) := by
      intro g Y
      simp only [omB]
      rw [hdet, htr, Units.val_one, Matrix.mul_one]
      ring
    rw [Finsupp.sum_mapDomain_index (f := cj) (s := z₀)
      (h := fun g (c' : ℂ) => c' • omB ν α g 1 (fun Y => c * (matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1 (P.val * Y)))
      (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _), ← h1]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring

theorem exists_comb_translates_mem_So : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (hM' : Γ.M'.IsGood B.ψ) (hlt : a' < a)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) {H : Type} (κ : H → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J)
    (ν α : (Fv F B.v₁)ˣ →* ℂˣ) (hν : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → ℂ))
    (hι : Γ.M'.IsLinBar B.ψ B.τ₁ 1 1 ι)
    (hact : ∀ g : GL (Fin a') (Fv F B.v₁), ∃ k : H, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ r →
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB _, om' (κ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₁ r ∧
        ι φ₁ = omB ν α g 1 (ι φ))
    {m : ℕ} (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (φ₀ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)
    (hSB : ∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) (h₀ : ∀ k, φ k B.v₁ = φ₀)
    (P : GL (Fin a') (Fv F B.v₁)) (Λ : Submodule 𝒪[Fv F B.v₁] (Fin (a + a') → Fv F B.v₁)) (c : ℂ)
    (hφ₀ : ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y)),
    ∃ z : H →₀ ℂ, zdeg z ≠ 0 ∧
      (z.sum fun k c => c • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k))) ∈ Γ.M'.So B.ψ B.τ₁ := by
  intro F E _ _ _ _ _ σ a a' B Γ hM' hlt om' H κ ν α hν ι hι hact m f φ φ₀ hSB hvac h₀ P Λ c hφ₀
  classical
  have hd : ((a' : ℕ) : ℝ) - 1 < (Fintype.card (Fin (a + a')) : ℝ) / 2 := by
    rw [Fintype.card_fin]; push_cast
    have : (a' : ℝ) + 1 ≤ a := by exact_mod_cast hlt
    linarith
  obtain ⟨z₁, hz₁, hz₁Y⟩ := exists_translates_primFrame_conj ν α hν hd Λ P c
  choose kf hkf using hact
  refine ⟨z₁.mapDomain kf, ?_, ?_⟩
  · rw [zdeg, Finsupp.sum_mapDomain_index (by simp) (by simp)]
    exact hz₁
  rw [Finsupp.sum_mapDomain_index (f := kf) (s := z₁)
    (h := fun k (c' : ℂ) => c' • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k)))
    (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hstd : ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    ((hvac i).and hM'.std).mono fun v h => h.1.trans h.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.T.exists_factor_pureTensor_component_at_place (B.v₁) (f i) (φ i) hstd
  have hφ₀SB : φ₀ ∈ GlobalTheory.WeilM.SB _ := h₀ i ▸ hSB i B.v₁
  have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₀ r := by
    rw [hrt, ← h₀ i, Function.update_eq_self]
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ₀ r := ⟨hr, hpure ▸ pure_mem_schA (f i) (φ i) (hSB i) hstd⟩
  have hinj := (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι).injOn
  let φ₁ : GL (Fin a') (Fv F B.v₁) → _ := fun g =>
    Function.invFunOn ι (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) : Set _) (omB ν α g 1 (ι φ₀))
  have hφ₁ : ∀ g, φ₁ g ∈ GlobalTheory.WeilM.SB _ ∧ ι (φ₁ g) = omB ν α g 1 (ι φ₀) ∧
      om' (κ (kf g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₀ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (φ₁ g) r := by
    intro g
    obtain ⟨ψ₁, hψ₁, he, hι₁⟩ := hkf g φ₀ hφ₀SB r hRest
    have hex : ∃ x ∈ (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) : Set _), ι x = omB ν α g 1 (ι φ₀) :=
      ⟨ψ₁, hψ₁, hι₁⟩
    have hm := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have h' : ψ₁ = φ₁ g := hinj hψ₁ hm (hι₁.trans heq.symm)
    exact ⟨hm, heq, h' ▸ he⟩
  set Φ₁ := ∑ g ∈ z₁.support, z₁ g • φ₁ g with hΦ₁
  have hΦ₁SB : Φ₁ ∈ GlobalTheory.WeilM.SB _ := Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hφ₁ g).1
  have htens : ∀ (s : Finset (GL (Fin a') (Fv F B.v₁))) (w : GL (Fin a') (Fv F B.v₁) → ℂ),
      ∑ g ∈ s, w g • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (φ₁ g) r =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (∑ g ∈ s, w g • φ₁ g) r := by
    intro s w
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  have hsum : ∑ g ∈ z₁.support, z₁ g • om' (κ (kf g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (Function.update (φ i) B.v₁ Φ₁) := by
    rw [← hrt, hpure, ← htens]
    exact Finset.sum_congr rfl fun g _ => by rw [(hφ₁ g).2.2]
  rw [hsum]
  refine Submodule.subset_span ⟨f i, Function.update (φ i) B.v₁ Φ₁, fun v => ?_, ?_, ?_, rfl⟩
  · by_cases hv : v = B.v₁
    · subst hv; rw [Function.update_self]; exact hΦ₁SB
    · rw [Function.update_of_ne hv]; exact hSB i v
  · filter_upwards [hvac i, Filter.eventually_cofinite_ne B.v₁] with v h1 h2
    rw [Function.update_of_ne h2, h1]
  · rw [Function.update_self]
    refine ⟨hΦ₁SB, ι, hι, fun Y hY => ?_⟩
    have hιΦ : ι Φ₁ = ∑ g ∈ z₁.support, z₁ g • omB ν α g 1 (ι φ₀) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΦ₁, map_sum]
      exact Finset.sum_congr rfl fun g _ => by rw [map_smul, (hφ₁ g).2.1]
    have hιφ₀ : ι φ₀ = fun Y => c * (matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁))).indicator 1 (P.val * Y) :=
      funext hφ₀
    have h3 := hz₁Y Y
    rw [hιφ₀] at hιΦ
    rw [hιΦ, ← hιφ₀]
    rw [← hιφ₀] at h3
    simp only [Finsupp.sum] at h3
    rw [h3, Set.indicator_of_notMem, mul_zero]
    intro hp
    apply hY
    have h4 := hp.1
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (P.isUnit.map Matrix.detMonoidHom), Fintype.card_fin] at h4

end GlobalTheory.CombAtGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareForm
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.ThetaMeanSquareF

theorem exists_invariant_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ M : Submodule ℂ (WOF F E nS nT → ℂ), (∀ f ∈ M, IsThetaFunOF σ JS JT ξ₀ B.ψ f) →
      ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∃ Bf : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WOF F E nS nT) (f g f' g' : M),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u f → (g' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u g →
            Bf f' g' = Bf f g) ∧
          ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (Bf f f).re := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ M hM μ 𝓕 hμ h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := countable_of_discrete_addSubgroup _
  haveI := hμ
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨Bf, hBf, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form (μ.restrict 𝓕) M
    (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨Bf, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hBf, hBf, hf, hg]
  have key := GlobalTheory.HeisOrtho.setIntegral_add_right (G := WOF F E nS nT) (ratLF F E nS nT) μ 𝓕 h𝓕
    (fun w => (f : WOF F E nS nT → ℂ) w * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WOF F E nS nT → ℂ) (ratWF γ + w) * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) (ratWF γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (symplOHF σ JS JT ξ₀ w u))
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * (f : WOF F E nS nT → ℂ) (w + u) *
    (starRingEnd ℂ) (B.ψ (symplOHF σ JS JT ξ₀ w u) * (g : WOF F E nS nT → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]

end GlobalTheory.ThetaMeanSquareF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomeomorphColumnFixatorCoreUnitaryGroup
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem fixFrames_equiv_core : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  obtain ⟨e, econt, eprop, erat⟩ := _root_.GlobalTheory.SphEis.core_embeds F E σ n J j m C D Z J₀ hF
  have hJ₀ := GlobalTheory.UAut.det_isUnit hF.herm₀
  set p0 : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) := adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) with hp0
  have p0Z : p0 * adMat F Z = 1 := by
    rw [hp0, ← Matrix.map_mul, Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hJ₀,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hrec : ∀ g, (matHom _ σ J₀ g).1 = p0 * (matHom _ σ J (e g)).1 * adMat F Z := fun g => by
    rw [Matrix.mul_assoc, (eprop g).2.2, ← Matrix.mul_assoc, p0Z, Matrix.one_mul]
  have inj : Function.Injective e := fun g h hgh => by
    apply matHom_injective _ σ J₀
    apply Units.ext
    rw [hrec g, hrec h, hgh]
  have DJx : ∀ x ∈ fixG σ J D, adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J x).1 =
      adMat F (cT (σ : E →+* E) D * J) := by
    intro x hx
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact (fixG σ J D).inv_mem hx
    have := GlobalTheory.UAut.form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have surj : ∀ x ∈ fixG σ J C ⊓ fixG σ J D, ∃ g, e g = x := by
    intro x hx
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := (Subgroup.mem_inf.1 hx).1
    have hxD : (matHom _ σ J x).1 * adMat F D = adMat F D := (Subgroup.mem_inf.1 hx).2
    obtain ⟨g₀, b, h1, h2, -, -⟩ := _root_.GlobalTheory.SphEis.core_isom F E σ n J j m C D Z J₀ hF x (Subgroup.mem_inf.1 hx).1
    have hb : b = 0 := by
      rw [h2, DJx x (Subgroup.mem_inf.1 hx).2, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have aC : (matHom _ σ J (e g₀)).1 * adMat F C = adMat F C := (eprop g₀).1
    have aD : (matHom _ σ J (e g₀)).1 * adMat F D = adMat F D := (eprop g₀).2.1
    refine ⟨g₀, eq_of_frame_cols F E σ n J j m C D Z J₀ hF _ _ ?_ ?_ ?_⟩
    · rw [aC, hxC]
    · rw [(eprop g₀).2.2, h1, hb, Matrix.mul_zero, add_zero]
    · rw [aD, hxD]
  let f : GAd σ J₀ →* ↥(fixG σ J C ⊓ fixG σ J D) :=
    e.codRestrict _ (fun g => Subgroup.mem_inf.2 ⟨(eprop g).1, (eprop g).2.1⟩)
  have fbij : Function.Bijective f :=
    ⟨fun g h hgh => inj (congrArg Subtype.val hgh), fun x =>
      let ⟨g, hg⟩ := surj x.1 x.2; ⟨g, Subtype.ext hg⟩⟩
  let me := MulEquiv.ofBijective f fbij
  have hme : ∀ x, e (me.symm x) = x.1 := fun x => congrArg Subtype.val (me.apply_symm_apply x)
  have cM : Continuous (matHom (AF F) σ J) := (isEmbedding_matHom (AF F) σ J).continuous
  have contInv : Continuous me.symm := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    rw [(isEmbedding_matHom (AF F) σ J₀).continuous_iff, Units.continuous_iff]
    constructor
    · have : (Units.val ∘ (matHom (AF F) σ J₀ ∘ me.symm)) =
          fun x => p0 * (matHom _ σ J x.1).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]; rw [hrec, hme]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_val.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
    · have : (fun x => (((matHom (AF F) σ J₀ ∘ me.symm) x)⁻¹ : GL _ _).val) =
          fun x => p0 * ((matHom _ σ J x.1)⁻¹ : GL _ _).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]
        rw [← map_inv (matHom _ σ J₀), ← map_inv me.symm, hrec, hme, Subgroup.coe_inv, map_inv]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
  refine ⟨{ toMulEquiv := me, continuous_toFun := continuous_induced_rng.2 econt, continuous_invFun := contInv }, ?_⟩
  intro g
  change g ∈ ratPts σ J₀ ↔ e g ∈ ratPts σ J
  refine ⟨erat g, fun hg => ?_⟩
  obtain ⟨g₀, b, -, -, h3, h4⟩ := _root_.GlobalTheory.SphEis.core_isom F E σ n J j m C D Z J₀ hF (e g) (eprop g).1
  have : g₀ = g := matHom_injective _ σ J₀ (Units.ext (h3.trans (hrec g).symm))
  exact this ▸ h4 hg

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLimitPowersIntegralAdeles
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

open scoped Nat

namespace GlobalTheory.AlgIntIdem

theorem natCast_dvd_pow_sub {E : Type} [Field E] [NumberField E] (x : 𝓞 E) (N t : ℕ)
    (hN : 0 < N) (ht : 0 < t) :
    (N : 𝓞 E) ∣ x ^ ((N ^ Module.finrank ℤ (𝓞 E))! * t) - x ^ (N ^ Module.finrank ℤ (𝓞 E))! := by
  set I : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    simp only [I, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ I) = N ^ Module.finrank ℤ (𝓞 E) := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      Ideal.absNorm_span_natCast]
  have h := GlobalTheory.IdealIdele.pow_factorial_mul (Ideal.Quotient.mk I x) t ht
  rw [hcard, ← map_pow, ← map_pow, Ideal.Quotient.eq] at h
  exact Ideal.mem_span_singleton.1 h

theorem idem : ∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w := by
  intro D x
  set d := Module.finrank ℤ (𝓞 D.host.E)
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  have hx : inc D (x : D.host.E) ∈ OhE D := VacMove.inc_int D x
  have key : ∀ N t : ℕ, 0 < N → 0 < t → ∃ w ∈ OhE D,
      inc D (x : D.host.E) ^ ((N ^ d)! * t) = inc D (x : D.host.E) ^ (N ^ d)! + (N : AE D) * w := by
    intro N t hN ht
    obtain ⟨w, hw, h⟩ := VacMove.inc_dvd D (natCast_dvd_pow_sub x N t hN ht)
    refine ⟨w, hw, ?_⟩
    rw [← h]
    push_cast
    rw [map_sub, map_pow, map_pow]
    ring
  obtain ⟨e, he, h⟩ := hcpl (fun N => inc D (x : D.host.E) ^ (N ^ d)!) (fun N => pow_mem hx _) (by
    intro N m hN hm
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial
      (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right N hm) d)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨w, hw, hh⟩ := key N t hN ht0
    exact ⟨w, hw, by simp only [ht, hh]⟩)
  refine ⟨e, he, ?_, fun N hN => ⟨(N ^ d)!, Nat.factorial_pos _, h N hN⟩⟩
  rw [← sub_eq_zero]
  refine hsep _ fun N hN => ?_
  obtain ⟨w, hw, hh⟩ := h N hN
  obtain ⟨c, hc, hc'⟩ := key N 2 hN two_pos
  refine ⟨c + (2 * inc D (x : D.host.E) ^ (N ^ d)! * w + N * w * w - w), ?_, ?_⟩
  · exact add_mem hc (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (pow_mem hx _)) hw)
      (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
  · rw [pow_mul] at hc'
    rw [hh]; linear_combination hc'

end GlobalTheory.AlgIntIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExistsStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_embedding_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl (F := F), SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  first | exact @GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | exact GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | (intros; apply GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully <;> assumption)
end

