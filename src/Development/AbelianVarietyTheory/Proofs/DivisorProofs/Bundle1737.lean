module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEmbeddingIdealLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelUnitValues
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.SerOne

open GlobalTheory.ClassScalarValue GlobalTheory.PtId

theorem guard_of_splitOffBad {D : D7} (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank)
    {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) {bad : ℕ} (h2 : 2 ∣ bad) (hM : l.M ∣ bad) {h : GA D V}
    (hs : SplitOffBad V bad h) : GlobalTheory.ClassScalarCompare.Guard H bad (Bridge.hLat V (fin V h)) := by
  obtain ⟨e, e1, e2, e3, e4⟩ := (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).1
    (GlobalTheory.RepsCompare.suppSplitOff_of_splitOffBad _ _ _ hs)
  have hs' : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (bad * l.M) (finHom V h).1 := by
    refine ⟨e, e1, e2, fun v hv => ⟨(e3 v hv).1, fun hm => (e3 v hv).2 ?_⟩, e4⟩
    rw [Nat.cast_mul] at hm
    refine (v.isPrime.mem_or_mem hm).elim id fun h => ?_
    obtain ⟨u, rfl⟩ := hM
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨-, c1, c2, -, -, c5⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL H l bad h2 h hs'
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := H)
    (L := (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La) ⟨c1, c2, c5⟩
  have e2 : (GlobalTheory.ClassScalarCompare.conjLat (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La).La =
    Bridge.hLat V (fin V h) := GlobalTheory.ClassScalarCompare.conjLat_conjLat _
  rwa [e2] at g

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}



end GlobalTheory.AdTh.SerOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartz
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolDense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem mem_pol_of_isGauss (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f₀ : SInf F (Fin n × Fin d)} (h : M.IsGauss ψ τ f₀) : f₀ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f₀ h

theorem mem_pol_of_actsD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h


open scoped Classical in
theorem pol_stable (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (v a : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h₁ : ∀ y, f₁ y = fderiv ℝ (⇑f) y v - 2 * Real.pi * Complex.I * (GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a : ℂ) * f y) :
    f₁ ∈ M.Pol ψ τ := by
  obtain ⟨u, hu, hD⟩ := GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq M ψ hψ (v, a)
  obtain ⟨D, hDa⟩ := GlobalTheory.HeisDeriv.exists_actsD_heisLine M ψ hψ u hu
  have e : D f = f₁ := by
    refine SchwartzMap.ext fun y => ?_
    rw [hD f (D f) (hDa f) y, h₁ y]
  exact e ▸ mem_pol_of_actsD M ψ τ hu hf (hDa f)


open scoped Classical in
theorem pol_dense : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨g, hg, Q, c, hc, hQ, hgQ⟩ := _root_.GlobalTheory.GaussVacPair.exists_gauss_vacuum F E σ B n d X W M χX χW om r s r' s' hP
  refine _root_.GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem _ _ g Q c hc hQ hgQ (mem_pol_of_isGauss M B.ψ B.emb hg) ?_ ?_
  · intro v f f₁ hf h₁
    refine pol_stable M B.ψ hψ B.emb v 0 hf fun y => ?_
    rw [h₁ y]
    simp [GlobalTheory.ArchUniq.trP]
  · intro ℓ f f₁ hf h₁
    have hnd := GlobalTheory.ArchSch.mixedTracePairing_nondegenerate F (Fin n × Fin d)
    obtain ⟨a, ha⟩ : ∃ a, ∀ y, GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a = ℓ y := by
      let e := (GlobalTheory.ArchSch.trP F (Fin n × Fin d)).flip.toDual hnd.flip
      refine ⟨e.symm ℓ.toLinearMap, fun y => ?_⟩
      calc GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y (e.symm ℓ.toLinearMap) = e (e.symm ℓ.toLinearMap) y := by
            simp only [e, LinearMap.BilinForm.toDual_def]; rfl
        _ = ℓ y := by rw [e.apply_symm_apply]; rfl
    have hmem : (-(2 * Real.pi * Complex.I)) • f₁ ∈ M.Pol B.ψ B.emb := by
      refine pol_stable M B.ψ hψ B.emb 0 a hf fun y => ?_
      simp [h₁ y, ha y]
      ring
    have hne : (-(2 * Real.pi * Complex.I)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := (M.Pol B.ψ B.emb).smul_mem (-(2 * Real.pi * Complex.I))⁻¹ hmem
    rwa [inv_smul_smul₀ hne] at this

end GlobalTheory.PolDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KInfPol

open GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem at_mul_right {m p q : Type} [Fintype p] {z : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hz : At (evI F) z)
    (A : Matrix p q (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : At (evI F) (z * A) := by
  intro u hu; rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

theorem heisLine_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (t : ℝ) :
    M.heisLine ψ u t 0 = 0 := by
  funext x
  simp [Model.heisLine, Darboux.rho, schr]

theorem sa_of_acts {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) : SA T f f₁ := by
  intro g hg
  refine h (fun x => g (fun i => (x i).2)) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  change g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [fin_eq_zero_of_at hz, add_zero]

theorem sd_intertwine {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ W.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (1, h)) f g) (hf₁ : Acts (evI F) (om (1, h)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (u * (mat h)ᵀ)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (1, h) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (1, h) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((1, h) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (u * (mat h)ᵀ) := by
    change (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (realAd F t • u) * (mat h)ᵀ = _
    rw [Matrix.one_mul, Matrix.smul_mul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

theorem pol_stable_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ ∈ M.Pol B.ψ B.emb := by
  intro F E _ _ _ _ _ σ B n d Y W M om χ₁ χ₂ hB hM hw k hk f hf f₁ hf₁
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.ArchLocalAct.exists_op_of_KInf F E σ B n d Y W M om χ₁ χ₂ hB hM hw k hk
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.HeisDer.derEx F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  have hle : M.Pol B.ψ B.emb ≤ (M.Pol B.ψ B.emb).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_right hu (mat k⁻¹)ᵀ
      have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
          calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
                ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
                (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_right hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.KInfPol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorLocalOperatorsStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_tensor_local_operators : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  first | exact @GlobalTheory.EvKer.ker_trivial | exact GlobalTheory.EvKer.ker_trivial | (intros; apply GlobalTheory.EvKer.ker_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.SchrFixUniq

theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

theorem schr_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w : (κ → R) × (κ → R)) (a : ℂ) (φ : (κ → R) → ℂ) : schr ψ w (a • φ) = a • schr ψ w φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem schr_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (φ : (κ → R) → ℂ) : schr ψ 0 φ = φ := by
  funext x
  simp [schr]

theorem char_ne_zero {R : Type} [CommRing R] (ψ : AddChar R ℂ) (x : R) : ψ x ≠ 0 := by
  intro hx
  have h2 : ψ (x + -x) = ψ x * ψ (-x) := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at h2
  exact one_ne_zero h2

theorem common_eigen {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (S : Set ((κ → R) × (κ → R))) (f g : (κ → R) → ℂ) (hf : ∀ s ∈ S, schr ψ s f = f)
    (hg : ∀ s ∈ S, schr ψ s g = g) (l : (κ → R) × (κ → R)) (hl : l ∈ AddSubgroup.closure S) :
    ∃ χ : ℂ, χ ≠ 0 ∧ schr ψ l f = χ • f ∧ schr ψ l g = χ • g := by
  induction hl using AddSubgroup.closure_induction with
  | mem s hs => exact ⟨1, one_ne_zero, by rw [hf s hs, one_smul], by rw [hg s hs, one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [schr_zero', one_smul], by rw [schr_zero', one_smul]⟩
  | add w w' _ _ h h' =>
    obtain ⟨χ, hχ, h1, h2⟩ := h
    obtain ⟨χ', hχ', h1', h2'⟩ := h'
    have hz := char_ne_zero ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2))
    have key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ w' φ = χ' • φ →
        schr ψ (w + w') φ = ((ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)))⁻¹ * (χ' * χ)) • φ := by
      intro φ a b
      have e := schr_comp ψ w w' φ
      rw [b, schr_smul', a, smul_smul] at e
      rw [mul_smul, e, smul_smul, inv_mul_cancel₀ hz, one_smul]
    exact ⟨_, mul_ne_zero (inv_ne_zero hz) (mul_ne_zero hχ' hχ), key f h1 h1', key g h2 h2'⟩
  | neg w _ h =>
    obtain ⟨χ, hχ, h1, h2⟩ := h
    have key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ (-w) φ = χ⁻¹ • φ := by
      intro φ a
      have e := schr_comp ψ (-w) w φ
      have e0 : ⅟(2 : R) * ((-w).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (-w).2) = 0 := by
        simp
      rw [a, schr_smul', neg_add_cancel, schr_zero', e0, AddChar.map_zero_eq_one, one_smul] at e
      conv_rhs => rw [← e]
      rw [smul_smul, inv_mul_cancel₀ hχ, one_smul]
    exact ⟨_, inv_ne_zero hχ, key f h1, key g h2⟩

theorem exists_shift {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψk : AddChar (Fv F v) ℂ)
    (hc : Continuous ψk) (h1 : ψk ≠ 1) : ∃ a : Fv F v, a ≠ 0 ∧ ∀ x : Fv F v,
      (∀ y ∈ v.adicCompletionIntegers F, ψk (a * (x * y)) = 1) ↔ x ∈ v.adicCompletionIntegers F := by
  have hne : ∃ t, ψk t ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (AddChar.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued ψk hc hne
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have ha0 : (Valued.v a : WithZero (Multiplicative ℤ)) ≠ 0 := by rw [ha]; exact WithZero.exp_ne_zero
  refine ⟨a, by simpa using ha0, fun x => ?_⟩
  have h := hn (a * x)
  rw [← ha, map_mul, mul_le_iff_le_one_right (zero_lt_iff.2 ha0)] at h
  simpa only [HeightOneSpectrum.mem_adicCompletionIntegers, mul_assoc] using h

theorem exists_pair {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψk : AddChar (Fv F v) ℂ) (hc : Continuous ψk) (h1 : ψk ≠ 1)
    (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v) (hc0 : c ≠ 0)
    (hself : ∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1)
    (hbd : ∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F)
    (η : κ → Fv F v) (hη : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) : ∃ y, (η, y) ∈ Λ := by
  classical
  obtain ⟨a, ha, hcond⟩ := exists_shift v ψk hc h1
  let Λ' : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := {w | (w.1, a • w.2) ∈ Λ}
      add_mem' := fun {x y} hx hy => by
        have := Λ.add_mem hx hy
        simpa [smul_add] using this
      zero_mem' := by
        show ((0 : κ → Fv F v), a • (0 : κ → Fv F v)) ∈ Λ
        rw [smul_zero]
        exact Λ.zero_mem
      neg_mem' := fun {x} hx => by
        have := Λ.neg_mem hx
        simpa using this }
  have hΛ' : ∀ w, w ∈ Λ' ↔ (w.1, a • w.2) ∈ Λ := fun _ => Iff.rfl
  have hbd' : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ', ∀ i,
      c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F := by
    rcases (v.adicCompletionIntegers F).mem_or_inv_mem a with h | h
    · refine ⟨a * c, mul_ne_zero ha hc0, fun l hl i => ?_⟩
      obtain ⟨p, q⟩ := hbd _ ((hΛ' l).1 hl) i
      refine ⟨by rw [mul_assoc]; exact mul_mem h p, ?_⟩
      convert q using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · refine ⟨c, hc0, fun l hl i => ?_⟩
      obtain ⟨p, q⟩ := hbd _ ((hΛ' l).1 hl) i
      refine ⟨p, ?_⟩
      convert mul_mem h q using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  obtain ⟨c', hc', hb'⟩ := hbd'
  have hs' : ∀ w, w ∈ Λ' ↔ ∀ l ∈ Λ', (ψk.mulShift a) (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
    intro w
    rw [hΛ', hself]
    constructor
    · intro h l hl
      have := h _ ((hΛ' l).1 hl)
      simp only [dotProduct_smul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_sub]
      exact this
    · intro h l hl
      have := h (l.1, a⁻¹ • l.2) (by rw [hΛ']; simpa [smul_smul, mul_inv_cancel₀ ha] using hl)
      rw [AddChar.mulShift_apply, mul_sub] at this
      simp only [dotProduct_smul, smul_eq_mul] at this ⊢
      rwa [mul_inv_cancel_left₀ ha] at this
  obtain ⟨y, hy⟩ := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (ψk.mulShift a) Λ' c' hc'
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x) hs' hb' η (fun b hb => by
      have := hη _ ((hΛ' _).1 hb)
      rwa [dotProduct_smul, smul_eq_mul, ← AddChar.mulShift_apply] at this)
  exact ⟨_, (hΛ' _).1 hy⟩

theorem proportional_of_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ (S : Set ((κ → Fv F v) × (κ → Fv F v))) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v),
    Λ ≤ AddSubgroup.closure S → c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ f g : (κ → Fv F v) → ℂ, (∀ s ∈ S, schr ψk s f = f) → (∀ s ∈ S, schr ψk s g = g) → f ≠ 0 → ∃ a : ℂ, g = a • f := by
  intro F _ _ v κ _ ψk hc h1 S Λ c hS hc0 hself hbd f g hf hg hf0
  classical
  have hall : ∀ l, ∃ χ : ℂ, l ∈ Λ → schr ψk l f = χ • f ∧ schr ψk l g = χ • g := by
    intro l
    by_cases hl : l ∈ Λ
    · obtain ⟨χ, -, h⟩ := common_eigen ψk S f g hf hg l (hS hl)
      exact ⟨χ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose χ hχ using hall
  refine GlobalTheory.heisenbergEigen_proportional ψk Λ χ f g (fun l hl ξ => ?_) (fun l hl ξ => ?_) hf0
    (exists_pair v ψk hc h1 Λ c hc0 hself hbd)
  · have := congrFun (hχ l hl).1 ξ
    rw [← invOf_eq_inv]
    exact this
  · have := congrFun (hχ l hl).2 ξ
    rw [← invOf_eq_inv]
    exact this

end GlobalTheory.SchrFixUniq
end

