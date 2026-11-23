module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetEigen

theorem heisO_lincomb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) :
    heisO ψ S T y (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • heisO ψ S T y (f i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cosetSum_eigen : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (Λd : AddSubgroup (WO S T)) (R : Finset (WO S T)) (x : WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ Λd, ψ (symplO S T u y) = 1) → (∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) → (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → y = y') → (∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a → ψ (symplO S T x a) = 1) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → ∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → heisO ψ S T y (∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g) = ψ (symplO S T x y) • ∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g := by
  intro D ψ S T ΛS ΛT P e he Λd R x hR h2 h3 h4 g hg y hy hyd
  classical
  have hec : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm]; exact he.2
  have half_add : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a + b) :=
    fun ha hb i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  have half_neg : ∀ {a : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) (-a) :=
    fun ha i j => by rw [Matrix.neg_apply, mul_neg, ha i j]
  have half_sub : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a - b) :=
    fun ha hb => by rw [sub_eq_add_neg]; exact half_add ha (half_neg hb)
  have ann_add : ∀ {a b : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → (∀ u ∈ Λd, ψ (symplO S T u b) = 1) →
      ∀ u ∈ Λd, ψ (symplO S T u (a + b)) = 1 :=
    fun ha hb u hu => by rw [Formalism.IndefR.Fin.symplO_add_right, AddChar.map_add_eq_mul, ha u hu, hb u hu, one_mul]
  have ann_neg : ∀ {a : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → ∀ u ∈ Λd, ψ (symplO S T u (-a)) = 1 :=
    fun ha u hu => by rw [Formalism.IndefR.Fin.symplO_neg_right, AddChar.map_neg_eq_inv, ha u hu, inv_one]
  choose! f hfR hfΛ using h2
  have hyz : ∀ z ∈ R, IsHalf (cA D e) (y + z) ∧ ∀ u ∈ Λd, ψ (symplO S T u (y + z)) = 1 := fun z hz =>
    ⟨half_add hy (hR z hz).1, ann_add hyd (hR z hz).2⟩
  have hzy : ∀ z ∈ R, IsHalf (cA D e) (z + -y) ∧ ∀ u ∈ Λd, ψ (symplO S T u (z + -y)) = 1 := fun z hz =>
    ⟨half_add (hR z hz).1 (half_neg hy), ann_add (hR z hz).2 (ann_neg hyd)⟩
  have hfix : ∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a →
      heisO ψ S T a g = g := fun a ha hh =>
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he a ha (Or.inr hh)
  have key : ∀ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T y (heisO ψ S T z g) =
      ψ (symplO S T x y) • (ψ (-symplO S T x (f (y + z))) • heisO ψ S T (f (y + z)) g) := by
    intro z hz
    obtain ⟨hh, ha⟩ := hyz z hz
    have hσR := hfR _ hh ha
    have ha0 := hfΛ _ hh ha
    generalize f (y + z) = s at hσR ha0 ⊢
    have hσh := (hR _ hσR).1
    have ha0h : IsHalf (cA D e) (y + z - s) := half_sub hh hσh
    have e1 : heisO ψ S T y (heisO ψ S T z g) = heisO ψ S T s g := by
      rw [← Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hy (hR z hz).1)]
      have hsplit : y + z = s + (y + z - s) := by abel
      rw [hsplit, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hσh ha0h), hfix _ ha0 ha0h]
    have hlin : symplO S T x y + symplO S T x z = symplO S T x s + symplO S T x (y + z - s) := by
      rw [← Formalism.IndefR.Fin.symplO_add_right, ← Formalism.IndefR.Fin.symplO_add_right]
      congr 1; abel
    have hph : -symplO S T x z = symplO S T x y + -symplO S T x s + -symplO S T x (y + z - s) := by
      linear_combination (-1 : AF D.host.F) * hlin
    rw [e1, hph, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv ψ (symplO S T x (y + z - s)),
      h4 _ ha0 ha0h, inv_one, mul_one, smul_smul]
  rw [heisO_lincomb, Finset.sum_congr rfl key, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_nbij' (fun z => f (y + z)) (fun z => f (z + -y)) (fun z hz => hfR _ (hyz z hz).1 (hyz z hz).2)
    (fun z hz => hfR _ (hzy z hz).1 (hzy z hz).2) (fun z hz => ?_) (fun z hz => ?_) (fun z hz => rfl)
  · have hs := hfR _ (hyz z hz).1 (hyz z hz).2
    have h1 := hfΛ _ (hyz z hz).1 (hyz z hz).2
    have h2' := hfΛ _ (hzy _ hs).1 (hzy _ hs).2
    have ht := hfR _ (hzy _ hs).1 (hzy _ hs).2
    have hsum := add_mem h1 h2'
    have heq : y + z - f (y + z) + (f (y + z) + -y - f (f (y + z) + -y)) = z - f (f (y + z) + -y) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ ht hsum).symm
  · have ht := hfR _ (hzy z hz).1 (hzy z hz).2
    have h1 := hfΛ _ (hzy z hz).1 (hzy z hz).2
    have h2' := hfΛ _ (hyz _ ht).1 (hyz _ ht).2
    have hs := hfR _ (hyz _ ht).1 (hyz _ ht).2
    have hsum := add_mem h1 h2'
    have heq : z + -y - f (z + -y) + (y + f (z + -y) - f (y + f (z + -y))) = z - f (y + f (z + -y)) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ hs hsum).symm

end GlobalTheory.CosetEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspMultiplicityMemSphericalEigenPartOfValuePara
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.ValPart

theorem lift_compMultilinearMap' {ι : Type*} [Fintype ι] {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module ℂ (Mi i)]
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) (T : MultilinearMap (RingHom.id ℂ) Mi E) :
    PiTensorProduct.lift (L.compMultilinearMap T) = L ∘ₗ PiTensorProduct.lift T := by
  apply PiTensorProduct.ext
  ext v
  simp

theorem valPart_mem : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → ForStage D fun c _ s => ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e := by
  intro hCRD D hMet c hc j hj s hs u w B hw hB
  have hconjH := (_root_.GlobalTheory.EvenOnto.ConjVal.values_conj_hecke hCRD D c hc j hj s hs).2
  have hBV : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (PiLocalization₂.val u w g)) B := hB
  obtain ⟨a, ha⟩ := GlobalTheory.ParamEigen.eig_of_param D s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S
    hs.sph B
  have heig : ∀ P d R, Hecke₂ s.V (s.J : Set (GA D s.V)) 1 c.S P d R →
      heckeLin s.V R (PiLocalization₂.val u w) = conj (a P d) • PiLocalization₂.val u w := by
    intro P d R hR
    have h1 := ha _ hBV P d R hR
    rw [hconjH] at h1
    funext g
    have h2 := congrArg (starRingEnd ℂ) (congrFun h1 g)
    simpa [map_mul] using h2
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M s.J (1 : GA D s.V → ℂ) c.S
    GlobalTheory.ChainOntoSph.exists_unif_of_F hc.inf (fun _ _ _ _ => by simp) hs.split
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun P d => conj (a P d), ?_⟩
  have hT : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (s.J : Set (GA D s.V)) 1 :=
    (mem_multT c.θ s.M _ _ _).1 u.2
  rw [mem_partFull]
  refine ⟨hT, fun P d R hR v => ?_⟩
  obtain ⟨hkeep, -, -⟩ := hops.2.2 P d R hR
  set T := PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) with hTdef
  have hT' : heckeOn s.M R T - conj (a P d) • T ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) 1 :=
    Submodule.sub_mem _ (hkeep T hT) (Submodule.smul_mem _ _ hT)
  have hmem : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) ∈ s.CC c := by
    show _ ∈ MultT c.θ s.M _ _
    rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact hT'
  let x : s.CC c := ⟨_, hmem⟩
  have hlift : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) =
      heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) - conj (a P d) • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    rw [map_sub, map_smul, heckeOn, postOn]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [lift_compMultilinearMap', hTdef, LinearEquiv.apply_symm_apply]
  have hx : PiLocalization₂.val x w = 0 := by
    show PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) w = 0
    rw [hlift]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [sub_eq_zero]
    exact heig P d R hR
  have hx0 := (_root_.GlobalTheory.EvenOnto.vanish_and_parLin D hMet).1 c hc j hj s hs x w hw0 hx
  have h3 : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) = 0 := congrArg Subtype.val hx0
  have h4 : heckeOn s.M R T - conj (a P d) • T = 0 := by
    have h := congrArg PiTensorProduct.lift.symm h3
    rwa [LinearEquiv.symm_apply_apply, map_zero] at h
  have h5 := congrArg (fun U : MMap s.M => U v) h4
  simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, MultilinearMap.zero_apply, sub_eq_zero] at h5
  simpa [heckeOn, postOn_apply] using h5

end GlobalTheory.EvenOnto.ValPart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspMultiplicitySpaceSpanSphericalEigenPartsEqTo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOntoDecomp

theorem cc_span_partFull : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e} = ⊤ := by
  classical
  intro hP D hfd c hc j hj s hs
  have hmul : ∀ k ∈ s.J, ∀ k' ∈ s.J, (1 : GA D s.V → ℂ) (k * k') = (1 : GA D s.V → ℂ) k * (1 : GA D s.V → ℂ) k' :=
    fun _ _ _ _ => by simp
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M s.J (1 : GA D s.V → ℂ) c.S
    GlobalTheory.ChainOntoSph.exists_unif_of_F hc.inf hmul hs.split
  obtain ⟨hLU, -, hH⟩ := hops
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  swap
  · push_neg at hsm
    obtain ⟨τ, hτ⟩ := hsm
    refine Submodule.eq_top_iff'.2 fun u => ?_
    have h0 : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0 := by
      refine MultilinearMap.ext fun v => ?_
      rw [MultilinearMap.zero_apply]
      have hv : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := (Submodule.eq_bot_iff _).1 hτ _ (v τ).2
      exact MultilinearMap.map_coord_zero (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) τ
        (Subtype.ext hv)
    have h1 := LinearEquiv.apply_symm_apply PiTensorProduct.lift (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
    rw [h0, map_zero] at h1
    have : u = 0 := Subtype.ext h1.symm
    rw [this]
    exact zero_mem _
  have hschur := GlobalTheory.MultFinite.schurMult (θ := c.θ) (M := s.M) (J := (s.J : Set (GA D s.V)))
    (χ := (1 : GA D s.V → ℂ)) hP s.ν s.fd
  haveI := hs.haar
  have hright : s.ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds s.V s.ν hs.haar
  obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M (s.J : Set (GA D s.V))
    (1 : GA D s.V → ℂ) s.ν s.fd hc.inf hs.haar hs.fund hschur hsm
  obtain ⟨v0, hv0⟩ := GlobalTheory.SchurConst.exists_vec s.M hsm
  have hspec : ∀ T ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      ∀ T' ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      IsMultIP s.M s.ν s.fd T T' (ipM s.M s.ν s.fd T T') := fun T hT T' hT' =>
    ipM_spec _ _ _ _ _ (hschur hc.inf hs.haar hs.fund T hT T' hT')
  let φ := Submodule.equivMapOfInjective (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap
    (LinearEquiv.injective _) (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))
  haveI : FiniteDimensional ℂ ((Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)).map
      (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap) := hfd c hc j hj s hs
  haveI : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) :=
    LinearEquiv.finiteDimensional φ.symm
  let I := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D s.V) //
    Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S t.1 t.2.1 t.2.2}
  let op : I → Module.End ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) := fun t =>
    (heckeOn s.M t.1.2.2).restrict fun T hT => (hH _ _ _ t.2).1 T hT
  have hcomm : ∀ i j, Commute (op i) (op j) := fun i j => by
    refine LinearMap.ext fun T => Subtype.ext ?_
    exact (hH _ _ _ i.2).2.1 _ _ _ j.2 T T.2
  have hadj : ∀ i, ∃ i', ∀ x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      ipM s.M s.ν s.fd (op i x : MMap s.M) y = ipM s.M s.ν s.fd x (op i' y : MMap s.M) := fun i => by
    obtain ⟨R', h', hip⟩ := (hH _ _ _ i.2).2.2
    refine ⟨⟨(i.1.1, dualLab i.1.2.1, R'), h'⟩, fun x y => ?_⟩
    have h1 := hspec _ ((hH _ _ _ i.2).1 x x.2) y y.2
    have h2 := (hip s.ν s.fd hs.haar hright hs.fund hschur x x.2 y y.2 _).1 h1
    have h3 := hspec x x.2 _ ((hH _ _ _ h').1 y y.2)
    exact hasPeterssonInner_unique s.M s.ν s.fd _ _ v0 hv0 h2 h3
  have htop := GlobalTheory.OntoDecomp.iSup_jointEigenspace_eq_top
    (fun x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => ipM s.M s.ν s.fd x y)
    (fun x y z a => (hlin x x.2 y y.2 z z.2 a).1) (fun x y => (hlin x x.2 y y.2 y y.2 0).2)
    (fun x hx => hpos x x.2 fun h => hx (Subtype.ext h)) op hcomm hadj
  have hsub : ∀ x : I → ℂ, ∀ T ∈ ⨅ i, (op i).eigenspace (x i), ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (T : MMap s.M) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S e := by
    classical
    intro x T hT
    refine ⟨fun P d => if h : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R
      then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0, ?_⟩
    rw [mem_partFull]
    refine ⟨T.2, fun P d R hR v => ?_⟩
    have hex : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R := ⟨R, hR⟩
    rw [dite_eq_left hex]
    have hlevT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 T.2).lev v
    rw [hLU P d R hex.choose hR hex.choose_spec _ hlevT]
    have h1 := (Submodule.mem_iInf _).1 hT ⟨(P, d, hex.choose), hex.choose_spec⟩
    rw [Module.End.mem_eigenspace_iff] at h1
    exact congrArg (fun U : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => (U : MMap s.M) v) h1
  rw [eq_top_iff]
  rintro u -
  obtain ⟨T, rfl⟩ := φ.surjective u
  have hT : T ∈ (⊤ : Submodule ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))) := trivial
  rw [← htop] at hT
  refine Submodule.iSup_induction (fun x : I → ℂ => ⨅ i, (op i).eigenspace (x i))
    (motive := fun T => φ T ∈ Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e}) hT ?_ ?_ ?_
  · intro x T hT
    obtain ⟨e, he⟩ := hsub x T hT
    refine Submodule.subset_span ⟨e, ?_⟩
    have : ((φ T : s.CC c) : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = PiTensorProduct.lift (T : MMap s.M) := rfl
    rw [this, LinearEquiv.symm_apply_apply]
    exact he
  · rw [φ.map_zero]; exact zero_mem _
  · intro a b ha hb; rw [φ.map_add]; exact add_mem ha hb

end GlobalTheory.EvenOntoDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecayWeightOneParamTranslateLeConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.OnePDecay

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hsn_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hsn A = ‖A‖ := by
  rw [hsn, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : hsn (A * B) ≤ hsn A * hsn B := by
  rw [hsn_eq_norm, hsn_eq_norm, hsn_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn A := Real.sqrt_nonneg _

theorem continuous_hsn_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun s : ℝ => hsn (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ) := by
  unfold hsn
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_iff_continuousAt.2 fun t => (GlobalTheory.Mem.Lift.hasDerivAt_exp_entry X t i j).continuousAt).norm.pow 2

theorem decay_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ N : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (x : GA D V) (t : ℝ), |t| < 1 → ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤
        L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ := by
  intro D θ hθ V τ X hX N
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_hsn_exp X).continuousOn
  set m : ℝ := max 1 (max M (hsn (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hbound : ∀ τ' (s : ℝ), |s| ≤ 1 → hsn (cmp θ τ' (oneP θ V τ X s)) ≤ m := by
    intro τ' s hs
    have h := GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s
    by_cases e : τ' = τ
    · subst e
      show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.1]
      have := hM s ⟨(abs_le.1 hs).1, (abs_le.1 hs).2⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_of_le_right (le_max_left _ _)))
    · show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.2 τ' e]
      exact le_max_of_le_right (le_max_right _ _)
  have hkey : ∀ (x : GA D V) (t : ℝ) τ', |t| < 1 →
      1 + hsn (cmp θ τ' x) ≤ (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) * m := by
    intro x t τ' ht
    have hx : x = x * oneP θ V τ X t * oneP θ V τ X (-t) := by
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one]
    have h1 : hsn (cmp θ τ' x) ≤ hsn (cmp θ τ' (x * oneP θ V τ X t)) * m := by
      have e2 : cmp θ τ' x = cmp θ τ' (x * oneP θ V τ X t) * cmp θ τ' (oneP θ V τ X (-t)) := by
        show infMat _ _ (θ τ') x = infMat _ _ (θ τ') _ * infMat _ _ (θ τ') _
        rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, ← hx]
      rw [e2]
      exact (hsn_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (hbound τ' (-t) (by rw [abs_neg]; exact ht.le)) (hsn_nonneg' _))
    nlinarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]
  refine ⟨m ^ (N * Fintype.card D.what₂.Tau), by positivity, fun x t ht => ?_⟩
  rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun τ' _ => inv_nonneg.2 (pow_nonneg (by linarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]) N)) (fun τ' _ => ?_)
  have ha := hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))
  have hb := hsn_nonneg' (cmp θ τ' x)
  have hk := hkey x t τ' ht
  have hpa : 0 < (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N := pow_pos (by linarith) N
  have hpb : 0 < (1 + hsn (cmp θ τ' x)) ^ N := pow_pos (by linarith) N
  rw [← div_eq_mul_inv, le_div_iff₀ hpb, inv_mul_eq_div, ← div_pow]
  refine pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) ?_ N
  rw [div_le_iff₀ (by linarith)]
  linarith

end GlobalTheory.OnePDecay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupMaxCompactSkewHermitia
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CompactLine

theorem exists_line_in_kInf_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb := by
  intro F E _ _ _ _ _ σ B n W r s hb hW k hk
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds n r s _ (W.θ w) (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf]; exact hA w
  obtain ⟨γ, hγ, Y, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin n) r s
    B.emb (incM F W.J) Complex.I A W.θ hb.cm hA1 hAθ k hk.1 hk.2
  refine ⟨γ, hγ, hγ1, fun t => ⟨hγ.2 t, fun w => ?_⟩⟩
  obtain ⟨A', hAA⟩ := (hA w).2
  exact commute_of_gen (A w) A' hAA _ _ (Y w) (hKC w) t.toAdd (hAθ w) (hgen t.toAdd w)

end GlobalTheory.CompactLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_reduction_eq_one_of_completion_congruence : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E), b ∉ PP.asIdeal → (∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L)) → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.LevRedTriv.redFn_eq_one_of_cong | exact GlobalTheory.LevRedTriv.redFn_eq_one_of_cong | (intros; apply GlobalTheory.LevRedTriv.redFn_eq_one_of_cong <;> assumption)
end

