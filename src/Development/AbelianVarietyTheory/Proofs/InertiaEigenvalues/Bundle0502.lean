module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveMaxUnramifiedSubfieldAlgebraMap
section
noncomputable section

namespace GlobalTheory.TopSteps.FinSummandDim

open Module TensorProduct
open GlobalTheory.AdmLoc GlobalTheory.TopSteps GlobalTheory.TopSteps.FinSummand Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace Qp] [TopologicalSpace LL]

theorem h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) : H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ = ⊥ := by
  obtain ⟨_, _, _⟩ := hO.1
  refine invariants_stableLattice_mod_irreducible_eq_bot (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hlam ?_
  change (coefRep (latRep (twLattice Γ.T₀.L Γ.χ₁⁻¹)) (O ⧸ Ideal.span {Γ.lam})).invariants = ⊥
  rw [latRep_twLattice]
  exact h0

theorem finrank_h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) :
    finrank LL ↥(H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) = 0 := by
  rw [h0V_tw hO Γ hχ hlam h0, finrank_bot]

theorem isCompl_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hfin : Module.Finite O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ)) :
    ∃ C : Submodule O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) C := by
  obtain ⟨_, _, _⟩ := hO.1
  exact exists_isCompl_of_saturated _ (h1fT_saturated PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L)

theorem finrank_tw [CompactSpace G] (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hT : IsOpen (Γ.T₀.L.T : Set Γ.T₀.V)) :
    finrank O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) = finrank LL (FiniteCohomology PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) := by
  obtain ⟨_, _, _⟩ := hO.1
  exact finrank_h1fT PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hT

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem cont_inv (hC : S.CrysCalc) : Continuous fun g => algebraMap S.O ↥S.LL.1 (S.Γ.χ₁⁻¹ g) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2.1

abbrev tw (hC : S.CrysCalc) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O := twLat S.Γ.T₀ S.Γ.χ₁⁻¹ (cont_inv S hC)

theorem tw_crysWith (hC : S.CrysCalc) :
    CrysWith (P.PD S.K) S.emb (tw S hC).ρ (fun i => (S.D.U i).map (· + -S.D.w i)) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  have h1 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁⁻¹ _ hρ h1).1

set_option synthInstance.maxHeartbeats 100000 in
theorem tw_finrank_h0V (hC : S.CrysCalc) (hV : S.Vanish) : finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) = 0 := by
  obtain ⟨⟨-, -, -, -, -, hlam⟩, -⟩ := S.hyp
  exact finrank_h0V_tw (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hlam hV.1

theorem exists_isCompl (hC : S.CrysCalc) (hH : S.FreeH) :
    ∃ C : Submodule S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) C :=
  isCompl_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hH.1.2.1

theorem finrank_hf (hC : S.CrysCalc) :
    finrank S.O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) = finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) :=
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  finrank_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC)
    (GlobalTheory.Cyc.locLat_isOpen (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ.T₀)

theorem sum_card_neg :
    ∑ i, Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) = S.D.dsum := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.filter_map, Multiset.card_map, TopData.d]
  exact congrArg _ (Multiset.filter_congr fun u _ => by simp)

theorem bijective_maxUnramifiedSubfield_algebraMap : Function.Bijective (algebraMap ↥(K0 S.K) ↥S.K.1) := by
  obtain ⟨⟨-, hA, -⟩, -⟩ := S.hyp
  exact ⟨RingHom.injective _, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩

theorem fSummand_of_finrank (hC : S.CrysCalc) (hH : S.FreeH)
    (hd : finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) = S.D.dsum) : S.FSummand :=
  ⟨exists_isCompl S hC hH, (finrank_hf S hC).trans hd⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem fSummand_of_dim (hC : S.CrysCalc) (hV : S.Vanish) (hH : S.FreeH)
    (hd : (finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) : ℤ) = (finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) : ℤ) +
      ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ)) : S.FSummand := by
  refine fSummand_of_finrank S hC hH ?_
  have h0 := tw_finrank_h0V S hC hV
  have h1 : ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ) = (S.D.dsum : ℤ) := by
    rw [← sum_card_neg S, Nat.cast_sum]
  have key : ∀ (a b c : ℕ) (s : ℤ), (a : ℤ) = (b : ℤ) + s → b = 0 → s = (c : ℤ) → a = c := by
    intro a b c s h h' h''
    omega
  exact key _ _ _ _ hd h0 h1

end GlobalTheory.TopSteps.FinSummandDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.LiftStep

theorem ev_eis_mul_mu {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : PiSys l e)
    {ε δ : OCb l} (hε : IsEps ε) (hδ : δ ^ l = ε) :
    ∃ u : Ainf l, IsUnit u ∧ ϖ.ev a (eis l a e) * muOf δ = u * muOf ε := by
  obtain ⟨⟨ξ, hξ, hμ⟩, -⟩ := (_root_.GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  have h : Associated (ϖ.ev a (eis l a e)) ξ := by
    rw [← Ideal.span_singleton_eq_span_singleton, hξ, PiSys.span_ev_eis]
  obtain ⟨v, hv⟩ := h
  refine ⟨((v⁻¹ : (Ainf l)ˣ) : Ainf l), Units.isUnit _, ?_⟩
  rw [hμ, ← hv]
  linear_combination (-(ϖ.ev a (eis l a e) * muOf δ)) * v.inv_mul

section Integral

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)

theorem E_pow_mul_iW (n : ℕ) (f : ZMod a → invE l e (A O K)) (hf : ∀ τ, E K l e ^ n * (f τ : K⟦X⟧) ∈ A O K) :
    inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ n * ϖ.iW t K f = inclO l O (ϖ.iTot t K fun τ => ⟨_, hf τ⟩) := by
  have h1 : inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) = ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) := by
    rw [← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  rw [h1, ← map_pow, ← map_mul, ← ϖ.iW_of_mem t K]
  congr 1

theorem integral (α β : ℕ) (hL : ∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) (hM : ∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) :
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * frobMat t ϖ P i j) ∧
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ β * frobMatInv t ϖ P i j) ∧
    ∀ y : ME P, y.1 ∈ P.EM α → ∀ i, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * toW t ϖ P y i := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun y hy i => ?_⟩
  · have hm : (fun τ k => P.mx τ k j) ∈ P.L := mem_tot.2 fun τ => Submodule.subset_span ⟨j, rfl⟩
    have h := mem_tot.1 (hL _ hm)
    exact ⟨_, (E_pow_mul_iW t ϖ α _ fun τ => h τ i).symm⟩
  · have hm : (fun (_ : ZMod a) (k : ι) => if k = j then (1 : K⟦X⟧) else 0) ∈ P.M :=
      mem_tot.2 fun τ k => by split_ifs <;> simp [Mc, mem_vecs]
    have h := fun τ => P.mem_extc_iff.1 (mem_tot.1 (hM _ hm) τ) i
    refine ⟨_, (E_pow_mul_iW t ϖ β (fun τ => ((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) i j) fun τ => ?_).symm⟩
    simpa [Matrix.mulVec, dotProduct, PhiMod.mxInv, mul_comm] using h τ
  · have h : ∀ τ, E K l e ^ α * (y.1 τ i) ∈ A O K := fun τ => by simpa using mem_tot.1 hy τ i
    refine ⟨ϖ.iTot t K fun τ => ⟨_, h τ⟩, ?_⟩
    rw [toW_apply]
    exact (E_pow_mul_iW t ϖ α (fun τ => ⟨y.1 τ i, mem_tot.1 y.2 τ i⟩) h).symm

end Integral

end GlobalTheory.BKGal.LiftStep

theorem GlobalTheory.BKGal.LiftStep.alg_step {S ι : Type} [CommRing S] [Fintype ι] (Ui Ew N Mh : S) (α β : ℕ)
    (hMN : Mh = Ui * Ew ^ (β + α) * N) (Xi : Matrix ι ι S) (m y : ι → S) (Yc : ι → ι → S) (yc : ι → S)
    (hY : ∀ i j, Yc i j = Ew ^ β * Xi i j) (hy : ∀ j, yc j = Ew ^ α * y j) :
    Mh • (Xi *ᵥ (m + y)) = (Matrix.of fun i j => Ui * Ew ^ α * Yc i j) *ᵥ (N • m) +
      fun i => Ui * ∑ j, Yc i j * (N * yc j) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, hY, hy, hMN,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


open GlobalTheory.BKGal.LiftStep in
theorem GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → ∀ (y : ME P), y.1 ∈ P.EM α → ∀ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P y → inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) • m₀ ∈ MA P ∧ inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) • phiW t ϖ P m₀ ∈ LA t ϖ P := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hL hM ε δ hε hδ y hy m₀ hm₀
  classical
  obtain ⟨u, hu, hEu⟩ := ev_eis_mul_mu a ϖ hε hδ
  have hfr : WittVector.frobenius (muOf δ) = muOf ε := ((_root_.GlobalTheory.MuOfEps.main l).2 ε δ hε hδ).2.1
  obtain ⟨-, hXi, hyI⟩ := integral t ϖ P α β hL hM
  choose cXi hcXi using hXi
  choose cy hcy using hyI y hy
  set ui : Ainf l := ((hu.unit⁻¹ : (Ainf l)ˣ) : Ainf l) with hui
  have hμ : muOf ε = ui * ϖ.ev a (eis l a e) * muOf δ := by
    rw [mul_assoc, hEu, ← mul_assoc, hui, IsUnit.val_inv_mul, one_mul]
  set Ew := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hEw
  set N := inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) with hN
  set Mh := inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) with hMh
  set Ui := inclO l O (1 ⊗ₜ (ui ^ (β + α))) with hUi
  have hMN : Mh = Ui * Ew ^ (β + α) * N := by
    rw [hMh, hUi, hEw, hN, ← map_pow, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, hμ, mul_pow, mul_pow]
  have hFN : frobOW l O N = Mh := by
    rw [hN, frobOW_inclO, frobOA_tmul, map_pow, hfr]
  set y' := toW t ϖ P y with hy'
  have hF : (fun i => frobOW l O (m₀ i)) = frobMatInv t ϖ P *ᵥ (m₀ + y') := by
    have h1 : frobMat t ϖ P *ᵥ (fun i => frobOW l O (m₀ i)) = m₀ + y' := by
      rw [← phiW_apply]; exact sub_eq_iff_eq_add'.1 hm₀
    rw [← h1, Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec]
  set z : ι → OW l O := N • m₀ with hz
  have hFz : (fun i => frobOW l O (z i)) = Mh • (fun i => frobOW l O (m₀ i)) := by
    funext i
    simp only [hz, Pi.smul_apply, smul_eq_mul, map_mul, hFN]
  set Y : Matrix ι ι (OA l O) := fun i j => (1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j
  set w : ι → OA l O := fun i => (1 ⊗ₜ (ui ^ (β + α))) * ∑ j, cXi i j * ((1 ⊗ₜ (muOf δ ^ (β + α))) * cy j)
  have heq : (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) := by
    rw [hFz, hF, alg_step Ui Ew N Mh α β hMN (frobMatInv t ϖ P) m₀ y' (fun i j => inclO l O (cXi i j))
      (fun j => inclO l O (cy j)) hcXi hcy]
    congr 2
    · ext i j
      change _ = inclO l O ((1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j)
      rw [map_mul, map_mul, map_pow]
      rfl
    · funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, map_mul, map_sum]
      rfl
  have hint := _root_.GlobalTheory.FrobIntO.frobenius_integrality_vec_O l O ι Y w z heq
  choose c hc using hint
  refine ⟨⟨c, funext fun i => hc i⟩, ⟨fun i => frobOA l O (c i), ?_⟩⟩
  rw [inclL_apply, phiW_apply, ← Matrix.mulVec_smul, ← hFz]
  congr 1
  funext i
  rw [← frobOW_inclO]
  exact congrArg _ (hc i)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem ne_one_of_isEps {l : ℕ} [hl : Fact l.Prime] {ε : OCb l} (hε : GlobalTheory.MemLoc.IsEps ε) : ε ≠ 1 := by
  rintro rfl
  exact hε.2 (by simp)

theorem coeff_zero_ne_zero_of_isPer {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l}
    (hτ : bk.IsPer τ) : τ.coeff 0 ≠ 0 := by
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  intro h
  have h1 := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) hφ
  simp only [map_mul, map_sub, map_one, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    WittVector.teichmuller_coeff_zero, h] at h1
  rw [zero_pow hl.out.ne_zero] at h1
  have hη : (η : Ainf l).coeff 0 ≠ 0 := by
    have := η.isUnit.map (WittVector.constantCoeff (p := l) (R := OCb l))
    rw [WittVector.constantCoeff_apply] at this
    exact this.ne_zero
  exact mul_ne_zero hη (sub_ne_zero.2 (ne_one_of_isEps hε)) h1.symm

theorem ρ₀_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)
  exact ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩

theorem isUnit_inclW_of_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    IsUnit (inclW l τ) ∧ bk.iA τ ≠ 0 ∧ τ ≠ 0 ∧ ∀ g : GQ l, IsUnit (inclW l (Per.σA g τ)) := by
  intro l _ K bk τ hτ
  have h0 := coeff_zero_ne_zero_of_isPer bk hτ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact h0 (WittVector.zero_coeff _ _ _)
  have hU : IsUnit (inclW l τ) := by
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [inclW, WittVector.map_coeff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 h0
  obtain ⟨ι, ⟨tb⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ (ρ₀_pos_lt_one bk).1 (ρ₀_pos_lt_one bk).2).1
  refine ⟨hU, fun h => hτ0 (hinj (h.trans (map_zero _).symm)), hτ0, fun g => ?_⟩
  rw [← galW_inclW]
  exact hU.map (galW l g)

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalBasisAndSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∃ b : ι → E.M (ϖ.prism a), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) ∧ ∀ x : E.M (ϖ.prism a), ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → (ϖ.prism a).A), x = ∑ j, ∑ q, s j q • (oE (c j q)).u (ϖ.prism a) (b j) := by
  first | exact @GlobalTheory.BKBasis.main | exact GlobalTheory.BKBasis.main | (intros; apply GlobalTheory.BKBasis.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_nonZeroDivisors_of_invertible_span {A : Type} [CommRing A] {I : Ideal A}
    (hI : Module.Invertible A ↥I) {d : A} (hd : I = Ideal.span {d}) : d ∈ nonZeroDivisors A := by
  have hdI : d ∈ I := hd ▸ Ideal.mem_span_singleton_self d
  let φ : A →ₗ[A] ↥I := LinearMap.toSpanSingleton A ↥I ⟨d, hdI⟩
  have hs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [hd] at hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact ⟨a, Subtype.ext (by simp [φ])⟩
  have hb := Module.Invertible.bijective_of_surjective hs
  refine mem_nonZeroDivisors_iff.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine hb.1 (?_ : φ a = φ 0)
    exact Subtype.ext (by simp [φ]; linear_combination ha)
  · refine hb.1 (?_ : φ a = φ 0)
    exact Subtype.ext (by simp [φ]; linear_combination ha)

theorem associated_of_span_eq {A : Type} [CommRing A] {d d' : A} (hd : d ∈ nonZeroDivisors A)
    (h : Ideal.span {d} = Ideal.span {d'}) : Associated d d' := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self d)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self d')
  have hab : a * b = 1 := by
    have : d * (a * b - 1) = 0 := by linear_combination a * hb + ha
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hd).1 _ this)
  exact ⟨⟨b, a, by rw [mul_comm]; exact hab, hab⟩, by rw [Units.val_mk, mul_comm]; exact hb⟩

theorem hf_E_pair : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B),
    BK.hf f bk.E ∈ nonZeroDivisors B.A ∧ Associated (BK.hf f bk.E) (BK.hf g bk.E) ∧
      BK.hf f bk.E ∣ BK.hf g X - BK.hf f X := by
  intro l _ K bk B f g
  obtain ⟨hfI, hfX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B f
  obtain ⟨hgI, hgX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B g
  have hreg := mem_nonZeroDivisors_of_invertible_span B.inv hfI
  refine ⟨hreg, associated_of_span_eq hreg (hfI.symm.trans hgI), ?_⟩
  rw [← Ideal.mem_span_singleton, ← hfI]
  exact Ideal.Quotient.eq.1 (hgX.trans hfX.symm)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinValueMulEisensteinPowEqSum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

namespace GlobalTheory.BKGal.HatVal

theorem value_mul_E_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hy b₂ hval c hc Y hY
  obtain ⟨m, c', hu, hmc, hmb⟩ := hval
  set E0 : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) with hE0
  have hEW : ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) = inclO l O E0 := by
    rw [hE0, ← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  have hYi : ∀ i, inclO l O (ϖ.iTot t K (Y i)) = inclO l O E0 ^ η * toW t ϖ D.toPhiMod ⟨y, hy⟩ i := by
    intro i
    rw [← ϖ.iW_of_mem t K, toW_apply, ← hEW, ← map_pow, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp [hY, EIn]
  set S : ι → OA l O := fun i => ∑ j, ϖ.iTot t K (Y j) * c j i with hSdef
  have hS : inclL t ϖ D.toPhiMod S = inclO l O (E0 ^ (H + η)) • toW t ϖ D.toPhiMod ⟨y, hy⟩ := by
    have h1 : S = ∑ j, fun i => ϖ.iTot t K (Y j) * c j i := by
      funext i; simp [hSdef, Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    simp only [inclL_smul_coord, hc]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hYi i, pow_add]
    simp only [map_mul, map_pow]
    ring
  have hkey : (fun i => m * S i) = fun i => E0 ^ (H + η) * c' i := by
    apply inclL_injective t ϖ D.toPhiMod
    rw [inclL_smul_coord, inclL_smul_coord, hS, ← hmc, smul_smul, smul_smul, mul_comm]
  have h2 := congrArg (fun v : ι → OA l O => R.jB fun i => toB l O (v i)) hkey
  have hL : (fun i => toB l O (m * S i)) = toB l O m • ∑ j, toB l O (ϖ.iTot t K (Y j)) • fun i => toB l O (c j i) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hSdef, Finset.sum_apply, Finset.mul_sum, map_sum]
  have hR : (fun i => toB l O (E0 ^ (H + η) * c' i)) = toB l O E0 ^ (H + η) • fun i => toB l O (c' i) := by
    funext i
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, hR, map_smul, map_smul, ← hmb, map_sum] at h2
  simp only [map_smul] at h2
  rw [smul_smul, mul_comm, ← smul_smul] at h2
  exact (hu.smul_left_cancel).1 h2.symm

end GlobalTheory.BKGal.HatVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffCoeffPowEqOfBox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory

theorem coeff_coeff_pow_eq_of_box :
    ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧),
      (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  intro R _ m i n G H h
  induction m generalizing i n with
  | zero => simp
  | succ k ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨p, q⟩ hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl ?_
    rintro ⟨s, t⟩ hst
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hst
    dsimp only at hpq hst ⊢
    rw [ih p s (fun i' hi' n' hn' => h i' (by omega) n' (by omega)), h q (by omega) t (by omega)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetPencilMemHeckeAlgebraStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_det_pencil_mem_heckeAlgebra : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ a b : X → Matrix (Fin n) (Fin n) O, InRing T rep a → InRing T rep b → ∀ j : ℕ, (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) + (b x).map (Polynomial.C (R := O)))).coeff j) ∈ T := by
  first | exact @GlobalTheory.SpanRing.coeff_det_pencil_mem | exact GlobalTheory.SpanRing.coeff_det_pencil_mem | (intros; apply GlobalTheory.SpanRing.coeff_det_pencil_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationVStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → Function.Bijective (A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e))) ∧ ∀ (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ), y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j) ↔ A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j + 1) := by
  first | exact @GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff | exact GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff | (intros; apply GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff <;> assumption)
end

