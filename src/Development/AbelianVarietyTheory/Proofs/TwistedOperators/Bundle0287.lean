module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfInvariantFormIsotropicAverageNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}

theorem res_smul_twisted_operators {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (a : ℂ) (F : WO V W → ℂ) : res V V' W C B μ 𝓨 (a • F) = a • res V V' W C B μ 𝓨 F :=
  funext fun x => integral_const_mul a _

set_option maxHeartbeats 1000000 in
theorem avgForm_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∃ ℓ' : (WO V' W → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO V' W, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ V' W f → ℓ' (heisO ψ V' W u f) = ℓ' f) ∧ ∃ f, IsThetaFunO ψ V W f ∧ avgForm ψ V V' W C B μ 𝓨 K e ℓ' f ≠ 0 := by
  intro D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he
  have hR := _root_.GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hμ
  have hth : ∀ {f : WO V W → ℂ}, IsThetaFunO ψ V W f → ∀ u, IsThetaFunO ψ V W (heisO ψ V W u f) :=
    fun hf u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  obtain ⟨f₁, hf₁, hres₁⟩ := hR.2
  obtain ⟨ℓ', hℓ', s, hs', hℓs⟩ : ∃ ℓ' : (WO V' W → ℂ) →ₗ[ℂ] ℂ, (∀ u, IsHalf (cA D e) u → ∀ f,
      IsThetaFunO ψ V' W f → ℓ' (heisO ψ V' W u f) = ℓ' f) ∧
      ∃ s, IsHalf e s ∧ ℓ' (heisO ψ V' W s (res V V' W C B μ 𝓨 f₁)) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hres₁ (GlobalTheory.ThetaStalk.eq_zero_of_invariant_forms D ψ hψ V' W e he _ (hR.1 f₁ hf₁).2.1 h)
  have hf₂ : IsThetaFunO ψ V W (heisO ψ V W (midPart V V' W B s) f₁) := hth hf₁ _
  have h0 : ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B s) f₁)) ≠ 0 := by
    rw [(hR.1 f₁ hf₁).2.2.1 s]; exact hℓs
  refine ⟨ℓ', fun u hu f hf => hℓ' u hu f hf, ?_⟩
  by_contra hall
  push_neg at hall
  obtain ⟨L, Kc, hL, hKc, hz, hloc⟩ := GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he _ hf₂
  obtain ⟨L', hL', hL'L, hsep⟩ := _root_.GlobalTheory.HalfSeparate.exists_open_separated D ψ hψ W r e he L hL
  have hφ := _root_.GlobalTheory.fourier_uniqueness_of_openSubgroup (haarHalf (cA D e) W.rank r)
    (fun (a : halfMx e W.rank r) (t : halfMx (cA D e) W.rank r) => ψ (halfSympl W (a : Mx D W.rank r) (t : Mx D W.rank r)))
    (fun a s t => by simp only [AddSubgroup.coe_add, halfSympl_add_right, AddChar.map_add_eq_mul])
    (fun a => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_right, AddChar.map_zero_eq_one])
    (fun t => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_left, AddChar.map_zero_eq_one])
    (fun a b t => by simp only [AddSubgroup.coe_add, halfSympl_add_left, AddChar.map_add_eq_mul])
    L' hL' hsep
    (fun t => ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) (heisO ψ V W (midPart V V' W B s) f₁))))
    Kc hKc (fun t ht => by simp only [hz t ht, map_zero])
    (fun t l hl => by simp only [hloc t l (hL'L hl)])
    (fun a _ => by
      rw [← hall _ (hth hf₂ (isoPart V W C (a : Mx D W.rank r)))]
      unfold avgForm
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [GlobalTheory.ThetaStalk.heisO_comm (restEmb V W K (t : Mx D W.rank r)) (isoPart V W C (a : Mx D W.rank r)), res_smul_twisted_operators, map_smul, smul_eq_mul,
        (hR.1 _ (hth hf₂ _)).2.2.2 (a : Mx D W.rank r), _root_.GlobalTheory.HalfAverage.sympl_restEmb_isoPart D V V' W r C B hs K hKC])
  apply h0
  have := congrFun hφ 0
  simpa [restEmb, GlobalTheory.SplitScalar.heisO_zero] using this

end GlobalTheory.HalfAverage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpsTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.OpsRowsTuple

theorem offS_badPl_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (w : Pl D.host.E) :
    OffS D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) w ↔ GlobalTheory.Hk3.Good R t w := by
  classical
  rw [GlobalTheory.GoodPrimes.offS_iff]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  refine forall₂_congr fun PP _ => ⟨fun h => ⟨fun e => h (by rw [e]), fun e => h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩, fun h e => ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact h.1 h1.symm
  · exact h.2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

theorem exists_ops_tuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ t : T, ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H, (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) ∧ GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h ∧ (∀ (c : Pl D.host.E → List ℤ → ℂ) P, GlobalTheory.Hk3.Good R t P → ∀ cc, ∀ x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, h P cc x = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, (∀ P d, GlobalTheory.Hk3.Good R t P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = c P (dualLab d) • x) → x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t
  have hgp := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hg := hgp.2.1
  have hoff := offS_badPl_iff R t
  have h0 : ∀ P, Good R t P → Good R A.μ0 P := fun P hP => (hg t P hP).2.2
  have hβ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  cases hβ with
  | intro n hβ =>
  have lev := fun P (hP : Good R t P) => _root_.GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hg _ P (h0 P hP)).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => h0 P hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have H := GlobalTheory.Hk3.OpsRows.exists_ops (θ := R.θ) (M := R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) R.ν0 R.fd0 hC.models.inf hC.models.ν0.1.1 hC.models.ν0.2
    hS.2.1 R.HE _ hC.models.HE (goodPart_le _ _ _ _ _) (Good R t)
    (fun P d B => ⟨fun hB => by
        have hP : Good R t P := by
          obtain ⟨_, _, _, _, hO, -⟩ := hB
          exact (hoff P).1 hO
        exact ⟨hP, (((lev P hP).2.1 _ d B).1 hB).2⟩,
      fun hB => ((lev P hB.1).2.1 _ d B).2 ⟨(hoff P).2 hB.1, hB.2⟩⟩)
    (fun P hP => (lev P hP).1)
    (fun P hP c U hU => by
      obtain ⟨hU1, hU2⟩ := (mem_goodPart _ _ _ _ _ _).1 hU
      refine (mem_goodPart _ _ _ _ _ _).2 ⟨(lev P hP).2.2.2.2 _ _ _ c hC.models.inf U hU1, fun v => ?_⟩
      have hfix : ∀ k ∈ hyp (Yc D 0) P, ∀ g, U v (g * k) = U v g := fun k hk g => by
        rw [GlobalTheory.Hk3.OpsRows.mult_lev hU1 v k ((lev P hP).1 k hk).1 g, ((lev P hP).1 k hk).2, one_mul]
      rw [postOn_apply]
      conv_rhs => rw [← hU2 v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [RealDat.e0, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      exact (lev P hP).2.2.2.1 c _ _ hfix)
  cases H with
  | intro h H2 =>
  exact ⟨h, H2.1, H2.2.1, fun c => H2.2.2.2.1 _, fun c => H2.2.2.2.2 _⟩

end GlobalTheory.Hk3.OpsRowsTuple

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsNeProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 1000000 in
theorem exists_part (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hs : A.fam.Ok s) (hC : GlobalTheory.Hk3.Core R F)
    (hS : GlobalTheory.Hk3.SchurAll R) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hSF : GlobalTheory.Hk3.IsSF R SF) (b : Bool)
    (i : Fin D.R.m) (hi : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥) :
    ∃ c, ∃ z ∈ GlobalTheory.Hk3.Wcc R SF i c, z ≠ 0 ∧ (R.HW i (sg0 D A)).e z ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) := by
  classical
  have irr : ∀ χ ∈ A.X, IsAbsIrrChar χ := hs.irr
  obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hi
  have hWall : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≤ R.Wall i (sg0 D A) :=
    (GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _).trans inf_le_left
  have hR : LinearMap.range (R.HW i (sg0 D A)).e = R.Wall i (sg0 D A) := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, rfl⟩ : y ∈ LinearMap.range (R.HW i (sg0 D A)).e := hR ▸ hWall hy
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  obtain ⟨hxe, hxt⟩ := (GlobalTheory.WatType.wat_iff_type R F hs hC b i x).1 hy
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS irr SF hSF i
  obtain ⟨hidem, -, -, -⟩ := GlobalTheory.Hk3.eH_laws R F hC irr i
  obtain ⟨lam, hlam⟩ : ∃ lam : (F.lvl b).P → ℂ, ∀ p, lam p = sg0 D A ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) :=
    ⟨_, fun _ => rfl⟩
  have lam_mul : ∀ p q, lam (p * q) = lam p * lam q := fun p q => by
    simp only [hlam, map_mul, Units.val_mul]
  have lam_ne : ∀ p, lam p ≠ 0 := fun p => by rw [hlam]; exact (map_ne_zero _).2 (Units.ne_zero _)
  have hxt' : ∀ p : (F.lvl b).P, R.gW i (sg0 D A) (p : G) x = lam p • x := fun p => by rw [hlam]; exact hxt p
  obtain ⟨π, hπ⟩ : ∃ π : Module.End ℂ (R.HW i (sg0 D A)).H,
      ∀ w, π w = ∑ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G) w :=
    ⟨∑ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G), fun w => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]⟩
  have htype : ∀ w (q : (F.lvl b).P), R.gW i (sg0 D A) (q : G) (π w) = lam q • π w := by
    intro w q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hπ, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun p => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, smul_smul, Equiv.coe_mulLeft]
    show (lam p)⁻¹ • R.gW i (sg0 D A) ((q : G) * p) w =
      (lam q * (lam (q * p))⁻¹) • R.gW i (sg0 D A) ((q * p : (F.lvl b).P) : G) w
    rw [lam_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (lam_ne q), one_mul]
    exact congrArg (fun g => (lam p)⁻¹ • R.gW i (sg0 D A) g w) (Subgroup.coe_mul _ q p).symm
  have hπmem : ∀ c w, w ∈ GlobalTheory.Hk3.Wcc R SF i c → π w ∈ GlobalTheory.Hk3.Wcc R SF i c := by
    intro c w hw
    rw [hπ]
    refine Submodule.sum_mem _ fun p _ => ?_
    refine Submodule.smul_mem _ _ ?_
    have h2 : R.gW i (sg0 D A) (p : G) w ∈ (GlobalTheory.Hk3.Wcc R SF i c).map (R.gW i (sg0 D A) (p : G)) :=
      Submodule.mem_map_of_mem hw
    exact hstab c (p : G) h2
  have hfix : π x = (Fintype.card (F.lvl b).P : ℂ) • x := by
    have h1 : ∀ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G) x = x := fun p => by
      rw [hxt' p, smul_smul, inv_mul_cancel₀ (lam_ne p), one_smul]
    rw [hπ, Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hπx : π x ≠ 0 := by
    intro h0
    apply hx0
    have hc : (Fintype.card (F.lvl b).P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h3 := congrArg (fun z => (Fintype.card (F.lvl b).P : ℂ)⁻¹ • z) (hfix.symm.trans h0)
    rwa [smul_zero, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
  have hxR := hsup.ge (LinearMap.mem_range.2 ⟨x, hxe⟩)
  have hmem := (Submodule.map_iSup π (fun c => GlobalTheory.Hk3.Wcc R SF i c)).le (Submodule.mem_map_of_mem (f := π) hxR)
  by_contra hall
  push_neg at hall
  have hbot : ∀ c, (GlobalTheory.Hk3.Wcc R SF i c).map π = ⊥ := by
    intro c
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hz : π w ∈ GlobalTheory.Hk3.Wcc R SF i c := hπmem c w hw
    have he : GlobalTheory.Hk3.eH R i (π w) = π w := by
      obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (hsup.le (Submodule.mem_iSup_of_mem c hz))
      rw [← hu, ← Module.End.mul_apply, hidem]
    by_contra h0
    exact hall c (π w) hz h0
      ((GlobalTheory.WatType.wat_iff_type R F hs hC b i _).2 ⟨he, fun p => by rw [htype w p, hlam]⟩)
  simp only [hbot, iSup_bot, Submodule.mem_bot] at hmem
  exact hπx hmem

theorem rowsNe : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF → (∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥) → RowsNe R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hs hC hS SF hSF hTR hW b
  obtain ⟨i, hi⟩ := hW b
  obtain ⟨c, z, hzc, hz0, hzW⟩ := exists_part R F hs hC hS SF hSF b i hi
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hez : (R.HW i (sg0 D A)).e z ≠ 0 := fun h => hz0 (hinj (h.trans (map_zero _).symm))
  have hzc' := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hzc)).2
  have hpart : (R.HW i (sg0 D A)).e z ∈ GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (R.eWf i (sg0 D A)) SF c := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hzW).1, ?_⟩, hzW⟩
    have h1 := (Submodule.mem_inf.1 hzc').2
    simp only [Submodule.mem_iInf] at h1 ⊢
    exact fun P d B hB => h1 P d B (_root_.GlobalTheory.LevOpFace.heckeOp_face_to_principal R F hC SF hSF b i P d B hB)
  have hne : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (R.eWf i (sg0 D A)) SF c ≠ ⊥ := fun h => hez ((Submodule.mem_bot ℂ).1 (h ▸ hpart))
  have hr := (hTR i).2 b c
  intro hE
  apply hne
  rw [← Submodule.rank_eq_zero, ← hr, Submodule.rank_eq_zero]
  exact eq_bot_iff.2 (inf_le_right.trans hE.le)

end GlobalTheory.RowsNeProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.ParamBound

section General

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem heckeVec_map_of_injective {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {K : Subgroup G}
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (hρ : ∀ g y, f (ρ g y) = ρ' g (f y)) (h : G → ℂ) (x : V) :
    f (heckeVec ρ K h x) = heckeVec ρ' K h (f x) := by
  unfold heckeVec
  have hs : (Function.support fun c : G ⧸ K => h c.out • ρ' c.out (f x)) =
      Function.support fun c : G ⧸ K => h c.out • ρ c.out x := by
    ext c
    simp only [Function.mem_support, ne_eq, ← hρ, ← map_smul]
    exact not_congr (map_eq_zero_iff f hf)
  by_cases hfin : (Function.support fun c : G ⧸ K => h c.out • ρ c.out x).Finite
  · rw [map_finsum f hfin]
    simp only [map_smul, hρ]
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (hs ▸ hfin), map_zero]

theorem comp_mem_hecke (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {h' : H → ℂ} (hh : h' ∈ Hecke ℂ K') : h' ∘ e ∈ Hecke ℂ K := by
  classical
  obtain ⟨h1, S, hS⟩ := hh
  refine ⟨fun a b g => ?_, S.image e.symm, fun g hg => ?_⟩
  · show h' (e (a * g * b)) = h' (e g)
    rw [map_mul, map_mul]
    exact h1 ⟨e a, (hK a).1 a.2⟩ ⟨e b, (hK b).1 b.2⟩ (e g)
  · obtain ⟨s, hs, a, b, hab⟩ := hS (e g) hg
    refine ⟨e.symm s, Finset.mem_image_of_mem _ hs, ⟨e.symm a, (hK _).2 (by simp)⟩,
      ⟨e.symm b, (hK _).2 (by simp)⟩, ?_⟩
    apply e.injective
    simp [hab]

theorem isUnitarisable_comp {ρ : Representation ℂ G V} (hρ : IsUnitarisable ρ) (φ : H →* G) :
    IsUnitarisable (ρ.comp φ) := by
  obtain ⟨B, h1, h2, h3⟩ := hρ
  exact ⟨B, h1, h2, fun g => h3 (φ g)⟩

end General

theorem norm_le_of_mem_bcParam {q n : ℕ} (hq : 2 ≤ q) {α : Fin (n / 2) → ℂˣ}
    (hα : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α) :
    ∀ b ∈ bcParam n α, ‖(b : ℂ)‖ ≤ ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) := by
  intro b hb
  simp only [bcParam, Multiset.mem_add, Multiset.mem_map, Finset.mem_univ_val, true_and,
    Multiset.mem_replicate] at hb
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  rcases hb with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨hn, rfl⟩
  · exact (hα i).2
  · rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hq2 _
    calc ‖(α i : ℂ)‖⁻¹ ≤ (((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)))⁻¹ := inv_anti₀ hpos (hα i).1
      _ = _ := by rw [Real.rpow_neg hq2.le, inv_inv]
  · simp only [Units.val_one, norm_one]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    exact Real.one_le_rpow (by nlinarith) (by linarith)

theorem exists_param_at (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hJ : SphOff J χ Sb) (f : GA D V → ℂ) (hfm : f ∈ bddAut V)
    (hf0 : f ≠ 0) (hlev : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (hc : ∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : v ∉ Sb) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : w.under (𝓞 D.host.F) = v) :
    ∃ B : Multiset ℂˣ, IsParamVec D.sp.cm.sig V.gram (frameLat V) h
        ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) f B ∧
      ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
  obtain ⟨hfix, heig⟩ := _root_.GlobalTheory.FinZeta.eigen_heckeAlg D V J χ Sb hJ v hv f hlev c hc
  let ρ : Representation ℂ (Gv V v) (bddAut V) := (bddRep V).comp (embV V v)
  let x : bddAut V := ⟨f, hfm⟩
  have hx0 : x ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
  have hint : ∀ g y, (bddAut V).subtype (ρ g y) =
      ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) g ((bddAut V).subtype y) := fun _ _ => rfl
  have hxfix : x ∈ fixed ρ (Kv V v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ((GlobalTheory.LGrp.mem_fixed.1 hfix) k hk)
  have hxeig : ∀ hh ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ρ (Kv V v) hh x = a • x := fun hh hm => by
    obtain ⟨a, ha⟩ := heig hh hm
    refine ⟨a, Subtype.val_injective ?_⟩
    have := heckeVec_map_of_injective (K := Kv V v) (bddAut V).subtype Subtype.val_injective hint hh x
    exact this.trans ha
  have hρU : IsUnitarisable ρ := isUnitarisable_comp (_root_.GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded D V).1 _
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    haveI := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases (exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w', hw'⟩
  · obtain ⟨e, he, -, -⟩ := SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hspan h hs hd
    have hfix' := (mem_fixed_comp_symm (ρ := ρ) e he.2).2 hxfix
    obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL D.host.E w V.rank (bddAut V) (ρ.comp e.symm.toMonoidHom)
      (isUnitarisable_comp hρU _) x hx0 hfix' fun h' hh' => by
        rw [heckeVec_comp_symm e he.2 hh'.1 hxfix]
        exact hxeig _ (comp_mem_hecke e he.2 hh')
    exact ⟨B, Or.inl ⟨hs, e, he, hB.map (bddAut V).subtype (fun g y => rfl) hf0⟩, fun b hb => (hbd b hb).1⟩
  · have h' : w'.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext (v.isMaximal.eq_of_le
      (Ideal.comap_ne_top _ w'.isPrime.ne_top) (Ideal.map_le_iff_le_comap.1 (le_of_eq hw'))).symm
    obtain ⟨-, -, huniq, -, -⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w' h' hw'
    obtain rfl : w = w' := (huniq w).1 h
    obtain ⟨-, ⟨τ, hτ, -⟩, -, hnorm, hconj⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w h hw'
    obtain ⟨⟨ϖ, hϖ⟩, hch⟩ := hconj τ hτ
    obtain ⟨e, he, -, -⟩ := hch V.rank V.gram (frameLat V) hH hL.fg hspan hd
    have hfix' := (mem_fixed_comp_symm (ρ := ρ) e he.2.2).2 hxfix
    obtain ⟨α, hα, hbd⟩ := _root_.GlobalTheory.Twist.satParam_exists_trivialBound (w.adicCompletion D.host.E) ϖ τ (qV D.host.F v) V.rank hϖ (bddAut V)
      (ρ.comp e.symm.toMonoidHom) (isUnitarisable_comp hρU _) x hx0 hfix' fun h'' hh'' => by
        rw [heckeVec_comp_symm e he.2.2 hh''.1 hxfix]
        exact hxeig _ (comp_mem_hecke e he.2.2 hh'')
    refine ⟨bcParam V.rank α,
      Or.inr ⟨hw', τ, ϖ, e, α, hϖ, he, hα.map hϖ (bddAut V).subtype (fun g y => rfl) hf0, rfl⟩, ?_⟩
    intro b hb
    rw [hnorm, Nat.cast_pow]
    exact norm_le_of_mem_bcParam hϖ.2.2.2.2.2.1 hbd b hb

end GlobalTheory.FinZeta.ParamBound

namespace GlobalTheory.FinZeta.ParamBound

theorem exists_param_bounded : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ f ∈ bddAut V, f ≠ 0 → (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → ∃ B : Fam D.host.E, IsParamFunV V Sb f B ∧ Bounded (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) B V.rank (((V.rank : ℝ) - 1) / 2) := by
  intro D V J χ Sb hJ f hfm hf0 hlev c hc
  classical
  have key := fun (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : v ∉ Sb) (w : HeightOneSpectrum (𝓞 D.host.E))
      (h : w.under (𝓞 D.host.F) = v) => exists_param_at D V J χ Sb hJ f hfm hf0 hlev c hc v hv w h
  let B : Fam D.host.E := fun w =>
    if hw : w.under (𝓞 D.host.F) ∉ Sb then (key _ hw w rfl).choose else 0
  have hB : ∀ w (hw : w.under (𝓞 D.host.F) ∉ Sb), B w = (key _ hw w rfl).choose := fun w hw => dif_pos hw
  refine ⟨B, ?_, ?_⟩
  · intro v hv w h
    subst h
    have hv' : w.under (𝓞 D.host.F) ∉ Sb := hv
    rw [hB w hv']
    exact (key _ hv' w rfl).choose_spec.1
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ Sb := hw
    rw [hB w hw']
    exact ⟨(IsParamVec.card (key _ hw' w rfl).choose_spec.1).le, (key _ hw' w rfl).choose_spec.2⟩

end GlobalTheory.FinZeta.ParamBound

end
end

