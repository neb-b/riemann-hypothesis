module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetVectorsNonzeroDepthFockVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosDep

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem isHalf_smul {e : AE D} {u : WO S T} (hu : IsHalf e u) (z : AE D) : IsHalf e (z • u) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [mul_left_comm, hu i j]

theorem isHalf_add {e : AE D} {u v : WO S T} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_sub {e : AE D} {u v : WO S T} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u - v) := fun i j => by
  simp only [Matrix.sub_apply, mul_sub, hu i j, hv i j]

theorem isHalf_idem {e : AE D} (he : e * e = e) (u : WO S T) : IsHalf e (e • u) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem mxAt_of_isHalf {e : AE D} (hinf : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) : MxAt (fun _ => True) u :=
  fun i j => by
    refine Ideal.mem_inf.2 ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, ← hu i j, map_mul, hinf, zero_mul]
    · refine Submodule.mem_iInf _ |>.2 fun w => ?_
      exact absurd trivial w.2

theorem cosInd_add {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos ΛS ΛT 𝔪) {u : WO S T} (hu : IsHalf e u)
    (hm : u ∈ hatMx (𝔪 • homLat ΛS ΛT)) (t : WO S T) : cosInd e κ (t + u) = cosInd e κ t := by
  have key : ∀ (t v : WO S T), IsHalf e v → v ∈ hatMx (𝔪 • homLat ΛS ΛT) → t ∈ cosSet e κ → t + v ∈ cosSet e κ := by
    rintro t v hv hvm ⟨ht, x₀, hx₀, hd⟩
    refine ⟨isHalf_add ht hv, x₀, hx₀, ?_⟩
    rw [add_sub_right_comm]
    exact add_mem hd hvm
  unfold cosInd
  by_cases h : t ∈ cosSet e κ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key t u hu hm h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro h'
    apply h
    have hn : IsHalf e (-u) := fun i j => by simp only [Matrix.neg_apply, mul_neg, hu i j]
    simpa using key (t + u) (-u) hn (neg_mem hm) h'

variable {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}

theorem heisO_fix_trans (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (hΦ : IsSBHalf e Λ Φ) {u : WO S T}
    (hu : IsHalf e u) (hinv : ∀ t, Φ (t + u) = Φ t) : heisO ψ S T u f = f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  rw [hall Tm hT, ← hT.trans Φ hΦ u hu]
  congr 1
  funext t
  exact hinv t

theorem heisO_fix_modul (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (hΦ : IsSBHalf e Λ Φ) {y : WO S T}
    (hy : IsHalf (cA D e) y) (hinv : ∀ t, Φ t ≠ 0 → ψ (symplO S T t y) = 1) : heisO ψ S T y f = f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  rw [hall Tm hT, ← hT.modul Φ hΦ y hy]
  congr 1
  funext t
  by_cases h0 : Φ t = 0
  · rw [h0, mul_zero]
  · rw [hinv t h0, one_mul]

end GlobalTheory.CosDep

namespace GlobalTheory.CosDep

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ}

theorem isLatVac_of_cos (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (κ : Cos ΛS ΛT 𝔪) (hcos : ∀ t ∈ cosSet e κ, t ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
    {f₀ f : WO S T → ℂ} (hf₀ : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) f₀)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ (cosInd e κ) f)
    {Γ : AddSubgroup (WO S T)}
    (hΓ : ∀ u ∈ Γ, u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ∧ e • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) :
    IsLatVac (heisO ψ S T) Γ f := by
  have e1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have e2 : e * cA D e = 0 := he.2
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, e1]
  have c2 : cA D e * e = 0 := by rw [mul_comm, e2]
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd hS hT h𝔪 e1 hinf κ
  have ann : ∀ x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), MxAt (fun _ => True) x →
      ∀ y ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), ψ (symplO S T x y) = 1 := fun x hx hx' =>
    (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T ΛS ΛT hS hT (fun _ => True) x hx').1 hx

  have hA : ∀ v, IsHalf e v → v ∈ hatMx (𝔪 • homLat ΛS ΛT) → heisO ψ S T v f = f := fun v hv hm =>
    heisO_fix_trans h hSB hv (cosInd_add κ hv hm)

  have hB : ∀ v, IsHalf (cA D e) v → v ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → heisO ψ S T v f = f :=
    fun v hv hm => heisO_fix_modul h hSB hv fun t ht => by
      have htc : t ∈ cosSet e κ := Set.mem_of_indicator_ne_zero ht
      exact ann t (hcos t htc) (mxAt_of_isHalf hinf htc.1) v hm

  have hC : ∀ r : WO S T, (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) → heisO ψ S T r f₀ = f₀ → heisO ψ S T r f = f :=
    fun r hr h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ _ f h r hr h0
  have hoff : ∀ u : WO S T, ∀ i j, e * (u - e • u - cA D e • u) i j = 0 ∧ cA D e * (u - e • u - cA D e • u) i j = 0 :=
    fun u i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      constructor
      · linear_combination (-(u i j)) * e1 + (-(u i j)) * e2
      · linear_combination (-(u i j)) * c2 + (-(u i j)) * c1
  have hdec : ∀ u : WO S T, u = e • u + (cA D e • u + (u - e • u - cA D e • u)) := fun u => by abel

  have dbl : ∀ a b r : WO S T, IsHalf e a → a ∈ hatMx (𝔪 • homLat ΛS ΛT) →
      a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → IsHalf (cA D e) b →
      b ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → r ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) →
      (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) → heisO ψ S T (2 • (a + (b + r))) f = f := by
    intro a b r hae ham hal hbe hbl hrl hr0
    have h2 : 2 • (a + (b + r)) = (a + a) + (b + b + (r + r)) := by rw [two_nsmul]; abel
    have hph : ψ (symplOH S T (a + a) (b + b + (r + r))) = 1 := by
      rw [GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self]
      exact ann a hal (mxAt_of_isHalf hinf hae) _ (add_mem (add_mem hbl hbl) (add_mem hrl hrl))
    have hbr : symplO S T (b + b) (r + r) = 0 := GlobalTheory.Hk3.symplO_half_off S T (isHalf_add hbe hbe) fun i j => by
      rw [GlobalTheory.DualPairCheck.cA_cA, Matrix.add_apply, mul_add, (hr0 i j).1, add_zero]
    have hrr : heisO ψ S T (r + r) f = f := hC _ (fun i j => by
        simp only [Matrix.add_apply, mul_add, (hr0 i j).1, (hr0 i j).2, add_zero, and_self])
      (by rw [← two_nsmul]; exact hf₀.1 r hrl)
    have hbb : heisO ψ S T (b + b) f = f := hB _ (isHalf_add hbe hbe) (add_mem hbl hbl)
    have haa : heisO ψ S T (a + a) f = f := hA _ (isHalf_add hae hae) (add_mem ham ham)
    have key := GlobalTheory.SplitScalar.heisO_heisO ψ S T (a + a) (b + b + (r + r)) f
    rw [hph, one_smul, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T hbr, hrr, hbb, haa] at key
    rw [h2, ← key]

  have sng : ∀ e' : AE D, IsSplitIdem D e' → ∀ a b r : WO S T, IsHalf e a → a ∈ hatMx (𝔪 • homLat ΛS ΛT) →
      IsHalf (cA D e) b → b ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) →
      r ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) →
      IsHalf e' a → IsHalf e' b → IsHalf e' r → heisO ψ S T (a + (b + r)) f = f := by
    intro e' he' a b r hae ham hbe hbl hrl hr0 ha' hb' hr'
    have horth : ∀ x y : WO S T, IsHalf e' x → IsHalf e' y → symplO S T x y = 0 := fun x y hx hy =>
      GlobalTheory.Hk3.symplO_half_off S T hx fun i j => by
        rw [← hy i j, ← mul_assoc, mul_comm (cA D e'), he'.2.1, zero_mul]
    rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth _ _ ha' (isHalf_add hb' hr')),
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth _ _ hb' hr'), hC r hr0 (hf₀.2 e' he' r hrl hr'),
      hB b hbe hbl, hA a hae ham]
  refine ⟨fun u hu => ?_, fun e' he' u hu hu' => ?_⟩
  · obtain ⟨hu1, hu2⟩ := hΓ u hu
    have ha := GlobalTheory.PlaceModelSum.idem_smul_latO e1 hu1
    have hb := GlobalTheory.PlaceModelSum.idem_smul_latO c1 hu1
    rw [hdec u]
    exact dbl _ _ _ (isHalf_idem e1 u) hu2 ha (isHalf_idem c1 u) hb (sub_mem (sub_mem hu1 ha) hb) (hoff u)
  · obtain ⟨hu1, hu2⟩ := hΓ u hu
    have ha := GlobalTheory.PlaceModelSum.idem_smul_latO e1 hu1
    have hb := GlobalTheory.PlaceModelSum.idem_smul_latO c1 hu1
    have hae : IsHalf e' (e • u) := isHalf_smul hu' e
    have hbe : IsHalf e' (cA D e • u) := isHalf_smul hu' _
    rw [hdec u]
    exact sng e' he' _ _ _ (isHalf_idem e1 u) hu2 (isHalf_idem c1 u) hb (sub_mem (sub_mem hu1 ha) hb) (hoff u)
      hae hbe (isHalf_sub (isHalf_sub hu' hae) hbe)

end GlobalTheory.CosDep

namespace GlobalTheory.CosDep

theorem cosInd_ne_zero {D : D7} {m n : ℕ} {e : AE D} (he : e * e = e) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos Λ Λ' 𝔪) : cosInd e κ ≠ 0 := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  intro h0
  have hmem : e • (x₀.1 : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ cosSet e (Submodule.Quotient.mk x₀ : Cos Λ Λ' 𝔪) :=
    ⟨fun i j => by simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he], x₀, rfl, by rw [sub_self]; exact zero_mem _⟩
  have := congrFun h0 (e • (x₀.1 : Matrix (Fin m) (Fin n) D.host.E).map (incA D))
  unfold cosInd at this
  rw [Set.indicator_of_mem hmem] at this
  exact one_ne_zero this

end GlobalTheory.CosDep

theorem GlobalTheory.CosDep.cosVec_dep : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ Dep W (.chi i 0) (W.cosVec i κ) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ) := by
  intro D hoff T L μ₀ hL sc G W M _ i hi κ
  obtain ⟨e, he, hcos⟩ := W.cosVec_is
  have h := hcos i hi κ
  obtain ⟨hS, hT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hv := (W.vac_is i hi).2
  have e1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd hS hT (G.pl.modul_ne_bot sc) e1 hinf κ
  refine ⟨?_, ⟨GlobalTheory.RowTheta.isThetaFunO_cosVec W i hi κ, ?_⟩, fun τ => ?_⟩
  · obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
    rw [hall Tm hTm]
    have hne : W.vac i ≠ 0 := by
      rintro h0
      obtain ⟨⟨p, hp⟩, hall'⟩ := hv.norm
      have := hall' p hp
      rw [h0] at this
      simp [nrm2] at this
    exact GlobalTheory.PlaceModelInj.placeModel_ne_zero D W.ψ _ _ _ _ e _ _ Tm W.ψ_std hS hT e1 he.2 hinf hTm hne hSB
      (GlobalTheory.CosDep.cosInd_ne_zero e1 κ)
  · exact GlobalTheory.CosDep.isLatVac_of_cos W.ψ_std hS hT he (G.pl.modul_ne_bot sc) κ
      (fun t ht => _root_.GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet hS he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hoff hL G) κ ht) hv.lat h fun u hu => ⟨hu.1, hu.2 e he⟩
  · exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is hinf
      (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj.infPart_eq h hv.theta
      (GlobalTheory.RowTheta.isThetaFunO_cosVec W i hi κ) (hv.fock τ)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyStagesParamSizeConditions
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.LedSize


set_option maxHeartbeats 1000000 in
theorem evG_exists_sizeRows : EvG fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) → ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max (max x0 x1) (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), ?_⟩
  rintro K rfl rfl rfl hs hx hG X hO heta hA
  have hx' := (le_max_left _ _).trans hx
  have hxL := (le_max_right _ _).trans hx
  have hP := K.ok
  have hOk := hG.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (GlobalTheory.EX.Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx') hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GlobalTheory.EX.OB.GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx') e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  refine ⟨L, e1, ?_⟩
  have hq : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < L.sc.X' := by
    have hmem := hOk.small.1
    rcases hOk.lev _ hmem with ⟨i, hi⟩ | hlt
    · exact absurd hi (hOk.small.2.2.2.1 i)
    · rw [e1]; exact hlt
  have xe : L.sc.x = K.s.x := by rw [e1]
  have ee : L.sc.eps = eps := by rw [e1]; exact hs
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of M.params M.parT (M.CnW_eq.trans hC.1.2.2.2.2.2.2.2.1) M.sizes
    M.win.1.1 M.win.2.1.1 M.win.2.1.2 M.win.2.2.1 M.g_le hq M.ccK_top ?_ (by rw [xe]; exact le_of_max_le_left hxL)
  rw [xe, ee]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) (le_of_max_le_right hxL) (by positivity)

end GlobalTheory.Mem.R3.LedSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealComponentFrameHomUnitaryDiag
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem conj_mem_UJ {n : ℕ} (ε : Fin n → Bool) (G fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr)
    (hJ : frᴴ * Formalism.REAL.Jm ε * fr = G) (hg : g ∈ Formalism.QuantumDeterminants.UH G) : Formalism.REAL.inUJ ε (fr * g * fr⁻¹) := by
  change gᴴ * G * g = G at hg
  unfold Formalism.REAL.inUJ
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hd
  have h2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc (fr * g * fr⁻¹)ᴴ * Formalism.REAL.Jm ε * (fr * g * fr⁻¹)
      = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g) * fr⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (fr⁻¹)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * fr⁻¹ := by rw [hJ, hg]
    _ = ((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem cmp_frame_hom : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ), ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ := by
  intro D θ hθ V S M τ
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hfi : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  have hif : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have cmul : ∀ g h : GA D V, M.fr τ * cmp θ τ (g * h) * (M.fr τ)⁻¹ =
      (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) * (M.fr τ * cmp θ τ h * (M.fr τ)⁻¹) := by
    intro g h
    have e : cmp θ τ (g * h) = cmp θ τ g * cmp θ τ h := map_mul (GlobalTheory.RowReal.infMatHom V (θ τ)) g h
    rw [e]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), hfi, Matrix.one_mul]
  have cone : M.fr τ * cmp θ τ (1 : GA D V) * (M.fr τ)⁻¹ = 1 := by
    have e : cmp θ τ (1 : GA D V) = 1 := map_one (GlobalTheory.RowReal.infMatHom V (θ τ))
    rw [e, Matrix.mul_one, hif]
  let u : GA D V → (Matrix (Fin V.rank) (Fin V.rank) ℂ)ˣ := fun g =>
    ⟨M.fr τ * cmp θ τ g * (M.fr τ)⁻¹, M.fr τ * cmp θ τ g⁻¹ * (M.fr τ)⁻¹,
      by rw [← cmul, mul_inv_cancel, cone], by rw [← cmul, inv_mul_cancel, cone]⟩
  have mem : ∀ g, u g ∈ Formalism.REAL.UJ (M.ε τ) := fun g =>
    conj_mem_UJ (M.ε τ) _ _ _ (M.fr_unit τ) (M.fr_gram τ)
      (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)
  refine ⟨{ toFun := fun g => ⟨u g, mem g⟩, map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · apply Subtype.ext; apply Units.ext; exact cone
  · intro g h; apply Subtype.ext; apply Units.ext; exact cmul g h

end GlobalTheory.FibreAtTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionColumnStepRenameConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Kronecker

namespace GlobalTheory.RowReal

theorem sum_conjSub_cast {ι : Type} {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (U : Matrix (Fin a') (Fin a') ℂ)
    (V : Matrix (Fin b') (Fin b') ℂ) (hV : star V * V = 1) (τ : ι) (p : Fin a) (q : Fin b) :
    ∑ x : Fin a, ∑ y : Fin b, MvPolynomial.C ((starRingEnd ℂ) (U.submatrix (Fin.cast ha) (Fin.cast ha) x p) *
        (starRingEnd ℂ) ((V.submatrix (Fin.cast hb) (Fin.cast hb))⁻¹ q y)) *
        (MvPolynomial.X (τ, Fin.cast hb y, Fin.cast ha x) : MvPolynomial (ι × Fin b' × Fin a') ℂ) =
      ∑ x : Fin b', ∑ y : Fin a', MvPolynomial.C ((V ⊗ₖ (star U)ᵀ) (x, y) (Fin.cast hb q, Fin.cast ha p)) *
        MvPolynomial.X (τ, x, y) := by
  subst ha hb
  have e : ∀ {n : ℕ} (h : n = n) (M : Matrix (Fin n) (Fin n) ℂ), M.submatrix (Fin.cast h) (Fin.cast h) = M := fun _ _ => by
    ext; simp
  simp only [e, Fin.cast_eq_self]
  rw [Matrix.inv_eq_left_inv hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 2
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.star_apply, RCLike.star_def, RingHomCompTriple.comp_apply,
    RingHom.id_apply, Complex.conj_conj]
  ring

theorem trRow_fockSubAll : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC i)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC (i + 1)))
    (Q : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank),
    GlobalTheory.RowReal.trRow G i (GlobalTheory.RowReal.fockSubAll (fun _ => 0) (fun _ => (G.V (.grid i D.R.m)).rank)
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2)))
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trRow G i Q) := by
  intro D T L sc G i u v Q
  have hL : ∀ P, linSub (homMat _ _ (u, v)) P = MvPolynomial.aeval (R := ℂ) (fun p : D.what₂.Tau × (Fin ((rowSizes D).nC (i + 1)) × Fin ((rowSizes D).nC i)) => ∑ j, MvPolynomial.C ((homMat _ _ (u, v)) p.1 j p.2) * (MvPolynomial.X (p.1, j) : MvPolynomial _ ℂ)) P := fun _ => rfl
  rw [hL, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, p, q⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, fockSubAll, trRow, MvPolynomial.aeval_X, MvPolynomial.rename_X, map_sum, map_mul, MvPolynomial.rename_C, Fintype.sum_prod_type]
  have hc : ¬ ((p : ℕ) < (G.V (.grid i D.R.m)).rank ↔ (q : ℕ) < 0) := by simp [p.2]
  simp only [if_neg hc]
  have hH : ∀ τ', homMat _ _ (u, v) τ' = ((v τ' : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) ⊗ₖ (star ((u τ' : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ))ᵀ := fun _ => rfl
  simp only [hH]
  exact sum_conjSub_cast _ _ _ _ (v τ).2.1 τ p q

end GlobalTheory.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionRowStepRenameUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem fockSubAll_rename_unitary {D : D7} {m n a b : ℕ} (ha : n = a) (hb : m = b)
    (u : UG D.what₂.Tau a) (v : UG D.what₂.Tau b) (Q : MvPolynomial (FVar D m n) ℂ) :
    MvPolynomial.rename (fun x : FVar D m n => (x.1, Fin.cast hb x.2.1, Fin.cast ha x.2.2))
      (fockSubAll (fun _ => n) (fun _ => m)
        (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast ha) (Fin.cast ha))
        (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast hb) (Fin.cast hb)) Q) =
      linSub (homMat a b (u, v))
        (MvPolynomial.rename (fun x : FVar D m n => (x.1, Fin.cast hb x.2.1, Fin.cast ha x.2.2)) Q) := by
  subst ha hb
  have hinv : ∀ τ, ((u τ : Matrix (Fin n) (Fin n) ℂ))⁻¹ = star (u τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 (u τ).2)
  have hc : ∀ k : ℕ, (Fin.cast (rfl : k = k)) = id := fun k => by funext i; rfl
  rw [hc, hc]
  have hid : (fun x : FVar D m n => (x.1, (id x.2.1 : Fin m), (id x.2.2 : Fin n))) = id := rfl
  rw [hid, MvPolynomial.rename_id, AlgHom.id_apply, AlgHom.id_apply]
  have hs : ∀ k (M : Matrix (Fin k) (Fin k) ℂ), M.submatrix id id = M := fun _ _ => rfl
  simp only [hs]
  show _ = (MvPolynomial.aeval (R := ℂ) fun p : D.what₂.Tau × (Fin m × Fin n) => ∑ j, MvPolynomial.C ((homMat n m (u, v)) p.1 j p.2) *
    (MvPolynomial.X (p.1, j) : MvPolynomial (D.what₂.Tau × (Fin m × Fin n)) ℂ)) Q
  refine DFunLike.congr_fun ?_ Q
  refine MvPolynomial.algHom_ext fun y => ?_
  obtain ⟨τ, p, q⟩ := y
  simp only [fockSubAll, MvPolynomial.aeval_X, hinv, homMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Fin.is_lt, iff_self, if_true, Matrix.transpose_apply, Matrix.star_apply]

theorem trCol_fockSubAll_unitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR j)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR (j + 1)))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank),
    GlobalTheory.RowReal.trCol G j (GlobalTheory.RowReal.fockSubAll (fun _ => (G.V (.top j)).rank) (fun _ => (G.V (.top (j + 1))).rank)
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le)))
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trCol G j Q) := by
  intro D T L sc G j u v Q
  exact fockSubAll_rename_unitary _ _ u v Q

end GlobalTheory.RowReal
end

