module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalRingCardinality.SpanPowerMembership
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0004
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0007
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0003
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevD
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
public import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0001
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0003
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.HypOver
section
noncomputable section

namespace GlobalTheory.Core.RkFamModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ GlobalTheory.Core.Rk NumberField Module

theorem xu_pos (D : D7) (u : D.what₂.Word) : 0 < (D.mem u).A.Xu := by
  have h1 := (D.mem u).A.Dstar_pos
  have h2 : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  unfold ColumnsAtT.Xu
  positivity

theorem fk_pos (R : Ranks) : (0 : ℝ) < (R.f : ℝ) * R.k := by
  have := R.m_add_three_le_k
  have h1 : 0 < R.k := by omega
  have h2 : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
  positivity

theorem log_tstar (D : D7) (u : D.what₂.Word) : Real.log (D.mem u).A.Tstar =
    Real.log (D.mem u).A.Xu - 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  unfold ColumnsAtT.Tstar
  rw [Real.log_mul (xu_pos D u).ne' (Real.rpow_pos_of_pos hG _).ne', Real.log_rpow hG]
  ring

theorem log_T_lt (D : D7) (u : D.what₂.Word) :
    Real.log ((D.mem u).A.T : ℝ) < Real.log (D.mem u).A.Xu + 1 / ((D.R.f : ℝ) * D.R.k) := by
  have hT : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hf := fk_pos D.R
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hs : 0 < (D.mem u).A.Tstar := mul_pos (xu_pos D u) (Real.rpow_pos_of_pos hG _)
  have h1 := Real.log_le_log hT (D.T_win u).2
  rw [Real.log_mul (by positivity) hs.ne', log_tstar] at h1
  have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((D.R.f : ℝ) * D.R.k))
  have h3 : 0 < 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP :=
    mul_pos (by positivity) (Real.log_pos (D.mem u).A.one_lt_gammaP)
  linarith


section Rank

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (N : ℕ)

variable (T : ℕ) [Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (hT : T ≠ 2) (s : ℂ)


end Rank

end GlobalTheory.Core.RkFamModel

namespace GlobalTheory.Core.RkOverModel

open Formalism.BasicNotions GlobalTheory.Core.Rk

end GlobalTheory.Core.RkOverModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.Model

open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp

variable {D : D7}

local instance relAt (v : Pl D) : ValuativeRel (Fv D.host.F v) := GlobalTheory.LocalData.complRel v
local instance locAt (v : Pl D) : IsNonarchimedeanLocalField (Fv D.host.F v) := GlobalTheory.LocalData.isLocalField v

def secAt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.mk' (fun a => singleTens D.host.E v (a ⊗ₜ[D.host.F] (1 : D.host.E)) * splitIdemAd (isCMExt_host D) τ)
    fun a b => by rw [TensorProduct.add_tmul, map_add (f := _), add_mul]

def prAt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D →+* Fv D.host.F v :=
  (splitProj τ).toRingHom.comp (GlobalTheory.AdelicU.compFin D.host.F D.host.E v)

theorem mem_int_iff {v : Pl D} (a : Fv D.host.F v) : a ∈ 𝒪[Fv D.host.F v] ↔ Valued.v a ≤ 1 := by
  have : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff,
    (isEquiv (valuation (Fv D.host.F v)) (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one]

def splitPt {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : SplitPt D (Fv D.host.F v) where
  v := v
  e := splitIdemAd (isCMExt_host D) τ
  split := isSplitIdem_iff_exists.2 ⟨v, τ, rfl⟩
  above := ⟨_, isPlaceIdem_placeIdem D v, (splitAt_splitIdemAd τ).2.2⟩
  pr := prAt τ
  sec := secAt τ
  pr_sec a := by
    change splitProj τ (GlobalTheory.AdelicU.compFin _ _ v (singleTens _ v _ * singleTens _ v _)) = a
    rw [map_mul, compFin_singleTens_self, compFin_singleTens_self, map_mul, splitProj_tmul, splitProj_splitIdem, map_one,
      mul_one, mul_one]
  sec_pr x := (splitIdemAd_mul (isCMExt_host D) τ x).symm
  cont_pr := (continuous_splitProj τ).comp
    (GlobalTheory.AutFunCompare.continuous_tensNU (E := D.host.E) (evFin D.host.F v).toLinearMap (map_mul (evFin D.host.F v)) (by
      exact (RestrictedProduct.continuous_eval v).comp continuous_snd))
  cont_sec := by
    have h1 : Continuous fun a : AF D.host.F => (a ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) :=
      (continuous_id.smul (continuous_const (y := (1 : AE D)))).congr fun a => by
        change a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (h1.comp (Continuous.prodMk continuous_const (continuous_singleFin v))).mul continuous_const
  int_iff a := (mem_int_iff a).trans (GlobalTheory.IdemPrime.mem_iff (splitAt_splitIdemAd τ) a).symm

theorem eq_single {v : Pl D} {a : AE D} (ha : a ∈ idAt D (· = v)) : a = singleTens D.host.E v (compAt D v a) := by
  have hc : ∀ u (z : AE D), GlobalTheory.AdelicU.compFin D.host.F D.host.E u z = compAt D u z := fun u z =>
    (tens_map_map (sndA D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) z).symm
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine adTens_ext (fun w => ?_) fun u => ?_
  · rw [compInf_singleTens]
    refine (tens_map_map (fstA D.host.F) (GlobalTheory.AutFunCompare.evW w) a).symm.trans ?_
    exact (congrArg (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)) h1).trans (map_zero _)
  · by_cases e : u = v
    · subst e; rw [compFin_singleTens_self, hc]
    · rw [compFin_singleTens_ne e, hc]
      exact (Submodule.mem_iInf _).1 h2 ⟨u, e⟩

theorem compAt_eq (u : Pl D) (z : AE D) : compAt D u z = GlobalTheory.AdelicU.compFin D.host.F D.host.E u z :=
  tens_map_map (sndA D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) z

theorem single_mem_idAt (v : Pl D) (y : Fv D.host.F v ⊗[D.host.F] D.host.E) : singleTens D.host.E v y ∈ idAt D (· = v) := by
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun u => ?_⟩
  · induction y using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul a x => exact TensorProduct.zero_tmul _ x
  · exact (compAt_eq u.1 _).trans (compFin_singleTens_ne u.2 y)

theorem mem_idAt_iff {v : Pl D} {a : AE D} :
    a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) (placeIdem v) * a = a := by
  rw [← singleTens_one, singleTens_mul, one_mul, ← compAt_eq]
  exact ⟨fun h => (eq_single h).symm, fun h => h ▸ single_mem_idAt v _⟩

theorem mem_grpAt_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (g : GA D S) : g ∈ grpAt S (· = p.v) ↔ SuppAt p.e S g := by
  obtain ⟨ε, h1, h2⟩ := p.above
  obtain rfl := isPlaceIdem_iff.1 h1
  rw [SuppAt, h2]
  simp only [← mem_idAt_iff]
  rw [grpAt, congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  have : Ideal.Quotient.mk (idAt D (· = p.v)) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idAt D (· = p.v))) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this]
  exact Iff.rfl

def intGrp (D : D7) (v : Pl D) : AddSubgroup (AE D) :=
  (idAt D (· = v)).toAddSubgroup ⊓ (intAE D).comap (finPart D).toAddMonoidHom

theorem latV_le_int (S : HSp D) (L : Lat S) (hL : ∀ x ∈ L, ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i) (v : Pl D) :
    latV S L (· = v) ≤ AddSubgroup.pi Set.univ fun _ => intGrp D v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, h0, a, rfl, x, hx, rfl⟩ i -
  obtain ⟨b, hb⟩ := hL x hx i
  refine ⟨Submodule.mem_inf.2 ⟨TensorProduct.zero_tmul _ _, (Submodule.mem_iInf _).2 fun u => ?_⟩,
    AddSubgroup.subset_closure ⟨α, hα, b, by rw [hb, ← one_mul (x i)]; rfl⟩⟩
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u.1 α ⊗ₜ[D.host.F] _ = 0
  rw [h0 _ u.2, TensorProduct.zero_tmul]

theorem single_mem_latV (S : HSp D) (L : Lat S) (v : Pl D) (i : Fin S.rank)
    (hL : ∀ b : 𝓞 D.host.E, Pi.single i (b : D.host.E) ∈ L) :
    intAE D ≤ (latV S L (· = v)).comap ((AddMonoidHom.single (fun _ : Fin S.rank => AE D) i).comp
      ((singleTens D.host.E v).toAddMonoidHom.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v).toAddMonoidHom)) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, b, rfl⟩
  refine AddSubgroup.subset_closure ⟨singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v α), fun u => ?_,
    fun u hu => evalV_singleFin_ne hu _, 1, rfl, Pi.single i (b : D.host.E), hL b, funext fun j => ?_⟩
  · by_cases e : u = v
    · subst e; rw [evalV_singleFin_self]; exact hα u
    · rw [evalV_singleFin_ne e]; exact zero_mem _
  · change (Pi.single i (pairA D.host.F 0 (singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v α)) ⊗ₜ[D.host.F] (b : D.host.E)) :
      Fin S.rank → AE D) j = _
    by_cases e : j = i
    · subst e; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne e, mul_zero, TensorProduct.tmul_zero]

theorem mem_latV_std (S : HSp D) (L : Lat S) (hL : ∀ x, x ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i) (v : Pl D)
    (y : Fin S.rank → AE D) : y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intAt D (· = v) := by
  refine ⟨fun hy i => latV_le_int S L (fun x => (hL x).1) v hy i trivial, fun hy => ?_⟩
  rw [← Finset.univ_sum_single y]
  refine sum_mem fun i _ => ?_
  rw [eq_single (hy i).1]
  refine single_mem_latV S L v i (fun b => (hL _).2 fun j => ?_) (hy i).2
  by_cases e : j = i
  · subst e; exact ⟨b, by rw [Pi.single_eq_same]⟩
  · exact ⟨0, by rw [Pi.single_eq_of_ne e]; rfl⟩

end GlobalTheory.FinPl.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

structure PairDat (p : ι → SplitPt D k) (A S : HSp D) (n : Type) [Fintype n] [DecidableEq n] where
  α : ∀ i, Frame (p i) A n
  α₀ : ∀ i, Frame (p i) S (n ⊕ Fin 1)
  P : ι → Pair k n

structure MidDat (p : ι → SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] where
  β : ∀ i, Frame (p i) S n
  Q : ι → Pair k n

variable {p : ι → SplitPt D k} {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n'']
  [DecidableEq n'']

def PairDat.Ram {A S : HSp D} (a : PairDat p A S n) (φ : GA D A → ℂ) : Prop := IsContAut A φ ∧ ∀ i, RamAt (a.α i) (a.P i) φ

def PairDat.sAll {A S : HSp D} (a : PairDat p A S n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (ε : ι → 𝓀[k]ˣ) (l : List ι)
    (φ : GA D A → ℂ) : GA D A → ℂ :=
  l.foldr (fun i ψ => sOp (a.α i) (a.P i) q (χ i) (ε i) ψ) φ

def OverAll (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S)
    (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (l : List ι) (f f' : WO S T → ℂ) : Prop :=
  l.foldr (fun i (r : (WO S T → ℂ) → Prop) f₂ => ∃ g, r g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f₂) (fun f₂ => f₂ = f) f'

structure DblLat {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) where
  L₀ : Lat B.V
  M₀ : Lat B.V₀
  L₁ : Lat J.W
  M₁ : Lat J.W₀
  L₂ : Lat B'.V
  M₂ : Lat B'.V₀

structure DblShape {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (Λ : DblLat B J B') (P : Pl D → Prop) (q : Unif k) (a : PairDat p B.A B.V₀ n')
    (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n'') : Prop where
  inj : Function.Injective fun i => (p i).v
  mem : ∀ i, P (p i).v
  good : ∀ v, P v → GoodBF ψ B J Λ.L₀ Λ.M₀ Λ.L₁ Λ.M₁ v
  adapt : ∀ v, P v → AdaptFB ψ J B' Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ v
  unr : ∀ v, P v → UnrAt s₁ v ∧ UnrAt s₂ v
  split : ∀ v, P v → (∀ i, v ≠ (p i).v) → SplitCore B' Λ.M₂ v
  gl : ∀ i, GluedCore B Λ.M₀ q (a.α i) (a.α₀ i) (a.P i)
  gl' : ∀ i, GluedCore B' Λ.M₂ q (a'.α i) (a'.α₀ i) (a'.P i)
  mid : ∀ i, (b.β i).IsLat Λ.M₁ (b.Q i).lat

def ShiftLaw (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (x : Mx D W.rank ρ)
    (P : Pl D → Prop) (𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ V W f → ∀ N : Mx D ρ ρ, MxAt P N → (∀ i j, j ≤ i → N i j = 0) →
    𝔉 (heisO ψ V W (dV.extX W (x ⬝ N)) f) = psiE ψ (upSum N) • 𝔉 f

def FlatShift (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J), ShiftLaw ψ B.d (xZero J.d) P (flatBF s)) ∧
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B),
      ShiftLaw ψ J.d (xLast B.d (vecB B.o B.ζ)) P (flatFB s)

def SupportShift (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W)
    (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v →
    ∀ 𝔉, IsFlatFB s (· = v) 𝔉 → ShiftLaw ψ J.d (xLast B.d (vecB B.o B.ζ)) (· = v) 𝔉 → ∀ f, Vac ψ J.W B.V LV LW (· = v) f →
      Vac ψ J.W₀ B.V₀ LV₀ LW₀ (· = v) (𝔉 f) ∧
      ∀ h ∈ grpAt B.V (· = v), 𝔉 (s.om (1, h) f) ≠ 0 →
        ∃ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) ∧ ∃ γ ∈ grpAt B.V₀ (· = v), ∃ κ, InK B.V LW (· = v) κ ∧
          h = n * B.d.emb0 γ * κ ∧ ∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ LW₀ (· = v) →
            mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ LW₀ (· = v)

def InBig (S : HSp D) (R : Subgroup (GA D S)) (L : Lat S) (P : Pl D → Prop) (h : GA D S) : Prop :=
  ∃ r ∈ R, r ∈ grpAt S P ∧ ∃ g ∈ grpOff S P, ∃ κ, InK S L P κ ∧ h = r * g * κ

def SuppFirst (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V)
    (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (P : Pl D → Prop), (∀ v, P v → GoodBF ψ B J LV LV₀ LW LW₀ v) →
    (∀ v, P v → UnrAt s v) → IsSelfDualC J.W LW → ∀ Φ, Vac ψ B.V J.W LV LW P Φ →
      (∀ κ κ', InK B.V LV P κ → InK J.W LW P κ' → s.om (κ, κ') Φ = Φ) ∧
      ∀ g ∈ grpOff B.V P, (∀ h, flatBF s (s.om (g, h) Φ) ≠ 0 → InBig J.W (jacGrp J.d) LW P h) ∧
        ∀ h ∈ grpOff J.W P, Vac ψ B.V₀ J.W₀ LV₀ LW₀ P (flatBF s (s.om (g, h) Φ))

def SuppSecond (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n'']
    [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1))
    (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Λ : DblLat B J B') (P : Pl D → Prop) (a : PairDat p B.A B.V₀ n') (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n''),
    DblShape s₁ s₂ Λ P q a b a' → IsSelfDualC B'.V Λ.L₂ → ∀ Φ₁ Φ₂, Vac ψ B.V J.W Λ.L₀ Λ.L₁ P Φ₁ → Vac ψ J.W B'.V Λ.L₁ Λ.L₂ P Φ₂ →
      (∀ κ κ', InK J.W Λ.L₁ P κ → InK B'.V Λ.L₂ P κ' → s₂.om (κ, κ') Φ₂ = Φ₂) ∧
      ∀ h₁ ∈ grpOff J.W P, (∀ h₂ ∈ grpOff B'.V P, Vac ψ J.W₀ B'.V₀ Λ.M₁ Λ.M₂ P (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))) ∧
        ∀ g ∈ grpOff B.V P, ∀ φ, a.Ram φ → ∀ h₂, Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ ≠ 0 →
          InBig B'.V (besGrp B'.d B'.o) Λ.L₂ P h₂

def AllBijective (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : ι → 𝓀[k]ˣ)
    (n : Type) [Fintype n] [DecidableEq n] (A S : HSp D) (a : PairDat p A S n), Function.Injective (fun i => (p i).v) →
    ∀ I : List ι, Set.BijOn (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} {φ | a.Ram φ} ∧
      ∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 ∨ c' g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ φ, a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ = c.sum fun g x => x • rTrans g φ) ∧
        ∀ φ, a.Ram φ → a.Ram (c'.sum fun g x => x • rTrans g φ) ∧
          a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (c'.sum fun g x => x • rTrans g φ) = φ

theorem SplitPt.sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b := by
  have h : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  have h2 := p.sec_pr (p.sec a * p.sec b)
  rwa [map_mul, p.pr_sec, p.pr_sec, ← mul_assoc, h] at h2

theorem SplitPt.sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  rw [← map_one p.pr, p.sec_pr, mul_one]

def SplitPt.idele (p : SplitPt D k) : kˣ →* (AE D)ˣ :=
  Units.map
    { toFun := fun a => 1 + p.sec (a - 1)
      map_one' := by rw [sub_self, map_zero, add_zero]
      map_mul' := fun a b => by
        rw [show a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) by ring, map_add (f := _), map_add (f := _), p.sec_mul]
        ring }

theorem SplitPt.idele_val (p : SplitPt D k) (a : kˣ) : (p.idele a : AE D) = 1 - p.e + p.sec a := by
  change 1 + p.sec (a - 1) = _
  rw [map_sub, p.sec_one]
  ring

def IsGlueConst (p : ι → SplitPt D k) (q : Unif k) (I : List ι) (N : ℕ) {r : ℕ} (μ : Fin r → ((AE D)ˣ →* Circle)) (c : ℂ) : Prop :=
  ∃ (a : ℤ) (m : Fin r → ℤ), c = (I.map fun i => ((resCard k : ℂ) ^ N - 1) * ((√(resCard k : ℝ) : ℝ) : ℂ) ^ a *
    ∏ j, ((μ j ((p i).idele (Units.mk0 _ q.ne_zero)) ^ m j : Circle) : ℂ)).prod


end GlobalTheory.FinPl

end
end

