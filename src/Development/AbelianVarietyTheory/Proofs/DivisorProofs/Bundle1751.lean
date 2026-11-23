module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSDa
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevel
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

namespace GlobalTheory.LevelTr
theorem exists_nat_mul_eq {E : Type} [Field E] [NumberField E] (w : 𝓞 E) (hw : w ≠ 0) :
    ∃ c : ℕ, 0 < c ∧ ∃ q : 𝓞 E, (c : 𝓞 E) = w * q := by
  refine ⟨Ideal.absNorm (Ideal.span {w}), Nat.pos_of_ne_zero fun h => hw ?_, ?_⟩
  · rwa [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
  · obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {w}))
    exact ⟨q, by rw [← hq, mul_comm]⟩

theorem inc_mem_OhE {D : D7} {e : D.host.E} (he : IsIntegral ℤ e) : Formalism.MainNotions.StandardLatticesGL3.inc D e ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D :=
  Formalism.UG.CS.incl_int (F := ℚ) (⟨e, he⟩ : 𝓞 D.host.E)

theorem exists_nat_IhE (D : D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) :
    ∃ c : ℕ, 0 < c ∧ ∀ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc,
      Formalism.MainNotions.StandardLatticesGL3.inc D ((c : D.host.E) * r⁻¹) * t ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 D.host.E)) r⁻¹
  obtain ⟨a0, ha0, hint⟩ := D.host.AA0.isFractional
  have hw : (s : 𝓞 D.host.E) * a0 ≠ 0 :=
    mul_ne_zero (nonZeroDivisors.ne_zero s.2) (nonZeroDivisors.ne_zero ha0)
  obtain ⟨c, hc, q, hq⟩ := exists_nat_mul_eq _ hw
  refine ⟨c, hc, fun t ht => ?_⟩
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, a, ha, s', hs', rfl⟩ := hy
    obtain ⟨b, hb⟩ := hint a ha
    have hcE : (c : D.host.E) = ((s : 𝓞 D.host.E) : D.host.E) * (a0 : D.host.E) * (q : D.host.E) := by
      have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hq
      simpa using this
    have e1 : (c : D.host.E) * r⁻¹ * (((k : D.host.K) : D.host.E) * a) =
        (q : D.host.E) * (x : D.host.E) * ((k : D.host.K) : D.host.E) * (b : D.host.E) := by
      have h1 : r⁻¹ * ((s : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := hxs
      have h2 : (b : D.host.E) = (a0 : D.host.E) * a := by
        have := hb; rw [Algebra.smul_def] at this; exact this
      rw [hcE, h2, ← h1]; ring
    have hk' : IsIntegral ℤ ((k : D.host.K) : D.host.E) := by
      first
        | exact (NumberField.RingOfIntegers.isIntegral_coe k).algebraMap
        | exact IsIntegral.algebraMap k.2
        | exact (NumberField.RingOfIntegers.isIntegral_coe k).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
    rw [← mul_assoc, ← map_mul, e1]
    refine mul_mem (inc_mem_OhE ?_) hs'
    exact ((q.2.mul x.2).mul hk').mul b.2
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha
end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem finQ_mt_of_isFinPt {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V} {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank}
    (hg : IsFinPt V g x) :
    (mt V g).map (finQ D) =
      ((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank =>
    ((k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j)
    (finStd_of_isFinPt V hG hg)
  rw [finStd_apply] at this
  exact this

theorem finQ_mt_inv_of_isFinPt {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V} {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank}
    (hg : IsFinPt V g x) :
    (mt V g⁻¹).map (finQ D) =
      (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  have h2 : finStd V hG g⁻¹ = x⁻¹ := by rw [map_inv, finStd_of_isFinPt V hG hg]
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank =>
    ((k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) h2
  rw [finStd_apply] at this
  exact this

theorem finQ_finRat {D : D7} (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    finQ D (GlobalTheory.VacUnique.finRat S T γ i j) = Formalism.MainNotions.StandardLatticesGL3.inc D (γ i j) := by
  rw [← finQ_inclR]
  rfl

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem finQ_finPt {D : D7} (S T : HSp D) (r : D.host.E) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) =
      -(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ • z.map (Formalism.MainNotions.StandardLatticesGL3.inc D)) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, finPt, finQ_finRat]
  simp [Matrix.of_apply, map_neg, map_mul]

theorem finQ_actO_sub {D : D7} (S T : HSp D) (hGS : S.gram = 1) (hGT : T.gram = 1) (r : D.host.E)
    (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T)
    (hg : IsFinPt S g x) (hh : IsFinPt T h y) (z z' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z').map (finQ D) =
      Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ • (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D) -
        ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
          z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
            Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) := by
  have e1 : (actO S T g h (finPt rfl rfl r z)).map (finQ D) =
      (mt T h).map (finQ D) * (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) * (mt S g⁻¹).map (finQ D) := by
    rw [actO, Matrix.map_mul, Matrix.map_mul]
  rw [Matrix.map_sub _ (map_sub (finQ D)), e1, finQ_mt_of_isFinPt T hGT hh, finQ_mt_inv_of_isFinPt S hGS hg, finQ_finPt, finQ_finPt]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict
open scoped TensorProduct

theorem infPart_mt_of_mem_GfC {D : D7} (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) :
    (mt V g).map (infPart D) = 1 := by
  have := congrArg (fun k : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    k.val) (MonoidHom.mem_ker.1 hg)
  exact this

theorem infPart_actO_sub {D : D7} (S T : HSp D) (r : D.host.E) (g : GA D S) (h : GA D T) (hg : g ∈ GfC S)
    (hh : h ∈ GfC T) (z z' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z').map (infPart D) = 0 := by
  have h0 : ∀ w : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (finPt (S := S) (T := T) rfl rfl r w).map (infPart D) = 0 := fun w => GlobalTheory.VacUnique.finRat_inf S T _
  rw [Matrix.map_sub _ (map_sub (infPart D)), actO, Matrix.map_mul, Matrix.map_mul, h0, h0,
    infPart_mt_of_mem_GfC T hh, infPart_mt_of_mem_GfC S (inv_mem hg)]
  simp

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem ennreal_volume_ratio_step_cancel {R : Type} [CommRing R] (a b c k t : R) (h : a * k = 1) :
    a * (b * (c * k * t)) = c * b * t := by
  linear_combination (b * c * t) * h


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 160000 in
theorem level_translate : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    heisO ψ S T (actO S T g h (finPt hS hT r z) - finPt hS hT r z') F = F := by
  intro D ψ θ S T a d hS hT cc δ r hset x y g h hg hh F hF z
  subst hS
  subst hT
  obtain ⟨U, hUo, hU⟩ := hF.level
  have sdS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have sdT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨m, hm, hmU⟩ := Formalism.IndefR.Fin.exists_nsmul_mem_cpt' _
    (Formalism.IndefR.Fin.latO_isCompact S T _ _ sdS sdT) (fun w hw n => AddSubgroup.nsmul_mem _ hw n) U hUo
  obtain ⟨N, hN, hNΛ⟩ := Formalism.IndefR.Fin.latO_nsmul_mem S T _ _ sdS sdT
  obtain ⟨c, hc, hcI⟩ := exists_nat_IhE D cc r
  refine ⟨c * (m * N), by positivity, fun z' hz' => ?_⟩
  have hinf := infPart_actO_sub S T r g h hg.1 hh.1 z z'
  have hfin := finQ_actO_sub S T hset.gS hset.gT r x y g h hg hh z z'
  set u := actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z' with hu
  have hk0 : ((m * N : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  set Y : WO S T := incA D ((m * N : ℕ) : D.host.E)⁻¹ • u with hY
  have hYinf : ∀ i j, infPart D (Y i j) = 0 := by
    intro i j
    have h1 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
    rw [hY, Matrix.smul_apply, smul_eq_mul, map_mul, h1, mul_zero]
  have hYfin : ∀ i j, finPart D (Y i j) ∈ intAE D := by
    intro i j
    rw [GlobalTheory.IdemSupport.mem_intAE_iff]
    have e : finPart D (Y i j) = GlobalTheory.BotFormula.toAfE D (finQ D (Y i j)) := (toAfE_finQ _).symm
    rw [e]
    refine (toAfE_int_iff _).2 ?_
    have hu_ij : finQ D (u i j) = Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D) -
        ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
          z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
            Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j :=
      congrFun (congrFun hfin i) j
    obtain ⟨t, ht, et⟩ := hz' i j
    have hkk' : Formalism.MainNotions.StandardLatticesGL3.inc D ((m * N : ℕ) : D.host.E)⁻¹ * ((m * N : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 := by
      rw [← map_natCast (Formalism.MainNotions.StandardLatticesGL3.inc D), ← map_mul, inv_mul_cancel₀ hk0, map_one]
    have e2 : finQ D (Y i j) = Formalism.MainNotions.StandardLatticesGL3.inc D ((c : D.host.E) * r⁻¹) * t := by
      rw [hY, Matrix.smul_apply, smul_eq_mul, map_mul, finQ_inclR, hu_ij, et, map_mul, map_natCast]
      rw [Nat.cast_mul c (m * N)]
      exact ennreal_volume_ratio_step_cancel _ _ _ _ _ hkk'
    rw [e2]
    exact hcI t ht
  have h1 := hmU _ (hNΛ Y hYfin hYinf)
  have hkY : m • N • Y = u := by
    refine Matrix.ext fun i j => ?_
    show m • N • Y i j = u i j
    rw [← mul_nsmul', nsmul_eq_mul, hY, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    have hkk : ((m * N : ℕ) : AE D) * incA D ((m * N : ℕ) : D.host.E)⁻¹ = 1 := by
      rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ hk0, map_one]
    rw [hkk, one_mul]
  have hmem : u ∈ U := hkY ▸ h1
  exact hU u hmem hinf

end GlobalTheory.LevelTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
section
noncomputable section

namespace GlobalTheory.ThK.ConeEulerChr

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_liftV (a : ∀ v : Pl F, Fv F v) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    Tendsto (fun v => GlobalTheory.LatVac.liftV v (a v)) cofinite (𝓝 0) := by
  have hf : ∀ v w : Pl F, evalV F w (singleFin v (a v)) ∈ w.adicCompletionIntegers F := fun v w => by
    by_cases h : w = v
    · subst h; rw [evalV_singleFin_self]; exact ha w
    · rw [evalV_singleFin_ne h]; exact zero_mem _
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have ht : Tendsto (fun v : Pl F => fun w : HeightOneSpectrum (𝓞 F) =>
      (⟨evalV F w (singleFin v (a v)), hf v w⟩ : (w.adicCompletionIntegers F : Set (w.adicCompletion F)))) cofinite
      (𝓝 fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) := by
    refine tendsto_pi_nhds.2 fun w => tendsto_subtype_rng.2 ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cofinite_ne w] with v hv
    exact (evalV_singleFin_ne (Ne.symm hv) _).symm
  have h2 : Tendsto (fun v : Pl F => singleFin v (a v)) cofinite (𝓝 (0 : Af F)) := (hc.tendsto _).comp ht
  have hp : Continuous fun β : Af F => pairA F 0 β := continuous_const.prodMk continuous_id
  exact (hp.tendsto 0).comp h2

theorem exists_coords {v : Pl F} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v, (∀ i, a i ∈ v.adicCompletionIntegers F) ∧
      y = ∑ i, a i ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
  refine intLoc_induction (p := fun y => ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v,
    (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ y = ∑ i, a i ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E))
    (fun a ha x => ?_) ⟨0, fun _ => zero_mem _, by simp⟩ ?_ ?_ hy
  · refine ⟨fun i => (RingOfIntegers.basis E).repr x i • a, fun i => zsmul_mem ha _, ?_⟩
    have hx : (x : E) = ∑ i, (RingOfIntegers.basis E).repr x i • ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
      simp
    rw [hx, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul _ _ _).symm
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨a + c, fun i => add_mem (ha i) (hc i), by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, fun i => neg_mem (ha i), by simp [TensorProduct.neg_tmul]⟩

theorem tendsto_zero_of_intLoc (x : Pl F → AE F E)
    (h : ∀ᶠ v in cofinite, At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v) :
    Tendsto x cofinite (𝓝 0) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have key : ∀ v : Pl F, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v,
      (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ (At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v →
      x v = ∑ i, GlobalTheory.LatVac.liftV v (a i) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E))) := fun v => by
    by_cases hv : At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v
    · obtain ⟨a, ha, e⟩ := exists_coords hv.2
      obtain ⟨h1, h2⟩ := at_evFin_iff.1 hv.1
      refine ⟨a, ha, fun _ => GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [h1, map_sum]
          exact (Finset.sum_eq_zero fun i _ => by
            rw [compInf_smul, show evInf F w (GlobalTheory.LatVac.liftV v (a i)) = 0 from rfl, zero_smul]).symm
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [map_sum]
          by_cases hw : w = v
          · subst hw
            rw [e]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [compFin_smul, GlobalTheory.LatVac.evFin_liftV]
            change _ = a i • (evFin F w 1 ⊗ₜ[F] _)
            rw [map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rfl
          · rw [h2 w hw]
            exact (Finset.sum_eq_zero fun i _ => by
              rw [compFin_smul, show evFin F w (GlobalTheory.LatVac.liftV v (a i)) = 0 from evalV_singleFin_ne hw _,
                zero_smul]).symm
    · exact ⟨0, fun _ => zero_mem _, fun h => absurd h hv⟩
  choose a ha e using key
  have ht : Tendsto (fun v => ∑ i, GlobalTheory.LatVac.liftV v (a v i) •
      ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) : AE F E)) cofinite
      (𝓝 (∑ i, (0 : AF F) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) : AE F E))) :=
    tendsto_finsetSum _ fun i _ => (tendsto_liftV (fun v => a v i) fun v => ha v i).smul_const _
  simp only [zero_smul, Finset.sum_const_zero] at ht
  refine ht.congr' ?_
  filter_upwards [h] with v hv using (e v hv).symm

theorem tendsto_one_of_unitsAt (m : Pl F → (AE F E)ˣ) (h : ∀ᶠ v in cofinite, m v ∈ unitsAt E v) :
    Tendsto m cofinite (𝓝 1) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have key : ∀ m : Pl F → (AE F E)ˣ, (∀ᶠ v in cofinite, m v ∈ unitsAt E v) →
      Tendsto (fun v => (m v : AE F E)) cofinite (𝓝 1) := fun m h => by
    have := (tendsto_zero_of_intLoc (fun v => (m v : AE F E) - 1) (h.mono fun v hv => ⟨hv.1, by
      rw [map_sub, map_one]; exact sub_mem (mem_unitsAt.1 hv).2.1 (one_mem _)⟩)).add_const 1
    simpa using this
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (key m h).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
    (key (fun v => (m v)⁻¹) (h.mono fun v hv => inv_mem hv)))

theorem eventually_chr_eq_one {ν : Chr F E} (hν : Continuous ν) (m : Pl F → (AE F E)ˣ)
    (h : ∀ᶠ v in cofinite, m v ∈ unitsAt E v) : ∀ᶠ v in cofinite, ν (m v) = 1 := by
  have key : ∀ v, ∃ n : ℕ, ‖(ν (m v) : ℂ) ^ n - 1‖ < 1 → ν (m v) = 1 := fun v => by
    by_contra hc
    push Not at hc
    exact (hc 0).2 (GlobalTheory.CharDualMat.circle_eq_one_of_pow_near _ fun n => (hc n).1)
  choose n hn using key
  have ht := tendsto_one_of_unitsAt (fun v => m v ^ n v) (h.mono fun v hv => pow_mem hv _)
  have hc : Continuous fun x : (AE F E)ˣ => ‖(ν x : ℂ) - 1‖ :=
    ((continuous_subtype_val.comp hν).sub continuous_const).norm
  have h1 := ((hc.tendsto 1).comp ht).eventually (gt_mem_nhds (show ‖(ν 1 : ℂ) - 1‖ < 1 by simp))
  filter_upwards [h1] with v hv
  exact hn v (by simpa using hv)

theorem cutIdele_eq (S : Finset (Pl F)) (l : (AE F E)ˣ) :
    GlobalTheory.Doubling.cutIdele S l = unitArch F E l * ∏ v ∈ S, unitAt E v l := by
  have h1 : (eInf F).1 = 1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
    rw [map_one]; exact evI_realAd_one)
  have ha : GlobalTheory.Doubling.cutIdele ∅ l = unitArch F E l := by
    refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun v => ?_
    · rw [GlobalTheory.Doubling.unitInf_cutIdele]
      refine Units.ext ?_
      change compInf F E w l = compInf F E w (eInf F • (l : AE F E) + (1 - eInf F) • 1)
      have h : evInf F w (eInf F) = 1 := congrFun h1 w
      rw [map_add (f := _), compInf_smul, compInf_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]
    · rw [GlobalTheory.Doubling.unitFin_cutIdele_of_notMem _ (Finset.notMem_empty v)]
      have := at_evI_iff.1 (unitArch_mem l) v
      rw [map_sub, map_one, sub_eq_zero] at this
      exact Units.ext this.symm
  rw [← ha, GlobalTheory.Doubling.cutIdele, GlobalTheory.Doubling.cutIdele, Finset.prod_empty, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← ideleAt_unitFin (unitAt_mem v l)]
  exact congrArg _ (Units.ext (compFin_unitAt_self v l).symm)

theorem chr_abs_eq_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E), Continuous ν → ∀ (l : (AE F E)ˣ) (z : ℕ),
    (Function.mulSupport fun v : Pl F => (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite ∧
    (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z = (ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z *
      ∏ᶠ v : Pl F, (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z := by
  intro F E _ _ _ _ _ ν hν l z
  have hu := eventually_unitAt_mem_unitsAt F E l
  have hfin : (Function.mulSupport fun v : Pl F =>
      (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite := by
    refine (eventually_cofinite.1 (hu.and (eventually_chr_eq_one hν _ hu))).subset fun v hv h => hv ?_
    simp only [h.2, absE_of_mem_unitsAt h.1]
    simp
  refine ⟨hfin, ?_⟩
  let χ : (AE F E)ˣ →* ℂ :=
    { toFun := fun x => (ν x : ℂ) * ((absE F E x : ℝ) : ℂ) ^ z
      map_one' := by simp
      map_mul' := fun x y => by simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul]; ring }
  have hχ : Continuous χ := (continuous_subtype_val.comp hν).mul
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z)
  refine tendsto_nhds_unique ((hχ.tendsto l).comp (GlobalTheory.Doubling.tendsto_cutIdele l)) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop hfin.toFinset] with S hS
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin hS, Function.comp_apply, cutIdele_eq, map_mul, map_prod]
  rfl

end GlobalTheory.ThK.ConeEulerChr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfStandardChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words.StdTheta

def negSum (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ :=
  -(∑ w : {w : InfinitePlace F // w.IsReal}, (LinearMap.proj w).comp (LinearMap.fst ℝ _ _))

theorem negSum_apply (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    negSum F z = -∑ w, z.1 w := by
  simp [negSum]

theorem negSum_nondeg (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (z : mixedEmbedding.mixedSpace F)
    (hz : z ≠ 0) : ∃ u, negSum F (z * u) ≠ 0 := by
  have h1 : z.1 ≠ 0 := by
    intro h0
    apply hz
    refine Prod.ext h0 (funext fun w => absurd (IsTotallyReal.isReal w.1) ?_)
    exact InfinitePlace.not_isReal_iff_isComplex.2 w.2
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h1
  refine ⟨(Pi.single w 1, 0), ?_⟩
  rw [negSum_apply]
  simpa [Pi.single_apply] using hw

theorem cmTypeComponents_sum_eq_realCoordinates_sum (D : D7) (x : Ainf D.host.F) :
    ∑ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((∑ w, (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x).1 w : ℝ) : ℂ) := by
  haveI := D.sp.cm.totReal
  have e1 : ∀ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (GlobalTheory.AdelicU.placeOf D ρ) (x (GlobalTheory.AdelicU.placeOf D ρ)) := by
    intro ρ
    show Formalism.L2.Fam.ThC.projAt (tauE D ρ) (x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Formalism.L2.Fam.ThC.projAt_tmul, map_one, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun ρ _ => e1 ρ,
    (GlobalTheory.AdelicU.placeOf_bijective D).sum_comp (fun w => InfinitePlace.Completion.extensionEmbedding w (x w)),
    Complex.ofReal_sum]
  refine (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w : InfinitePlace D.host.F => IsTotallyReal.isReal w) _ _
    fun w => ?_).symm
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2 (x w.1)

theorem isStdInf_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    GlobalTheory.WeilL2Words.IsStdInf D.host.F ψ := by
  intro D ψ hψ
  haveI := D.sp.cm.totReal
  have h := Formalism.L2.Fam.ThC.allSome_fam.1 hψ.2
  refine ⟨negSum D.host.F, negSum_nondeg D.host.F, fun z => ?_⟩
  have hx := h ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z)
  rw [cmTypeComponents_sum_eq_realCoordinates_sum, RingEquiv.apply_symm_apply] at hx
  show psiInf D.host.F ψ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z) = _
  rw [hx, negSum_apply]
  congr 1
  push_cast
  ring

end GlobalTheory.WeilL2Words.StdTheta
end
end

