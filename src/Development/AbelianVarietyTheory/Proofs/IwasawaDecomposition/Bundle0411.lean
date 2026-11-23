module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.KernelLattices.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.ColInst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0403
public import Lean

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointUnitaryNormalisesLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleBasePoint_unitary_normalisesLevel : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (k : GL (Fin n) (AfE F E)) (c : DiaG (E := E) (ST := ST)), (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → k ∈ UAd hc n ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) ∧ (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, k.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) ∧ ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) k)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.basePt_facts | exact GlobalTheory.Mem.Col2.ChEx.basePt_facts | (intros; apply GlobalTheory.Mem.Col2.ChEx.basePt_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassesBijectiveOrbitsFramedLatticesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartClasses_bijective_orbits_framedLattices : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.clsF_bij | exact GlobalTheory.Mem.Col2.ChEx.clsF_bij | (intros; apply GlobalTheory.Mem.Col2.ChEx.clsF_bij <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChangeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_moves_with_frameChange : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.invActs_cqOf | exact GlobalTheory.Mem.Col2.ChEx.invActs_cqOf | (intros; apply GlobalTheory.Mem.Col2.ChEx.invActs_cqOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoRawMulIdem
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_den_idem {Q w : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε) (hw : w ≠ Q)
    (a : E ⊗[F] Formalism.L2.Herm.Af F) :
    ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ ∃ hm : iA F E (algebraMap (𝓞 E) E t) * (ε * a) ∈ Formalism.L2.Herm.intAf F E,
      resS F w ⟨_, hm⟩ = 0 := by
  obtain ⟨N, hN, hNa⟩ := GlobalTheory.PlaceDatum.exists_den_adele (F := F) (E := E) a
  have hN0 : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have hv0 : Q.intValuation (N : 𝓞 E) ≠ 0 := Q.intValuation_ne_zero _ hN0
  set k : ℕ := (-(WithZero.log (Q.intValuation (N : 𝓞 E)))).toNat with hk
  have hvk : Q.intValuation (N : 𝓞 E) = WithZero.exp (-(k : ℤ)) := by
    have h1 := Q.intValuation_le_one (N : 𝓞 E)
    rw [← WithZero.exp_log hv0] at h1 ⊢
    have h2 : WithZero.log (Q.intValuation (N : 𝓞 E)) ≤ 0 := by
      rw [← WithZero.exp_le_exp]; simpa using h1
    congr 1
    rw [hk]; omega
  obtain ⟨t, htk, htw⟩ : ∃ t ∈ Q.asIdeal ^ k, t ∉ w.asIdeal := by
    by_contra hn
    push Not at hn
    have hle : Q.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hn
    exact hw (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm
  have hNE : ((N : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hval : Q.valuation E ((t : E) * ((N : 𝓞 E) : E)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, show (t : E) = algebraMap (𝓞 E) E t from rfl,
      show ((N : 𝓞 E) : E) = algebraMap (𝓞 E) E (N : 𝓞 E) from rfl,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hvk,
      mul_inv_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), one_mul]
    exact (Q.intValuation_le_pow_iff_mem t k).2 htk
  have hNc : ((N : ℕ) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E ((N : 𝓞 E) : E) := by simp
  have hinv : iA F E ((N : 𝓞 E) : E) * iA F E (((N : 𝓞 E) : E))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hNE, map_one]
  have e : iA F E (algebraMap (𝓞 E) E t) * (ε * a) =
      ε * iA F E ((t : E) * ((N : 𝓞 E) : E)⁻¹) * ((N : E ⊗[F] Formalism.L2.Herm.Af F) * a) := by
    rw [hNc, map_mul, show algebraMap (𝓞 E) E t = (t : E) from rfl]
    linear_combination (-(iA F E (t : E) * ε * a)) * hinv
  have hm : iA F E (algebraMap (𝓞 E) E t) * (ε * a) ∈ Formalism.L2.Herm.intAf F E := by
    rw [e]; exact mul_mem (h.mul_mem_of_val hval) hNa
  have hm2 : ε * (iA F E (algebraMap (𝓞 E) E t) * a) ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_left_comm]; exact hm
  refine ⟨t, htw, hm, ?_⟩
  have e2 : (⟨_, hm⟩ : Formalism.L2.Herm.intAf F E) = ⟨_, hm2⟩ := Subtype.ext (mul_left_comm _ _ _)
  rw [e2]
  exact h.resS_eq_zero hw hm2

section Lat

variable [StarRing E] {n : ℕ} [NeZero n]

theorem pullV_mul_idem {ε : E ⊗[F] Formalism.L2.Herm.Af F} (x g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hg : ε • ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) = (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)
    (v : Fin n → E) (i : Fin n) :
    pullV (x * g⁻¹) v i = pullV x v i +
      ε * ((((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ pullV x v) i) := by
  rw [pullV_mul_inv]
  conv_lhs => rw [← sub_add_cancel (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) 1, ← hg]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, add_comm]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem mem_localization_globLat_mul_inv_of_ne {Q w : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε) (hw : w ≠ Q)
    (x g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hg : ε • ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) = (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)
    (v : Fin n → E) (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) :
    v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat (x * g⁻¹) (stdLat E n)) ∧
      ∀ i, redA w (pullV (x * g⁻¹) v i) = redA w (pullV x v i) := by
  obtain ⟨s, hs, hsu⟩ := pullV_den hv
  set c := ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ pullV x v with hc
  choose t ht hm hz using fun i => exists_den_idem h hw (c i)
  have hT : (∏ i, t i) ∉ w.asIdeal := fun hT => by
    obtain ⟨i, _, hi⟩ := (w.isPrime.prod_mem_iff).1 hT
    exact ht i hi
  have hTc : ∀ i, iA F E (algebraMap (𝓞 E) E (∏ j, t j)) * (ε * c i) ∈ Formalism.L2.Herm.intAf F E := by
    intro i
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
    rw [hr, map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E (t i))), mul_assoc]
    exact mul_mem (iA_mem r) (hm i)
  refine ⟨(Formalism.L2.Col.mem_locP w _ v).2 ⟨s * ∏ j, t j, fun hh => (w.isPrime.mem_or_mem hh).elim hs hT,
    (mem_globLat _ _).2 fun i => ?_⟩, fun i => ?_⟩
  · rw [pullV_osmul, pullV_mul_idem x g hg, map_mul, map_mul, mul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm (iA F E (algebraMap (𝓞 E) E s)), mul_assoc]
      exact mul_mem (iA_mem _) (hsu i)
    · rw [mul_assoc]
      exact mul_mem (iA_mem _) (hTc i)
  · have h1 : iA F E (algebraMap (𝓞 E) E (s * t i)) * pullV x v i ∈ Formalism.L2.Herm.intAf F E := by
      rw [map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E s)), mul_assoc]
      exact mul_mem (iA_mem _) (hsu i)
    have h2 : iA F E (algebraMap (𝓞 E) E (s * t i)) * (ε * c i) ∈ Formalism.L2.Herm.intAf F E := by
      rw [map_mul, map_mul, mul_assoc]
      exact mul_mem (iA_mem _) (hm i)
    have hst : s * t i ∉ w.asIdeal := fun hh => (w.isPrime.mem_or_mem hh).elim hs (ht i)
    rw [pullV_mul_idem x g hg, redA_add w hst h1 h2]
    have h0 : redA w (ε * c i) = 0 := redA_eq w (ht i) (hm i) (by rw [mul_zero, hz i])
    rw [h0, add_zero]

end Lat

theorem decoRaw_mul_idem [StarRing E] {n : ℕ} [NeZero n] (ST SG : Finset (Pl E)) (Q : Pl E)
    (ε : E ⊗[F] Formalism.L2.Herm.Af F) (h : IdemOf F Q ε) (hQT : Q ∉ ST) (hQG : Q ∉ SG)
    (y b : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hb : ε • (b.1 - 1) = b.1 - 1) :
    (decoRaw ST SG (y * b)).f = (decoRaw ST SG y).f ∧ (decoRaw ST SG (y * b)).be = (decoRaw ST SG y).be := by
  have hb' : ε • (((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) =
      ((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 := by
    have e : ((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 =
        -(((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          ((b : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)) := by
      rw [Matrix.mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      abel
    rw [e, smul_neg, ← Matrix.mul_smul]
    congr 2
  have hiff : ∀ w : Pl E, w ≠ Q → ∀ v : Fin n → E,
      v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat (y * b) (stdLat E n)) ↔
        v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) := by
    intro w hw v
    constructor
    · intro hv
      have := (mem_localization_globLat_mul_inv_of_ne h hw (y * b) b hb v hv).1
      rwa [mul_inv_cancel_right] at this
    · intro hv
      have := (mem_localization_globLat_mul_inv_of_ne h hw y b⁻¹ hb' v hv).1
      rwa [inv_inv] at this
  have hred : ∀ w : Pl E, w ≠ Q → ∀ v : Fin n → E,
      v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) →
        ∀ i, redA w (pullV (y * b) v i) = redA w (pullV y v i) := by
    intro w hw v hv i
    have := (mem_localization_globLat_mul_inv_of_ne h hw y b⁻¹ hb' v hv).2 i
    rwa [inv_inv] at this
  refine ⟨funext fun P => funext fun v => ?_, funext fun w => funext fun v => ?_⟩
  · have hP : P.1 ≠ Q := fun e => hQT (e ▸ P.2)
    simp only [decoRaw]
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n))
    · rw [if_pos ((hiff P.1 hP v).2 hv), if_pos hv, hred P.1 hP v hv]
    · rw [if_neg (fun h' => hv ((hiff P.1 hP v).1 h')), if_neg hv]
  · have hP : w.1 ≠ Q := fun e => hQG (e ▸ w.2)
    simp only [decoRaw]
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n))
    · rw [if_pos ((hiff w.1 hP v).2 hv), if_pos hv]
      funext i
      exact hred w.1 hP v hv i
    · rw [if_neg (fun h' => hv ((hiff w.1 hP v).1 h')), if_neg hv]

end GlobalTheory.InertNbr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EMtTied
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.EMt

theorem eMtTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch) (C : ColsTiedSym (I.rec7 l Z)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)), (∀ u F G, inner ℂ ((I.rec7 l Z).eMt u F) ((I.rec7 l Z).eMt u G) = I.ipMt l u I.mu0 F G) → (∀ u (a : (I.rec7 l Z).what₂.Tup), a ≠ (I.rec7 l Z).what₂.mu0 → ∀ F G, inner ℂ ((I.rec7 l Z).eMtTw u a F) ((I.rec7 l Z).eMtTw u a G) = I.ipMt l u a F G) → Formalism.L2.Rows.EMtTied (I.rec7 l Z) C t := by
  intro B X I hOk hP l Z l0 nch tp C t h0 h1
  refine ⟨fun u F G => ?_, fun u a ha F G => ?_⟩
  · rw [h0 u F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u I.mu0 (C.forms u).jM (C.forms u).per.2.1 (C.forms u).per.2.2).1 F G
  · rw [h1 u a ha F G]
    exact (GlobalTheory.Mem.Col2.IpMt.ipMt_tie I hOk hP l Z u a (t.ptE.jM u a) (t.ptE.per u a ha).2.1 (t.ptE.per u a ha).2.2).1 F G

end GlobalTheory.Mem.Col2.EMt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def eWt (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) :=
  LinearEquiv.refl ℂ _

theorem eWt_apply (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (z : (I.per l u a).Wrow)
    (c : (I.fm l u a).clsP) (s : Formalism.L2.Forms.FrP (I.rec7 l Z)) (s' : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1))
    (h : s'.1 = s.1) : eWt I l Z u a z c s = z c s' := by
  have e : s' = s := Subtype.ext h
  subst e
  rfl

end GlobalTheory.Mem.Col2.TwP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvLgCanonical
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwIdxEx

open JetEx

def stepSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E)
    (k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E))) : Set ℂ :=
  jetSet (hostAmb (amb0 P.host) (chiId χ)) (P.R.N k.2.1) (P.R.N (k.2.1 + 1)) k.2.2.1
    ((∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1) * (P.T k.1 * (∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1))) (totDeg P k.1 k.2.1)

def allSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Set ℂ :=
  ⋃ k ∈ {k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (k.2.1 < P.R.m ∧ (∀ Q ∈ k.2.2.1, Q ∈ badP P Ξ) ∧ ∀ Q ∈ k.2.2.2, Q ∈ badP P Ξ) ∧ FinAlg (stepSet P χ k)}, stepSet P χ k

theorem finAlg_allSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (h : Ξ.Finite) : FinAlg (allSet P χ Ξ) := by
  have hb := badPrimes_finite₂ P h
  have hs : {S : Finset (HeightOneSpectrum (𝓞 P.host.E)) | ∀ Q ∈ S, Q ∈ badP P Ξ}.Finite :=
    hb.toFinset.powerset.finite_toSet.subset fun S hS =>
      Finset.mem_coe.2 (Finset.mem_powerset.2 fun Q hQ => hb.mem_toFinset.2 (hS Q hQ))
  refine finAlg_biUnion ?_ fun k hk => hk.2
  exact (Set.finite_univ.prod ((Set.finite_Iio P.R.m).prod (hs.prod hs))).subset fun k hk => ⟨trivial, hk.1⟩


open Classical in
def gens (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Finset ℂ :=
  if h : FinAlg (allSet P χ Ξ) then h.choose else ∅

theorem gens_algebraic (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : ∀ z ∈ gens P χ Ξ, IsAlgebraic ℚ z := by
  unfold gens
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem allSet_subset (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (h : Ξ.Finite) {K : Subfield ℂ}
    (hK : ∀ z ∈ gens P χ Ξ, z ∈ K) : allSet P χ Ξ ⊆ K := by
  have h1 := finAlg_allSet P χ h
  rw [gens, dite_eq_left h1] at hK
  exact h1.choose_spec.2.trans (Subfield.closure_le.2 hK)

theorem jetsIn_of_isTw {B : Base} {X : PreX B.toPre} (hL : StagesInhab.HasLetters B.toPre) {I : TC B X} (h : I.Ok) (ht : I.IsTw)
    (hJ : I.J = amb0 B.host) (hK : ∀ z ∈ gens B.toPre I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) :
    ColIn.JetsIn I := by
  have hall := allSet_subset B.toPre I.C.chiPsi (Set.finite_range I.xi) hK
  refine I.jetsIn_iff.2 fun a u i hi N N' c x hx e he => ?_
  have hM : I.modulus a u = (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1) *
      (B.T u * (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1)) := by
    have eA : (I.cst a).A = B.R.m + 1 := by rw [ht.cst_eq a]; rfl
    have eB : (I.cst a).B = B.R.m + 1 := by rw [ht.cst_eq a]; rfl
    unfold ColIn.modulus cAof cBof
    rw [eA, eB, Finset.prod_coe_sort _ qOf]
  have hS : stepSet B.toPre I.C.chiPsi (u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)) =
      jetSet I.A (B.R.N i) (B.R.N (i + 1)) (I.Sb a u) (I.modulus a u) (totDeg B.toPre u i) := by
    rw [hM, ColIn.A, hJ]
    exact (jetSet_amb B _ _ _ _ _ _ _).symm
  have hpos : 0 < I.modulus a u := by
    rw [hM]
    have := Finset.prod_pos fun Q (_ : Q ∈ rowSG (B.primes X) I.sel (I.tup a)) =>
      Nat.pos_of_ne_zero (by simpa using qPow_ne_zero Q 1 : qOf Q ≠ 0)
    have := (B.T_prime u).pos
    positivity
  refine hall (Set.mem_iUnion₂.2 ⟨(u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)),
    ⟨⟨hi, Sb_subset h a u, rowSG_subset h a⟩, ?_⟩, ?_⟩)
  · rw [hS]
    exact finAlg_step hL h a u _ _ _ _ hpos
  · rw [hS]
    exact ⟨N, N', c, x, e, hx, degree_eq_totDeg B u i e he, rfl⟩

theorem lg_gens (K : Top.Ctx) : Top.large₂ K fun B f T => ∀ z ∈ gens B.toPre f.chiPsi (T.set f), z ∈ B.embLL.fieldRange :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P f _ _ Ξ => gens P f.chiPsi Ξ, by simp,
    fun P f _ _ Ξ => gens_algebraic P f.chiPsi Ξ, fun _ _ _ _ h _ _ => h.2⟩

theorem exists_quot {K : Top.Ctx} {P : Pre} (h : K.Over P) (X : PreX P) :
    ∃ X' : PreX P, X'.piG = X.piG ∧ ∀ u, P.cOf u * (X'.piT u : P.host.E) = (X'.piT P.u₀ : P.host.E) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  refine ⟨{ X with
    piT := K.Lv.piT
    piT_K := K.Lv.piT_K
    piT_norm := K.Lv.piT_norm
    piT_cong := fun u => Ideal.mem_span_singleton.1 (K.Lv.piT_cong u) }, rfl, fun u => ?_⟩
  exact div_mul_cancel₀ _ (K.Lv.piT_ne u)

theorem evLg_canonical : GlobalTheory.Mem.Top.EvLg fun _ B f T => (letI := B.host.cmStar; ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b → B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b) → Nonempty (PreX B.toPre) → ∀ Pv, IsSel B.fields Pv → ∃ (X : PreX B.toPre) (I : TC B X), I.Ok ∧ TC.Pins B X ∧ I.IsTw ∧ ColIn.JetsIn I ∧ I.sel = Pv ∧ I.C = f ∧ I.S = {p | p ∈ GlobalTheory.Mem.Top.offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} ∧ Set.range I.xi = T.set f ∧ ∀ C W V S N G, Formalism.L2.Host.ValLL0 (assemble B C W V S N G) (GlobalTheory.Mem.Top.Fr.at ⟨B, C, W, V, S, N, G⟩ f) ∧ GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE := by
  refine InEx.ev_of_forall fun K => ((InEx.lg_colIn K).inter (lg_gens K)).imp fun B f T hO h hi ⟨X₀⟩ Pv hPv => ?_
  obtain ⟨X₁, hX⟩ := InEx.exists_oriented X₀ f.P
  obtain ⟨X, e, hc⟩ := exists_quot hO X₁
  have hX' : InEx.Oriented X f.P := by
    unfold InEx.Oriented at hX ⊢
    rw [e]; exact hX
  obtain ⟨I, a1, rfl, a3, a4, a5, a6, a7⟩ := h.1.1 X hX' Pv hPv (amb0 B.host) (exists_ambIn_ok B.host).choose_spec
  have hk : (canon I).Ok := canon_ok a1 fun a P hP => ((a7 a).2.2.2 P hP).ge
  exact ⟨X, canon I, hk, ⟨hi, hc⟩, canon_isTw I,
    jetsIn_of_isTw (hasLetters_of_over hO) hk (canon_isTw I) a6 (by have := h.2; rw [← a4] at this; exact this), a5, rfl, a3, a4,
    fun C W V S N G => ⟨h.1.2.1 C W V S N G, h.1.2.2⟩⟩

end GlobalTheory.Mem.Col2.TwIdxEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSRestRe
section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

section Core

variable {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
  (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)
  (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y))


set_option maxHeartbeats 4000000 in
def sIsoRe (hR : Formalism.L2.Theta.RealTied D) (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) :
    SIso (reD D ⟨P.toNew hD j, N, hh⟩).s (sOf hF) where
  cd := by
    have h := (real_reS D (P.toNew hD j)).1 hR
    exact cdScale_eq_cdScaleOf (reD D ⟨P.toNew hD j, N, hh⟩) ((by with_unfolding_all exact (h.cdScale :)))
  del := rfl
  letter := rfl
  eHH := (by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))
  eCu := fun u => (by with_unfolding_all exact (eCure ⟨P.toNew hD j, N, hh⟩ P.fin hF u :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).1 :))
  volN := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).1 :))
  volH := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).2 :))
  eT := fun u u' => (by with_unfolding_all exact (eRT ⟨P.toNew hD j, N, hh⟩ P.Y u u' :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => by
    apply Subtype.ext
    exact (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.1 :))
  atP := fun p => (by with_unfolding_all exact ((hL p).some :))
  ePl := (by with_unfolding_all exact (Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.1 q :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.1 :))
  eP := fun u u' => (by with_unfolding_all exact ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose :))
  pfst := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1 :))
  psnd := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.1 :))
  s0 := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.1 :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.1 :))
  pval := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.2 :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} (p : RP P.Y u u') => by
    have h1 := ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 p.1.1).2.2.2.2.2.2.2.2.1
    have h2 := ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1
    exact (by with_unfolding_all exact (h1.trans (congrArg (fun t => Formalism.L2.SG.PairVal.massTerm t) h2) :))
  meanCount := by
    funext u u' w
    exact (by with_unfolding_all exact ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').2 w :))

end Core

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 4000000 in
theorem exists_sRest_re : ∀ (D : D7) (F : ∀ u, Forms0 D u) (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F F') (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)), Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.Theta.RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → ∃ S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro D F P hD j N hh F' hs hF hph hL hR hDs
  have hR' := (real_reS D (P.toNew hD j)).1 hR
  have hDs' : (reD D ⟨P.toNew hD j, N, hh⟩).what₂.Dstar = StandardLattice.DstarD (reD D ⟨P.toNew hD j, N, hh⟩) := (by with_unfolding_all exact (hDs.trans (real_reS D (P.toNew hD j)).2.1.symm :))
  have hAut : Formalism.MainNotions.S.AutTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.B
      (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.pl :=
    GlobalTheory.BundleTie.autTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X
      ⟨(by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))⟩ ((by with_unfolding_all exact (hph :))) hDs' (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).inst
      ((by with_unfolding_all exact (Formalism.L2.Theta.VolTieG.volTie hR'.vol :))) ((by with_unfolding_all exact (hR'.cdScale :))) ((by with_unfolding_all exact (hR'.dsig_all :)))
  refine ⟨⟨sIsoRe P hD j N hh hF hR hL, hAut, ?_, j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G), ?_, (by with_unfolding_all exact (hL :))⟩, rfl⟩
  · intro u x
    apply Subtype.ext
    exact (by with_unfolding_all exact (colDictL_reTr ⟨P.toNew hD j, N, hh⟩ (P.tr u) (hs u).2.1 (hs u).2.2 P.Y.hK x :))
  · intro x
    exact (by with_unfolding_all exact ((conjHH_eEECre ⟨P.toNew hD j, N, hh⟩ P.G (j x)).symm :))

end GlobalTheory.Mem.SRe
end
end

