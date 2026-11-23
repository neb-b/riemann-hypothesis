module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FEqAndRdEq
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace GlobalTheory.DegreeRankEquations

theorem f_eq (D : D7) (X : HidaSetting D) : X.B.I.f = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  unfold AutInst.f
  omega

theorem rd_eq (D : D7) (X : HidaSetting D) : X.B.I.rd = D.host.rdE := by
  have hd : discr X.B.I.E = discr D.host.E := NumberField.discr_eq_discr_of_algEquiv X.B.I.E X.ιE.toRatAlgEquiv
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : (Module.finrank ℚ D.host.E : ℝ) = 2 * (X.B.I.f : ℝ) := by
    unfold AutInst.f
    have : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ X.B.I.F := by rw [← e1, ← e2, e3, mul_comm]
    rw [this]; push_cast; ring
  unfold AutInst.rd Host.rdE
  rw [hd, e4]

end GlobalTheory.DegreeRankEquations
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStepLocallyStandardDualCoeffIntegral
section
open Formalism.MainNotions.S

namespace GlobalTheory.LocCoef

theorem h_es_eq_zero_of_mem_Fj {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type}
    [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
    (a : Fin r) (u : V) (hu : u ∈ Fr.Fj a.val) : H.h u (Fr.es a) = 0 := by
  unfold Formalism.MainNotions.S.LocNG.FrameD.Fj at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b.val < a.val := hb
    have hba : b ≠ a := fun h => by subst h; exact lt_irrefl _ hb'
    unfold Formalism.MainNotions.S.LocNG.FrameD.e
    rw [Fr.h_es b a, if_neg hba]
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

theorem h_es_mem_O_of_mem_LamStd {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type}
    [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) (w : V) (hw : w ∈ Fr.LamStd L) :
    H.h w (Fr.es a) ∈ M.L.O := by
  unfold Formalism.MainNotions.S.LocNG.FrameD.LamStd at hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx.1 a
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
  | smul c x _ hx =>
    have : H.h (c • x) (Fr.es a) = (c : E) * H.h x (Fr.es a) := H.h_smul_left (c : E) x _
    rw [this]; exact M.L.O.mul_mem c.2 hx

end GlobalTheory.LocCoef

theorem GlobalTheory.locCoef_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) (v : V), v ∈ Fr.Fj (a.val + 1) → v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L) → H.h v (Fr.es a) ∈ M.L.O := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn L a v hv hvimg
  unfold Formalism.MainNotions.S.LocNG.img at hvimg
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hvimg
  have hwv' : n w = v := hwv
  have hu := (_root_.GlobalTheory.unipRadical_moves_step_into_prev Fr n hn (a.val + 1) (Nat.succ_le_of_lt a.isLt) v hv).2
  simp only [Nat.add_sub_cancel] at hu
  have hsymm : n.symm v = w := by rw [← hwv']; exact n.symm_apply_apply w
  rw [hsymm] at hu
  have h0 := GlobalTheory.LocCoef.h_es_eq_zero_of_mem_Fj Fr a (w - v) hu
  have hwO := GlobalTheory.LocCoef.h_es_mem_O_of_mem_LamStd Fr L a w hw
  have hdecomp : H.h w (Fr.es a) = H.h (w - v) (Fr.es a) + H.h v (Fr.es a) := by
    rw [← H.h_add_left, sub_add_cancel]
  rw [hdecomp, h0, zero_add] at hwO
  exact hwO
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianPushforwardDensityStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_pushforward_density : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (G : (ι → ℝ) → ℂ), Continuous G → (∀ S : Set (ι → ℝ), IsCompact S → ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, gauss (y v) : ℝ) : ℂ) = ∫ b in S, G b) → ∀ b : ι → ℝ, (∀ v, b v ≠ 0) → G b = ((∏ v, gaussDens (ε v) (b v) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.GaussMean.ProdDensity.density_eq_prod | exact GlobalTheory.GaussMean.ProdDensity.density_eq_prod | (intros; apply GlobalTheory.GaussMean.ProdDensity.density_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraSeriesCentralIdempotentNeZero
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem ip_symm_of_inv {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun x => ?_
  simp [mul_comm]

theorem exists_cusp_list (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hG : Green) :
    ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 →
      ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2) ∧ degL (Q.map Prod.snd) = n ∧
        f = (Q.map Prod.fst).prod := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn h0
    by_cases hu : IsUnit f
    · have h1 : f = 1 := hf.isUnit_iff.mp hu
      refine ⟨[], by simp, ?_, by simpa using h1⟩
      rw [← hn, h1]; simp [degL]
    · obtain ⟨P, hPm, hPi, q, hq⟩ := Polynomial.exists_monic_irreducible_factor f hu
      have hqm : q.Monic := hPm.of_mul_monic_left (hq ▸ hf)
      have hdeg : n = P.natDegree + q.natDegree := by
        rw [← hn, hq, hPm.natDegree_mul hqm]
      have hpos : 0 < P.natDegree := hPi.natDegree_pos
      have hc : P.coeff 0 * q.coeff 0 ≠ 0 := by
        rwa [hq, Polynomial.mul_coeff_zero] at h0
      obtain ⟨Q, hQ1, hQ2, hQ3⟩ := ih q.natDegree (by omega) q hqm rfl (right_ne_zero_of_mul hc)
      obtain ⟨τ, hτ, -⟩ := hG g L P.natDegree hpos
      have hP : IsPrimeLab P.natDegree P := ⟨hPm, hPi, left_ne_zero_of_mul hc, rfl⟩
      refine ⟨(P, ⟨P.natDegree, τ P⟩) :: Q, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact (hτ P hP).1
        · exact hQ1 p hp
      · rw [hdeg, ← hQ2]; simp [degL]
      · rw [List.map_cons, List.prod_cons, ← hQ3]; exact hq

theorem exists_irr_hasLabel (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hG : Green) (n : ℕ) (f : (ZMod g)[X])
    (hf : f.Monic) (hn : f.natDegree = n) (h0 : f.coeff 0 ≠ 0) :
    ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ HasLabel L ρ f := by
  obtain ⟨Q, hQ1, hQ2, hQ3⟩ := exists_cusp_list g L hG n f hf hn h0
  have hirr : ∀ p ∈ Q.map Prod.snd, IsIrr p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hQ1 q hq).2.1.2.1
  have hch : IsChar (hcL (Q.map Prod.snd) n) :=
    (_root_.GlobalTheory.gl_list_product_perm_char g _ (Q.map Prod.snd) n hQ2.symm fun p hp => by
      obtain ⟨V, -, hV⟩ := hirr p hp
      exact ⟨V, hV⟩).1
  have hne : hcL (Q.map Prod.snd) n 1 ≠ 0 := by
    intro h
    have hd := _root_.GlobalTheory.GLq.HcDeg.hc_degree g (Q.map Prod.snd) n hQ2.symm
    rw [h, zero_mul] at hd
    refine mul_ne_zero ?_ ?_ hd.symm
    · refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
      have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
      have h1 : 1 < g ^ i := Nat.one_lt_pow hi1 (Fact.out : g.Prime).one_lt
      rw [sub_ne_zero]
      exact_mod_cast h1.ne'
    · refine List.prod_ne_zero fun hz => ?_
      obtain ⟨p, hp, hp0⟩ := List.mem_map.mp hz
      obtain ⟨d, hd0, hd1⟩ := (_root_.GlobalTheory.GLq.trIdem (Gn g p.1) 1 p.2).2.1 (hirr p hp)
      rw [hp0] at hd1
      have : d = 0 := by exact_mod_cast hd1.symm
      omega
  have hdec := _root_.GlobalTheory.charDec (Gn g n) (hcL (Q.map Prod.snd) n)
  have hsum := hdec.2.1 (hdec.2.2.1 hch)
  by_contra hcon
  push Not at hcon
  apply hne
  rw [hsum, finsum_mem_of_eqOn_zero]
  · rfl
  · intro ρ hρ
    have : ip (hcL (Q.map Prod.snd) n) ρ = 0 := by
      by_contra hip
      exact hcon ρ hρ ⟨Q, hQ1, hQ2, hQ3, by rwa [ip_symm_of_inv]⟩
    simp [this]

theorem zOf_ne_zero_of_isIrr {G : Type} [Group G] [Fintype G] {ρ : G → ℂ} (hρ : IsIrr ρ) : zOf ρ ≠ 0 := by
  intro h
  obtain ⟨-, h1, h2⟩ := _root_.GlobalTheory.GLq.trIdem G 1 ρ
  obtain ⟨d, hd0, hd1⟩ := h1 hρ
  have htr : tr (1 : MonoidAlgebra ℂ G) ρ = ρ 1 := by
    unfold tr
    rw [Finset.sum_eq_single 1]
    · simp [MonoidAlgebra.one_def]
    · intro b _ hb
      simp [MonoidAlgebra.one_def, Finsupp.single_apply, hb, hb.symm]
    · simp
  have hd : ρ 1 ≠ 0 := by rw [hd1]; exact_mod_cast hd0.ne'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h, mul_zero, htr] at h2
  exact mul_ne_zero (div_ne_zero hd hc) hd (h2.symm.trans (by simp))

theorem eSerC_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), Green → ∀ (n : ℕ) (f : (ZMod g)[X]),
    f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → eSerC L n f ≠ 0 := by
  intro g _ L hG n f hf hn h0 he
  obtain ⟨ρ, hρ, hl⟩ := exists_irr_hasLabel g L hG n f hf hn h0
  have hfin : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1.subset fun χ hχ => hχ.1
  apply zOf_ne_zero_of_isIrr hρ
  have h : zOf ρ * eSerC L n f = zOf ρ := by
    unfold eSerC
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, Finset.sum_eq_single ρ]
    · rw [(_root_.GlobalTheory.GLq.ZOrth.zorth _ ρ ρ hρ hρ).1, if_pos rfl]
    · intro b hb hne
      rw [(_root_.GlobalTheory.GLq.ZOrth.zorth _ ρ b hρ (hfin.mem_toFinset.mp hb).1).1, if_neg hne.symm]
    · intro hb
      exact absurd (hfin.mem_toFinset.mpr ⟨hρ, hl⟩) hb
  rw [← h, he, mul_zero]

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsDistSectionMulBlock
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.SectionHsCompare

variable {P Q P' Q' : ℕ}

section Frob
open scoped Matrix.Norms.Frobenius

theorem frob_sq (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two]

theorem frob_split (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ‖Z‖ ^ 2 = ‖Z (e none) (e none)‖ ^ 2 + ∑ b, ‖Z (e none) (e (some b))‖ ^ 2 +
      ∑ i, ‖Z (e (some i)) (e none)‖ ^ 2 + ∑ i, ∑ b, ‖Z (e (some i)) (e (some b))‖ ^ 2 := by
  have h : ∀ x, ∑ w, ‖Z x w‖ ^ 2 = ∑ o, ‖Z x (e o)‖ ^ 2 := fun x =>
    (e.sum_comp (fun w => ‖Z x w‖ ^ 2)).symm
  rw [frob_sq, Finset.sum_congr rfl (fun x _ => h x),
    ← e.sum_comp (fun x => ∑ o, ‖Z x (e o)‖ ^ 2)]
  simp only [Fintype.sum_option, Finset.sum_add_distrib]
  ring

theorem add_le_mul_pow_of_sq_le_of_le_mul {t η R W : ℝ} (ht : 1 < t) (hη : η = (t - 1) / (3 * t)) (hR : 0 ≤ R)
    (hW : 0 ≤ W) (h1 : W ≤ R + η * R) (h2 : R ≤ W + η * R) :
    R ^ 2 ≤ t * W ^ 2 ∧ W ^ 2 ≤ t * R ^ 2 := by
  have h3 : 0 < 3 * t := by linarith
  have hη0 : 0 ≤ η := by rw [hη]; exact div_nonneg (by linarith) h3.le
  have key : η * (3 * t) = t - 1 := by rw [hη]; field_simp
  have hηt : η < 1 / 3 := by nlinarith
  constructor
  ·
    have hW' : (1 - η) * R ≤ W := by linarith
    have hsq : ((1 - η) * R) ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (by nlinarith) hW' 2
    have hge : 1 ≤ t * (1 - η) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ t), sq_nonneg R]
  ·
    have hW' : W ≤ (1 + η) * R := by linarith
    have hsq : W ^ 2 ≤ ((1 + η) * R) ^ 2 := pow_le_pow_left₀ hW hW' 2
    have hle : (1 + η) ^ 2 ≤ t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg R)]

private lemma le_of_sq_le_sq_of_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  nlinarith

theorem hsDist_section_mul_block : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptSq e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptSq e y + hsDist g ≤ t * hsDist (a * j g) ∧ hsDist (a * j g) ≤ t * (ptSq e y + hsDist g) := by
  intro P Q P' Q' e j hj t ht
  set η : ℝ := (t - 1) / (3 * t) with hη
  have hηpos : 0 < η := div_pos (by linarith) (by linarith)
  have hη3 : η < 1 / 3 := by
    rw [hη, div_lt_iff₀ (by linarith)]; linarith
  set c : ℝ := η / 3 with hc
  have hcpos : 0 < c := by positivity
  have hc1 : c < 1 := by linarith
  refine ⟨min 1 (c ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro y a hy hya hrow hblk g
  have hyc : ptSq e y < c ^ 2 := lt_of_lt_of_le hy (min_le_right _ _)
  have hy1 : ptSq e y < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  obtain ⟨h00, h0b, ha0, hab⟩ := hj g

  have hcol : ∀ x, UpqT.mat a x (e none) = y x := by
    intro x
    have := congrFun hya x
    simpa [act, baseVec, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  set S : ℝ := ∑ i, ‖y (e (some i))‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hpt : ptSq e y = ‖y (e none) - 1‖ ^ 2 + 2 * S := rfl
  have hSpt : S ≤ ptSq e y := by nlinarith [sq_nonneg ‖y (e none) - 1‖]
  have hSc : S < c ^ 2 := lt_of_le_of_lt hSpt hyc
  have hS1 : S < 1 := lt_of_le_of_lt hSpt hy1

  have hn1 : 1 ≤ ‖1 + y (e none)‖ := by
    have h1 : ‖y (e none) - 1‖ < 1 := by
      nlinarith [norm_nonneg (y (e none) - 1), sq_nonneg ‖y (e none) - 1‖]
    have h2 : (2 : ℂ) = (1 + y (e none)) - (y (e none) - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖1 + y (e none)‖ + ‖y (e none) - 1‖ := by
      rw [h2]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith

  set M := UpqT.mat a with hM
  set K := UpqT.mat (j g) - 1 with hK
  set Ep : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := Matrix.of fun x w =>
    (e.symm x).elim 0 (fun _ => (e.symm w).elim 0 (fun _ => (M - 1) x w)) with hEp
  set Z0 := (M - 1) + K - Ep with hZ0
  set Z := UpqT.mat (a * j g) - 1 with hZ
  have hmul : UpqT.mat (a * j g) = M * UpqT.mat (j g) := rfl
  have hZe : Z = (M - 1) + K + (M - 1) * K := by
    rw [hZ, hmul, hK]; noncomm_ring
  have hdiff : Z - Z0 = Ep + (M - 1) * K := by
    rw [hZe, hZ0]; abel

  have hK2 : ‖K‖ ^ 2 = hsDist g := by
    rw [frob_split e K]
    simp [hK, Matrix.sub_apply, Matrix.one_apply, h00, h0b, ha0, hab, hsDist]
  have hEp2 : ‖Ep‖ ^ 2 = ∑ i, ∑ b, ‖(M - 1) (e (some i)) (e (some b))‖ ^ 2 := by
    rw [frob_split e Ep]
    simp [hEp, Matrix.of_apply]
  have hEpS : ‖Ep‖ ^ 2 ≤ S ^ 2 := by
    rw [hEp2, sq, hS, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => ?_
    rw [hblk i b, div_pow, ← mul_pow]
    have hp : 0 ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 := sq_nonneg _
    calc (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 / ‖1 + y (e none)‖ ^ 2
        ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 / 1 :=
          div_le_div_of_nonneg_left hp one_pos (by nlinarith)
      _ = (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 := div_one _
  have hM2 : ‖M - 1‖ ^ 2 = ptSq e y + ‖Ep‖ ^ 2 := by
    rw [frob_split e (M - 1), hEp2, hpt]
    simp [Matrix.sub_apply, Matrix.one_apply, hcol, hrow]
    rw [hS, Fintype.sum_sum_type]
    ring
  have e00 : Z0 (e none) (e none) = y (e none) - 1 := by
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, hcol, h00]
  have e0b : ∀ b, Z0 (e none) (e (some b)) = M (e none) (e (some b)) := by
    intro b
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, h0b]
  have ei0 : ∀ i, Z0 (e (some i)) (e none) = y (e (some i)) := by
    intro i
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hcol, ha0]
  have eib : ∀ i b, Z0 (e (some i)) (e (some b)) = (UpqT.mat g - 1) i b := by
    intro i b
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hab]
  have hZ02 : ‖Z0‖ ^ 2 = ptSq e y + hsDist g := by
    rw [frob_split e Z0, e00]
    simp only [e0b, ei0, eib, hrow]
    rw [hpt, hS]
    unfold hsDist
    ring
  have hZ2 : ‖Z‖ ^ 2 = hsDist (a * j g) := by
    rw [frob_sq]; rfl

  have hR0 : 0 ≤ ‖Z0‖ := norm_nonneg _
  have hEpb : ‖Ep‖ ≤ c * ‖Z0‖ := by
    apply le_of_sq_le_sq_of_nonneg (by positivity)
    rw [mul_pow, hZ02]
    have hg : 0 ≤ hsDist g := by rw [← hK2]; positivity
    calc ‖Ep‖ ^ 2 ≤ S ^ 2 := hEpS
      _ = S * S := sq S
      _ ≤ S * c ^ 2 := mul_le_mul_of_nonneg_left hSc.le hS0
      _ ≤ ptSq e y * c ^ 2 := mul_le_mul_of_nonneg_right hSpt (sq_nonneg c)
      _ ≤ c ^ 2 * (ptSq e y + hsDist g) := by
        rw [mul_comm, mul_add]; exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg c) hg)
  have hMb : ‖M - 1‖ ≤ 2 * c := by
    apply le_of_sq_le_sq_of_nonneg (by positivity)
    rw [hM2]
    have h1 : ‖Ep‖ ^ 2 ≤ c ^ 2 :=
      calc ‖Ep‖ ^ 2 ≤ S ^ 2 := hEpS
        _ = S * S := sq S
        _ ≤ S * c ^ 2 := mul_le_mul_of_nonneg_left hSc.le hS0
        _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hS1.le (sq_nonneg c)
        _ = c ^ 2 := one_mul _
    have h2 : (2 * c) ^ 2 = 4 * c ^ 2 := by ring
    rw [h2]
    linarith [sq_nonneg c]
  have hKb : ‖K‖ ≤ ‖Z0‖ := by
    apply le_of_sq_le_sq_of_nonneg hR0
    rw [hK2, hZ02]
    have : 0 ≤ ptSq e y := by rw [hpt]; positivity
    linarith
  have hdb : ‖Z - Z0‖ ≤ η * ‖Z0‖ := by
    rw [hdiff]
    calc ‖Ep + (M - 1) * K‖ ≤ ‖Ep‖ + ‖(M - 1) * K‖ := norm_add_le _ _
      _ ≤ ‖Ep‖ + ‖M - 1‖ * ‖K‖ := by gcongr; exact Matrix.frobenius_norm_mul _ _
      _ ≤ c * ‖Z0‖ + 2 * c * ‖Z0‖ := by gcongr
      _ = η * ‖Z0‖ := by rw [hc]; ring
  have h1 : ‖Z‖ ≤ ‖Z0‖ + η * ‖Z0‖ := by
    calc ‖Z‖ = ‖Z0 + (Z - Z0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖Z0‖ + ‖Z - Z0‖ := norm_add_le _ _
      _ ≤ ‖Z0‖ + η * ‖Z0‖ := by gcongr
  have h2 : ‖Z0‖ ≤ ‖Z‖ + η * ‖Z0‖ := by
    calc ‖Z0‖ = ‖Z - (Z - Z0)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Z‖ + ‖Z - Z0‖ := norm_sub_le _ _
      _ ≤ ‖Z‖ + η * ‖Z0‖ := by gcongr
  obtain ⟨hA, hB⟩ := add_le_mul_pow_of_sq_le_of_le_mul ht hη hR0 (norm_nonneg _) h1 h2
  rw [hZ02, hZ2] at hA hB
  exact ⟨hA, hB⟩

end Frob

end GlobalTheory.SectionHsCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfLowest
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.LowestVectorDegree

theorem isFdeg_fdegOf_lowest : ∀ (D : D7) (X : HidaSetting D) (v : InfinitePlace X.B.I.F),
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) :=
  fun _ X v => isFdeg_fdegOf_of_isDS (X.ds v) (X.low v).1

end GlobalTheory.LowestVectorDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponentsStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_lattice_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] v.adicCompletion F), y ∈ loc v L ↔ (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2) ∧ (∀ g : GL (Fin n) (v.adicCompletion F), ∃! h : UPts cm.sig J (v.adicCompletion F), bc ((RingHom.fst _ _).comp sp.toRingHom) h.1 = g) ∧ ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 = ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
  first | exact @GlobalTheory.St.G.split_components | exact GlobalTheory.St.G.split_components | (intros; apply GlobalTheory.St.G.split_components <;> assumption)
end

