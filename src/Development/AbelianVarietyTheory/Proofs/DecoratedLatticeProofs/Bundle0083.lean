module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0059
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicHatMulOfMulClosed
section
noncomputable section

namespace GlobalTheory.AdelicLatticeClosure

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem adelic_hat_mul_of_mul_closed {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (J : Set E) (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J) {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F J) (hw : w ∈ GlobalTheory.AdLat.hat1 F J) :
    z * w ∈ GlobalTheory.AdLat.hat1 F J := by
  unfold GlobalTheory.AdLat.hat1 at hz hw ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x * y, hJ x hx y hy, ?_⟩
      · exact mul_mem (ha v) (hb v)
      · exact Algebra.TensorProduct.tmul_mul_tmul a b x y
    | zero => rw [mul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | neg u _ hu => rw [mul_neg]; exact neg_mem hu
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

theorem adelic_hat_one_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E))
    (hw : w ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) :
    z * w ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
  refine adelic_hat_mul_of_mul_closed _ ?_ hz hw
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
  exact (FractionalIdeal.mem_one_iff _).2 ⟨a * b, map_mul _ a b⟩

end GlobalTheory.AdelicLatticeClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfSqrtDetTwistStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist : ∀ (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ), HasTypes (Cover.twist R) lam → HasTypes R fun a => lam a + 1 / 2 := by
  first | exact @GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | exact GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | (intros; apply GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralVectorBasesBoundedFiniteUnitaryClasses
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.BasesFin

theorem trForm_denom : ∀ (I : AutInst), ∃ c : ℕ, 0 < c ∧ ∀ x y : Fin I.n → I.E, IntVec I x → IntVec I y →
    ∃ m : ℤ, (c : ℚ) * trForm I x y = m := by
  intro I
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : Fin I.n × Fin I.n => I.J p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  have hcJ : ∀ a b, IsIntegral ℤ ((y.natAbs : I.E) * I.J a b) := by
    intro a b
    have h := hyi (I.J a b) (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩)
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with hy | hy
    · rw [hy] at h; simpa using h
    · rw [hy] at h
      have := h.neg
      simpa [neg_mul] using this
  intro x z hx hz
  have hint : IsIntegral ℤ ((y.natAbs : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x z) := by
    unfold Formalism.UG.hform
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun j _ => ?_
    have : (y.natAbs : I.E) * ((starRingEnd I.E) (x i) * I.J i j * z j)
        = (starRingEnd I.E) (x i) * ((y.natAbs : I.E) * I.J i j) * z j := by ring
    rw [this]
    have hs : IsIntegral ℤ ((starRingEnd I.E) (x i)) := (hx i).map (starRingEnd I.E).toIntAlgHom
    exact (hs.mul (hcJ i j)).mul (hz j)
  have htr := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) hint
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr
  refine ⟨m, ?_⟩
  rw [eq_intCast] at hm
  rw [hm]
  unfold trForm
  rw [← map_natCast (algebraMap ℚ I.E), ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem fix_one (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I.n) I.E)
    (he : IsZBasis I e) (hA : ∀ j, A *ᵥ e j = e j) : A = 1 := by
  have key : ∀ u, IntVec I u → A *ᵥ u = u := by
    intro u hu
    obtain ⟨z, rfl⟩ := (he.2 u).1 hu
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hA]
  ext i j
  have hs : IntVec I (Pi.single j 1) := by
    intro l
    by_cases h : l = j
    · subst h; simpa using isIntegral_one
    · simp [Pi.single_apply, h, isIntegral_zero]
  have := congrFun (key _ hs) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem bases_finite_classes : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  intro I N R
  classical
  obtain ⟨c, hc0, hc⟩ := trForm_denom I
  let T := (Module.Free.ChooseBasisIndex ℤ (𝓞 I.E) → Fin N → Fin N → ℤ) × (Fin N → Fin N → ℚ)
  let has : (Fin N → Fin I.n → I.E) → T → Prop := fun e t =>
    (∀ k j, (integralBasis I.E k : I.E) • e j = ∑ i, t.1 k j i • e i) ∧ ∀ i j, trForm I (e i) (e j) = t.2 i j
  let A : Set T := (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => {z : ℤ | |(z:ℝ)| ≤ R}) ×ˢ
    (Set.univ.pi fun _ => Set.univ.pi fun _ => {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m})
  have hZ : {z : ℤ | |(z:ℝ)| ≤ R}.Finite := by
    refine (Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun z hz => ?_
    simp only [Set.mem_setOf_eq] at hz
    have h := abs_le.mp hz
    have hR := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉:ℝ)) ≤ z := by linarith
      exact_mod_cast this
    · have : (z:ℝ) ≤ ⌈R⌉ := by linarith
      exact_mod_cast this
  have hQ : {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m}.Finite := by
    refine ((Set.finite_Icc (-⌈R * c⌉) ⌈R * c⌉).image fun m : ℤ => (m : ℚ) / c).subset ?_
    rintro q ⟨hq, m, hm⟩
    have hcpos : (0:ℝ) < c := by exact_mod_cast hc0
    have hmq : (m:ℝ) = c * q := by exact_mod_cast hm.symm
    have h := abs_le.mp hq
    have hR := Int.le_ceil (R * c)
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · have : (-(⌈R*c⌉:ℝ)) ≤ m := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have : (m:ℝ) ≤ ⌈R*c⌉ := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have hc' : (c:ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
      simp only
      rw [← hm]; field_simp
  have hA : A.Finite := (Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => hZ).prod
    (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hQ)
  let pick : T → (Fin N → Fin I.n → I.E) := fun t =>
    if h : ∃ e, IsZBasis I e ∧ has e t then Classical.choose h else 0
  have hpick : ∀ t (h : ∃ e, IsZBasis I e ∧ has e t), IsZBasis I (pick t) ∧ has (pick t) t := by
    intro t h
    simp only [pick, dif_pos h]
    exact Classical.choose_spec h
  have uniq : ∀ (f : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → ∀ k j (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → w = t.1 k j := by
    intro f t hf hft k j w hw
    rw [hft.1 k j] at hw
    have h0 : ∑ i, (w i - t.1 k j i) • f i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hw, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf.1 _ h0 i)
  have compat : ∀ (f g : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → has g t →
      ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → (integralBasis I.E k : I.E) • g j = ∑ i, w i • g i := by
    intro f g t hf hft hgt k j w hw
    rw [uniq f t hf hft k j w hw]
    exact hgt.1 k j
  refine ⟨pick '' {t ∈ A | ∃ e, IsZBasis I e ∧ has e t}, (hA.subset (Set.sep_subset _ _)).image _, ?_, ?_⟩
  · rintro _ ⟨t, ⟨-, h⟩, rfl⟩
    exact (hpick t h).1
  · intro e he hb
    choose z hz hzb using hb.1
    let t : T := (z, fun i j => trForm I (e i) (e j))
    have ht : has e t := ⟨hz, fun i j => rfl⟩
    have hint : ∀ i, IntVec I (e i) := fun i => (he.2 (e i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
    have htA : t ∈ A := ⟨fun k _ j _ i _ => hzb k j i, fun i _ j _ => ⟨hb.2 i j, hc _ _ (hint i) (hint j)⟩⟩
    have hex : ∃ e', IsZBasis I e' ∧ has e' t := ⟨e, he, ht⟩
    obtain ⟨he₀, ht₀⟩ := hpick t hex
    obtain ⟨M, hMi, hMe⟩ := _root_.GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul I e (pick t) he he₀ (compat e (pick t) t he ht ht₀)
    obtain ⟨M', hM'i, hM'e⟩ := _root_.GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul I (pick t) e he₀ he (compat (pick t) e t he₀ ht₀ ht)
    have h1 : M' * M = 1 := fix_one I e _ he fun j => by rw [← Matrix.mulVec_mulVec, hMe, hM'e]
    have h2 : M * M' = 1 := (mul_eq_one_comm_of_card_eq (Fin I.n) (Fin I.n) I.E rfl).mp h1
    let γ : GL (Fin I.n) I.E := ⟨M, M', h2, h1⟩
    refine ⟨pick t, ⟨t, ⟨htA, hex⟩, rfl⟩, γ, ?_, hMi, hM'i, hMe⟩
    show Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J
    exact GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis I e M he fun i j => by rw [hMe, hMe]; exact ht₀.2 i j

end GlobalTheory.BasesFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpli
section
open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.SplitValuePow

theorem val_pow {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (N : ℕ) (w : HeightOneSpectrum (𝓞 L)) :
    (χ ^ N).val w = χ.val w ^ N := by
  unfold Formalism.L2.Host.HChar.val Formalism.L2.Host.HChar.locK Formalism.L2.Host.HChar.loc
  simp only [MonoidHom.comp_apply, SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem inf_pow {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (N : ℕ) (k : Lˣ) :
    (χ ^ N).inf k = χ.inf k ^ N := by
  unfold Formalism.L2.Host.HChar.inf
  simp only [MonoidHom.comp_apply, SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  intro D χ a p ha ha0 hp w hw hfin
  obtain ⟨N, hN, hunr⟩ := _root_.GlobalTheory.Corev.UnrPow.exists_pow_unrAt D.host.E χ
  obtain ⟨n, hn2, hinf⟩ := ha
  have hn0 : ∀ τ, n τ ≠ 0 := fun τ h => ha0 τ (by have := hn2 τ; rw [h] at this; push_cast at this; linarith)
  have ht : ∀ v, (χ ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (χ ^ N).HasInf (Formalism.L2.Host.embPsi D.host) (fun g => (N : ℤ) * n (D.eTau.symm g)) := by
    intro k
    rw [inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Fintype.prod_equiv D.eTau _ _ fun τ => ?_
    show _ = _ ^ ((N : ℤ) * n (D.eTau.symm (D.eTau τ)))
    rw [Equiv.symm_apply_apply, ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  refine GlobalTheory.SplitValue.not_isOfFinOrder_val D (χ ^ N) _ p ht hinf'
    (fun g => mul_ne_zero (by exact_mod_cast hN.ne') (hn0 _)) hp w hw ?_
  rw [val_pow]
  exact hfin.pow

end GlobalTheory.SplitValuePow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumLabelsOneRecord
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section
open scoped Classical
open Formalism.MainNotions Formalism.MainNotions.KTwoCosetCount Formalism.MainNotions.MinorIntegralityTorus
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem sum_labels_one_record : ∀ (CH C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), 1 ≤ Cl → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E), (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) → ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b (21 + 4 * |CH|) D.R.m D.R.f ^ ((21 + 4 * |CH|) * (D.R.rS : ℝ)) := by
  intro CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hCl1 hH j hj T hTm
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, rfl, rfl⟩ := hTm δ hδ
    exact labFacts_conc t
  have h := kloostermanCosetSum_le Formalism.MainNotions.MinorIntegralityTorus.NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact
  unfold H1C
  refine h.trans ?_
  have hb : 1 ≤ large₂.sc.b := by linarith [KappaEndpoints.two_le_scale_b D large₂]
  have hCl0 : 0 < Cl := by linarith
  have hc0 : 0 ≤ ccOf CH Cl := by unfold ccOf; positivity
  have hcle : ccOf CH Cl ≤ 21 + 4 * |CH| := by
    unfold ccOf
    have : 4 / Cl ≤ 4 := by rw [div_le_iff₀ hCl0]; linarith
    linarith
  unfold Hb
  rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS := by positivity
  have e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) =
      ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  have e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) =
      (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx

end GlobalTheory.Core.Deg
end
end

