module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Counterexamples.AnisotropicRankZero.WittSphericalSectionLeftInvariantRationalParabol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem per_mM {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {m : ℕ} {f : (κ → AF F) → ℂ}
    (h : Per F m f) (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : Per F m (mM F l f) := by
  intro x z hz
  have hev : ∀ a b : AF F, evI F (a + b) = evI F a + evI F b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hmul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b =>
    map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have ha : arch F (x + z) = arch F x := by
    funext i
    obtain ⟨a, ha0, -, hza⟩ := hz i
    show evI F (x i + z i) = evI F (x i)
    rw [hev, hza, hmul, ha0, mul_zero, add_zero]
  unfold mM
  rw [ha, h x z hz]

theorem norm_word_rep {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) (N : ℕ) :
    ‖word F (List.replicate N (Sum.inr l)) f x‖ = |l (arch F x)| ^ N * ‖f x‖ := by
  induction N with
  | zero => simp [word]
  | succ N ih =>
    rw [List.replicate_succ, word_cons]
    show ‖(l (arch F x) : ℂ) * word F (List.replicate N (Sum.inr l)) f x‖ = _
    rw [norm_mul, ih, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    ring

theorem om_bound_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨K, l, C0, hl, hpoly⟩ := _root_.GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow F (Fin n × Fin d) N
  obtain ⟨P, Cs, c, hsob⟩ := _root_.GlobalTheory.ArchDecay.sobolev_per F (Fin n × Fin d) μ hμ
  obtain ⟨C1, k1, hfin⟩ := _root_.GlobalTheory.ArchDecay.per_om_level F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C2, k2, hL2⟩ := _root_.GlobalTheory.ArchDecay.word_action_square_integrable F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ μ hμ (P + N)
  set A : ℝ := max (max Cs 0 * max C1 1 ^ c * max C2 0) 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  refine ⟨max C0 0 * (K + 1) * A, k1 * c + k2, fun g h x => ?_⟩
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1)
    (by exact_mod_cast one_le_heightGL F h.1)
  obtain ⟨m, hm0, hmC, hper⟩ := hfin g h

  have key : ∀ w : List (Op F (Fin n × Fin d)), w.length ≤ N → (∀ o ∈ w, ∃ l', o = Sum.inr l' ∧ ‖l'‖ ≤ 1) →
      ‖word F w (om (g, h) Φ) x‖ ≤ A * H ^ (k1 * c + k2) := by
    intro w hw hwo
    have hS : word F w (om (g, h) Φ) ∈ schA F (Fin n × Fin d) ∧ Per F m (word F w (om (g, h) Φ)) := by
      clear hw
      induction w with
      | nil => exact ⟨(hP.weil.isUSplitting).pres _ _ hΦ, hper⟩
      | cons o w ih =>
        obtain ⟨l', rfl, -⟩ := hwo o List.mem_cons_self
        obtain ⟨i1, i2⟩ := ih fun o' ho' => hwo o' (List.mem_cons_of_mem _ ho')
        exact ⟨_root_.GlobalTheory.ArchDecay.SchAStab.app_mem_schA F _ (Sum.inr l') _ i1, per_mM i2 l'⟩
    have hH0 : 0 ≤ H := le_trans zero_le_one hH1
    have hb : 0 ≤ max C2 0 * H ^ k2 := mul_nonneg (le_max_right _ _) (pow_nonneg hH0 _)
    have hw' : ∀ v : List (Fin n × Fin d → mixedEmbedding.mixedSpace F), v.length ≤ P → (∀ u ∈ v, ‖u‖ ≤ 1) →
        ∫⁻ y, ‖wordD F v (word F w (om (g, h) Φ)) y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (max C2 0 * H ^ k2) := by
      intro v hv hv1
      have hlen : (v.map Sum.inl ++ w).length ≤ P + N := by
        rw [List.length_append, List.length_map]; omega
      have hsz : ∀ o ∈ v.map Sum.inl ++ w, size F o ≤ 1 := by
        intro o ho
        rcases List.mem_append.1 ho with ho | ho
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ho
          exact hv1 u hu
        · obtain ⟨l', rfl, hl'⟩ := hwo o ho
          exact hl'
      have h3 := hL2 g h (v.map Sum.inl ++ w) hlen hsz
      rw [word_append] at h3
      exact h3.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _)))
    have h2 := hsob m hm0 _ hS.1 hS.2 (max C2 0 * H ^ k2) hb hw' x
    have hm' : (m : ℝ) ^ c ≤ (max C1 1 * H ^ k1) ^ c :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _))) c
    have e1 : ‖word F w (om (g, h) Φ) x‖ ^ 2 ≤ A * H ^ (k1 * c + k2) := by
      refine h2.trans ?_
      calc Cs * (m : ℝ) ^ c * (max C2 0 * H ^ k2)
          ≤ max Cs 0 * (max C1 1 * H ^ k1) ^ c * (max C2 0 * H ^ k2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) hm' (by positivity) (le_max_right _ _)) hb
        _ = (max Cs 0 * max C1 1 ^ c * max C2 0) * H ^ (k1 * c + k2) := by
            rw [mul_pow, ← pow_mul, pow_add]; ring
        _ ≤ A * H ^ (k1 * c + k2) := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _)
    have hT : 1 ≤ A * H ^ (k1 * c + k2) := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ hH1)
    nlinarith [norm_nonneg (word F w (om (g, h) Φ) x)]
  have hx := hpoly (arch F x)
  have k0 : ‖om (g, h) Φ x‖ ≤ A * H ^ (k1 * c + k2) := by
    simpa [word] using key [] (by simp) (by simp)
  have kj : ∀ j, |l j (arch F x)| ^ N * ‖om (g, h) Φ x‖ ≤ A * H ^ (k1 * c + k2) := fun j => by
    have h4 := key (List.replicate N (Sum.inr (l j))) (by simp)
      (fun o ho => ⟨l j, List.eq_of_mem_replicate ho, hl j⟩)
    rwa [norm_word_rep] at h4
  show ‖om (g, h) Φ x‖ * (1 + ‖arch F x‖) ^ N ≤ _
  calc ‖om (g, h) Φ x‖ * (1 + ‖arch F x‖) ^ N
      ≤ ‖om (g, h) Φ x‖ * (max C0 0 * (1 + ∑ j, |l j (arch F x)| ^ N)) :=
        mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
          (norm_nonneg _)
    _ = max C0 0 * (‖om (g, h) Φ x‖ + ∑ j, |l j (arch F x)| ^ N * ‖om (g, h) Φ x‖) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ max C0 0 * (A * H ^ (k1 * c + k2) + ∑ _j : Fin K, A * H ^ (k1 * c + k2)) :=
        mul_le_mul_of_nonneg_left (add_le_add k0 (Finset.sum_le_sum fun j _ => kj j)) (le_max_right _ _)
    _ = max C0 0 * (K + 1) * A * H ^ (k1 * c + k2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittDecompositionIsotropicFrameEisensteinDiction
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch GlobalTheory.ResidueEisenstein
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResidueDictionary

theorem dict : ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ (r + 1)), IsAniso V₀ → ∀ l : Lvl V, l.Good → HasIw d l.K → DataJ D.sp.cm.sig V.gram d.e d.e' l.L l.c (fun g => (iwAbs (absDet d) l.K g : ℝ)) ∧ (∃ T, IsRepsJ D.sp.cm.sig V.gram d.e T) ∧ ∀ T, IsRepsJ D.sp.cm.sig V.gram d.e T → ∀ (g : GA D V) (s : ℂ), sphericalEisensteinSeriesOnGroup d l.K g s = ∑' t : T, (((iwAbs (absDet d) l.K (t.1.1 * g) : ℝ≥0) : ℝ) : ℂ) ^ (s + ((V.rank : ℂ) - (r + 1)) / 2) := by
  intro D V V₀ r d hA l hl hIw
  have hsc : ∀ q : stab d, ScalesBy D.sp.cm.sig V.gram d.e (q : GA D V) (onX d q) := fun q => mul_jX d q
  have hstab := (GlobalTheory.EisCont.parFlag_stab_leftInv D V V₀ (r + 1) d).2.2.1
  have hiff : ∀ x : GA D V, (∃ β, ScalesBy D.sp.cm.sig V.gram d.e x β) ↔ x ∈ stab d := fun x =>
    ⟨fun ⟨β, e⟩ => (hstab x β e).1, fun hx => ⟨_, hsc ⟨x, hx⟩⟩⟩
  have htriv := GlobalTheory.Doubling.triv_of_isCompact (isClosed_stab d) (continuous_absDet d) hl.isCompact_K

  have hmk : ∀ t γ : GQ V, GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) t = GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ ↔
      ((γ * t⁻¹ : GQ V) : GA D V) ∈ stab d := fun t γ => by
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    constructor
    · rintro ⟨δ, hδ⟩
      have : (γ * t⁻¹ : GQ V) = δ := by rw [← hδ]; group
      rw [this]; exact δ.2
    · intro h
      exact ⟨⟨γ * t⁻¹, h⟩, by simp⟩
  refine ⟨⟨isCMExt_host D, GlobalTheory.Doubling.isHermND_gram V, GlobalTheory.WittFrameOfDec.isWittFrame_of_hypDec D V V₀ _ d hA, hl.1,
    fun g => ?_, fun p β e k hk => ?_⟩, ?_, fun T hT g s => ?_⟩
  · obtain ⟨q, k, hk, rfl⟩ := hIw g
    exact ⟨q, onX d q, hsc q, k, hk, rfl⟩
  · obtain ⟨hp, rfl⟩ := hstab p β e
    have := iwAbs_mul_of_triv htriv ⟨p, hp⟩ hk
    rw [this]
    rfl
  · refine ⟨Set.range fun q : GlobalTheory.AutomorphicL2Unitary.Quot ((stab d).subgroupOf (GQ V)) => (q.out : GQ V), fun γ => ?_⟩
    refine ⟨(GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ).out, ⟨⟨_, rfl⟩, (hiff _).2 ((hmk _ _).1 (Quotient.out_eq _))⟩, ?_⟩
    rintro t' ⟨⟨q, rfl⟩, ht'⟩
    have e := (hmk q.out γ).2 ((hiff _).1 ht')
    have e2 : q = GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ := (Quotient.out_eq q).symm.trans e
    subst e2
    rfl
  · have hbij : Function.Bijective fun t : T => GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) (t.1 : GQ V) := by
      constructor
      · rintro ⟨t, ht⟩ ⟨t', ht'⟩ e
        have e' := (hmk _ _).1 e
        obtain ⟨u, -, hu⟩ := hT t'
        have h1 := hu t' ⟨ht', (hiff _).2 (by simp)⟩
        have h2 := hu t ⟨ht, (hiff _).2 e'⟩
        exact Subtype.ext (h2.trans h1.symm)
      · intro q
        induction q using Quotient.inductionOn with
        | h γ =>
          obtain ⟨t, ⟨ht, hs⟩, -⟩ := hT γ
          exact ⟨⟨t, ht⟩, (hmk _ _).2 ((hiff _).1 hs)⟩
    change cosetSum (stab d) (GQ V) (sphericalSectionIwasawa d l.K s) g = _
    rw [GlobalTheory.Eis.cosetSum_eq_tsum (GlobalTheory.AnisotropicResidueNonvanishing.witt_spherical_section_left_invariant_rational_parabolic d l hl hIw s) hbij g]
    refine tsum_congr fun t => ?_
    simp only [sphericalSectionIwasawa, npow, rhoH]
    congr 1
    push_cast
    ring

end GlobalTheory.ResidueDictionary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResidueEisenstein.FrameLeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem absE_det_of_scalesBy {k : ℕ} {X : Matrix (Fin n) (Fin k) E} {L : Matrix (Fin k) (Fin n) E} (hL : L * X = 1)
    {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X γ β) :
    absE F E (Matrix.GeneralLinearGroup.det β) = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F X = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hb : β.1 = (L * γ0.1.1 * X).map (inclR (F := F) (AF F)) := by
    have := congrArg (adMat F L * ·) e
    have h2 : adMat F L * (adMat F X * β.1) = β.1 := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
    rw [h2, hmat] at this
    rw [← this]
    simp only [adMat, Matrix.map_mul, Matrix.mul_assoc]
  set c : E := (L * γ0.1.1 * X).det with hc
  have hd : (Matrix.GeneralLinearGroup.det β).1 = inclR (F := F) (AF F) c := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hb, hc, RingHom.map_det]
    rfl
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := (Matrix.GeneralLinearGroup.det β).mul_inv
      rw [hd, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim (Matrix.GeneralLinearGroup.det β) 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = Matrix.GeneralLinearGroup.det β from
      Units.ext (by simp [hd])] at this

end GlobalTheory.ResidueEisenstein.FrameLeviFacts

namespace GlobalTheory.ResidueEisenstein


open GlobalTheory.StdPar GlobalTheory.ResLine.LeviFacts in
theorem frame_levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, ∀ u ∈ unipRad σ J X, m * u * m⁻¹ ∈ unipRad σ J X) ∧ (∀ g ∈ unipRad σ J X, g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} → g = 1) ∧ (∀ u ∈ unipRad σ J X, ScalesBy σ J X u 1) ∧ (∀ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ β, ScalesBy σ J X m β ∧ absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ (∀ γ ∈ ratPts σ J, ∀ β, ScalesBy σ J X γ β → absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} ∧ IsClosed ((GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hX : initCols X (Fin.last r) = X := rfl
  have hY : initCols Y (Fin.last r) = Y := rfl
  have hlev : ∀ m ∈ levi σ J X Y {Fin.last r}, m ∈ frameStab σ J X ⊤ ∧ m ∈ frameStab σ J Y ⊤ := fun m hm => by
    simp only [levi, Subgroup.mem_iInf] at hm
    exact hm _ (Finset.mem_singleton_self _)
  refine ⟨fun m hm u hu => conj_mem hW (Fin.last r) (hlev m hm).1 hu,
    fun g hg hm => eq_one h hJ hW (Fin.last r) hg (hlev g hm).2,
    fun u hu => (unipRad_fix hu).trans (by simp), fun m hm => ?_,
    fun γ hγ β e => FrameLeviFacts.absE_det_of_scalesBy (yx h hJ hW) hγ e, inf_le_left,
    (isClosed_levi {Fin.last r} h hJ hW).2⟩
  have h2 : m ∈ ⨅ k ∈ ({Fin.last r} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
  simp only [Subgroup.mem_iInf] at h2
  obtain ⟨B, hB, e⟩ := h2 _ (Finset.mem_singleton_self _)
  exact ⟨B, e, hB⟩

end GlobalTheory.ResidueEisenstein
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameRankLeAndExistsRationalSwap
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.Swap

open GlobalTheory.ResLine.Swap

theorem two_mul_le_and_exists_ratPts_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    2 * (r + 1) ≤ n ∧ ∃ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F Y = adMat F X ∧
      (matHom _ σ J w).1 * adMat F X = adMat F Y := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW
  classical
  have hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0 := hW.xx
  have hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 := hW.yy
  have hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 := hW.xy
  have hJ' := cT_eq_of_isHermND hJ
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have h := congrArg (Formalism.UG.cT (σ : E →+* E)) hxy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ', Formalism.UG.cT_one] at h
    simpa [Matrix.mul_assoc] using h
  refine ⟨?_, ?_⟩
  ·
    let f : ((Fin (r + 1) → E) × (Fin (r + 1) → E)) →ₗ[E] (Fin n → E) :=
      Y.mulVecLin.comp (LinearMap.fst E _ _) + X.mulVecLin.comp (LinearMap.snd E _ _)
    have hf : Function.Injective f := by
      intro p q hpq
      have hp : ∀ p : (Fin (r + 1) → E) × (Fin (r + 1) → E),
          (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ f p = p.1 ∧ (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ f p = p.2 := by
        intro p
        simp only [f, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
          Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, hxx, hyy, hxy, hyx,
          Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
        exact ⟨trivial, trivial⟩
      have h1 := hp p
      have h2 := hp q
      rw [hpq] at h1
      exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
    have h := LinearMap.finrank_le_finrank_of_injective hf
    simpa [Module.finrank_prod, two_mul] using h
  set u := X - Y with hu
  set v := Formalism.UG.cT (σ : E →+* E) u * J with hv
  have hvy : v * Y = 1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxy, hyy, sub_zero]
  have hvx : v * X = -1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxx, hyx, zero_sub]
  set w0 : Matrix (Fin n) (Fin n) E := 1 + u * v with hw0
  have hw0y : w0 * Y = X := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvy, Matrix.mul_one, hu]; abel
  have hw0x : w0 * X = Y := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvx, Matrix.mul_neg, Matrix.mul_one, hu]; abel
  have hw0u : w0 * u = -u := by
    rw [hu, Matrix.mul_sub, hw0y, hw0x]; abel
  have hsq : w0 * w0 = 1 := by
    conv_lhs => rw [show w0 * w0 = w0 * (1 + u * v) from rfl]
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hw0u, hw0, Matrix.neg_mul]; abel
  have hcw : Formalism.UG.cT (σ : E →+* E) w0 * J = J * w0 := by
    rw [hw0, cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, hv, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ',
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hunit : Formalism.UG.cT (σ : E →+* E) w0 * J * w0 = J := by
    rw [hcw, Matrix.mul_assoc, hsq, Matrix.mul_one]
  let U : GL (Fin n) E := ⟨w0, w0, hsq, hsq⟩
  have hU : U ∈ Formalism.UG.UJ (σ : E →+* E) J := hunit
  refine ⟨GlobalTheory.AdelicU.ratEmb σ J ⟨U, hU⟩, ?_, ?_, ?_⟩
  · rw [← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨_, rfl⟩
  · change w0.map (inclR (F := F) (AF F)) * adMat F Y = adMat F X
    simp only [adMat]
    rw [← Matrix.map_mul, hw0y]
  · change w0.map (inclR (F := F) (AF F)) * adMat F X = adMat F Y
    simp only [adMat]
    rw [← Matrix.map_mul, hw0x]

end GlobalTheory.ResidueEisenstein.Swap

end
end

