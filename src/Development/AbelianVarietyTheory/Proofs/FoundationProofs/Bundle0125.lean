module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePadicSpanOfPowPMulMem
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix

theorem zp_eq_algebraMap_zpAlg {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω] (m : ℤ_[p]) :
    zp Ω m = @algebraMap ℤ_[p] Ω _ _ (zpAlg (p := p) (Ω := Ω)) m := by
  show _ = algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) m)
  rw [zp, algebraMap_zp_eq, HahnSeries.C_apply]

theorem exists_fin_span_of_pow_mul :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω),
      (∀ t, IsInt (p := p) (E t) ∧ IsAlgZp (p := p) (E t)) → ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω),
        (∀ j, IsInt (p := p) (f j) ∧ IsAlgZp (p := p) (f j)) ∧
        ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt (p := p) y →
          (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t → ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  intro p _ Ω _ _ hc d E hE v
  letI := zpAlg (p := p) (Ω := Ω)
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : CharZero Ω := Basic.charZero_of_isClo hc
  have halg (x : Ω) : IsAlgZp (p := p) x ↔ IsAlgebraic ℤ_[p] x := by
    unfold IsAlgZp IsAlgebraic
    simp only [Polynomial.aeval_map_algebraMap]
  have hsm : ∀ (m : ℤ_[p]) (x : Ω), m • x = zp Ω m * x := fun m x => by
    rw [Algebra.smul_def, zp_eq_algebraMap_zpAlg]
  have hpv : ((p : Ω) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  set S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E) with hS
  let S' : Submodule ℤ_[p] Ω :=
    { carrier := {y | IsInt (p := p) y ∧ (p : Ω) ^ v * y ∈ S}
      add_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        exact ⟨IsIntegral.add hx1 hy1, by rw [mul_add]; exact S.add_mem hx2 hy2⟩
      zero_mem' := ⟨isIntegral_zero, by simp⟩
      smul_mem' := by
        rintro c x ⟨hx1, hx2⟩
        refine ⟨?_, ?_⟩
        · rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω]
          exact IsIntegral.mul isIntegral_algebraMap hx1
        · rw [mul_smul_comm]; exact S.smul_mem c hx2 }
  have hle : S' ≤ Submodule.span ℤ_[p] (Set.range (fun t => E t / (p : Ω) ^ v)) := by
    rintro y ⟨_, hy⟩
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hy
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, ?_⟩
    have : y = ((p : Ω) ^ v * y) / (p : Ω) ^ v := by field_simp
    rw [this, ← hc', Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_div_assoc]
  have hnoeth : IsNoetherian ℤ_[p] (Submodule.span ℤ_[p] (Set.range (fun t => E t / (p : Ω) ^ v))) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  have hfg : S'.FG := isNoetherian_submodule.1 hnoeth S' hle
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hfmem : ∀ j, f j ∈ S' := fun j => hf ▸ Submodule.subset_span ⟨j, rfl⟩
  have halgS : ∀ x ∈ S, IsAlgebraic ℤ_[p] x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact (halg _).1 (hE t).2
    | zero => exact isAlgebraic_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]; exact (isAlgebraic_algebraMap c).mul hx
  refine ⟨m, f, fun j => ⟨(hfmem j).1, ?_⟩, ?_⟩
  · rw [halg]
    have h1 : IsAlgebraic ℤ_[p] ((p : Ω) ^ v * f j) := halgS _ (hfmem j).2
    have h2 : IsAlgebraic ℤ_[p] (((p : Ω) ^ v)⁻¹) := by
      refine IsAlgebraic.inv ?_
      have : ((p : Ω) ^ v) = algebraMap ℤ_[p] Ω ((p : ℤ_[p]) ^ v) := by simp
      rw [this]; exact isAlgebraic_algebraMap _
    have := h2.mul h1
    rwa [← mul_assoc, inv_mul_cancel₀ hpv, one_mul] at this
  · intro l y hy hyl
    have hyS : y ∈ S' := by
      refine ⟨hy, ?_⟩
      rw [hyl]
      refine S.sum_mem fun t _ => ?_
      rw [← hsm]
      exact S.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩)
    rw [← hf] at hyS
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hyS
    exact ⟨μ, by rw [← hμ]; exact Finset.sum_congr rfl fun j _ => hsm _ _⟩

end GlobalTheory.GeoFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix

theorem exists_lau_approx (p : ℕ) [Fact p.Prime] (K : ℕ) (x : O0 p) :
    ∃ (a : Lau p) (c : O0 p), x = algebraMap (Lau p) (O0 p) a + (p : O0 p) ^ K * c := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (pI p) K x)
  have hker : RingHom.ker (AdicCompletion.evalₐ (pI p) K) = (pI p ^ K).map (algebraMap (Lau p) (O0 p)) := by
    ext y
    rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem (Lau p), ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    have hle : (pI p ^ K • ⊤ : Ideal (Lau p)) ≤ pI p ^ K := by intro z hz; simpa using hz
    rw [← AdicCompletion.factor_eval_eq_evalₐ (pI p) y hle]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (pI p) (Lau p) K y)
      rw [← hb] at h ⊢
      have : b ∈ pI p ^ K := Ideal.Quotient.eq_zero_iff_mem.mp h
      exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
    · intro h; rw [h, map_zero]
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈ RingHom.ker (AdicCompletion.evalₐ (pI p) K) := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ha, sub_self]
  rw [hker, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨a, c, by rw [mul_comm, hc]; ring⟩

theorem exists_cong_lau :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
      (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ →
      ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt (p := p) (e t)) →
      ∀ K : ℕ, ∃ a : Fin d → Lau p,
        Cong (p := p) K (∑ t, e t * ψ (b t))
          (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  intro p hp Ω _ _ T n ψ h d e b he K
  choose a c hac using fun t => exists_lau_approx p K (b t)
  have hq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (pow_pos hp.out.pos n) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hψ (x : O0 p) : IsIntegral (O0 p) (ψ x) := by
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [h.rng] at hx
    exact adjoin_le_integralClosure hq hx
  refine ⟨a, ∑ t, e t * ψ (c t), IsIntegral.sum _ fun t _ => IsIntegral.mul (he t) (hψ (c t)), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hac t, map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.GeoFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPadicCocycleOfCompatiblePolyFamily
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.CocLift

open MvPolynomial CongruenceSubgroup

theorem gamma_of_dvd {a b : ℕ} (h : a ∣ b) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma b) : δ ∈ Gamma a := by
  rw [Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have key : ∀ x : ℤ, ZMod.castHom h (ZMod a) (x : ZMod b) = (x : ZMod a) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, map_one]
  · rw [← key, h2, map_zero]
  · rw [← key, h3, map_zero]
  · rw [← key, h4, map_one]

theorem gamma_le_gam {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    δ ∈ Gam N l := by
  have h1 := Gamma_mem.mp (gamma_of_dvd hN hδ)
  have h2 := Gamma_mem.mp (gamma_of_dvd hl hδ)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]; exact ⟨h1.1, h1.2.2.2, h1.2.2.1⟩
  · rw [Gamma0_mem]; exact h2.2.2.1

theorem entries_of_gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    ∀ i j, (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := Gamma_mem.mp hδ
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem step (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w)
    (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) (hΦ : IsFam l w (Gam N l) Φ)
    (n : ℕ) (y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (hy : IsCoc w (Gam N l) y) (hyn : Near y (Φ n)) :
    ∃ y' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))), IsCoc w (Gam N l) y' ∧ Near y' (Φ (n + 1)) ∧
      ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (y' γ) = y γ := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨z', hz', hz'n⟩ := _root_.GlobalTheory.KZ.H3.exists_coc_near N l w hN hp hl2 hlN hw Φ hΦ (n + 1)
  set c := ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) with hc
  have L := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ n))
  have L' := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ (n + 1)))
  let r : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) := fun δ => MvPolynomial.map c (z' δ)
  have hr : IsCoc w (Gam N l) r := by
    refine ⟨fun γ hγ => (hz'.1 γ hγ).map c, fun γ hγ δ hδ => ?_⟩
    simp only [r]
    rw [hz'.2 γ hγ δ hδ, map_add (f := _), L'.2.2.2.2.1 _ c]
  have hnear : Near r y := by
    obtain ⟨M1, hM1, h1⟩ := hz'n
    obtain ⟨M2, hM2, h2⟩ := hΦ.2.2.2 n
    obtain ⟨M3, hM3, h3⟩ := hyn
    refine ⟨M1 * M2 * M3, by positivity, fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl |>.trans (Dvd.intro _ rfl)) hδ
    have d2 := gamma_of_dvd ((Dvd.intro_left _ rfl).trans (Dvd.intro _ rfl)) hδ
    have d3 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only [r]
    rw [h1 δ d1]
    exact (h2 δ d2).trans (h3 δ d3).symm
  obtain ⟨p, hph, hpγ⟩ := _root_.GlobalTheory.KZ.H3.adj_of_near N l w n hN hp hl2 hlN hw r y hr hy hnear
  let pt : MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))) :=
    ∑ m ∈ p.support, MvPolynomial.monomial m (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1)))
  have hpc : ∀ m, pt.coeff m = (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1))) := by
    intro m
    simp only [pt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff] at h
      rw [h, ZMod.val_zero, Nat.cast_zero]
  have hmap : MvPolynomial.map c pt = p := by
    ext m
    rw [MvPolynomial.coeff_map, hpc, map_natCast, ZMod.natCast_zmod_val]
  have hpth : pt.IsHomogeneous w := by
    intro m hm
    apply hph
    intro h0
    apply hm
    rw [hpc, h0, ZMod.val_zero, Nat.cast_zero]
  refine ⟨fun δ => z' δ - (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) pt - pt), ⟨fun γ hγ => ?_, fun γ hγ δ hδ => ?_⟩, ?_, ?_⟩
  · exact (hz'.1 γ hγ).sub ((L'.2.2.1 _ w pt hpth).sub hpth)
  · simp only
    rw [hz'.2 γ hγ δ hδ, Matrix.SpecialLinearGroup.coe_mul, L'.1, map_sub, map_sub]
    abel
  · obtain ⟨M1, hM1, h1⟩ := hz'n
    refine ⟨M1 * l ^ (n + 1), Nat.mul_pos hM1 (pow_pos hp.pos _), fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only
    rw [L'.2.2.2.2.2.1 _ 1 pt (entries_of_gamma d2), L'.2.1, sub_self, sub_zero, h1 δ d1]
  · intro γ hγ
    simp only
    rw [map_sub, map_sub, L'.2.2.2.2.1 _ c, hmap, ← hpγ γ hγ]
    simp only [r]
    abel

end GlobalTheory.KZ.H3.CocLift

namespace GlobalTheory.KZ.H3


open Classical in
theorem cocycle_lift_of_fam : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ →
    ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) ℤ_[l], IsCoc w (Gam N l) z ∧
      ∀ n, Near (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (z δ)) (Φ n) := by
  intro N l w _ hN hl2 hlN hw Φ hΦ
  have hp : l.Prime := Fact.out
  have lev := _root_.GlobalTheory.KZ.H3.exists_coc_near N l w hN hp hl2 hlN hw Φ hΦ
  choose F hF1 hF2 hF3 using CocLift.step N l w hN hl2 hlN hw Φ hΦ
  let seq : (n : ℕ) → {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) // IsCoc w (Gam N l) y ∧ Near y (Φ n)} :=
    fun n => Nat.rec (motive := fun n => {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) //
        IsCoc w (Gam N l) y ∧ Near y (Φ n)})
      ⟨(lev 0).choose, (lev 0).choose_spec⟩
      (fun n y => ⟨F n y.1 y.2.1 y.2.2, hF1 n y.1 y.2.1 y.2.2, hF2 n y.1 y.2.1 y.2.2⟩) n
  have hseq : ∀ n, ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      ((seq (n + 1)).1 γ) = (seq n).1 γ :=
    fun n => hF3 n (seq n).1 (seq n).2.1 (seq n).2.2
  let fam : SL(2, ℤ) → (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) :=
    fun δ n => if δ ∈ Gam N l then (seq n).1 δ else 0
  have hfam : ∀ δ ∈ Gam N l, ∀ n, fam δ n = (seq n).1 δ := fun δ hδ n => if_pos hδ
  have hhom : ∀ δ n, (fam δ n).IsHomogeneous w := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ]; exact (seq n).2.1.1 δ hδ
    · simp only [fam, if_neg hδ]; exact MvPolynomial.isHomogeneous_zero _ _ _
  have hcomp : ∀ δ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      (fam δ (n + 1)) = fam δ n := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ, hfam δ hδ]; exact hseq n δ hδ
    · simp only [fam, if_neg hδ, map_zero]
  choose q hq using fun δ => homogeneous_lift_compatible l w (fam δ) (hhom δ) (hcomp δ)
  have L := GlobalTheory.KZ.polySlash_laws ℤ_[l]
  refine ⟨q, ⟨fun γ _ => (hq γ).1, fun γ hγ δ hδ => ?_⟩, fun n => ?_⟩
  · refine ((hq (γ * δ)).2.2 _ fun n => ?_).symm
    have hγδ : γ * δ ∈ Gam N l := (Gam N l).mul_mem hγ hδ
    rw [map_add (f := _), L.2.2.2.2.1 _ _, (hq γ).2.1 n, (hq δ).2.1 n, hfam γ hγ, hfam δ hδ, hfam _ hγδ,
      (seq n).2.1.2 γ hγ δ hδ]
  · obtain ⟨M, hM, hMδ⟩ := (seq n).2.2
    refine ⟨M * (N * l), Nat.mul_pos hM (Nat.mul_pos hN hp.pos), fun δ hδ => ?_⟩
    have d1 := CocLift.gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := CocLift.gamma_le_gam (N := N) (l := l) ((Dvd.intro _ rfl).trans (Dvd.intro_left _ rfl))
      ((Dvd.intro_left _ rfl).trans (Dvd.intro_left _ rfl)) hδ
    simp only
    rw [(hq δ).2.1 n, hfam δ d2]
    exact hMδ δ d1

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionQDerivationModIntegralClosure
section
noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.QDer

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem isDerOn_mono {B B' : Subalgebra A S} {D : S → M} (h : IsDerOn B D) (hle : B' ≤ B) :
    IsDerOn B' D :=
  ⟨fun x hx y hy => h.add x (hle hx) y (hle hy), fun x hx y hy => h.mul x (hle hx) y (hle hy),
    h.alg⟩

theorem isDerOn_sub {B : Subalgebra A S} {D₁ D₂ : S → M} (h₁ : IsDerOn B D₁) (h₂ : IsDerOn B D₂) :
    IsDerOn B (fun x => D₁ x - D₂ x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    simp only [h₁.add x hx y hy, h₂.add x hx y hy]
    abel
  · intro x hx y hy
    simp only [h₁.mul x hx y hy, h₂.mul x hx y hy, smul_sub]
    abel
  · intro a
    simp [h₁.alg a, h₂.alg a]

theorem isDerOn_pow {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    {n : ℕ} (hn : 1 ≤ n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, h.mul _ (pow_mem hx _) _ hx, ih (by omega), smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

end General

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by simp [zS, T.ζpow])

theorem qS_succ_pow (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by simp [qS, T.qpow])

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zS_succ_pow]; exact pow_mem (zS_mem_levelAlg T _) _
  · rw [← qS_succ_pow]; exact pow_mem (qS_mem_levelAlg T _) _

theorem towerAlg_le_iSup (T : Tower p Ω) : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (zS_mem_levelAlg T m))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (qS_mem_levelAlg T m))

theorem exists_level (hC : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) :
    ∃ D : integralClosure (O0 p) Ω → Frac p Ω, IsDerOn (levelAlg T n) D ∧ D (zS T n) = 0 ∧
      D (qS T n) = Submodule.Quotient.mk (T.qq n / (p : Ω) ^ n) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine _root_.GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg p Ω hC T n hn (Frac p Ω) 0 _ (smul_zero _) ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p), ?_⟩
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rw [Algebra.linearMap_apply, ← IsScalarTower.algebraMap_apply, Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) ^ n * qS T n ^ (p ^ n - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) ^ n * T.qq n ^ (p ^ n - 1) := by
    simp [qS]
  rw [key, ← GlobalTheory.AlmostEt.qq_pow T n]
  field_simp
  rw [pow_sub_one_mul hpn]

theorem smul_mk_eq (hC : IsClo p Ω) (T : Tower p Ω) (m : ℕ) :
    ((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1)) •
        (Submodule.Quotient.mk (T.qq (m + 1) / (p : Ω) ^ (m + 1)) : Frac p Ω) =
      Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpn : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) * T.qq (m + 1) ^ (p - 1) := by
    simp [qS]
  rw [key, ← T.qpow m, ← pow_sub_one_mul hpn (T.qq (m + 1)), pow_succ]
  field_simp

theorem exists_qDer (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (hC : IsClo p Ω) (T : Tower p Ω) :
    ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧
      ∀ m : ℕ, D (zS T m) = 0 ∧ D (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  choose Dl hDl hz hq using fun m : ℕ => exists_level hC T (m + 1) (by omega)

  have hz' : ∀ m, Dl m (zS T m) = 0 := fun m => by
    rw [← zS_succ_pow, isDerOn_pow (hDl m) (zS_mem_levelAlg T _) hp1, hz, smul_zero]
  have hq' : ∀ m, Dl m (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := fun m => by
    rw [← qS_succ_pow, isDerOn_pow (hDl m) (qS_mem_levelAlg T _) hp1, hq, smul_mk_eq hC T m]

  have hcomp : ∀ m, ∀ x ∈ levelAlg T (m + 1), Dl (m + 1) x = Dl m x := by
    intro m x hx
    have hE := isDerOn_sub (isDerOn_mono (hDl (m + 1)) (levelAlg_le_succ T (m + 1))) (hDl m)
    have hspan := _root_.GlobalTheory.AlmostEt.derOn_adjoin_mem_span (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω) {zS T (m + 1), qS T (m + 1)}
      _ hE x hx
    have h1 : Dl (m + 1) (zS T (m + 1)) - Dl m (zS T (m + 1)) = 0 := by rw [hz' (m + 1), hz m, sub_zero]
    have h2 : Dl (m + 1) (qS T (m + 1)) - Dl m (qS T (m + 1)) = 0 := by rw [hq' (m + 1), hq m, sub_self]
    simp only [Set.image_insert_eq, Set.image_singleton, h1, h2, Set.insert_eq_of_mem,
      Set.mem_singleton_iff, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hspan
    exact sub_eq_zero.1 hspan
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D, hD, hag⟩ := GlobalTheory.T.exists_derivationOn_iSup_of_compatible (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono Dl hDl hcomp
  refine ⟨D, isDerOn_mono hD (towerAlg_le_iSup T), fun m => ⟨?_, ?_⟩⟩
  · rw [hag m _ (levelAlg_le_succ T m (zS_mem_levelAlg T m)), hz']
  · rw [hag m _ (levelAlg_le_succ T m (qS_mem_levelAlg T m)), hq']

end GlobalTheory.AlmostEt.QDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem jT_invariant (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ :=
  ReciprocityTheory.ChartRestriction.L1.jT_smul γ τ

theorem DD_mul_jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD τ * jT (γ • τ) = E₄ τ ^ 3 := by
  rw [jT_invariant, jT, ReciprocityTheory.ChartRestriction.L1.AA, mul_div_cancel₀ _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)]

theorem jT_level_one : ∀ E : Subring ℂ, Lv E 1 1 jT ∧ ∀ (γ : SL(2, ℤ)) (τ : ℍ), jT (γ • τ) = jT τ := by
  intro E
  refine ⟨⟨fun γ _ τ => jT_invariant γ τ, fun γ => ?_⟩, jT_invariant⟩
  have hE4 : QAll (· ∈ E) 1 ⇑E₄ := ((eis_q 1 one_pos _ (Or.inl rfl)).2.1) E
  have h3 : QAll (· ∈ E) 1 fun τ => E₄ τ ^ 3 := (QAllSubring.ring_closed E 1 one_pos).2.2.2.2.1 _ 3 hE4
  have hfun : (fun τ => DD τ ^ 1 * jT (γ • τ)) = fun τ => E₄ τ ^ 3 := by
    funext τ; rw [pow_one, DD_mul_jT_smul]
  rw [hfun]; exact h3

end GlobalTheory.FN
end

