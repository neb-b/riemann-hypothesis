module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0034
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0044
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CompleteMax
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

private theorem isPrecomplete_of_module_finite {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [hR : IsPrecomplete I R] [Module.Finite R M] : IsPrecomplete I M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨fun g hg => ?_⟩
  have hd : ∀ k, g (k + 1) - g k ∈ I ^ k • Submodule.span R (Set.range s) := by
    intro k
    rw [hs]
    have h := SModEq.sub_mem.1 (hg (Nat.le_succ k))
    have h2 := neg_mem h
    rwa [neg_sub] at h2
  choose A hA hAs using fun k =>
    (Submodule.mem_ideal_smul_span_iff_exists_sum (I ^ k) s (g (k + 1) - g k)).1 (hd k)
  have hc : ∀ i : Fin n, ∀ {a b : ℕ}, a ≤ b →
      (∑ k ∈ Finset.range a, A k i) ≡ (∑ k ∈ Finset.range b, A k i) [SMOD (I ^ a • ⊤ : Submodule R R)] := by
    intro i a b hab
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Finset.sum_range_add_sum_Ico _ hab,
      sub_add_cancel_left]
    refine neg_mem (sum_mem fun k hk => ?_)
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (hA k i)
  choose C hC using fun i : Fin n => hR.prec' _ (hc i)
  refine ⟨g 0 + ∑ i, C i • s i, fun K => ?_⟩
  rw [SModEq.sub_mem]
  have hgK : g K = g 0 + ∑ i, (∑ k ∈ Finset.range K, A k i) • s i := by
    have h1 : ∑ k ∈ Finset.range K, (g (k + 1) - g k) = g K - g 0 := Finset.sum_range_sub g K
    have h2 : ∑ k ∈ Finset.range K, (g (k + 1) - g k) =
        ∑ i, (∑ k ∈ Finset.range K, A k i) • s i := by
      simp only [← hAs, Finsupp.sum_fintype, zero_smul, implies_true, Finset.sum_smul]
      exact Finset.sum_comm
    rw [← h2, h1]
    abel
  rw [hgK]
  have hsplit : g 0 + ∑ i, (∑ k ∈ Finset.range K, A k i) • s i - (g 0 + ∑ i, C i • s i) =
      ∑ i, ((∑ k ∈ Finset.range K, A k i) - C i) • s i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  refine sum_mem fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  have h := SModEq.sub_mem.1 (hC i K)
  rwa [Ideal.smul_eq_mul, Ideal.mul_top] at h


set_option maxHeartbeats 800000 in
theorem complete_max {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  classical
  haveI hmax : (IsLocalRing.maximalIdeal ↥(OL LL)).IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  have hcomap : (IsLocalRing.maximalIdeal ↥(OL LL)).comap (algebraMap ℤ_[l] ↥(OL LL)) =
      IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) _)
  have hl : ((l : ℤ_[l])) ∈ IsLocalRing.maximalIdeal ℤ_[l] :=
    by
    first
      | (rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _)
      | exact (IsLocalRing.mem_maximalIdeal _).2 (PadicInt.mem_nonunits.2 PadicInt.norm_p_lt_one)
  have hl0 : algebraMap ℤ_[l] ↥(OL LL) (l : ℤ_[l]) ≠ 0 := by
    rw [map_natCast]
    intro h
    have h2 := congrArg (fun x : ↥(OL LL) => ((x : ↥LL.1) : Om l)) h
    simp at h2
    exact (Fact.out : l.Prime).ne_zero h2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hm : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ} := by
    first
      | exact hϖ.maximalIdeal_eq
      | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have key1 : ∀ (k : ℕ) (x : ↥(OL LL)), x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ ((e + 1) * k) →
      x ∈ ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL)) := by
    intro k x hx
    have hle : e * k ≤ (e + 1) * k := by rw [add_mul, one_mul]; exact Nat.le_add_right _ _
    have hx' : x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ (e * k) := Ideal.pow_le_pow_right hle hx
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx'
    obtain ⟨b, rfl⟩ := hx'
    have hϖe : ϖ ^ e = ((u⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) * algebraMap ℤ_[l] ↥(OL LL) (l : ℤ_[l]) := by
      rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    have hb : b * ϖ ^ (e * k) =
        ((l : ℤ_[l]) ^ k) • (b * ((u⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) ^ k) := by
      rw [Algebra.smul_def, map_pow, pow_mul, hϖe, mul_pow]
      ring
    rw [hb]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl k) Submodule.mem_top
  have key2 : ∀ (k : ℕ) (x : ↥(OL LL)),
      x ∈ ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL)) →
      x ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k := by
    intro k x hx
    have hmap : (IsLocalRing.maximalIdeal ℤ_[l] ^ k).map (algebraMap ℤ_[l] ↥(OL LL)) ≤
        (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hcomap.ge) k
    have hsub : ((IsLocalRing.maximalIdeal ℤ_[l]) ^ k • ⊤ : Submodule ℤ_[l] ↥(OL LL)) ≤
        ((IsLocalRing.maximalIdeal ↥(OL LL)) ^ k).restrictScalars ℤ_[l] := by
      rw [Submodule.smul_le]
      intro r hr y _
      rw [Submodule.restrictScalars_mem, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (hmap (Ideal.mem_map_of_mem _ hr))
    exact hsub hx
  haveI hH : IsHausdorff (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
    refine ⟨fun x hx => ?_⟩
    have hI := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal ↥(OL LL))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have hx' : x ∈ ⨅ i : ℕ, (IsLocalRing.maximalIdeal ↥(OL LL)) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      have h := SModEq.sub_mem.1 (hx i)
      rwa [sub_zero, Ideal.smul_eq_mul, Ideal.mul_top] at h
    rw [hI] at hx'
    exact (Submodule.mem_bot _).1 hx'
  haveI hP : IsPrecomplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
    refine ⟨fun f hf => ?_⟩
    have hcau : ∀ {a b : ℕ}, a ≤ b → f a - f b ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ a := by
      intro a b hab
      have h := SModEq.sub_mem.1 (hf hab)
      rwa [Ideal.smul_eq_mul, Ideal.mul_top] at h
    have hSp : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL) := isPrecomplete_of_module_finite _
    obtain ⟨L, hL⟩ := hSp.prec' (fun k => f ((e + 1) * k)) (fun {a b} hab => by
      rw [SModEq.sub_mem]
      exact key1 a _ (hcau (Nat.mul_le_mul (le_refl _) hab)))
    refine ⟨L, fun k => ?_⟩
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    have hk : k ≤ (e + 1) * k := by rw [add_mul, one_mul]; exact Nat.le_add_left k (e * k)
    have h1 := hcau hk
    have h2 : f ((e + 1) * k) - L ∈ (IsLocalRing.maximalIdeal ↥(OL LL)) ^ k :=
      key2 k _ (SModEq.sub_mem.1 (hL k))
    have h3 := Ideal.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at h3
  exact IsAdicComplete.mk

theorem lemmaDN0_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have hT := h1 l K 1 LL hg
  obtain ⟨hE, hC, hQ⟩ := h11 l K LL
  have := complete_max LL
  have h9D : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l' _ K' s' LL' h' => (h1 l' K' s' LL' h').2.2.2.2.2.2.2.2.1
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F h9D
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lemmaDN0_of_admits _ hE hC hQ (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hg) hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.2.2.2.1 ?_ ?_
  · intro hA hl11 c ζ hζ
    have hK : K.1 ≤ MaximalUnramifiedExtension l := by
      intro x hx
      obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
      have hyx : ((y : ↥(K0 K)) : Om l) = x := congrArg (fun z : ↥K.1 => (z : Om l)) hy
      rw [← hyx]
      exact y.2.2
    have hAD : CaseA K LL := ⟨hK, by rw [← hp]; exact hA.2.2, hg⟩
    have h5l : 5 ≤ l := by rw [← hp]; omega
    obtain ⟨τ, hτ⟩ := hpt l K LL hAD h5l c ζ (by rwa [hp] at hζ)
    refine ⟨τ, ?_, hτ⟩
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    apply AlgHom.ext
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    show τ (algebraMap ↥(K0 K) ↥K.1 x) = _
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  · rw [hp]
    exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.GoodOfLpow
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

def Good (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (z : W.DD T) : Prop :=
  InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z) ∧
  ∀ (k : ℕ) (f : Fin d → W.EE),
    RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k • z) f →
    (∀ m, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f m)) →
    ∃ κ : ℕ, SecIn W (c' + (e : ZMod n)) e (condNN W T (c' + (e : ZMod n)) e b) fun m => lE W κ * f m

theorem lE_mul (s t : ℕ) (y : W.EE) : lE W s * (lE W t * y) = lE W (s + t) * y := by
  unfold lE; rw [pow_add]; ring

theorem lE_eq (t : ℕ) : lE W t = algebraMap (LetA O n) W.EE (lA W ^ t) := by
  unfold lE lA; rw [map_pow, map_natCast]

theorem repVV_lA (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (z : W.DD T) (f : Fin d → W.EE) (s t : ℕ)
    (h : RepVV W T c' e M Λ b sol (lA W ^ t • z) f) :
    RepVV W T c' e M Λ b sol (lA W ^ (t + s) • z) (fun m => lE W s * f m) := by
  have := repVV_smul W T c' e M Λ b sol _ f (lA_mem W s) h
  rwa [lA_smul_smul, ← lE_eq] at this

theorem good_of_sec (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z : W.DD T)
    (hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z)) (k₀ : ℕ) (f₀ : Fin d → W.EE)
    (hrep₀ : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k₀ • z) f₀)
    (hfr₀ : ∀ m, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f₀ m)) (κ₀ : ℕ)
    (hS₀ : SecIn W (c' + (e : ZMod n)) e (condNN W T (c' + (e : ZMod n)) e b) fun m => lE W κ₀ * f₀ m) :
    Good A c' e T b sol z := by
  refine ⟨hz, fun k f hrep hfr => ?_⟩
  have r1 := repVV_lA T c' e _ _ b sol z f k₀ k hrep
  have r2 := repVV_lA T c' e _ _ b sol z f₀ k k₀ hrep₀
  rw [add_comm k₀ k] at r2
  obtain ⟨t, ht⟩ := sec_unique W C.hinj C.hV C.hO2 C.hs C.hR C.hp0 C.h5 C.hTr C.hH C.hCA C.h5p T
    (C.h3 T hT.1) (C.hmod T hT.1) A hA c' hc' hT b sol hb e _ _ _ r1 r2
    (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr m) k₀) (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₀ m) k)
  have hD := secIn_piLam W C.hR.1 A (c' + (e : ZMod n)) e T b
    (fun c₀ s hs => dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 e s hs c₀) _ ht
  have hS := secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hD κ₀) (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₀ (t + k))
  refine ⟨κ₀ + (t + k₀), ?_⟩
  convert hS using 1
  rw [show κ₀ + (t + k₀) = κ₀ + (t + k₀) from rfl]
  unfold lE
  funext m
  simp only [Pi.add_apply]
  ring

theorem good_of_lpow (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e K : ℕ) (z : W.DD T)
    (hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z)) (h : Good A c' e T b sol (lA W ^ K • z)) :
    Good A c' e T b sol z := by
  obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _
    h.1
  obtain ⟨κ', hS⟩ := h.2 κ f hrep hfr
  rw [lA_smul_smul] at hrep
  exact good_of_sec C A hA c' hc' T hT b sol hb e z hz _ f hrep hfr κ' hS

theorem good_add (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z₁ z₂ : W.DD T)
    (h₁ : Good A c' e T b sol z₁) (h₂ : Good A c' e T b sol z₂) : Good A c' e T b sol (z₁ + z₂) := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (z₁ + z₂)) := by
    rw [smul_add]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _ h₁.1 h₂.1
  obtain ⟨κ₁, f₁, hrep₁, hfr₁⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol
    hb _ h₁.1
  obtain ⟨κ₂, f₂, hrep₂, hfr₂⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol
    hb _ h₂.1
  obtain ⟨κ'₁, hS₁⟩ := h₁.2 κ₁ f₁ hrep₁ hfr₁
  obtain ⟨κ'₂, hS₂⟩ := h₂.2 κ₂ f₂ hrep₂ hfr₂
  have r1 := repVV_lA T c' e _ _ b sol z₁ f₁ κ₂ κ₁ hrep₁
  have r2 := repVV_lA T c' e _ _ b sol z₂ f₂ κ₁ κ₂ hrep₂
  rw [add_comm κ₂ κ₁] at r2
  have r := repVV_add W C.hinj T c' e _ _ b sol _ _ _ _ r1 r2
  rw [← smul_add] at r
  refine good_of_sec C A hA c' hc' T hT b sol hb e _ hz _ _ r
    (fun m => inFr_add W (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₁ m) κ₂) (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₂ m) κ₁))
    (κ'₁ + κ'₂) ?_
  have hS := secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₁ (κ'₂ + κ₂))
    (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₂ (κ'₁ + κ₁))
  convert hS using 1
  unfold lE
  funext m
  simp only [Pi.add_apply]
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

