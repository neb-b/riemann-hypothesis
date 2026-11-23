module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0184
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DependentOfCardLe
section
open GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

namespace GlobalTheory.Cyc.CocycleCount

theorem dependent_of_card_le : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (ψ : G →* ℤ_[l]ˣ) (C n : ℕ), (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ∧ Nat.card (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ≤ C * l ^ (r * n)) → ∀ z : Fin (n + 1) → G → ℚ_[l], (∀ i, Continuous (z i)) → (∀ i g h, z i (g * h) = z i g + ((ψ g : ℤ_[l]) : ℚ_[l]) * z i h) → ∃ c : Fin (n + 1) → ℚ_[l], c ≠ 0 ∧ ∀ g, ∑ i, c i * z i g = 0 := by
  intro l _ G _ _ _ _ ψ C n hC z hz hcoc
  have hl : l.Prime := Fact.out
  by_contra hne
  push Not at hne

  obtain ⟨B, hB⟩ := (isCompact_range (continuous_pi hz : Continuous fun g i => z i g)).isBounded.exists_norm_le
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt ℚ_[l] (r := (max B 1)⁻¹) (by positivity)
  have ha1 : ∀ i g, ‖a * z i g‖ ≤ 1 := fun i g => by
    rw [norm_mul]
    have h1 : ‖z i g‖ ≤ max B 1 :=
      ((norm_le_pi_norm (fun i => z i g) i).trans (hB _ ⟨g, rfl⟩)).trans (le_max_left _ _)
    calc ‖a‖ * ‖z i g‖ ≤ (max B 1)⁻¹ * max B 1 := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have ha' : a ≠ 0 := norm_pos_iff.1 ha0
  let w : Fin (n + 1) → G → ℤ_[l] := fun i g => ⟨a * z i g, ha1 i g⟩
  have hw : ∀ i, Continuous (w i) := fun i => (continuous_const.mul (hz i)).subtype_mk _
  have hwc : ∀ i g h, w i (g * h) = w i g + (ψ g : ℤ_[l]) * w i h := fun i g h => Subtype.ext (by
    change a * z i (g * h) = a * z i g + ((ψ g : ℤ_[l]) : ℚ_[l]) * (a * z i h)
    rw [hcoc]; ring)
  let W : Fin (n + 1) → C(G, ℚ_[l]) := fun i => ⟨fun g => a * z i g, continuous_const.mul (hz i)⟩
  let L : (Fin (n + 1) → ℚ_[l]) →ₗ[ℚ_[l]] C(G, ℚ_[l]) := Fintype.linearCombination ℚ_[l] W
  have hL : ∀ c g, L c g = ∑ i, c i * (a * z i g) := fun c g => by
    simp [L, W, Fintype.linearCombination_apply, ContinuousMap.sum_apply]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    obtain ⟨g, hg⟩ := hne c h0
    apply hg
    have h1 := hL c g
    rw [hc, ContinuousMap.zero_apply] at h1
    apply mul_left_cancel₀ ha'
    rw [mul_zero, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  obtain ⟨v, hv⟩ := pow_unbounded_of_one_lt (K : ℝ) hl1
  have key : ∀ r : ℕ, 0 < r → l ^ r ≤ C * l ^ (v * n) := by
    intro r hr
    obtain ⟨hfin, hcard⟩ := hC (r + v) (by omega)
    let F : (Fin (n + 1) → Fin (l ^ r)) →
        ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ (r + v))) := fun c =>
      ⟨fun g => PadicInt.toZModPow (r + v) (∑ i, ((c i : ℕ) : ℤ_[l]) * w i g),
        (continuous_toZModPow _).comp
          (continuous_finsetSum _ fun i _ => continuous_const.mul (hw i)), fun g h => by
        rw [ReciprocityTheory.Gal.charRep_apply, redChar_apply, ← map_mul, ← map_add (f := _), Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine congrArg (PadicInt.toZModPow (r + v)) ?_
        exact Finset.sum_congr rfl fun i _ => by rw [hwc]; ring⟩
    have hF : Function.Injective F := by
      intro c c' h
      let d : Fin (n + 1) → ℚ_[l] := fun i => ((((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) : ℤ) : ℚ_[l])
      have h1 : ‖L d‖ ≤ (l : ℝ) ^ (-((r + v : ℕ) : ℤ)) := by
        rw [ContinuousMap.norm_le _ (by positivity)]
        intro g
        have h2 : PadicInt.toZModPow (r + v) (∑ i, ((c i : ℕ) : ℤ_[l]) * w i g) =
            PadicInt.toZModPow (r + v) (∑ i, ((c' i : ℕ) : ℤ_[l]) * w i g) :=
          congrFun (congrArg Subtype.val h) g
        rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
          ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def] at h2
        refine le_of_eq_of_le (congrArg norm ?_) h2
        rw [hL, ← Finset.sum_sub_distrib]
        refine Eq.trans ?_ (map_sum (PadicInt.Coe.ringHom (p := l)) _ _).symm
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = ((((c i : ℕ) : ℤ_[l]) * w i g - ((c' i : ℕ) : ℤ_[l]) * w i g : ℤ_[l]) : ℚ_[l])
        have hwv : ((w i g : ℤ_[l]) : ℚ_[l]) = a * z i g := rfl
        rw [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_natCast,
          PadicInt.coe_natCast, hwv]
        simp only [d, Int.cast_sub, Int.cast_natCast]
        ring
      have h3 : ‖d‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
        have h4 := ZeroHomClass.bound_of_antilipschitz L hK d
        calc ‖d‖ ≤ K * ‖L d‖ := h4
          _ ≤ (l : ℝ) ^ v * (l : ℝ) ^ (-((r + v : ℕ) : ℤ)) := by gcongr
          _ = _ := by
            rw [← zpow_natCast, ← zpow_add₀ (by positivity)]
            congr 1
            push_cast; ring
      funext i
      have h5 := (Padic.norm_int_le_pow_iff_dvd (p := l) _ r).1 ((norm_le_pi_norm d i).trans h3)
      apply Fin.ext
      have h6 : ((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd h5
        have e1 : ((c i : ℕ) : ℤ) < (l : ℤ) ^ r := by exact_mod_cast (c i).2
        have e2 : ((c' i : ℕ) : ℤ) < (l : ℤ) ^ r := by exact_mod_cast (c' i).2
        rw [abs_lt]
        constructor <;> omega
      omega
    have h7 := (Nat.card_le_card_of_injective F hF).trans hcard
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin] at h7
    have h8 : l ^ r * l ^ (r * n) ≤ (C * l ^ (v * n)) * l ^ (r * n) := by
      calc l ^ r * l ^ (r * n) = (l ^ r) ^ (n + 1) := by ring
        _ ≤ _ := h7
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h8 (pow_pos hl.pos _)
  have h9 := key (C * l ^ (v * n) + 1) (Nat.succ_pos _)
  have h10 : C * l ^ (v * n) + 1 < l ^ (C * l ^ (v * n) + 1) := Nat.lt_pow_self hl.one_lt
  omega

end GlobalTheory.Cyc.CocycleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfLocallyConstant
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.UnramifiedClasses

theorem eq_zero_of_locallyConstant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type} [AddCommGroup A] (I : Subgroup G) (φ : G)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤) (c : G → A)
    (hlc : IsLocallyConstant c) (hc : ∀ g h, c (g * h) = c g + c h) (hφ : c φ = 0)
    (hI : ∀ g ∈ I, c g = 0) (g : G) : c g = 0 := by
  have h1 : c 1 = 0 := by
    have := hc 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  let H : Subgroup G :=
    { carrier := {g | c g = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hc, ha, hb, add_zero]
      one_mem' := h1
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have := hc a a⁻¹
        rw [mul_inv_cancel, h1, ha, zero_add] at this
        exact this.symm }
  have hle : Subgroup.zpowers φ ⊔ I ≤ H :=
    sup_le ((Subgroup.zpowers_le (G := G)).mpr hφ) (fun g hg => hI g hg)
  have hcl : (Subgroup.zpowers φ ⊔ I).topologicalClosure ≤ H :=
    Subgroup.topologicalClosure_minimal _ hle (hlc.isClosed_fiber 0)
  rw [hgen] at hcl
  exact hcl (Subgroup.mem_top g)

theorem isLocallyConstant_mkQ {X : Type} [TopologicalSpace X] {O V : Type} [CommRing O]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [ContinuousAdd V] (T : Submodule O V)
    (hT : IsOpen (T : Set V)) (f : X → V) (hf : Continuous f) :
    IsLocallyConstant (fun x => T.mkQ (f x)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => f y + (-f x)) ⁻¹' (T : Set V),
    hT.preimage (hf.add continuous_const), by simp, fun y hy => ?_⟩
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, sub_eq_add_neg]
  exact hy

theorem exists_not_mem_range {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL] :
    ∃ y : LL, y ∉ Set.range (algebraMap O LL) := by
  by_contra h
  push Not at h
  apply IsDiscreteValuationRing.not_isField O
  exact (RingEquiv.ofBijective (algebraMap O LL)
    ⟨IsFractionRing.injective O LL, h⟩).toMulEquiv.isField (Field.toIsField LL)

theorem HfD_eq_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [IsTopologicalGroup G] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsTopologicalRing LL], GoodO (Qp := Qp) LL O → ∀ (T : LocLat G Qp LL O), Module.finrank LL T.V = 1 → (∀ g x, T.ρ g x = x) → Module.finrank LL (FiniteCohomology PD T.ρ) = 1 → ∀ (I : Subgroup G) (φ : G), (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤ → ∀ δ : G → LL, δ ∈ finiteCocycles PD (1 : Representation LL G LL) → (∀ g ∈ I, δ g = 0) → δ ≠ 0 → HfD PD T.L ≠ ⊥ ∧ ∀ c : G → T.V ⧸ T.L.T, c ∈ HfD PD T.L ↔ (c ∈ divisibleCocycles T.L ∧ ∃ x, ∀ g ∈ I, c g = actD T.L g x - x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ _ LL _ _ _ O _ _ _ hO T hV hρ
    hH I φ hgen δ hδ hδI hδ0
  have hopen := GlobalTheory.Cyc.locLat_isOpen hO T
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L hV
  obtain ⟨y₀, hy₀⟩ := exists_not_mem_range (O := O) (LL := LL)
  obtain ⟨⟨hδc, hδh⟩, x₀, hx₀⟩ := hδ
  have hδadd : ∀ g h, δ (g * h) = δ g + δ h := fun g h => by simpa using hδh g h
  have hact : ∀ g (x : T.V ⧸ T.L.T), actD T.L g x = x := by
    intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg (Submodule.Quotient.mk (p := T.L.T)) (hρ g x)
  have hBD : BD T.L = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [hact]
  have hB1 : B1 T.ρ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob, hρ]
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hc₀c : Continuous fun g => e (δ g) := by
    have : (fun g => e (δ g)) = fun g => δ g • e 1 := by
      funext g
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [this]
    exact hδc.smul continuous_const
  have hc₀ : (fun g => e (δ g)) ∈ finiteCocycles PD T.ρ := by
    let m := AlgebraTensorModule.map (e : LL →ₗ[LL] T.V) (LinearMap.id : B →ₗ[Qp] B)
    have hm : ∀ g y, m (actVB PD (1 : Representation LL G LL) g y) = actVB PD T.ρ g (m y) := by
      intro g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m, actVB, hρ]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    refine ⟨⟨hc₀c, fun g h => by simp only [hδadd, map_add (f := _), hρ]⟩, m x₀, fun g => ?_⟩
    have := congrArg m (hx₀ g)
    simp only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this
    rw [← hm]
    exact this
  obtain ⟨g₀, hg₀⟩ : ∃ g, δ g ≠ 0 := Function.ne_iff.mp hδ0
  have hdim : Module.finrank LL ↥(finiteCocycles PD T.ρ) = 1 := by
    rw [← hH]
    refine (Submodule.quotEquivOfEqBot _ ?_).finrank_eq.symm
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  have hspan : ∀ z ∈ finiteCocycles PD T.ρ, ∃ a : LL, ∀ g, z g = e (a * δ g) := by
    intro z hz
    have hne : (⟨_, hc₀⟩ : ↥(finiteCocycles PD T.ρ)) ≠ 0 := by
      intro h
      have := congrFun (congrArg Subtype.val h) g₀
      exact hg₀ (by simpa using this)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hz⟩
    refine ⟨a, fun g => ?_⟩
    have := congrFun (congrArg Subtype.val ha) g
    rw [← smul_eq_mul, map_smul]
    exact this.symm

  let r : LL → G → T.V ⧸ T.L.T := fun a g => T.L.T.mkQ (e (a * δ g))
  have hHf : ∀ c, c ∈ HfD PD T.L ↔ ∃ a, c = r a := by
    intro c
    unfold HfD
    rw [hBD, sup_bot_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha⟩ := hspan z hz
      exact ⟨a, funext fun g => by simp [r, ha]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨a • fun g => e (δ g), (finiteCocycles PD T.ρ).smul_mem a hc₀, ?_⟩
      funext g
      simp [r, ← map_smul]
  have hrlc : ∀ a, IsLocallyConstant (r a) := fun a => by
    refine isLocallyConstant_mkQ T.L.T hopen (fun g => e (a * δ g)) ?_
    have : (fun g => e (a * δ g)) = fun g => a • e (δ g) := by
      funext g
      rw [← map_smul, smul_eq_mul]
    rw [this]
    exact hc₀c.const_smul a
  have hradd : ∀ a g h, r a (g * h) = r a g + r a h := fun a g h => by
    simp only [r, hδadd, mul_add, map_add (f := _)]
  have hrI : ∀ a, ∀ g ∈ I, r a g = 0 := fun a g hg => by
    simp only [r, hδI g hg, mul_zero, map_zero]
  have hr₀ : r (y₀ / δ g₀) g₀ ≠ 0 := by
    intro h
    simp only [r, div_mul_cancel₀ _ hg₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact hy₀ ((he _).mp h)
  have hφ : δ φ ≠ 0 := by
    intro h
    exact hr₀ (eq_zero_of_locallyConstant I φ hgen _ (hrlc _) (hradd _)
      (by simp only [r, h, mul_zero, map_zero]) (hrI _) g₀)
  refine ⟨fun h => ?_, fun c => ?_⟩
  · have : r (y₀ / δ g₀) ∈ HfD PD T.L := (hHf _).mpr ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hr₀ (congrFun this g₀)
  · rw [hHf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨hrlc a, fun g h => by rw [hact, hradd]⟩, 0, fun g hg => by
        rw [hrI a g hg, hact, sub_zero]⟩
    · rintro ⟨⟨hlc, hcoc⟩, x, hx⟩
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (c φ)
      refine ⟨e.symm v / δ φ, funext fun g => sub_eq_zero.mp ?_⟩
      refine eq_zero_of_locallyConstant I φ hgen (fun g => c g - r (e.symm v / δ φ) g)
        (hlc.sub (hrlc _)) (fun g h => ?_) ?_ (fun g hg => ?_) g
      · simp only [hcoc, hact, hradd]
        abel
      · simp only [r, div_mul_cancel₀ _ hφ, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, hv,
          sub_self]
      · simp only [hx g hg, hact, hrI _ g hg, sub_self]

end GlobalTheory.UnramifiedClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompat
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem ioE_fixed_of_resΓ_eq_one (hO : Function.Injective (algebraMap O LL)) (g : G)
    (hg : W.resΓ g = 1) (e : W.EE) : gR g (E.ioE e) = E.ioE e := by
  rw [← GlobalTheory.TorsionBoundCompare.ioE_γ E hO g e, hg, map_one]
  rfl

theorem ioE_letπ : E.ioE (algebraMap (LetA O n) W.EE letπ) = inclR πA := by
  rw [E.ioE_ext, E.io_π]

theorem ioE_bounded_pole {p : ℕ} (hp : PD.p = p) (e : W.EE) :
    ∃ c : ℕ, Near (inclR : RA →+* RW) p (inclR πA) 0 (inclR πA ^ c * E.ioE e) := by
  obtain ⟨a, m, h⟩ := W.EE_dense e 1
  rw [pow_one, Ideal.mem_span_singleton, hp] at h
  obtain ⟨r, hr⟩ := h
  have h1 := congrArg E.ioE hr
  rw [map_sub, map_mul, map_mul, map_natCast, map_pow, map_pow, ioE_letπ, E.ioE_ext] at h1
  refine ⟨m, E.io a, E.ioE r, ?_⟩
  rw [pow_zero, one_mul, ← h1]
  change _ = inclR (E.io a) + _
  ring

end Generic

theorem ioE_compat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ e, E.tie.ioE (W.φE e) = φRW LL (E.tie.ioE e)) ∧ (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ e, AI.gRW LL (g : GQ l) (E.tie.ioE e) = E.tie.ioE e) ∧ E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ) = piR AI LL s ∧ (∀ e, ∃ c : ℕ, NearPi AI LL s 0 (piR AI LL s ^ c * E.tie.ioE e)) := by
  intro l _ P AI K s LL h W E
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  exact ⟨fun e => GlobalTheory.TorsionBoundCompare.ioE_φ E.tie hO e,
    fun g hg e => ioE_fixed_of_resΓ_eq_one E.tie hO g hg e, ioE_letπ E.tie,
    fun e => ioE_bounded_pole E.tie (P.PD_p K) e⟩

end GlobalTheory.Decompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfCocycleRecursionOfFrobeniusTwist
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpStep

theorem exists_fixed {A W : Type} [CommRing A] [CommRing W] (i : A →+* W) (φ : A →+* A)
    (Φ : W →+* W) (h : ∀ a, Φ (i a) = i (φ a)) {N D c : A} (hD : IsUnit (i D))
    (hN : φ N = c * N) (hD' : φ D = c * D) : ∃ w : W, Φ w = w ∧ i N = w * i D := by
  obtain ⟨v, hv⟩ := hD.exists_left_inv
  have e : i N = i N * v * i D := by rw [mul_assoc, hv, mul_one]
  refine ⟨i N * v, ?_, e⟩
  apply (hD.map Φ).mul_right_cancel
  rw [← map_mul, ← e, h, h, hN, hD', map_mul, map_mul]
  linear_combination (i c) * e

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem isUnit_inclW {a : Ainf l} (ha : a.coeff 0 ≠ 0) : IsUnit (inclW l a) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [inclW, WittVector.map_coeff]
  exact fun hz => ha (IsFractionRing.injective (OCb l) (Cb l) (by rw [hz, map_zero]))

theorem π₁_coeff : AI.π₁.coeff 0 ≠ 0 := by
  have h0 : AI.π₁.coeff 0 = AI.ε1 - 1 := by
    change WittVector.constantCoeff (WittVector.teichmuller l AI.ε1 - 1) = _
    rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  rw [h0]
  intro hz
  apply AI.ε_ne_one
  rw [← frobeniusEquiv_symm_pow_p (OCb l) l AI.ε]
  change AI.ε1 ^ l = 1
  rw [sub_eq_zero.mp hz, one_pow]

theorem act_π₁_coeff (g : GQ l) : (AI.actW g AI.π₁).coeff 0 ≠ 0 := by
  rw [LocAinf.actW, WittVector.map_coeff]
  intro hz
  exact π₁_coeff AI ((AI.actT g).injective (by rw [map_zero]; exact hz))

theorem frob_π₁ : WittVector.frobenius AI.π₁ = AI.μ := by
  rw [LocAinf.π₁, LocAinf.μ, map_sub, map_one, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller, LocAinf.ε1, frobenius_apply_frobeniusEquiv_symm]

theorem frob_act (g : GQ l) (a : Ainf l) :
    WittVector.frobenius (AI.actW g a) = AI.actW g (WittVector.frobenius a) := by
  ext n
  simp only [LocAinf.actW, WittVector.coeff_frobenius_charP, WittVector.map_coeff, map_pow]

theorem frob_zl (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  rw [WittVector.frobenius_eq_map_frobenius]
  exact map_zlW l _ z

theorem frobW_inclW (a : Ainf l) : frobW l (inclW l a) = inclW l (WittVector.frobenius a) := by
  ext n
  change (WittVector.map (frobenius (Cb l) l) (inclW l a)).coeff n = _
  simp only [inclW, WittVector.coeff_frobenius_charP, WittVector.map_coeff, map_pow, frobenius_def]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (U : ℤ_[l]) (k : ℕ) (β η : Ainf l), Step AI g U AI.μ k (WittVector.frobenius β - AI.ξ ^ k * β) (WittVector.frobenius η - AI.ξ ^ k * η) → ∃ z : ℤ_[l], Step AI g U AI.π₁ k β (η + algebraMap ℤ_[l] (Ainf l) z * AI.π₁ ^ k) := by
  intro l _ P AI g U k β η h
  have hu : IsUnit (inclW l (AI.π₁ ^ k * AI.actW g AI.π₁ ^ k)) := by
    rw [map_mul, map_pow, map_pow]
    exact ((isUnit_inclW (π₁_coeff AI)).pow k).mul ((isUnit_inclW (act_π₁_coeff AI g)).pow k)
  obtain ⟨w, hw, e⟩ := exists_fixed (inclW l) WittVector.frobenius (frobW l : WCb l →+* WCb l)
    frobW_inclW (N := algebraMap ℤ_[l] (Ainf l) U * AI.actW g β * AI.π₁ ^ k
      - AI.actW g AI.π₁ ^ k * β - AI.actW g AI.π₁ ^ k * η)
    (c := AI.ξ ^ k * AI.actW g AI.ξ ^ k) hu (by
      unfold Step at h
      simp only [map_sub, map_mul, map_pow, frob_act, frob_zl, frob_π₁, AI.μ_eq, mul_pow] at h ⊢
      linear_combination h) (by
      simp only [map_mul, map_pow, frob_act, frob_π₁, AI.μ_eq, mul_pow]
      ring)
  obtain ⟨z, rfl⟩ := (GlobalTheory.ArtinSchreierWitt.main l).2.1 w hw
  refine ⟨z, ?_⟩
  rw [← (inclWA l).commutes z] at e
  change _ = inclW l _ * _ at e
  rw [← map_mul] at e
  have e' := WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l)) e
  unfold Step
  linear_combination e'

end GlobalTheory.ExpStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixedLiftOfFixedModPrime
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem actWCbHom_teichmuller_eq {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (g : GQ l) (c : Cb l) :
    AI.actWCbHom g (WittVector.teichmuller l c) =
      WittVector.teichmuller l (autCb l (AI.actT g) c) :=
  WittVector.map_teichmuller l (autCb l (AI.actT g)).toRingHom c

theorem exists_fix_lift_of_fix_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (H : Set (GQ l)) (x : RW LL)
    (h : ∀ g ∈ H, ∃ r, AI.gRW LL g x - x = (l : RW LL) * r) :
    ∃ y ∈ fixSub AI LL H, ∃ r, y - x = (l : RW LL) * r := by
  obtain ⟨y, hy⟩ : ∃ y : RW LL, ∀ i, crd (basisO LL) i y =
      WittVector.teichmuller l ((crd (basisO LL) i x).coeff 0) :=
    ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ((crd (basisO LL) j x).coeff 0),
      fun i => crd_sum (basisO LL) _ i⟩
  refine ⟨y, mem_fixSub.2 fun g hg => ext_crd (basisO LL) fun i => ?_,
    (dvd_iff_crd LL _).2 fun i => ?_⟩
  · have h1 := (dvd_iff_crd LL _).1 (h g hg) i
    rw [LinearMap.map_sub, sub_coeff_zero, crd_gRW, coeff_actWCbHom] at h1
    rw [crd_gRW, hy, actWCbHom_teichmuller_eq, sub_eq_zero.1 h1]
  · rw [LinearMap.map_sub, sub_coeff_zero, hy, WittVector.teichmuller_coeff_zero, sub_self]

end GlobalTheory.Decompl
end

