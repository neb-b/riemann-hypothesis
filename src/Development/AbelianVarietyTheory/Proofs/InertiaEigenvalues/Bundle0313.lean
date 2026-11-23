module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorFullyFaithful
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmSubOneNeZeroPt
section
noncomputable section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Trans

variable (l : ℕ) [Fact l.Prime]

theorem map_ne_zero_pt : ∀ y : Formalism.Per.Ainf l, y ≠ 0 →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) y ≠ 0 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  obtain ⟨N, h01, -, -, hmul, hA⟩ := GlobalTheory.GaussExt.exists_gauss_acris l _ le_rfl hr1
  have hbdd : ∀ a : Formalism.Per.Ainf l, BddAbove (Set.range fun n : ℕ =>
      ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n) := by
    intro a
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 :=
      (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
    have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) h1 (by positivity)
    have h3 : ((l : ℝ)⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity) hr1.le
    calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpos : ∀ a : Formalism.Per.Ainf l, a ≠ 0 → 0 < N (algebraMap _ _ a) := by
    intro a ha0
    obtain ⟨n, ha⟩ : ∃ n, a.coeff n ≠ 0 := by
      by_contra hc
      apply ha0
      refine WittVector.ext fun n => ?_
      rw [WittVector.zero_coeff]
      by_contra hn
      exact hc ⟨n, hn⟩
    rw [hA]
    refine lt_of_lt_of_le ?_ (le_ciSup (hbdd a) n)
    have hne : (((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
      intro h
      apply ha
      refine (GlobalTheory.TiltAbs.untilt_ultrametric_definite l (a.coeff n) 0).2 ?_
      exact Subtype.ext h
    have hl0 : (0 : ℝ) < l := lt_trans one_pos hl
    exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _) (pow_pos (inv_pos.2 hl0) _)
  have hN0 : N 0 = 0 := by
    have hz : ∀ n : ℕ, (0 : ℝ) ^ ((1 : ℝ) / (l : ℝ) ^ n) = 0 := fun n => Real.zero_rpow (by positivity)
    rw [← map_zero (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)), hA]
    have hz' : ∀ n : ℕ, (0 : ℝ) ^ (((l : ℝ) ^ n)⁻¹) = 0 := fun n => Real.zero_rpow (by positivity)
    simp [hz, hz', GlobalTheory.GaussExt.untilt_zero]
  intro y hy h0
  have := hpos y hy
  rw [h0, hN0] at this
  exact lt_irrefl _ this

theorem tm_sub_one_ne_zero_pt (e : Formalism.Per.Fl l) (he : e ≠ 1) : (Formalism.Per.tm e - 1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  apply he
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) (sub_eq_zero.1 h)
  simpa using h'

theorem one_ne_zero_pt : (1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h
  simp at h'

theorem map_prod_ne_zero_pt : ∀ s : List (Formalism.Per.Fl l), (∀ e ∈ s, e ≠ 1) →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (s.map fun e => Formalism.Per.tm e - 1).prod ≠ 0 := by
  intro s
  induction s with
  | nil =>
    intro _
    rw [List.map_nil, List.prod_nil]
    exact map_ne_zero_pt l 1 (one_ne_zero_pt l)
  | cons e s ih =>
    intro hs
    rw [List.map_cons, List.prod_cons, map_mul]
    intro h
    exact (_root_.GlobalTheory.PMon.Gauss.acris_mul_eq_zero l _ _ h).elim
      (map_ne_zero_pt l _ (tm_sub_one_ne_zero_pt l e (hs e List.mem_cons_self)))
      (ih fun e' he' => hs e' (List.mem_cons_of_mem _ he'))

end GlobalTheory.PMon.Trans

theorem GlobalTheory.PMon.Trans.acris_bcris : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)) ∧ (∀ x : Formalism.Per.Acris l, Formalism.Per.φB l (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l x)) ∧ ∀ c : ℤ_[l], algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (zc l c) = Formalism.Per.zB l c := by
  intro l _
  refine ⟨?_, fun x => GlobalTheory.CrisMaps.φB_phiA l x, fun c => (GlobalTheory.RingIface.zB_alg l c).symm⟩
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, h⟩ := GlobalTheory.CrisLoc.exists_pow_mul_eq_zero l e he hne hx
  refine (_root_.GlobalTheory.PMon.Gauss.acris_mul_eq_zero l _ _ h).resolve_left ?_
  have h1 := GlobalTheory.PMon.Trans.map_prod_ne_zero_pt l (List.replicate n e)
    fun e' he' => (List.eq_of_mem_replicate he').symm ▸ hne
  rwa [List.map_replicate, List.prod_replicate, map_pow] at h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleFundamentalMultipleModPow
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.UnifSpan

open GlobalTheory.TateTop

private theorem quotRep_twist_apply {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) (n : ℕ) (g : G) (q : O ⧸ powSub (M := O) ϖ n) :
    quotRep (twist ε O) ϖ n g q = ((ε g : Oˣ) : O) • q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [quotRep_mk, twist_apply, Submodule.Quotient.mk_smul]

private theorem factor_quotRep_of_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) {m n : ℕ} (hmn : m ≤ n) (g : G)
    (q : O ⧸ powSub (M := O) ϖ n) :
    Submodule.factor (powSub_anti (M := O) ϖ hmn) (quotRep (twist ε O) ϖ n g q) =
      quotRep (twist ε O) ϖ m g (Submodule.factor (powSub_anti (M := O) ϖ hmn) q) := by
  rw [quotRep_twist_apply, quotRep_twist_apply]
  exact map_smul _ _ _

theorem span_mod_pow {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
    {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p])
    (hgen : ∀ r, GlobalTheory.TateTop.Gen χ r c) (φ : ℤ_[p] →+* O) (ε : G →* Oˣ)
    (hε : ∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) (ϖ : O) (hϖ : Irreducible ϖ)
    (hp : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hopen : ∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O))
    (w : G × G → O) (hw : w ∈ Z2 (twist ε O)) :
    ∃ a : O, ∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧
      ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) =
        Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h))) := by
  classical
  have hwZ := (mem_cocycles2 (twist ε O) w).mp hw

  have hp' := hp
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton] at hp'
  obtain ⟨t, ht⟩ := hp'

  have hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M := O) ϖ n) := fun n =>
    QuotientAddGroup.discreteTopology (N := (powSub (M := O) ϖ n).toAddSubgroup) (hopen n)

  let S : ℕ → Set O := fun n => {a | ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧
      ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) =
        Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h)))}

  have hne : ∀ n, (S n).Nonempty := by
    intro n
    have := hdisc n
    letI : Module ℤ_[p] (O ⧸ powSub (M := O) ϖ n) := Module.compHom _ φ
    have hsm : ∀ (s : ℤ_[p]) (q : O ⧸ powSub (M := O) ϖ n), s • q = φ s • q := fun _ _ => rfl
    have : CompactSpace (O ⧸ powSub (M := O) ϖ n) := by
      refine ⟨?_⟩
      rw [← (Submodule.mkQ_surjective (powSub (M := O) ϖ n)).range_eq]
      exact isCompact_range (Submodule.continuous_mkQ _)
    have : Finite (O ⧸ powSub (M := O) ϖ n) := finite_of_compact_of_discrete
    have hkill : ∀ m : O ⧸ powSub (M := O) ϖ n, ((p : ℤ_[p]) ^ n) • m = 0 := by
      intro m
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [hsm, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_powSub]
      refine ⟨t ^ n * x, ?_⟩
      rw [map_pow, map_natCast, ht, smul_eq_mul, smul_eq_mul]
      ring
    obtain ⟨-, hex, -⟩ := hgen n (O ⧸ powSub (M := O) ϖ n) hkill
    have hz : IsCoc χ (fun q : G × G => (Submodule.Quotient.mk (w q) : O ⧸ powSub (M := O) ϖ n)) := by
      refine ⟨(IsLocallyConstant.iff_continuous _).mpr ((Submodule.continuous_mkQ _).comp hwZ.1),
        fun g h k => ?_⟩
      have e := hwZ.2 g h k
      rw [twist_apply, hε g] at e
      rw [hsm, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub,
        ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_sub, e, Submodule.Quotient.mk_zero]
    obtain ⟨x, b, hb, hzb⟩ := hex _ hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨a, b, hb.continuous, fun g h => ?_⟩
    have e := hzb (g, h)
    simp only [cob, hsm] at e
    rw [d1_apply, quotRep_twist_apply, hε g, Submodule.Quotient.mk_sub, e,
      show a * φ (c (g, h)) = φ (c (g, h)) • a from mul_comm _ _, Submodule.Quotient.mk_smul]
    abel

  have hanti : ∀ n, S (n + 1) ⊆ S n := by
    intro n a ha
    obtain ⟨b, hb, hd⟩ := ha
    refine ⟨fun g => Submodule.factor (powSub_anti (M := O) ϖ (Nat.le_succ n)) (b g),
      (continuous_factor ϖ (Nat.le_succ n)).comp hb, fun g h => ?_⟩
    have e := hd g h
    rw [d1_apply] at e
    rw [d1_apply, ← factor_quotRep_of_le ε ϖ (Nat.le_succ n), ← map_sub, ← map_add (f := _), e]
    exact Submodule.factor_mk _ _

  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    have := hdisc n
    have hpre : S n = (powSub (M := O) ϖ n).mkQ ⁻¹' ((powSub (M := O) ϖ n).mkQ '' S n) := by
      refine (Set.subset_preimage_image _ _).antisymm ?_
      rintro a' ⟨a, ⟨b, hb, hd⟩, hmk⟩
      refine ⟨b, hb, fun g h => ?_⟩
      rw [hd g h, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub]
      congr 1
      rw [Submodule.Quotient.eq]
      have hmk' : Submodule.Quotient.mk (p := powSub (M := O) ϖ n) a =
          Submodule.Quotient.mk a' := hmk
      have hd' := Submodule.smul_mem _ (φ (c (g, h))) ((Submodule.Quotient.eq _).mp hmk')
      rw [smul_eq_mul] at hd'
      convert hd' using 1
      ring
    rw [hpre]
    exact (isClosed_discrete _).preimage (Submodule.continuous_mkQ _)

  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
    (hclosed 0).isCompact hclosed
  exact ⟨a, fun n => Set.mem_iInter.mp ha n⟩

end GlobalTheory.UnifSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleMemCoboundariesOfModUniformizerPow
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.PadicH2SeparatedDVR

open GlobalTheory.LocDualInt

theorem discrete_quot {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (P : Submodule O O) (hP : IsOpen (P : Set O)) : DiscreteTopology (O ⧸ P) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
  have hq := (Submodule.isOpenQuotientMap_mkQ P).isQuotientMap
  rw [← hq.isOpen_preimage]
  have : (P.mkQ ⁻¹' {Submodule.Quotient.mk x}) = (fun y => y - x) ⁻¹' (P : Set O) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, SetLike.mem_coe]
    exact Submodule.Quotient.eq P
  rw [this]
  exact hP.preimage (continuous_sub_right x)

theorem continuous_mk {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (P : Submodule O O) : Continuous (Submodule.Quotient.mk : O → O ⧸ P) :=
  (Submodule.isOpenQuotientMap_mkQ P).continuous

theorem d1_mk {O : Type} [CommRing O] {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) (n : ℕ)
    (b : G → O) :
    d1 (quotRep (twist ε O) ϖ n) (fun g => Submodule.Quotient.mk (b g)) =
      fun p => Submodule.Quotient.mk (d1 (twist ε O) b p) := by
  funext p
  show quotRep (twist ε O) ϖ n p.1 (Submodule.Quotient.mk (b p.2)) - Submodule.Quotient.mk (b (p.1 * p.2))
      + Submodule.Quotient.mk (b p.1) = Submodule.Quotient.mk ((twist ε O) p.1 (b p.2) - b (p.1 * p.2) + b p.1)
  rw [quotRep_mk, Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub]

theorem separated_dvr_second_cohomology_mem : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  intro O _ _ _ _ _ _ _ G _ _ ε ϖ hopen hbasis hfin w hw hmod
  haveI hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M := O) ϖ n) := fun n => discrete_quot _ (hopen n)
  let α : ∀ s : ℕ, Set (G → O ⧸ powSub (M := O) ϖ s) := fun s =>
    {β | Continuous β ∧ d1 (quotRep (twist ε O) ϖ s) β = fun p => Submodule.Quotient.mk (w p)}
  have hα : ∀ s, (α s).Finite := by
    intro s
    rcases Set.eq_empty_or_nonempty (α s) with h | ⟨c, hc⟩
    · rw [h]; exact Set.finite_empty
    refine ((hfin s).image (fun f => f + c)).subset ?_
    rintro β ⟨hβ, hd⟩
    refine ⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩
    have e : d1 (quotRep (twist ε O) ϖ s) (β - c) (g, h) = 0 := by
      rw [map_sub, hd, hc.2, sub_self]; rfl
    have e2 : quotRep (twist ε O) ϖ s g ((β - c) h) - (β - c) (g * h) + (β - c) g = 0 := e
    have : (β - c) g + quotRep (twist ε O) ϖ s g ((β - c) h) - (β - c) (g * h) = 0 := by
      rw [← e2]; abel
    exact (sub_eq_zero.1 this).symm
  let T : ℕ → Set (G → O) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : G → O) g =>
      (Submodule.Quotient.mk (b g) : O ⧸ powSub (M := O) ϖ s)) ⁻¹' α s
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_mk _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨β, hβc, hβ⟩ := hmod r
    refine ⟨fun g => qlift (β g), Set.mem_iInter₂.2 fun s hs => ⟨?_, ?_⟩⟩
    · have e : (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ s)) =
          fun g => Submodule.factor (powSub_anti (M := O) ϖ hs) (β g) := by
        funext g
        conv_rhs => rw [← mk_qlift (β g)]
        rfl
      show Continuous (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ s))
      rw [e]
      exact (continuous_factor ϖ hs).comp hβc
    · rw [d1_mk]
      funext p
      have h1 : (Submodule.Quotient.mk (d1 (twist ε O) (fun g => qlift (β g)) p) :
          O ⧸ powSub (M := O) ϖ r) = Submodule.Quotient.mk (w p) := by
        rw [← congrFun (d1_mk ε ϖ r (fun g => qlift (β g))) p]
        have : (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ r)) = β :=
          funext fun g => mk_qlift _
        rw [this]
        exact hβ p.1 p.2
      rw [Submodule.Quotient.eq] at h1 ⊢
      exact powSub_anti ϖ hs h1
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => (Submodule.Quotient.mk (b g) : O ⧸ powSub (M := O) ϖ s)) ∈ α s :=
    fun s => Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  have hbc : Continuous b := by
    rw [continuous_iff_continuousAt]
    intro x V hV
    have hW : (fun u => u + b x) ⁻¹' V ∈ nhds (0 : O) := by
      apply (continuous_add_const (b x)).continuousAt.preimage_mem_nhds
      simpa using hV
    obtain ⟨n, hn⟩ := hbasis _ hW
    have hloc : {y | (Submodule.Quotient.mk (b y) : O ⧸ powSub (M := O) ϖ n) =
        Submodule.Quotient.mk (b x)} ∈ nhds x :=
      ((isOpen_discrete {(Submodule.Quotient.mk (b x) : O ⧸ powSub (M := O) ϖ n)}).preimage
        (hb' n).1).mem_nhds rfl
    show b ⁻¹' V ∈ nhds x
    refine Filter.mem_of_superset hloc fun y hy => ?_
    have hy' : b y - b x ∈ powSub (M := O) ϖ n := (Submodule.Quotient.eq _).1 hy
    have := hn hy'
    simpa using this
  refine ⟨b, hbc, ?_⟩
  funext p
  have hall : ∀ n : ℕ, d1 (twist ε O) b p - w p ∈ powSub (M := O) ϖ n := by
    intro n
    have := congrFun (hb' n).2 p
    rw [d1_mk] at this
    exact (Submodule.Quotient.eq _).1 this
  by_contra hne'
  have hd : d1 (twist ε O) b p - w p ≠ 0 := sub_ne_zero.2 hne'
  obtain ⟨n, hn⟩ := hbasis _ (isOpen_compl_singleton.mem_nhds (Ne.symm hd))
  exact hn (hall n) rfl

end GlobalTheory.PadicH2SeparatedDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesAddSubLe
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem lam_add_sub_le : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x y : Fl l), 1 ≤ h → r < 1 → ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖lam h j (x + y) - lam h j x - lam h j y‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  intro l _ h j r x y hh hr hx hy
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hx
  have hxy : ‖sh (x + y)‖ ≤ r := (_root_.GlobalTheory.PSer.sh_add_le l r x y hx hy).2
  have sx := (_root_.GlobalTheory.PSer.lam_hasSum_norm_le_frob l h j r x hh hr hx).1
  have sy := (_root_.GlobalTheory.PSer.lam_hasSum_norm_le_frob l h j r y hh hr hy).1
  have sxy := (_root_.GlobalTheory.PSer.lam_hasSum_norm_le_frob l h j r (x + y) hh hr hxy).1
  have hs := (sxy.sub sx).sub sy
  have hg := (_root_.GlobalTheory.gam_laws l h j r hh hr0 hr).1
  have hpw := _root_.GlobalTheory.PSer.PwLaws.pw_laws l
  have hε : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (_root_.GlobalTheory.gam_laws l h j r hh hr0 hr).2.2.1
  have key := _root_.GlobalTheory.norm_hasSum_sub_finset_sum_le ℂ_[l] ℤ _ _ ∅ _ hε hs (by
    intro n _
    set k : ℤ := n * h + j
    beta_reduce
    rw [hpw.1 k x y]
    have e : (l : ℂ_[l]) ^ (-n) * sh (pw k x + pw k y) - (l : ℂ_[l]) ^ (-n) * sh (pw k x)
        - (l : ℂ_[l]) ^ (-n) * sh (pw k y)
        = (l : ℂ_[l]) ^ (-n) * (sh (pw k x + pw k y) - sh (pw k x) - sh (pw k y)) := by ring
    rw [e, norm_mul, norm_zpow]
    have hl0 : 0 ≤ (l : ℝ) ^ k := zpow_nonneg (Nat.cast_nonneg _) _
    have bx : ‖sh (pw k x)‖ ≤ r ^ ((l : ℝ) ^ k) := by
      rw [hpw.2.2.2.2.2.2 k x]; exact Real.rpow_le_rpow (norm_nonneg _) hx hl0
    have by' : ‖sh (pw k y)‖ ≤ r ^ ((l : ℝ) ^ k) := by
      rw [hpw.2.2.2.2.2.2 k y]; exact Real.rpow_le_rpow (norm_nonneg _) hy hl0
    have ha := (_root_.GlobalTheory.PSer.sh_add_le l _ (pw k x) (pw k y) bx by').1
    have hn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (-n) := zpow_nonneg (norm_nonneg _) _
    calc ‖(l : ℂ_[l])‖ ^ (-n) * ‖sh (pw k x + pw k y) - sh (pw k x) - sh (pw k y)‖
        ≤ ‖(l : ℂ_[l])‖ ^ (-n) * (‖(l : ℂ_[l])‖ * r ^ ((l : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left ha hn
      _ = ‖(l : ℂ_[l])‖ * (‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ k)) := by ring
      _ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := mul_le_mul_of_nonneg_left (hg n) (norm_nonneg _))
  simpa using key

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltSumSubLe
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (s : Finset ι) (r : ℝ) (x : ι → Fl l), 0 ≤ r → (∀ i ∈ s, ‖sh (x i)‖ ≤ r) → ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, sh (x i)‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (∑ i ∈ s, x i)‖ ≤ r := by
  intro l _ ι s r x hr hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : sh (0 : Fl l) = 0 := by
      have h : (0 : Fl l).untilt = 0 := Perfection.teichmuller_zero
      simp only [sh, h]; rfl
    simp only [Finset.sum_empty, h0, sub_zero, norm_zero]
    exact ⟨mul_nonneg (norm_nonneg _) hr, hr⟩
  | insert a t ha ih =>
    have ih' := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    have hxa : ‖sh (x a)‖ ≤ r := hs a (Finset.mem_insert_self a t)
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.PSer.sh_add_le l r (x a) (∑ i ∈ t, x i) hxa ih'.2
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, h2⟩
    have : sh (x a + ∑ i ∈ t, x i) - (sh (x a) + ∑ i ∈ t, sh (x i)) =
        (sh (x a + ∑ i ∈ t, x i) - sh (x a) - sh (∑ i ∈ t, x i)) + (sh (∑ i ∈ t, x i) - ∑ i ∈ t, sh (x i)) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ih'.1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorFullyFaithfulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFunctor_fullyFaithful : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : W.DD T →ₗ[W.EE] W.DD T'), (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) → ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x := by
  first | exact @GlobalTheory.FontaineFullyFaithful.main | exact GlobalTheory.FontaineFullyFaithful.main | (intros; apply GlobalTheory.FontaineFullyFaithful.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBot
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem wild_antitone_and_eventually_bot :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L], Antitone (wild K L) ∧ ∃ m, wild K L m = ⊥ := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨fun i j hij ↦ ?_, ?_⟩
  · exact lowerRamificationGroup_antitone K L (by simp only [add_le_add_iff_right, Nat.cast_le]; exact hij)
  · obtain ⟨n, hn⟩ := exists_lowerRamificationGroup_eq_bot K L
    exact ⟨n, hn _ (by omega)⟩

end GlobalTheory.PMon.Ram
end

