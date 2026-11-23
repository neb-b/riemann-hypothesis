module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0042
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise

namespace GlobalTheory.PoitouTateConj

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def conjBack (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x)) :
    G F Ω →* G F Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := (σ.trans g.toRingEquiv).trans σ.symm) (fun x => by
    simp only [RingEquiv.trans_apply, hστ, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [← hστ, RingEquiv.symm_apply_apply])
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

theorem conjBack_apply (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
    (g : G F Ω) (x : Ω) : conjBack σ τ hστ g x = σ.symm (g (σ x)) := rfl

theorem apply_conjBack (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
    (g : G F Ω) (x : Ω) : σ (conjBack σ τ hστ g x) = g (σ x) := by
  rw [conjBack_apply, RingEquiv.apply_symm_apply]

theorem mem_Dec_of_forall {A : ValuationSubring Ω} {g : G F Ω} (h : ∀ x, g x ∈ A ↔ x ∈ A) :
    g ∈ Dec (F := F) A := by
  show g • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

variable (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
  {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
include hA

theorem valuation_le_one_iff_of_map (x : Ω) :
    A'.valuation (σ x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, hA]

theorem valuation_lt_one_iff_of_map (x : Ω) :
    A'.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', hA, ← map_inv₀, hA, map_eq_zero_iff _ σ.injective]

omit hA in
include hA in
theorem conjBack_mem_Dec {g : G F Ω} (hg : g ∈ Dec (F := F) A') :
    conjBack σ τ hστ g ∈ Dec (F := F) A :=
  mem_Dec_of_forall fun x => by
    rw [← hA, apply_conjBack, apply_mem_iff_of_mem_Dec hg, hA]

omit hA in
include hA in
theorem conjBack_mem_Ine {g : G F Ω} (hg : g ∈ Ine (F := F) A') :
    conjBack σ τ hστ g ∈ Ine (F := F) A := by
  refine ⟨conjBack_mem_Dec σ τ hστ hA hg.1, fun x hx => ?_⟩
  rw [← valuation_lt_one_iff_of_map σ hA, map_sub, apply_conjBack]
  exact hg.2 _ ((valuation_le_one_iff_of_map σ hA x).2 hx)

omit hA in
include hA in
theorem conjBack_isFrob {q : ℕ} {g : G F Ω} (hg : IsFrob A' q g) :
    IsFrob A q (conjBack σ τ hστ g) := by
  refine ⟨conjBack_mem_Dec σ τ hστ hA hg.1, fun x hx => ?_⟩
  rw [← valuation_lt_one_iff_of_map σ hA, map_sub, apply_conjBack, map_pow]
  exact hg.2 _ ((valuation_le_one_iff_of_map σ hA x).2 hx)

omit hA in
theorem cycMod_conjBack (l : ℕ) [Fact l.Prime] (r : ℕ) (g : G F Ω) :
    cycMod F Ω l r (conjBack σ τ hστ g) = cycMod F Ω l r g := by
  have e : MulSemiringAction.toRingAut (G F Ω) Ω (conjBack σ τ hστ g) =
      σ⁻¹ * MulSemiringAction.toRingAut (G F Ω) Ω g * σ := by
    ext x; rfl
  simp only [cycMod, cycZ, MonoidHom.comp_apply, e, map_mul, map_inv]
  rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]


omit hA in
theorem continuous_conjBack [Algebra.IsAlgebraic F Ω] : Continuous (conjBack σ τ hστ) := by
  haveI : Algebra.IsIntegral F Ω := inferInstance
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  have hU : IsOpen (⋂ i, (MulAction.stabilizer (G F Ω) (σ (b i : Ω)) : Set (G F Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral _
  refine Filter.mem_of_superset (hU.mem_nhds (Set.mem_iInter.2 fun i => (MulAction.stabilizer (G F Ω) _).one_mem)) fun g hg => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, conjBack σ τ hστ g (b i) = b i := fun i => by
    have := Set.mem_iInter.1 hg i
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    rw [conjBack_apply, this, RingEquiv.symm_apply_apply]
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hb]


omit hA in
include hA hστ in
theorem exists_place_map {v : HeightOneSpectrum (𝓞 F)} (hAv : IsPlaceOver A v) :
    ∃ v' : HeightOneSpectrum (𝓞 F), IsPlaceOver A' v' ∧ normV v' = normV v ∧
      ∀ ϖ : 𝓞 F, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∃ ϖ' : 𝓞 F, ϖ' ∈ v'.asIdeal ∧
        ϖ' ∉ v'.asIdeal ^ 2 ∧ algebraMap F Ω (ϖ' : F) = σ (algebraMap F Ω (ϖ : F)) := by
  let e : 𝓞 F ≃+* 𝓞 F := RingOfIntegers.mapRingEquiv τ
  have he : ∀ x : 𝓞 F, ((e x : 𝓞 F) : F) = τ (x : F) := fun x => rfl
  let v' : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v.asIdeal.map (e : 𝓞 F →+* 𝓞 F)
      isPrime := Ideal.map_isPrime_of_equiv e
      ne_bot := by
        rw [Ne, Ideal.map_eq_bot_iff_of_injective (f := (e : 𝓞 F →+* 𝓞 F)) e.injective]
        exact v.ne_bot }
  have hmem : ∀ x : 𝓞 F, x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal := fun x => by
    show x ∈ v.asIdeal.map (e : 𝓞 F →+* 𝓞 F) ↔ _
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap]
  refine ⟨v', fun x => ?_, ?_, fun ϖ h1 h2 => ⟨e ϖ, ?_, ?_, ?_⟩⟩
  · rw [hmem, ← hAv, ← valuation_lt_one_iff_of_map σ hA, hστ]
    congr 3
    rw [← he, RingEquiv.apply_symm_apply]
  · unfold normV
    exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal v'.asIdeal e rfl).toEquiv.symm
  · rw [hmem, RingEquiv.symm_apply_apply]; exact h1
  · show e ϖ ∉ (v.asIdeal.map (e : 𝓞 F →+* 𝓞 F)) ^ 2
    rw [← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
    exact h2
  · rw [he, hστ]

end GlobalTheory.PoitouTateConj

namespace GlobalTheory.PoitouTateConj
open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [hl : Fact l.Prime] {r : ℕ}

theorem conjCompatible (hr : 0 < r) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ r)) {inv : InvFam F Ω l r}
    (h : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A)) :
    ConjCompatible ζ inv := by
  intro σ τ hστ c hc A A' v hAv hA z z' hz
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  let ψ : Dec (F := F) A' →* Dec (F := F) A :=
    ((conjBack σ τ hστ).comp (Dec (F := F) A').subtype).codRestrict (Dec (F := F) A)
      (fun g => conjBack_mem_Dec σ τ hστ hA g.2)
  have hψv : ∀ g : Dec (F := F) A', ((ψ g : Dec (F := F) A) : G F Ω) = conjBack σ τ hστ g := fun _ => rfl
  have hψc : Continuous ψ :=
    (((continuous_conjBack σ τ hστ).comp continuous_subtype_val)).subtype_mk _
  have hψ : ∀ (g' : Dec (F := F) A') x, (g' : G F Ω) (σ x) = σ (((ψ g' : Dec (F := F) A) : G F Ω) x) :=
    fun g' x => (apply_conjBack σ τ hστ g' x).symm
  have hcyc : ∀ g' : Dec (F := F) A',
      ((cycMod F Ω l r ((ψ g' : Dec (F := F) A) : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) =
        ((cycMod F Ω l r (g' : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := fun g' => by
    rw [hψv, cycMod_conjBack]
  have hz' : ∀ p, z'.1 p = c * z.1 (ψ p.1, ψ p.2) := fun p => hz _ _ p.1 p.2 (hψ p.1) (hψ p.2)

  have hTZ : ∀ w : Z2 (muLoc F l r A),
      (fun p : Dec (F := F) A' × Dec (F := F) A' => c * w.1 (ψ p.1, ψ p.2)) ∈ Z2 (muLoc F l r A') := by
    intro w
    refine ⟨continuous_const.mul (w.2.1.comp ((hψc.comp continuous_fst).prodMk (hψc.comp continuous_snd))),
      fun g h k => ?_⟩
    have e := w.2.2 (ψ g) (ψ h) (ψ k)
    simp only [charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul] at e ⊢
    rw [← hcyc g]
    linear_combination c * e
  have hTB : ∀ f : Dec (F := F) A → ZMod (l ^ r), Continuous f →
      ∃ f' : Dec (F := F) A' → ZMod (l ^ r), Continuous f' ∧
        ∀ p, d1 (muLoc F l r A') f' p = c * d1 (muLoc F l r A) f (ψ p.1, ψ p.2) := by
    intro f hf
    refine ⟨fun g => c * f (ψ g), continuous_const.mul (hf.comp hψc), fun p => ?_⟩
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, charRep_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, map_mul]
    rw [← hcyc p.1]
    ring

  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.Published.PoitouTate.Model.exists_unramified hAv (n := l ^ r)
    (Nat.one_lt_pow hr.ne' hl.out.one_lt)
  obtain ⟨ϖ, y, κ, z0, ha, hb, hy, hκ, hz0e⟩ :=
    GlobalTheory.Published.PoitouTate.Model.exists_kummer hζ A v χ h1 h2
  have hz0 : inv A (Submodule.Quotient.mk z0) = 1 := (h A v hAv).2 ϖ y κ χ z0 ha hb hy hκ h1 h3 h4 hz0e
  set a := inv A (Submodule.Quotient.mk z) with ha_def
  have hzz : (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk (a • z0) := by
    rw [Submodule.Quotient.mk_smul]
    exact (h A v hAv).1.1 (by rw [map_smul, hz0, smul_eq_mul, mul_one])
  rw [Submodule.Quotient.eq] at hzz
  obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hzz)
  obtain ⟨f', hf', hf'e⟩ := hTB f hf

  obtain ⟨v', hA'v', hN, hϖ⟩ := exists_place_map σ τ hστ hA hAv
  obtain ⟨ϖ', ha', hb', hϖe⟩ := hϖ ϖ ha hb
  let z0' : Z2 (muLoc F l r A') := ⟨_, hTZ z0⟩
  have hpow : ∀ s t : ZMod (l ^ r), ζ ^ (s * t).val = ζ ^ (s.val * t.val) := fun s t => by
    rw [ZMod.val_mul]
    conv_rhs => rw [← Nat.mod_add_div (s.val * t.val) (l ^ r), pow_add, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  have hz0' : inv A' (Submodule.Quotient.mk z0') = 1 := by
    refine (h A' v' hA'v').2 ϖ' (σ y) (fun g => c * κ (ψ g)) (fun g => χ (ψ g)) z0' ha' hb' ?_ ?_
      ?_ ?_ ?_ ?_
    · rw [← map_pow, hy, hϖe]
    · intro g
      rw [hψ, hκ, map_mul, map_pow, hc, ← pow_mul, hpow]
    · intro g h; rw [map_mul, h1]
    · intro g hg; exact h3 _ (by rw [hψv]; exact conjBack_mem_Ine σ τ hστ hA hg)
    · intro g hg; exact h4 _ (by rw [hψv]; rw [hN] at hg; exact conjBack_isFrob σ τ hστ hA hg)
    · intro g h; show c * z0.1 (ψ g, ψ h) = _; rw [hz0e]; ring
  have hzz' : (Submodule.Quotient.mk z' : H2 (muLoc F l r A')) = Submodule.Quotient.mk (a • z0') := by
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨f', hf', ?_⟩)
    funext p
    rw [hf'e, hfe]
    show _ = z'.1 p - a * (c * z0.1 (ψ p.1, ψ p.2))
    rw [hz']
    show c * (z.1 _ - a * z0.1 _) = _
    ring
  rw [hzz', Submodule.Quotient.mk_smul, map_smul, hz0', smul_eq_mul, mul_one]

theorem poitouTateDuality_of_normalised (h : PoitouTateNormalised) : PoitouTateDuality := by
  intro F Ω _ _ _ _ _ l _ r hl hr ζ hζ
  obtain ⟨inv, h1, h2⟩ := h F Ω l r hl hr ζ hζ
  exact ⟨inv, ⟨h1, conjCompatible hr hζ h1⟩, h2⟩

end GlobalTheory.PoitouTateConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLaws
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.PwLaws
variable {l : ℕ} [Fact l.Prime]
theorem pw_apply_eq (k : ℤ) (x : Fl l) :
    pw k x = ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ k : RingAut (Fl l)) x := rfl
theorem pw_zadd (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  simp only [pw_apply_eq, zpow_add, RingAut.mul_apply]
theorem pw_one (x : Fl l) : pw 1 x = x ^ l := by
  rw [pw_apply_eq, zpow_one]
  show frobeniusEquiv (Fl l) l x = _
  rw [frobeniusEquiv_apply, frobenius_def]
theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_apply_eq]
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
    rw [h, pw_zadd, ih, pw_one, ← pow_mul, pow_succ]

theorem pw_zero_int (x : Fl l) : pw 0 x = x := by
  simp [pw_apply_eq]
theorem sh_pow' (x : Fl l) (m : ℕ) : sh (x ^ m) = sh x ^ m := by
  simp only [sh, map_pow, SubmonoidClass.coe_pow]
theorem norm_sh_pw_nat (n : ℕ) (x : Fl l) : ‖sh (pw (n : ℤ) x)‖ = ‖sh x‖ ^ (l ^ n) := by
  rw [pw_nat, sh_pow', norm_pow]
theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [norm_sh_pw_nat, zpow_natCast, ← Real.rpow_natCast]
    push_cast
    rfl
  · set y := pw (-(n : ℤ)) x with hy
    have hx : x = pw (n : ℤ) y := by
      rw [hy, ← pw_zadd, add_neg_cancel, pw_zero_int]
    have hne : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have e : ((l : ℝ) ^ (-(n : ℤ))) = (((l ^ n : ℕ) : ℝ))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
      push_cast
      rfl
    conv_rhs => rw [hx, norm_sh_pw_nat, e]
    exact (Real.pow_rpow_inv_natCast (norm_nonneg _) hne).symm

theorem pw_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (k : ℤ) (x y : Fl l), pw k (x + y) = pw k x + pw k y) ∧ (∀ (k : ℤ) (x y : Fl l), pw k (x * y) = pw k x * pw k y) ∧ (∀ k : ℤ, pw k (0 : Fl l) = 0) ∧ (∀ (a b : ℤ) (x : Fl l), pw (a + b) x = pw a (pw b x)) ∧ (∀ (n : ℕ) (x : Fl l), pw n x = x ^ l ^ n) ∧ (∀ (k : ℤ) (n : ℕ) (x : Fl l), pw k (x ^ n) = pw k x ^ n) ∧ (∀ (k : ℤ) (x : Fl l), ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k)) := by
  intro l _
  refine ⟨fun k x y => ?_, fun k x y => ?_, fun k => ?_, pw_zadd, pw_nat, fun k n x => ?_, norm_sh_pw⟩
  · simp only [pw_apply_eq, map_add (f := _)]
  · simp only [pw_apply_eq, map_mul]
  · simp only [pw_apply_eq, map_zero]
  · simp only [pw_apply_eq, map_pow]

end GlobalTheory.PSer.PwLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendsto
section
open GlobalTheory.UnitLemma Polynomial Filter Topology

namespace GlobalTheory.UnitLemma

theorem unitaryLimit : UnitaryLimit := by
  have L0 := _root_.GlobalTheory.UnitLemma.OrbitFinite.orbits_finite
  have S1 := _root_.GlobalTheory.UnitLemma.lattice_sandwich
  have S2 := _root_.GlobalTheory.TorusOrbitLat.orbit_count
  have S3 := _root_.GlobalTheory.UnitLemma.UU_eq_sum_orbits
  have S4 := _root_.GlobalTheory.UnitLemma.torus_mod_intUnits_structure
  have S5 := _root_.GlobalTheory.UnitLemma.rho_pow_eq_card_box
  have S6 := _root_.GlobalTheory.ratio_box_counts_tendsto_one

  intro K B hB a ha x hx
  classical
  obtain ⟨r, φ, c, hsurj, hker, hc, hint⟩ := S4 K B hB a ha
  have hrho : ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) :=
    S5 K B a r φ c hsurj hker hint
  have hpos : ∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j) := fun j => by
    rw [hrho]; exact Finset.prod_pos fun i _ => by omega
  obtain ⟨hfin, hstab⟩ := L0 K B hB.2 x hx.1 hx.2
  choose m hm using fun o : Orb K.O B.T (B.X x) => S1 K B hB a ha _ (Quot.out o).2.1
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  set M := Finset.univ.sup m with hMdef
  have hmM : ∀ o, m o ≤ M := fun o => Finset.le_sup (Finset.mem_univ o)
  have key := fun (k : ℕ) (hk : M ≤ k) (o : Orb K.O B.T (B.X x)) =>
    S2 K B _ (hstab _ (Quot.out o).2).1 (hstab _ (Quot.out o).2).2 a hpos M k hk
      (hm o M (hmM o)).1 (hm o M (hmM o)).2
  have hUU : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) =
      ∑ o : Orb K.O B.T (B.X x), (Nat.card {L' : Submodule K.O B.A // (∃ t ∈ B.T, L' = mulLat K.O (t : B.A) (Quot.out o).1) ∧
        algebraMap K.O B.A a ^ k ∈ L'} : ℝ) := by
    intro k hk
    rw [S3 K B x _ hfin (fun o => (key k hk o).1), finsum_eq_sum_of_fintype]
    push_cast; rfl
  have hN : (B.N x : ℝ) = ∑ o : Orb K.O B.T (B.X x),
      (((stabLat K.O (Quot.out o).1 ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℝ) := by
    unfold InvAlg.N orbSum
    rw [finsum_eq_sum_of_fintype]
    push_cast
    simp
  have hlo : ∀ k, M ≤ k → (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) ≤ B.UU x (algebraMap K.O B.A a ^ k) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.1
  have hhi : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) ≤ (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.2
  have hposR : ∀ j, (0 : ℝ) < B.rho (algebraMap K.O B.A a ^ j) := fun j => by exact_mod_cast hpos j
  have hup : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have := (S6 r c M).const_mul (B.N x : ℝ)
    rw [mul_one] at this
    refine this.congr fun k => ?_
    rw [hrho, hrho, mul_div_assoc]
  have hdown : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have h1 := ((S6 r c M).inv₀ one_ne_zero).comp (tendsto_sub_atTop_nat M)
    have h2 := h1.const_mul (B.N x : ℝ)
    rw [inv_one, mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop M] with k hk
    simp only [Function.comp_apply, inv_div]
    rw [Nat.sub_add_cancel hk, hrho, hrho, mul_div_assoc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdown hup ?_ ?_
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hlo k hk) (hposR k).le
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hhi k hk) (hposR k).le

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsEqOfPowPredEqOfValOne
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory

theorem eq_of_pow_pred_eq_of_sub_one_mem {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R)
    (hI : I ≠ ⊤) (l : ℕ) (hl : 0 < l) (hlI : (l : R) ∈ I) (a b : R)
    (hab : a ^ (l - 1) = b ^ (l - 1)) (ha : a - 1 ∈ I) (hb : b - 1 ∈ I) : a = b := by
  by_contra hne
  have h := geom_sum₂_mul a b (l - 1)
  rw [hab, sub_self] at h
  have hs := (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have ha' : Ideal.Quotient.mk I a = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact ha
  have hb' : Ideal.Quotient.mk I b = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hb
  have hl' : (l : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hlI
  have h2 := congrArg (Ideal.Quotient.mk I) hs
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, ha', hb', one_pow, mul_one, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, map_zero] at h2
  rw [Nat.cast_sub hl, hl', Nat.cast_one, zero_sub, neg_eq_zero] at h2
  apply hI
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem, map_one]
  exact h2

def posValIdeal {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) : Ideal ↥(OL LL) where
  carrier := {x | 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, (algebraMap ↥(OL LL) ↥LL.1).map_add] at ha hb ⊢
    exact (P.v LL).map_lt_add ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, (algebraMap ↥(OL LL) ↥LL.1).map_mul,
      AddValuation.map_mul] at hx ⊢
    have hc : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 c) := (P.v_O LL _).2 c.2
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)

theorem oneUnit_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (a b : ↥(OL LL)) (hab : a ^ (l - 1) = b ^ (l - 1))
    (ha : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 a - 1))
    (hb : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 b - 1)) : a = b := by
  refine eq_of_pow_pred_eq_of_sub_one_mem (posValIdeal P LL) ?_ l (Fact.out : l.Prime).pos ?_ a b
    hab ?_ ?_
  · rw [Ne, Ideal.eq_top_iff_one]
    change ¬ 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 1)
    simp
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)))
    rw [map_natCast, P.v_l]
    exact zero_lt_one
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (a - 1))
    rwa [map_sub, map_one]
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (b - 1))
    rwa [map_sub, map_one]

theorem units_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (u w : (↥(OL LL))ˣ) (h : u ^ (l - 1) = w ^ (l - 1))
    (hu : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (u : ↥(OL LL)) - 1))
    (hw : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1)) : u = w := by
  apply Units.ext
  refine oneUnit_eq_of_pow_pred_eq_of_pos P LL _ _ ?_ hu hw
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h]

theorem units_eq_of_pow_pred_eq_of_val_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (LL : FinExt l) (u w : (↥(OL LL))ˣ), u ^ (l - 1) = w ^ (l - 1) →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((u : ↥(OL LL)) - 1)) = 1 →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1) = 1 → u = w := by
  intro l _ P LL u w h hu hw
  rw [map_sub, map_one] at hu
  refine units_eq_of_pow_pred_eq_of_pos P LL u w h ?_ ?_
  · rw [hu]; exact zero_lt_one
  · rw [hw]; exact zero_lt_one

end GlobalTheory
end

