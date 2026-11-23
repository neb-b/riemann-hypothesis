module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.Bundle0012
public import GroundTheory.GlobalFields.KummerTheory.Splitting
public import GroundTheory.GlobalFields.TateThesis.Bundle0011

@[expose] public section

-- bundled from GroundTheory.GlobalFields.TateThesis.ChebotarevCount
section
namespace GroundTheory.Global

open NumberField IsDedekindDomain IntermediateField AdeleBaseChange
open scoped Pointwise

noncomputable section

section Sets

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

def chebotarevSet (C : Set Gal(L/K)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal ∈ C}


omit [IsGalois K L] in
theorem mem_fixingSubgroup_fixedField_zpowers (σ : Gal(L/K)) :
    σ ∈ fixingSubgroup (fixedField (Subgroup.zpowers σ)) := by
  rw [fixingSubgroup_fixedField]
  exact Subgroup.mem_zpowers σ

def galFixedZpowers (σ : Gal(L/K)) : Gal(L/fixedField (Subgroup.zpowers σ)) :=
  fixingSubgroupEquiv _ ⟨σ, mem_fixingSubgroup_fixedField_zpowers σ⟩

omit [IsGalois K L] in
theorem restrictScalars_galFixedZpowers (σ : Gal(L/K)) :
    (galFixedZpowers σ).restrictScalars K = σ :=
  AlgEquiv.ext fun _ ↦ rfl


omit [IsGalois K L] in
theorem restrictScalars_mem_zpowers (σ : Gal(L/K)) (g : Gal(L/fixedField (Subgroup.zpowers σ))) :
    g.restrictScalars K ∈ Subgroup.zpowers σ := by
  have h1 : g.restrictScalars K ∈ fixingSubgroup (fixedField (Subgroup.zpowers σ)) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ g.commutes ⟨x, hx⟩
  rwa [fixingSubgroup_fixedField] at h1


omit [IsGalois K L] in
theorem isMulCommutative_gal_fixedField_zpowers (σ : Gal(L/K)) :
    IsMulCommutative Gal(L/fixedField (Subgroup.zpowers σ)) := ⟨⟨fun a b ↦ by
  apply AlgEquiv.restrictScalars_injective K
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (restrictScalars_mem_zpowers σ a)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (restrictScalars_mem_zpowers σ b)
  have h : ∀ c d : Gal(L/fixedField (Subgroup.zpowers σ)),
      (c * d).restrictScalars K = c.restrictScalars K * d.restrictScalars K :=
    fun _ _ ↦ AlgEquiv.ext fun _ ↦ rfl
  rw [h, h, ← hi, ← hj, zpow_mul_comm]⟩⟩

theorem natCard_gal_fixedField_zpowers (σ : Gal(L/K)) :
    Nat.card Gal(L/fixedField (Subgroup.zpowers σ)) = orderOf σ := by
  rw [IsGalois.card_aut_eq_finrank, finrank_fixedField_eq_card, Nat.card_zpowers]

def deuringSet (σ : Gal(L/K)) : Set (HeightOneSpectrum (𝓞 (fixedField (Subgroup.zpowers σ)))) :=
  {u | u.asIdeal.inertiaDeg (𝓞 K) = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver u.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
      arithFrobAt (𝓞 (fixedField (Subgroup.zpowers σ))) Gal(L/fixedField (Subgroup.zpowers σ))
        w.asIdeal = galFixedZpowers σ}

theorem absNorm_eq_of_inertiaDeg_eq_one {E : Type*} [Field E] [NumberField E] [Algebra K E]
    (u : HeightOneSpectrum (𝓞 E)) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Ideal.absNorm u.asIdeal = Ideal.absNorm (HeightOneSpectrum.under (𝓞 K) u).asIdeal := by
  have h := Ideal.absNorm_pow_inertiaDeg (u.asIdeal.under (𝓞 K)) u.asIdeal
  rw [hf, pow_one] at h
  rw [HeightOneSpectrum.under_asIdeal, h]

end Sets

section Deuring

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem under_mem_deuringSet (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) (hσ : arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ) :
    HeightOneSpectrum.under (𝓞 (fixedField (Subgroup.zpowers σ))) w ∈ deuringSet σ := by
  set u := HeightOneSpectrum.under (𝓞 (fixedField (Subgroup.zpowers σ))) w with hudef
  have hD : MulAction.stabilizer Gal(L/K) w.asIdeal = Subgroup.zpowers σ := by
    rw [stabilizer_eq_zpowers_arithFrobAt (below K w) w he, hσ]
  have hwu : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  have huv : u.asIdeal.LiesOver (below K w).asIdeal :=
    ⟨by rw [hudef, HeightOneSpectrum.under_asIdeal, Ideal.under_under]; rfl⟩
  have hf := ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_stabilizer_le (Subgroup.zpowers σ)
    (below K w) u w hD.le
  refine ⟨hf.2, fun w' hw' ↦ ?_⟩
  have hw'w : w' = w := eq_of_under_eq_of_le_stabilizer (Subgroup.zpowers σ) w w' hD.ge
    (by rw [← hw'.over, ← hwu.over])
  subst w'
  refine ⟨he, arithFrobAt_eq_of_isArithFrobAt w ?_ ?_⟩
  · have := Ideal.ramificationIdx_tower (R := 𝓞 K) u.asIdeal w.asIdeal
    rw [he] at this
    exact (mul_eq_one.1 this.symm).2
  · rw [← isArithFrobAt_restrictScalars_iff (fixedField (Subgroup.zpowers σ)) w hf.2,
      restrictScalars_galFixedZpowers, ← hσ]
    exact IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal

theorem arithFrobAt_eq_of_mem_deuringSet (σ : Gal(L/K))
    {u : HeightOneSpectrum (𝓞 (fixedField (Subgroup.zpowers σ)))} (hu : u ∈ deuringSet σ)
    (w : HeightOneSpectrum (𝓞 L)) [hw : w.asIdeal.LiesOver u.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ := by
  obtain ⟨he, hF⟩ := hu.2 w hw
  refine ⟨he, arithFrobAt_eq_of_isArithFrobAt w he ?_⟩
  have hf : (w.asIdeal.under (𝓞 (fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 := by
    rw [← hw.over]
    exact hu.1
  have h0 := IsArithFrobAt.arithFrobAt (𝓞 (fixedField (Subgroup.zpowers σ)))
    Gal(L/fixedField (Subgroup.zpowers σ)) w.asIdeal
  rw [hF] at h0
  have h := (isArithFrobAt_restrictScalars_iff (fixedField (Subgroup.zpowers σ)) w hf
    (galFixedZpowers σ)).2 h0
  rwa [restrictScalars_galFixedZpowers] at h

theorem under_mem_chebotarevSet (σ : Gal(L/K))
    {u : HeightOneSpectrum (𝓞 (fixedField (Subgroup.zpowers σ)))} (hu : u ∈ deuringSet σ) :
    HeightOneSpectrum.under (𝓞 K) u ∈ chebotarevSet {τ : Gal(L/K) | IsConj σ τ} := by
  have : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  intro w hw
  obtain ⟨⟨w0, hw0⟩⟩ := nonempty_placesOver L u
  obtain ⟨he0, hF0⟩ := arithFrobAt_eq_of_mem_deuringSet σ hu w0
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) Gal(L/K)
    w0.asIdeal w.asIdeal (by rw [← hw.over, HeightOneSpectrum.under_asIdeal, hw0.over,
      Ideal.under_under])
  have hgw : w = g • w0 := HeightOneSpectrum.ext hg
  subst hgw
  refine ⟨by rw [ramificationIdx_smul, he0], ?_⟩
  rw [arithFrobAt_smul g w0 he0, hF0]
  exact isConj_iff.2 ⟨g, rfl⟩

end Deuring

section Count

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem card_fiber_deuringSet_mul_orderOf (σ : Gal(L/K)) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ chebotarevSet {τ : Gal(L/K) | IsConj σ τ}) :
    Nat.card {u // u ∈ deuringSet σ ∧ HeightOneSpectrum.under (𝓞 K) u = v} * orderOf σ =
      Nat.card (Subgroup.centralizer {σ}) := by
  have : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  set Z := Subgroup.centralizer {σ}

  obtain ⟨⟨w1, hw1⟩⟩ := nonempty_placesOver L v
  obtain ⟨he1, hc⟩ := hv w1 hw1
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  set w0 := c⁻¹ • w1 with hw0def
  have he0 : w0.asIdeal.ramificationIdx (𝓞 K) = 1 := by rw [ramificationIdx_smul, he1]
  have hF0 : arithFrobAt (𝓞 K) Gal(L/K) w0.asIdeal = σ := by
    rw [hw0def, arithFrobAt_smul _ _ he1, ← hc]
    group
  have hw0 : w0.asIdeal.LiesOver v.asIdeal :=
    (below_eq_iff _ _).1 ((below_smul _ _).trans ((below_eq_iff _ _).2 hw1))
  have hD0 : MulAction.stabilizer Gal(L/K) w0.asIdeal = Subgroup.zpowers σ := by
    rw [stabilizer_eq_zpowers_arithFrobAt (below K w0) w0 he0, hF0]
  have hle : Subgroup.zpowers σ ≤ Z :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)

  set S : Set (HeightOneSpectrum (𝓞 L)) :=
    {w | w.asIdeal.LiesOver v.asIdeal ∧ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = σ} with hSdef
  have heS : ∀ w ∈ S, w.asIdeal.ramificationIdx (𝓞 K) = 1 := fun w hw ↦ (hv w hw.1).1
  have hDS : ∀ w ∈ S, MulAction.stabilizer Gal(L/K) w.asIdeal = Subgroup.zpowers σ := by
    intro w hw
    rw [stabilizer_eq_zpowers_arithFrobAt (below K w) w (heS w hw), hw.2]

  have hSorb : S = MulAction.orbit Z w0 := by
    ext w
    constructor
    · rintro ⟨hwv, hwF⟩
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) Gal(L/K)
        w0.asIdeal w.asIdeal (hw0.over.symm.trans hwv.over)
      have hgw : w = g • w0 := HeightOneSpectrum.ext hg
      have hconj := arithFrobAt_smul g w0 he0
      rw [← hgw, hwF, hF0] at hconj
      have hgZ : g ∈ Z := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g * σ = (g * σ * g⁻¹) * g := by group
          _ = σ * g := by rw [← hconj]
      exact ⟨⟨g, hgZ⟩, hgw.symm⟩
    · rintro ⟨z, rfl⟩
      have hz : (z : Gal(L/K)) * σ = σ * z := Subgroup.mem_centralizer_singleton_iff.1 z.2
      refine ⟨(below_eq_iff _ _).1 ((below_smul (z : Gal(L/K)) w0).trans
        ((below_eq_iff _ _).2 hw0)), ?_⟩
      change arithFrobAt (𝓞 K) Gal(L/K) ((z : Gal(L/K)) • w0).asIdeal = σ
      rw [arithFrobAt_smul _ w0 he0, hF0, hz]
      group

  have hstab : MulAction.stabilizer Z w0 = (Subgroup.zpowers σ).subgroupOf Z := by
    ext z
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ← hD0, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact congrArg HeightOneSpectrum.asIdeal h
    · intro h
      exact HeightOneSpectrum.ext h
  have hcardS : Nat.card S * orderOf σ = Nat.card Z := by
    rw [hSorb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, ← Nat.card_zpowers,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ← hstab, mul_comm,
      Subgroup.card_mul_index]

  let f : S → {u // u ∈ deuringSet σ ∧ HeightOneSpectrum.under (𝓞 K) u = v} := fun w ↦
    ⟨HeightOneSpectrum.under (𝓞 (fixedField (Subgroup.zpowers σ))) w.1,
      under_mem_deuringSet σ w.1 (heS w.1 w.2) w.2.2,
      HeightOneSpectrum.ext (by
        rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
        exact w.2.1.over.symm)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h := congrArg (fun x ↦ x.1.asIdeal) hab
      simp only [f, HeightOneSpectrum.under_asIdeal] at h
      exact (Subtype.ext (eq_of_under_eq_of_le_stabilizer (Subgroup.zpowers σ) a.1 b.1
        (hDS a.1 a.2).ge h.symm)).symm
    · rintro ⟨u, hu, huv⟩
      obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L u
      obtain ⟨-, hF⟩ := arithFrobAt_eq_of_mem_deuringSet σ hu w
      have hwv : w.asIdeal.LiesOver v.asIdeal :=
        ⟨by rw [← huv, HeightOneSpectrum.under_asIdeal, hw.over, Ideal.under_under]⟩
      exact ⟨⟨w, hwv, hF⟩, Subtype.ext (HeightOneSpectrum.ext hw.over.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), hcardS]

end Count

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.HeckeTheoremScaling
section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem ofReal_inv_cpow_of_pos {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne), cpow_neg]

theorem globalZeta_comp_smul (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (a : IdeleGroup K) (s : ℂ) :
    globalZeta (fun y ↦ F (a • y)) χ s =
      (χ.toIdele a : ℂ)⁻¹ * ((ideleModule K a : ℝ) : ℂ) ^ (-s) * globalZeta F χ s := by
  unfold globalZeta
  have h := integral_mul_left_eq_self (μ := ideleMeasure K)
    (fun x : IdeleGroup K ↦ F (a • (x : 𝔸[K])) * (χ.toIdele x : ℂ) *
      ((ideleModule K x : ℝ) : ℂ) ^ s) a⁻¹
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  have h1 : a • ((a⁻¹ * x : IdeleGroup K) : 𝔸[K]) = (x : 𝔸[K]) := by
    rw [Units.smul_def, smul_eq_mul, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : ((ideleModule K (a⁻¹ * x) : ℝ) : ℂ) ^ s =
      ((ideleModule K a : ℝ) : ℂ) ^ (-s) * ((ideleModule K x : ℝ) : ℂ) ^ s := by
    rw [map_mul, map_inv, Positive.val_mul, Positive.coe_inv, ofReal_mul,
      mul_cpow_ofReal_nonneg (inv_nonneg.2 (ideleModule K a).2.le) (ideleModule K x).2.le,
      ofReal_inv_cpow_of_pos (ideleModule K a).2]
  beta_reduce
  rw [h1, h2]
  simp only [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
  ring

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def discrNormConductor : ℝ := |(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ)

theorem discrNormConductor_pos : 0 < χ.discrNormConductor := by
  refine mul_pos (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))) (Nat.cast_pos.2 ?_)
  exact Nat.pos_of_ne_zero fun h ↦ χ.conductor_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem discrNormConductor_inv : χ⁻¹.discrNormConductor = χ.discrNormConductor := by
  rw [discrNormConductor, discrNormConductor, conductor_inv]

theorem ideleModule_ofFinite_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    (ideleModule K (ofFinite δ) : ℝ) = χ.discrNormConductor⁻¹ := by
  have hI : χ.conductor * differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
    mul_ne_zero χ.conductor_ne_bot differentIdeal_ne_bot
  have hunit : idealUnit χ.conductor χ.conductor_ne_bot * differentUnit = idealUnit _ hI := by
    ext
    simp [idealUnit, differentUnit, FractionalIdeal.coeIdeal_mul]
  have hpos : ∀ v, 0 ≤ ord v (ofFinite δ) := fun v ↦ by
    rw [← count_toFractionalIdeal, hδ, hunit]
    change 0 ≤ FractionalIdeal.count K v
      (((χ.conductor * differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K))) : FractionalIdeal (𝓞 K)⁰ K)
    rw [count_coeIdeal_eq_multiplicity v hI]
    positivity
  have hideal : idealOfExponents (ordFinsupp K (ofFinite δ)) =
      χ.conductor * differentIdeal ℤ (𝓞 K) := by
    have h1 : toFractionalIdeal (ofFinite δ) =
        idealUnit _ (idealOfExponents_ne_bot (K := K) (n := ordFinsupp K (ofFinite δ)) hpos) := by
      rw [toFractionalIdeal_eq_iff]
      intro v
      exact (count_idealOfExponents (n := ordFinsupp K (ofFinite δ)) hpos v).symm
    rw [hδ, hunit] at h1
    exact FractionalIdeal.coeIdeal_injective (K := K) (congrArg Units.val h1).symm
  have hinf : infiniteModule (ofFinite δ) = 1 := by
    have e : ((ofFinite δ : IdeleGroup K) : 𝔸[K]).1 = 1 := by
      change ((toInfinite K (ofFinite δ) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1
      rw [toInfinite_ofFinite, Units.val_one]
    simp only [infiniteModule, e]
    exact Finset.prod_eq_one fun w _ ↦ by
      rw [show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  rw [ideleModule_apply, hinf, one_mul, finiteModule_ofFinite_eq hpos, hideal, map_mul,
    absNorm_differentIdeal K (𝓞 K), discrNormConductor, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs,
    mul_comm]

theorem globalZeta_adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (s : ℂ) :
    globalZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        globalZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hf : adelicFourier K χ.testFunction =
      fun y ↦ χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y) :=
    funext (χ.adelicFourier_testFunction hδ)
  have h1 : globalZeta (fun y ↦ χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y)) χ⁻¹ s =
      χ.fourierConst δ * globalZeta (fun y ↦ (χ⁻¹).testFunction (ofFinite δ • y)) χ⁻¹ s := by
    unfold globalZeta
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hf, h1, globalZeta_comp_smul, χ.ideleModule_ofFinite_of_toFractionalIdeal_eq hδ,
    ofReal_inv_cpow_of_pos χ.discrNormConductor_pos, neg_neg, χ.inv_toIdele, Circle.coe_inv, inv_inv]
  ring

theorem exists_inv_ne_one (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) :
    ∃ v : normOneSubgroup K, χ⁻¹.toIdele (v : IdeleGroup K) ≠ 1 := by
  obtain ⟨v, hv⟩ := hχ
  exact ⟨v, by rw [χ.inv_toIdele, ne_eq, inv_eq_one]; exact hv⟩

theorem inv_eq_cpow_of_forall {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∀ x : IdeleGroup K,
      ((χ⁻¹).toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ (((-τ : ℝ) : ℂ) * I) := fun x ↦ by
  rw [χ.inv_toIdele, Circle.coe_inv, hτ, ← cpow_neg]
  push_cast
  ring_nf

theorem differentiable_const_cpow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r : ℝ}
    (hr : 0 < r) : Differentiable ℂ fun s ↦ c * (r : ℂ) ^ s * f s :=
  ((differentiable_const c).mul
    (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 hr.ne')))).mul hf

theorem tateZeta_adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) (s : ℂ) :
    tateZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        tateZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hχ' := χ.exists_inv_ne_one hχ
  have h := eq_tateZeta_of_differentiable (adelicFourier_mem_schwartzBruhat χ.testFunction_mem) hχ'
    (G := fun s ↦ χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
      tateZeta (χ⁻¹).testFunction χ⁻¹ s)
    (differentiable_const_cpow_mul (differentiable_tateZeta (χ⁻¹).testFunction_mem hχ') _
      χ.discrNormConductor_pos)
    fun s hs ↦ by
      rw [tateZeta_eq_globalZeta (χ⁻¹).testFunction_mem _ hs,
        χ.globalZeta_adelicFourier_testFunction hδ]
  exact (congrFun h s).symm

theorem tateZeta_adelicFourier_testFunction_of_forall {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {s : ℂ} (hs₀ : s ≠ (τ : ℂ) * I) (hs₁ : s ≠ 1 + (τ : ℂ) * I) :
    tateZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        tateZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hτ' := χ.inv_eq_cpow_of_forall hτ
  have hpole : ∀ z : ℂ, z ≠ (τ : ℂ) * I → z ≠ 1 + (τ : ℂ) * I →
      z ≠ -(((-τ : ℝ) : ℂ) * I) ∧ z ≠ 1 - ((-τ : ℝ) : ℂ) * I := fun z h0 h1 ↦ by
    push_cast
    constructor
    · rw [neg_mul, neg_neg]; exact h0
    · rw [neg_mul, sub_neg_eq_add]; exact h1
  have hmem : s ∈ ({-(((-τ : ℝ) : ℂ) * I), 1 - ((-τ : ℝ) : ℂ) * I} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact hpole s hs₀ hs₁
  have h := eqOn_tateZeta_of_differentiableOn hτ'
    (adelicFourier_mem_schwartzBruhat χ.testFunction_mem)
    (G := fun s ↦ χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
      tateZeta (χ⁻¹).testFunction χ⁻¹ s)
    (fun z hz ↦ by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
      refine DifferentiableAt.differentiableWithinAt ?_
      exact ((differentiableAt_const _).mul ((differentiableAt_id).const_cpow
        (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).mul
        (differentiableAt_tateZeta hτ' (χ⁻¹).testFunction_mem hz.1 hz.2))
    fun s hs ↦ by
      rw [tateZeta_eq_globalZeta (χ⁻¹).testFunction_mem _ hs,
        χ.globalZeta_adelicFourier_testFunction hδ]
  exact (h hmem).symm

end HeckeCharacter

end

end GroundTheory.Global
end

