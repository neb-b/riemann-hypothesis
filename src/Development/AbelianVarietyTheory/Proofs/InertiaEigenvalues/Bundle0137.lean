module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitTraceFormDiscrUnramifiedExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (π : K.O) (π' : K'.O),
      algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) →
      IsLocalRing.maximalIdeal K.O = Ideal.span {π} →
      IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∀ w : Module.Basis (Fin d) K.E K'.E,
         (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
           ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) →
         ∃ u : K.O, IsUnit u ∧
           algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det) := by
  intro K K' d φ _ π π' hππ' hm hm'
  let : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  have hdiscr : ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u =
      (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det := by
    have hj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
    have hi : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
    have hφ : ∀ e : K.E, φ e = algebraMap K.E K'.E e := fun _ => rfl

    have hlift : ∀ a : K.O, φ (algebraMap K.O K.E a) ∈ (algebraMap K'.O K'.E).range := by
      intro a
      apply (hw _).2
      intro k
      obtain ⟨c, hc⟩ := (hw 1).1 ⟨1, map_one _⟩ k
      refine ⟨a * c, ?_⟩
      have h1 : φ (algebraMap K.O K.E a) = (algebraMap K.O K.E a) • (1 : K'.E) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hc]
    let e : K'.O ≃+* (algebraMap K'.O K'.E).range :=
      RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
        ⟨fun x y h => hj (congrArg Subtype.val h), (algebraMap K'.O K'.E).rangeRestrict_surjective⟩
    let ι : K.O →+* K'.O :=
      e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift)
    have hι : ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
      intro a
      exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift a))
    let : Algebra K.O K'.O := ι.toAlgebra
    have hsm : ∀ (a : K.O) (y : K'.O),
        algebraMap K'.O K'.E (a • y) = algebraMap K.O K.E a • algebraMap K'.O K'.E y := by
      intro a y
      rw [Algebra.smul_def, map_mul, Algebra.smul_def]
      exact congrArg (· * _) (hι a)
    have hsum : ∀ (g : Fin d → K.O) (v : Fin d → K'.O),
        algebraMap K'.O K'.E (∑ k, g k • v k) = ∑ k, algebraMap K.O K.E (g k) • algebraMap K'.O K'.E (v k) := by
      intro g v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => hsm _ _

    have hw1 : ∀ k, ∃ y : K'.O, algebraMap K'.O K'.E y = w k := by
      intro k
      apply (hw _).2
      intro m
      refine ⟨if m = k then 1 else 0, ?_⟩
      rw [w.repr_self, Finsupp.single_apply]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    choose bv hbv using hw1
    have hcoord : ∀ (y : K'.O) (k : Fin d), ∃ a : K.O, algebraMap K.O K.E a = w.repr (algebraMap K'.O K'.E y) k :=
      fun y => (hw _).1 ⟨y, rfl⟩
    choose c hc using hcoord
    have hli : LinearIndependent K.O bv := by
      rw [Fintype.linearIndependent_iff]
      intro g hg k
      have h1 := congrArg (algebraMap K'.O K'.E) hg
      rw [hsum, map_zero] at h1
      simp only [hbv] at h1
      have h2 := (Fintype.linearIndependent_iff.1 w.linearIndependent) _ h1 k
      exact hi (by rw [h2, map_zero])
    have hsp : ⊤ ≤ Submodule.span K.O (Set.range bv) := by
      intro y _
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨c y, hj ?_⟩
      rw [hsum]
      simp only [hbv, hc]
      exact w.sum_repr _
    let b : Module.Basis (Fin d) K.O K'.O := Module.Basis.mk hli hsp
    have hb : ∀ k, algebraMap K'.O K'.E (b k) = w k := fun k => by
      rw [Module.Basis.mk_apply]; exact hbv k
    have hrep : ∀ y k, algebraMap K.O K.E (b.repr y k) = w.repr (algebraMap K'.O K'.E y) k := by
      intro y k
      conv_rhs => rw [← b.sum_repr y, hsum]
      simp only [hb]
      rw [w.repr_sum_self]

    have hTr : ∀ y, algebraMap K.O K.E (Algebra.trace K.O K'.O y) =
        Algebra.trace K.E K'.E (algebraMap K'.O K'.E y) := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace w, Matrix.trace, Matrix.trace,
        map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
        Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hrep, map_mul, hb]

    have hιπ : ι π = π' := hj (by rw [hι, hππ'])
    have hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
      rw [hm, Ideal.map_span, Set.image_singleton]
      have h1 : algebraMap K.O K'.O π = π' := hιπ
      rw [h1, ← hm']
      exact IsLocalRing.maximalIdeal.isMaximal _
    refine ⟨Algebra.discr K.O b, ResDisc.isUnit_discr_of_isMaximal_map b hmax, ?_⟩
    rw [Algebra.discr_def, RingHom.map_det]
    congr 1
    ext k m
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Matrix.of_apply, hTr, map_mul, hb]
  exact hdiscr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegrandIsLocallyConstantCo
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbTest

theorem eta_eq_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  unfold eta
  by_cases hx : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [if_pos hx, if_pos (h ▸ hx)]
  · rw [if_neg hx, if_neg (h ▸ hx)]

theorem isLocallyConstant_eta_comp {X F : Type} [TopologicalSpace X] [NormedField F] [IsUltrametricDist F]
    (h : X → F) (hc : Continuous h) (h0 : ∀ x, h x ≠ 0) : IsLocallyConstant (fun x => eta (h x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : 0 < ‖h x‖ := norm_pos_iff.mpr (h0 x)
  have hev : ∀ᶠ y in 𝓝 x, dist (h y) (h x) < ‖h x‖ := (hc.tendsto x) (Metric.ball_mem_nhds _ hx)
  filter_upwards [hev] with y hy
  apply eta_eq_of_norm_eq
  rw [dist_eq_norm] at hy
  have hy' : ‖h x - h y‖ < ‖h x‖ := by rwa [norm_sub_rev]
  have e1 : ‖h y‖ ≤ max ‖h y - h x‖ ‖h x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h y - h x) (h x)
  have e2 : ‖h x‖ ≤ max ‖h x - h y‖ ‖h y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h x - h y) (h y)
  apply le_antisymm
  · exact e1.trans (max_le hy.le le_rfl)
  · rcases le_total ‖h x - h y‖ ‖h y‖ with hh | hh
    · exact e2.trans (max_le hh le_rfl)
    · exact absurd (e2.trans (max_le le_rfl hh)) (not_le.mpr hy')

theorem continuous_act {r : ℕ} {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] (Y : Gl r k) :
    Continuous (fun g : GL (Fin r) k => act g Y) := by
  unfold act
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const))
  · exact (Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv
  · exact Units.continuous_val.matrix_mulVec continuous_const
  · exact continuous_const.matrix_vecMul Units.continuous_coe_inv

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem continuous_actU {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [ContinuousStar E] (X : Hn r F E) :
    Continuous (fun g : Matrix.unitaryGroup (Fin r) E => actU g X) := by
  unfold actU
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
  · exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul continuous_subtype_val.star
  · exact continuous_subtype_val.matrix_mulVec continuous_const

end GlobalTheory.JR.OrbTest

namespace GlobalTheory.JR.OrbTest

theorem isTest_orbG_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f' : Gl r F → ℂ) (hf : IsTest f') (Y : Gl r F)
    (hY : Delta (inv Y) ≠ 0) :
    IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y)) := by
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨-, hL1b, hL1c, hL1d, hL1e⟩ := _root_.GlobalTheory.JR.normalForm_invariants F r
  obtain ⟨hL6a, hL6b⟩ := _root_.GlobalTheory.JR.transfer_factor_lemma F r
  obtain ⟨-, -, -, hL4⟩ := _root_.GlobalTheory.JR.OrbitProper.main F E r
  have hC : (Cm Y).det ≠ 0 := by
    intro h0; apply hY; rw [Delta, ← hL1c Y, Matrix.det_mul, h0, zero_mul]
  have hld : (fun g : GL (Fin r) F => lastDet (act g Y)) = fun g =>
      (-1) ^ r * ((Cm Y).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) := by
    funext g; rw [hL6a, hL6b, Matrix.det_mul]
  refine ⟨?_, ?_⟩
  · refine IsLocallyConstant.comp₂ (hf.1.comp_continuous (continuous_act Y)) ?_ (fun a b => a * b)
    show IsLocallyConstant (fun g : GL (Fin r) F => eta (lastDet (act g Y)))
    refine isLocallyConstant_eta_comp (fun g : GL (Fin r) F => lastDet (act g Y)) ?_ ?_
    · rw [hld]
      exact continuous_const.mul (continuous_const.mul Units.continuous_coe_inv.matrix_det)
    · intro g
      rw [show lastDet (act g Y) = _ from congrFun hld g]
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hC ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit).ne_zero
  · have ha : Delta (inv (sec (inv Y))) ≠ 0 := by rw [hL1b]; exact hY
    obtain ⟨g₀, ⟨hg₀, -⟩, -⟩ := hL1e (sec (inv Y)) Y ha (hL1b _).symm
    have hS : IsCompact {h : GL (Fin r) F | act h (sec (inv Y)) ∈ tsupport f'} := by
      have := hL4 (tsupport f') {inv Y} hf.2 isCompact_singleton (by rintro b rfl; exact hY)
      convert this.image continuous_fst using 1
      ext h; constructor
      · intro hh; exact ⟨(h, inv Y), ⟨rfl, hh⟩, rfl⟩
      · rintro ⟨⟨h', a'⟩, ⟨ha', hc⟩, rfl⟩
        simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
    have hK : IsCompact {g : GL (Fin r) F | act g Y ∈ tsupport f'} := by
      have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
      convert this using 1
      ext g; simp [Homeomorph.coe_mulRight, hL1d, hg₀]
    refine HasCompactSupport.intro' hK ((isClosed_tsupport f').preimage (continuous_act Y)) ?_
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [image_eq_zero_of_notMem_tsupport hg, zero_mul]

theorem isTest_orbU_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f : Hn r F E → ℂ) (hf : IsTest f) (a : Inv r F)
    (X : Hn r F E) (ha : Delta a ≠ 0) (hX : HasInv X a) :
    IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  haveI : ContinuousStar E := ⟨by
    have : Continuous (starAddEquiv : E ≃+ E) :=
      AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1
        (fun x => by rw [starAddEquiv_apply, Unram.norm_star (F := F), one_mul])
    exact this⟩
  obtain ⟨-, -, hL5c, -⟩ := _root_.GlobalTheory.JR.HermInv.herm_invariants F E r
  obtain ⟨-, hL5iv⟩ := _root_.GlobalTheory.JR.image_openClosed_section F E r a ha
  obtain ⟨Ω, s, -, -, haΩ, -, hs, hprop⟩ := hL5iv ⟨X, hX⟩
  obtain ⟨g₀, hg₀, -⟩ := hL5c (s a) X a ha (hs a haΩ).2 hX
  refine ⟨hf.1.comp_continuous (continuous_actU X), ?_⟩
  have hS : IsCompact {h : Matrix.unitaryGroup (Fin r) E | actU h (s a) ∈ tsupport f} := by
    have h1 := (hprop (tsupport f) hf.2).inter_right (isClosed_univ.prod (isClosed_singleton (x := a)))
    convert h1.image continuous_fst using 1
    ext h; constructor
    · intro hh; exact ⟨(h, a), ⟨⟨haΩ, hh⟩, Set.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨h', a'⟩, ⟨⟨-, hc⟩, -, ha'⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
  have hK : IsCompact {g : Matrix.unitaryGroup (Fin r) E | actU g X ∈ tsupport f} := by
    have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
    convert this using 1
    ext g; simp [Homeomorph.coe_mulRight, actU_mul, hg₀]
  refine HasCompactSupport.intro' hK ((isClosed_tsupport f).preimage (continuous_actU X)) ?_
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  exact image_eq_zero_of_notMem_tsupport hg

end GlobalTheory.JR.OrbTest


open GlobalTheory.JR.OrbTest in
theorem GlobalTheory.JR.orb_integrand_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  intro F E _ _ _ _ _ r _
  exact ⟨fun f' hf Y hY => isTest_orbG_integrand F E r f' hf Y hY,
    fun f hf a X ha hX => isTest_orbU_integrand F E r f hf a X ha hX⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorLinearDescentPointOne
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem eta_inv_eq {F : Type} [NormedField F] (x : F) : eta x⁻¹ = eta x := by
  have key : (∃ y : F, ‖x⁻¹‖ = ‖y‖ ^ 2) ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y⁻¹, ?_⟩
      rw [norm_inv] at hy
      rw [norm_inv, inv_pow, ← hy, inv_inv]
    · rintro ⟨y, hy⟩
      exact ⟨y⁻¹, by rw [norm_inv, norm_inv, inv_pow, hy]⟩
  unfold eta
  by_cases h : ∃ y : F, ‖x‖ = ‖y‖ ^ 2
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

theorem eta_neg_one_pow {F : Type} [NormedField F] (r : ℕ) : eta ((-1 : F) ^ r) = 1 := by
  unfold eta
  rw [if_pos]
  exact ⟨1, by simp⟩

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem row_pow (hG : A.IsGen τ p) (c : A.K) (n : ℕ) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* (companion p) ^ n =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ n * c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ih, ← leftMul_tau A hG, row_mul]
    funext j
    congr 2
    ring

theorem Cm_pt_one (hG : A.IsGen τ p) (lam : F) (a : A.K) :
    Cm (pt A hG lam 1 a) = Algebra.traceMatrix F (bas A hG) * Algebra.leftMulMatrix (bas A hG) a := by
  ext i j
  have h1 : Cm (pt A hG lam 1 a) i j = Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ (i : ℕ) * a)) := by
    simp only [Cm, pt, Matrix.of_apply]
    rw [row_pow A hG]
  have h2 := congrFun (row_mul A hG a (τ ^ (i : ℕ))) j
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [h1, Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bas_apply]
  rw [mul_comm (τ ^ (i : ℕ)) a, ← h2]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm (τ ^ (i : ℕ))]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem omega_pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F),
    ∃ κ₀ : ℂ, ∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F,
      omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a := by
  intro F E _ _ _ _ _ A r τ p hG lam
  obtain ⟨hmul, -, -, -⟩ := _root_.GlobalTheory.EtaChar.main F E
  have hnd := (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.1
  have hT : (Algebra.traceMatrix F (bas A hG)).det ≠ 0 := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (bas A hG)] at hnd
    convert hnd using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  refine ⟨eta (Algebra.traceMatrix F (bas A hG)).det, fun a ha g => ?_⟩
  have hL := _root_.GlobalTheory.JR.transfer_factor_lemma F r
  have hdet : (g : Matrix (Fin r) (Fin r) F).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hg : (g : Matrix (Fin r) (Fin r) F).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hginv := eq_inv_of_mul_eq_one_right hdet
  have hna : Algebra.norm F a ≠ 0 := (ha.map (Algebra.norm F)).ne_zero
  have hr : (-1 : F) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  unfold omega Et.etaK
  rw [hL.1, hL.2, Cm_pt_one, Matrix.det_mul, Matrix.det_mul, ← Algebra.norm_eq_matrix_det, hginv,
    hmul _ _ hr (mul_ne_zero (mul_ne_zero hT hna) (inv_ne_zero hg)),
    hmul _ _ (mul_ne_zero hT hna) (inv_ne_zero hg), hmul _ _ hT hna, eta_neg_one_pow, eta_inv_eq]
  ring

end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LetterSandwichOfFrobMatrices
section
noncomputable section

namespace GlobalTheory.WachLettersCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

attribute [local instance] letterModule

theorem mul_letE (i : ZMod n) (a : LetA O n) : a * letE i = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  rw [mul_letE]; simp [letE]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem letE_smul_mem (i : ZMod n) {x : W.DD T} (hx : x ∈ W.N T) :
    (letE i : LetA O n) • x ∈ W.Nl T i := ⟨x, hx, rfl⟩

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this


include W in
theorem neZero_letters : NeZero n := by
  have := PD.finK₀
  exact ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩

theorem isUnit_Q : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    have h1 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simpa [letπ, LocWach.q] using W.q₀_def
    set x := algebraMap (LetA O n) W.EE letπ with hx
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : W.EE) x
    obtain ⟨u, hu⟩ : IsUnit (x ^ PD.p) := W.EE_π.pow _
    have := W.EE_complete
    have hj : ((PD.p : ℕ) : W.EE) ∈ Ideal.jacobson (⊥ : Ideal W.EE) :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
        (Ideal.mem_span_singleton_self _)
    have h2 := (Ideal.mem_jacobson_bot.1 hj) (x * r * (↑u⁻¹ : W.EE))
    have h3 : x * algebraMap (LetA O n) W.EE W.q =
        (((PD.p : ℕ) : W.EE) * (x * r * (↑u⁻¹ : W.EE)) + 1) * u := by
      rw [hx, ← map_mul, h1, map_sub, map_pow, map_add (f := _), map_one, ← hx, hr, ← hu]
      have := u.inv_mul
      linear_combination (-((PD.p : ℕ) : W.EE) * x * r) * this
    exact isUnit_of_mul_isUnit_right (h3 ▸ h2.mul u.isUnit)
  have key : ∀ k : ℕ, IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) W.q)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      rw [pow_succ', AlgHom.mul_apply]
      have := W.φE_ext ((W.φA ^ k) W.q)
      exact this ▸ ih.map W.φE
  exact key _

theorem Q_pow_smul_cancel (m : ℕ) {x y : W.DD T} (h : W.Q ^ m • x = W.Q ^ m • y) : x = y := by
  rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (W.Q ^ m) y, map_pow] at h
  exact ((isUnit_Q W).pow m).smul_left_cancel.1 h

variable {W T}

variable (W T)

end Generic

end GlobalTheory.WachLettersCompare
end
end

