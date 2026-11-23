module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

theorem val_unif (P : HeightOneSpectrum (𝓞 E)) : P.valuation E ((Formalism.L2.Host.unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) :=
  (P.valuedAdicCompletion_eq_valuation' _).symm.trans (Formalism.L2.Host.unif_spec P)

theorem exists_unit_part (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    ∃ u : Eˣ, P.valuation E (u : E) = 1 ∧ k = Formalism.L2.Host.unif P ^ Formalism.L2.Host.ordF P k * u := by
  refine ⟨(Formalism.L2.Host.unif P ^ Formalism.L2.Host.ordF P k)⁻¹ * k, ?_, by rw [mul_inv_cancel_left]⟩
  have h0 : P.valuation E (k : E) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, val_unif,
    ← WithZero.exp_zsmul, ← WithZero.exp_neg, Formalism.L2.Host.ordF]
  conv_lhs => rw [← WithZero.exp_log h0, WithZero.log_exp, ← WithZero.exp_add]
  simp

theorem twVal_half (χ : Formalism.L2.Host.HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1)
    (k : Eˣ) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal χ (1 / 2) P k =
      (((χ.locK P (Formalism.L2.Host.unif P) : ℂˣ) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)) ^ Formalism.L2.Host.ordF P k := by
  obtain ⟨u, hu, hk⟩ := exists_unit_part P k
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  generalize Formalism.L2.Host.ordF P k = n at hk ⊢
  rw [hk, map_mul, h u hu, mul_one, map_zpow, Units.val_zpow_eq_zpow_val, mul_zpow]
  congr 1
  have hN : (0 : ℝ) ≤ (Nat.card (kP P) : ℕ) := Nat.cast_nonneg _
  rw [show Ideal.absNorm P.asIdeal = Nat.card (kP P) from Ideal.absNorm_eq_natCard _, ← Complex.ofReal_zpow, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hN, ← Real.rpow_intCast, ← Real.rpow_mul hN, Complex.ofReal_cpow hN]
  push_cast
  congr 1
  ring

end General

theorem locK_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hu : UnramEverywhere D c)
    (P : Pl D.host.E) (u : D.host.Eˣ) (h : P.valuation D.host.E (u : D.host.E) = 1) : χ.locK P u = 1 := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, hP, hQ⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have key : ∀ k : D.host.E, P.valuation D.host.E k = 1 → finPart D (locE D e k) ∈ intAE D := by
    intro k hk
    rw [h2]
    intro Q
    have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := h1 k
    have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (ι (finPart D (incA D k)) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
    rw [h5, h4]
    change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
    by_cases hQP : Q = P
    · subst hQP
      rw [hP, one_mul, add_sub_cancel]
      exact ((Q.valuedAdicCompletion_eq_valuation' k).trans hk).le
    · rw [hQ Q hQP, zero_mul, add_zero, map_one]
  have hinv : (((locU he.1 u)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((u⁻¹ : D.host.Eˣ) : D.host.E) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [locU_val, locE_mul_locE he.1]
    simp [locE]
  have h6 := hu (locU he.1 u) (by
    rw [locU_val, locE, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, hinf, zero_mul, add_zero])
    (key _ h) (by
      rw [hinv]
      refine key _ ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one])
  have h7 := hc.2 P e he u (locU he.1 u) rfl
  rw [h6] at h7
  exact Units.ext h7.symm

end GlobalTheory.EtaConjChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
section
namespace GlobalTheory.EtaConjExist

section General

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

theorem fin_supp {M : Type} [CommGroup M] (c : HeightOneSpectrum (𝓞 L) → M) {n : HeightOneSpectrum (𝓞 L) → ℤ}
    (h : {v | n v ≠ 0}.Finite) : (Function.mulSupport fun v => c v ^ n v).Finite :=
  h.subset fun v hv h0 => hv (by simp only [h0, zpow_zero])

noncomputable def idealChar (c : HeightOneSpectrum (𝓞 L) → ℂˣ) : Neutral.B1.Ideles L →* ℂˣ :=
  MonoidHom.mk' (fun a => ∏ᶠ v, c v ^ GlobalTheory.Idele.ord_vw (GlobalTheory.HeckeProduct.finPart L a) v) fun a b => by
    rw [← finprod_mul_distrib (fin_supp c (Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero _)))
      (fin_supp c (Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero _)))]
    refine finprod_congr fun v => ?_
    rw [map_mul, GlobalTheory.Idele.ord_vw_mul, zpow_add]

theorem idealChar_apply (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (a : Neutral.B1.Ideles L) :
    idealChar c a = ∏ᶠ v, c v ^ (-WithZero.log (Valued.v ((a : AdeleRing (𝓞 L) L).2 v))) := rfl

theorem idealChar_unit (c : HeightOneSpectrum (𝓞 L) → ℂˣ) {a : Neutral.B1.Ideles L} (ha : a ∈ unitIdl L) : idealChar c a = 1 := by
  rw [idealChar_apply]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [ha v, WithZero.log_one, neg_zero, zpow_zero]

theorem idealChar_local (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    idealChar c (Neutral.B1.localIdele L v x) = c v ^ (-WithZero.log (Valued.v (x : v.adicCompletion L))) := by
  rw [idealChar_apply, finprod_eq_single _ v, GlobalTheory.HeckeProduct.localIdele_snd_self]
  intro w hw
  rw [GlobalTheory.HeckeProduct.localIdele_snd_ne L v w hw, map_one, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_classChar (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (h : ∀ k : Lˣ, ∏ᶠ v, c v ^ Formalism.L2.Host.ordF v k = 1) :
    ∃ ξ : Formalism.L2.Host.HChar L, ξ.IsUnitary ∧ (∀ v, ξ.UnrAt v) ∧ ∀ v, ξ.val v = c v := by
  have hd : ∀ k : Lˣ, idealChar c (Neutral.B1.diagUnits L k) = 1 := fun k => by
    rw [idealChar_apply, ← h k]
    refine finprod_congr fun v => ?_
    have hk : Valued.v ((Neutral.B1.diagUnits L k : AdeleRing (𝓞 L) L).2 v) = v.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)
    rw [hk, Formalism.L2.Host.ordF]
  have hc : Continuous (idealChar c) := by
    refine continuous_of_continuousAt_one _ ?_
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.mem_nhds (unitIdl L).one_mem] with a ha
    exact (idealChar_unit c ha).symm
  refine ⟨⟨idealChar c, hc, hd⟩, fun x => ?_, fun v x hx => ?_, fun v => ?_⟩
  · have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
    obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (Neutral.B1.diagUnits L).range).pow_index_mem x)
    have e1 := congrArg (fun z => ((idealChar c z : ℂˣ) : ℂ)) e
    simp only [map_mul, map_pow, idealChar_unit c hu, hd, one_mul, Units.val_one, Units.val_pow_eq_pow_val] at e1
    exact Complex.norm_eq_one_of_pow_eq_one e1.symm this.index_ne_zero
  · refine (idealChar_local c v x).trans ?_
    rw [show Valued.v (x : v.adicCompletion L) = 1 from hx, WithZero.log_one, neg_zero, zpow_zero]
  · refine (idealChar_local c v _).trans ?_
    rw [show Valued.v ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = _ from Formalism.L2.Host.unif_spec v,
      WithZero.log_exp, neg_neg, zpow_one]

theorem finprod_sqrt [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Lˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 L), ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ Formalism.L2.Host.ordF v k) *
      ∏ i, ‖φ i (k : L)‖ = 1 := by
  have h1 := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h1
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) (k : L) ^ (InfinitePlace.mk (φ i)).mult = ‖φ i (k : L)‖ * ‖φ i (k : L)‖ := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq, sq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 L), FinitePlace.equivHeightOneSpectrum.symm v (k : L) =
      ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ Formalism.L2.Host.ordF v k *
        ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ Formalism.L2.Host.ordF v k := fun v => by
    have h0 : v.valuation L (k : L) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
    rw [← mul_zpow, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), inv_zpow',
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def,
      WithZeroMulInt.toNNReal_neg_apply _ h0, Formalism.L2.Host.ordF, neg_neg]
    push_cast
    congr 1
  have h4 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) =>
      ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ Formalism.L2.Host.ordF v k).Finite :=
    (GlobalTheory.HeckeProduct.finite_ordF k).subset fun v hv h0 => hv (by simp only [h0, zpow_zero])
  simp only [h2, h3] at h1
  rw [finprod_mul_distrib h4 h4, Finset.prod_mul_distrib] at h1
  refine (mul_self_eq_one_iff.1 (by linear_combination h1)).resolve_right fun h => ?_
  have : (0 : ℝ) ≤ -1 := h ▸ mul_nonneg (finprod_nonneg fun v => by positivity) (by positivity)
  linarith

theorem finprod_alg [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : Formalism.L2.Host.HChar L) (hu : ∀ v, χ.UnrAt v)
    (hi : χ.HasInf φ fun _ => 1) (w : HeightOneSpectrum (𝓞 L) → ℂˣ)
    (hw : ∀ v, (w v : ℂ) = χ.val v * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) : ℂ)) (k : Lˣ) :
    ((∏ᶠ v, w v ^ Formalism.L2.Host.ordF v k : ℂˣ) : ℂ) * ∏ i, φ i (k : L) = 1 := by
  have e5 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e5
  have e6 := finprod_sqrt φ hφ k
  have hs : ∀ {M : Type} [CommGroupWithZero M] (f : HeightOneSpectrum (𝓞 L) → M), ∏ᶠ v, f v ^ Formalism.L2.Host.ordF v k =
      ∏ v ∈ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset, f v ^ Formalism.L2.Host.ordF v k := fun f =>
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      exact fun h0 => hv (by simp only [h0, zpow_zero])
  have hs' : ∀ (f : HeightOneSpectrum (𝓞 L) → ℂˣ), ((∏ᶠ v, f v ^ Formalism.L2.Host.ordF v k : ℂˣ) : ℂ) =
      ∏ v ∈ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset, (f v : ℂ) ^ Formalism.L2.Host.ordF v k := fun f => by
    rw [finprod_eq_prod_of_mulSupport_subset (s := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset) _ fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      exact fun h0 => hv (by simp only [h0, zpow_zero])]
    simp
  have e7 := congrArg Units.val e5
  have e8 := congrArg Complex.ofReal e6
  rw [Units.val_mul, hs', hi k, Units.val_one] at e7
  rw [hs] at e8
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_zpow, Complex.ofReal_one] at e8
  simp only [zpow_one, Finset.prod_div_distrib] at e7
  have h0 : ∏ i, ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one e8
  rw [hs']
  simp only [hw, mul_zpow, Finset.prod_mul_distrib]
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq h0] at e7
  rw [mul_right_comm, mul_comm _ (∏ i, φ i (k : L)), e7, mul_comm, e8]

theorem finprod_quot {M : Type} [Field M] (e σ : M →+* ℂ) (y : HeightOneSpectrum (𝓞 L) → Mˣ) (k : Lˣ) (n : M)
    (h : ((∏ᶠ v, Units.map e.toMonoidHom (y v) ^ Formalism.L2.Host.ordF v k : ℂˣ) : ℂ) * e n = 1) (hn : σ n = e n) :
    ∏ᶠ v, (Units.map σ.toMonoidHom (y v) / Units.map e.toMonoidHom (y v)) ^ Formalism.L2.Host.ordF v k = 1 := by
  have hf := GlobalTheory.HeckeProduct.finite_ordF k
  have hm : ∀ f : M →+* ℂ, ∏ᶠ v, Units.map f.toMonoidHom (y v) ^ Formalism.L2.Host.ordF v k =
      Units.map f.toMonoidHom (∏ᶠ v, y v ^ Formalism.L2.Host.ordF v k) := fun f => by
    rw [MonoidHom.map_finprod _ (fin_supp y hf)]
    simp only [map_zpow]
  simp only [div_zpow]
  rw [finprod_div_distrib (fin_supp _ hf) (fin_supp _ hf), hm, hm, div_eq_one]
  rw [hm] at h
  have h1 : ((∏ᶠ v, y v ^ Formalism.L2.Host.ordF v k : Mˣ) : M) * n = 1 := e.injective (by rw [map_mul, map_one]; exact h)
  have h2 := congrArg σ h1
  rw [map_mul, map_one, hn, ← h] at h2
  exact Units.ext (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h) h2)

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ)
    (hu : ∀ P, χ.UnrAt P) : UnramEverywhere D c := by
  intro x hx h4 h5
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  apply Circle.ext
  rw [GlobalTheory.Mem.EtaTilde.val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu x hx, Circle.coe_one,
    Units.val_eq_one]
  refine finprod_eq_one_of_forall_eq_one fun P => ?_
  have e := GlobalTheory.Mem.EtaTilde.val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
  have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    refine le_antisymm ((h2 _).1 h4 P) ?_
    rw [← e']
    exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
  rw [e1, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_norm (D : D7) (k : D.host.E) :
    ∃ n ∈ D.host.K, D.what₂.embLL (D.embE n) = ∏ g, Formalism.L2.Host.embPsi D.host g k := by
  have hE := D.host.hostE_isGalois
  have h := Algebra.norm_eq_prod_automorphisms D.host.K k
  refine ⟨_, (Algebra.norm D.host.K k).2, (DFunLike.congr_fun D.embE_φ₀ _).trans ?_⟩
  change D.host.φ₀ (algebraMap D.host.K D.host.E _) = _
  rw [h, map_prod]
  exact (Fintype.prod_bijective _ (GlobalTheory.InducedType.galK_bijective D.host) _ _ fun _ => rfl).symm

theorem exists_conj {D : D7} (η : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq η χ)
    (hχ : Formalism.L2.Host.IsEtaT D.host χ)
    (hy : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ y : D.what₂.LL,
      D.what₂.embLL y = χ.val P * (((Real.sqrt (Ideal.absNorm P.asIdeal : ℕ))⁻¹ : ℝ) : ℂ))
    (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) : ∃ η', IsEtaConj σ η η' := by
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨_, -, hd, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  choose y hy using hy
  have hy0 : ∀ P, D.what₂.embLL (y P) ≠ 0 := fun P => by
    have : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℕ) :=
      Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
    rw [hy]
    exact mul_ne_zero (Units.ne_zero _) (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 this).ne'))
  let u : HeightOneSpectrum (𝓞 D.host.E) → D.what₂.LLˣ := fun P => Units.mk0 (y P) ((map_ne_zero _).1 (hy0 P))
  obtain ⟨ξ, x1, x2, x3⟩ := exists_classChar
    (fun P => Units.map σ.toMonoidHom (u P) / Units.map D.what₂.embLL.toMonoidHom (u P)) fun k => by
      obtain ⟨n, hn, hn'⟩ := exists_norm D k
      refine finprod_quot _ _ u k (D.embE n) ?_ (hσ n hn)
      rw [hn']
      exact finprod_alg _ hd.bij χ hχ.unr hχ.inf _ hy k
  obtain ⟨c, hc'⟩ := GlobalTheory.CharTransport.exists_chrEq D (χ * ξ) fun x => by
    change ‖((χ.1 x * ξ.1 x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, hχ.unitary x, x1 x, one_mul]
  have hcard (P : HeightOneSpectrum (𝓞 D.host.E)) : Nat.card (kP P) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨c, hc'.1, unram_of_chrEq hc' fun P x hx => ?_, fun P e he x hx => ⟨y P, ?_, ?_⟩⟩
  · change χ.loc P x * ξ.loc P x = 1
    rw [hχ.unr P x hx, x2 P x hx, one_mul]
  · rw [hc.2 P e he _ x hx]
    rw [hcard]
    exact hy P
  · rw [hcard]
    have h1 : ((c x : Circle) : ℂ) = ((χ.val P * ξ.val P : ℂˣ) : ℂ) := hc'.2 P e he _ x hx
    rw [h1, x3, Units.val_mul, mul_right_comm, Units.val_div_eq_div_val]
    have h2 := hy P
    refine Eq.trans ?_ (congrArg (· * (σ (y P) / D.what₂.embLL (y P))) h2)
    exact (mul_div_cancel₀ _ (hy0 P)).symm

end GlobalTheory.EtaConjExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHWOfFd
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem exists_isHW_of_fd : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act →
    (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∀ U : Submodule ℂ V, U ≠ ⊥ →
    FiniteDimensional ℂ U → KStable act U → ∃ (μ : Ix p q → ℚ) (v : V), v ∈ U ∧ IsHW act μ v := by
  intro p q V _ _ act hL hd U hU hfd hK
  exact GlobalTheory.BlockReps.exists_hw (fun Y Z _ _ => hL Y Z) hK (fun v _ => hd v) hU

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut

open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.SplitScalar

variable {D : D7}

def IsHalfIdem (D : D7) (ε : AE D) : Prop :=
  ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧
    (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧
    ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0

theorem exists_isHalfIdem (D : D7) : ∃ ε, IsHalfIdem D ε := _root_.GlobalTheory.HalfIdem.exists_half_idem D

theorem finRat_eq (S T : HSp D) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T x = (1 - realIdem D) • (ratW T S x : WO S T) := by
  funext i j
  refine adele_ext ?_ ?_
  · exact (congrFun (congrFun (finRat_inf S T x) i) j).trans (congrFun (congrFun (fin_smul_fin (ratW T S x)) i) j).symm
  · show finPart D (ratW T S x i j) = finPart D ((1 - realIdem D) * ratW T S x i j)
    rw [RingHom.map_mul, RingHom.map_sub, finPart_realIdem, RingHom.map_one, sub_zero, one_mul]

theorem finRat_smul (S T : HSp D) (c : D.host.E) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T (c • x) = incA D c • finRat S T x := by
  rw [finRat_eq, finRat_eq, smul_comm]
  congr 1
  funext i j
  exact (incA D).map_mul c (x i j)

def latQ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {x | finRat S T x ∈ latO S T LS LT fun _ => True}
  add_mem' {x y} hx hy := by
    show finRat S T (x + y) ∈ latO S T LS LT fun _ => True
    rw [map_add (f := _)]
    exact add_mem hx hy
  zero_mem' := by
    show finRat S T 0 ∈ latO S T LS LT fun _ => True
    rw [map_zero]
    exact zero_mem _
  smul_mem' r x hx := by
    show finRat S T ((r : D.host.E) • x) ∈ latO S T LS LT fun _ => True
    rw [finRat_smul]
    exact GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ _ (finPart_intA r) _ hx

theorem mem_latQ {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} :
    x ∈ latQ S T LS LT ↔ finRat S T x ∈ latO S T LS LT fun _ => True := Iff.rfl

def gamQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  ψ (symplO S T (finRat S T x) (finRat S T y))


open Classical in
def chiLat (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (x : WO S T) : ℂ :=
  if (1 - realIdem D) • x ∈ latO S T LS LT (fun _ => True) then
    ψ (symplOH S T (intA D w • (1 - realIdem D) • x) ((1 - realIdem D) • x)) else 0

def serO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : RW T S) : WO S T → ℂ :=
  GlobalTheory.HeisenbergGaussianSeries.series (G := WO S T) (piW θ T S) (iotaW σ T S) (fun x y => ψ (symplOH S T x y))
    (omO S T) (jO S T sS sT) (ratL T S) (chiLat ψ S T LS LT w) a

def actR (S T : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : RW T S :=
  fun τ => (b τ * Matrix.of (v τ) * a τ : Matrix (Fin T.rank) (Fin S.rank) ℂ)

def gaussR (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I) * (omO S T (actR S T a b v) v : ℝ)) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (actR S T a b v - v) (jO S T sS sT (actR S T a b v - v)) : ℝ))

def sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    Module.End K (Matrix (Fin m) (Fin n) K) where
  toFun x := b * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem sandw_apply {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K)
    (x : Matrix (Fin m) (Fin n) K) : sandw b a x = b * x * a := rfl

theorem toMatrix_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.toMatrix (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin m) (Fin n)) (sandw b a) = b ⊗ₖ aᵀ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, sandw_apply]
  have : ∀ x : Matrix (Fin m) (Fin n) K, (Matrix.stdBasis K (Fin m) (Fin n)).repr x (i, j) = x i j := fun x => by
    simp [Matrix.stdBasis]
  rw [this]
  simp [Matrix.mul_apply, Matrix.single, ite_and]

theorem det_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a) = (b ⊗ₖ aᵀ).det := by
  rw [← toMatrix_sandw, LinearMap.det_toMatrix]

theorem det_sandw_sub_one {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a - 1) = (b ⊗ₖ aᵀ - 1).det := by
  rw [← toMatrix_sandw, ← LinearMap.det_toMatrix (Matrix.stdBasis K (Fin m) (Fin n)), map_sub, LinearMap.toMatrix_one]

end GlobalTheory.RatAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

theorem IsMultIP₂ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (x y : H.H) :
    ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := by
  have h1 : ∀ x y : H.H, inner ℂ x y ≠ 0 → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := fun x y hxy => by
    by_contra hc
    apply hxy
    rw [h, ipM, dite_eq_right hc, mul_zero]
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, fun v v' => by simp⟩
  by_cases hxy : inner ℂ x y = 0
  · obtain ⟨c, hc⟩ := h1 x (x + y) (by rw [inner_add_right, hxy, add_zero]; exact inner_self_ne_zero.2 hx)
    obtain ⟨c', hc'⟩ := h1 x x (inner_self_ne_zero.2 hx)
    refine ⟨c - c', fun v v' => ?_⟩
    have e : (fun g => star (H.e x v g) * H.e y v' g) =
        fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g := by
      funext g; simp [mul_add]
    rw [e]
    exact ⟨(hc v v').1.sub (hc' v v').1, by rw [integral_sub (hc v v').1 (hc' v v').1, (hc v v').2, (hc' v v').2, sub_mul]⟩
  · exact h1 x y hxy

theorem schurMult_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R h i σ _ _ _ T hT T' hT'
  obtain ⟨-, hr, hip⟩ := h i σ
  have hT1 : T ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT
  have hT2 : T' ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT'
  obtain ⟨x, rfl⟩ := hT1
  obtain ⟨y, rfl⟩ := hT2
  exact IsMultIP₂ (R.HW i σ) hip x y

end GlobalTheory.LiftLower

end
end

