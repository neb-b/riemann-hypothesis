module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidue
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameSplitChar

open GlobalTheory.CharLocProd

theorem locK_eq_of_congr {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    (P : HeightOneSpectrum (𝓞 L)) (ht : χ.TameAt P) (k b : Lˣ) (hb : P.valuation L (b : L) = 1)
    (h : Valued.v (algebraMap L (P.adicCompletion L) (k : L) - algebraMap L (P.adicCompletion L) (b : L)) ≤
      WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.locK P b := by
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have e : ((Formalism.L2.Host.atFin P (k * b⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) - 1 =
      (algebraMap L (P.adicCompletion L) (k : L) - algebraMap L (P.adicCompletion L) (b : L)) *
        algebraMap L (P.adicCompletion L) ((b : L)⁻¹) := by
    show algebraMap L (P.adicCompletion L) ((k * b⁻¹ : Lˣ) : L) - 1 = _
    rw [sub_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ b.ne_zero, map_one, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : Valued.v (((Formalism.L2.Host.atFin P (k * b⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) - 1) ≤
      WithZero.exp (-1 : ℤ) := by
    rw [e, map_mul, val_algebraMap, map_inv₀, hb, inv_one, mul_one]
    exact h
  have h2 : χ.locK P (k * b⁻¹) = 1 := by
    refine ht _ ?_ h1
    show Valued.v _ = 1
    rw [← map_one (Valued.v : Valuation (P.adicCompletion L) _)]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [map_one]
    exact h1.trans_lt hlt
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2

theorem idem_apply {L : Type} [Field L] [NumberField L] (ε : FiniteAdeleRing (𝓞 L) L) (hε : ε * ε = ε)
    (Q : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L, x ≠ 0 → (x ∈ Q.asIdeal ↔
      ¬ ∀ R, Valued.v (CharLocProd.evalAt R (ε * algebraMap L (FiniteAdeleRing (𝓞 L) L) ((x : L)⁻¹))) ≤ 1)) :
    CharLocProd.evalAt Q ε = 1 ∧ ∀ R, R ≠ Q → CharLocProd.evalAt R ε = 0 := by
  have h01 : ∀ R, CharLocProd.evalAt R ε ≠ 0 → CharLocProd.evalAt R ε = 1 := fun R hR =>
    mul_left_cancel₀ hR (by rw [← map_mul, hε, mul_one])
  have h0 : ∀ R, R ≠ Q → CharLocProd.evalAt R ε = 0 := by
    intro R hR
    by_contra hne
    have hnle : ¬ R.asIdeal ≤ Q.asIdeal := fun hle =>
      hR (HeightOneSpectrum.ext (R.isMaximal.eq_of_le Q.isPrime.ne_top hle))
    obtain ⟨y, hyR, hyQ⟩ := Set.not_subset.1 hnle
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hyQ Q.asIdeal.zero_mem
    have h2 := not_not.1 (mt (h y hy0).2 hyQ) R
    rw [map_mul, h01 R hne, one_mul] at h2
    exact (GlobalTheory.PlaceIdem.val_inv_le_one R hy0).1 h2 hyR
  refine ⟨h01 Q fun hQ => ?_, h0⟩
  obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
  refine (h y hy0).1 hyQ fun R => ?_
  have : CharLocProd.evalAt R ε = 0 := by
    by_cases hR : R = Q
    · rw [hR, hQ]
    · exact h0 R hR
  rw [map_mul, this, zero_mul, map_zero]
  exact zero_le

theorem val_sub_le_of_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Pl E) (φ : Formalism.L2.Herm.intAf F E →+* P.adicCompletion E) (h1 : ∀ z, Valued.v (φ z) ≤ 1)
    (h2 : ∀ t : 𝓞 E, φ (oToS F E t) = algebraMap E _ (t : E)) (a : Formalism.L2.Herm.intAf F E) (b : 𝓞 E)
    (hab : resS F P a = Ideal.Quotient.mk P.asIdeal b) :
    Valued.v (φ a - algebraMap E _ (b : E)) ≤ WithZero.exp (-1 : ℤ) := by
  have h0 : resS F P (a - oToS F E b) = 0 := by rw [map_sub, resS_oToS, hab, sub_self]
  have hm : a - oToS F E b ∈ idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS F P.asIdeal)
      (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  rw [← h2, ← map_sub]
  generalize a - oToS F E b = z at hm
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, ht, rfl⟩ := hy
    rw [h2, val_algebraMap]
    have := (P.intValuation_le_pow_iff_mem t 1).2 (by simpa using ht)
    rw [show P.valuation E (t : E) = P.intValuation t from HeightOneSpectrum.valuation_of_algebraMap P t]
    simpa using this
  | zero => rw [map_zero, map_zero]; exact zero_le
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Valuation.map_add_le _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_mul' (h1 r) hx).trans (one_mul _).le

theorem map_mix {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (e a : A) :
    f (e * a + (1 - e)) = f e * f a + (1 - f e) := by
  rw [map_add (f := _), map_mul, map_sub, map_one]

theorem map_finset_sum {A B ι : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s


set_option maxHeartbeats 800000 in
theorem char_eq_prod_res : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D) (ρ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → IsIdemSum e P → (∀ PP ∈ P, χ.TameAt PP ∧ IsRes χ PP (ρ PP)) → ∀ (x : (AE D)ˣ) (a : AE D) (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ), (x : AE D) = e * a + (1 - e) → (a' : Lev.EAf D) = toEAf D a → (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') → ((c x : Circle) : ℂ) = ∏ PP ∈ P, ((ρ PP (u PP) : ℂˣ) : ℂ) := by
  classical
  intro D c χ P e ρ hc he ht x a a' u hx ha hu
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_mix, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero]
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ R : Pl D.host.E, AE D →+* R.adicCompletion D.host.E,
      ∀ R z, ev R z = CharLocProd.evalAt R (ι (finPart D z)) :=
    ⟨fun R => (CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (finPart D)), fun _ _ => rfl⟩
  have hidem : ∀ Q ∈ P, ev Q (es Q) = 1 ∧ ∀ R, R ≠ Q → ev R (es Q) = 0 := by
    intro Q hQ
    simp only [hev]
    refine idem_apply _ (by rw [← RingEquiv.map_mul, ← RingHom.map_mul, (hes Q hQ).1.1]) Q fun y hy => ?_
    refine ((hes Q hQ).2 y hy).trans (not_congr ((h2 _).trans ?_))
    rw [RingHom.map_mul, RingEquiv.map_mul, show finPart D (incA D ((y : D.host.E)⁻¹)) =
      (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((y : D.host.E)⁻¹) from rfl, h1]
    rfl
  have hxP : ∀ R ∈ P, ev R x = ev R a := by
    intro R hR
    have : ev R e = 1 := by
      rw [hsum, map_finset_sum, Finset.sum_eq_single R, (hidem R hR).1]
      · intro Q hQ hne; exact (hidem Q hQ).2 R hne.symm
      · intro h; exact absurd hR h
    rw [hx, map_mix, this, one_mul, sub_self, add_zero]
  have hxP' : ∀ R, R ∉ P → ev R x = 1 := by
    intro R hR
    have : ev R e = 0 := by
      rw [hsum, map_finset_sum]
      exact Finset.sum_eq_zero fun Q hQ => (hidem Q hQ).2 R fun h => hR (h ▸ hQ)
    rw [hx, map_mix, this, zero_mul, zero_add, sub_zero]
  have hx0 : ∀ R, ev R x ≠ 0 := fun R => (RingHom.isUnit_map (ev R) x.isUnit).ne_zero
  choose k hk using fun R => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN R _ (hx0 R)
  have hfin : {R : Pl D.host.E | R.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hinf (P ∪ hfin.toFinset) (fun R => if R ∈ P then k R else 1) ?_ ?_
  rotate_left
  · intro R _
    change Valued.v (CharLocProd.evalAt R (ι (finPart D x))) = _ ∧
      Valued.v (CharLocProd.evalAt R (ι (finPart D x)) - _) ≤ _
    rw [← hev]
    by_cases hR : R ∈ P
    · simp only [if_pos hR]
      exact ⟨(hk R).1, (hk R).2.1⟩
    · simp only [if_neg hR]
      rw [hxP' R hR, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
  · intro R hR
    rw [Finset.mem_union, not_or] at hR
    change Valued.v (CharLocProd.evalAt R (ι (finPart D x))) = _ ∧ _
    rw [← hev, hxP' R hR.1, map_one]
    exact ⟨rfl, fun h => hR.2 (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h))⟩
  rw [key, ← Finset.prod_subset Finset.subset_union_left
    (fun R _ hR => by rw [if_neg hR, map_one, Units.val_one])]
  refine Finset.prod_congr rfl fun R hR => ?_
  rw [if_pos hR]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u R : kP R)
  have := R.isPrime
  have hbR : b ∉ R.asIdeal := fun h => (u R).ne_zero (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)
  have hb0 : (b : D.host.E) ≠ 0 := fun h => hbR (RingOfIntegers.coe_eq_zero_iff.1 h ▸ R.asIdeal.zero_mem)
  have hbv : R.valuation D.host.E (b : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) R (r := b)).2 hbR
  let cm := (Algebra.TensorProduct.comm D.host.F (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)
  let φ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R.adicCompletion D.host.E :=
    (CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (cm.symm.toRingEquiv.toRingHom.comp
      (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype))
  have hφ : ∀ z, φ z = CharLocProd.evalAt R (ι (cm.symm (z : Lev.EAf D))) := fun _ => rfl
  have hv := val_sub_le_of_resS R φ (fun z => (h2 _).1 ((GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _).2
      (by change cm (cm.symm (z : Lev.EAf D)) ∈ _; rw [AlgEquiv.apply_symm_apply]; exact z.2)) R)
    (fun t => by
      rw [hφ, show cm.symm ((oToS D.host.F D.host.E t : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
        (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E) from rfl, h1]
      rfl) a' b ((hu R hR).symm.trans hb.symm)
  have hφa : φ a' = ev R x := by
    rw [hxP R hR, hev, hφ, ha]
    exact congrArg (fun z => CharLocProd.evalAt R (ι z)) (cm.symm_apply_apply (finPart D a))
  rw [hφa] at hv
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hxv : Valued.v (ev R x) = 1 := by
    rw [← hbv, ← val_algebraMap]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [val_algebraMap, hbv]
    exact hv.trans_lt hlt
  have hk3 := (hk R).2.2
  rw [← (hk R).1, hxv, mul_one] at hk3
  rw [(ht R hR).2 b (Units.mk0 _ hb0) (u R) rfl hb.symm,
    locK_eq_of_congr χ R (ht R hR).1 (k R) (Units.mk0 _ hb0) hbv ?_]
  have e4 : algebraMap D.host.E (R.adicCompletion D.host.E) (k R : D.host.E) -
      algebraMap D.host.E (R.adicCompletion D.host.E) (b : D.host.E) =
      (ev R x - algebraMap D.host.E _ (b : D.host.E)) - (ev R x - algebraMap D.host.E _ (k R : D.host.E)) := by
    ring
  rw [Units.val_mk0, e4]
  exact Valuation.map_sub_le _ hv hk3

end GlobalTheory.TameSplitChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoFinitePlaceTruncationAdeleE
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

open Filter Topology

theorem tendsto_sum_placeIdem {F : Type} [Field F] [NumberField F]
    (α : HeightOneSpectrum (𝓞 F) → GlobalTheoryTheory.GenusMassVolumes.Af F) (h1 : ∀ v, evalV F v (α v) = 1)
    (h0 : ∀ v v', v' ≠ v → evalV F v' (α v) = 0) :
    Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∑ v ∈ s, α v) atTop (𝓝 1) := by
  classical
  have hv : ∀ (s : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)),
      evalV F w (1 - ∑ v ∈ s, α v) = if w ∈ s then 0 else 1 := by
    intro s w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_one, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single_of_mem w hw (fun v _ hvw => h0 v w (Ne.symm hvw)), h1, sub_self]
    · rw [Finset.sum_eq_zero (fun v hvs => h0 v w (by rintro rfl; exact hw hvs)), sub_zero]

  let y : Finset (HeightOneSpectrum (𝓞 F)) → (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F :=
    fun s w => if w ∈ s then 0 else 1
  have hy : Tendsto y atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {w}] with s hs
    have hws : w ∈ s := Finset.singleton_subset_iff.mp hs
    simp [y, hws]
  let g : ((w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F) → GlobalTheoryTheory.GenusMassVolumes.Af F :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) Filter.cofinite
  have hg : Continuous g := RestrictedProduct.isEmbedding_structureMap.continuous
  have hgy : ∀ s, g (y s) = 1 - ∑ v ∈ s, α v := by
    intro s
    refine FiniteAdeleRing.ext (R := 𝓞 F) (K := F) (fun w => ?_)
    have e1 : (g (y s)) w = ((y s w : w.adicCompletionIntegers F) : w.adicCompletion F) := rfl
    have e2 : (1 - ∑ v ∈ s, α v) w = evalV F w (1 - ∑ v ∈ s, α v) := rfl
    rw [e1, e2, hv]
    by_cases hw : w ∈ s <;> simp [y, hw]
  have hg0 : g 0 = 0 := FiniteAdeleRing.ext (R := 𝓞 F) (K := F) (fun w => rfl)
  have hlim : Tendsto (fun s => 1 - ∑ v ∈ s, α v) atTop (𝓝 (0 : GlobalTheoryTheory.GenusMassVolumes.Af F)) := by
    have h := (hg.tendsto 0).comp hy
    rw [hg0] at h
    exact h.congr (fun s => hgy s)
  simpa using (tendsto_const_nhds (x := (1 : GlobalTheoryTheory.GenusMassVolumes.Af F))).sub hlim

theorem tendsto_truncation : ∀ (D : D7) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ a : AE D, infPart D a = 0 → Filter.Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) * a) Filter.atTop (nhds a) := by
  intro D ε hε a ha
  simp only [IsPlaceIdem] at hε
  choose α hαε hα1 hα0 using hε
  have hsum : ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      ∑ v ∈ s, ε v = pairA D.host.F 0 (∑ v ∈ s, α v) := by
    intro s
    simp only [hαε]
    exact (map_sum (AddMonoidHom.inr (InfiniteAdeleRing D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) α s).symm
  have hpair : Continuous (pairA D.host.F 0) := by
    show Continuous fun y : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => ((0 : InfiniteAdeleRing D.host.F), y)
    exact continuous_const.prodMk continuous_id
  have hlimF : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => ∑ v ∈ s, ε v) atTop
      (𝓝 (pairA D.host.F 0 1)) := by
    simp_rw [hsum]
    exact (hpair.tendsto 1).comp (tendsto_sum_placeIdem α hα1 hα0)

  have hidem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * a = a := by
    have hsplit : pairA D.host.F 0 1 = 1 - pairA D.host.F 1 0 := by
      rw [eq_sub_iff_add_eq]
      show ((0 + 1, 1 + 0) : InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F) = 1
      rw [zero_add, add_zero]
      rfl
    have hr : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) = GlobalTheory.SplitScalar.realIdem D := by
      rw [GlobalTheory.SplitScalar.realIdem, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsplit, map_sub, map_one, hr, sub_mul, one_mul, GlobalTheory.SplitScalar.realIdem_mul_of_fin ha, sub_zero]
  have hT := hlimF.smul_const a
  rw [Algebra.smul_def, hidem] at hT
  exact hT.congr (fun s => Algebra.smul_def _ _)

end GlobalTheory.VecInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.ThetaSquare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem cocompact (V W : HSp D) : Cocompact V W := by
  obtain ⟨-, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have h := hK.image (QuotientAddGroup.continuous_mk (N := (ratL W V : AddSubgroup (WO V W))))
  refine ⟨(Set.eq_univ_of_forall fun q => ?_ : _ = Set.univ) ▸ h⟩
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨γ, hγ, hk⟩ := hc w
  exact ⟨_, hk, QuotientAddGroup.eq.2 (by simpa using hγ)⟩

theorem symplOH_zero_right (w : WO V W) : symplOH V W w 0 = 0 := by
  have := symplOH_add_right w 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_zero_left (w : WO V W) : symplOH V W 0 w = 0 := by
  have := symplOH_add_left 0 0 w
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_neg_self (u : WO V W) : symplOH V W (-u) u = 0 := by
  have := symplOH_add_left (-u) u u
  rwa [neg_add_cancel, symplOH_zero_left, symplOH_self, add_zero, eq_comm] at this

theorem squareIntegrable (hψ : IsStdChar D ψ (-1)) : SquareIntegrable ψ V W :=
  fun _ h => ⟨theta_norm_periodic hψ h, theta_bounded hψ h, fun _ _ hμ h𝓕 => GlobalTheory.Size.memLp_theta hψ hμ h𝓕 h⟩

theorem heisUnitary (hψ : IsStdChar D ψ (-1)) : HeisUnitary ψ V W := by
  refine ⟨heisO_heisO, fun u f => ?_, fun u f h => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ h u,
    fun _ _ hμ h𝓕 u _ _ h h' => GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 h h' u, ?_⟩
  · rw [heisO_heisO, symplOH_neg_self, ψ.map_zero_eq_one, one_smul, neg_add_cancel, heisO_zero]
  · rintro _ ⟨γ, rfl⟩ f h
    have e := h.quasi γ 0
    rw [symplOH_zero_right, neg_zero, ψ.map_zero_eq_one, one_mul, add_zero] at e
    change ψ (symplOH V W 0 (ratW W V γ)) * f (0 + ratW W V γ) = f 0
    rw [symplOH_zero_left, ψ.map_zero_eq_one, one_mul, zero_add, e]

theorem norm_heisO (hψ : IsStdChar D ψ (-1)) (u : WO V W) (f : WO V W → ℂ) (x : WO V W) :
    ‖heisO ψ V W u f x‖ = ‖f (x + u)‖ := by
  rw [heisO, norm_mul, hψ.1.2.1, one_mul]

theorem ipO_dLine (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO V W} (hL : IsRealDir W V L)
    {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f f' : WO V W → ℂ} (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    ipO μ 𝓕 (dLine ψ V W L f) f' = -ipO μ 𝓕 f (dLine ψ V W L f') := by
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  have hd := theta_dLine hθ hψ hL h
  have hd' := theta_dLine hθ hψ hL h'
  have hI := fun {g g'} => GlobalTheory.Size.integrableOn_mul_conj (f := g) (f' := g') hψ hμ h𝓕
  have hT := fun {g} (hg : IsThetaFunO ψ V W g) t => theta_heisO_real hθ hψ (hL.2 t) hg
  obtain ⟨a, ha⟩ := theta_bounded hψ h
  obtain ⟨b, hb⟩ := theta_bounded hψ h'
  obtain ⟨c, hc⟩ := theta_bounded hψ hd
  obtain ⟨d, hd0⟩ := theta_bounded hψ hd'
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ => c * b + a * d)
    (F := fun t x => heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) f' x))
    (F' := fun t x => heisO ψ V W (L t) (dLine ψ V W L f) x * conj (heisO ψ V W (L t) f' x) +
      heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) (dLine ψ V W L f') x))
    Filter.univ_mem
    (.of_forall fun t => (hI (hT h t) (hT h' t)).aestronglyMeasurable)
    (hI (hT h 0) (hT h' 0))
    ((hI (hT hd 0) (hT h' 0)).add (hI (hT h 0) (hT hd' 0))).aestronglyMeasurable
    (.of_forall fun x t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
        rw [norm_mul, Complex.norm_conj, norm_heisO hψ, norm_heisO hψ]
      · exact mul_le_mul (hc _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (hc 0))
      · exact mul_le_mul (ha _) (hd0 _) (norm_nonneg _) ((norm_nonneg _).trans (ha 0)))
    (integrable_const _)
    (.of_forall fun x t _ =>
      (hasDerivAt_heisO hθ hψ hL h x t).mul (hasDerivAt_heisO hθ hψ hL h' x t).star)).2
  have e : (fun t => ∫ x in 𝓕, heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) f' x) ∂μ) = fun _ => ipO μ 𝓕 f f' :=
    funext fun t => GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 h h' (L t)
  rw [e] at key
  have k := key.unique (hasDerivAt_const _ _)
  simp only [map_zero, heisO_zero] at k
  rw [integral_add (hI hd h') (hI h hd')] at k
  exact eq_neg_of_add_eq_zero_left k

theorem derSkew (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) : DerSkew ψ θ V W := by
  intro τ z
  have hL := isRealDir_lineAt (S := V) (T := W) hθ τ z
  refine ⟨fun f h x => ?_, fun f h => theta_dRho hθ hψ τ z h, fun μ 𝓕 hμ h𝓕 f f' h h' => ipO_dLine hψ hθ hL hμ h𝓕 h h'⟩
  exact (hasDerivAt_heisO hθ hψ hL h x 0).differentiableAt.hasDerivAt

theorem commScalar_eq (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    commScalar V W τ τ' z w = -(2 * Real.pi * Complex.I) * (GlobalTheory.FockIndep.omDir V W τ z τ' w : ℝ) := by
  unfold commScalar GlobalTheory.FockIndep.omDir
  split_ifs
  · rfl
  · simp

theorem symplO_eq (x y : WO V W) : symplO V W x y = symplOH V W x y + symplOH V W x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem derComm (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) : DerComm ψ θ V W := by
  intro τ τ' z w
  rw [commScalar_eq]
  refine ⟨fun s t => ?_, fun f h => sub_eq_of_eq_add (GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' w h)⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (smooth_iff_sm_and_real_lines D θ σ h W V).2.1
  rw [symplO_eq, AddChar.map_add_eq_mul, e _ (isRealDir_lineAt hθ τ z) s, e _ (isRealDir_lineAt hθ τ' w) t,
    psi_symplOH h hψ, h.pi_iota, LinearMap.map_smul₂, map_smul, GlobalTheory.FockIndep.piW_lineAt hθ,
    GlobalTheory.FockIndep.piW_lineAt hθ, GlobalTheory.FockIndep.omO_single, ← Complex.exp_add]
  congr 1
  simp only [smul_eq_mul]
  push_cast
  ring

theorem finRealComm (hθ : IsInfFam θ) : FinRealComm ψ θ V W := by
  refine fun u hu => ⟨fun v hv f => ?_, fun τ z f _ => (GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f).symm⟩
  rw [heisO_heisO, heisO_heisO, (symplOH_fin_real hu hv).1, (symplOH_fin_real hu hv).2, add_comm]

theorem theta_square_integrable (D : D7) : ThetaSquareIntegrable D :=
  fun V W => ⟨cocompact V W, fun _ hψ => ⟨squareIntegrable hψ, heisUnitary hψ,
    fun _ hθ => ⟨derSkew hψ hθ, derComm hψ hθ, finRealComm hθ⟩⟩⟩

end GlobalTheory.ThetaSquare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistPlaces

theorem typePlaces_disjoint_twistPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  rw [Finset.disjoint_left]
  intro PP hPg hQ
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := R.C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = R.C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : PP.asIdeal.IsPrime := PP.isPrime
  haveI : Nontrivial (kP PP) := inferInstance
  haveI : Fintype (kP PP) := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hmemE
    simpa using this
  have h0q : ((q : ℕ) : kP PP) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP PP)
  have hd1 : ringChar (kP PP) ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP PP) ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP PP) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1

end GlobalTheory.TwistPlaces
end

