module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointDegreePos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {k : Type u} [Field k] {N : ℕ}

theorem oneBlock_homogeneousComponent (f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    oneBlock (S := k) (N := N) (homogeneousComponent n f) =
      homogeneousComponent n (oneBlock (S := k) (N := N) f) := by
  classical
  have ho : ∀ g, oneBlock (S := k) (N := N) g = rename (HilbertPositive.blockEquiv N) g := fun _ => rfl
  ext d
  set d' := Finsupp.mapDomain (HilbertPositive.blockEquiv N).symm d with hd'
  have hd : d = Finsupp.mapDomain (HilbertPositive.blockEquiv N) d' := by
    rw [hd', ← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : d.degree = d'.degree := by
    rw [hd, Finsupp.degree_mapDomain]
  rw [ho, ho, coeff_homogeneousComponent, hd,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_homogeneousComponent, ← hd, hdeg]

theorem isMultiProjPrime_comap_oneBlock {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {pp : Ideal (Poly k N)} (h : IsSubvar x pp 0) :
    NumbersDVR.IsMultiProjPrime (pp.comap (oneBlock (S := k) (N := N)).toRingHom) ∧
      FieldNumbers.relDim (pp.comap (oneBlock (S := k) (N := N)).toRingHom) =
        ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  have := h.isPrime
  let e : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (HilbertPositive.blockEquiv N)).toRingEquiv
  have hc : pp.comap (oneBlock (S := k) (N := N)).toRingHom = pp.comap e.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  refine ⟨⟨Ideal.comap_isPrime _ _, ?_, ?_⟩, ?_⟩
  · intro f hf b
    have heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) b f =
        homogeneousComponent (b ()) f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent,
        HilbertPositive.weight_blockWeight_one d]
      congr 1
      apply propext
      constructor
      · intro h; rw [← h]
      · intro h; funext u; exact h
    rw [heq]
    change oneBlock (S := k) (N := N) _ ∈ pp
    change oneBlock (S := k) (N := N) f ∈ pp at hf
    rw [oneBlock_homogeneousComponent]
    exact h.homog _ hf _
  · intro u
    obtain ⟨i, hi⟩ := h.relevant
    refine ⟨i, ?_⟩
    change oneBlock (S := k) (N := N) (X _) ∉ pp
    rw [oneBlock, rename_X]
    exact hi
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit, hc]
    have hm : pp = (pp.comap e.toRingHom).map e.toRingHom := by
      rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective]
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hm), h.dim]

end

theorem PointDegreePos.proof : PointDegreePos.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  obtain ⟨hP, hrel⟩ := isMultiProjPrime_comap_oneBlock h
  have := hP.isPrime
  obtain ⟨hfd, -⟩ := FieldNumbers.IntNumBase.full k Unit (fun _ => Fin (N + 1)) _ hP hrel
  unfold FieldNumbers.resDeg
  rw [dite_eq_left hP.isPrime]
  exact Module.finrank_pos

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictGenerated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace RestrictGenerated

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}


variable (y) in
def toChartY (I : Chart x) (h : ∀ i ∈ I.1, y i ≠ 0) : Chart y :=
  ⟨I.1, I.2.1, fun i hi => (mem_support y).mpr (h i hi)⟩

theorem liftChart_toChartY (I : Chart x) (h : ∀ i ∈ I.1, y i ≠ 0) :
    liftChart hxy (toChartY y I h) = I := rfl

theorem r_zero {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) : r 0 = 0 := by
  have := h.add J 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this

theorem r_sub {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {u v : Ω}
    (hu : u ∈ Q.sub (liftChart hxy J)) (hv : v ∈ Q.sub (liftChart hxy J)) :
    r (u - v) = r u - r v := by
  have := h.add J (u - v) (sub_mem hu hv) v hv
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm

theorem exists_of_mem {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ w ∈ Q.sub (liftChart hxy J), r w = t := by
  rw [← h.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht => obtain ⟨w, hw, rfl⟩ := ht; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, zero_mem _, r_zero h J⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨w', hw', rfl⟩ := ht'
    exact ⟨w + w', add_mem hw hw', h.add J w hw w' hw'⟩
  | smul b t _ ht =>
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
    let a : chartRing S x (liftChart hxy J) := ⟨aeval x f / aeval x s, f, s, e, hs, hf, hse, rfl⟩
    refine ⟨a • w, (Q.sub _).smul_mem a hw, ?_⟩
    show r (aeval x f / aeval x s * w) = (b : K') * r w
    rw [h.smul J w hw f s e hs hf hse, hb]

theorem sub_ne_bot (Q' : LineBundle S y) (J : Chart y) : Q'.toSubSystem.sub J ≠ ⊥ := by
  intro h0
  obtain ⟨Q'', hQ''⟩ := Q'.invertible J
  have h1 : (1 : K') ∈ (1 : Submodule (chartRing S y J) K') := Submodule.mem_one.mpr ⟨1, map_one _⟩
  rw [← hQ''] at h1
  change (1 : K') ∈ Q'.toSubSystem.sub J * Q'' at h1
  rw [h0, Submodule.bot_mul] at h1
  exact one_ne_zero ((Submodule.mem_bot _).mp h1)

theorem mem_twist_of_eq_zero (Q : LineBundle S x) (Q' : LineBundle S y) {r : Ω → K'}
    {pp : Ideal (Poly S N)} (hpp : primeOf (S := S) y = pp)
    (h : RestrictData Q.toSubSystem hxy Q'.toSubSystem r) (J : Chart y) {z : Ω}
    (hz : z ∈ Q.toSubSystem.sub (liftChart hxy J)) (hr : r z = 0) :
    z ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
  obtain ⟨w₀, hw₀, hrw₀⟩ : ∃ w ∈ Q.toSubSystem.sub (liftChart hxy J), r w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply sub_ne_bot Q' J
    rw [← h.span J, Submodule.span_eq_bot]
    rintro _ ⟨w, hw, rfl⟩
    exact hcon w hw
  obtain ⟨Q'', hQ''⟩ := Q.invertible (liftChart hxy J)
  have hmulA : ∀ u ∈ Q.toSubSystem.sub (liftChart hxy J), ∀ v ∈ Q'',
      u * v ∈ chartRing S x (liftChart hxy J) := by
    intro u hu v hv
    have : u * v ∈ Q.toSubSystem.sub (liftChart hxy J) * Q'' := Submodule.mul_mem_mul hu hv
    change u * v ∈ Q.sub (liftChart hxy J) * Q'' at this
    rw [hQ''] at this
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp this
    rw [← hb]; exact b.2
  have hkey : ∀ v ∈ Q'', z * v ∈ idealMod (x := x) pp (liftChart hxy J) := by
    intro v hv
    obtain ⟨f, s, e, hs, hf, hse, ha⟩ := hmulA z hz v hv
    obtain ⟨g, t, e', ht, hg, hte, hb⟩ := hmulA w₀ hw₀ v hv
    have h1 := h.smul J w₀ hw₀ f s e hs hf hse
    have h2 := h.smul J z hz g t e' ht hg hte
    have heq : aeval x f / aeval x s * w₀ = aeval x g / aeval x t * z := by
      rw [← ha, ← hb]; ring
    rw [heq, h2, hr, mul_zero] at h1
    have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos J hs
    have hfy : aeval y f = 0 :=
      (div_eq_zero_iff.mp ((mul_eq_zero.mp h1.symm).resolve_right hrw₀)).resolve_right hs0
    have hfp : f ∈ pp := by
      rw [← hpp]; exact (mem_primeOf_of_isHomogeneous y hf).mpr hfy
    rw [ha]
    exact Submodule.subset_span ⟨f, s, e, hfp, hs, hf, hse, rfl⟩
  have hall : ∀ m ∈ Q.sub (liftChart hxy J) * Q'',
      z * m ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
    intro m hm
    induction hm using Submodule.mul_induction_on' with
    | mem_mul_mem q hq v hv =>
      refine Submodule.subset_span ⟨z * v, hkey v hv, q, hq, ?_⟩
      rw [smul_eq_mul]; ring
    | add m _ m' _ hm hm' => rw [mul_add]; exact add_mem hm hm'
  have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy J) * Q'' := by
    rw [hQ'']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  simpa using hall 1 h1

end RestrictGenerated


open RestrictGenerated in
theorem RestrictGenerated.proof : RestrictGenerated.Statement.{u, w} := by
  intro S _ Ω _ _ N x K' _ _ y hxy pp _ hyp Q Q' r h hgen I
  have hX : ∀ i, (X i : Poly S N) ∈ pp ↔ y i = 0 := fun i => by
    rw [← hyp, mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i), aeval_X]
  have hQtw : ∀ (I' : Chart x) (i : Fin (N + 1)), i ∈ I'.1 → y i = 0 →
      Q.toSubSystem.sub I' ≤ (Q.toSubSystem.twist (idealSys x pp)).sub I' := fun I' i hi hyi =>
    StepThree.OnW.Gen.sub_le_twist_idealSys_of_mem _ I' hi ((hX i).mpr hyi)
  by_cases hI : ∀ i ∈ I.1, y i ≠ 0
  swap
  · push Not at hI
    obtain ⟨i, hi, hyi⟩ := hI
    exact le_sup_of_le_right (hQtw I i hi hyi)

  have hlift : ∀ t ∈ Q'.toSubSystem.secs, ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 →
        s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
      ∀ (I' : Chart x) (hI' : ∀ i ∈ I'.1, y i ≠ 0), r (s I') = t := by
    intro t ht
    have ht' : ∀ J, t ∈ Q'.toSubSystem.sub J := fun J => (Submodule.mem_iInf _).mp ht J
    choose w hw hrw using fun J => exists_of_mem h J (ht' J)
    classical
    have hmem : ∀ I', (if hI' : ∀ i ∈ I'.1, y i ≠ 0 then w (toChartY y I' hI') else 0) ∈
        Q.toSubSystem.sub I' := by
      intro I'
      split_ifs with hI'
      · have := hw (toChartY y I' hI')
        rwa [liftChart_toChartY] at this
      · exact zero_mem _
    refine ⟨fun I' => if hI' : ∀ i ∈ I'.1, y i ≠ 0 then w (toChartY y I' hI') else 0, hmem,
      fun I₁ I₂ h12 => ?_, fun I' hI' => ?_⟩
    · by_cases h2 : ∀ i ∈ I₂.1, y i ≠ 0
      · have h1 : ∀ i ∈ I₁.1, y i ≠ 0 := fun i hi => h2 i (h12 hi)
        have hm1 := Q.toSubSystem.mono I₁ I₂ h12 _ (hw (toChartY y I₁ h1))
        have hm2 := hw (toChartY y I₂ h2)
        dsimp only
        rw [dite_eq_left h1, dite_eq_left h2]
        exact mem_twist_of_eq_zero Q Q' hyp h (toChartY y I₂ h2) (sub_mem hm1 hm2)
          (by rw [r_sub h (toChartY y I₂ h2) hm1 hm2, hrw, hrw, sub_self])
      · push Not at h2
        obtain ⟨i, hi, hyi⟩ := h2
        exact hQtw I₂ i hi hyi (sub_mem (Q.toSubSystem.mono I₁ I₂ h12 _ (hmem I₁)) (hmem I₂))
    · dsimp only
      rw [dite_eq_left hI']
      exact hrw _
  let J : Chart y := toChartY y I hI
  have hJ : ∀ t ∈ Q'.toSubSystem.sub J, ∃ u ∈ Submodule.span (chartRing S x I)
      {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
        (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
        z = s I}, u ∈ Q.toSubSystem.sub I ∧ r u = t := by
    intro t ht
    rw [← hgen J] at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨s, hs, hc, hr⟩ := hlift t ht
      exact ⟨s I, Submodule.subset_span ⟨s, hs, hc, rfl⟩, hs I, hr I hI⟩
    | zero => exact ⟨0, zero_mem _, zero_mem _, r_zero h J⟩
    | add t t' _ _ ht ht' =>
      obtain ⟨u, hu, hu', rfl⟩ := ht
      obtain ⟨v, hv, hv', rfl⟩ := ht'
      exact ⟨u + v, add_mem hu hv, add_mem hu' hv', h.add J u hu' v hv'⟩
    | smul b t _ ht =>
      obtain ⟨u, hu, hu', rfl⟩ := ht
      obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
      let a : chartRing S x I := ⟨aeval x f / aeval x s, f, s, e, hs, hf, hse, rfl⟩
      refine ⟨a • u, Submodule.smul_mem _ a hu, Submodule.smul_mem _ a hu', ?_⟩
      show r (aeval x f / aeval x s * u) = (b : K') * r u
      rw [h.smul J u hu' f s e hs hf hse, hb]
  intro q hq
  obtain ⟨u, hu, hu', hru⟩ := hJ (r q) (h.mem J q hq)
  have hd : q - u ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I :=
    mem_twist_of_eq_zero Q Q' hyp h J (sub_mem hq hu') (by rw [r_sub h J hq hu', hru, sub_self])
  rw [show q = u + (q - u) by abel]
  exact Submodule.add_mem_sup hu hd

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionMulInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionMulInj

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_of_mem_idealMod (J : Ideal (Poly S N)) (I : Chart x) {z : Ω} (hz : z ∈ idealMod (x := x) J I) :
    ∃ (G m : Poly S N) (e : ℕ), G ∈ J ∧ m ∈ monos I.1 ∧ G.IsHomogeneous e ∧ m.IsHomogeneous e ∧
      z = aeval x G / aeval x m := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    obtain ⟨G', m', e', hG', hm', hGe', hme', rfl⟩ := hb
    refine ⟨G * m' + m * G', m * m', e + e', J.add_mem (J.mul_mem_right _ hG) (J.mul_mem_left _ hG'),
      mul_mem hm hm', (hGe.mul hme').add (hme.mul hGe'), hme.mul hme', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hm) (eval_ne_zero_of_mem_monos I hm')]
    simp only [map_add (f := _), map_mul]
  | smul r a _ ha =>
    obtain ⟨F, m₀, e₀, hm₀, hF, hm₀e, hr⟩ := r.2
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    refine ⟨F * G, m₀ * m, e₀ + e, J.mul_mem_left _ hG, mul_mem hm₀ hm, hF.mul hGe, hm₀e.mul hme, ?_⟩
    rw [chartRing_smul_def, hr, map_mul, map_mul, div_mul_div_comm]


omit [Algebra S Ω] in
theorem not_mem_of_mem_monos {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) {I : Chart x}
    (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {m : Poly S N} (hm : m ∈ monos I.1) : m ∉ pp := by
  induction hm using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    exact hX j (by exact_mod_cast hj)
  | one => exact fun h => hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  | mul a b _ _ ha hb => exact fun h => (hpp.mem_or_mem h).elim ha hb

theorem mem_of_div_mem_idealMod {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {F m : Poly S N} {e : ℕ} (hm : m ∈ monos I.1)
    (hF : F.IsHomogeneous e) (hme : m.IsHomogeneous e) (h : aeval x F / aeval x m ∈ idealMod (x := x) pp I) :
    F ∈ pp := by
  obtain ⟨G, m', e', hG, hm', hGe, hme', heq⟩ := exists_of_mem_idealMod pp I h
  have h0 := eval_ne_zero_of_mem_monos I hm
  have h0' := eval_ne_zero_of_mem_monos I hm'
  have hdiff : F * m' - m * G ∈ primeOf (S := S) x := by
    have hhom : (F * m' - m * G).IsHomogeneous (e + e') := (hF.mul hme').sub (hme.mul hGe)
    rw [mem_primeOf_of_isHomogeneous x hhom, map_sub, map_mul, map_mul, sub_eq_zero]
    rw [div_eq_div_iff h0 h0'] at heq
    rw [heq, mul_comm]
  have hFm : F * m' ∈ pp := by
    have := pp.add_mem (hZ hdiff) (pp.mul_mem_left m hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem hFm).resolve_right (not_mem_of_mem_monos hpp hX hm')

theorem mem_or_mem {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) (a b : chartRing S x I)
    (h : (a : Ω) * b ∈ idealMod (x := x) pp I) :
    (a : Ω) ∈ idealMod (x := x) pp I ∨ (b : Ω) ∈ idealMod (x := x) pp I := by
  obtain ⟨F, m, e, hm, hF, hme, ha⟩ := a.2
  obtain ⟨F', m', e', hm', hF', hme', hb⟩ := b.2
  rw [ha, hb, div_mul_div_comm, ← map_mul, ← map_mul] at h
  have := mem_of_div_mem_idealMod hpp hZ hX (mul_mem hm hm') (hF.mul hF') (hme.mul hme') h
  refine (hpp.mem_or_mem this).imp (fun hF0 => ?_) (fun hF0 => ?_)
  · rw [ha]; exact Submodule.subset_span ⟨F, m, e, hF0, hm, hF, hme, rfl⟩
  · rw [hb]; exact Submodule.subset_span ⟨F', m', e', hF0, hm', hF', hme', rfl⟩

end SectionMulInj


open SectionMulInj in
theorem SectionMulInj.proof : SectionMulInj.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp hhom hZ D M s ⟨f, hf, hfp⟩ I y hy hsy
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change y ∈ idealMod (x := x) pp I * M.sub I
  by_cases hX : ∃ j ∈ I.1, (X j : Poly k N) ∈ pp
  · obtain ⟨j, hj, hXj⟩ := hX
    have := StepThree.OnW.Gen.sub_le_twist_idealSys_of_mem M.toSubSystem I hj hXj hy
    rwa [SubSystem.twist_sub_eq_mul_of_line] at this
  push Not at hX
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)

  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e f ∉ pp := by
    by_contra hall
    push Not at hall
    exact hfp (by rw [← sum_homogeneousComponent f]; exact pp.sum_mem fun d _ => hall d)
  set g : chartRing k x I := ⟨_, StepThree.Away.div_pow_mem_chartRing I hi
    (homogeneousComponent_isHomogeneous e f)⟩ with hg
  have hgI : (g : Ω) ∉ idealMod (x := x) pp I := fun h => he <| by
    refine mem_of_div_mem_idealMod hpp hZ hX (pow_mem (X_mem_monos hi) e)
      (homogeneousComponent_isHomogeneous e f) (isHomogeneous_X_pow i e) ?_
    rw [map_pow, aeval_X]; exact h

  have hgD : Submodule.span (chartRing k x I) {(g : Ω)} * D.sub I ≤ Submodule.span _ {s} := by
    rw [Submodule.mul_le]
    intro a ha δ hδ
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
      (StepThree.Away.homogeneousComponent_mul_mem D.toSubSystem s I hi hf e δ hδ)
    rw [Submodule.mem_span_singleton]
    refine ⟨r * t, ?_⟩
    have hpow : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    rw [chartRing_smul_def] at ht
    change ((r * t : chartRing k x I) : Ω) * s = ((r : Ω) * (g : Ω)) * δ
    rw [Subalgebra.coe_mul, hg]
    change (r : Ω) * t * s = (r : Ω) * (aeval x (homogeneousComponent e f) / x i ^ e) * δ
    rw [mul_assoc (r : Ω), mul_assoc (r : Ω)]
    congr 1
    rw [div_mul_eq_mul_div, eq_div_iff hpow, ← ht]
    ring
  obtain ⟨D', hD'⟩ := D.invertible I
  obtain ⟨M', hM'⟩ := M.invertible I
  have h1D : (1 : Ω) ∈ D.sub I * D' := by rw [hD']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩

  have hgs : (g : Ω) ∈ Submodule.span (chartRing k x I) {s} * D' := by
    have := Submodule.mul_mem_mul (Submodule.mem_span_singleton_self (g : Ω)) h1D
    rw [mul_one, ← mul_assoc] at this
    exact mul_le_mul' hgD le_rfl this
  have hsy' : s * y ∈ idealMod (x := x) pp I * (D.sub I * M.sub I) := by
    rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line] at hsy
    exact hsy
  have hgy : Submodule.span (chartRing k x I) {(g : Ω) * y} ≤ idealMod (x := x) pp I * M.sub I := by
    calc Submodule.span (chartRing k x I) {(g : Ω) * y}
        ≤ Submodule.span (chartRing k x I) {s} * D' * Submodule.span _ {y} := by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact Submodule.mul_mem_mul hgs (Submodule.mem_span_singleton_self y)
      _ = D' * Submodule.span _ {s * y} := by
          rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span]; ring
      _ ≤ D' * (idealMod (x := x) pp I * (D.sub I * M.sub I)) := by
          gcongr
          rw [Submodule.span_le, Set.singleton_subset_iff]; exact hsy'
      _ = idealMod (x := x) pp I * M.sub I * (D.sub I * D') := by ring
      _ = idealMod (x := x) pp I * M.sub I := by rw [hD', mul_one]

  have hyM : Submodule.span (chartRing k x I) {y} * M' ≤ idealMod (x := x) pp I := by
    intro z hz
    have hz1 : z ∈ (1 : Submodule (chartRing k x I) Ω) := by
      rw [← hM']
      refine (mul_le_mul' ?_ le_rfl : _ ≤ M.sub I * M') hz
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hz1
    have hgz : (g : Ω) * algebraMap (chartRing k x I) Ω r ∈ idealMod (x := x) pp I := by
      have hle : Submodule.span (chartRing k x I) {(g : Ω)} * (Submodule.span _ {y} * M') ≤
          idealMod (x := x) pp I := by
        calc Submodule.span (chartRing k x I) {(g : Ω)} * (Submodule.span _ {y} * M')
            = Submodule.span _ {(g : Ω) * y} * M' := by
              rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span]; ring
          _ ≤ idealMod (x := x) pp I * M.sub I * M' := by gcongr
          _ = idealMod (x := x) pp I := by rw [mul_assoc, hM', mul_one]
      exact hle (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) hz)
    exact ((mem_or_mem hpp hZ hX g r hgz).resolve_left hgI)
  have hle : Submodule.span (chartRing k x I) {y} ≤ idealMod (x := x) pp I * M.sub I :=
    calc Submodule.span (chartRing k x I) {y}
        = Submodule.span (chartRing k x I) {y} * M' * M.sub I := by
          rw [mul_assoc, mul_comm M', hM', mul_one]
      _ ≤ idealMod (x := x) pp I * M.sub I := by gcongr
  exact hle (Submodule.mem_span_singleton_self y)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

