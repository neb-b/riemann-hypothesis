module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem FinGradedSub.tildeSys_natCast_eq_twist (M : FinGradedSub (S := S) (x := x) E) (a : ℕ) :
    M.tildeSys (a : ℤ) = (M.tildeSys 0).twist (twistSys S x (a : ℤ)) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hA : x i ^ a ∈ twistMod S x (a : ℤ) I := by
    rw [twistMod_eq_span _ I hi, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.subset_span ⟨x i ^ a, hA, (aeval x (s * X i ^ a))⁻¹ • m,
      Submodule.subset_span ⟨m, s * X i ^ a, b, e + a, mul_mem hs (pow_mem (X_mem_monos hi) a),
        hse.mul (isHomogeneous_X_pow i a), hm, by push_cast; omega, rfl⟩, ?_⟩
    rw [smul_smul, map_mul, map_pow, aeval_X, mul_inv, ← mul_assoc, mul_comm (x i ^ a),
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero a hxi), mul_one]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x (a : ℤ) I at hq
    rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at hq
    obtain ⟨β, rfl⟩ := hq
    have key : x i ^ a • y ∈ M.tilde (a : ℤ) I := by
      refine Submodule.span_induction (p := fun y _ => x i ^ a • y ∈ M.tilde (a : ℤ) I) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
        refine Submodule.subset_span ⟨aeval x (X i ^ a : Poly S N) • m, s, b + a, e, hs, hse,
          M.smul_mem a b _ m (isHomogeneous_X_pow i a) hm, by omega, ?_⟩
        rw [smul_smul, smul_smul, map_pow, aeval_X, mul_comm]
      · rw [smul_zero]
        exact Submodule.zero_mem _
      · intro y y' _ _ h h'
        rw [smul_add]
        exact Submodule.add_mem _ h h'
      · intro c y _ h
        rw [Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]
        exact Submodule.smul_mem _ c h
    rw [SetLike.mem_coe, chartRing_smul_def, ← smul_smul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ β key

end Tilde

theorem AmpleVanish.proof (hC : VeryAmpleCech.Statement.{u, v, w}) (hE : Extension.Statement.{u, v, w})
    (hT : TildeVanish.Statement.{u, v, w}) : AmpleVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H hH
  obtain ⟨r, h, hh⟩ := hH
  obtain ⟨F', hF', hiso⟩ := hC S Ω N x E F hF H r h hh
  obtain ⟨M, -, hM⟩ := hE S Ω r h E F' hF'
  obtain ⟨c₀, hc₀⟩ := hT S Ω r h E M
  refine ⟨c₀.toNat, fun i a hi ha => ?_⟩
  obtain ⟨e⟩ := hiso a i
  have hsys : F'.toSubSystem = M.tildeSys 0 := SubSystem.ext_sub fun J => (hM J).symm
  have hv := hc₀ i hi a (by omega)
  rw [M.tildeSys_natCast_eq_twist a, ← hsys] at hv
  exact e.toEquiv.subsingleton

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimSeq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Forms

variable {R : Type u} [CommRing R] {N : ℕ}

theorem homogeneousComponent_mul_form (r g : Poly R N) {d : ℕ} (hg : g.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (r * g) ∈ Submodule.span R
      {z | ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧ d' + d = e ∧ z = h * g} := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show r * g = ∑ i ∈ Finset.range (r.totalDegree + 1), homogeneousComponent i r * g by
    rw [← Finset.sum_mul, sum_homogeneousComponent], map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hm : homogeneousComponent i r * g ∈ homogeneousSubmodule (Fin (N + 1)) R (i + d) :=
    (mem_homogeneousSubmodule _ _).mpr ((homogeneousComponent_isHomogeneous i r).mul hg)
  rw [homogeneousComponent_of_mem hm]
  split_ifs with h
  · exact Submodule.subset_span ⟨_, i, homogeneousComponent_isHomogeneous i r, h.symm, rfl⟩
  · exact Submodule.zero_mem _

theorem mem_span_forms_of_mem_ideal {G : Set (Poly R N)} (deg : Poly R N → ℕ)
    (hG : ∀ g ∈ G, g.IsHomogeneous (deg g)) {f : Poly R N} {e : ℕ} (hf : f ∈ Ideal.span G)
    (he : f.IsHomogeneous e) :
    f ∈ Submodule.span R {z | ∃ g ∈ G, ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧
      d' + deg g = e ∧ z = h * g} := by
  obtain ⟨c, t, htG, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← homogeneousComponent_eq_self he, map_sum]
  refine Submodule.sum_mem _ fun g hg => ?_
  have hc := homogeneousComponent_mul_form (c g) g (hG g (htG hg)) e
  rw [smul_eq_mul]
  refine Submodule.span_le.mpr ?_ hc
  rintro _ ⟨h, d', hh, hd, rfl⟩
  exact Submodule.subset_span ⟨g, htG hg, h, d', hh, hd, rfl⟩

theorem isHomogeneous_totalDegree {g : Poly R N} {d : ℕ} (hg : g.IsHomogeneous d) :
    g.IsHomogeneous g.totalDegree := by
  by_cases h0 : g = 0
  · rw [h0]; exact isHomogeneous_zero _ _ _
  · rwa [hg.totalDegree h0]

end Forms

section Chart

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem form_mul_mem_twistMod {h : Poly k N} {d : ℕ} (hh : h.IsHomogeneous d) {c : ℤ} (I : Chart x)
    {o : Ω} (ho : o ∈ twistMod k x c I) : aeval x h * o ∈ twistMod k x (c + d) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x h * o ∈ twistMod k x (c + d) I) ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    exact Submodule.subset_span ⟨h * f, s, e, d + e', hs, hh.mul hf, hse, by push_cast; omega,
      by rw [map_mul, mul_div_assoc]⟩
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have := Submodule.smul_mem _ a hz
    rw [chartRing_smul_def] at this ⊢
    rwa [mul_left_comm]

theorem div_mem_chartRing {e : ℕ} (I : Chart x) {o : Ω} (ho : o ∈ twistMod k x e I) {s : Poly k N}
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) : o / aeval x s ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
  obtain ⟨a, rfl⟩ := ho
  have hq : x i ^ (e : ℤ) / aeval x s ∈ chartRing k x I :=
    ⟨X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, by rw [map_pow, aeval_X, zpow_natCast]⟩
  rw [chartRing_smul_def, mul_div_assoc]
  exact mul_mem a.2 hq

variable (T : StepData k x)

theorem StepData.form_mem_J {f : Poly k N} {e : ℕ} (hf : f ∈ T.J) (he : f.IsHomogeneous e) (I : Chart x)
    {δ : Ω} (hδ : δ ∈ T.D.sub I) : ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o := by
  have hG : ∀ g ∈ {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o}, g.IsHomogeneous g.totalDegree :=
    fun g ⟨c, hc, _⟩ => isHomogeneous_totalDegree hc
  have hmem := mem_span_forms_of_mem_ideal _ hG hf he
  refine Submodule.span_induction (p := fun f _ => ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o)
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨g, ⟨c, hc, hg⟩, h, d', hh, hd, rfl⟩
    by_cases h0 : g = 0
    · exact ⟨0, Submodule.zero_mem _, by rw [h0, mul_zero, map_zero, zero_mul, mul_zero]⟩
    obtain ⟨o, ho, hgo⟩ := hg I δ hδ
    rw [hc.totalDegree h0] at hd
    refine ⟨aeval x h * o, ?_, by rw [map_mul, mul_assoc, hgo, mul_left_comm]⟩
    have := form_mul_mem_twistMod hh I ho
    rwa [show (c : ℤ) + d' = e by omega] at this
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, zero_mul, mul_zero]⟩
  · rintro _ _ _ _ ⟨o, ho, h1⟩ ⟨o', ho', h2⟩
    exact ⟨o + o', Submodule.add_mem _ ho ho', by rw [map_add (f := _), add_mul, h1, h2, mul_add]⟩
  · rintro a _ _ ⟨o, ho, h1⟩
    refine ⟨a • o, (twistMod k x e I).smul_of_tower_mem a ho, ?_⟩
    rw [map_smul, smul_mul_assoc, h1, mul_smul_comm]

def StepData.Jg : FinGradedSub (S := k) (x := x) Ω where
  piece c := Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span k {z | ∃ (f : Poly k N)
      (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f}) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, hge, rfl, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, T.J.mul_mem_left f hg, hf.mul hge,
        by push_cast; ring, by rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; rw [smul_comm]; exact Submodule.smul_mem _ a hz
  fg := by
    classical
    set G : Set (Poly k N) := {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o} with hGdef
    have hJ : T.J = Ideal.span G := rfl
    have hfg : (Submodule.span (Poly k N) G).FG := IsNoetherian.noetherian _
    obtain ⟨G₀, hG₀, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
    have hG : ∀ g ∈ (G₀ : Set (Poly k N)), g.IsHomogeneous g.totalDegree :=
      fun g hg => by obtain ⟨c, hc, _⟩ := hG₀ hg; exact isHomogeneous_totalDegree hc
    let gj : Fin G₀.card → Poly k N := fun j => (G₀.equivFin.symm j : Poly k N)
    refine ⟨G₀.card, fun j => ((gj j).totalDegree : ℤ), fun j => aeval x (gj j), fun j => ?_, fun c => ?_⟩
    · refine Submodule.subset_span ⟨gj j, _, ?_, hG _ (G₀.equivFin.symm j).2, rfl, rfl⟩
      rw [hJ]; exact Ideal.subset_span (hG₀ (G₀.equivFin.symm j).2)
    · rw [Submodule.span_le]
      rintro _ ⟨f, e, hf, he, rfl, rfl⟩
      rw [hJ, Ideal.span, hspan] at hf
      have hm := mem_span_forms_of_mem_ideal _ hG hf he
      refine Submodule.span_induction (p := fun f _ => aeval x f ∈ _) ?_ ?_ ?_ ?_ hm
      · rintro _ ⟨g, hg, h, d', hh, hd, rfl⟩
        refine Submodule.subset_span ⟨G₀.equivFin ⟨g, hg⟩, h, d', hh, ?_, ?_⟩
        · simp only [gj, Equiv.symm_apply_apply]; omega
        · simp only [gj, Equiv.symm_apply_apply, map_mul, smul_eq_mul]
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz; rw [map_smul]; exact Submodule.smul_mem _ a hz

theorem StepData.Jg_tilde (I : Chart x) : (T.Jg.tildeSys 0).sub I = idealMod T.J I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ idealMod T.J I)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨f, e', hf, hfe, rfl, rfl⟩
      have he : e' = e := by omega
      subst he
      exact Submodule.subset_span ⟨f, s, e', hf, hs, hfe, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro c z _ hz; rw [smul_comm]; exact (idealMod T.J I).smul_of_tower_mem c hz
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    exact Submodule.subset_span ⟨aeval x f, s, e, e, hs, hse,
      Submodule.subset_span ⟨f, e, hf, hfe, rfl, rfl⟩, sub_self _, by rw [smul_eq_mul, div_eq_inv_mul]⟩

theorem StepData.isUnit_D (I : Chart x) : IsUnit (T.D.sub I) := by
  obtain ⟨i, hi⟩ := I.2.1
  have h0 : (twistSys k x 0).sub I = 1 := by
    change twistMod k x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  have hO : IsUnit ((twistSys k x (T.m - T.c₁)).sub I) :=
    IsUnit.of_mul_eq_one ((twistSys k x (-(T.m - T.c₁))).sub I) (by rw [twistSys_sub_mul, add_neg_cancel, h0])
  obtain ⟨Q', hQ'⟩ := T.M.invertible I
  rw [StepData.D, twistMul_sub]
  exact hO.mul ((IsUnit.of_mul_eq_one _ hQ').pow _)

theorem StepData.idealMod_mul_D (hZ : ZeroIdealChart.Statement.{u, w}) (I : Chart x) :
    idealMod T.J I * T.D.sub I = Submodule.span (chartRing k x I) {T.si} := by
  apply le_antisymm
  · refine Submodule.mul_le.mpr fun a ha δ hδ => ?_
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := idealMod_mem_form T.J I ha
    obtain ⟨o, ho, hgo⟩ := T.form_mem_J hg hge I hδ
    refine Submodule.mem_span_singleton.mpr ⟨⟨o / aeval x s, div_mem_chartRing I ho hs hse⟩, ?_⟩
    rw [chartRing_smul_def]
    change o / aeval x s * T.si = aeval x g / aeval x s * δ
    rw [div_mul_eq_mul_div (aeval x g), hgo]
    ring
  · obtain ⟨Q', hQ'⟩ := (T.isUnit_D I).exists_right_inv
    have hle : Submodule.span (chartRing k x I) {T.si} * Q' ≤ idealMod T.J I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ c (hZ k Ω N x T I b fun δ hδ => ?_)
      have h1 : b * δ ∈ T.D.sub I * Q' := by
        rw [mul_comm b]; exact Submodule.mul_mem_mul hδ hb
      rw [hQ', Submodule.mem_one] at h1
      obtain ⟨y, hy⟩ := h1
      rw [← hy]; exact y.2
    calc Submodule.span (chartRing k x I) {T.si}
        = Submodule.span (chartRing k x I) {T.si} * Q' * T.D.sub I := by
          rw [mul_assoc, mul_comm Q', hQ', mul_one]
      _ ≤ idealMod T.J I * T.D.sub I := Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (hle ha) hb

end Chart

theorem ClaimSeq.proof (hZ : ZeroIdealChart.Statement.{u, w}) : ClaimSeq.Statement.{u, w} := by
  intro k _ Ω _ _ N x T
  refine ⟨T.Jg, fun c => rfl, fun b c I z => ?_⟩
  have hm : (twistSys k x T.m).sub I = (twistSys k x T.c₁).sub I * (twistSys k x (T.m - T.c₁)).sub I := by
    rw [twistSys_sub_mul, show T.c₁ + (T.m - T.c₁) = T.m by ring]
  have hc : (twistSys k x (c + T.c₁)).sub I = (twistSys k x c).sub I * (twistSys k x T.c₁).sub I := by
    rw [twistSys_sub_mul]
  have hJD := T.idealMod_mul_D hZ I
  have hL : T.L.sub I = (twistSys k x T.c₁).sub I * T.D.sub I := by
    rw [StepData.L, StepData.D, twistMul_sub, twistMul_sub, hm, mul_assoc]
  have key : ((T.Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))).sub I =
      Submodule.span (chartRing k x I) {T.si} * ((T.L.pow b).twist (twistSys k x (c + T.c₁))).sub I := by
    simp only [SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, T.Jg_tilde I, hc, ← hJD, hL]
    ring
  rw [key, Submodule.mem_span_singleton_mul]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ClaimLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem coordGraded_tilde_mem_chartRing {I : Chart x} {y : Ω}
    (hy : y ∈ (coordGraded k x).tilde 0 I) : y ∈ chartRing k x I := by
  refine Submodule.span_induction (p := fun y _ => y ∈ chartRing k x I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hm' : m ∈ Submodule.span k {z | ∃ (f : Poly k N) (e' : ℕ), f.IsHomogeneous e' ∧
        (e' : ℤ) = a ∧ z = aeval x f} := hm
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ chartRing k x I)
      ?_ ?_ ?_ ?_ hm'
    · rintro _ ⟨f, e', hf, he', rfl⟩
      have hee : e' = e := by omega
      subst hee
      exact ⟨f, s, e', hs, hf, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact (chartRing k x I).zero_mem
    · intro a b _ _ ha hb; rw [smul_add]; exact (chartRing k x I).add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact (chartRing k x I).smul_mem ha r
  · exact (chartRing k x I).zero_mem
  · intro a b _ _ ha hb; exact (chartRing k x I).add_mem ha hb
  · intro a y _ hy; rw [chartRing_smul_def]; exact (chartRing k x I).mul_mem a.2 hy

theorem coordGraded_tildeSys_twist (X : SubSystem k x Ω) :
    ((coordGraded k x).tildeSys 0).twist X = X := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    have hyA := coordGraded_tilde_mem_chartRing hy
    have hqy : q • y = (⟨y, hyA⟩ : chartRing k x I) • q := by
      rw [smul_eq_mul, chartRing_smul_def, mul_comm]
    rw [SetLike.mem_coe, hqy]
    exact (X.sub I).smul_mem _ hq
  · intro q hq
    refine Submodule.subset_span ⟨q, hq, 1, ?_, by rw [smul_eq_mul, mul_one]⟩
    exact Submodule.subset_span ⟨1, 1, 0, 0, one_mem _, isHomogeneous_one _ _,
      Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩, by simp, by simp⟩

theorem twist_tildeSys_mono {M₁ M₂ : FinGradedSub (S := k) (x := x) Ω}
    (h : ∀ c, M₂.piece c ≤ M₁.piece c) (X : SubSystem k x Ω) (I : Chart x) :
    ∀ y ∈ ((M₂.tildeSys 0).twist X).sub I, y ∈ ((M₁.tildeSys 0).twist X).sub I := by
  intro y hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨q, hq, z, hz, rfl⟩
  refine ⟨q, hq, z, Submodule.span_mono ?_ hz, rfl⟩
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩

variable (T : StepData k x) (Jg : FinGradedSub (S := k) (x := x) Ω)
  (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
    f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f})


include hJg in
theorem claim_le : ∀ c, Jg.piece c ≤ (coordGraded k x).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, -, hf, he, rfl⟩
  exact ⟨f, e, hf, he, rfl⟩


include hJg in
theorem claim_kill : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → ∀ (a : ℤ),
    ∀ z ∈ (coordGraded k x).piece a, aeval x f • z ∈ Jg.piece (a + e) := by
  intro f e hf hfe a z hz
  have hz' : z ∈ Submodule.span k {z | ∃ (g : Poly k N) (e' : ℕ), g.IsHomogeneous e' ∧
      (e' : ℤ) = a ∧ z = aeval x g} := hz
  refine Submodule.span_induction (p := fun z _ => aeval x f • z ∈ Jg.piece (a + e)) ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨g, e', hg, he', rfl⟩
    rw [hJg]
    exact Submodule.subset_span ⟨f * g, e + e', T.J.mul_mem_right g hf, hfe.mul hg,
      by push_cast; omega, by rw [map_mul, smul_eq_mul]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha

end ClaimLemmas

theorem ClaimVanish.proof (h₁ : StepTwo.Statement.{u, w, w}) (h₂ : TwistVanish.Statement.{u, w})
    (h₃ : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  obtain ⟨Jg, hJg, hseq⟩ := h₃ k Ω N x T
  obtain ⟨cS, hS⟩ := h₁ k Ω N x T hK Ω (coordGraded k x) Jg (claim_le T Jg hJg)
    (claim_kill T Jg hJg)
  obtain ⟨cB, hB⟩ := h₂ k Ω N x (twistBundle k x 0) (twistBundle k x 1) N x (twist_hyps k N x).1
    (twist_hyps k N x).2
  refine ⟨max cS cB, fun b => ?_⟩
  induction b with
  | zero =>
    intro c hc
    have h0 := hB 0 c (le_trans (le_max_right _ _) hc)
    have e : ((twistBundle k x 0).twist ((twistBundle k x 1).pow 0)).twist (twistSys k x c) =
        (T.L.pow 0).twist (twistSys k x c) := by
      show ((twistSys k x 0).twist (twistSys k x 0)).twist (twistSys k x c) =
        (twistSys k x 0).twist (twistSys k x c)
      rw [twistSys_zero_twist]
    rw [e] at h0
    exact h0
  | succ b ih =>
    intro c hc
    have hq := hS (b + 1) c (le_trans (le_max_left _ _) hc)
    rw [coordGraded_tildeSys_twist] at hq
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))) ?_ ?_ hq
    · intro I y hy
      have hy' := twist_tildeSys_mono (claim_le T Jg hJg) _ I y hy
      rwa [coordGraded_tildeSys_twist] at hy'
    · exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b c)
        (ih (c + T.c₁) (le_trans hc (by linarith [T.c₁_pos])))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistAlg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem twistMul_twist_twistMul {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a a' : ℕ) (c c' : ℤ) :
    (twistMul M a c).twist (twistMul M a' c') = twistMul M (a + a') (c + c') := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line, twistMul_sub, twistMul_sub, twistMul_sub, pow_add,
    ← twistSys_sub_mul]
  ring

theorem TwistAlg.proof : TwistAlg.Statement.{u, w} := by
  intro S _ Ω _ _ N x M p q m m' b₁ b₂ h
  rw [pow_twistMul, pow_twistMul, pow_twistMul, twistMul_twist_twistMul]
  congr 1
  · ring
  · push_cast
    linear_combination (b₁ : ℤ) * h

end

end GroundTheory.Heights₂.Heights.Kleiman
end

