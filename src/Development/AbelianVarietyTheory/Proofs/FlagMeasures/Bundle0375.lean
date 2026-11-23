module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0060
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0030
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0373
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerCongruentLocalModGOnePlace
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CongrLoc

private lemma exists_integer_mul_eq_of_valuation_le (D : D7) (q : PlF D) (x y : D.host.F) (hy : y ≠ 0)
    (h : q.valuation D.host.F x ≤ q.valuation D.host.F y) :
    ∃ β ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp),
      (D.s.atP q).ιF x = (D.s.atP q).ιF y * β := by
  have hle : (D.s.atP q).ιF x ≤ᵥ (D.s.atP q).ιF y := ((D.s.atP q).val x y).2 h
  have hv := (Valuation.vle_iff_le (ValuativeRel.valuation (D.s.atP q).Fp)).1 hle
  have hy' : (D.s.atP q).ιF y ≠ 0 := (map_ne_zero _).2 hy
  have hpos : 0 < ValuativeRel.valuation (D.s.atP q).Fp ((D.s.atP q).ιF y) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy')
  refine ⟨(D.s.atP q).ιF x / (D.s.atP q).ιF y, ?_, ?_⟩
  · rw [Valuation.mem_integer_iff, map_div₀]
    exact (div_le_one₀ hpos).2 hv
  · field_simp

private lemma algebraMap_mem_O_of_mem_integer' (D : D7) (q : PlF D) (w : (D.s.atP q).Fp)
    (hw : w ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp)) :
    algebraMap (D.s.atP q).Fp (D.s.atP q).Ep w ∈ (D.s.atP q).O := by
  rw [(D.s.atP q).O_def]
  exact isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp))
    (x := (⟨w, hw⟩ : Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp)))

private lemma exists_smul_sub_eq_gS_mul_mem_O (D : D7) (p : PlF D) (f : (D.s.atP p).Fp) (e : D.host.E) :
    ∃ b : D.host.E, ∃ o ∈ (D.s.atP p).O,
      f • (D.s.atP p).ιE e - (D.s.atP p).ιE b = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  classical
  have := (D.s.atP p).char0
  have := (D.s.atP p).lf
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Pf.StabIntSh.gS_ne
  have hgN : (gS D : ℕ) ≠ 0 := by
    intro h
    apply hg0
    simp [h]
  have halg : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).mpr inferInstance
  obtain ⟨d, hd0, hdint⟩ := (halg.isAlgebraic e).exists_integral_multiple

  set u : (D.s.atP p).Fp := ((gS D : ℕ) : (D.s.atP p).Fp) * ((d : ℤ) : (D.s.atP p).Fp) with hu
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)
  have hvu : ValuativeRel.valuation (D.s.atP p).Fp u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hnhds : {z : (D.s.atP p).Fp | ValuativeRel.valuation (D.s.atP p).Fp (z - f) <
      ((Units.mk0 _ hvu : (ValuativeRel.ValueGroupWithZero (D.s.atP p).Fp)ˣ) : ValuativeRel.ValueGroupWithZero (D.s.atP p).Fp)} ∈ nhds f :=
    (IsValuativeTopology.mem_nhds_iff').2 ⟨Units.mk0 _ hvu, subset_rfl⟩
  obtain ⟨a, ha⟩ := (D.s.atP p).dense.mem_nhds hnhds
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at ha

  have hβ : ValuativeRel.valuation (D.s.atP p).Fp ((f - (D.s.atP p).ιF a) / u) ≤ 1 := by
    rw [map_div₀, ← Valuation.map_neg, neg_sub]
    exact (div_le_one₀ (zero_lt_iff.2 hvu)).2 ha.le
  refine ⟨algebraMap D.host.F D.host.E a * e,
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((f - (D.s.atP p).ιF a) / u) * (D.s.atP p).ιE ((d : ℤ) • e),
    mul_mem (algebraMap_mem_O_of_mem_integer' D p _ ((Valuation.mem_integer_iff _ _).2 hβ))
      (Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨(d : ℤ) • e, hdint⟩), ?_⟩
  rw [map_mul, (D.s.atP p).compat, zsmul_eq_mul, map_mul, map_intCast, map_natCast, Algebra.smul_def]
  have hsplit : f = (f - (D.s.atP p).ιF a) / u * u + (D.s.atP p).ιF a := by
    field_simp
    ring
  conv_lhs => rw [hsplit]
  rw [hu]
  simp only [map_add (f := _), map_mul, map_natCast, map_intCast]
  ring

private lemma exists_pow_mul_finset_sum_mem_subring (D : D7) (p : PlF D) (x : (D.s.atP p).Ep) :
    ∃ b : D.host.E, ∃ o ∈ (D.s.atP p).O,
      x - (D.s.atP p).ιE b = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  classical
  have hx : x ∈ Submodule.span (D.s.atP p).Fp (Set.range (D.s.atP p).ιE) := by
    rw [(D.s.atP p).span]
    exact Submodule.mem_top
  obtain ⟨w, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx
  rw [Finsupp.sum]
  induction w.support using Finset.induction_on with
  | empty => exact ⟨0, 0, zero_mem _, by simp⟩
  | insert i s hi ih =>
    obtain ⟨b₁, o₁, ho₁, h₁⟩ := ih
    obtain ⟨b₂, o₂, ho₂, h₂⟩ := exists_smul_sub_eq_gS_mul_mem_O D p (w i) i
    refine ⟨b₂ + b₁, o₂ + o₁, add_mem ho₂ ho₁, ?_⟩
    rw [Finset.sum_insert hi, map_add (f := _), mul_add, ← h₁, ← h₂]
    ring

private lemma exists_intValuation_sub_one_le_and_le_elsewhere (D : D7) (p : PlF D) (r : 𝓞 D.host.F) (hr : r ≠ 0) :
    ∃ t : 𝓞 D.host.F, p.intValuation (t - 1) ≤ p.intValuation r ∧
      ∀ q : PlF D, q ≠ p → q.intValuation t ≤ q.intValuation r := by
  classical
  have hfin : {q : PlF D | r ∈ q.asIdeal}.Finite := by
    have hI : Ideal.span {r} ≠ 0 := by
      simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
    refine (Ideal.finite_factors hI).subset ?_
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq ⊢
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert p hfin.toFinset)
    (fun q : PlF D => q.asIdeal) (fun q => multiplicity q.asIdeal (Ideal.span {r}))
    (fun q _ => q.prime) (fun q _ q' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun q => if (q : PlF D) = p then 1 else 0)
  refine ⟨y, ?_, ?_⟩
  · have h := hy p (Finset.mem_insert_self _ _)
    simp only [if_true] at h
    rw [p.intValuation_eq_exp_neg_multiplicity hr]
    exact (p.intValuation_le_pow_iff_mem _ _).2 h
  · intro q hq
    by_cases hqs : r ∈ q.asIdeal
    · have h := hy q (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hqs))
      simp only [hq, if_false, sub_zero] at h
      rw [q.intValuation_eq_exp_neg_multiplicity hr]
      exact (q.intValuation_le_pow_iff_mem _ _).2 h
    · rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hqs]
      exact q.intValuation_le_one _

theorem exists_int_congr_gS : ∀ (D : D7) (p : PlF D) (c : (D.s.atP p).Ep), c ∈ (D.s.atP p).O → ∃ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - c = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) ∧ ∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p c hc
  classical
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Pf.StabIntSh.gS_ne
  have hgN : (gS D : ℕ) ≠ 0 := by
    intro h
    apply hg0
    simp [h]

  obtain ⟨b₀, o₀, ho₀, h₀⟩ := exists_pow_mul_finset_sum_mem_subring D p c
  have halg : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).mpr inferInstance
  obtain ⟨d, hd0, hdint⟩ := (halg.isAlgebraic b₀).exists_integral_multiple
  set r : 𝓞 D.host.F := ((gS D : ℕ) : 𝓞 D.host.F) * ((d : ℤ) : 𝓞 D.host.F) with hr
  have hr0 : r ≠ 0 := mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)

  obtain ⟨t, ht₁, ht₂⟩ := exists_intValuation_sub_one_le_and_le_elsewhere D p r hr0
  set a : D.host.E := algebraMap D.host.F D.host.E (t : D.host.F) * b₀ with ha
  have hιa : ∀ q : PlF D, (D.s.atP q).ιE a =
      algebraMap (D.s.atP q).Fp (D.s.atP q).Ep ((D.s.atP q).ιF (t : D.host.F)) * (D.s.atP q).ιE b₀ := by
    intro q
    rw [ha, map_mul, (D.s.atP q).compat]
  have hG : ∀ q : PlF D, (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) ∈ (D.s.atP q).O := by
    intro q
    rw [map_natCast]
    exact natCast_mem _ _
  have hb₀ : (D.s.atP p).ιE b₀ ∈ (D.s.atP p).O := by
    have : (D.s.atP p).ιE b₀ = c - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o₀ := by
      rw [← h₀]; ring
    rw [this]
    exact sub_mem hc (mul_mem (hG p) ho₀)
  have hdb : ∀ q : PlF D, (D.s.atP q).ιE ((d : ℤ) • b₀) ∈ (D.s.atP q).O :=
    fun q => Formalism.L2.SG.Pf.StabIntSh.lg_iota_int q ⟨(d : ℤ) • b₀, hdint⟩

  have hp : ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE a - c = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
    have hle : p.valuation D.host.F ((t : D.host.F) - 1) ≤ p.valuation D.host.F ((gS D : ℕ) : D.host.F) := by
      have e1 : ((t : D.host.F) - 1) = algebraMap (𝓞 D.host.F) D.host.F (t - 1) := by simp
      have e2 : ((gS D : ℕ) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F ((gS D : ℕ) : 𝓞 D.host.F) := by simp
      rw [e1, e2, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      refine ht₁.trans ?_
      rw [hr, map_mul]
      exact mul_le_of_le_one_right' (p.intValuation_le_one _)
    obtain ⟨β, hβ, hβe⟩ := exists_integer_mul_eq_of_valuation_le D p _ _ (by exact_mod_cast hgN) hle
    refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep β * (D.s.atP p).ιE b₀ - o₀,
      sub_mem (mul_mem (algebraMap_mem_O_of_mem_integer' D p β hβ) hb₀) ho₀, ?_⟩
    have ht : (D.s.atP p).ιF (t : D.host.F) = (D.s.atP p).ιF ((gS D : ℕ) : D.host.F) * β + 1 := by
      rw [← hβe, map_sub, map_one]; ring
    rw [hιa p, ht, map_add (f := _), map_mul, map_one, map_natCast, map_natCast, map_natCast]
    have : c = (D.s.atP p).ιE b₀ + ((gS D : ℕ) : (D.s.atP p).Ep) * o₀ := by
      rw [← map_natCast (D.s.atP p).ιE, ← h₀]; ring
    rw [this]
    ring

  have hq : ∀ q : PlF D, q ≠ p →
      ∃ o ∈ (D.s.atP q).O, (D.s.atP q).ιE a = (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) * o := by
    intro q hqp
    have hle : q.valuation D.host.F (t : D.host.F) ≤
        q.valuation D.host.F (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) := by
      have e1 : (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F r := by
        simp [hr]
      rw [e1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact ht₂ q hqp
    have hne : (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)
    obtain ⟨β, hβ, hβe⟩ := exists_integer_mul_eq_of_valuation_le D q _ _ hne hle
    refine ⟨algebraMap (D.s.atP q).Fp (D.s.atP q).Ep β * (D.s.atP q).ιE ((d : ℤ) • b₀),
      mul_mem (algebraMap_mem_O_of_mem_integer' D q β hβ) (hdb q), ?_⟩
    rw [hιa q, hβe, zsmul_eq_mul]
    simp only [map_mul, map_intCast, map_natCast]
    ring

  have hloc : ∀ q : PlF D, (D.s.atP q).ιE a ∈ (D.s.atP q).O := by
    intro q
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨o, ho, he⟩ := hp
      have : (D.s.atP q).ιE a = c + (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) * o := by
        rw [← he]; ring
      rw [this]
      exact add_mem hc (mul_mem (hG q) ho)
    · obtain ⟨o, ho, he⟩ := hq q hqp
      rw [he]
      exact mul_mem (hG q) ho
  have hint : IsIntegral ℤ a := Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc a hloc
  exact ⟨⟨a, hint⟩, hp, hq⟩

end GlobalTheory.CongrLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusFamilyCarriedByLatticeInLocalOrbits
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.GlueOrbit

variable {D : D7}

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hmap : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E (((LatLoc.cE D).toLinearMap) '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (LatLoc.cE D).surjective
  have := (_root_.GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hmap).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

theorem img_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (L : Submodule M.L.O V) :
    LocNG.img (1 : V ≃ₗ[E] V) L = L := by
  ext x
  simp [LocNG.img]

theorem img_lattice {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  unfold LocNG.img
  rw [Submodule.map_coe]
  have e1 : (⇑((g : V →ₗ[E] V).restrictScalars M.L.O) : V → V) = ⇑(g : V →ₗ[E] V) := rfl
  rw [e1, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem glue_local_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y y' : Dat Z FP), LocOver Λ y → InGen y y' → ∃ Λ', LocOver Λ' y' ∧ ∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ' := by
  intro D X Y u u' F F' w _ _ Z FP _ hR Λ y y' ⟨hΛ, hτ⟩ ⟨hrel, hfin⟩
  have key : ∀ p, ∃ h ∈ (FP p).UW0, (y' p = y p → h = 1) ∧
      ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (y' p) τ ∧
        τ.abelian₂ = LocNG.img h (lattice₂ D Z.M p Λ) := by
    intro p
    obtain ⟨τ, hτ1, hτ2⟩ := hτ p
    by_cases hp : y' p = y p
    · exact ⟨1, one_mem _, fun _ => rfl, τ, hp ▸ hτ1, by rw [img_one, hτ2]⟩
    · obtain ⟨g, hg, hm⟩ := hrel p
      exact ⟨g, hg, fun h => absurd h hp, _,
        (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p) g hg
          (y p) (y' p) τ hτ1 hm).1, by rw [← hτ2]⟩
  choose h hU h1 τ hτ1 hτ2 using key
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
  obtain ⟨t, ht, heq⟩ := hτ p
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (_root_.GlobalTheory.GenMass.Fibre.termLat D Z FP p (y p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    let U := Submodule.span D.host.E (Λ : Set (VS D).V)
    let b := Module.finBasis D.host.E U
    let W := Submodule.span (D.s.atP p).Ep
      (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
    have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
      have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
      change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
      rw [map_sum, map_sum] at hx
      rw [← hx]
      exact W.sum_mem fun i _ => by
        rw [map_smul, baseChange_smul₂]
        exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have htop : W = ⊤ := by
      apply top_le_iff.mp
      rw [← hspan, lattice₂, Submodule.span_span_of_tower]
      refine Submodule.span_le.2 ?_
      rintro y ⟨x, hx, heq⟩
      rw [← heq]
      exact hW ⟨x, Submodule.subset_span hx⟩
    refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
    rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
    simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
      finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
  obtain ⟨Λ', hΛ', hp⟩ := (_root_.GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).2 Λ hfull (fun p => LocNG.img (h p) (lattice₂ D Z.M p Λ))
    (fun p => by
      obtain ⟨t, ht, heq⟩ := hτ p
      apply img_lattice
      rw [← heq]
      exact _root_.GlobalTheory.GenMass.Fibre.termLat D Z FP p (y p) t ht)
    (hfin.subset fun p hp hc => hp (by simp only [h1 p hc, img_one]))
  exact ⟨Λ', ⟨hΛ', fun p => ⟨τ p, hτ1 p, (hτ2 p).trans (hp p).symm⟩⟩, fun p => ⟨h p, hU p, (hp p).symm⟩⟩

end GlobalTheory.Unfold.GlueOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroup
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusStab

theorem finrank_Vp_k (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem inGen_of_gRel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y' := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel Λ d y y' hov hgen hgr
  obtain ⟨hext, hUW, -, hmove⟩ := _root_.GlobalTheory.RatLocMove.rat_ext_moves D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨h, hh, hmv⟩ := hgr
  obtain ⟨y'', hov'', hmv''⟩ := hmove h hh Λ y hov
  have hact := fun p => _root_.GlobalTheory.InnerDatumAct.exists_mulAction (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_k D p) (hRel p)
  choose act hiff _ using hact
  have heq : ∀ p, y' p = y'' p := by
    intro p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    obtain ⟨g2, he2, hm2⟩ := hmv'' p
    obtain rfl : g1 = g2 := (hext h p).unique he1 he2
    have hg : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a1 := ((hiff p) ⟨g1, hg⟩ (y p) (y' p)).1 hm1
    have a2 := ((hiff p) ⟨g1, hg⟩ (y p) (y'' p)).1 hm2
    rw [← a1, ← a2]
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨g0, hg0, hm0⟩ := hgen.1 p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    have hg1 : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a0 := ((hiff p) ⟨g0, hg0⟩ (d p) (y p)).1 hm0
    have a1 := ((hiff p) ⟨g1, hg1⟩ (y p) (y' p)).1 hm1
    refine ⟨g1 * g0, mul_mem hg1 hg0, ((hiff p) ⟨g1 * g0, mul_mem hg1 hg0⟩ (d p) (y' p)).2 ?_⟩
    letI := act p
    let a : (FP p).UW0 := ⟨g1, hg1⟩
    let b : (FP p).UW0 := ⟨g0, hg0⟩
    have hm : (a * b) • d p = a • (b • d p) := mul_smul a b (d p)
    change (a * b) • d p = y' p
    rw [hm]
    change a • (act p).smul b (d p) = y' p
    rw [a0]
    exact a1
  · have full_of_over (L : LV D) (z : Dat Z FP) (hz : LocOver L z) :
        Submodule.IsFullLattice D.host.E L := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
      obtain ⟨t, ht, heq⟩ := hz.2 p
      have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p L : Set (Vp D p)) = ⊤ := by
        rw [← heq]
        exact (_root_.GlobalTheory.GenMass.Fibre.termLat D Z FP p (z p) t ht).2
      let U := Submodule.span D.host.E (L : Set (VS D).V)
      let b := Module.finBasis D.host.E U
      let W := Submodule.span (D.s.atP p).Ep
        (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
      have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
        have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
        change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
        rw [map_sum, map_sum] at hx
        rw [← hx]
        exact W.sum_mem fun i _ => by
          rw [map_smul, baseChange_smul₂]
          exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
      have htop : W = ⊤ := by
        apply top_le_iff.mp
        rw [← hspan, lattice₂, Submodule.span_span_of_tower]
        refine Submodule.span_le.2 ?_
        rintro y ⟨x, hx, heq⟩
        rw [← heq]
        exact hW ⟨x, Submodule.subset_span hx⟩
      refine { toIsLattice := hz.1, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
      rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
      simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
        finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
    have hfin := ((_root_.GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).1 Λ (Formalism.HermitianLatticesTheory.gmap h Λ) (full_of_over Λ y hov) (full_of_over _ y'' hov'')).1
    refine (hfin.union hgen.2).subset fun p hp => ?_
    by_cases hyd : y p = d p
    · left
      intro hl
      apply hp
      rw [heq p, ← hyd]
      obtain ⟨τ, hτ, hL⟩ := hov.2 p
      obtain ⟨τ'', hτ'', hL''⟩ := hov''.2 p
      have hlam : τ''.abelian₂ = τ.abelian₂ := by rw [hL'', hL]; exact hl.symm
      have key := _root_.GlobalTheory.HL.LatUniq.datum_of_lattice (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
        (finrank_Vp_k D p) (hRel p) (y'' p) (y p) τ'' τ hτ'' hτ
      exact key hlam
    · right
      exact hyd

end GlobalTheory.GenusStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingLeadingMinorEqOfUnitriangularChangesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (f f' g g' : Fin (r + 1) → V) (hg : Tri E f g) (hg' : Tri E f' g') (l : ℕ), H.Dl g g' l = H.Dl f f' l := by
  first | exact @GlobalTheory.MinorTri.Dl_eq_of_tri | exact GlobalTheory.MinorTri.Dl_eq_of_tri | (intros; apply GlobalTheory.MinorTri.Dl_eq_of_tri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDictGoodOpNonempty
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem rowDict_goodOp_nonempty :
    ∀ (D : D7) (X : HidaSetting D), Nonempty (Formalism.L2.SG.RowDict.GoodOp X) :=
  fun _ X => Formalism.L2.SG.Pf.rowDictGoodOp_exists X

end GlobalTheory
end

