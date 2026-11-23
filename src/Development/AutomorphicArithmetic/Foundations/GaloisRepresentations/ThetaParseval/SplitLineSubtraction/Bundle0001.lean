module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.MetAndHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.ClTwHolds
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.clTw_holds :
    FrobSub → TwLoc → TwJumps → PstOfDR → WDFacts → ContLeft → ClTw := by
  intro hF hL hJ hP hW hC E Ω _ _ _ _ _ l _ ι a s μ hs hμ w S c J m h1 h2
  refine ⟨fun hw => (hF E Ω l ι a w S c μ (h1.1 hw)).2 s (h2.1 hw), ?_⟩
  intro P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, d1, j1, p1⟩ := h1.2 P AI hT A h O Bw hj
  obtain ⟨c2, d2, j2, p2⟩ := h2.2 P AI hT A h O Bw hj
  have e1 : (rk1 μ).comp (Dec (F := E) A).subtype = rk1 (μ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw s μ).comp (Dec (F := E) A).subtype =
      tw (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have e3 : Formalism.MainNotions.SumRepresentations.At.twGL (s.comp (Dec (F := E) A).subtype)
      (Matrix.GeneralLinearGroup.det.comp (rk1 (μ.comp (Dec (F := E) A).subtype))) =
      tw (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype) := by
    have hdet : Matrix.GeneralLinearGroup.det.comp (rk1 (μ.comp (Dec (F := E) A).subtype))
        = μ.comp (Dec (F := E) A).subtype := by
      ext g
      simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, UpperTheory.V.Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  rw [e1] at c1 d1 j1 p1
  rw [e2]
  have cs : Continuous (s.comp (Dec (F := E) A).subtype) := hs.comp continuous_subtype_val
  have cμ : Continuous (μ.comp (Dec (F := E) A).subtype) := hμ.comp continuous_subtype_val
  have ck := (hC _ (Qbar l) 1 1).2.2.2 _ cμ
  have ct := (hC _ (Qbar l) a 1).2.2.1 _ _ cs cμ
  obtain ⟨l1, l2⟩ := hL l P AI hT E Ω A O Bw a (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype)
  have dt := l1 d2 d1
  refine ⟨l2 c2 c1, dt, ?_, ?_⟩
  · intro τ LL' τ' hi
    exact hJ l P AI hT E Ω A O Bw a _ _ cs cμ τ (J τ) (m τ) (j2 τ LL' τ' hi) (j1 τ LL' τ' hi)
  · intro g
    have q1 := hP l P AI hT E Ω A O Bw a _ cs d2
    have q2 := hP l P AI hT E Ω A O Bw 1 _ ck d1
    have q3 := hP l P AI hT E Ω A O Bw a _ ct dt
    have hcs : Continuous fun g : ↥(Dec (F := E) A) =>
        ((s.comp (Dec (F := E) A).subtype g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) :=
      Units.continuous_val.comp cs
    have hck : Continuous fun g : ↥(Dec (F := E) A) =>
        ((rk1 (μ.comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l)) :=
      Units.continuous_val.comp ck
    rw [← e3] at q3
    have key := GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l P AI hT ι E Ω A w h O Bw hj a _ _ hcs hck q1 q2 q3
    rw [e3] at key
    rw [key]
    exact (hW E Ω A w h _ _).2.2.2 g S c (p2 g) (p1 g)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharAbove
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charAbove_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.HeckeLAdicCharacterDeRham → GlobalTheory.Published.AlgebraicCharacterWD → PstOfDR → ContLeft → CharAbove := by
  intro H hD hW hP hC E Ω _ _ _ _ _ l _ ι art ha χ n μ h1 h2 h3 w hu P AI hT A h O _ _ _ Bw hj
  obtain ⟨a, ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hξ := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) χ
  have d := hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj
  have hc : Continuous ((rk1 μ).comp (Dec (F := E) A).subtype) :=
    ((hC (G E Ω) (Qbar l) 0 0).2.2.2 μ h2).comp continuous_subtype_val
  have hr := hP l P AI hT E Ω A O Bw 1 _ hc d.1
  have e := hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha'
  have hun := (GlobalTheory.Published.CharCrysModel.isUnram_iff χ w).2 hu
  refine ⟨?_, d.1, d.2, fun g => ?_⟩
  · rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr, e, GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
    exact hun
  · have hv : (χ.loc w (a g) : ℂ) = ((χ.val w : ℂˣ) : ℂ) ^ (-deg g) := by
      have ho : GlobalTheory.SmGL.ord (w.adicCompletion E) (atFin w (unif w)) = 1 := by
        rw [GlobalTheory.SmGL.SphCompletion.ord_completion, show Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _ from unif_spec w]
        simp
      have h1 : ∀ x : (w.adicCompletion E)ˣ, χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x := fun x => by
        have h0 : GlobalTheory.SmGL.ord (w.adicCompletion E) (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 0 := by
          have hz : ∀ (y : (w.adicCompletion E)ˣ), GlobalTheory.SmGL.unrChar (w.adicCompletion E) (Units.mk0 2 two_ne_zero) y =
              (Units.mk0 (2:ℂ) two_ne_zero) ^ GlobalTheory.SmGL.ord _ y := fun _ => rfl
          let φ : (w.adicCompletion E)ˣ →* Multiplicative ℤ := MonoidHom.mk' (fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord _ y))
            fun y z => by rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
          have : φ (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 1 := by
            rw [map_mul, map_inv, map_zpow]
            simp [φ, ho, ← ofAdd_zsmul]
          exact this
        have := hun _ ((GlobalTheory.SmGL.ord_eq_zero_iff).1 h0)
        rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at this
        exact this
      rw [h1, ha'.ord_eq, Units.val_zpow_eq_zpow_val]
    rw [e, WD.charPol_eq_prod, GlobalTheory.LocLanglands.eig_lpOfChar]
    simp [unrPol, hv]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharEx
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charEx_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → CharFrob → CharAbove → CharInj → CharEx := by
  classical
  intro H hF hA hI E Ω _ _ _ _ _ l _ ι
  obtain ⟨art, hart, hex⟩ := H E Ω
  have hL : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r :=
    fun χ n h => (hex l ι χ n h).exists
  let L : HChar E → ((E →+* ℂ) → ℤ) → (G E Ω →* (Qbar l)ˣ) :=
    fun χ n => if h : IsAlgPos χ n then (hL χ n h).choose else 1
  have hspec : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      Continuous (L χ n) ∧ IsLAdicOf art ι χ n (L χ n) := by
    intro χ n h
    have e : L χ n = (hL χ n h).choose := dif_pos h
    rw [e]
    exact (hL χ n h).choose_spec
  refine ⟨L, fun χ n h => ⟨(hspec χ n h).1, fun w hw => ⟨fun hl => ?_, ?_⟩⟩, fun χ n χ' n' h h' e => ?_⟩
  · exact hF E Ω l ι art hart χ n (L χ n) (hspec χ n h).2 w hl hw
  · exact hA E Ω l ι art hart χ n (L χ n) h (hspec χ n h).1 (hspec χ n h).2 w hw
  · exact hI E Ω l ι art hart χ χ' n n' (L χ n) (hspec χ n h).2 (e ▸ (hspec χ' n' h').2)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharFrob
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

theorem charFrob_holds : CharFrob := by
  intro E Ω _ _ _ _ _ l _ ι art ha χ n μ h w hw hu A hA
  have hv : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∨ n = 0 := Or.inl hw
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : μ s = 1 := (h.unr_iff ha hv hA).mpr hu s hs
    simp [rk1, h1]
  · have h1 : ((μ σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val w : ℂˣ) : ℂ))⁻¹ := h.frob_unr ha hv hu hA hσ
    simp [rk1, Matrix.charpoly, Matrix.det_fin_one, h1, Polynomial.map_sub]

end UpperTheory.Gal.TP.Sub

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharInj
section
open NumberField Neutral.B1 GlobalTheory.HeckeGal
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charInj_holds :
    CharInj := by
  intro E Ω _ _ _ _ _ l _ ι art _ χ χ' n n' μ hχ hχ'
  have hl : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  have hfin := Ideal.finite_factors hl
  have hquot : χ * χ'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (χ * χ'⁻¹).1
      (χ * χ'⁻¹).2.1 (χ * χ'⁻¹).2.2 hfin.toFinset fun v hv x => ?_)
    have hl' : (l : 𝓞 E) ∉ v.asIdeal :=
      fun h => hv (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr h))
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := E) (Ω := Ω) (art (localIdele E v x))
    have a := hχ.loc_away (Or.inl hl') x σ hσ.symm
    have b := hχ'.loc_away (Or.inl hl') x σ hσ.symm
    have hloc : χ.loc v x = χ'.loc v x :=
      Units.ext (ι.symm.injective (a.symm.trans b))
    change χ.loc v x * (χ'.loc v x)⁻¹ = 1
    rw [hloc, mul_inv_cancel]
  exact mul_inv_eq_one.mp hquot
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClAway
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.clAway_holds :
    ClAway := by
  intro E Ω _ _ _ _ _ l _ ι a r w hl S J
  refine ⟨fun h => h.1 hl, fun h => ⟨fun _ => h, ?_⟩⟩
  intro P AI _ A hA O _ _ _ Bw hj
  exact absurd (hj.mem_placesOver hA) hl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClConj
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem exists_finExt_gl {l n : ℕ} [Fact l.Prime] (A : GL (Fin n) (Qbar l)) :
    ∃ K : FinExt l, ∀ i j, (A : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 := by
  let s : Set (Qbar l) := Set.range (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2) ∪
    Set.range (fun p : Fin n × Fin n => ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  haveI : Finite s := hs.to_subtype
  refine ⟨⟨IntermediateField.adjoin ℚ_[l] s,
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩, fun i j => ⟨?_, ?_⟩⟩
  · exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨(i, j), rfl⟩)
  · exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨(i, j), rfl⟩)

private theorem isdRAt_conj {l : ℕ} [Fact l.Prime] {P : LocPrime l} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {Bw : LocBridge l E Ω Gw O} {m : ℕ} {r : ↥Gw →* GL (Fin m) (Qbar l)} (A : GL (Fin m) (Qbar l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1)
    (hr : IsdRAt P Bw r) : IsdRAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r₀, hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := GlobalTheory.ConjCrys.exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, -⟩ := GlobalTheory.Pst.local_ext P Bw h r₀
  exact ⟨_, _, hM, (GlobalTheory.ConjCrys.local_conj P Bw _ M _).2.1 (hdR2.2 hc)⟩

theorem UpperTheory.Gal.TP.Sub.clConj_holds :
    CpFacts → ContLeft → PstOfDR → ClConj := by
  intro hCp hCont hPst E Ω _ _ _ _ _ l _ ι a r r' hr hiso w S J hcl
  obtain ⟨g, hg⟩ := id hiso
  obtain ⟨h1, h2⟩ := hcl
  refine ⟨fun hl A hA => ?_, ?_⟩
  · obtain ⟨i1, i2⟩ := h1 hl A hA
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · rw [hg, i1 s hs]
      simp
    · have e : (r' σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
          (r σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
        (hCp (G E Ω) (Qbar l) a a).2.2 r r' hiso σ⁻¹
      rw [e]
      exact i2 σ hσ
  · intro P AI hT A h O _ _ _ Bw hj
    obtain ⟨c1, c2, c3, c4⟩ := h2 P AI hT A h O Bw hj
    obtain ⟨K, hK⟩ := exists_finExt_gl (g⁻¹)
    have e : r'.comp (Dec (F := E) A).subtype =
        (MulAut.conj (g⁻¹)⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) A).subtype) := by
      ext1 x
      simp [hg, MulAut.conj_apply]
    have hc' : Continuous r' := (hCont (G E Ω) (Qbar l) a a).2.1 r r' hiso hr
    have cρ : Continuous (r.comp (Dec (F := E) A).subtype) := hr.comp continuous_subtype_val
    have cρ' : Continuous (r'.comp (Dec (F := E) A).subtype) := hc'.comp continuous_subtype_val
    have d' : IsdRAt P Bw (r'.comp (Dec (F := E) A).subtype) := by
      rw [e]
      exact isdRAt_conj _ K hK c2
    refine ⟨?_, d', fun τ LL' τ' hI => ?_, fun x => ?_⟩
    · rw [e]
      exact GlobalTheory.ConjCrys.isCrysAt_conj _ K hK c1
    · rw [e]
      exact GlobalTheory.ConjCrys.isJumpsAt_conj _ K hK (c3 τ LL' τ' hI)
    · rw [GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj (r.comp (Dec (F := E) A).subtype)
        (r'.comp (Dec (F := E) A).subtype) g (fun x => hg x)
        (hPst l P AI hT E Ω A O Bw a _ cρ c2) (hPst l P AI hT E Ω A O Bw a _ cρ' d')]
      exact c4 x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem cont_of_val {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (h : Continuous fun g => (r g : Matrix (Fin n) (Fin n) k)) : Continuous r := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have e : (fun g => (((r g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      (fun g => (r g : Matrix (Fin n) (Fin n) k)) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  rw [e]
  exact h.comp continuous_inv

private theorem val_cont {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} :
    Continuous fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k) := Units.continuous_val

private theorem sumRep_entry {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k)
    (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  have hi : finSumFinEquiv.symm (Fin.castAdd b i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
  have hj : finSumFinEquiv.symm (Fin.castAdd b j) = Sum.inl j := finSumFinEquiv_symm_apply_castAdd j
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
  rfl

theorem UpperTheory.Gal.TP.Sub.contLeft_holds :
    ContLeft := by
  intro Γ k _ _ _ _ _ _ a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s hc
    apply cont_of_val r
    have hm : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) := val_cont.comp hc
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have he : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) :=
      (continuous_apply _).comp ((continuous_apply _).comp hm)
    refine he.congr fun g => ?_
    exact sumRep_entry r s g i j
  · rintro r r' ⟨u, hu⟩ hr
    have hf : (⇑r') = fun x => u * r x * u⁻¹ := funext hu
    rw [hf]
    exact (continuous_const.mul hr).mul continuous_const
  · intro r c hr hc
    apply cont_of_val
    have hv : (fun g => ((tw r c g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) = fun g => ((c g : kˣ) : k) • (r g : Matrix (Fin a) (Fin a) k) := by
      funext g
      exact UpperTheory.V.Af.tw_val r c g
    rw [hv]
    exact (Units.continuous_val.comp hc).smul (val_cont.comp hr)
  · intro c hc
    apply cont_of_val
    have hv : (fun g => ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) = fun g => Matrix.diagonal fun _ => ((c g : kˣ) : k) := by
      funext g
      simp [rk1, Matrix.scalar_apply]
    rw [hv]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.comp hc)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCpFacts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.cpFacts_holds :
    CpFacts := by
  intro Γ k _ _ a b
  refine ⟨fun r s g => GlobalTheory.EigTwist.charpoly_sumRep r s g, ?_, ?_⟩
  · intro c g
    simp [cp, rk1, Matrix.charpoly, Matrix.charmatrix, Matrix.det_unique]
  · rintro r r' ⟨u, hu⟩ g
    simp only [cp, hu, Units.val_mul]
    rw [Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj u (r g : Matrix (Fin a) (Fin a) k)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PDenseId
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

theorem denseId_holds : CpFacts → DgFacts → DenseId := by
  intro _ _ Γ _ _ l _ m m' t t' r r' a a' hr hr' ha ha' D hD hEq g
  apply Polynomial.funext
  intro x
  have key : ∀ {n : ℕ} (s : Γ →* GL (Fin n) (Qbar l)), Continuous s →
      Continuous fun g => (cp s g).eval x := by
    intro n s hs
    simp only [cp, Matrix.eval_charpoly]
    exact (continuous_const.sub (Units.continuous_val.comp hs)).matrix_det
  have keyl : ∀ {n : ℕ} (b : Fin n → Γ →* (Qbar l)ˣ), (∀ i, Continuous (b i)) →
      Continuous fun g => (lin b g).eval x := by
    intro n b hb
    simp only [lin, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact continuous_finsetProd _ fun i _ =>
      continuous_const.sub (Units.continuous_val.comp (hb i))
  have h := Continuous.ext_on hD ((key r hr).mul (keyl a' ha')) ((key r' hr').mul (keyl a ha))
    (fun g hg => by
      simp only [Pi.mul_apply]
      rw [← Polynomial.eval_mul, ← Polynomial.eval_mul, hEq g hg])
  have hg := congrFun h g
  simp only [Pi.mul_apply] at hg
  rw [Polynomial.eval_mul, Polynomial.eval_mul]
  exact hg

end UpperTheory.Gal.TP.Sub

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPstOfDR
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.pstOfDR_holds :
    GlobalTheory.Published.DeRhamPotSemistable → PstOfDR := by
  intro hB l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r hr hd
  obtain ⟨T⟩ := hT
  exact hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
end

