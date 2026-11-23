module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLaw
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovMul

open GlobalTheory.Amp.Swap GlobalTheory.DegVol.Swap

variable {k r j : ℕ}

theorem upperIn_0 (β : Fin r → ℕ) : upperIn β 0 = 1 := by
  ext a b
  by_cases h : a < b
  · simp [upperIn, upper, h, h.ne]
  · simp [upperIn, upper, h, Matrix.one_apply]

private lemma wI_eq_mI (m : Fin (k + 1)) : wI k r m = UEmb.mI k r m := Fin.ext (by simp [wI, UEmb.mI])

theorem pOf_mul_we (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a : Fin (k + 1)) (b : Fin r) :
    (pOf k r q * uEmb k r u) (wI k r a) (eI k r b) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Rad.cases3 (P := fun l => pOf k r q (wI k r a) l * uEmb k r u l (eI k r b) = 0) ?_ ?_ ?_ l
  · intro c
    simp only [pOf, Rad.pEl_we, zero_mul]
  · intro c
    rw [wI_eq_mI c, UEmb.u_me, mul_zero]
  · intro c
    rw [UEmb.u_se, mul_zero]

theorem pOf_mul_se (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (pOf k r q * uEmb k r u) (esI k r a) (eI k r b) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Rad.cases3 (P := fun l => pOf k r q (esI k r a) l * uEmb k r u l (eI k r b) = 0) ?_ ?_ ?_ l
  · intro c
    simp only [pOf, Rad.pEl_se, zero_mul]
  · intro c
    rw [wI_eq_mI c, UEmb.u_me, mul_zero]
  · intro c
    rw [UEmb.u_se, mul_zero]

private lemma crd_eI_eI (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    crd k r j β x (eI k r a) (eI k r b) = upperIn β x.1 a b := by
  simp only [crd, pTop]
  exact pOf_mul_ee _ _ a b

private lemma crd_mI_eI_eq_zero (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (m : Fin (k + 1)) (b : Fin r) :
    crd k r j β x (UEmb.mI k r m) (eI k r b) = 0 := by
  rw [← wI_eq_mI]
  simp only [crd, pTop]
  exact pOf_mul_we _ _ m b

private lemma crd_esI_eI_eq_zero (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    crd k r j β x (esI k r a) (eI k r b) = 0 := by
  simp only [crd, pTop]
  exact pOf_mul_se _ _ a b

theorem upperIn_mul (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) :
    upperIn β w.1 = upperIn β p.1 * upperIn β q.1 := by
  ext a b
  have e : (crd k r j β p * crd k r j β q) (eI k r a) (eI k r b) = crd k r j β w (eI k r a) (eI k r b) := by
    rw [h]
  rw [crd_eI_eI, Matrix.mul_apply, UEmb.sum_idx] at e
  simp only [crd_mI_eI_eq_zero, crd_esI_eI_eq_zero, crd_eI_eI, mul_zero, Finset.sum_const_zero, add_zero] at e
  rw [← e, Matrix.mul_apply]

theorem upper_mul_entry (x y : UT r → ℂ) (i : UT r)
    (hx : ∀ l : UT r, l.1.2.val - l.1.1.val < i.1.2.val - i.1.1.val → x l = 0) :
    (upper x * upper y) i.1.1 i.1.2 = x i + y i := by
  obtain ⟨⟨a, b⟩, hab⟩ := i
  rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab.ne]
  · simp only [upper, lt_irrefl, dif_neg, not_false_eq_true, if_true, dif_pos hab, one_mul, mul_one]
    exact add_comm _ _
  · rintro c ⟨hca, hcb⟩
    simp only [upper]
    by_cases h1 : a < c
    · by_cases h2 : c < b
      · have hl : c.val - a.val < b.val - a.val := by
          have := Fin.lt_def.mp h1; have := Fin.lt_def.mp h2; omega
        rw [dif_pos h1, hx ⟨(a, c), h1⟩ hl, zero_mul]
      · rw [dif_neg h2, if_neg hcb, mul_zero]
    · rw [dif_neg h1, if_neg (Ne.symm hca), zero_mul]

theorem first (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) (i : UTin β)
    (hi : ∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) :
    w.1 i = p.1 i + q.1 i := by
  have e := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M i.1.1.1 i.1.1.2) (upperIn_mul β p q w h)
  simp only [upperIn] at e
  rw [upper_mul_entry _ _ i.1] at e
  · simpa [upper, i.1.2, i.2] using e
  · intro l hl
    split_ifs with hβ
    · exact hi ⟨l, hβ⟩ hl
    · rfl

theorem cancel (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) (hp : p.1 = 0) :
    pTop k r j p.2 * pTop k r j q.2 = pTop k r j w.2 := by
  have hm := upperIn_mul β p q w h
  rw [hp, upperIn_0, one_mul] at hm
  set U := upperIn β q.1 with hUdef
  have hT : U.IsUpperTriangular := by
    intro a b hba
    have h1 : ¬ a < b := not_lt.mpr hba.le
    have h2 : a ≠ b := ne_of_gt hba
    simp [hUdef, upperIn, upper, h1, h2]
  have hU : IsUnit U.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    simp [hUdef, upperIn, upper]
  have hV : uEmb k r U * uEmb k r U⁻¹ = 1 := by
    rw [← UEmb.uEmb_mul, Matrix.mul_nonsing_inv _ hU, UEmb.uEmb_one]
  have h' : pTop k r j p.2 * pTop k r j q.2 * uEmb k r U = pTop k r j w.2 * uEmb k r U := by
    have h2 := h
    simp only [crd, hp, upperIn_0, UEmb.uEmb_one, mul_one, hm] at h2
    rw [mul_assoc]
    exact h2
  calc pTop k r j p.2 * pTop k r j q.2
      = pTop k r j p.2 * pTop k r j q.2 * uEmb k r U * uEmb k r U⁻¹ := by rw [mul_assoc _ (uEmb k r U), hV, mul_one]
    _ = pTop k r j w.2 * uEmb k r U * uEmb k r U⁻¹ := by rw [h']
    _ = pTop k r j w.2 := by rw [mul_assoc, hV, mul_one]

private lemma eq_and_eq_of_pEl_eq (B B' : Fin r → Fin (k + 1) → ℂ) (S S' : Matrix (Fin r) (Fin r) ℂ)
    (h : pEl k r B S = pEl k r B' S') : B = B' ∧ S = S' := by
  have hB : B = B' := by
    funext b c
    simpa [Rad.pEl_ws] using
      congrArg (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M (wI k r c) (esI k r b)) h
  subst hB
  refine ⟨rfl, ?_⟩
  ext a b
  simpa [Rad.pEl_es] using
    congrArg (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M (eI k r a) (esI k r b)) h

theorem crd_mul : ∀ (k r j : ℕ) (β : Fin r → ℕ), crd k r j β 0 = 1 ∧ ∀ p q w : (UTin β → ℂ) × PTop k r j, crd k r j β p * crd k r j β q = crd k r j β w → (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  intro k r j β
  refine ⟨?_, fun p q w h => ⟨fun i hi => first β p q w h i hi, fun hp => ?_, fun hp hB => ?_⟩⟩
  · have hS : skewM (r := r) (fun _ => 0) (fun _ => 0) = 0 := by
      ext a b
      simp only [skewM, Matrix.zero_apply]
      split_ifs <;> simp
    simp only [crd, Prod.fst_zero, Prod.snd_zero, upperIn_0, UEmb.uEmb_one, mul_one, pTop, pOf,
      Pi.zero_apply, dite_eq_ite, ite_self, hS]
    exact Rad.pEl_zero
  · have hc := cancel β p q w h hp
    simp only [pTop, pOf] at hc
    rw [Rad.pEl_mul] at hc
    have hB' := (eq_and_eq_of_pEl_eq _ _ _ _ hc).1
    funext a c
    have e := congrFun (congrFun hB' a.1) c
    simpa [a.2] using e.symm
  · have hc := cancel β p q w h hp
    simp only [pTop, pOf, hB, Pi.zero_apply, dite_eq_ite, ite_self] at hc
    rw [Rad.pEl_mul] at hc
    have hS' := (eq_and_eq_of_pEl_eq _ _ _ _ hc).2
    simp only [Rad.herm_Hb] at hS'
    ext x
    · obtain ⟨⟨⟨a, b⟩, hab⟩, hj⟩ := x
      have e := congrFun (congrFun hS' a) b
      simp [skewM, hab, hj] at e
      simpa using e.symm
    · obtain ⟨a, ha⟩ := x
      have e := congrArg Complex.im (congrFun (congrFun hS' a) a)
      simp [skewM, ha] at e
      simpa using e.symm

end GlobalTheory.DegVol.RefCovMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.ReImLattice

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem covolume_prod (μ : Measure E) [μ.IsAddHaarMeasure] (L L' : Submodule ℤ E)
    [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L] [IsZLattice ℝ L'] :
    ZLattice.covolume (L.prod L') (μ.prod μ) = ZLattice.covolume L μ * ZLattice.covolume L' μ := by
  have hD : IsAddFundamentalDomain (L.prod L') (latticeDomain L ×ˢ latticeDomain L')
      (μ.prod μ) := by
    refine IsAddFundamentalDomain.mk' ((measurableSet_latticeDomain L).prod
      (measurableSet_latticeDomain L')).nullMeasurableSet fun x => ?_
    obtain ⟨a, ha, hu⟩ := existsUnique_add_mem_latticeDomain L x.1
    obtain ⟨a', ha', hu'⟩ := existsUnique_add_mem_latticeDomain L' x.2
    refine ⟨⟨(a, a'), a.2, a'.2⟩, ⟨?_, ?_⟩, ?_⟩
    · simpa [Submodule.vadd_def, add_comm] using ha
    · simpa [Submodule.vadd_def, add_comm] using ha'
    · rintro ⟨b, hb⟩ hb'
      have h1 := hu ⟨b.1, hb.1⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.1)
      have h2 := hu' ⟨b.2, hb.2⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.2)
      apply Subtype.ext
      simp [← h1, ← h2]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hD, measureReal_prod_prod,
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L μ),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L' μ)]

theorem reflection_stable (μ : Measure E) [μ.IsAddHaarMeasure] (M : Submodule ℤ (E × E))
    [DiscreteTopology M] [IsZLattice ℝ M] (hM : ∀ p ∈ M, (p.1, -p.2) ∈ M) (A B : Submodule ℤ E)
    (hA : ∀ y, y ∈ A ↔ (y, (0 : E)) ∈ M) (hB : ∀ y, y ∈ B ↔ ((0 : E), y) ∈ M) :
    (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧
      ZLattice.covolume A μ * ZLattice.covolume B μ ≤
        2 ^ Module.finrank ℝ E * ZLattice.covolume M (μ.prod μ) := by
  have h2A : ∀ p ∈ M, p.1 + p.1 ∈ A := fun p hp => by
    rw [hA]
    have := M.add_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  have h2B : ∀ p ∈ M, p.2 + p.2 ∈ B := fun p hp => by
    rw [hB]
    have := M.sub_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  haveI dA : DiscreteTopology A :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : A => (⟨(x.1, 0), (hA _).1 x.2⟩ : M))
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.1) h))
  haveI dB : DiscreteTopology B :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : B => (⟨(0, x.1), (hB _).1 x.2⟩ : M))
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.2) h))
  have key : ∀ (C : Submodule ℤ E) (f : E × E →ₗ[ℝ] E), Function.Surjective f →
      (∀ p ∈ M, f p + f p ∈ C) → Submodule.span ℝ (C : Set E) = ⊤ := by
    intro C f hf hC
    rw [eq_top_iff, ← LinearMap.range_eq_top.2 hf, LinearMap.range_eq_map,
      ← IsZLattice.span_top (K := ℝ) (L := M), Submodule.map_span, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have h := (Submodule.span ℝ (C : Set E)).smul_mem (2⁻¹ : ℝ) (Submodule.subset_span (hC p hp))
    rwa [← two_smul ℝ, inv_smul_smul₀ two_ne_zero] at h
  haveI lA : IsZLattice ℝ A := ⟨key A (LinearMap.fst ℝ E E) LinearMap.fst_surjective h2A⟩
  haveI lB : IsZLattice ℝ B := ⟨key B (LinearMap.snd ℝ E E) LinearMap.snd_surjective h2B⟩
  refine ⟨⟨dA, lA⟩, ⟨dB, lB⟩, ?_⟩
  have hle : A.prod B ≤ M := fun p hp => by
    have := M.add_mem ((hA _).1 hp.1) ((hB _).1 hp.2)
    simpa using this
  rw [← covolume_prod μ A B, covolume_eq_relIndex_mul_of_haar (μ.prod μ) _ M hle]
  refine mul_le_mul_of_nonneg_right ?_ (ZLattice.covolume_pos M (μ.prod μ)).le
  let f : M.toAddSubgroup →+ A :=
    { toFun := fun p => ⟨p.1.1 + p.1.1, h2A _ p.2⟩
      map_zero' := by ext; simp
      map_add' := fun p q => by ext; simp; abel }
  have hK : (nsmulAddMonoidHom (α := A) 2).range.index = 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.index_range_nsmul, ZLattice.rank ℝ A]
  have hc : (A.prod B).toAddSubgroup.addSubgroupOf M.toAddSubgroup =
      (nsmulAddMonoidHom (α := A) 2).range.comap f := by
    ext p
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_prod,
      AddSubgroup.mem_comap, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨⟨_, h1⟩, Subtype.ext (by simp [f, two_nsmul])⟩
    · rintro ⟨y, hy⟩
      have h1 : y.1 + y.1 = p.1.1 + p.1.1 := by
        have := congrArg Subtype.val hy
        simpa [f, two_nsmul] using this
      have h2 : y.1 = p.1.1 := by
        rw [← two_smul ℝ, ← two_smul ℝ] at h1
        exact smul_right_injective E two_ne_zero h1
      have h3 : p.1.1 ∈ A := h2 ▸ y.2
      refine ⟨h3, (hB _).2 ?_⟩
      have := M.sub_mem p.2 ((hA _).1 h3)
      convert this using 1
      ext <;> simp
  have hidx : (A.prod B).toAddSubgroup.relIndex M.toAddSubgroup ≤ 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.relIndex, hc, AddSubgroup.index_comap, ← hK, ← AddSubgroup.relIndex_top_right]
    refine AddSubgroup.relIndex_le_of_le_right le_top ?_
    rw [AddSubgroup.relIndex_top_right, hK]
    positivity
  exact_mod_cast hidx

end General

noncomputable def reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    ((ι → κ → ℝ) × (ι → κ → ℝ)) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v i => ⟨p.1 v i, p.2 v i⟩
      invFun := fun z => (fun v i => (z v i).re, fun v i => (z v i).im)
      map_add' := fun p q => by ext v i; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v i; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }

theorem reImEquiv_apply {ι κ : Type} [Fintype ι] [Fintype κ] (p : (ι → κ → ℝ) × (ι → κ → ℝ))
    (v : ι) (i : κ) : reImEquiv ι κ p v i = ⟨p.1 v i, p.2 v i⟩ := rfl

theorem measurePreserving_reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (reImEquiv ι κ) (Measure.prod volume volume) volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow (κ → ℝ) (κ → ℝ) ι).symm
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ κ).symm
  have h3 := Complex.volume_preserving_equiv_real_prod.symm
  have h4 := volume_preserving_pi (ι := κ) (fun _ => h3)
  have h5 := volume_preserving_pi (ι := ι) (fun _ => h4.comp h2)
  exact h5.comp h1

theorem real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  intro ι κ _ _ L _ _ hL A B hA hB
  have hmem : ∀ p, p ∈ ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap ↔ reImEquiv ι κ p ∈ L :=
    fun p => Iff.rfl
  have h := reflection_stable volume (ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap)
    (fun p hp => by
      rw [hmem] at hp ⊢
      convert hL _ hp using 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply]) A B
    (fun y => by
      rw [hA, hmem]
      congr! 1)
    (fun y => by
      rw [hB, hmem]
      congr! 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply])
  haveI : (volume : Measure (κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : ((volume : Measure (ι → κ → ℝ)).prod (volume : Measure (ι → κ → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [ZLattice.covolume_comap L volume _ (measurePreserving_reImEquiv ι κ)] at h
  have hr : Module.finrank ℝ (ι → κ → ℝ) = Fintype.card ι * Fintype.card κ := by
    rw [Module.finrank_pi_fintype]; simp
  rwa [hr] at h

end GlobalTheory.ReImLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddingsMatchInfinitePlacesAutInstance
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.Place

theorem comap_mk_phi (I : AutInst) (v : InfinitePlace I.F) :
    (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E) = v := by
  have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem placeMatch : ∀ (I : AutInst) (xf : I.Gf), PlaceMatch I.φ I.P (frm I (1, xf)) := by
  intro I xf
  have hb := GlobalTheory.Count.FrameMajorant.comap_bijective I
  refine ⟨⟨fun v v' h => ?_, fun w => ⟨w.comap (algebraMap I.F I.E), hb.1 (comap_mk_phi I _)⟩⟩, fun v => ?_⟩
  · have h' : InfinitePlace.mk (I.φ v) = InfinitePlace.mk (I.φ v') := h
    rw [← comap_mk_phi I v, h', comap_mk_phi]
  · have he := GlobalTheory.PointEquivariance.embedding_eq I (InfinitePlace.mk (I.φ v))
    have hu : ∀ u, uMat ((((1, xf) : I.GA)).1 u) = 1 := fun u => rfl
    rw [comap_mk_phi] at he
    unfold frm
    rw [comap_mk_phi, hu, Matrix.mul_one]
    by_cases h : (InfinitePlace.mk (I.φ v)).embedding = I.φ v
    · exact Or.inl ⟨h, if_pos h⟩
    · exact Or.inr ⟨he.resolve_left h, if_neg h⟩

end GlobalTheory.RadCov.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjGaugeInvariant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

def innerAutTop {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (s : G) : G ≃ₜ* G :=
  { MulAut.conj s with
    continuous_toFun := by
      change Continuous fun g : G => s * g * s⁻¹
      fun_prop
    continuous_invFun := by
      change Continuous fun g : G => s⁻¹ * g * s
      fun_prop }

theorem inUJ_map_conj {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (g.map (starRingEnd ℂ)) := by
  unfold Formalism.REAL.inUJ at hg ⊢
  have hJ : (Formalism.REAL.Jm ε).map (starRingEnd ℂ) = Formalism.REAL.Jm ε := by
    ext i j
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hH : (g.map (starRingEnd ℂ))ᴴ = gᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h2
  rw [hH]
  exact h2

noncomputable def conjUJHom {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε →* Formalism.REAL.UJ ε :=
  ((Units.map ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom).comp (Formalism.REAL.UJ ε).subtype).codRestrict
    (Formalism.REAL.UJ ε) fun g => inUJ_map_conj ε g.2

theorem uMat_conjUJHom {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    uMat (conjUJHom ε g) = (uMat g).map (starRingEnd ℂ) := rfl

theorem conjUJHom_invol {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : conjUJHom ε (conjUJHom ε g) = g := by
  apply Subtype.ext
  apply Units.ext
  show uMat (conjUJHom ε (conjUJHom ε g)) = uMat g
  rw [uMat_conjUJHom, uMat_conjUJHom]
  ext i j
  simp

theorem continuous_conjUJHom {n : ℕ} (ε : Fin n → Bool) : Continuous (conjUJHom ε) := by
  have hc : Continuous ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom := by
    show Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)
    exact Continuous.matrix_map continuous_id Complex.continuous_conj
  have hu := Continuous.units_map _ hc
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

noncomputable def conjUJ {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε where
  toFun := conjUJHom ε
  invFun := conjUJHom ε
  left_inv := conjUJHom_invol ε
  right_inv := conjUJHom_invol ε
  map_mul' := map_mul _
  continuous_toFun := continuous_conjUJHom ε
  continuous_invFun := continuous_conjUJHom ε

theorem gauge_map_inner_comp {n : ℕ} (ε : Fin n → Bool) (C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε)
    (hC : ∀ g, Formalism.REAL.hs (uMat (C g) - 1) = Formalism.REAL.hs (uMat g - 1)) (s : Formalism.REAL.UJ ε) (c : ℝ)
    (hc : IsGauge ε c) :
    (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  have hT : ∀ g, (C.trans (innerAutTop s)) (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) = C g := by
    intro g
    show s * C (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) * s⁻¹ = C g
    simp only [map_mul, map_inv, C.apply_symm_apply]
    group
  have key := gauge_map_of_iso n n ε ε rfl (C.trans (innerAutTop s)) (C.symm s⁻¹)
    (fun g => by rw [hT]; exact hC g) c c hc hc
  have hf : (fun g => s * C g * s⁻¹) = ⇑(C.trans (innerAutTop s)) := by
    funext g
    rfl
  rw [hf]
  exact key

theorem exists_conj_gauge_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (τ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → ∃ C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε, (∀ g, uMat (C g) = (uMat g).map τ) ∧ ∀ (s : Formalism.REAL.UJ ε) (c : ℝ), IsGauge ε c → (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  intro n ε τ hτ
  rcases hτ with rfl | rfl
  · refine ⟨ContinuousMulEquiv.refl _, fun g => ?_, fun s c hc => ?_⟩
    · ext i j
      simp
    · exact gauge_map_inner_comp ε (ContinuousMulEquiv.refl _) (fun g => rfl) s c hc
  · refine ⟨conjUJ ε, fun g => uMat_conjUJHom ε g, fun s c hc => ?_⟩
    refine gauge_map_inner_comp ε (conjUJ ε) (fun g => ?_) s c hc
    have h1 : uMat (conjUJ ε g) = (uMat g).map (starRingEnd ℂ) := uMat_conjUJHom ε g
    rw [h1]
    unfold Formalism.REAL.hs
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e : ((uMat g).map (starRingEnd ℂ) - 1) i j = starRingEnd ℂ ((uMat g - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    rw [e, Complex.norm_conj]

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasisStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → IsSatFlag I (lamX I (1, xf)) j S := by
  first | exact @GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted | exact GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted | (intros; apply GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted <;> assumption)
end

