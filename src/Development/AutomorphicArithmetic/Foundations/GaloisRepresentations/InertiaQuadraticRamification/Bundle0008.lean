module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplit
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem zpow_mem_fix {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : G F Ω) (z : Ω)
    (h : σ z = z) (n : ℤ) : (σ ^ n) z = z := by
  have hs : σ ∈ MulAction.stabilizer (G F Ω) z := h
  exact (MulAction.stabilizer (G F Ω) z).zpow_mem hs n

private theorem sq_apply_of_pm {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (φ : G F Ω) (z : Ω)
    (h : φ z = z ∨ φ z = -z) : (φ ^ (2 : ℤ)) z = z := by
  have e : φ ^ (2 : ℤ) = φ * φ := zpow_two φ
  rw [e, AlgEquiv.mul_apply]
  rcases h with h | h
  · rw [h, h]
  · rw [h, map_neg, h, neg_neg]

private theorem fix_of_parity {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [CharZero Ω] (φ : G F Ω) (e x : Ω)
    (he0 : e ≠ 0) (hφe : φ e = e ∨ φ e = -e) (hφx : φ x = x ∨ φ x = -x) (k m : ℤ)
    (hk : (φ ^ k) e ≠ e) (hm : (φ ^ m) e = e) : (φ ^ m) x = x := by
  rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj, ← two_mul, zpow_mul]
    exact zpow_mem_fix _ x (sq_apply_of_pm φ x hφx) j
  · exfalso
    have hφe' : φ e = -e := by
      rcases hφe with h | h
      · exact absurd (zpow_mem_fix φ e h k) hk
      · exact h
    rw [hj, zpow_add, zpow_one, zpow_mul, AlgEquiv.mul_apply, hφe', map_neg,
      zpow_mem_fix _ e (sq_apply_of_pm φ e hφe) j] at hm
    have h2 : (2 : Ω) * e = 0 := by linear_combination -hm
    rcases mul_eq_zero.1 h2 with h | h
    · exact two_ne_zero h
    · exact he0 h

private theorem pm_of_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : G F Ω) (z : Ω)
    (h : σ (z ^ 2) = z ^ 2) : σ z = z ∨ σ z = -z := by
  rw [map_pow] at h
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

private theorem fixes_of_imag {Y Ω : Type} [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω]
    (e : Y) (he : e ≠ 0) (hce : IsCMField.complexConj Y e = -e) (g : G (maximalRealSubfield Y) Ω)
    (hg : g (algebraMap Y Ω e) = algebraMap Y Ω e) : Fixes Y g := by
  intro y
  have h2 : (2 : Y) ≠ 0 := two_ne_zero
  obtain ⟨a, haa⟩ : ∃ a : Y, a = (y + IsCMField.complexConj Y y) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b : Y, b = (y - IsCMField.complexConj Y y) / (2 * e) := ⟨_, rfl⟩
  have ha : IsCMField.complexConj Y a = a := by
    rw [haa, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
  have hb : IsCMField.complexConj Y b = b := by
    rw [hbb, map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hce]
    field_simp
    ring
  have hy : y = a + e * b := by
    rw [haa, hbb]
    field_simp
    ring
  have hfa : g (algebraMap Y Ω a) = algebraMap Y Ω a :=
    g.commutes ⟨a, (IsCMField.complexConj_eq_self_iff Y a).1 ha⟩
  have hfb : g (algebraMap Y Ω b) = algebraMap Y Ω b :=
    g.commutes ⟨b, (IsCMField.complexConj_eq_self_iff Y b).1 hb⟩
  rw [hy, map_add (f := _), map_mul, map_add (f := _), map_mul, hfa, hfb, hg]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.inertSplit :
    DecGen → InertSplit := by
  intro hD Y Ω _ _ _ _ _ _ A u hu x a hx hI hg h hh
  obtain ⟨g, hgD, hgY⟩ := hg
  haveI : IsAlgClosure (maximalRealSubfield Y) Ω := IsAlgClosure.ofAlgebraic _ Y Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 (maximalRealSubfield Y)), IsPlaceOver A v := by
    refine ⟨⟨u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y)), Ideal.IsPrime.comap _, ?_⟩, ?_⟩
    · intro hb
      exact u.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
    · intro z
      exact hu (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y) z)
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  obtain ⟨e, he0, hce⟩ : ∃ e : Y, e ≠ 0 ∧ IsCMField.complexConj Y e = -e := by
    obtain ⟨y, hy⟩ : ∃ y : Y, IsCMField.complexConj Y y ≠ y := by
      by_contra hc
      push_neg at hc
      exact IsCMField.complexConj_ne_one Y (AlgEquiv.ext hc)
    refine ⟨y - IsCMField.complexConj Y y, sub_ne_zero.2 (Ne.symm hy), ?_⟩
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hXf : ({x, algebraMap Y Ω e} : Set Ω).Finite := Set.toFinite _
  have hIX : ∀ τ ∈ (Ine A : Subgroup (G (maximalRealSubfield Y) Ω)),
      ∀ y ∈ ({x, algebraMap Y Ω e} : Set Ω), τ y = y := by
    intro τ hτ y hy
    rcases hy with rfl | rfl
    · exact (hI τ hτ).2
    · exact (hI τ hτ).1 e
  let h' : G (maximalRealSubfield Y) Ω := AlgEquiv.restrictScalars _ h
  have hh' : h' ∈ Dec A := (GlobalTheory.AboveL.mem_dec_congr A h' h (fun _ => rfl)).2 hh
  obtain ⟨k, hk⟩ := hD _ Ω A v hv φ hφ _ hXf hIX g hgD
  obtain ⟨m, hm⟩ := hD _ Ω A v hv φ hφ _ hXf hIX h' hh'
  have hE0 : algebraMap Y Ω e ≠ 0 := (map_ne_zero _).2 he0
  have hpmE : φ (algebraMap Y Ω e) = algebraMap Y Ω e ∨ φ (algebraMap Y Ω e) = -algebraMap Y Ω e := by
    apply pm_of_sq
    have hs : e ^ 2 ∈ maximalRealSubfield Y := by
      rw [← IsCMField.complexConj_eq_self_iff, map_pow, hce, neg_sq]
    rw [← map_pow]
    exact φ.commutes (⟨e ^ 2, hs⟩ : maximalRealSubfield Y)
  have hpmx : φ x = x ∨ φ x = -x := by
    apply pm_of_sq
    rw [hx, map_intCast]
  have hkE : (φ ^ k) (algebraMap Y Ω e) ≠ algebraMap Y Ω e := by
    rw [← hk _ (by simp)]
    intro hgE
    exact hgY (fixes_of_imag e he0 hce g hgE)
  have hmE : (φ ^ m) (algebraMap Y Ω e) = algebraMap Y Ω e := by
    rw [← hm _ (by simp)]
    exact h.commutes e
  have hfx := fix_of_parity φ _ x hE0 hpmE hpmx k m hkE hmE
  rw [← hm x (by simp)] at hfx
  exact hfx
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.LayerOf
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.layerOf :
    InclOf → IndexComap → LayerOf := by
  intro hIncl hIdx
  unfold LayerOf
  intro E Ω _ _ _ _ _ _ S H H' hH' hle hp X Y hX hY u hS hDec hτex
  obtain ⟨A, hA, τ, hτ, hτ'⟩ := hτex
  unfold Cuts at hX hY
  have overUnder : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver B w →
      IsPlaceOver B (w.under (𝓞 (maximalRealSubfield E))) := by
    intro B w hB x
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hB]
    rfl
  have resLift : ∀ (g : G (maximalRealSubfield E) Ω) (hg : Fixes E g),
      AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (GlobalTheory.AboveL.DecRes.lift (E := E) g hg) = g :=
    fun g hg => AlgEquiv.ext fun x => rfl
  have hτD := Ine_le_Dec A hτ
  obtain ⟨hτE, hτH⟩ := hDec A hA τ hτD
  obtain ⟨τ', hres⟩ : ∃ τ' : G E Ω, AlgEquiv.restrictScalarsHom (maximalRealSubfield E) τ' = τ :=
    ⟨_, resLift τ hτE⟩
  have fY : fixGrp E Ω Y.K = H'.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hY g
  have fX : fixGrp E Ω X.K = H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hX g
  have hidx := hIdx (G (maximalRealSubfield E) Ω) (G E Ω)
    (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) H H' hH'.comm hle hp
    ⟨τ', by rw [hres]; exact hτH, by rw [hres]; exact hτ'⟩
  obtain ⟨x0, t0E, t0Ω, hgal, hfin⟩ := hIncl E Ω X Y (by rw [fY, fX]; exact Subgroup.comap_mono hle)
  rw [fY, fX, hidx] at hfin
  obtain ⟨w, hw⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := maximalRealSubfield E) (K := E) hA
  have hwu : w.under (𝓞 (maximalRealSubfield E)) = u := eq_of_isPlaceOver (overUnder A w hw) hA
  have hfixX : Fixes X.K τ' := (hX τ').2 (by rw [hres]; exact hτH)
  refine ⟨⟨x0, t0E, t0Ω, hgal, by rw [hfin]; exact hp, w, ?_, ?_, A, hw,
    GlobalTheory.AboveL.DecRes.lift (E := X.K) τ' hfixX, ?_, ?_⟩, ?_⟩
  · intro hwS
    exact hS w hwS hwu
  · intro B hB g hg
    have hBu : IsPlaceOver B u := by
      rw [← hwu]
      exact overUnder B w hB
    obtain ⟨hgE, hgH⟩ := hDec B hBu g hg
    refine ⟨hgE, ?_⟩
    have h1 := (hX (GlobalTheory.AboveL.DecRes.lift (E := E) g hgE)).2 (by rw [resLift]; exact hgH)
    exact h1
  · subst hres
    rw [mem_Ine]
    have hτI := (mem_Ine (A := A)).1 hτ
    exact ⟨(GlobalTheory.AboveL.mem_dec_congr A _ _ (fun x => rfl)).2 hτI.1, hτI.2⟩
  · intro hfix
    exact hτ' (by rw [← hres]; exact (hY τ').1 hfix)
  · intro x1 t1
    have hx : x1 = x0 := by
      refine Algebra.algebra_ext _ _ fun r => (algebraMap Y.K Ω).injective ?_
      rw [← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x1 _ _ t1 r,
        ← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x0 _ _ t0Ω r]
    subst hx
    exact hfin
end

