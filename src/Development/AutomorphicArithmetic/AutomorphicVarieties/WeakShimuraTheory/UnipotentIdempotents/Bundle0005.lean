module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfKer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private noncomputable def bu {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) (γ : G ℚ Ω →* c.Oˣ) : G L Ω →* (ResidueField c.O)ˣ :=
  ((Units.map (residue c.O).toMonoidHom).comp γ).comp (resQ L)

private theorem bu_val {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) (γ : G ℚ Ω →* c.Oˣ) (g : G L Ω) :
    (bu L γ g : ResidueField c.O) = Raw.bar γ (resQ L g) := rfl

private theorem bu_open {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) [NumberField L] (γ : G ℚ Ω →* c.Oˣ) (h : IsOpen {g : G ℚ Ω | Raw.bar γ g = 1}) :
    IsOpen ((bu L γ).ker : Set (G L Ω)) := by
  have hk : ((bu L γ).ker : Set (G L Ω)) = resQ L ⁻¹' {g | Raw.bar γ g = 1} := by
    ext g
    simp [MonoidHom.mem_ker, Units.ext_iff, bu_val]
  rw [hk]
  exact h.preimage (Af.continuous_restrictScalarsHom ℚ L Ω)

private theorem eq_of_ker {Γ Δ : Type} [Group Γ] [Group Δ] {f : Γ →* Δ} {a b : Γ} (h : a⁻¹ * b ∈ f.ker) : f a = f b := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

private theorem dec_of {Ω F F' : Type} [Field Ω] [Field F] [Field F'] [NumberField F] [NumberField F'] [Algebra F Ω] [Algebra F' Ω] {A : ValuationSubring Ω}
    {σ : G F Ω} {τ : G F' Ω} (h : ∀ x, τ x = σ x) (hσ : σ ∈ Dec (F := F) A) : τ ∈ Dec (F := F') A := by
  have h2 := apply_mem_iff_of_mem_Dec hσ
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h2 (τ⁻¹ x), ← h]
  simp

theorem UpperTheory.V.Ws.Lk.setEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), D.Good → T.Ok → Nonempty (SetD T) := by
  intro Ω _ _ _ l _ c D T hG hT
  classical
  obtain ⟨hps, hom, -⟩ := barFacts hG
  obtain ⟨g0, hg0eq, hg0om⟩ := gEx T hT
  let U : Subgroup (G T.L Ω) := (bu T.L (D.ps 0)).ker ⊓ (bu T.L (D.ps 1)).ker ⊓
    (bu T.L (D.ps 2)).ker ⊓ (bu T.L (D.ps 3)).ker ⊓ (bu T.L D.om).ker
  have hU : IsOpen (U : Set (G T.L Ω)) := by
    simp only [U, Subgroup.coe_inf]
    exact ((((bu_open _ _ (hps 0)).inter (bu_open _ _ (hps 1))).inter (bu_open _ _ (hps 2))).inter
      (bu_open _ _ (hps 3))).inter (bu_open _ _ hom)
  have hM0 : 2 * (∏ q ∈ D.S, q) * (NumberField.discr T.L).natAbs ≠ 0 := by
    have h1 : (∏ q ∈ D.S, q) ≠ 0 := Finset.prod_ne_zero_iff.2 fun q hq => (hG.S_prime q hq).ne_zero
    have h2 : (NumberField.discr T.L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
    exact mul_ne_zero (mul_ne_zero two_ne_zero h1) h2
  obtain ⟨v, B, p, hp, hpM, hpv, hnorm, hB, hBdec, hBpow, hBone⟩ := v0Ex T.L Ω U hU g0 _ hM0
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _)
  have hpS : p ∉ D.S := fun h =>
    hpM (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ h) 2) _)
  have hpd : ¬ (p : ℤ) ∣ NumberField.discr T.L := by
    intro h
    apply hpM
    apply dvd_mul_of_dvd_right
    simpa using Int.natAbs_dvd_natAbs.mpr h
  obtain ⟨e, he⟩ := placesEq T
  obtain ⟨-, ⟨φ, hφ, hφL⟩, -⟩ := galEq T
  have hIne : ∀ A : ValuationSubring Ω, Ine (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
    intro A σ hσ
    apply (hφL σ).1
    apply hT.unr A
    exact ⟨dec_of (hφ σ) hσ.1, fun x hx => by rw [hφ]; exact hσ.2 x hx⟩
  have hSdec : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation q < 1 →
      Dec (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
    intro q hq A hA σ hσ
    apply (hφL σ).1
    show resQ T.F (φ σ) ∈ T.K.fixingSubgroup
    apply hT.split q hq A hA
    exact dec_of (fun x => by simp [resQ, hφ]) hσ
  obtain ⟨s, hsA, hs0, hsfin, hsB, hsaway⟩ := mkSet l T.L Ω hG.l_odd hIne D.S hG.S_prime hG.l_mem hSdec
    (fun v => T.pl (e v)) he v B p hp hp2 hpS hpd hpv hnorm hB hBdec
  refine ⟨SetD.mk s e hsA hsfin hsaway ?_ ?_ ?_ (ccOf T s)⟩
  · rw [hs0]
    exact hsB
  · intro g hg i j
    rw [hs0] at hg
    obtain ⟨n, hn⟩ := hBpow g hg
    simp only [U, Subgroup.mem_inf] at hn
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩ := hn
    have key : ∀ k, bu T.L (D.ps k) g = bu T.L (D.ps k) (g0 ^ n) := by
      intro k
      fin_cases k
      exacts [eq_of_ker h0, eq_of_ker h1, eq_of_ker h2, eq_of_ker h3]
    have hg0' : bu T.L (chi D T.pr i) g0 = bu T.L (chi D T.pr j) g0 :=
      Units.ext (by rw [bu_val, bu_val]; exact hg0eq i j)
    rw [← bu_val, ← bu_val]
    change ((bu T.L (D.ps (lab T.pr i)) g : ResidueField c.O)) = (bu T.L (D.ps (lab T.pr j)) g : ResidueField c.O)
    rw [key, key]
    congr 1
    simp only [map_pow, map_zpow]
    exact congrArg (· ^ n) hg0'
  · obtain ⟨d, hd, hdU⟩ := hBone
    refine ⟨d, by rw [hs0]; exact hd, ?_⟩
    have h4 : d⁻¹ * g0 ∈ (bu T.L D.om).ker := (Subgroup.mem_inf.1 hdU).2
    rw [← bu_val, eq_of_ker h4, bu_val]
    exact hg0om
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.ResidEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.residEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (Y : SetD T) (V : Y.s.Lev), D.Good → T.Ok → V.S' = Y.s.S → ∃ r : W.Resid V.frame c'.O 4, (∀ i (g : G T.L Ω), r.chib i (V.pr g) = X.cb i g) ∧ (∀ (v : W.Vl l T.L) i (g : Dec (F := T.L) (Y.s.A v)), r.psib v i g = r.chib i (V.pr g)) ∧ (∀ v i, r.th v i = 1) := by
  intro Ω _ _ _ l _ c D T c' h X Y V hG hT hS
  have hcb := cbFacts X hG
  have hpr := prFacts l T.L Ω Y.s V
  have hd : ∀ i, ∃ χ : V.η.ker →* (ResidueField c'.O)ˣ, IsOpen (χ.ker : Set V.η.ker) ∧
      ∀ g, χ (V.pr g) = X.cb i g := fun i =>
    descend l T.L Ω Y.s V _ (X.cb i) (hcb.1 i)
      (fun A v hA hv => hcb.2.1 i A (Y.away A v hA (by rwa [hS] at hv)))
  choose χ hχo hχ using hd
  have hinj : Function.Injective χ := by
    intro i j hij
    apply cbInj X hT
    exact MonoidHom.ext fun g => by rw [← hχ, ← hχ, hij]
  have hpol : V.frame.IsPolar c'.O (W.GDet.ofRep (W.diagRep χ)) := by
    apply polar V.frame c'.O (ResidueField c'.O) 4 χ Fin.revPerm
    intro i g
    obtain ⟨g1, rfl⟩ := hpr.1 g
    obtain ⟨g', hg', hconj⟩ := hpr.2.1 g1
    obtain ⟨σ, hσ, hσc⟩ := Y.cc
    have key := hcb.2.2 σ hσ g1 g' (hσc g1 g' hg') i
    have heps := hpr.2.2.1 c'.O (ResidueField c'.O) g1
    rw [hconj]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Fin.revPerm_apply]
    erw [hχ i g', hχ i.rev g1, heps, IsLocalRing.ResidueField.algebraMap_eq]
    have e3 : ((4 : ℕ) : ℤ) - 1 = ((3 : ℕ) : ℤ) := by norm_num
    rw [e3, zpow_natCast]
    exact key
  refine ⟨W.Resid.mk χ hχo hinj hpol (fun v i => (χ i).comp (V.frame.φ v)) ?_ (fun _ _ => 1)
    (fun _ _ _ _ => rfl), fun i g => hχ i g, fun v i g => rfl, fun v i => rfl⟩
  intro v i
  exact (hχo i).preimage (V.frame.φ_cont v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.V0ok
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.v0ok :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (Y : SetD T) (V : Y.s.Lev), D.Good → ∀ r : W.Resid V.frame c'.O 4, (∀ i (g : G T.L Ω), r.chib i (V.pr g) = X.cb i g) → r.V0ok := by
  intro Ω _ _ _ l _ c D T c' h X Y V hD r hr
  haveI : IsLocalHom (inc h) := (UpperTheory.V.Ws.P1.coefRes c).2.2.1 c' h
  have hres : ∀ x : c.O, residue c'.O (inc h x) = ResidueField.map (inc h) (residue c.O x) := fun x =>
    (ResidueField.map_residue _ x).symm
  refine ⟨?_, ?_, ?_⟩
  · rintro i _ ⟨g, hg, rfl⟩
    exact MonoidHom.mem_ker.2 ((hr i g).trans (MonoidHom.mem_ker.1 ((cbFacts X hD).2.1 i _ Y.away0 hg)))
  · rintro _ ⟨g, hg, rfl⟩ i j
    refine (hr i g).trans (Eq.trans (Units.ext ?_) (hr j g).symm)
    rw [X.cb_val, X.cb_val, map_mul, map_mul, hres, hres]
    exact congrArg (fun x => residue c'.O (X.κ g) * ResidueField.map (inc h) x) (Y.eq0 g hg i j)
  · obtain ⟨g, hg, hne⟩ := Y.om0
    refine ⟨V.pr g, ⟨g, hg, rfl⟩, fun h' => hne ?_⟩
    have h1 := (prFacts l T.L Ω Y.s V).2.2.1 c'.O (ResidueField c'.O) g
    rw [h', Units.val_one] at h1
    have h2 : (chiO T.L Ω l c'.O g : c'.O) = inc h (chiO ℚ Ω l c.O (resQ T.L g)) := rfl
    rw [hD.om_bar]
    apply (ResidueField.map (inc h)).injective
    rw [map_one, Raw.bar, ← hres, ← h2]
    exact h1.symm
end

