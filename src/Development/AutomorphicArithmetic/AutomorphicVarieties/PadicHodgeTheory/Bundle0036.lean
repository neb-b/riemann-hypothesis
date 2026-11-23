module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsEps
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial
open UpperTheory.V.Loc.OrdinaryDeformation TrivSqZeroExt

section Fibre

variable {E B : Type} [Field E] [CommRing B] [Algebra E B] (π : B →ₐ[E] E)

private noncomputable def fib : Subalgebra E (B × DualNumber E) :=
  AlgHom.equalizer (π.comp (AlgHom.fst E B _)) ((fstHom E E E).comp (AlgHom.snd E B _))

private noncomputable def p1 : fib π →ₐ[E] B := (AlgHom.fst E B _).comp (fib π).val

private noncomputable def p2 : fib π →ₐ[E] DualNumber E := (AlgHom.snd E B _).comp (fib π).val

private noncomputable def p3 (ε : B) (h0 : π ε = 0) (hε : ∀ b, b * ε = π b • ε) : fib π →ₐ[E] B where
  toFun c := c.1.1 + c.1.2.snd • ε
  map_one' := by simp
  map_zero' := by simp
  map_add' c c' := by
    simp only [Subalgebra.coe_add, Prod.fst_add, Prod.snd_add, snd_add, add_smul]
    abel
  map_mul' c c' := by
    have h : π c.1.1 = c.1.2.fst := c.2
    have h' : π c'.1.1 = c'.1.2.fst := c'.2
    simp only [Subalgebra.coe_mul, Prod.fst_mul, Prod.snd_mul, DualNumber.snd_mul, add_mul, mul_add, mul_smul_comm,
      smul_mul_assoc, mul_comm ε c'.1.1, hε, h, h', h0, smul_smul, add_smul, mul_zero, zero_smul, add_zero]
    rw [map_add (f := _), map_smul, h0, smul_zero, add_zero, h, mul_comm c'.1.2.snd, mul_comm c.1.2.snd]
    abel
  commutes' a := by simp [algebraMap_eq_inl]

private theorem exists_eps [IsNoetherianRing B] (hπ : ∀ a, π a = 0 → IsNilpotent a) (x : B) (hx : π x = 0)
    (hx0 : x ≠ 0) : ∃ ε : B, ε ≠ 0 ∧ π ε = 0 ∧ ∀ b, b * ε = π b • ε := by
  classical
  have hn : ∃ k, RingHom.ker π ^ (k + 1) = ⊥ := by
    obtain ⟨k, hk⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian (RingHom.ker π))).2
      fun a ha => hπ a ha
    exact ⟨k, by rw [pow_succ, hk]; simp⟩
  have h1 := Nat.find_spec hn
  have h2 : Nat.find hn ≠ 0 := fun h => by
    rw [h, zero_add, pow_one] at h1
    exact hx0 (Ideal.mem_bot.1 (h1 ▸ (hx : x ∈ RingHom.ker π)))
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h2
  obtain ⟨ε, h3, h4⟩ := (Submodule.ne_bot_iff _).1 (Nat.find_min hn (hk ▸ Nat.lt_succ_self k))
  refine ⟨ε, h4, Ideal.pow_le_self k.succ_ne_zero h3, fun b => ?_⟩
  have h5 : ε * (b - algebraMap E B (π b)) ∈ RingHom.ker π ^ (k + 1 + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul h3 (by simp [RingHom.mem_ker])
  rw [hk] at h1
  rw [h1, Ideal.mem_bot] at h5
  rw [Algebra.smul_def]
  linear_combination h5

end Fibre

theorem UpperTheory.V.Loc.ordEq :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG (m := 3) (R := B)), D.InDcr (π : B →+* E) r ↔ D.InDord (π : B →+* E) r := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r
  refine ⟨fun hr => ?_, dcr_of_dord⟩
  induction hn : finrank ℚ_[l] B using Nat.strong_induction_on generalizing B with
  | _ N ih =>
  by_cases hinj : ∀ x, π x = 0 → x = 0
  · refine ⟨r, 1, ⟨hr, fun g a b h => hinj _ ?_⟩, (congOne_iff _ _).2 (map_one _), fun a b _ => by simp,
      (conjBy_one r).symm⟩
    have hab : a ≠ b := by
      rintro rfl
      simp [wt] at h
    change (((GG.map (π : B →+* E)).comp r) g).mat a b = 0
    rw [hr.red, rz_eq, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab]
  push Not at hinj
  obtain ⟨x, hx, hx0⟩ := hinj
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite ℚ_[l] B
  obtain ⟨ε, hε0, h0, hε⟩ := exists_eps π hπ x hx hx0
  let I : Ideal B := Ideal.span {ε}
  let q : B →ₐ[E] B ⧸ I := Ideal.Quotient.mkₐ E I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective E I
  let π' : (B ⧸ I) →ₐ[E] E := Ideal.Quotient.liftₐ I π fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, h0, mul_zero]
  have hπq : π'.comp q = π := AlgHom.ext fun _ => rfl
  have hπ' : ∀ a, π' a = 0 → IsNilpotent a := fun a ha => by
    obtain ⟨b, rfl⟩ := hq a
    exact (hπ b ha).map q
  have hlt : finrank ℚ_[l] (B ⧸ I) < N := by
    rw [← hn, ← (q.restrictScalars ℚ_[l]).toLinearMap.finrank_range_add_finrank_ker,
      LinearMap.range_eq_top.2 hq, finrank_top]
    refine Nat.lt_add_of_pos_right (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨ε, ?_⟩, fun h => hε0 (congrArg Subtype.val h)⟩)
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε)
  have hr' := dcr_map (q.restrictScalars ℚ_[l]) hq (π' := (π' : (B ⧸ I) →+* E)) (RingHom.ext fun _ => rfl) hr
  obtain ⟨u', n', hu', hn1', hn2', e'⟩ := ih _ hlt (B ⧸ I) π' hπ' _ hr' rfl
  obtain ⟨u₁, hu₁, rfl⟩ := triLift hP D E B π hπ (B ⧸ I) π' hπ' q hq hπq u' hu'
  obtain ⟨n₁, hn₁, rfl⟩ := lift_lower (q : B →+* B ⧸ I) hq n' hn2'
  have hc₁ : Matrix.GeneralLinearGroup.map (π : B →+* E) n₁ = 1 := ((congOne_iff _ _).1 hn1' :)
  have hr₁ := dcr_conj hu₁.toInDcrAt n₁ hc₁
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  haveI : Module.Finite ℚ_[l] (fib π) :=
    Module.Finite.of_injective ((fib π).val.restrictScalars ℚ_[l]).toLinearMap Subtype.val_injective
  let f₁ : fib π →ₐ[ℚ_[l]] B := (p1 π).restrictScalars ℚ_[l]
  let f₂ : fib π →ₐ[ℚ_[l]] DualNumber E := (p2 π).restrictScalars ℚ_[l]
  let f₃ : fib π →ₐ[ℚ_[l]] B := (p3 π ε h0 hε).restrictScalars ℚ_[l]
  have i12 : ∀ c c', f₁ c = f₁ c' → f₂ c = f₂ c' → c = c' := fun c c' h h' => Subtype.ext (Prod.ext h h')
  have i13 : ∀ c c', f₁ c = f₁ c' → f₃ c = f₃ c' → c = c' := fun c c' h h' => by
    have h1 : c.1.1 = c'.1.1 := h
    have h2 : c.1.1 + c.1.2.snd • ε = c'.1.1 + c'.1.2.snd • ε := h'
    have h3 : π c.1.1 = c.1.2.fst := c.2
    have h4 : π c'.1.1 = c'.1.2.fst := c'.2
    rw [h1, add_right_inj] at h2
    exact i12 c c' h (TrivSqZeroExt.ext (by rw [h1, h4] at h3; exact h3.symm) (smul_left_injective E hε0 h2))
  have g12 : ∀ (s : B) (t : DualNumber E), π s = t.fst → ∃ c, f₁ c = s ∧ f₂ c = t := fun s t h => ⟨⟨(s, t), h⟩, rfl, rfl⟩
  have g13 : ∀ s t : B, q s = q t → ∃ c, f₁ c = s ∧ f₃ c = t := fun s t h => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h.symm)
    refine ⟨⟨(s, (π s, π c)), rfl⟩, rfl, ?_⟩
    change s + π c • ε = t
    rw [← hε, hc, add_sub_cancel]
  have s2 : Function.Surjective f₂ := fun t => (g12 (algebraMap E B t.fst) t (π.commutes _)).imp fun _ h => h.2
  have s3 : Function.Surjective f₃ := fun t => (g13 t t rfl).imp fun _ h => h.2
  have k2 : (fstHom E E E : DualNumber E →+* E).comp (f₂ : fib π →+* DualNumber E) =
      (π : B →+* E).comp (f₁ : fib π →+* B) := RingHom.ext fun c => Eq.symm c.2
  have k3 : (π : B →+* E).comp (f₃ : fib π →+* B) = (π : B →+* E).comp (f₁ : fib π →+* B) := RingHom.ext fun c => by
    change π (c.1.1 + c.1.2.snd • ε) = π c.1.1
    rw [map_add (f := _), map_smul, h0, smul_zero, add_zero]
  obtain ⟨R, hR1, hR3⟩ := glue_hom (f₁ : fib π →+* B) (f₃ : fib π →+* B) (q : B →+* B ⧸ I) (q : B →+* B ⧸ I) i13 g13
    (conjBy n₁ u₁) r ((map_conjBy _ _ _).trans e'.symm)
  have hR := dcr_pair f₁ f₃ i13 (hR1 ▸ hr₁) (hR3 ▸ hr)
  obtain ⟨u₂, n₂, hu₂, hn₂, hn₂', e₂⟩ := dual_ord hP D E _ (dcr_map f₂ s2 k2 hR)
  obtain ⟨u, hu1, hu2⟩ := glue_hom (f₁ : fib π →+* B) (f₂ : fib π →+* DualNumber E) (π : B →+* E)
    (fstHom E E E : DualNumber E →+* E) i12 g12 u₁ u₂ (hu₁.red.trans hu₂.red.symm)
  obtain ⟨n, hn1, hn2⟩ := glue_GL (f₁ : fib π →+* B) (f₂ : fib π →+* DualNumber E) (π : B →+* E)
    (fstHom E E E : DualNumber E →+* E) i12 g12 n₁ n₂ (hc₁.trans ((congOne_iff _ _).1 hn₂).symm)
  subst hu1 hu2 hn1 hn2
  rw [← hR3]
  refine dord_map f₃ s3 k3 ⟨u, n, ⟨dcr_pair f₁ f₂ i12 hu₁.toInDcrAt hu₂.toInDcrAt, fun g a b h => ?_⟩,
    (congOne_iff _ _).2 hc₁, fun a b h => ?_, MonoidHom.ext fun g => ?_⟩
  · exact i12 _ _ ((hu₁.tri g a b h).trans (map_zero _).symm) ((hu₂.tri g a b h).trans (map_zero _).symm)
  · exact i12 _ _ (((map_sub_one _ n a b).symm.trans (hn₁ a b h)).trans (map_zero _).symm)
      (((map_sub_one _ n a b).symm.trans (hn₂' a b h)).trans (map_zero _).symm)
  · exact gg_ext (f₁ : fib π →+* B) (f₂ : fib π →+* DualNumber E) i12
      (DFunLike.congr_fun (hR1.trans (map_conjBy _ n u).symm) g) (DFunLike.congr_fun (e₂.trans (map_conjBy _ n u).symm) g)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFinrankTwoCocyclesCharRatio
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem finrank_Z1_chRep_eq_two_of_ne_one_ne_cyc (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ) (hr : φ.range = ⊤)
    {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]
    (κ : H →* Eˣ) (hκ : Continuous fun g => (κ g : E)) (h0 : ∃ g, κ g ≠ 1) (h2 : ∃ g, κ g ≠ cycA l l E (φ g)) :
    finrank E ↥(ReciprocityTheory.Gal.Z1 (chRep κ)) = 2 := by
  have hρ : ∀ g x, chRep κ g x = (κ g : E) * x := fun g x => by simp [chRep]
  have hc : ReciprocityTheory.Gal.ContAction (chRep κ) := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ]
    exact (hκ.comp continuous_fst).mul continuous_snd
  obtain ⟨f1, -, e1, e2⟩ := tateRat hP (l := l) φ hφ (chRep κ) hc
  obtain ⟨g, hg⟩ := h0
  have hz : ∀ m : E, chRep κ g m - m = 0 → m = 0 := by
    intro m hm
    have h1 : ((κ g : E) - 1) * m = 0 := by
      rw [sub_mul, one_mul, ← hρ, hm]
    exact (mul_eq_zero.1 h1).resolve_left fun h => hg (Units.val_eq_one.1 (sub_eq_zero.1 h))
  have hH0 : ReciprocityTheory.Gal.H0 (chRep κ) = ⊥ :=
    eq_bot_iff.2 fun m hm => hz m (sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm g))
  have hB : finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1 := by
    unfold ReciprocityTheory.Gal.B1
    rw [LinearMap.finrank_range_of_inj, finrank_self]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    exact fun m hm => hz m (congrFun hm g)
  have hD : H0dual ((cycA l l E).comp φ) (chRep κ) = ⊥ := by
    obtain ⟨s, hs⟩ := h2
    refine eq_bot_iff.2 fun F hF => LinearMap.ext fun x => ?_
    have h1 := hF s x
    rw [hρ, ← smul_eq_mul, map_smul, smul_eq_mul, ← sub_eq_zero, ← sub_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left fun h => hs (Units.ext (sub_eq_zero.1 h))
  have hBZ : ReciprocityTheory.Gal.B1 (chRep κ) ≤ ReciprocityTheory.Gal.Z1 (chRep κ) := by
    rintro _ ⟨m, rfl⟩
    refine ⟨?_, fun g h => ?_⟩
    · show Continuous fun g => chRep κ g m - m
      simp only [hρ]
      exact (hκ.mul continuous_const).sub continuous_const
    · simp only [amitsur_d0_apply, hρ, map_mul κ, Units.val_mul]
      ring
  have eB := Submodule.comapSubtypeEquivOfLe hBZ
  rw [hD, finrank_bot] at e2
  rw [hH0, finrank_bot, e2, if_pos rfl, hr, Subgroup.index_top, finrank_self] at e1
  haveI : Module.Finite E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := finite_of_finrank_pos (by omega)
  haveI := Module.Finite.equiv eB.symm
  haveI : Module.Finite E ↥(ReciprocityTheory.Gal.Z1 (chRep κ)) :=
    Module.Finite.of_submodule_quotient ((ReciprocityTheory.Gal.B1 (chRep κ)).comap (ReciprocityTheory.Gal.Z1 (chRep κ)).subtype)
  have e3 := Submodule.finrank_quotient_add_finrank
    ((ReciprocityTheory.Gal.B1 (chRep κ)).comap (ReciprocityTheory.Gal.Z1 (chRep κ)).subtype)
  rw [eB.finrank_eq, hB, e1] at e3
  omega

private theorem dec_iso {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ φ : ↥(Dec (F := ℚ) A) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧ φ.range = ⊤ ∧
      ∀ g, cyc l l (φ g) = cycZ ℚ Ω l (g : G ℚ Ω) := by
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := l) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (decEmb (F := ℚ) (Ω := Ω) (v := l)).1 A w hAw hw
  obtain ⟨-, φ, h1, -, h3, -, h5, -⟩ := (decEmb (F := ℚ) (Ω := Ω) (v := l)).2 j
  exact ⟨φ, h1, eq_top_iff.2 fun σ _ => (h3 σ).2 fun x => by simp, h5 l⟩

theorem UpperTheory.exists_finrank_two_cocycles_char_ratio :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (a b : Fin 4), a < b → ∃ T : Submodule E (D.Gp l → E), (∀ z, z ∈ T ↔ QCont l z ∧ ∀ g h : D.Gp l, z (g * h) = z g + algebraMap c.O E ((D.ps a g * (D.ps b g)⁻¹ : c.Oˣ) : c.O) * z h) ∧ finrank E ↥T = 2 := by
  intro hP Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ a b hab
  have facts := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have F2 := facts.2.1
  have F4 := facts.2.2.2.1
  have F7 := facts.2.2.2.2.2.2.1
  have LargeParameterEstimates := facts.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨φ, hφ, hr, hcy⟩ := dec_iso l (D.pl l) (hD.pl_over l Fact.out)
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have hinj : Function.Injective (algebraMap c.O E) := IsFractionRing.injective _ _
  let f : (c.O)ˣ →* Eˣ := Units.map (algebraMap c.O E : c.O →* E)
  have hf : Function.Injective f := Units.map_injective hinj
  let κ : D.Gp l →* Eˣ := f.comp ((D.ps a * (D.ps b)⁻¹).comp (D.Gp l).subtype)
  have hκ : ∀ g : D.Gp l, κ g = f (D.ps a g * (D.ps b g)⁻¹) := fun _ => rfl
  have hps : ∀ i, Continuous fun g : G ℚ Ω => algebraMap c.O E (D.ps i g : c.O) := fun i =>
    (ptCont (l := l) (O := c.O) c.O E (Algebra.ofId c.O E)).1 _ _ (LargeParameterEstimates i)
  have hκc : Continuous fun g => (κ g : E) := by
    have : (fun g => (κ g : E)) = fun g : D.Gp l =>
        algebraMap c.O E (D.ps a g : c.O) * algebraMap c.O E (D.ps b (g : G ℚ Ω)⁻¹ : c.O) := funext fun g => by
      rw [hκ, map_inv (D.ps b), ← map_mul]
      rfl
    rw [this]
    exact ((hps a).comp continuous_subtype_val).mul ((hps b).comp (continuous_subtype_val.inv))
  have hce : ∀ g : D.Gp l, cycA l l E (φ g) = f (chiO ℚ Ω l c.O g) := fun g => Units.ext (by
    show algebraMap ℤ_[l] E (cyc l l (φ g) : ℤ_[l]ˣ) = algebraMap c.O E (algebraMap ℤ_[l] c.O (cycZ ℚ Ω l g : ℤ_[l]ˣ))
    rw [hcy, ← IsScalarTower.algebraMap_apply])
  have hord : ¬ IsOfFinOrder (chiO ℚ Ω l c.O D.s0) := by
    have hi : Function.Injective (algebraMap ℤ_[l] c.O) := by
      refine Function.Injective.of_comp (f := algebraMap c.O E) ?_
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
      exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    exact fun h => hD.decompSigma_ord ((Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hi).isOfFinOrder_iff.1 h)
  refine ⟨ReciprocityTheory.Gal.Z1 (chRep κ), fun z => Iff.rfl, finrank_Z1_chRep_eq_two_of_ne_one_ne_cyc hP φ hφ hr κ hκc ⟨D.s0, fun h => ?_⟩ ?_⟩
  · rw [hκ, map_eq_one_iff f hf, mul_inv_eq_one] at h
    exact hab.ne (F7 (congrArg Units.val h))
  · by_cases hl : lamW a = lamW b
    · refine ⟨D.s0, fun h => ?_⟩
      rw [hκ, hce] at h
      have h1 := hf h
      rw [F4 a _ hD.decompSigma_mem, F4 b _ hD.decompSigma_mem, mul_inv_eq_iff_eq_mul, ← pow_succ'] at h1
      have h2 := injective_pow_iff_not_isOfFinOrder.2 hord h1
      have := hD.two_le
      fin_cases a <;> fin_cases b <;> simp [lamW, Raw.wts4] at hab hl h2 <;> omega
    · obtain ⟨h1, -, h3⟩ := F2 l (Finset.mem_insert_self _ _)
      refine ⟨⟨D.sg l, h1⟩, fun h => h3 a b hl ?_⟩
      rw [hκ, hce] at h
      have h4 : D.ps a (D.sg l) * (D.ps b (D.sg l))⁻¹ = 1 := (hf h).trans (by
        show Units.map _ (cycZ ℚ Ω l (D.sg l)) = 1
        rw [hD.sg_cyc, map_one])
      rw [mul_inv_eq_one] at h4
      exact congrArg (fun x : c.Oˣ => residue c.O (x : c.O)) h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsLocallyAlgebraicTransferOfPlaceIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
variable {F M Ω : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Algebra M Ω] [IsAlgClosure M Ω] {A : ValuationSubring Ω} {v : Plc F} {w : Plc M}
  {h : IsPlaceOver A v} {h' : IsPlaceOver A w}

private theorem locAlg_step {l : ℕ} [Fact l.Prime] (c : Weil h →* Weil h')
    (hc : ∀ (σ : Weil h) z, (σ : G F Ω) z = (c σ : G M Ω) z) (hdeg : ∀ σ, deg (c σ) = deg σ)
    (i : v.adicCompletion F ≃+* w.adicCompletion M) (hi : Continuous i) (hi' : Continuous i.symm)
    (hA : ∀ a, IsLocalArtin h a → ∃ a', IsLocalArtin h' a' ∧ ∀ σ, (a' (c σ) : w.adicCompletion M) = i (a σ))
    (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (κ' : ↥(Dec (F := M) A) →* (Qbar l)ˣ)
    (hκ : ∀ (g : ↥(Dec (F := F) A)) (g' : ↥(Dec (F := M) A)), (∀ z, (g : G F Ω) z = (g' : G M Ω) z) → κ g = κ' g')
    (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ)
    (hwt : ∀ τ' : Emb l w, wt' τ' = wt ⟨τ'.1.comp i.toRingHom, τ'.2.comp hi⟩) :
    IsLocAlg h' κ' wt' → IsLocAlg h κ wt := by
  rintro ⟨ph, hop, hph⟩
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hm : ∀ σ : Ine (F := F) A, ((c (ineIncl h σ) : Weil h') : G M Ω) ∈ Ine (F := M) A := fun σ => by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  let e : Ine (F := F) A →* Ine (F := M) A :=
    (((Weil h').subtype.comp c).comp (ineIncl h)).codRestrict _ hm
  have he : ∀ σ, ineIncl h' (e σ) = c (ineIncl h σ) := fun σ => Subtype.ext rfl
  refine ⟨ph.comp e, ?_, fun a ha σ => ?_⟩
  · obtain ⟨O', hO', hpre⟩ := isOpen_induced_iff.mp hop
    have h1 : (1 : G M Ω) ∈ O' := by
      have : (1 : Ine (F := M) A) ∈ Subtype.val ⁻¹' O' := by rw [hpre]; simp
      exact this
    obtain ⟨U, hU, hU1, hUO⟩ := GlobalTheory.WeilTransport.conj_nhds F Ω M Ω (RingEquiv.refl Ω) O' (hO'.mem_nhds h1)
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hU1) fun τ hτ => ?_)
    have hO : e τ ∈ Subtype.val ⁻¹' O' := hUO τ hτ _ (hc (ineIncl h τ))
    rw [hpre] at hO
    exact hO
  · obtain ⟨a', ha', haa⟩ := hA a ha
    have h1 := hph a' ha' (e σ)
    rw [hκ _ (Subgroup.inclusion (Weil_le_Dec h') (ineIncl h' (e σ))) (hc (ineIncl h σ)), MonoidHom.comp_apply, h1, he, haa]
    let E : Emb l w ≃ Emb l v :=
      { toFun := fun τ' => ⟨τ'.1.comp i.toRingHom, τ'.2.comp hi⟩
        invFun := fun τ => ⟨τ.1.comp i.symm.toRingHom, τ.2.comp hi'⟩
        left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by simp)
        right_inv := fun τ => Subtype.ext (RingHom.ext fun x => by simp) }
    rw [← finprod_comp_equiv E]
    refine finprod_congr fun τ => ?_
    rw [hwt]
    rfl

private theorem artin_step (hG : GlobalArtinReciprocity) (c : Weil h' →* Weil h) (hcs : Function.Surjective c)
    (c' : Weil h →* Weil h') (hcc : ∀ σ, c' (c σ) = σ)
    (hsm : ∀ ξ : Weil h' →* ℂˣ, GlobalTheory.WeilDeligne.IsSmooth ξ → GlobalTheory.WeilDeligne.IsSmooth (ξ.comp c'))
    (i : v.adicCompletion F ≃+* w.adicCompletion M) (hi' : Continuous i.symm)
    (a : Weil h →* (v.adicCompletion F)ˣ) (ha : IsLocalArtin h a)
    (hglob : ∀ art', IsGlobalArtin art' → ∀ σ' : Weil h',
      art' (Neutral.B1.localIdele M w (Units.map i.toRingHom.toMonoidHom (a (c σ')))) = toAb M Ω σ') :
    IsLocalArtin h' ((Units.map i.toRingHom.toMonoidHom).comp (a.comp c)) := by
  obtain ⟨art, hart⟩ := hG M Ω
  obtain ⟨b, hs, ho, hg⟩ := GlobalTheory.InvLocalArtin.exists_invLocalArtin M Ω A w h' art hart
  have hb : (Units.map i.toRingHom.toMonoidHom).comp (a.comp c) = b := MonoidHom.ext fun σ =>
    _root_.GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' M Ω art hart w ((hglob art hart σ).trans (hg σ).symm)
  refine ⟨hb ▸ hs, hb ▸ GlobalTheory.ArtinInvCont.continuous_inv_on_ine M Ω A w h' art b hart ho hg, hb ▸ ho, fun ξ hξ => ?_, hglob⟩
  obtain ⟨χ, hχ, e⟩ := ha.factor _ (hsm ξ hξ)
  refine ⟨χ.comp (Units.map i.symm.toRingHom.toMonoidHom), IsOpen.preimage (Continuous.units_map _ hi') hχ, ?_⟩
  refine MonoidHom.ext fun σ => ?_
  have h1 : Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom (a (c σ))) = a (c σ) := by
    ext; simp
  have h2 := DFunLike.congr_fun e (c σ)
  simp only [MonoidHom.comp_apply] at h2 ⊢
  rw [h1, ← h2, hcc]

end

theorem UpperTheory.isLocallyAlgebraic_transfer_of_placeIso :
    GlobalArtinReciprocity → ∀ {F M Ω : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra M Ω] [IsAlgClosure M Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : Plc F} {w : Plc M} (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* M) (i : v.adicCompletion F ≃+* w.adicCompletion M) (hP : PlaceIso A v A w (RingEquiv.refl Ω) j i) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (κ' : ↥(Dec (F := M) A) →* (Qbar l)ˣ), (∀ (g : ↥(Dec (F := F) A)) (g' : ↥(Dec (F := M) A)), (∀ z, (g : G F Ω) z = (g' : G M Ω) z) → κ g = κ' g') → ∀ (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ), (∀ τ' : Emb l w, wt' τ' = wt ⟨τ'.1.comp i.toRingHom, τ'.2.comp hP.cont⟩) → (IsLocAlg h κ wt ↔ IsLocAlg h' κ' wt') := by
  intro hG F M Ω _ _ _ _ _ _ _ _ _ l _ A v w h h' j i hP κ κ' hκ wt wt' hwt
  obtain ⟨c, hc, hdeg, -, hsm⟩ := GlobalTheory.WeilTransport.weil_equiv F Ω A v h M Ω A w h' _ j i hP
  have hi' : Continuous i.symm := by
    have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
    have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion M w
    exact i.toEquiv.continuous_symm_iff.2
      (AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hP.cont)
  have hr : ∀ σ, WeilRel (RingEquiv.refl Ω) σ (c σ) := fun σ => (hc σ _).2 rfl
  have hr' : ∀ σ', WeilRel (RingEquiv.refl Ω) (c.symm σ') σ' := fun σ => (hc _ σ).2 (c.apply_symm_apply σ)
  have inj := _root_.GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits'
  constructor
  · refine locAlg_step c.symm.toMonoidHom (fun σ z => (hr' σ z).symm)
      (fun σ => by rw [← hdeg]; simp) i.symm hi' hP.cont (fun a' ha' => ⟨_, artin_step hG c.toMonoidHom c.surjective
        c.symm.toMonoidHom c.symm_apply_apply (fun ξ hξ => (hsm _ _).2 ?_) i.symm hP.cont a' ha' fun art hart σ => ?_,
          fun σ => by simp⟩) κ' κ (fun g g' hg => (hκ g' g fun z => (hg z).symm).symm) wt' wt fun τ => ?_
    · convert hξ using 1
      ext; simp
    · obtain ⟨art', hart'⟩ := hG M Ω
      refine _root_.GlobalTheory.LocDegOne.artin_of_placeIso F Ω A v h M Ω A w h' _ j i hP art art' hart hart' σ (c σ) _ (hr σ) ?_
      rw [← ha'.glob art' hart' (c σ)]
      congr 2
      ext; simp
    · rw [hwt]
      congr 1
      exact Subtype.ext (RingHom.ext fun x => by simp)
  · refine locAlg_step c.toMonoidHom (fun σ z => hr σ z) hdeg i hP.cont hi'
      (fun a ha => ⟨_, artin_step hG c.symm.toMonoidHom c.symm.surjective
        c.toMonoidHom c.apply_symm_apply (fun ξ hξ => (hsm _ _).1 hξ) i hi' a ha fun art' hart' σ => ?_,
          fun σ => by simp⟩) κ κ' hκ wt wt' hwt
    obtain ⟨art, hart⟩ := hG F Ω
    obtain ⟨b, -, -, hg⟩ := GlobalTheory.InvLocalArtin.exists_invLocalArtin M Ω A w h' art' hart'
    have hx : Units.map i.toRingHom.toMonoidHom (Units.map i.symm.toRingHom.toMonoidHom (b σ)) = b σ := by
      ext; simp
    have h1 := _root_.GlobalTheory.LocDegOne.artin_of_placeIso F Ω A v h M Ω A w h' _ j i hP art art' hart hart' (c.symm σ) σ _ (hr' σ)
      (by rw [hx]; exact hg σ)
    have h2 := inj F Ω art hart v (h1.trans (ha.glob art hart (c.symm σ)).symm)
    rw [← hg σ, ← hx, h2]
    rfl
end

