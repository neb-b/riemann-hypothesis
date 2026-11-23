module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_vanishing_from_cover : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS U S) j)) → ∀ j < s, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS U S) j)) → ∀ j, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS U S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H F j)) := by
  first | exact @GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | exact GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | (intros; apply GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFil

section Rings

variable {R B : Type} [CommRing R] [CommRing B] {I : Ideal R} {J : Ideal B}

theorem dividedPowerFiltration_anti (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') : pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

theorem one_mem_pdP_zero (δ : DividedPowers J) : (1 : B) ∈ pdP δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem mul_mem_map (γ : DividedPowers I) (i : R →+* B) (r r' : ℕ) {x y : B}
    (hx : x ∈ (pdP γ r).map i) (hy : y ∈ (pdP γ r').map i) : x * y ∈ (pdP γ (r + r')).map i := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul] at h
  exact Ideal.map_mono (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le γ r r') h

theorem dpow_mem_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ (pdP γ n).map i := by
  have h0 : ∀ y ∈ J, δ.dpow 0 y ∈ (pdP γ 0).map i := fun y hy => by
    rw [δ.dpow_zero hy, ← map_one i]
    exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
  rw [hJ] at hx
  revert n
  refine Submodule.span_induction (p := fun x _ => ∀ n, δ.dpow n x ∈ (pdP γ n).map i) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩ n
    rw [hi.2 a ha]
    exact Ideal.mem_map_of_mem i (GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ n ha)
  · intro n
    by_cases hn : n = 0
    · subst hn
      exact h0 0 J.zero_mem
    · rw [δ.dpow_eval_zero hn]
      exact Ideal.zero_mem _
  · intro y z hy hz ihy ihz n
    have hy' : y ∈ J := hJ ▸ hy
    have hz' : z ∈ J := hJ ▸ hz
    rw [δ.dpow_add hy' hz']
    refine Ideal.sum_mem _ fun ab hab => ?_
    have e : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    rw [← e]
    exact mul_mem_map γ i _ _ (ihy _) (ihz _)
  · intro a y hy ihy n
    have hy' : y ∈ J := hJ ▸ hy
    rw [smul_eq_mul, δ.dpow_mul hy']
    exact Ideal.mul_mem_left _ _ (ihy n)

theorem dividedPowerFiltration_eq_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) (r : ℕ) : pdP δ r = (pdP γ r).map i := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map hi r hx)
  rintro _ ⟨l, hl, hr, rfl⟩
  have key : ∀ l : List (ℕ × B), (∀ q ∈ l, q.2 ∈ J) →
      (l.map fun q => δ.dpow q.1 q.2).prod ∈ (pdP γ (l.map Prod.fst).sum).map i := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [← map_one i]
      exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
    | cons a t ih =>
      intro h
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact mul_mem_map γ i _ _ (dpow_mem_map γ δ i hi hJ (h a (by simp)) _)
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
  exact Ideal.map_mono (dividedPowerFiltration_anti γ hr) (key l hl)

end Rings

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

theorem sub_mem_J (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (z : c.D.B) : f.φ z - g.φ z ∈ T.J := by
  obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
  have e := (hu _ f.pt).trans (hu _ g.pt).symm
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun e (Ideal.Quotient.mk _ z))

theorem sub_mem_pdP (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (n : ℕ) {x : c.D.B} (hx : x ∈ (pdP γ n).map c.D.i) : f.φ x - g.φ x ∈ pdP T.δ (n + 1) := by
  refine Submodule.span_induction (p := fun x _ => f.φ x - g.φ x ∈ pdP T.δ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, -, rfl⟩
    have e : f.φ (c.D.i a) - g.φ (c.D.i a) = 0 := by rw [f.comm, g.comm, sub_self]
    rw [e]
    exact Ideal.zero_mem _
  · rw [map_zero, map_zero, sub_zero]
    exact Ideal.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact Ideal.add_mem _ hy hz
  · intro a y hy ih
    have e : f.φ (a • y) - g.φ (a • y) = f.φ a * (f.φ y - g.φ y) + (f.φ a - g.φ a) * g.φ y := by
      rw [smul_eq_mul, map_mul, map_mul]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h1 : f.φ a - g.φ a ∈ pdP T.δ 1 := T.J_le_pdPow_one (sub_mem_J c hT f g a)
    have hm : (pdP γ n).map c.D.i ≤ pdP c.D.δ n :=
      Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map c.D.compat n hx
    have hy' : y ∈ pdP c.D.δ n := hm hy
    have h2 : g.φ y ∈ pdP T.δ n := dividedPowerFiltration_map g.dp n hy'
    have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ 1 n (Ideal.mul_mem_mul h1 h2)
    rwa [add_comm 1 n] at h3

theorem chart_grConst : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  intro O R _ _ I γ p X q κ V d c h Q hQ hD
  have h1 : ∀ r, c.D.pdPow r = (pdP γ r).map c.D.i := fun r =>
    dividedPowerFiltration_eq_map γ c.D.δ c.D.i c.D.compat c.J_eq r
  refine ⟨h1, ?_⟩
  intro n T σ σ' x hx
  have hx' : (show c.D.B from x) ∈ c.D.pdPow ((n : ℤ).toNat) := hx
  rw [Int.toNat_natCast, h1] at hx'
  change _ ∈ T.obj.pdPow (((n : ℤ) + 1).toNat)
  have e : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [e]
  exact sub_mem_pdP c (hQ _ T.property) σ.hom σ'.hom n hx'

end GlobalTheory.CompanionTheory.ChartFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainBaseChangeEquivalences
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CochainBC

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C]
    [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F'),
    ∃ (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F') (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F'),
      (∀ c, E₀ (1 ⊗ₜ c) = fun T ↦ m.α T (c T)) ∧ (∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ)) ∧
      (∀ c, E₂ (1 ⊗ₜ c) = fun T T' T'' φ ψ ↦ m.α T'' (c T T' T'' φ ψ)) ∧
      (∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x)) ∧ ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x) := by
  intro R R' _ _ _ C _ _ _ F F' m
  obtain ⟨E₀, hE₀⟩ := GlobalTheory.CompanionTheory.PerfExt.ext0 m
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.CompanionTheory.PerfExt.ext1 m
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.CompanionTheory.PerfExt.ext2 m
  refine ⟨E₀, E₁, E₂, hE₀, hE₁, hE₂, fun x => ?_, fun x => ?_⟩
  · have h := GlobalTheory.CompanionTheory.PerfExt.bc_ext (E₁.toLinearMap ∘ₗ (d0 F).baseChange R') ((d0 F') ∘ₗ E₀.toLinearMap) (by
      intro n
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, hE₁, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hE₀]
      funext T T' φ
      dsimp only
      rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, m.naturality])
    exact LinearMap.congr_fun h x
  · have h := GlobalTheory.CompanionTheory.PerfExt.bc_ext (E₂.toLinearMap ∘ₗ (d1 F).baseChange R') ((d1 F') ∘ₗ E₁.toLinearMap) (by
      intro n
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, hE₂, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hE₁]
      funext T T' T'' φ ψ
      dsimp only
      rw [d1_apply, d1_apply, map_add (f := _), map_sub, m.naturality])
    exact LinearMap.congr_fun h x

end GlobalTheory.CompanionTheory.CochainBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Low

variable {R : Type} [CommRing R]

theorem homology_equiv {A B D : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] [Module R A] [Module R B]
    [Module R D] (a : A →ₗ[R] B) (b : B →ₗ[R] D)
    (w : ModuleCat.ofHom a ≫ ModuleCat.ofHom b = 0) :
    Nonempty ((LinearMap.ker b ⧸ (LinearMap.range a).comap (LinearMap.ker b).subtype) ≃ₗ[R]
      (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).homology) := by
  have heq : (LinearMap.range a).comap (LinearMap.ker b).subtype =
      LinearMap.range (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).moduleCatToCycles := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ heq).trans
    (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).moduleCatHomologyIso.symm.toLinearEquiv⟩

variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev nerveComplex : CochainComplex (ModuleCat.{0} R) ℕ :=
  nerveCx.obj (F ⋙ forget₂ (CommAlgCat.{0} R) (AlgCat.{0} R) ⋙ forget₂ (AlgCat.{0} R) (ModuleCat.{0} R))

theorem d_eq (n : ℕ) : (nerveComplex F).d n (n + 1) = ModuleCat.ofHom (MainStatements.Hodge.dn F n) :=
  nerveCx_d _ n

theorem d_zero : (nerveComplex F).d 0 0 = ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0) :=
  ((nerveComplex F).shape 0 0 (by simp)).trans ModuleCat.ofHom_zero.symm

theorem comp_eq (n : ℕ) :
    ModuleCat.ofHom (MainStatements.Hodge.dn F n) ≫ ModuleCat.ofHom (MainStatements.Hodge.dn F (n + 1)) = 0 := by
  simpa only [d_eq] using! (nerveComplex F).d_comp_d n (n + 1) (n + 1 + 1)

theorem comp_zero_eq :
    ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0) ≫ ModuleCat.ofHom (MainStatements.Hodge.dn F 0) = 0 := by
  rw [ModuleCat.ofHom_zero, zero_comp]

def scIso (n : ℕ) : (nerveComplex F).sc' n (n + 1) (n + 2) ≅
    ShortComplex.mk (ModuleCat.ofHom (MainStatements.Hodge.dn F n)) (ModuleCat.ofHom (MainStatements.Hodge.dn F (n + 1))) (comp_eq F n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((d_eq F n).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((d_eq F (n + 1)).symm.trans (Category.comp_id _).symm))

def scIso0 : (nerveComplex F).sc' 0 0 1 ≅
    ShortComplex.mk (ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0)) (ModuleCat.ofHom (MainStatements.Hodge.dn F 0))
      (comp_zero_eq F) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((d_zero F).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((d_eq F 0).symm.trans (Category.comp_id _).symm))

theorem homology_nerveCx :
    ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveComplex F).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveComplex F).homology (n + 1)) := by
  intro R _ C _ F
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨e⟩ := GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_equiv
      (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0)
      (MainStatements.Hodge.dn F 0) (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.comp_zero_eq F)
    have hbot : (LinearMap.range (0 : MainStatements.Hodge.Cn F 0 →ₗ[R]
        MainStatements.Hodge.Cn F 0)).comap
        (LinearMap.ker (MainStatements.Hodge.dn F 0)).subtype = ⊥ := by
      simp
    exact ⟨((Submodule.quotEquivOfEqBot _ hbot).symm.trans e).trans
      (((nerveComplex F).homologyIsoSc'
        0 0 1 (by simp) (by simp)) ≪≫
        ShortComplex.homologyMapIso (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.scIso0 F)).symm.toLinearEquiv⟩
  · obtain ⟨e⟩ := GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_equiv
      (MainStatements.Hodge.dn F n) (MainStatements.Hodge.dn F (n + 1))
      (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.comp_eq F n)
    exact ⟨e.trans
      (((nerveComplex F).homologyIsoSc'
        n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
        ShortComplex.homologyMapIso (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.scIso F n)).symm.toLinearEquiv⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve.Low
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleZeroAlt
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto

universe u v w

noncomputable section

namespace GlobalTheory.CompanionTheory.CovDescent

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)

theorem cosieve_capU (hU : ∀ α, Cosieve (U α)) (S : Finset ι) : Cosieve (capU U S) := fun _ _ φ h =>
  ⟨h.1.imp fun a ha => hU a φ ha, fun α hα => hU α φ (h.2 α hα)⟩

variable {U} in
theorem capU_mono {S T : Finset ι} (h : S ⊆ T) {X : C} (hX : capU U T X) : capU U S X :=
  ⟨hX.1, fun α hα => hX.2 α (h hα)⟩

variable {U} in
theorem capU_cons {n : ℕ} {a : ι} {i : Fin n → ι} {T : C} (ha : U a T) (hi : capU U (ent i) T) :
    capU U (ent (Fin.cons (α := fun _ => ι) a i)) T := by
  refine ⟨⟨a, ha⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  refine Fin.cases ?_ (fun k => ?_) k
  · exact ha
  · exact hi.2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

def liftC (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : ComposableArrows (capU U S).FullSubcategory n :=
  (capU U S).lift s fun k => cosieve_capU U hU S (s.map (homOfLE (Fin.zero_le k))) h

abbrev Tm (n : ℕ) : PM.{max u v w} R ι := (covSy F U hQ).term n

def evL (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : (Tm F U hQ n).M S →ₗ[R] F.obj (s.obj (Fin.last n)) :=
  (LinearMap.proj (R := R) (φ := fun t : ComposableArrows (capU U S).FullSubcategory n =>
    ((capU U S).ι ⋙ F).obj (t.obj (Fin.last n))) (liftC U hU S s h)) ∘ₗ
    (relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n).subtype

variable {F U hQ}

theorem evL_congr (hU : ∀ α, Cosieve (U α)) {n p : ℕ} (f : ∀ i : Fin p → ι, (Tm F U hQ n).M (ent i))
    {i i' : Fin p → ι} (e : i = i') (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0))
    (h' : capU U (ent i') (s.obj 0)) : evL F U hQ hU _ s h (f i) = evL F U hQ hU _ s h' (f i') := by
  subst e; rfl

theorem evL_d (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X p)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0)) :
    evL F U hQ hU _ s h ((Tm F U hQ n).cech.d p y i) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        evL F U hQ hU _ s (capU_mono (ent_comp i k.succAbove) h) (y (i ∘ k.succAbove)) := by
  have e := congrArg ((evL F U hQ hU _ s h) ∘ₗ
    (LinearMap.proj (R := R) (φ := fun i : Fin (p + 2) → ι => (Tm F U hQ n).M (ent i)) i))
    (Cos.d_apply (Tm F U hQ n).cech p y)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at e
  simp only [map_zsmul] at e
  exact e

theorem capU_const {b : ι} {T : C} (hb : U b T) : capU U (ent fun _ : Fin 1 => b) T := by
  refine ⟨⟨b, hb⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  exact hb

theorem cons_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Function.comp]

theorem cons_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ j.succ.succAbove =
      Fin.cons (α := fun _ => ι) a (i ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.comp]
  · simp [Function.comp]

theorem M_ext (hU : ∀ α, Cosieve (U α)) {n : ℕ} {S : Finset ι} {x y : (Tm F U hQ n).M S}
    (h : ∀ t : ComposableArrows (capU U S).FullSubcategory n,
      evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property x =
        evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property y) : x = y :=
  Subtype.ext (funext h)

def mkM {n : ℕ} (S : Finset ι) (f : CH.Cn ((capU U S).ι ⋙ F) n)
    (hf : ∀ t : ComposableArrows (capU U S).FullSubcategory n, Q (t.obj 0).obj → f t = 0) :
    (Tm F U hQ n).M S :=
  (⟨f, hf⟩ : relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n)

theorem evL_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (x : (Tm F U hQ n).M S)
    (s : ComposableArrows C n) (h : capU U S (s.obj 0)) (hs : Q (s.obj 0)) :
    evL F U hQ hU S s h x = 0 :=
  x.2 (liftC U hU S s h) hs

theorem cocycle_eq (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X (p + 1))
    (hy : (Tm F U hQ n).cech.d (p + 1) y = 0) (i : Fin (p + 2) → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d (p + 1) y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_succ] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 : ∀ j : Fin (p + 2),
      evL F U hQ hU _ s (capU_mono (ent_comp _ j.succ.succAbove) h')
        (y ((Fin.cons (α := fun _ => ι) b i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) =
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) :=
    fun j => evL_congr hU y (cons_succ _ i j) s _ _
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

theorem cocycle_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (y : (Tm F U hQ n).cech.X 0)
    (hy : (Tm F U hQ n).cech.d 0 y = 0) (i : Fin 1 → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = evL F U hQ hU _ s (capU_const hb) (y fun _ => b) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d 0 y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_two] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 := evL_congr hU y (i := (Fin.cons (α := fun _ => ι) b i : Fin 2 → ι) ∘ (1 : Fin 2).succAbove)
    (i' := fun _ => b) (funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl) s (capU_mono (ent_comp _ _) h') (capU_const hb)
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

def hh (hU : ∀ α, Cosieve (U α)) (a : ∀ T, (∃ b, U b T) → ι) (ha : ∀ T h, U (a T h) T) {p n : ℕ}
    (y : (Tm F U hQ n).cech.X (p + 1)) : (Tm F U hQ n).cech.X p := fun i =>
  mkM (ent i) (fun t => evL F U hQ hU _ (t ⋙ (capU U (ent i)).ι)
      (capU_cons (ha _ (t.obj 0).property.1) (t.obj 0).property)
      (y (Fin.cons (α := fun _ => ι) (a _ (t.obj 0).property.1) i)))
    fun t ht => evL_zero hU _ _ _ _ ht

theorem desc (hU : ∀ α, Cosieve (U α)) (n : ℕ) : (Tm F U hQ n).Ex := by
  have hc : ∀ T : C, ∀ h : ∃ b, U b T, ∃ b, U b T := fun _ h => h
  choose a ha using hc
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU _ i _ _).trans ?_
    refine Eq.trans ?_ (map_zero (evL F U hQ hU _ _ _)).symm
    rw [Fin.sum_univ_two]
    change (-1 : ℤ) ^ 0 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x +
      (-1 : ℤ) ^ 1 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x = 0
    simp
  · rw [one_smul]
    refine M_ext hU fun t => ?_
    have hb := ha _ (t.obj 0).property.1
    have h1 := congrArg (evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const hb))
      (congrFun hx fun _ => a _ (t.obj 0).property.1)
    exact (h1.trans (map_zero _)).trans (map_zero _).symm
  · refine ⟨mkM ∅ (fun t => evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const (ha _ (t.obj 0).property.1))
      (y fun _ => a _ (t.obj 0).property.1)) fun t ht => evL_zero hU _ _ _ _ ht, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    exact (cocycle_zero hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
  · refine ⟨hh hU a ha y, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU (hh hU a ha y) i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property).trans ?_
    refine Eq.trans ?_ (cocycle_eq hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
    rfl

theorem covDesc : CovDesc := fun _ _ _ _ _ _ _ _ _ _ hU n => desc hU n

end GlobalTheory.CompanionTheory.CovDescent
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordsOfEtaleBasicOpenStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_of_etale_basic_open : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens}, IsAffineOpen W → ∀ (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)), letI := (strV q W).toAlgebra; (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g)) (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale → ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) := by
  first | exact @GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen | exact GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen | (intros; apply GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen <;> assumption)
end

