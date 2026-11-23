module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0128
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionUniversalSquareZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0132
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CotangentLocalOpenChartExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyProjectorComplexBounded
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0124
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormInRelativeImage
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupVanishingAntisymmetricCross
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem cup_add_cup_swap {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (a b : H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a', rfl⟩ := H1.mk_surjective F a
  obtain ⟨b', rfl⟩ := H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add (f := _), H2.mk_eq_zero]
  refine ⟨-(fun T T' φ => a'.1 T T' φ * b'.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [map_neg, Pi.neg_apply, d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp, map_mul]
  ring

theorem hopf_pull_lift_cup {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R)
    (π : CoefMap (RingHom.id R) (box F) G) (m : CoefMap (RingHom.id R) F G)
    (hm : ∀ c, m.pull1 c = π.pull1 ((boxL F).pull1 c + (boxR F).pull1 c))
    (t : H1 F ⊗[R] H1 F) :
    m.pull2 (TensorProduct.lift (cup F) t) =
      π.pull2 ((boxL F).pull2 (TensorProduct.lift (cup F) t) +
        (boxR F).pull2 (TensorProduct.lift (cup F) t) +
        TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.lift.tmul, CoefMap.pullCohomologyTwo_cup m a b, hm a, hm b, ← CoefMap.pullCohomologyTwo_cup π _ _]
    refine congrArg (fun x => π.pull2 x) ?_
    rw [CoefMap.pullCohomologyTwo_cup (boxL F) a b, CoefMap.pullCohomologyTwo_cup (boxR F) a b, TensorProduct.comm_tmul, map_sub,
      TensorProduct.lift.tmul, TensorProduct.lift.tmul, crossB_apply, crossB_apply]
    simp only [map_add (f := _), LinearMap.add_apply]
    have h := cup_add_cup_swap (box F) ((boxL F).pull1 b) ((boxR F).pull1 a)
    have h3 : cup (box F) ((boxR F).pull1 a) ((boxL F).pull1 b) =
        -cup (box F) ((boxL F).pull1 b) ((boxR F).pull1 a) :=
      eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h)
    rw [h3]
    abel
  | add x y hx hy =>
    simp only [map_add (f := _), map_sub, hx, hy]
    abel

theorem hopf_cross_antisymm : LowSt → ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), Hopf F False → ∀ t : H1 F ⊗[R] H1 F,
    TensorProduct.lift (cup F) t = 0 →
      TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t) = 0 := by
  intro hLow R _ C _ F hH t ht
  obtain ⟨D, _, G, π, m, hq, hm, -⟩ := hH
  have h2 := hopf_pull_lift_cup F G π m hm t
  simp only [ht, map_zero, zero_add] at h2
  obtain ⟨-, hinj, -⟩ := hLow R (C × C) D (box F) G π hq
  apply hinj.1
  rw [map_zero]
  exact h2.symm

end GlobalTheory.CompanionTheory.WedgeOf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CompanionTheory.ChartAlg in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_from_coordinates : ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ)
    (hb : TFBase γ l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) {V : X.Opens} {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∃ (c' : Chart γ 0 q κ V d) (e : R ⊗[O] Γ(X, V) ≃+* c'.D.B), TF l s c'.D ∧ (∀ r, e (r ⊗ₜ 1) = c'.D.i r) ∧
      (∀ i, e (1 ⊗ₜ c.t i) = c'.t i) ∧ ∀ f, ev c'.D c'.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f)) := by
  intro O R _ _ _ I γ l s hb X q κ hκ V d c
  let a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  have hstr : algebraMap O Γ(X, V) = strV q V := rfl
  have hE : (MvPolynomial.eval₂Hom (algebraMap O Γ(X, V)) c.t : MvPolynomial (Fin d) O →+* Γ(X, V)).Etale := c.etale
  have hF : Module.Flat O Γ(X, V) := flat_of_etale c.t hE
  let iL : R →+* R ⊗[O] Γ(X, V) := Algebra.TensorProduct.includeLeftRingHom
  have hl : ∀ x : R ⊗[O] Γ(X, V), (l : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun x h => by
    have := tf_tensor (G := Γ(X, V)) (O := O) (pdP γ s) l (hb.tf s) x (by rw [h]; exact zero_mem _)
    rw [hb.nil, Ideal.map_bot] at this
    exact this
  have hlk : ∀ (k : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) ^ k * x = 0 → x = 0 := fun k => by
    induction k with
    | zero => intro x h; simpa using h
    | succ k ih =>
      intro x h
      refine ih x (hl _ ?_)
      rw [← h, pow_succ']
      ring
  have hn : ∀ n : ℕ, n ≠ 0 → ∀ x : R ⊗[O] Γ(X, V), (n : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun n hn0 x h => by
    obtain ⟨k, u, hu⟩ := hb.dv n hn0
    refine hlk k x ?_
    have e := congrArg iL hu
    rw [map_mul, map_pow, map_natCast, map_natCast] at e
    rw [← e, mul_comm (n : R ⊗[O] Γ(X, V)), mul_assoc, h, mul_zero]
  obtain ⟨δ, hδ⟩ := exists_dp γ iL hn
  have hP := dividedPowerFiltration_eq_map γ iL δ hδ
  let g : Γ(X, V) →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL :=
    (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[O] R ⊗[O] Γ(X, V)).toRingHom
  let ψ : R ⧸ I →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL := Ideal.quotientMap _ iL Ideal.le_comap_map
  have hcomp : g.comp (strV q V) = ψ.comp κ := RingHom.ext fun a => by
    change Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[O] (algebraMap O Γ(X, V) a)) = ψ (κ a)
    rw [hκ]
    change _ = Ideal.Quotient.mk _ ((algebraMap O R a) ⊗ₜ[O] (1 : Γ(X, V)))
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let y : PtOver X q κ ((R ⊗[O] Γ(X, V)) ⧸ I.map iL) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec), by
      change (Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec) ≫ q = _
      rw [Category.assoc, fromSpec_comp q c.affine, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]⟩
  have hnil : IsNilpotent (I.map iL) := ⟨s, by
    have h := pow_le_pdP δ s
    rw [hP, hb.nil, Ideal.map_bot] at h
    exact le_bot_iff.1 h⟩
  let D : Thick (nlFun γ 0 X q κ) := mkT (R ⊗[O] Γ(X, V)) iL (I.map iL) δ ⟨fun h => (h rfl).elim, fun _ => hnil⟩ hδ y
    (fun r => rfl)
  have hin : InU V D := top_le_specMap c.affine g
  let c' : Chart γ 0 q κ V d :=
    { D := D
      t := fun k => (1 : R) ⊗ₜ[O] c.t k
      etale := etale_tensor c.t hE
      J_eq := rfl
      inV := hin
      rep := fun B' y' hy' => rep_tensor hstr hκ c.affine y (fun r => rfl) g (fun f => rfl) rfl B' y' hy' }
  have key : ∀ (r : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) * x ∈ pdP δ r → x ∈ pdP δ r := fun r x hx => by
    rw [hP] at hx ⊢
    exact tf_tensor (pdP γ r) l (hb.tf r) x hx
  refine ⟨c', RingEquiv.refl _, ⟨?_, fun r x hx => ?_⟩, fun r => rfl, fun k => rfl, fun f => ?_⟩
  · change pdP δ s = ⊥
    rw [hP, hb.nil, Ideal.map_bot]
  · exact key r x hx
  · have := evalAt_specMap c.affine g (pt D) rfl hin
    exact RingHom.congr_fun this f
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNbhd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Cot

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp [spMap]

theorem exists_nbhd : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∃ (P : Type) (_ : CommRing P) (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R ∧ (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) ∧ j ≫ s = spMap α ∧ spMap ε ≫ j = e ∧ Mono j ∧ ∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y := by
  intro R _ X s e he
  have : IsImmersion (e ≫ s) := by rw [he]; infer_instance
  have : IsImmersion e := IsImmersion.of_comp e s
  let U := e.coborderRange
  let e' : Sp R ⟶ U := e.liftCoborder
  have he' : e' ≫ U.ι = e := e.liftCoborder_ι
  let t : (U : Scheme.{0}) ⟶ Sp R := U.ι ≫ s
  have het : e' ≫ t = 𝟙 _ := by simp only [t]; rw [← Category.assoc, he', he]
  have hE : IsAffine (e'.ker ^ 2).subscheme := _root_.GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq R U t e' het
  let c := (e'.ker ^ 2).subschemeι
  have hle : c.ker ≤ e'.ker := by
    simp only [c, Scheme.IdealSheafData.ker_subschemeι]
    exact pow_le_of_le_one zero_le le_top two_ne_zero
  let i' : Sp R ⟶ (e'.ker ^ 2).subscheme := IsClosedImmersion.lift c e' hle
  have hi' : i' ≫ c = e' := IsClosedImmersion.lift_fac _ _ _
  let E := (e'.ker ^ 2).subscheme
  let P : Type := Γ(E, ⊤)
  let iso : E ≅ Sp P := E.isoSpec
  let j : Sp P ⟶ X := iso.inv ≫ c ≫ U.ι
  let α : R →+* P := (Spec.preimage (iso.inv ≫ c ≫ t)).hom
  let ε : P →+* R := (Spec.preimage (i' ≫ iso.hom)).hom
  have hα : spMap α = iso.inv ≫ c ≫ t := Spec.map_preimage _
  have hε : spMap ε = i' ≫ iso.hom := Spec.map_preimage _
  have hjs : j ≫ s = spMap α := by simp [j, hα, t]
  have hεj : spMap ε ≫ j = e := by
    simp only [hε, j, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i', hi', he']
  refine ⟨P, inferInstance, α, ε, j, ?_, ?_, hjs, hεj, inferInstance, ?_⟩
  · apply spMap_inj
    rw [spMap_comp, hε, hα, spMap_id]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i', hi', het]
  · have h0 : CommRingCat.ofHom ε = i'.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom := by
      have h1 : (spMap ε).appTop = (Scheme.ΓSpecIso (.of P)).hom ≫ i'.appTop := by
        rw [hε, Scheme.Hom.comp_appTop]
        simp only [iso, Scheme.isoSpec, asIso_hom]
        exact congrArg (fun f ↦ f ≫ i'.appTop) (Scheme.toSpecΓ_appTop E)
      have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ε)
      rw [h1, Category.assoc] at h2
      exact ((cancel_epi _).1 h2).symm
    have hk : ∀ a : P, ε a = 0 → i'.appTop a = 0 := fun a ha ↦ by
      have h3 : (Scheme.ΓSpecIso (.of R)).hom (i'.appTop a) = 0 := by
        have := congrArg (fun f ↦ f.hom a) h0
        simpa [ha] using this.symm
      exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1).1 h3
    intro a b ha hb
    exact _root_.GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero R U e' i' hi' a b (hk a ha) (hk b hb)
  · intro Q B _ _ q ρ y hq hsq hy
    have hsurj : Function.Surjective (spMap q) := by
      intro x
      have hx : x ∈ Set.range (PrimeSpectrum.comap q) := by
        rw [range_comap_of_surjective _ _ hq]
        intro a ha
        have : a * a = 0 := hsq a a ha ha
        exact x.2.mem_or_mem (by simp [this] : a * a ∈ x.asIdeal) |>.elim id id
      exact hx
    have hr : Set.range y ⊆ Set.range U.ι := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨x', rfl⟩ := hsurj x
      have h1 : y (spMap q x') = e (spMap ρ x') := by
        rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
      rw [h1, ← he', Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    let y' : Sp Q ⟶ U := IsOpenImmersion.lift U.ι y hr
    have hy' : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
    have hy2 : spMap q ≫ y' = spMap ρ ≫ e' := by
      rw [← cancel_mono U.ι, Category.assoc, hy', hy, Category.assoc, he']
    have hk : c.ker ≤ y'.ker := by
      simp only [c, Scheme.IdealSheafData.ker_subschemeι]
      exact _root_.GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker R Q B U e' q ρ y' hq hsq hy2
    let w : Sp Q ⟶ E := IsClosedImmersion.lift c y' hk
    have hw : w ≫ c = y' := IsClosedImmersion.lift_fac _ _ _
    refine ⟨(Spec.preimage (w ≫ iso.hom)).hom, ?_⟩
    have : spMap (Spec.preimage (w ≫ iso.hom)).hom = w ≫ iso.hom := Spec.map_preimage _
    rw [this]
    simp only [j, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc w, hw, hy']

theorem cotSt : CotSt := by
  intro R _ X s e g he hs
  obtain ⟨P, _, α, ε, j, h1, h2, h3, h4, h5, h6⟩ := exists_nbhd R X s e he
  obtain ⟨W, i1, i2, i3, i4, y₀, hy⟩ := _root_.GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting R X s e P α ε j h1 h2 h3 h4 h5 h6
  refine ⟨W, i1, i2, i3, i4, y₀, _root_.GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens R W g fun p ↦ ?_, hy⟩
  obtain ⟨r, A, C, _, _, _, _, j, k, hr, _, _, hjs, hε, f1, f2, f3⟩ := _root_.GlobalTheory.CompanionTheory.CotChart.exists_smooth_chart R X s e g he hs p
  obtain ⟨E⟩ := _root_.GlobalTheory.CompanionTheory.CotLoc.cotangent_away R X s e he W y₀ hy r A C j k hjs hε
  have : Nontrivial (Localization.Away r) := by
    refine ⟨⟨algebraMap R _ 1, algebraMap R _ 0, fun h ↦ ?_⟩⟩
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) _).1 h
    have h0 : r ^ n ∈ p.asIdeal := by
      have : r ^ n = 0 := by simpa using hc
      rw [this]; exact zero_mem _
    exact hr (p.2.mem_of_pow_mem n h0)
  have : Nontrivial A := (algebraMap A (Localization.Away r)).domain_nontrivial
  have hf : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) := Module.Free.of_equiv E.symm
  have hn : Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) := Module.Finite.equiv E.symm
  exact ⟨r, hr, hf, hn, by rw [E.finrank_eq, Module.finrank_baseChange, f3]⟩

end GlobalTheory.CompanionTheory.Cot
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareTransportAlongEquiv
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem wedge_transport {R : Type} [CommRing R] {V V' W W' : Type} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V'] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] (u : V ≃ₗ[R] V') (v : W ≃ₗ[R] W') (c : V →ₗ[R] V →ₗ[R] W) (c' : V' →ₗ[R] V' →ₗ[R] W') (h : ∀ a b, v (c a b) = c' (u a) (u b)) (e : ⋀[R]^2 V' ≃ₗ[R] W') (he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = c' a b) : ∃ e' : ⋀[R]^2 V ≃ₗ[R] W, ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = c a b := by
  have h₁ : (u : V →ₗ[R] V') ∘ₗ (u.symm : V' →ₗ[R] V) = LinearMap.id :=
    LinearMap.ext fun x => by simp
  have h₂ : (u.symm : V' →ₗ[R] V) ∘ₗ (u : V →ₗ[R] V') = LinearMap.id :=
    LinearMap.ext fun x => by simp
  let A : ⋀[R]^2 V ≃ₗ[R] ⋀[R]^2 V' :=
    LinearEquiv.ofLinear (exteriorPower.map 2 (u : V →ₗ[R] V'))
      (exteriorPower.map 2 (u.symm : V' →ₗ[R] V))
      (by rw [← exteriorPower.map_comp, h₁, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, h₂, exteriorPower.map_id])
  refine ⟨A.trans (e.trans v.symm), fun a b => ?_⟩
  have hu : (⇑(u : V →ₗ[R] V') ∘ ![a, b]) = ![u a, u b] := by
    funext i
    fin_cases i <;> rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply,
    exteriorPower.map_apply_ιMulti, hu, he, ← h, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.HopfC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareVectorBundleRank
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem vb_exteriorPower_two : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ),
    VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by
  intro R V _ _ _ g h
  obtain ⟨hf, hp, hr⟩ := h
  have hproj : Module.Projective R (⋀[R]^2 V) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hp
    haveI : Module.Free R (⋀[R]^2 (V →₀ R)) := exteriorPower.instFree R 2
    refine Module.Projective.of_split (exteriorPower.map 2 s)
      (exteriorPower.map 2 (Finsupp.linearCombination R id)) ?_
    rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hb := LocalizedModule.isBaseChange p.asIdeal.primeCompl V
  have hb2 := GlobalTheory.TopForm.isBaseChange_exteriorPower hb 2
  let S := Localization.AtPrime p.asIdeal
  let M := LocalizedModule p.asIdeal.primeCompl V
  let q : PrimeSpectrum S := IsLocalRing.closedPoint S
  have hq : PrimeSpectrum.comap (algebraMap R S) q = p :=
    PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := p.asIdeal))
  have h1 := Module.rankAtStalk_isBaseChange hb q
  have h2 := Module.rankAtStalk_isBaseChange hb2 q
  rw [hq] at h1 h2
  haveI : Module.Finite S M := Module.Finite.equiv hb.equiv
  haveI : Module.Flat S M := Module.Flat.of_linearEquiv hb.equiv.symm
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  have h3 : Module.finrank S M = g := by
    rw [← hr p, ← h1, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank S (⋀[S]^2 M) = _
  rw [exteriorPower.finrank_eq, h3]

end GlobalTheory.CompanionTheory.WedgeOf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteChains
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfN

theorem QIsoAt.transport {R A₀ A₁ A₂ B₀ B₁ B₂ B₀' B₁' B₂' : Type} [CommRing R] [AddCommGroup A₀] [AddCommGroup A₁]
    [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₀'] [AddCommGroup B₁']
    [AddCommGroup B₂'] [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R B₀'] [Module R B₁'] [Module R B₂'] {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁}
    {b₁ : B₁ →ₗ[R] B₂} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'} {f : A₁ →ₗ[R] B₁}
    (v₀ : B₀ →ₗ[R] B₀') (v₁ : B₁ →ₗ[R] B₁') (v₂ : B₂ →ₗ[R] B₂')
    (s₀ : Function.Surjective v₀) (s₁ : Function.Bijective v₁) (s₂ : Function.Injective v₂)
    (c₀ : ∀ x, v₁ (b₀ x) = b₀' (v₀ x)) (c₁ : ∀ x, v₂ (b₁ x) = b₁' (v₁ x))
    (H : QIsoAt a₀ a₁ b₀ b₁ f) : QIsoAt a₀ a₁ b₀' b₁' (v₁ ∘ₗ f) := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := s₀ y
    exact H.1 x hx ⟨y, s₁.1 (by rw [c₀, hy]; rfl)⟩
  · obtain ⟨z, rfl⟩ := s₁.2 z
    obtain ⟨x, y, hx, hy⟩ := H.2 z (s₂ (by rw [c₁, hz, map_zero]))
    refine ⟨x, v₀ y, hx, ?_⟩
    rw [← c₀, ← hy, map_sub]; rfl

theorem finite_chains (P : Type) [PartialOrder P] [Finite P] (n : ℕ) : Finite (Fin (n + 1) ⥤ Pᵒᵖ) := by
  have : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun (c : Fin (n + 1) ⥤ Pᵒᵖ) (i : Fin (n + 1)) ↦ c.obj i) fun c c' h ↦ ?_
  exact CategoryTheory.Functor.ext (fun i ↦ congrFun h i) (fun _ _ _ ↦ Subsingleton.elim _ _)

theorem flat_Cn {R : Type} [CommRing R] (P : Type) [PartialOrder P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
    (hF : ∀ T, Module.Flat R (F.obj T)) (n : ℕ) : Module.Flat R (Cn F n) := by
  have := finite_chains P n
  have := Fintype.ofFinite (Fin (n + 1) ⥤ Pᵒᵖ)
  classical
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R (Fin (n + 1) ⥤ Pᵒᵖ)
    (fun c ↦ F.obj (c.obj (Fin.last n)))).symm

theorem perfNoeth : CxSt → DictSt → PerfNoethSt := by
  intro hCx hD R _ P _ _ F hN hfl hf0 hfs
  obtain ⟨hd, -⟩ := hCx R Pᵒᵖ F
  obtain ⟨e₀, e₁, e₂, e₃, -, -, -, -, h0, h1, h2⟩ := hD R Pᵒᵖ F
  obtain ⟨e, h, B, i1, i2, i3, i4, i5⟩ := _root_.GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation P F
  have := fun n ↦ flat_Cn P F hfl n
  obtain ⟨Q, ψ, f1, f2, f3, f4⟩ := _root_.GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model (fun n ↦ Cn F n) (dn F) hd e h B i1 i2 i3 i4 i5 hf0 hfs
  have g₀ : ∀ x, e₁ (dn F 0 x) = d0 F (e₀ x) := h0
  have g₁ : ∀ x, e₂ (dn F 1 x) = d1 F (e₁ x) := h1
  have g₂ : ∀ x, e₃ (dn F 2 x) = d2 F (e₂ x) := h2
  have k : ∀ n x, ψ (n + 1) ((Q.d n (n + 1)).hom x) = dn F n (ψ n x) := fun n x ↦
    LinearMap.congr_fun (f3 n) x
  have lt : ∀ {A B A' B' : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B'] [Module R A]
      [Module R B] [Module R A'] [Module R B'] (M : ModuleCat.{0} R) (u : A ≃ₗ[R] A') (v : B ≃ₗ[R] B')
      (b : A →ₗ[R] B) (b' : A' →ₗ[R] B'), (∀ x, v (b x) = b' (u x)) →
      ∀ x, (v : B →ₗ[R] B').lTensor M (b.lTensor M x) = b'.lTensor M ((u : A →ₗ[R] A').lTensor M x) := by
    intro A B A' B' _ _ _ _ _ _ _ _ M u v b b' h x
    have : (v : B →ₗ[R] B') ∘ₗ b = b' ∘ₗ (u : A →ₗ[R] A') := LinearMap.ext h
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, this]
  have bij : ∀ {A A' : Type} [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R A'] (M : ModuleCat.{0} R)
      (u : A ≃ₗ[R] A'), Function.Bijective ((u : A →ₗ[R] A').lTensor M) := fun M u ↦
    (u.lTensor M).bijective
  refine ⟨Q.X 0, Q.X 1, Q.X 2, Q.X 3, (Q.d 0 1).hom, (Q.d 1 2).hom, (Q.d 2 3).hom, (e₀ : _ →ₗ[R] _) ∘ₗ ψ 0,
    (e₁ : _ →ₗ[R] _) ∘ₗ ψ 1, (e₂ : _ →ₗ[R] _) ∘ₗ ψ 2, ⟨f1 0, f2 0⟩, ⟨f1 1, f2 1⟩, ⟨f1 2, f2 2⟩, ⟨f1 3, f2 3⟩,
    ?_, ?_, ?_, ?_, ⟨(e₃ : _ →ₗ[R] _) ∘ₗ ψ 3, ?_⟩, fun M ↦ ?_⟩
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d 0 1 2)
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d 1 2 3)
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, k]
    exact g₀ _
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [k 1]; exact g₁ _
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [k 2]; exact g₂ _
  · obtain ⟨q0, qs⟩ := f4 M
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    exact ⟨QIsoAt.transport LinearMap.id _ _ Function.surjective_id (bij M e₀) (bij M e₁).1
        (fun x ↦ by simp) (lt M e₀ e₁ _ _ g₀) q0,
      QIsoAt.transport _ _ _ (bij M e₀).2 (bij M e₁) (bij M e₂).1 (lt M e₀ e₁ _ _ g₀) (lt M e₁ e₂ _ _ g₁) (qs 0),
      QIsoAt.transport _ _ _ (bij M e₁).2 (bij M e₂) (bij M e₃).1 (lt M e₁ e₂ _ _ g₁) (lt M e₂ e₃ _ _ g₂) (qs 1)⟩

end GlobalTheory.CompanionTheory.PerfN
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpressionStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_integral_expression : ∀ {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K)), (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∀ (e : ℕ), 0 < e → ∀ (y : Fin m → MvPolynomial σ K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) (MvPolynomial σ K ⧸ I) → ∀ (w : ℕ) (a : MvPolynomial σ K), a.IsHomogeneous (e * w) → ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧ a ^ s + ∑ l ∈ Finset.range s, MvPolynomial.aeval y (c l) * a ^ l ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.Geo.exists_hom_relation | exact GlobalTheory.CompanionTheory.Geo.exists_hom_relation | (intros; apply GlobalTheory.CompanionTheory.Geo.exists_hom_relation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormInRelativeImageStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_form_in_relative_image : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ) (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 → Tset g D.1 ⊆ S → ∃ ω ∈ relOm K (I0 n K S) a, omMap (incl le_top) a ω = monW K g D := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningGradedVanishNegativeStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_graded_vanish_negative : ∀ {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ), r < 0 → ∀ j : ℕ,
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := by
  first | exact @GlobalTheory.CompanionTheory.Cone.HU_gr_neg | exact GlobalTheory.CompanionTheory.Cone.HU_gr_neg | (intros; apply GlobalTheory.CompanionTheory.Cone.HU_gr_neg <;> assumption)
end

