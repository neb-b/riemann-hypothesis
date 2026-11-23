module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyCountableDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa

theorem exists_keyPB_on {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : KeyIn R) (Q : Out.PolAV (Sp R'))
    (φ : Q.A.left ⟶ x.P.A.left) (h : IsGrpPullback Q.A x.P.A (spMap f) φ) (hL : LBIso Q.L (x.P.L.pull φ))
    (hgg : Q.g = x.P.g) (hg : 1 ≤ Q.g) :
    ∃ rig hr th hth v hv, KeyPB ⟨Q, hg, rig, hr, th, hth, v, hv⟩ x f := by
  obtain ⟨w, hw⟩ := hL
  have hw' := (isGen_iff _).1 hw
  have he : eSec Q.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  obtain ⟨rig, hr, hm⟩ := H1.exists_gen_move x.P.isLB Q.isLB w hw' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec Q.A)
    (fun _ => 1) (spMap f) (fun _ => he) x.rig x.rig_gen
  obtain ⟨th, e'⟩ := sec_pull_down hw' x.P.isLB Q.isLB x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj Q.A := Q.isAb.comm
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange R R' f x.P.A Q.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  have hb : ∀ {n : ℕ} (e : n = x.P.g), IsLieBasis fun i : Fin n => u (i.cast e) := fun e => by
    subst e
    exact hu
  refine ⟨rig, hr, th, fun s => ?_, _, hb hgg, φ, he, w, hgg, Chart.dualMapR f, h, hw,
    (maps_iff w _ (fun _ => eSec x.P.A) _ rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).2 hm,
    appLE_eq_of_stalk _ x.th th (e' _ (𝟙 _)), fun a => ?_, ?_, fun i => huv _⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨l, hl⟩ := exists_chart Q.isLB y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨l, hl, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := e' _ (𝟙 _) y k l hk hl
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_keyPB_rescale {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : KeyIn R) (Q : Out.PolAV (Sp R'))
    (hg rig hr th hth v hv th' hth' v' hv') (H : KeyPB ⟨Q, hg, rig, hr, th, hth, v, hv⟩ x f) (a : R) (ha : IsUnit a)
    (M : Matrix (Fin Q.g) (Fin Q.g) R) (hM : IsUnit M.det)
    (hth'' : ∀ i, LB.Sec.f th' i = constFn Q.A.hom _ (f a) * LB.Sec.f th i)
    (hv'' : ∀ i, IsLieComb (fun k => f (M i k)) v (v' i)) :
    ∃ y : KeyIn R, KeyPB ⟨Q, hg, rig, hr, th', hth', v', hv'⟩ y f := by
  obtain ⟨φ, he, w, hgg, F, h, hw, hrr, hs, hF, hFe, hvv⟩ := H
  dsimp only at φ he w hgg h hw hrr hs hvv
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun a => by rw [hF]; ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by rw [hFe]; ext <;> simp [Chart.dualMapR])
  subst hF'
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hb⟩ := LieComb.lieComb_algebra R x.P.A x.P.g x.v x.basis.1
  have hc : ∀ {n : ℕ} (e : n = x.P.g) (t t' : Fin n → (epsR R' ⟶ Q.A)) (N : Matrix (Fin n) (Fin n) R), IsUnit N.det →
      (∀ i, (t i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (x.v (i.cast e)).left) →
      (∀ i, IsLieComb (fun k => f (N i k)) t (t' i)) →
      ∃ u : Fin x.P.g → (epsR R ⟶ x.P.A), IsLieBasis u ∧
        ∀ i, (t' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (u (i.cast e)).left := fun e t t' N hN ht ht' => by
    subst e
    choose u hu using fun i => (hex (N i)).exists
    exact ⟨u, (hb N u x.basis hu).2 hN,
      fun i => (lieComb_baseChange R R' f x.P.A Q.A φ h _ x.v (u i) (N i) t (t' i) ht (hu i)).2 (ht' i)⟩
  obtain ⟨u, hu, huv⟩ := hc hgg v v' M hM hvv hv''
  have e := (KeyCancel.appLE_eq_iff_stalk w x.th th).1 hs
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyNormalExists.constMul x.P.A.hom a x.th, fun s => ?_, u, hu⟩,
    φ, he, w, hgg, _, h, hw, hrr, appLE_eq_of_stalk _ _ th' fun y j k hj hk => ?_, hF, hFe, huv⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, KeyNormalExists.mem_nonzeroLocus_constMul _ ha _ hz'⟩
  · have a₁ := e _ (𝟙 _) y j k hj hk
    rw [Category.id_comp] at a₁ ⊢
    have a₃ := gs_of_id φ y hj ((sec_eq_iff x.P.A.hom (KeyNormalExists.constMul x.P.A.hom a x.th) x.th a).1
      (fun _ => rfl) j _ hj)
    rw [a₃, a₁, h.1.w, cst_comp, (sec_eq_iff _ _ _ _).1 hth'' k y hk, mul_left_comm]

theorem exists_isPullback_prod {S S₀ : Scheme.{0}} {g : S ⟶ S₀} {A : Over S} {A₀ : Over S₀} {π : A.left ⟶ A₀.left}
    (h : IsPullback π A.hom A₀.hom g) : ∃ π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left,
      IsPullback π₂ (A ⊗ A).hom (A₀ ⊗ A₀).hom g ∧ π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π ∧
        π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π := by
  have h₀ : IsPullback (snd A₀ A₀).left (fst A₀ A₀).left A₀.hom A₀.hom := (IsPullback.of_hasPullback A₀.hom A₀.hom).flip
  have h₁ : IsPullback (snd A A).left (fst A A).left A.hom A.hom := (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₂ := h₁.paste_horiz h
  rw [← h.w] at h₂
  have w : ((snd A A).left ≫ π) ≫ A₀.hom = ((fst A A).left ≫ π) ≫ A₀.hom := by
    rw [h₂.w, Category.assoc]
  have e₁ := h₀.lift_fst _ _ w
  have e₂ := h₀.lift_snd _ _ w
  refine ⟨h₀.lift _ _ w, ?_, e₂, e₁⟩
  rw [← e₁] at h₂
  have h₃ := (IsPullback.of_right h₂ e₂ h₀).paste_vert h
  rwa [Over.w, Over.w] at h₃

theorem exists_polAV_descent (hL : Out.Laws) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R]
    (P : Out.PolAV (Sp R)) : ∃ (R₁ : Subring R) (_ : IsLocalRing R₁) (_ : IsPrincipalIdealRing R₁) (P₁ : Out.PolAV (Sp R₁))
      (j : P.A.left ⟶ P₁.A.left), Countable R₁ ∧ IsGrpPullback P.A P₁.A (spMap R₁.subtype) j ∧
        LBIso P.L (P₁.L.pull j) ∧ P.g = P₁.g := by
  have := P.isAb.smooth
  obtain ⟨Hb, hH, m, s, hs⟩ := AbProj.isProjBy_of_isPullback P (IsPullback.id_horiz P.A.hom)
  obtain ⟨R₀, _, _, X₀, f₀, π, H₀, s₀, hc₀, -, -, -, hπ, hfl, hH₀, hs₀, -⟩ :=
    _root_.GlobalTheory.veryAmpleBy_descends_countable_subring R P.A.left P.A.hom Hb m s ∅ hH hs Set.countable_empty
  have hp₀ : AbLaw.IsProjBy f₀ := ⟨H₀, hH₀, m, s₀, hs₀⟩
  have hpr : IsProper f₀ := AbLaw.isProper_of_isProjBy R₀ X₀ f₀ hp₀
  have hfp : LocallyOfFinitePresentation f₀ := inferInstance
  let A₀ : Over (Sp R₀) := Over.mk f₀
  obtain ⟨π₂, hπ₂, a₁, a₂⟩ := exists_isPullback_prod (A := P.A) (A₀ := A₀) hπ
  have hpr₂ : IsProper (A₀ ⊗ A₀).hom := inferInstanceAs (IsProper (pullback.fst f₀ f₀ ≫ f₀))
  obtain ⟨Se, hSe⟩ := morphism_descends_to_subring R R₀ (Sp R) (Sp R₀) X₀ (𝟙 _) (𝟙 _) f₀ (spMap R₀.subtype)
    (η[P.A].left ≫ π) (IsPullback.id_vert _) (by
      have a : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
      rw [Category.assoc, hπ.w, ← Category.assoc, a]; simp)
  obtain ⟨Si, hSi⟩ := morphism_descends_to_subring R R₀ P.A.left X₀ X₀ P.A.hom f₀ f₀ π
    ((GrpObj.inv : P.A ⟶ P.A).left ≫ π) hπ (by rw [Category.assoc, hπ.w, ← Category.assoc, Over.w])
  obtain ⟨Sm, hSm⟩ := morphism_descends_to_subring R R₀ (P.A ⊗ P.A).left (A₀ ⊗ A₀).left X₀ (P.A ⊗ P.A).hom
    (A₀ ⊗ A₀).hom f₀ π₂ (μ[P.A].left ≫ π) hπ₂ (by rw [Category.assoc, hπ.w, ← Category.assoc, Over.w, hπ₂.w])
  obtain ⟨Sl, hSl⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R R₀ P.A.left X₀ P.A.hom f₀ π P.L hπ P.isLB
  obtain ⟨R₁, _, _, hc₁, hsub, -, hff⟩ := GlobalTheory.exists_countable_local_pid_subring R ((R₀ : Set R) ∪ ((Se : Set R) ∪ (Si ∪ (Sm ∪ Sl))))
    ((Set.countable_coe_iff.1 hc₀).union (Se.countable_toSet.union (Si.countable_toSet.union
      (Sm.countable_toSet.union Sl.countable_toSet))))
  simp only [Set.union_subset_iff] at hsub
  obtain ⟨h₀₁, be, bi, bm, bl⟩ := hsub
  have h01 : R₀ ≤ R₁ := h₀₁
  have hsp : spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h01) := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  obtain ⟨A₁, π₁, h₁⟩ : ∃ (A₁ : Over (Sp R₁)) (π₁ : A₁.left ⟶ X₀), IsPullback π₁ A₁.hom f₀ (spMap (Subring.inclusion h01)) :=
    ⟨Over.mk (pullback.snd _ _), pullback.fst _ _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨j, j₁, j₂⟩ : ∃ j : P.A.left ⟶ A₁.left, j ≫ π₁ = π ∧ j ≫ A₁.hom = P.A.hom ≫ spMap R₁.subtype :=
    ⟨h₁.lift π (P.A.hom ≫ spMap R₁.subtype) (by rw [hπ.w, Category.assoc, hsp]), h₁.lift_fst _ _ _, h₁.lift_snd _ _ _⟩
  have hj : IsPullback j P.A.hom A₁.hom (spMap R₁.subtype) := IsPullback.of_right (by rw [j₁, ← hsp]; exact hπ) j₂ h₁
  obtain ⟨ρ₂, hρ₂, b₁, b₂⟩ := exists_isPullback_prod (A := A₁) (A₀ := A₀) h₁
  obtain ⟨j', hj', c₁, c₂⟩ := exists_isPullback_prod hj
  have lft : ∀ (T : Over (Sp R)) (T₁ : Over (Sp R₁)) (k : T.left ⟶ T₁.left) (φ : T ⟶ P.A) (ψ : T₁.left ⟶ X₀),
      k ≫ T₁.hom = T.hom ≫ spMap R₁.subtype → k ≫ ψ = φ.left ≫ π →
      ψ ≫ f₀ = T₁.hom ≫ spMap (Subring.inclusion h01) → ∃ φ₁ : T₁ ⟶ A₁, φ.left ≫ j = k ≫ φ₁.left := by
    intro T T₁ k φ ψ hk e₁ e₂
    refine ⟨Over.homMk (h₁.lift ψ T₁.hom e₂) (h₁.lift_snd _ _ _), ?_⟩
    change _ = k ≫ h₁.lift ψ T₁.hom e₂
    apply h₁.hom_ext
    · rw [Category.assoc, j₁, Category.assoc, h₁.lift_fst, e₁]
    · rw [Category.assoc, j₂, Category.assoc, h₁.lift_snd, hk, ← Category.assoc, Over.w]
  obtain ⟨ψe, e₁, e₂⟩ := hSe R₁ h01 be (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h01)) (spMap R₁.subtype)
    (IsPullback.id_vert _) hsp.symm (by simp)
  obtain ⟨e, he⟩ := lft (𝟙_ _) (𝟙_ _) (spMap R₁.subtype) η[P.A] ψe (by simp) e₁ (by simpa using e₂)
  obtain ⟨ψi, i₁, i₂⟩ := hSi R₁ h01 bi A₁.left A₁.hom π₁ j h₁ j₁ j₂
  obtain ⟨i, hi⟩ := lft P.A A₁ j GrpObj.inv ψi j₂ i₁ (i₂.trans h₁.w)
  obtain ⟨ψm, m₁, m₂⟩ := hSm R₁ h01 bm (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom ρ₂ j' hρ₂ (by
    apply pullback.hom_ext
    · change (j' ≫ ρ₂) ≫ (fst A₀ A₀).left = π₂ ≫ (fst A₀ A₀).left
      rw [Category.assoc, b₁, ← Category.assoc, c₁, Category.assoc, j₁, a₁]
    · change (j' ≫ ρ₂) ≫ (snd A₀ A₀).left = π₂ ≫ (snd A₀ A₀).left
      rw [Category.assoc, b₂, ← Category.assoc, c₂, Category.assoc, j₁, a₂]) hj'.w
  obtain ⟨mu, hmu⟩ := lft (P.A ⊗ P.A) (A₁ ⊗ A₁) j' μ[P.A] ψm hj'.w m₁ (m₂.trans hρ₂.w)
  obtain ⟨L₁, hL₁, hiso⟩ := hSl R₁ h01 bl A₁.left A₁.hom π₁ j h₁ j₁ j₂
  have : Flat A₁.hom := MorphismProperty.of_isPullback (P := @Flat) h₁ hfl
  have : IsProper A₁.hom := MorphismProperty.of_isPullback (P := @IsProper) h₁ hpr
  obtain ⟨_, hG⟩ := GlobalTheory.GrpDescent.grpObj_descends_faithfullyFlat R₁ R P.A A₁ j e mu i j' hj c₁ c₂ he hmu hi
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆⟩ := GlobalTheory.PolFlatDescent.polarisation_of_faithfullyFlat hL R₁ R P A₁ L₁ j
    (AbLaw.isProjBy_baseChange R₀ R₁ _ X₀ A₁.left f₀ π₁ A₁.hom h₁ hp₀) hL₁ hG hiso
  exact ⟨R₁, inferInstance, inferInstance, { A := A₁, isAb := p₁, g := P.g, smoothDim := p₂, L := L₁, isLB := hL₁, rigid := p₃, sym := p₄, ample := p₅, ktriv := p₆ }, j, hc₁, hG, hiso, rfl⟩

theorem exists_keyIn_descent (hL : Out.Laws) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R]
    (x : KeyIn R) (s : Set R) (hs : s.Countable) : ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀)
      (x₀ : KeyIn R₀), Countable R₀ ∧ s ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ KeyPB x x₀ R₀.subtype := by
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  obtain ⟨R₁, _, _, P₁, j, hc₁, hG, hiso, hgg⟩ := exists_polAV_descent hL R P
  obtain ⟨x₁, rfl⟩ := (GlobalTheory.KeyOnPol.main hL R₁).1 P₁ (hgg ▸ hg)
  obtain ⟨rig₁, hr₁, th₁, hth₁, v₁, hv₁, H₁⟩ := exists_keyPB_on R₁.subtype x₁ P j hG hiso hgg hg
  obtain ⟨a, t, ht, hat, H₂⟩ := (GlobalTheory.KeyOnPol.main hL R).2 ⟨P, hg, rig₁, hr₁, th₁, hth₁, v₁, hv₁⟩ rig hr th hth v hv
  have := P.isAb.comm
  choose M hM using fun i => (hv₁.2 (v i) (hv.1 i)).exists
  have hdet : IsUnit (Matrix.of M).det := ((LieComb.lieComb_algebra R P.A P.g v₁ hv₁.1).2.2.2.2 M v hv₁ hM).1 hv
  obtain ⟨R₂, _, _, hc₂, hsub, hloc, -⟩ := GlobalTheory.exists_countable_local_pid_subring R
    ((R₁ : Set R) ∪ (s ∪ ({(a : R)} ∪ Set.range fun p : Fin P.g × Fin P.g => M p.1 p.2)))
    ((Set.countable_coe_iff.1 hc₁).union (hs.union ((Set.countable_singleton _).union (Set.countable_range _))))
  simp only [Set.union_subset_iff, Set.singleton_subset_iff, Set.range_subset_iff] at hsub
  obtain ⟨h₁₂, bs, ba, bM⟩ := hsub
  have h12 : R₁ ≤ R₂ := h₁₂
  obtain ⟨x₂, H₃⟩ := exists_keyPB_ring x₁ (Subring.inclusion h12)
  have e₁₂ : R₂.subtype.comp (Subring.inclusion h12) = R₁.subtype := RingHom.ext fun _ => rfl
  have H₄ := KeyCancel.keyPB_cancel _ _ _ x₁ x₂ _ (Subring.inclusion h12) R₂.subtype H₃ (by rw [e₁₂]; exact H₁)
  let N : Matrix (Fin P.g) (Fin P.g) R₂ := fun i k => ⟨M i k, bM (i, k)⟩
  have hN : IsUnit N.det := isUnit_of_map_unit R₂.subtype _ (by rw [RingHom.map_det]; exact hdet)
  obtain ⟨y, H₅⟩ := exists_keyPB_rescale R₂.subtype x₂ P hg rig₁ hr₁ th₁ hth₁ v₁ hv₁ t ht v hv H₄ ⟨a, ba⟩
    (isUnit_of_map_unit R₂.subtype _ a.isUnit) N hN hat hM
  have H₆ := keyPB_trans _ _ _ y _ _ _ _ H₅ H₂
  rw [RingHom.id_comp] at H₆
  exact ⟨R₂, inferInstance, inferInstance, y, hc₂, bs, hloc, H₆⟩

theorem keyIn_descends_countable : Out.Laws → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] [CharZero R] (x : KeyIn R) (s : Set R), s.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (x₀ : KeyIn R₀), Countable R₀ ∧ s ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ KeyPB x x₀ R₀.subtype) ∧ KeyDesc := by
  refine fun hL => ⟨fun R _ _ _ _ _ x s hs => exists_keyIn_descent hL R x s hs, fun K _ _ x => ?_⟩
  obtain ⟨R₀, _, _, x₀, hc, -, hloc, H⟩ := exists_keyIn_descent hL K x ∅ Set.countable_empty
  let K₀ : Subfield K :=
    { R₀ with
      inv_mem' := fun z hz => by
        by_cases h0 : z = 0
        · rw [h0, inv_zero]; exact R₀.zero_mem
        · obtain ⟨b, hb⟩ := (isUnit_of_map_unit R₀.subtype ⟨z, hz⟩ (IsUnit.mk0 z h0)).exists_right_inv
          have e : z * (b : K) = 1 := congrArg Subtype.val hb
          rw [← eq_inv_of_mul_eq_one_right e]; exact b.2 }
  exact ⟨K₀, x₀, hc, H⟩

end GlobalTheory.KeyCountableDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDatumConnectedFamilyOfPolarizedArithmeticFami
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.Frames

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem spMap_comp (f : R →+* R') (f' : R' →+* R'') : spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem polPB_comp {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')} {f : R →+* R'}
    {f' : R' →+* R''} {g : R →+* R''} (e : f'.comp f = g) (h' : ∃ φ', PolPB P'' P' (spMap f') φ')
    (h : ∃ φ, PolPB P' P (spMap f) φ) : ∃ ψ, PolPB P'' P (spMap g) ψ := by
  obtain ⟨φ', hc', hg', w', hw'⟩ := h'
  obtain ⟨φ, hc, hg, w, hw⟩ := h
  subst e
  obtain ⟨w'', T⟩ := exists_comp P'.isLB w w' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw') P.isLB P''.isLB
  exact ⟨φ' ≫ φ, (hc'.comp hc).congr (spMap_comp f f').symm rfl, hg'.trans hg, w'',
    (isGen_iff w'').2 (T.pgen_comp P'.isLB ((isGen_iff w).1 hw) ((isGen_iff w').1 hw'))⟩

theorem polPB_cancel {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')} {f : R →+* R'}
    {f' : R' →+* R''} {g : R →+* R''} (e : f'.comp f = g) (h : ∃ φ, PolPB P' P (spMap f) φ)
    (h'' : ∃ ψ, PolPB P'' P (spMap g) ψ) : ∃ φ', PolPB P'' P' (spMap f') φ' := by
  obtain ⟨φ'', hc'', hg'', w'', hw''⟩ := h''
  obtain ⟨φ, hc, hg, w, hw⟩ := h
  subst e
  have hsp := spMap_comp f f'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : P''.A.left ⟶ P'.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ P'.A.hom = P''.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (P''.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' g g'' P'.isLB P''.isLB
  exact ⟨φ', hc.cancel (hc''.congr hsp rfl) hw0, hg''.trans hg.symm, w',
    (isGen_iff w').2 (T.pgen_cancel P.isLB g g'')⟩

theorem polPB_exists (hB : Out.PolBaseChangeSt) (P : Out.PolAV (Sp R)) (f : R →+* R') :
    ∃ (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), PolPB P' P (spMap f) φ := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB _ _ (spMap f) P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, hg, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem polPB_of_keyPB {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} (h : KeyPB x' x f) :
    ∃ φ, PolPB x'.P x.P (spMap f) φ :=
  let ⟨φ, _, w, hg, _, hc, hw, _⟩ := h
  ⟨φ, hc, hg, w, hw⟩

theorem exists_points (K K' R : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [CommRing R] [Algebra K R] (s : R →+* ℂ) (s₀ : R →ₐ[K] K) :
    ∃ (i : R →+* K' ⊗[K] R) (s' : K' ⊗[K] R →+* ℂ) (s₀' : K' ⊗[K] R →ₐ[K'] K'),
      s'.comp i = s ∧ s₀'.toRingHom.comp i = (algebraMap K K').comp s₀.toRingHom := by
  letI : Algebra K ℂ := (s.comp (algebraMap K R)).toAlgebra
  haveI : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let e : K' →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let sA : R →ₐ[K] ℂ := { s with commutes' := fun _ => rfl }
  refine ⟨Algebra.TensorProduct.includeRight.toRingHom,
    (Algebra.TensorProduct.lift e sA fun _ _ => Commute.all _ _).toRingHom,
    Algebra.TensorProduct.lift (AlgHom.id K' K') ((Algebra.ofId K K').comp s₀) fun _ _ => Commute.all _ _,
    RingHom.ext fun r => ?_, RingHom.ext fun r => ?_⟩
  · simp [sA]
  · simp

end GlobalTheory.KeyFam.Frames

namespace GlobalTheory.KeyFam
open Frames

theorem connFam_of_polFam : Out.Laws → Out.Laws2 → PolFam → GlobalTheory.KeyKa.ConnFam := by
  intro hL hL2 hF x
  obtain ⟨K, _, _, R, _, _, Q, s, s₀, φ, hG, hP, hK⟩ := hF x.P x.g_pos
  obtain ⟨P₀, φ₀, hP₀⟩ := polPB_exists hL.polBaseChange Q s₀.toRingHom
  obtain ⟨K', _, _, j, hKn⟩ := hK P₀ φ₀ hP₀
  letI : Algebra K K' := j.toAlgebra
  obtain ⟨i, s', s₀', hs', hs₀'⟩ := exists_points K K' R s s₀
  obtain ⟨Q', ψ, hQ'⟩ := polPB_exists hL.polBaseChange Q i
  have hG' : GeomInt K' (K' ⊗[K] R) := (_root_.GlobalTheory.KeyFam.geomInt_baseChange_and_away K K' R hG).1
  haveI := hG'.1
  haveI : IsNoetherianRing (K' ⊗[K] R) := Algebra.FiniteType.isNoetherianRing K' _
  obtain ⟨r, hr, hr₀, y, χ, hy⟩ := _root_.GlobalTheory.KeyFam.exists_keyIn_near_two hL hL2 (K' ⊗[K] R) Q' ⟨RingHom.ker s', RingHom.ker_isPrime _⟩
    ⟨RingHom.ker s₀'.toRingHom, RingHom.ker_isPrime _⟩ (by rw [hQ'.2.1, ← hP.2.1]; exact x.g_pos)
  have hu : IsUnit (s' r) := isUnit_iff_ne_zero.2 hr
  have hu₀ : IsUnit (s₀'.toRingHom r) := isUnit_iff_ne_zero.2 hr₀
  have hS : GeomInt K' (Localization.Away r) :=
    (_root_.GlobalTheory.KeyFam.geomInt_baseChange_and_away K' K' _ hG').2 r fun h => hr (h ▸ Ideal.zero_mem _)
  let t : Localization.Away r →+* ℂ := IsLocalization.Away.lift r hu
  have ht : t.comp (algebraMap _ _) = s' := IsLocalization.Away.lift_comp r hu
  let u : Localization.Away r →+* K' := IsLocalization.Away.lift r hu₀
  have hu' : u.comp (algebraMap _ _) = s₀'.toRingHom := IsLocalization.Away.lift_comp r hu₀
  let t₀ : Localization.Away r →ₐ[K'] K' :=
    { u with
      commutes' := fun a => by
        rw [IsScalarTower.algebraMap_apply K' (K' ⊗[K] R) (Localization.Away r)]
        exact (RingHom.congr_fun hu' _).trans (s₀'.commutes a) }
  have hyQ := polPB_comp rfl ⟨χ, hy⟩ ⟨ψ, hQ'⟩
  obtain ⟨φ₁, hφ₁⟩ := polPB_cancel (f' := t) (by rw [← RingHom.comp_assoc, ht, hs']) hyQ ⟨φ, hP⟩
  obtain ⟨S', _, _, j', y', v, v₀, ψ', hS', hx, hy', hv₀⟩ := _root_.GlobalTheory.KeyFam.exists_univ_frames hL K' _ y x t φ₁ t₀ hS hφ₁
  obtain ⟨y₀, hy₀⟩ := exists_keyPB_ring y' v₀.toRingHom
  have e₁ : v₀.toRingHom.comp j'.toRingHom = u := congrArg AlgHom.toRingHom hv₀
  have h₁ := polPB_comp e₁ (polPB_of_keyPB hy₀) ⟨ψ', hy'⟩
  have h₂ := polPB_comp (g := ((RingHom.id K').comp j).comp s₀.toRingHom)
    (by rw [← RingHom.comp_assoc, hu', hs₀']; rfl) h₁ hyQ
  obtain ⟨φ₂, hφ₂⟩ := polPB_cancel rfl ⟨φ₀, hP₀⟩ h₂
  obtain ⟨c, hc⟩ := hKn K' (RingHom.id K') y₀ φ₂ hφ₂
  exact ⟨K', _, ‹_›, S', _, _, y', v, v₀, c, hS'.1, hS'.2, hx, fun e x₀ h =>
    hc e x₀ (KeyCancel.keyPB_cancel _ _ _ y' y₀ x₀ _ _ hy₀ h)⟩

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.RootConst

open GlobalTheory.AffinePoints

theorem preconnectedSpace_algHom (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra.FiniteType ℂ S] : PreconnectedSpace (S →ₐ[ℂ] ℂ) := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) S 1 one_ne_zero
  refine ⟨(isEmbedding_coe (R := ℂ) (A := S) (C := ℂ)).isInducing.isPreconnected_image.1 ?_⟩
  convert hc.isPreconnected using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨_, rfl, by simp⟩
  · rintro ⟨φ, rfl, -⟩
    exact ⟨φ, trivial, rfl⟩

theorem exists_chart (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.Smooth ℂ S] (p : S →ₐ[ℂ] ℂ) :
    ∃ (d : ℕ) (e : OpenPartialHomeomorph (S →ₐ[ℂ] ℂ) (Fin d → ℂ)),
      IsAlgebraicChart e ∧ p ∈ e.source := by
  have := RingHom.ker_isPrime p
  obtain ⟨s, hs, J, K, _, _, ⟨Q⟩⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℂ (RingHom.ker p)
  have H : Algebra.IsStandardSmoothOfRelativeDimension Q.dimension ℂ (Localization.Away s) :=
    Q.isStandardSmoothOfRelativeDimension rfl
  exact ⟨Q.dimension, exists_isAlgebraicChart_of_away s (Localization.Away s) p hs⟩

theorem continuous_of_holomorphic_families (S : Type) [CommRing S] [Algebra ℂ S]
    [Algebra.Smooth ℂ S] (t : (S →ₐ[ℂ] ℂ) → ℂ)
    (h : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)), IsOpen B →
      (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → ContinuousOn (fun p => t (s p)) B) :
    Continuous t := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨d, e, he, hp⟩ := exists_chart S p
  have h1 := h d e.target e.symm e.open_target fun a => (he.analyticOnNhd a).differentiableOn
  have h2 : ContinuousOn t e.source :=
    (h1.comp e.continuousOn e.mapsTo).congr fun q hq => by
      simp only [Function.comp_apply, e.left_inv hq]
  exact h2.continuousAt (e.open_source.mem_nhds hp)

theorem eq_of_pow_eq_one {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {u : X → ℂ}
    (hu : Continuous u) {N : ℕ} (hN : 1 ≤ N) (h : ∀ x, u x ^ N = 1) (x y : X) : u x = u y := by
  have hfin : {z : ℂ | z ^ N = 1}.Finite := by
    refine (Polynomial.nthRootsFinset N (1 : ℂ)).finite_toSet.subset fun z hz => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset hN 1).2 hz)
  exact isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete hu.continuousOn
    (fun z _ => h z) trivial trivial

theorem value_eq_unit_of_pow_eq : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S] (y : KeyIn S) (N : ℕ) (r : Sˣ) (t : (S →ₐ[ℂ] ℂ) → ℂ) (s₀ : S →ₐ[ℂ] ℂ), 1 ≤ N → (∀ s, ∃ x : KeyIn ℂ, KeyPB x y s.toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t s = M.det ^ 4 / c ^ 8)) → (∀ s, t s ^ N = s r ^ N) → t s₀ = s₀ r → ∀ s, t s = s r := by
  intro hL hT hI S _ _ _ _ y N r t s₀ hN hx hpow h0 s
  have := preconnectedSpace_algHom S
  have ht : Continuous t := continuous_of_holomorphic_families S t fun m B σ hB hσ =>
    _root_.GlobalTheory.ThetaValueCont.continuousOn_value hL hT hI S y m B σ (fun p => t (σ p)) hB hσ fun p _ => hx (σ p)
  have hr : ∀ q : S →ₐ[ℂ] ℂ, q r ≠ 0 := fun q => (r.isUnit.map q).ne_zero
  have hu : Continuous fun q : S →ₐ[ℂ] ℂ => t q / q r := ht.div (continuous_eval _) hr
  have h1 := eq_of_pow_eq_one hu hN
    (fun q => by rw [div_pow, hpow, div_self (pow_ne_zero N (hr q))]) s s₀
  rw [h0, div_self (hr s₀)] at h1
  exact (div_eq_one_iff_eq (hr s)).1 h1

end GlobalTheory.RootConst
end

