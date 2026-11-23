module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0457
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RingCont

abbrev MC (R : Type) [CommRing R] (F : Shv R) : CommRingCat.{0} ⥤ AbCx := Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F

theorem locVan (R : Type) [CommRing R] (F : Shv R) : ∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : ((MC R F).obj A).X n),
    ((MC R F).obj A).d n (n + 1) z = 0 →
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : ((MC R F).obj B).X (n - 1),
      ((MC R F).obj B).d (n - 1) n y = ((MC R F).map g).f n z := by
  intro n hn A z hz
  obtain ⟨_, cl, -, -, hcl0, hpull⟩ := _root_.GlobalTheory.EtC.HCElements.main R F
  obtain ⟨Y, f, hfe, hfs, hx⟩ := _root_.GlobalTheory.EtC.classes_die_on_etale_cover R (Spec A) F n hn (cl (sch.obj (Spec A)) n z hz)
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection A Y f hfe hfs
  refine ⟨B, g, hg, ?_⟩
  obtain ⟨h', hh'⟩ := hpull (sch.obj (Spec B)) (sch.obj (Spec A)) (sch.map (Spec.map g)) n z hz
  have h0 : pull R (sch.map (Spec.map g)) F n (cl (sch.obj (Spec A)) n z hz) = 0 := by
    rw [← hhf, Functor.map_comp, pull_comp, hx, map_zero]
  rw [hh', hcl0] at h0
  obtain ⟨y, hy⟩ := h0
  exact ⟨y, hy.symm⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.EtC.HCZero.main R F
  have hF0 : PreservesFilteredColimitsOfSize.{0, 0} (onRings F ⋙ forget₂ _ AddCommGrpCat.{1}) :=
    ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).1.1 hF)
  exact GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent (MC R F) (onRings F ⋙ forget₂ _ AddCommGrpCat.{1})
    (Functor.whiskerLeft Scheme.Spec.rightOp ι) hF0
    (fun A => hι (op (Spec A)))
    (fun n hn A => (_root_.GlobalTheory.EtC.HCElements.main R F).1 _ n hn)
    (locVan R F)
    (fun A B g hg n => GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F CommRingCat.{0} (Scheme.Spec.rightOp ⋙ sch.op) A _ (coAug g)
      (GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat R A B g hg) n)
    J D c hc n

end GlobalTheory.EtC.RingCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheaf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem heightFunctionalStatement_of_pairingProperties (hA5 : A5)
    (hsect : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
      Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _) : B2 := by
  intro R _ A _ hA F n hn
  have key : ∀ x : H R (sp A) F n, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hA5 R (Spec (CommRingCat.of A)) F n hn x
    obtain ⟨s, hsf⟩ := hsect A hA Y f hf hs
    calc x = pull R (𝟙 (sp A)) F n x := (pull_id R _ F n x).symm
      _ = pull R (sch.map (s ≫ f)) F n x := by rw [hsf, CategoryTheory.Functor.map_id]
      _ = pull R (sch.map s) F n (pull R (sch.map f) F n x) := by
          rw [CategoryTheory.Functor.map_comp, pull_comp]
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem b2 : B2 := heightFunctionalStatement_of_pairingProperties _root_.GlobalTheory.EtC.classes_die_on_etale_cover _root_.GlobalTheory.EtC.etale_surjective_section_of_SH

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_fin_span_of_cover {X : Scheme.{0}} (T : X.affineOpens) (B : Set Γ(X, T.1))
    (hB : ∀ x ∈ T.1, ∃ f ∈ B, x ∈ X.basicOpen f) :
    ∃ (n : ℕ) (b : Fin n → Γ(X, T.1)), Ideal.span (Set.range b) = ⊤ ∧ ∀ i, b i ∈ B := by
  have hsp : Ideal.span B = ⊤ := by
    rw [← T.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hf, hxf⟩ := hB x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hsp
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, fun i ↦ hFB (F.equivFin.symm i).2⟩
  rw [eq_top_iff, ← hF]
  exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩

theorem le_basicOpen_of_isUnit_mp {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    {T S : AffOp X} (u : T ⟶ S) (f : (OAff s).obj T) (hu : IsUnit (mp (OAff s) u f)) :
    S.unop.1 ≤ X.basicOpen (show Γ(X, T.unop.1) from f) := by
  change IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op
    (show Γ(X, T.unop.1) from f)) at hu
  have h1 := Scheme.basicOpen_of_isUnit X hu
  rw [Scheme.basicOpen_res] at h1
  rw [← h1]; exact inf_le_right

theorem cohO_basis_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (P : Type) [Preorder P] (G : P → X.affineOpens) (hG : Monotone G), (∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ a, x ∈ (G a).1 ∧ (G a).1 ≤ U.1) → (∀ (a b : P) (x : X), x ∈ (G a).1 → x ∈ (G b).1 → ∃ c, c ≤ a ∧ c ≤ b ∧ x ∈ (G c).1) → Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull2 ∧ (CohomZeroIsConstants (OAff s) → CohomZeroIsConstants (hG.functor.op ⋙ OAff s)) := by
  intro R _ X s P _ G hG h1 h2
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : Pᵒᵖ) (v : T ⟶ hG.functor.op.obj t) (w : hG.functor.op.obj t ⟶ S), v ≫ w = u := by
    intro T
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover T.unop
      {f | ∃ a, X.basicOpen f ≤ (G a).1 ∧ (G a).1 ≤ T.unop.1} (fun x hx ↦ by
        obtain ⟨a, hxa, haT⟩ := h1 T.unop x hx
        obtain ⟨f, hf, hxf⟩ := T.unop.2.exists_basicOpen_le (V := (G a).1) ⟨x, hxa⟩ hx
        exact ⟨f, ⟨a, hf, haT⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S u hu ↦ ?_⟩
    obtain ⟨a, hfa, haT⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op a, (homOfLE (show G a ≤ T.unop from haT)).op,
      (homOfLE (show S.unop ≤ G a from hS.trans hfa)).op, Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩
  have hdir : ∀ (t₁ t₂ : Pᵒᵖ) (S : AffOp X), (hG.functor.op.obj t₁ ⟶ S) → (hG.functor.op.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (hG.functor.op.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS₁ : S.unop.1 ≤ (G t₁.unop).1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G t₂.unop).1 := leOfHom a₂.unop
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover S.unop
      {f | ∃ c, c ≤ t₁.unop ∧ c ≤ t₂.unop ∧ X.basicOpen f ≤ (G c).1} (fun x hx ↦ by
        obtain ⟨c, hc₁, hc₂, hxc⟩ := h2 t₁.unop t₂.unop x (hS₁ hx) (hS₂ hx)
        obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := (G c).1) ⟨x, hxc⟩ hx
        exact ⟨f, ⟨c, hc₁, hc₂, hf⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S' u hu ↦ ?_⟩
    obtain ⟨c, hc₁, hc₂, hfc⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op c, ⟨(homOfLE hc₁).op⟩, ⟨(homOfLE hc₂).op⟩,
      ⟨(homOfLE (show S'.unop ≤ G c from hS.trans hfc)).op⟩⟩
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) hG.functor.op H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv2 := _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt (OAff s) hG.functor.op H hcov hdir
  refine ⟨⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩,
    ⟨_root_.GlobalTheory.CatCoh.pull2_restrict_injective_of_comma _ _ hs hg hv, _root_.GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma _ _ hs hg hv hv2⟩, ?_⟩
  intro h0 g hg0
  have hcomp : ∀ ⦃t t' : Pᵒᵖ⦄ (a : t ⟶ t'), g t' = mp (OAff s) (hG.functor.op.map a) (g t) := by
    intro t t' a
    have e : d0 (hG.functor.op ⋙ OAff s) g t t' a = 0 := by rw [hg0]; rfl
    rw [amitsur_d0_apply] at e
    exact sub_eq_zero.1 e
  obtain ⟨g1, hg1c, hg1e⟩ := _root_.GlobalTheory.compat_family_extend (OAff s) hG.functor.op hs hg g hcomp
  have hd : d0 (OAff s) g1 = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply, hg1c φ, sub_self]
    rfl
  obtain ⟨r, hr, huniq⟩ := h0 g1 hd
  refine ⟨r, fun t ↦ ?_, fun r' hr' ↦ huniq r' fun T ↦ ?_⟩
  · rw [← hg1e t]; exact hr _
  · refine sub_eq_zero.1 (hs T _ fun t u ↦ ?_)
    rw [map_sub, ← hg1c u, hg1e t, hr' t, AlgHom.commutes]
    exact sub_self _

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNumBlockSetsMulGammaTwoSidedBounds
section
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem numBlockSetsOfTotalSize_zero {r : ℕ} (b : Fin r → ℕ) : splitDoublingNBlock b 0 = 1 := by
  unfold splitDoublingNBlock
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext J
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (h1 hx)
    have : i ∈ Finset.univ.filter fun i => b i ∈ J := by simp [hx]
    rw [h2] at this
    simp at this
  · rintro rfl
    simp

theorem numBlockSetsOfTotalSize_le_choose {r : ℕ} (b : Fin r → ℕ) (j : ℕ) : splitDoublingNBlock b j ≤ r.choose j := by
  unfold splitDoublingNBlock
  have h : r.choose j = (Finset.powersetCard j (Finset.univ : Finset (Fin r))).card := by simp
  rw [h]
  refine Finset.card_le_card_of_injOn (fun J => Finset.univ.filter fun i => b i ∈ J) ?_ ?_
  · intro J hJ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hJ
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hJ.2⟩
  · intro J hJ K hK hJK
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hJ hK
    have key : ∀ i, b i ∈ J ↔ b i ∈ K := fun i => by
      have := Finset.ext_iff.1 hJK i
      simpa using this
    ext x
    constructor
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hJ.1 hx)
      exact (key i).1 hx
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hK.1 hx)
      exact (key i).2 hx

theorem gam_le_pow (q l : ℕ) : gam q l ≤ q ^ l := by
  unfold gam
  split_ifs with h
  · simp [h]
  · exact Nat.sub_le _ _

theorem gam_cast {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) :
    (gam q k : ℝ) = (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold gam
  rw [if_neg (by omega), Nat.add_sub_cancel, Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  field_simp
  ring

theorem one_add_pow_le_two_mul {x : ℝ} (hx : 0 ≤ x) {r : ℕ} (h : (r : ℝ) * x ≤ 1) :
    (1 + x) ^ r ≤ 1 + 2 * (r * x) := by
  have h0 : 0 ≤ (r : ℝ) * x := by positivity
  have h1 : (1 + x) ^ r ≤ Real.exp x ^ r :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) r
  rw [← Real.exp_nat_mul] at h1
  have h2 := Real.abs_exp_sub_one_le (x := r * x) (by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg h0] at h2
  linarith [(abs_le.1 h2).2]

theorem sum_choose_mul_pow_le {x : ℝ} (hx : 0 ≤ x) (r k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j ≤ (1 + x) ^ r := by
  have h1 : ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j
      ≤ ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun _ _ _ => by positivity)
  have h2 : ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * x ^ j
      = ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (by simpa using hj)]
    simp
  rw [add_comm 1 x, add_pow]
  refine h1.trans (le_of_eq ?_)
  rw [← h2]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

theorem sum_numBlockSets_mul_gamma_two_sided_bounds : ∀ (r k q : ℕ) (b : Fin r → ℕ), 1 ≤ k → 1 ≤ r → r ≤ q → 2 ≤ q → (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) ≤ ((∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam q (k - j) : ℕ) : ℝ) ∧ ((∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam q (k - j) : ℕ) : ℝ) ≤ (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ)) := by
  intro r k q b hk hr hrq hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hg := gam_cast (q := q) (k := k) (by omega) hk
  rw [Finset.sum_range_succ', numBlockSetsOfTotalSize_zero, one_mul, Nat.sub_zero]
  push_cast
  rw [hg]
  constructor
  · have : 0 ≤ ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith
  · have hx : (0 : ℝ) ≤ 1 / q := by positivity
    have h1 := sum_choose_mul_pow_le hx r k
    have h2 := one_add_pow_le_two_mul hx (r := r) (by
      rw [mul_one_div, div_le_one hq0]; exact_mod_cast hrq)
    rw [Finset.sum_range_succ'] at h1
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h1
    have h3 : ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ)
        ≤ (q : ℝ) ^ k * ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j + 1 ≤ k := by simpa using hj
      have e : (q : ℝ) ^ k * ((r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1))
          = (r.choose (j + 1) : ℝ) * (q : ℝ) ^ (k - (j + 1)) := by
        conv_lhs => rw [← Nat.sub_add_cancel hj', pow_add]
        rw [one_div_pow]
        field_simp
      rw [e]
      exact_mod_cast Nat.mul_le_mul (numBlockSetsOfTotalSize_le_choose b _) (gam_le_pow _ _)
    have h4 : ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1)
        ≤ 2 * (r * (1 / (q : ℝ))) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (pow_nonneg hq0.le k)
    have e : (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ))
        = (q : ℝ) ^ k * (2 * (r * (1 / (q : ℝ)))) + (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) := by ring
    rw [e]
    linarith

end GlobalTheory.FinGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem mem_map_of_smul_eq_zero_of_flat {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) (hb : t • b = 0) :
    b ∈ J.map (algebraMap R S) := by
  let f : J →ₗ[R] R := J.subtype
  let g : R →ₗ[R] R := LinearMap.mulLeft R t
  have ex : Function.Exact f g := by
    intro y
    change t * y = 0 ↔ y ∈ Set.range f
    rw [_root_.mul_comm, ← hJ]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.2⟩
  have ex' := Module.Flat.lTensor_exact S ex
  have h0 : g.lTensor S (b ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    change b ⊗ₜ[R] (t * 1) = 0
    rw [_root_.mul_one, ← _root_.mul_one t, ← smul_eq_mul, ← TensorProduct.smul_tmul, hb,
      TensorProduct.zero_tmul]
  obtain ⟨y, hy⟩ := (ex' _).1 h0
  have key : ∀ y : S ⊗[R] J, TensorProduct.rid R S (f.lTensor S y) ∈ J.map (algebraMap R S) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s j =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ j.2)
    | add x z hx hz => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hz
  have := key y
  rwa [hy, TensorProduct.rid_tmul, _root_.one_smul] at this

theorem mem_map_ann_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) :
    b ∈ J.map (algebraMap R S) ↔ t • b = 0 := by
  refine ⟨fun hb ↦ ?_, mem_map_of_smul_eq_zero_of_flat t J hJ b⟩
  rw [Algebra.smul_def]
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_mul, _root_.mul_comm, (hJ a).1 ha, map_zero]
  | zero => exact MulZeroClass.mul_zero _
  | add x y _ _ hx hy => rw [_root_.mul_add, hx, hy, _root_.add_zero]
  | smul a x _ hx => rw [smul_eq_mul, _root_.mul_left_comm, hx, MulZeroClass.mul_zero]

theorem mem_map_span_singleton_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R) (b : S) :
    b ∈ (Ideal.span {t}).map (algebraMap R S) ↔ ∃ c : S, b = t • c := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by rw [Algebra.smul_def, _root_.mul_comm]⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, by rw [Algebra.smul_def, _root_.mul_comm]⟩

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem preα_surjective_and_ker : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ _ _ hE hF U
  obtain ⟨hσ, hk, hσ₀, hk₀⟩ := hE
  have A := secPull_surjective_and_ker R R' (Ideal.span {t}) σ hσ hk X' X s' s φ h (prePair φ U.unop) rfl
  have B := secPull_surjective_and_ker R R₀ (RingHom.ker σ₀) σ₀ hσ₀ rfl X₀ X s₀ s φ₀ h₀
    (prePair φ₀ U.unop) rfl
  haveI : Flat s := hF
  have hfl : (algebraMap R (Sec s U.unop.1)).Flat := by
    change ((s.appLE ⊤ U.unop.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
      (Flat.flat_appLE s (isAffineOpen_top _) U.unop.2 le_top)
  haveI : Module.Flat R (Sec s U.unop.1) := hfl
  exact ⟨A.1, fun b ↦ (A.2 b).trans (mem_map_span_singleton_iff t b), B.1,
    fun b ↦ (B.2 b).trans (mem_map_ann_iff t _ (fun a ↦ RingHom.mem_ker.trans (hk₀ a)) b)⟩

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePullHO2OfPullHO1
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pullHO2_surjective_of_wedge : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ),
    Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by
  first
  | exact @_root_.GlobalTheory.PullbackCupProduct.main
  | exact _root_.GlobalTheory.PullbackCupProduct.main
  | (apply _root_.GlobalTheory.PullbackCupProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PullbackCupProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PullbackCupProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PullbackCupProduct.main ..)

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLocalizationEtaleNbhdEqUnitMulPow
section
namespace GlobalTheory.EtC

theorem kummer_divisor_step : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro q k B _ _ _ _ _ _ hq f hf A₂ _ _ hA c
  obtain ⟨b₁, m, e, he, hc⟩ := GlobalTheory.T.exists_unit_form_localization_etale_nbhd B A₂ f hA c
  by_cases hb : b₁ = 0
  · refine ⟨1, isCoprime_one_right, 1, ?_, ⟨B, inferInstance, inferInstance, isExcisionNbhd_self B 1, 1, by simp⟩⟩
    have hL := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA e 1 (by simpa using he)
    refine ⟨Localization.Away e, inferInstance, inferInstance, inferInstance, inferInstance, hL, by simp, 1, ?_⟩
    intro φ ψ hφ hψ
    subst hb
    have hc' := congrArg φ hc
    simp only [map_zero, map_mul, map_pow] at hc'
    have hx : IsUnit (φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) e) *
        φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f)) ^ m) := by
      have h1 : ∀ y : A₂, φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) y) =
          algebraMap (Localization.Away e) _ (algebraMap A₂ (Localization.Away e) y) := fun y => by
        rw [← RingHom.comp_apply, hφ]; rfl
      rw [h1, h1]
      refine IsUnit.mul ((IsLocalization.Away.algebraMap_isUnit e).map _) (IsUnit.pow _ ?_)
      rw [← IsScalarTower.algebraMap_apply]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (Localization.Away e) f)) (algebraMap B (Localization.Away e) f)
    have hu := (c.isUnit.map φ).mul hx
    rw [← hc'] at hu
    haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
    exact Subsingleton.elim _ _
  · obtain ⟨g, hg0, hfg, u, n, d, t, n', d', hn, hd, hn', hd', h1, h2⟩ := GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition k B q hq f hf b₁ hb m
    exact ⟨g, hfg, u, GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus k B q hq f hf A₂ hA c b₁ m e he hc g hfg u n d hn hd h1,
      GlobalTheory.T.coprime_unit_etale_extension k B q hq f g hg0 u t n' d' hn' hd' h2⟩

end GlobalTheory.EtC
end

