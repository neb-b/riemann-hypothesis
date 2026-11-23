module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyVectorBundleRank
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle

theorem exists_base {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (B : Type) [CommRing B] [Algebra R B] :
    ∃ (A' : Over (Sp B)) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R B)) := by
  have h := isGrpPullback_pullback A (spMap (algebraMap R B))
  obtain ⟨h1, h2⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ _ _ _ g h hA hg
  exact ⟨_, inferInstance, _, h1, h2, h.1⟩

theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

theorem vb_of_bijective' {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F') n) : VB R (H1 F) n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, fun p => ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

theorem finrank_of_vb {k M : Type} [Field k] [AddCommGroup M] [Module k M] {n : ℕ} (h : VB k M n) :
    Module.finrank k M = n := by
  obtain ⟨hf, -, hr⟩ := h
  have e := hr ⊥
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem first_cohomology_vector_bundle_rank : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureFieldDim → SmallLiftSt → PerfVBSt → H1StructureBundle := by
  intro hD hL hB hP hS hK hT hV R _ A _ g hA hg
  have : IsProper A.hom := hA.proper
  have : IsSeparated A.hom := inferInstance
  have : Smooth A.hom := hg.smooth
  obtain ⟨P, iP, fP, S, hPerf⟩ := hP R A.left A.hom inferInstance inferInstance
  have low : ∀ {R₀ : Type} [CommRing R₀] (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
      ∀ (S₀ : Sys A₀.left P), Function.Bijective (resSys A₀.hom S₀).pull1 ∧
        (Stein (OAff A₀.hom) ↔ Stein (OSys A₀.hom S₀)) := fun {R₀} _ A₀ _ h₀ S₀ => by
    have : IsProper A₀.hom := h₀.proper
    obtain ⟨b1, -, st⟩ := hL R₀ _ _ (OAff A₀.hom) (OSys A₀.hom S₀) (resSys A₀.hom S₀)
      (hD R₀ A₀.left A₀.hom inferInstance P S₀)
    exact ⟨b1, st⟩
  refine vb_of_bijective' (resSys A.hom S) (low A hA S).1 (hV R P (OSys A.hom S) g hPerf ?_ ?_ ?_)
  · intro R' _ _
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg R'
    obtain ⟨S', m, -⟩ := hB R R' A.left A'.left A.hom A'.hom φ h inferInstance P S
    exact ⟨OSys A'.hom S', m, (low A' hA' S').2.1 (hS R' A' g hA' hg')⟩
  · intro k _ _
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg k
    obtain ⟨S', m, -⟩ := hB R k A.left A'.left A.hom A'.hom φ h inferInstance P S
    exact ⟨OSys A'.hom S', m, finrank_of_vb
      (vb_of_bijective _ (low A' hA' S').1 (hK k A' g hA' hg' (Field.toIsField k)))⟩
  · intro B _ _ _ t ht
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg B
    obtain ⟨S', m, -⟩ := hB R B A.left A'.left A.hom A'.hom φ h inferInstance P S
    obtain ⟨A'', _, φ', hA'', hg'', h'⟩ := exists_base A' hA' hg' (B ⧸ Ideal.span {t})
    have : IsProper A'.hom := hA'.proper
    obtain ⟨S'', m', hm'⟩ := hB B (B ⧸ Ideal.span {t}) A'.left A''.left A'.hom A''.hom φ' h' inferInstance P S'
    refine ⟨OSys A'.hom S', m, OSys A''.hom S'', m', fun y => ?_⟩
    have b2 := (low A'' hA'' S'').1
    obtain ⟨d, rfl⟩ := b2.2 y
    obtain ⟨c, hc⟩ := hT B A' g hA' hg' t ht A''.left A''.hom φ' h' d
    refine ⟨(resSys A'.hom S').pull1 c, ?_⟩
    obtain ⟨d', hd'⟩ := b2.2 (m'.coef.pull1 ((resSys A'.hom S').pull1 c))
    have e := (existsUnique_isPullO h'.w c).unique hc (hm' c d' hd'.symm)
    rw [e, hd']

end GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLift
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Collapse
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}

theorem form_sum_zsmul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {m : ℕ} (I : Fin m → Fin d)
    {ι : Type} [Fintype ι] (a : ι → ℤ) (w : ι → Φ.A.obj E.D) (u : ComposableArrows C m) :
    E.form σ I (∑ i, a i • w i) u = ∑ i, a i • E.form σ I (w i) u := by
  unfold Frame.form
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, mul_smul_comm]

theorem form_zsmul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {m : ℕ} (I : Fin m → Fin d)
    (a : ℤ) (w : Φ.A.obj E.D) (u : ComposableArrows C m) :
    E.form σ I (a • w) u = a • E.form σ I w u := by
  unfold Frame.form
  rw [map_zsmul, mul_smul_comm]

theorem sgn_eq_zero_of_not_injective {m : ℕ} (I : Idx m d) {J : Fin m → Fin d} (h : ¬ Function.Injective J) :
    sgn I J = 0 := by
  refine Finset.sum_eq_zero fun π _ => if_neg ?_
  intro e
  exact h (e ▸ I.2.injective.comp π.injective)

theorem exists_increasing {m : ℕ} {J : Fin m → Fin d} (h : Function.Injective J) :
    ∃ (I : Idx m d) (π : Equiv.Perm (Fin m)), J = I.1 ∘ π := by
  refine ⟨⟨J ∘ Tuple.sort J, (Tuple.monotone_sort J).strictMono_of_injective
    (h.comp (Tuple.sort J).injective)⟩, (Tuple.sort J)⁻¹, ?_⟩
  funext k
  simp

theorem sgn_comp_self {m : ℕ} (I : Idx m d) (π : Equiv.Perm (Fin m)) :
    sgn I (I.1 ∘ π) = (Equiv.Perm.sign π : ℤ) := by
  unfold sgn
  rw [Finset.sum_eq_single π]
  · simp
  · intro b _ hb
    refine if_neg fun e => hb ?_
    exact (Equiv.ext fun k => I.2.injective (congrFun e k)).symm
  · simp

theorem sgn_comp_of_ne {m : ℕ} {I I' : Idx m d} (π : Equiv.Perm (Fin m)) (h : I' ≠ I) :
    sgn I' (I.1 ∘ π) = 0 := by
  refine Finset.sum_eq_zero fun π' _ => if_neg fun e => h (Subtype.ext ?_)
  refine (StrictMono.range_inj I'.2 I.2).1 ?_
  have e' := congrArg Set.range e
  rw [π.surjective.range_comp, π'.surjective.range_comp] at e'
  exact e'.symm

theorem rep_finset_sum {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ} {ι : Type} (t : Finset ι)
    {z : ι → ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : ι → CH.H (sq a b) j}
    (h : ∀ i, CrystallineSemistableComparison.Pb.Rep a b (z i) (c i)) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => ∑ i ∈ t, z i s) (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rep_zero fun s => Ideal.zero_mem _
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact rep_add (h i) ih

theorem rep_collapse_one {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (m : ℕ) (r : ℤ) (hr : r = m) (J : Fin m → Fin d) (w : Φ.A.obj E.D)
    (c : CH.H (gr Fil r) m) (h : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ J w) c) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (sgn I J • w) u) c := by
  have hw : w ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]
    trivial
  have hr0 : r = (m : ℤ) + ((0 : ℕ) : ℤ) := by simpa using hr
  by_cases hJ : Function.Injective J
  · obtain ⟨I, π, rfl⟩ := exists_increasing hJ
    obtain ⟨c₀, h₀⟩ := GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc m 0 r hr0 I.1 w hw
    have h₁ := (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc m 0 r hr0 I.1 w hw c₀ h₀).2.1 π
    obtain rfl := rep_unique h h₁
    have h₂ := GlobalTheory.CompanionTheory.AltForm.Rep.zsmul (Equiv.Perm.sign π : ℤ) h₀
    refine rep_congr h₂ fun u => ?_
    rw [Finset.sum_eq_single I, sgn_comp_self, form_zsmul, Pi.smul_apply, sub_self]
    · exact Ideal.zero_mem _
    · intro I' _ hI'
      rw [sgn_comp_of_ne π hI', zero_smul]
      unfold Frame.form
      simp
    · simp
  · obtain rfl := (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc m 0 r hr0 J w hw c h).1 hJ
    refine rep_zero fun u => ?_
    rw [Finset.sum_eq_zero]
    · exact Ideal.zero_mem _
    · intro I _
      rw [sgn_eq_zero_of_not_injective I hJ, zero_smul]
      unfold Frame.form
      simp

theorem rep_collapse : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (r : ℤ), r = m → ∀ {ι : Type} [Fintype ι] (J : ι → Fin m → Fin d) (w : ι → Φ.A.obj E.D) (x : CH.H (gr Fil r) m),
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ i, E.form σ (J i) (w i) u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u) x := by
  intro R _ C _ Φ Fil d hF E σ hc m r hr ι _ J w x h
  have hw : ∀ i, w i ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := fun i => by
    rw [hF.top _ (by simp)]
    trivial
  have hr0 : r = (m : ℤ) + ((0 : ℕ) : ℤ) := by simpa using hr
  choose c hcl using fun i => GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc m 0 r hr0 (J i) (w i) (hw i)
  obtain rfl := rep_unique h (rep_finset_sum Finset.univ hcl)
  have h₂ := rep_finset_sum Finset.univ fun i => rep_collapse_one hF E σ hc m r hr (J i) (w i) (c i) (hcl i)
  refine rep_congr h₂ fun u => ?_
  rw [Finset.sum_comm]
  have e : ∀ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u = ∑ i, E.form σ I.1 (sgn I (J i) • w i) u := by
    intro I
    rw [form_sum_zsmul]
    exact Finset.sum_congr rfl fun i _ => (form_zsmul E σ I.1 _ _ u).symm
  simp only [e, sub_self]
  exact Ideal.zero_mem _

end Collapse

end GlobalTheory.CompanionTheory.ConeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormFrame
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.FrameEx

theorem dividedPowerFiltration_dividedPowersBot (O : Type) [CommRing O] {n : ℕ} (hn : n ≠ 0) :
    pdP (dividedPowersBot O) n = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have hpos : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra hne
    push_neg at hne
    have : (l.map Prod.fst).sum = 0 := by
      refine List.sum_eq_zero ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hne p hp
    omega
  obtain ⟨p, hp, hp0⟩ := hpos
  have h0 : p.2 = 0 := by simpa using hl p hp
  have : (dividedPowersBot O).dpow p.1 p.2 = 0 := by
    rw [h0]; exact (dividedPowersBot O).dpow_eval_zero hp0
  have hz : (l.map fun q => (dividedPowersBot O).dpow q.1 q.2).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨p, hp, this⟩)
  rw [hz]
  exact Ideal.zero_mem _

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem inU_of_SS {l s : ℕ} {W : X.Opens} (T : Thick (LL q)) (h : SS q l s W T) : InU W T := by
  obtain ⟨-, V, hV, hT⟩ := h
  rw [Set.mem_singleton_iff.1 hV] at hT
  exact hT

end GlobalTheory.CompanionTheory.GrForm.FrameEx

namespace GlobalTheory.CompanionTheory.GrForm


open FrameEx in
theorem stFrame : StFrame := by
  intro O _ l s hb X q W d c u hu
  letI := (strV q W).toAlgebra
  obtain ⟨c', e, hTF, he1, het, hev⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := O) (I := ⊥) (dividedPowersBot O) l s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  have good := GlobalTheory.T.chart_is_good c'
  have hQ : ∀ T, SS q l s W T → InU W T := inU_of_SS
  have hD : SS q l s W c'.D := ⟨hTF, W, rfl, c'.inV⟩
  obtain ⟨hpow, hgr⟩ := _root_.GlobalTheory.CompanionTheory.ChartFil.chart_grConst c' good (SS q l s W) hQ hD
  have hval : ∀ (T : Thick (LL q)) (h : InU W T) (σ : c'.D ⟶ T) (f : Γ(X, W)),
      Ideal.Quotient.mk T.J (σ.φ (e (1 ⊗ₜ f))) = ev T h f := by
    intro T h σ f
    rw [ev_nat σ c'.inV h f, hev f]
    rfl
  have hσ : ∀ T : (SS q l s W).FullSubcategory, ∃ σ : c'.D ⟶ T.obj, ∀ i, σ.φ (c'.t i) = u i T.obj := by
    intro T
    have hT := hQ _ T.property
    obtain ⟨σ₀⟩ := good.1 T.obj hT
    obtain ⟨σ, h1, -⟩ := good.2 T.obj σ₀ (fun i => u i T.obj - σ₀.φ (c'.t i)) (fun i => by
      refine Ideal.Quotient.eq.1 ?_
      rw [hu i T.obj hT, ← het i, hval T.obj hT σ₀])
    exact ⟨σ, fun i => by simpa using h1 i⟩
  choose σ hσ using hσ
  let θ : Γ(X, W) ≃+* (sP (SS q l s W)).A.obj (c'.frame good (SS q l s W) hQ hD).D :=
    ((Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv).trans e
  have hθ : ∀ f, θ f = e (1 ⊗ₜ f) := fun f => rfl
  refine ⟨c'.frame good (SS q l s W) hQ hD, fun T => ObjectProperty.homMk (σ T), θ, hgr, ?_, ?_, ?_, ?_⟩
  · intro n hn
    change c'.D.pdPow ((n : ℤ).toNat) = ⊥
    rw [Int.toNat_natCast, hpow, dividedPowerFiltration_dividedPowersBot O hn, Ideal.map_bot]
  · intro i T s s'
    change (s'.hom.φ (c'.t i) - s.hom.φ (c'.t i) : T.obj.B) = s'.hom.φ (θ (c.t i)) - s.hom.φ (θ (c.t i))
    rw [hθ, het]
  · intro i T
    change (σ T).φ (θ (c.t i)) = u i T.obj
    rw [hθ, het, hσ]
  · intro T h f
    exact hval T.obj h (σ T) f

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeTateCharacterWeight
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem finite_units_zpow_eq {F : Type*} [Field F] {d : ℤ} (hd : d ≠ 0) (w : Fˣ) :
    {z : Fˣ | z ^ d = w}.Finite := by
  have hm : 0 < d.natAbs := Int.natAbs_pos.2 hd
  have key : ∀ c : F, {z : Fˣ | (z : F) ^ d.natAbs = c}.Finite := fun c =>
    ((Polynomial.nthRoots d.natAbs c).toFinset.finite_toSet.preimage
      (Units.val_injective (α := F)).injOn).subset fun z hz => by
        simpa [Polynomial.mem_nthRoots hm] using hz
  rcases Int.natAbs_eq d with h | h
  · refine (key (w : F)).subset fun z hz => ?_
    have hz' : z ^ d = w := hz
    rw [h, zpow_natCast] at hz'
    change (z : F) ^ d.natAbs = w
    rw [← Units.val_pow_eq_pow_val, hz']
  · refine (key ((w⁻¹ : Fˣ) : F)).subset fun z hz => ?_
    have hz' : z ^ d = w := hz
    rw [h, zpow_neg, zpow_natCast] at hz'
    change (z : F) ^ d.natAbs = ((w⁻¹ : Fˣ) : F)
    rw [← Units.val_pow_eq_pow_val, ← hz', inv_inv]

theorem eq_one_of_tpow_mul_unit_eigen {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l))
    [FiniteDimensional ℚ_[l] ↥L]
    (hI : ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite)
    (u : (Formalism.Per6.BdRp l)ˣ) (n : ℕ) (a : Gal(Om l/↥L) → ℚ_[l])
    (hact : ∀ σ : Gal(Om l/↥L), σ • (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)) =
      algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a σ) * (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)))
    (hin : ∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      a σ = (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) :
    n = 1 := by
  by_contra hn
  have ht : GroundTheory.PAdicHodge.tBdR l ≠ 0 := (GroundTheory.PAdicHodge.irreducible_tBdR (p := l)).ne_zero
  let c : ℤ_[l]ˣ →* ℚ_[l]ˣ := Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom
  have hc : Function.Injective c := fun x y h =>
    Units.ext (Subtype.ext (congrArg Units.val h))
  let χ : Gal(Om l/↥L) → ℚ_[l] := fun σ => (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])
  have hχ : ∀ σ, χ σ ≠ 0 := fun σ => (c (GroundTheory.PAdicHodge.cycloChar L σ)).ne_zero
  let A : ℚ_[l] →+* Formalism.Per6.BdRp l := algebraMap ℚ_[l] (Formalism.Per6.BdRp l)
  have hu : ∀ σ : Gal(Om l/↥L), A (χ σ) ^ n * (σ • (u : Formalism.Per6.BdRp l)) = A (a σ) * u := by
    intro σ
    have h := hact σ
    rw [smul_mul', smul_pow', GroundTheory.PAdicHodge.gal_smul_tBdR, mul_pow] at h
    refine mul_left_cancel₀ (pow_ne_zero n ht) ?_
    change _ = _ at h
    linear_combination h
  have hu' : ∀ σ : Gal(Om l/↥L), σ • (u : Formalism.Per6.BdRp l) = A (a σ * (χ σ ^ n)⁻¹) * u := by
    intro σ
    have e : A ((χ σ ^ n)⁻¹) * A (χ σ) ^ n = 1 := by
      rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero n (hχ σ)), map_one]
    calc σ • (u : Formalism.Per6.BdRp l)
        = (A ((χ σ ^ n)⁻¹) * A (χ σ) ^ n) * (σ • (u : Formalism.Per6.BdRp l)) := by rw [e, one_mul]
      _ = A ((χ σ ^ n)⁻¹) * (A (a σ) * u) := by rw [mul_assoc, hu]
      _ = A (a σ * (χ σ ^ n)⁻¹) * u := by rw [map_mul]; ring
  have hx0 : GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) ≠ 0 :=
    (u.isUnit.map (GroundTheory.PAdicHodge.thetaAlgHom l)).ne_zero
  have hθ : ∀ (σ : Gal(Om l/↥L)) (q : ℚ_[l]),
      σ • (u : Formalism.Per6.BdRp l) = algebraMap ℚ_[l] (Formalism.Per6.BdRp l) q * u →
        σ • GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) =
          algebraMap ℚ_[l] ℂ_[l] q * GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) := by
    intro σ q h
    rw [GroundTheory.PAdicHodge.thetaAlgHom_apply, ← GroundTheory.PAdicHodge.thetaBDeRhamPlusField_gal_smul, h,
      ← GroundTheory.PAdicHodge.thetaAlgHom_apply, map_mul, AlgHom.commutes]
    rfl
  obtain ⟨ψ, hψc, hψx⟩ := GroundTheory.PAdicHodge.EigenChar.exists_eigenChar hx0
    fun σ : Gal(Om l/↥L) => ⟨_, hθ σ _ (hu' σ)⟩
  have hfin := GroundTheory.PAdicHodge.ACris.senTateCharacters (p := l) L ψ hψc _ hx0 hψx
  have hd : (1 - (n : ℤ)) ≠ 0 := fun h => hn (by omega)
  have hψ : ∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      (c (GroundTheory.PAdicHodge.cycloChar L σ)) ^ (1 - (n : ℤ)) = ψ σ := by
    intro σ hσ
    have h2 : a σ * (χ σ ^ n)⁻¹ = ψ σ := GroundTheory.PAdicHodge.EigenChar.eq_of_mul_eq hx0
      ((hθ σ _ (hu' σ)).symm.trans (hψx σ))
    refine Units.ext ?_
    rw [Units.val_zpow_eq_zpow_val, ← h2, hin σ hσ]
    change χ σ ^ (1 - (n : ℤ)) = χ σ * (χ σ ^ n)⁻¹
    rw [zpow_sub₀ (hχ σ), zpow_one, zpow_natCast, div_eq_mul_inv]
  refine (hI.image hc.injOn) (Set.Finite.of_finite_fibers (fun z => z ^ (1 - (n : ℤ))) ?_ ?_)
  · refine hfin.subset ?_
    rintro _ ⟨_, ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩, rfl⟩
    exact ⟨σ, hσ, (hψ σ hσ).symm⟩
  · intro w _
    refine (finite_units_zpow_eq hd w).subset fun z hz => ?_
    exact hz.2

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

lemma range_app_iso_comp {X : Scheme.{0}} {P Q E : X.Modules} (e : P ≅ Q) (f : Q ⟶ E)
    (V : X.Opens) : Set.range ((e.hom ≫ f).app V) = Set.range (f.app V) := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.app V x, by rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.app V y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_assoc]

theorem secs_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (E : X.Modules) (hE : E.IsQuasicoherent) (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) :
    secs (powSub I E n) V =
      ((Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(E, V)) :
        Set Γ(E, V)) := by
  rw [← range_idealPowι_app I E hV n, ← range_app_iso_comp
    (Subobject.underlyingIso (idealPowι I E n)) (idealPowι I E n) V]
  unfold secs powSub
  rw [Subobject.underlyingIso_hom_comp_eq_mk]

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiBaseLe
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisFrob

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redLe (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem phi_base_le {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((phiPt F κ m).app B₀ ((basePt F _ (red_κb κ true h)).app B₀ y)).1.2 =
      ((basePt F _ (red_κb κ true h)).app B₀ ((phiPt F κ n).app B₀ y)).1.2 := by
  rw [SH.phi_snd F κ m B₀ _ (l_zero y.1.1), SH.base_snd, SH.base_snd, SH.phi_snd F κ n B₀ _ (l_zero y.1.1)]

theorem red_phi_le : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ true m j), redHc F κ true h j (phiHc F κ m j x) = phiHc F κ n j (redHc F κ true h j x) := by
  intro l _ O _ F κ m n h j x
  unfold redHc phiHc redMor phiMorC
  exact cr_square (SH.phiM F κ m) (redLe F κ true h) (redLe F κ true h) (SH.phiM F κ n) ((base l).phi_cris m)
    (red_cris _ h) (red_cris _ h) ((base l).phi_cris n) ((pdOk_frob _).red_acr h) (phi_base_le F κ h) j x

end GlobalTheory.CompanionTheory.CrisFrob
end
end

