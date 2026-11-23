module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesMinimal
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.FinAffAmple

variable {X : Scheme.{0}} {M : LB X}

theorem mem_secAdd_iff_right {s t : M.Sec} {x : X} (ht : x ∉ nonzeroLocus t) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus s := by
  by_cases hc : ∃ k, x ∈ M.U k
  · obtain ⟨k, hk⟩ := hc
    rw [GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk, GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk] at *
    change x ∈ X.basicOpen (s.f k + t.f k) ↔ _
    rw [Scheme.mem_basicOpen _ _ _ hk, Scheme.mem_basicOpen _ _ _ hk] at *
    rw [map_add (f := _)]
    have hm : (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (t.f k) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 ht
    have := Ideal.add_mem_iff_left (IsLocalRing.maximalIdeal _)
      (a := (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (s.f k)) hm
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff] at this
    exact not_iff_not.1 this
  · push_neg at hc
    exact ⟨fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc),
      fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc)⟩

theorem mem_secAdd_iff_left {s t : M.Sec} {x : X} (hs : x ∉ nonzeroLocus s) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus t := by
  have e : DVR.SecOps.secAdd s t = DVR.SecOps.secAdd t s := DVR.SecOps.sec_ext fun i => add_comm (s.f i) (t.f i)
  rw [e]
  exact mem_secAdd_iff_right hs

theorem exists_sec_forall_mem (T : Finset X) (t : X → M.Sec) (ht : ∀ x ∈ T, x ∈ nonzeroLocus (t x))
    (ht' : ∀ x ∈ T, ∀ y ∈ T, y ≠ x → y ∉ nonzeroLocus (t x)) :
    ∃ g : M.Sec, ∀ x ∈ T, x ∈ nonzeroLocus g := by
  classical
  suffices H : ∀ T' : Finset X, T' ⊆ T → ∃ g : M.Sec, ∀ x ∈ T, (x ∈ nonzeroLocus g ↔ x ∈ T') by
    obtain ⟨g, hg⟩ := H T subset_rfl
    exact ⟨g, fun x hx => (hg x hx).2 hx⟩
  intro T'
  induction T' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨DVR.SecOps.secZero, fun x _ => ?_⟩
    rw [GlobalTheory.nonzeroLocus_secZero]
    simp
  | insert a T' ha ih =>
    intro hsub
    obtain ⟨g, hg⟩ := ih ((Finset.subset_insert a T').trans hsub)
    have haT : a ∈ T := hsub (Finset.mem_insert_self a T')
    refine ⟨DVR.SecOps.secAdd g (t a), fun x hx => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      rw [mem_secAdd_iff_left (fun h => ha ((hg x hx).1 h))]
      simpa using ht x haT
    · rw [mem_secAdd_iff_right (ht' a haT x hx hxa), hg x hx, Finset.mem_insert]
      simp [hxa]

theorem exists_specializes_minimal {Z : Type*} [TopologicalSpace Z] [T0Space Z] (F : Finset Z) {x : Z}
    (hx : x ∈ F) : ∃ y ∈ F, x ⤳ y ∧ ∀ z ∈ F, y ⤳ z → z = y := by
  classical
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (F.filter (x ⤳ ·)) (fun y => (F.filter (y ⤳ ·)).card)
    ⟨x, Finset.mem_filter.2 ⟨hx, specializes_refl x⟩⟩
  obtain ⟨hyF, hxy⟩ := Finset.mem_filter.1 hy
  refine ⟨y, hyF, hxy, fun z hz hyz => ?_⟩
  have hsub : F.filter (z ⤳ ·) ⊆ F.filter (y ⤳ ·) := fun w hw => by
    obtain ⟨hwF, hzw⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hwF, hyz.trans hzw⟩
  have hle := hmin z (Finset.mem_filter.2 ⟨hz, hxy.trans hyz⟩)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hzy : z ⤳ y := (Finset.mem_filter.1 (heq ▸ Finset.mem_filter.2 ⟨hyF, specializes_refl y⟩ :
    y ∈ F.filter (z ⤳ ·))).2
  exact (hyz.antisymm hzy).eq.symm

theorem finAff_of_isAmpleLB {Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f] {L : LB X}
    (h : IsAmpleLB L) : FinAff X := by
  classical
  intro F
  let F' := F.filter (fun x => ∀ z ∈ F, x ⤳ z → z = x)
  let V : X → X.Opens := fun x =>
    ⟨(⋃ y ∈ F'.erase x, closure ({y} : Set X))ᶜ, (isClosed_biUnion_finset fun _ _ => isClosed_closure).isOpen_compl⟩
  have hV : ∀ x ∈ F', x ∈ V x := by
    intro x hx hmem
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨hyx, hyF'⟩ := Finset.mem_erase.1 hy
    have hyx' : y ⤳ x := specializes_iff_mem_closure.2 hxy
    exact hyx ((Finset.mem_filter.1 hyF').2 x (Finset.mem_filter.1 hx).1 hyx').symm
  have hV' : ∀ x ∈ F', ∀ y ∈ F', y ≠ x → y ∉ V x := fun x _ y hy hyx hmem =>
    hmem (Set.mem_iUnion₂.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, subset_closure rfl⟩)
  choose n hn s hs hsV _ using fun x : F' => h.exists_affine_le (hV x.1 x.2)
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow n hn s
  let tt : X → (lbPow L N).Sec := fun x => if hx : x ∈ F' then t ⟨x, hx⟩ else DVR.SecOps.secZero
  have htt : ∀ x (hx : x ∈ F'), nonzeroLocus (tt x) = nonzeroLocus (s ⟨x, hx⟩) := fun x hx => by
    simp only [tt, dif_pos hx, ht]
  obtain ⟨g, hg⟩ := exists_sec_forall_mem F' tt (fun x hx => (htt x hx).symm ▸ hs ⟨x, hx⟩)
    (fun x hx y hy hyx hmem => hV' x hx y hy hyx (hsV ⟨x, hx⟩ ((htt x hx) ▸ hmem)))
  refine ⟨nonzeroLocus g, h.isAffineOpen_nonzeroLocus f hN g, fun x hx => ?_⟩
  obtain ⟨y, hyF, hxy, hmin⟩ := exists_specializes_minimal F hx
  exact hxy.mem_open (nonzeroLocus g).isOpen (hg y (Finset.mem_filter.2 ⟨hyF, hmin⟩))

theorem finAff_of_relAmple : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ L : LB B.left, L.IsLB → Out.RelAmple B L → FinAff B.left := by
  intro R _ B _ hB L hL hA
  have := hB.proper
  exact finAff_of_isAmpleLB B.hom (isAmpleLB_of_relAmple_of_isAffine B hL hA)

end GlobalTheory.DualCon.FinAffAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfVectorFieldOnOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerField

variable {X : Scheme.{0}} {W : X.Opens} {d : Fld X} {x : X}

theorem germ_field_congr (hd : IsField W d) {O O' : X.Opens} (hO : x ∈ O) (hO' : x ∈ O')
    (hOW : O ≤ W) (hO'W : O' ≤ W) (f : Γ(X, O)) (f' : Γ(X, O'))
    (h : (X.presheaf.germ O x hO).hom f = (X.presheaf.germ O' x hO').hom f') :
    (X.presheaf.germ O x hO).hom (d O f) = (X.presheaf.germ O' x hO').hom (d O' f') := by
  obtain ⟨V, hV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hO hO' f f' h
  have h1 : (X.presheaf.germ O x hO).hom (d O f) =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iU) f)) := by
    rw [hd.2.2 O V (leOfHom iU) hOW f]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iU x hV _).symm
  have h2 : (X.presheaf.germ O' x hO').hom (d O' f') =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iV) f')) := by
    rw [hd.2.2 O' V (leOfHom iV) hO'W f']
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iV x hV _).symm
  have e' : resG X (leOfHom iU) f = resG X (leOfHom iV) f' := e
  rw [h1, h2, e']

theorem exists_rep (hxW : x ∈ W) (t : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f : Γ(X, O)), (X.presheaf.germ O x hO).hom f = t := by
  obtain ⟨U, m, s, hs⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf t
  refine ⟨U ⊓ W, ⟨m, hxW⟩, inf_le_right, resG X (inf_le_left : U ⊓ W ≤ U) s, ?_⟩
  rw [← hs]
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨m, hxW⟩ s

theorem exists_rep₂ (hxW : x ∈ W) (t t' : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f f' : Γ(X, O)),
      (X.presheaf.germ O x hO).hom f = t ∧ (X.presheaf.germ O x hO).hom f' = t' := by
  obtain ⟨O₁, h₁, hW₁, f₁, e₁⟩ := exists_rep hxW t
  obtain ⟨O₂, h₂, hW₂, f₂, e₂⟩ := exists_rep hxW t'
  refine ⟨O₁ ⊓ O₂, ⟨h₁, h₂⟩, inf_le_left.trans hW₁, resG X (inf_le_left : O₁ ⊓ O₂ ≤ O₁) f₁,
    resG X (inf_le_right : O₁ ⊓ O₂ ≤ O₂) f₂, ?_, ?_⟩
  · rw [← e₁]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨h₁, h₂⟩ f₁
  · rw [← e₂]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x ⟨h₁, h₂⟩ f₂

def germMap (hxW : x ∈ W) (t : X.presheaf.stalk x) : X.presheaf.stalk x :=
  (X.presheaf.germ _ x (exists_rep hxW t).choose_spec.choose).hom
    (d _ (exists_rep hxW t).choose_spec.choose_spec.choose_spec.choose)

theorem germMap_germ (hd : IsField W d) (hxW : x ∈ W) {O : X.Opens} (hO : x ∈ O) (hOW : O ≤ W)
    (f : Γ(X, O)) :
    germMap (d := d) hxW ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  have hs := (exists_rep hxW ((X.presheaf.germ O x hO).hom f)).choose_spec.choose_spec
  exact germ_field_congr hd _ hO hs.choose hOW _ f hs.choose_spec.choose_spec

end GlobalTheory.StalkDerField


open GlobalTheory.StalkDerField in
theorem GlobalTheory.StalkDerField.exists_stalk_derivation : ∀ (X : Scheme.{0}) (W : X.Opens) (d : Fld X), IsField W d → ∀ (x : X), x ∈ W → ∃ δ : Derivation ℤ (X.presheaf.stalk x) (X.presheaf.stalk x), ∀ (O : X.Opens) (hO : x ∈ O), O ≤ W → ∀ f, δ ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  intro X W d hd x hxW
  let g : X.presheaf.stalk x →+ X.presheaf.stalk x := AddMonoidHom.mk' (germMap (d := d) hxW) (by
    intro t t'
    obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
    rw [← map_add (f := _), germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
      germMap_germ hd hxW hO hOW, hd.1 O hOW f f', map_add])
  refine ⟨Derivation.mk' g.toIntLinearMap ?_, fun O hO hOW f => germMap_germ hd hxW hO hOW f⟩
  intro t t'
  obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
  show germMap hxW _ = _ • germMap hxW _ + _ • germMap hxW _
  rw [← map_mul, germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
    germMap_germ hd hxW hO hOW, hd.2.1 O hOW f f', smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularFrameInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertFrameUnimod

theorem selfDual_scaled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
  ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  intro F E _ _ _ _ _ σ B d W r s hW v w hw
  obtain ⟨t, ht0, s₁, s₂, h1, h2, c1, c2⟩ := _root_.GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt hw
  exact ⟨t, ht0, _root_.GlobalTheory.SkewScaleInert.isSelfDualAt_smul_transpose σ B W r s hW hw t ht0 s₁ s₂ h1 h2 c1 c2⟩

theorem isConjAt_conjW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (GlobalTheory.InertBigCell.conjW σ hw) := fun y =>
  congrArg (fun z => toCompl (under_eq_of_isInertAt hw) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z))
    ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y)

theorem exists_frame_unimod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
  ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  ∃ (b : GL (Fin d) (w.adicCompletion E)) (δ : w.adicCompletion E),
    (∀ u, u ∈ GlobalTheory.LFun.latAt w W.L ↔ GlobalTheory.InertBigCell.InLat (w.adicCompletionIntegers E) b u) ∧
    GlobalTheory.InertBigCell.conjW σ hw δ = δ ∧
    (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))) i j ∈ w.adicCompletionIntegers E) ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det ≠ 0 ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det⁻¹ ∈ w.adicCompletionIntegers E := by
  intro F E _ _ _ _ _ σ B d W r s _hB hW v w hw
  have hc := isConjAt_conjW σ hw
  obtain ⟨t, ht0, hsd⟩ := selfDual_scaled σ B W r s hW hw
  haveI := hW.lat
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := W.L) hw (Submodule.IsLattice.fg E W.L) Submodule.IsLattice.span_eq_top
  have hdet : (algebraMap F E t • W.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).2 ht0)) (GlobalTheory.FinUniq.det_ne_zero_skew hW)
  obtain ⟨B0, hB0, eB0⟩ := InertChart.exists_gram hw hc hdet hsd ha
  obtain ⟨C, hC⟩ := hB0
  set δ : w.adicCompletion E := algebraMap E (w.adicCompletion E) (algebraMap F E t) with hδdef
  have hδ : GlobalTheory.InertBigCell.conjW σ hw δ = δ := by
    rw [hδdef, InertChart.conj_algebraMap hc, AlgHom.commutes]
  have key : δ • ((a : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw)) =
      (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ := by
    rw [eB0, Matrix.transpose_mul, Matrix.transpose_mul]
    have e1 : ((algebraMap F E t • W.Jᵀ).map (algebraMap E (w.adicCompletion E)))ᵀ =
        δ • W.J.map (algebraMap E (w.adicCompletion E)) := by
      ext i j
      simp only [hδdef, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    have e2 : (Formalism.UG.cT (GlobalTheory.InertBigCell.conjW σ hw) (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ =
        (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw) := by
      simp [Formalism.UG.cT]
    rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hBC : (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).map (Formalism.UG.Ov E w).subtype := by
    rw [← hC]; rfl
  have hdetB : (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E)).det =
      (Formalism.UG.Ov E w).subtype (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det := by
    rw [hBC, ← RingHom.mapMatrix_apply, RingHom.map_det]
  have hCu : IsUnit (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 C.isUnit
  refine ⟨a, δ, fun u => ?_, hδ, fun i j => ?_, ?_, ?_⟩
  · have h1 := ha ((a⁻¹ : GL (Fin d) (w.adicCompletion E)).1 *ᵥ u)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1.symm
  · rw [key, Matrix.transpose_apply, hBC, Matrix.map_apply]
    exact (C.1 j i).2
  · rw [key, Matrix.det_transpose, hdetB]
    intro h0
    exact hCu.ne_zero (Subtype.ext h0)
  · rw [key, Matrix.det_transpose, hdetB]
    obtain ⟨u, hu⟩ := hCu
    have : (Formalism.UG.Ov E w).subtype (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det *
        (Formalism.UG.Ov E w).subtype (u⁻¹ : (Formalism.UG.Ov E w)ˣ) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [inv_eq_of_mul_eq_one_right this]
    exact (u⁻¹ : (Formalism.UG.Ov E w)ˣ).1.2

end GlobalTheory.InertFrameUnimod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfNormOneFractionRingDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.KeyEven.fractionRing_norm_one_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (C : Type) [NormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ a : FractionRing V, ‖algebraMap (FractionRing V) C a‖ = 1 → ∃ u : Vˣ, a = algebraMap V (FractionRing V) u := by
  intro V _ _ _ C _ _ hC a ha
  have key : ∀ x : V, ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 → IsUnit x := by
    intro x hx
    by_contra hu
    have hm : x ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal x).2 hu
    have := hC.2 x hm
    rw [hx] at this
    exact lt_irrefl _ this
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hu := key x (by rw [hx]; exact ha)
    exact ⟨hu.unit, by simp [hx]⟩
  · have hx' : ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 := by
      rw [hx, map_inv₀, norm_inv, ha, inv_one]
    have hu := key x hx'
    refine ⟨hu.unit⁻¹, ?_⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have h1 : algebraMap V (FractionRing V) (↑hu.unit⁻¹ : V) * algebraMap V (FractionRing V) x = 1 := by
      rw [← map_mul]
      have : (↑hu.unit⁻¹ : V) * x = 1 := by
        have := hu.unit.inv_mul
        simpa using this
      rw [this, map_one]
    rw [hx] at h1
    field_simp at h1
    exact h1.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitThetaKeyRuleOpenModelChart
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpenModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem charZero_of_range [IsOpenImmersion Y.j] {R : Type} [CommRing R] [Nontrivial R] (z : Sp R ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : CharZero R :=
  charZero_of_injective_ringHom (Spec.preimage (IsOpenImmersion.lift Y.j z h ≫ pullback.snd _ _)).hom.injective

theorem exists_keyAt_of_range [IsOpenImmersion Y.j] (hpq : 1 ≤ D.p + D.q) (M : GChart Y) {R : Type} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (h : Set.range z ⊆ Set.range Y.j) :
    ∃ x : KeyIn R, KeyAt M z hz x := by
  obtain ⟨t, ⟨m⟩⟩ := exists_sab z Y.t
  have e : IsOpenImmersion.lift Y.j z h ≫ Y.j = z := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t Y.j (IsOpenImmersion.lift Y.j z h) Y.m (e.symm ▸ m)
  have hp₀ := Y.oF.proper
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp₀
  have hA : Out.RelAmple t.G t.PP.L := by
    have h₁ := AmpleBaseChange.relAmple_of_isPullback Y.oF.t.PP.isLB Y.oF.ample m'.cart.1
    refine (GlobalTheory.KeyAtFam.relAmple_iff_of_cls (pull_isLB Y.oF.t.PP.isLB m'.φ) t.PP.isLB le_rfl ?_).2 h₁
    rw [one_smul]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m')
  have := charZero_of_range z h
  have : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h₂ := IsTotallyComplex.finrank E
    exact Nat.mul_pos (by omega) hpq
  obtain ⟨x₀, -, h₀⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (spMap (algebraMap R (FractionRing R)) ≫ z)
    (le_preimage_comp _ hz) (by
      rintro _ ⟨s, rfl⟩
      exact h ⟨_, rfl⟩) hpos
  obtain ⟨x, -, hx⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hz m hp hA _ h₀
  exact ⟨x, hx⟩

theorem exists_unit_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y hO hj hpq κ hκ M
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have : IsReduced Y.X := by
    have (x : Y.X) : _root_.IsReduced (Y.X.presheaf.stalk x) := by
      have := GlobalTheory.IsNormalScheme.isDomain_stalk x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  let W₀ : Y.X.Opens := M.U ⊓ Y.j.opensRange
  have hW₀ : ∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j := fun x => Iff.rfl
  have hr : ∀ {R : Type} [CommRing R] (z : Sp R ⟶ Y.X), ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := by
    rintro R _ z hz _ ⟨s, rfl⟩
    exact ((hW₀ _).1 (hz (Set.mem_univ s))).2
  let P : Y.X.Opens → Prop := fun W => IsDomain Γ(Y.X, W)
  have hP : ∀ q ∈ W₀, ∃ W : Y.X.Opens, IsAffineOpen W ∧ W ≤ W₀ ∧ P W ∧ q ∈ W := fun q hq => by
    obtain ⟨D', hqD, hD⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X q
    obtain ⟨_, ⟨W, hW, rfl⟩, hqW, hle⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show q ∈ ((W₀ ⊓ D' : Y.X.Opens) : Set Y.X) from ⟨hq, hqD⟩) (W₀ ⊓ D').isOpen
    exact ⟨W, hW, fun r hr => (hle hr).1, hD W hqW fun r hr => (hle hr).2, hqW⟩
  have loc₁ : ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (hWV : W ≤ W₀), P W →
      ∃ (y : KeyIn Γ(Y.X, W)) (u : Γ(Y.X, W)ˣ),
        KeyAt M (tau hW) (tau_le hW (hWV.trans inf_le_left)) y ∧ GlobalTheory.KeyCl.IsValue κ y (u : Γ(Y.X, W)) := by
    intro W hW hWV hdom
    have : IsDomain Γ(Y.X, W) := hdom
    have : IsNoetherianRing Γ(Y.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : IsIntegrallyClosed Γ(Y.X, W) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
    have : CharZero Γ(Y.X, W) := charZero_of_range (tau hW) (hr _ (tau_le hW hWV))
    obtain ⟨y, hy⟩ := exists_keyAt_of_range hpq M (tau hW) (tau_le hW (hWV.trans inf_le_left)) (hr _ (tau_le hW hWV))
    obtain ⟨u, hu⟩ := GlobalTheory.KeyFamUnit.famUnit κ hκ.2.1 hκ.2.2.1 Γ(Y.X, W) y
    exact ⟨y, u, hy, hu⟩
  obtain ⟨f, hf⟩ := GlobalTheory.KeyOpen.glue_units W₀ P hP
    (fun L _ z v => ∀ (hc : CharZero L) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn L), KeyAt M z hz' x → v = (κ L x : L))
    (fun L _ z hz v w hv hw => by
      have hc : CharZero L := charZero_of_range z (hr z hz)
      have hz' : ⊤ ≤ z ⁻¹ᵁ M.U := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      obtain ⟨x, hx⟩ := exists_keyAt_of_range hpq M z hz' (hr z hz)
      exact (hv hc _ x hx).trans (hw hc _ x hx).symm)
    (fun W hW hWV hPW => by
      obtain ⟨y, u, hy, hu⟩ := loc₁ W hW hWV hPW
      refine ⟨u, fun L _ z hz hc hz' x hx => ?_⟩
      have e : spMap (ev z W hz) ≫ tau hW = z := GlobalTheory.FlagMod.spMap_ev z hW hz
      generalize ev z W hz = φ at e ⊢
      subst e
      exact (hu L φ x (GlobalTheory.KeyAtBC.keyPB_of_keyAt hy hx)).symm)
  exact ⟨W₀, f, hW₀, fun K _ hK z hz hz' x hx => hf K z hz hK hz' x hx⟩

end GlobalTheory.KeyOpenModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductSpecFieldPointFactorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreProduct_spec_fieldPoint_factors : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P), (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨ (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := by
  first | exact @GlobalTheory.SpecFibreProduct.point_factors | exact GlobalTheory.SpecFibreProduct.point_factors | (intros; apply GlobalTheory.SpecFibreProduct.point_factors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldOfEtaleOnOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  first | exact @GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open | exact GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open | (intros; apply GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open <;> assumption)
end

