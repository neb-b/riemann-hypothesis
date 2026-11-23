module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenLatticeImageLeSpanAfterBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenLatticeLeSpanCmHomImages
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat.LieSpan

section Over

variable {S S' : Scheme.{0}} {s : S' ⟶ S} {G B : Over S} {G' B' : Over S'} [GrpObj B] [GrpObj B'] [IsCommMonObj B]
  [IsCommMonObj B'] {φ : G'.left ⟶ G.left} {m : B'.left ⟶ B.left}

theorem one_over (w : φ ≫ G.hom = G'.hom ≫ s) (hm : IsGrpPullback B' B s m) :
    (1 : G' ⟶ B').left ≫ m = φ ≫ (1 : G ⟶ B).left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hm G'.hom (G'.hom ≫ s) rfl
  let φ₀ : Over.mk (G'.hom ≫ s) ⟶ G := Over.homMk φ w
  have h1 := he 1
  rw [map_one, ← comp_one φ₀] at h1
  exact h1.symm

theorem prod_over (w : φ ≫ G.hom = G'.hom ≫ s) (hm : IsGrpPullback B' B s m) {I : Type} (t : Finset I)
    {x' : I → (G' ⟶ B')} {x : I → (G ⟶ B)} (h : ∀ i, (x' i).left ≫ m = φ ≫ (x i).left) :
    (∏ i ∈ t, x' i).left ≫ m = φ ≫ (∏ i ∈ t, x i).left := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using one_over w hm
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact FamDesc.exists_mul w hm (h a) ih

end Over

section Rel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' : Type} [CommRing R] [CommRing R']
  {j : R →+* R'} {A B : PAT H (Sp R)} {A' B' : PAT H (Sp R')} (mA : SABMap A'.t A.t (spMap j))
  (mB : SABMap B'.t B.t (spMap j))

theorem exists_linear_over {f : A.t.G ⟶ B.t.G} (hf : Serre.IsLinearHom A.t.act B.t.act f) :
    ∃ f' : A'.t.G ⟶ B'.t.G, Serre.IsLinearHom A'.t.act B'.t.act f' ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  haveI := hf.isMonHom
  obtain ⟨f', hm, e⟩ := PairingFibre.exists_hom mA.cart mB.cart f
  refine ⟨f', ⟨hm, fun c => ?_⟩, e⟩
  apply Over.OverMorphism.ext
  apply mB.cart.1.hom_ext
  · have hc := congrArg CommaMorphism.left (hf.comm c)
    simp only [Over.comp_left] at hc ⊢
    rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
      ← Category.assoc, ← Category.assoc, e]
  · simp only [Over.comp_left, Category.assoc, Over.w]

theorem comb_over {n : ℕ} {f : Fin n → (A.t.G ⟶ B.t.G)} {f' : Fin n → (A'.t.G ⟶ B'.t.G)}
    (h : ∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) (x : Fin n → 𝓞 E) :
    (∏ i, (A'.t.act.act (x i) ≫ f' i)).left ≫ mB.φ = mA.φ ≫ (∏ i, (A.t.act.act (x i) ≫ f i)).left := by
  refine prod_over mA.cart.1.w mB.cart _ fun i => ?_
  rw [Over.comp_left, Over.comp_left, Category.assoc, h, ← Category.assoc, mA.act, Category.assoc]

theorem rel_descend (hj : Function.Injective j) {n : ℕ} {f : Fin n → (A.t.G ⟶ B.t.G)}
    {f' : Fin n → (A'.t.G ⟶ B'.t.G)} (h : ∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) (x : Fin n → 𝓞 E)
    (hx : ∏ i, (A'.t.act.act (x i) ≫ f' i) = 1) : ∏ i, (A.t.act.act (x i) ≫ f i) = 1 := by
  have : IsSchemeTheoreticallyDominant (spMap j) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom j) hj
  have : QuasiCompact (spMap j) := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom j)))
  have := A.ab.smooth
  have : Flat A.t.G.hom := inferInstance
  have : IsSeparated B.t.G.hom := B.t.semi.separated
  refine ExtUnique.over_hom_ext_of_isPullback mA.cart.1 ?_
  rw [← comb_over mA mB h x, hx]
  exact one_over mA.cart.1.w mB.cart

theorem exists_pow_eq {n : ℕ} {f : A.t.G ⟶ B.t.G} {φ : Fin n → (A.t.G ⟶ B.t.G)}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hφ : ∀ a, Serre.IsLinearHom A.t.act B.t.act (φ a)) {x₀ : 𝓞 E}
    (h₀ : x₀ ≠ 0) {x : Fin n → 𝓞 E} (h : (A.t.act.act x₀ ≫ f) * ∏ a, (A.t.act.act (x a) ≫ φ a) = 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ y : Fin n → 𝓞 E, f ^ N = ∏ a, (A.t.act.act (y a) ≫ φ a) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x₀}))
  have hN : Ideal.absNorm (Ideal.span {x₀}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  refine ⟨_, Nat.pos_of_ne_zero hN, fun a => -(z * x a), ?_⟩
  let F : Serre.Pts B.t.act A.t.G := Serre.Pts.mk _ f
  let Φ : Fin n → Serre.Pts B.t.act A.t.G := fun a => Serre.Pts.mk _ (φ a)
  have h1 : x₀ • F + ∑ a, x a • Φ a = 0 := by
    apply Serre.Pts.ext
    rw [Serre.Pts.hom_add, Serre.Pts.hom_sum, Serre.Pts.hom_zero, ← h, hf.comm]
    simp only [Serre.Pts.hom_smul, (hφ _).comm, F, Φ, Serre.Pts.hom_mk]
  have h2 : Ideal.absNorm (Ideal.span {x₀}) • F = ∑ a, (-(z * x a)) • Φ a := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hz, mul_smul, eq_neg_of_add_eq_zero_left h1, smul_neg, Finset.smul_sum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [neg_smul, mul_smul]
  have h3 := congrArg Serre.Pts.hom h2
  rw [Serre.Pts.hom_sum] at h3
  simp only [Serre.Pts.hom_smul, ← (hφ _).comm, Φ, Serre.Pts.hom_mk] at h3
  exact h3

end Rel

section Diff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {A B : PAT H (Sp (𝓞 K))} {FA : GenFib A.pol} {FB : GenFib B.pol}


open IntCoord in
theorem smul_diff_eq {p : ℕ} {φ : Fin p → (A.t.G ⟶ B.t.G)}
    {MP : Fin p → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))} (hMP : ∀ a, FA.IsDiffOf FB (φ a) (MP a))
    {f : A.t.G ⟶ B.t.G} {M : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)} (hM : FA.IsDiffOf FB f M) {n : ℕ}
    {x : Fin p → 𝓞 E} (hfn : f ^ n = ∏ a, (A.t.act.act (x a) ≫ φ a)) {τ : 𝓞 E →+* 𝓞 K} {e : Fin FA.P₀.g → K}
    (he : e ∈ FA.eigLat A.t.act τ) : n • M e = ∑ a, ((τ (x a) : 𝓞 K) : K) • MP a e := by
  obtain ⟨u, hu, heig⟩ := ((integral_tangent_coordinates K _ FA).2.2.2.2.2 _ _ τ e).1 he
  have hd := hM u e hu
  have hs : ∀ a, FB.IsCoord (u ≫ (A.t.act.act (x a) ≫ φ a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FA hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, (A.t.act.act (x a) ≫ φ a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • M e) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have h1 := hpow n
  rw [← comp_pow, hfn] at h1
  rw [((integral_tangent_coordinates K _ FB).1 _ h1.1).unique h1 (hprod Finset.univ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← algebraMap_smul K (τ (x a)) e, map_smul]

end Diff

theorem exists_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
    {ρ : 𝓞 K} {A B : PAT H (Sp (𝓞 K))} {p q : ℕ} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (hA : HasType H A.t.act ρ 1 0)
    (hB : HasType H B.t.act ρ p q) {n : ℕ} (hn : p + q < n) {ψ : Fin n → (A.t.G ⟶ B.t.G)}
    (hψ : ∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) :
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  let β : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)
  have hβ : Function.Injective β := σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨A', mA, -⟩ := PAT.exists_pullback E H _ _ (spMap β) A
  obtain ⟨B', mB, -⟩ := PAT.exists_pullback E H _ _ (spMap β) B
  choose ψ' hψ' e using fun i => exists_linear_over mA mB (hψ i)
  obtain ⟨x, hx, h⟩ := _root_.GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure E H (β ρ) A' B' p q (by rw [← map_pow, hρ, map_neg, map_natCast])
    ((hasType_baseChange E H _ _ β _ _ mA ρ 1 0).1 hβ hA) ((hasType_baseChange E H _ _ β _ _ mB ρ p q).1 hβ hB)
    n hn ψ' hψ'
  exact ⟨x, hx, rel_descend mA mB hβ e x h⟩

theorem eigLat_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ ≤ Submodule.span (𝓞 K)
            {w | ∃ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE w hw
  obtain ⟨K', _, _, j, ω, C, A', B', mA, mB, DA, DB, hA, hB, rA, -, ⟨tA⟩, ⟨tB⟩⟩ :=
    _root_.GlobalTheory.CM.TenPair.exists_isTen_pair E H K ρ (X.A true) X.B 1 p X.ρ_sq X.typeP X.typeB
  obtain ⟨n, f', g', hf', hg', hfg⟩ := _root_.GlobalTheory.CM.isTen_retract_of_rank_one E H _ ω C A' B' DA DB hA hB rA tA tB
  have hj : Function.Injective (RingOfIntegers.mapRingHom j) := fun a b h => by
    apply RingOfIntegers.ext
    apply j.injective
    exact congrArg (fun x : 𝓞 K' => (x : K')) h
  have hφ : ∀ a, Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X a) := fun a => X.lin (Sum.inl a)
  choose φ' hφ' eφ using fun a => exists_linear_over mA mB (hφ a)
  have key : ∀ i, ∃ f : (X.A true).t.G ⟶ X.B.t.G, Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
      (f' i).left ≫ mB.φ = mA.φ ≫ f.left ∧ ∃ N : ℕ, 0 < N ∧ ∃ y : Fin p → 𝓞 E,
        f ^ N = ∏ a, ((X.A true).t.act.act (y a) ≫ phiP X a) := fun i => by
    obtain ⟨x, hx, h⟩ := exists_rel (ρ := RingOfIntegers.mapRingHom j ρ) (A := A') (B := B') (p := p) (q := 0)
      (by rw [← map_pow, X.ρ_sq, map_neg, map_natCast])
      ((hasType_baseChange E H _ _ _ _ _ mA ρ 1 0).1 hj X.typeP)
      ((hasType_baseChange E H _ _ _ _ _ mB ρ p 0).1 hj X.typeB) (Nat.lt_succ_self p)
      (ψ := Fin.cons (f' i) φ') (Fin.cases (hf' i) hφ')
    rw [Fin.prod_univ_succ] at h
    simp only [Fin.cons_zero, Fin.cons_succ] at h
    have h₀ : x 0 ≠ 0 := fun h₀ => by
      haveI := (hf' i).isMonHom
      rw [h₀, Serre.act_zero, MonObj.one_comp, _root_.one_mul] at h
      have hs := _root_.GlobalTheory.FlatCM.HomIndep.phiP_independent E H K ρ σ₁ p 0 X _ (rel_descend mA mB hj eφ _ h)
      exact hx (funext (Fin.cases h₀ fun a => congrFun hs a))
    obtain ⟨N, hN, y, hy⟩ := exists_pow_eq (hf' i) hφ' h₀ h
    obtain ⟨f, hf, e₁, e₂⟩ := _root_.GlobalTheory.eq_pow_of_baseChange_eq_pow E H K K' j (X.A true) X.B A' B' mA mB _ (f' i) N hN (isLinearHom_prod X y) (hf' i)
      (by rw [hy]; exact comb_over mA mB eφ y)
    exact ⟨f, hf, e₂, N, hN, y, e₁⟩
  choose f hf ef N hN y hy using key
  choose M hM using fun i =>
    (DiffCoord.existsUnique_isDiffOf K _ FP _ FB (f i) (hf i).isMonHom).1.exists
  refine _root_.GlobalTheory.FlatDescent.mem_of_mem_span_map K K' j _ _ w (Submodule.span_mono (Set.image_mono ?_)
    (_root_.GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff E H K K' j (X.A true) X.B A' B' mA mB n f f' g' hf hf' hg' ef hfg FP FB M hM τ w hw))
  rintro _ ⟨i, e, he, rfl⟩
  have hE : (N i : E) ≠ 0 := Nat.cast_ne_zero.2 (hN i).ne'
  have hK : (N i : K) ≠ 0 := Nat.cast_ne_zero.2 (hN i).ne'
  refine Submodule.subset_span ⟨fun a => (y i a : E) / N i,
    Submodule.subset_span ⟨N i, hN i, y i, fun a => by field_simp, f i, hf i, hy i⟩, e, he, ?_⟩
  refine smul_right_injective _ hK ?_
  show (N i : K) • M i e = (N i : K) • _
  rw [Nat.cast_smul_eq_nsmul, smul_diff_eq hMP (hM i) (hy i) he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, map_div₀, hτE, map_natCast, mul_div_cancel₀ _ hK]

end GlobalTheory.FlatCM.HomLat.LieSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  have h1 : ∀ z : AF F, At (evFin F v) z → GlobalTheory.LatVac.liftV v 1 * z = z := by
    intro z hz
    have := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul] at this
    linear_combination -this
  have h2 := GlobalTheory.LatVac.at_liftV v 1 (b - GlobalTheory.LatVac.liftV v (evFin F v b))
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul] at h2
  have h3 := h1 _ (GlobalTheory.LatVac.at_liftV v (evFin F v b))
  linear_combination h2 + h3

omit [NumberField E] in
theorem smul_eq_map (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem eq_zero_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (ha : GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = a) (h1 : piW t a = 0) (h2 : piW (t.comp σ) a = 0) : a = 0 := by
  have h0 : compFin F E v a = 0 :=
    split_ext h t (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  rw [← ha, smul_eq_map, h0, map_zero]

omit [NumberField E] in
theorem one_sub_smul {m n : Type} {v : Pl (F := F)} {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) :
    (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • u = 0 :=
  hu _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])

theorem smul_eq_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {m n : Type}
    {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) (g : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (h1 : ∀ i j, piW t g * piW t (u i j) = 0) (h2 : ∀ i j, piW (t.comp σ) g * piW (t.comp σ) (u i j) = 0) :
    g • u = 0 := by
  have h0 := one_sub_smul hu
  rw [sub_smul, one_smul, sub_eq_zero] at h0
  ext i j
  have h3 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • u i j = u i j := (congrFun (congrFun h0 i) j).symm
  refine eq_zero_of_piW h t ?_ ?_ ?_
  · rw [Matrix.smul_apply, smul_comm, h3]
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, h1]
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, h2]

theorem swap_at_acts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  intro F E _ _ _ _ _ σ h a' d J v t f hf _ _ ht htσ w hw
  refine ⟨?_, ?_⟩
  · intro r hr
    have h1 : r * GlobalTheory.LatVac.liftV v (1 : Fv F v) = 0 := GlobalTheory.LatVac.at_liftV v 1 r hr
    have h2 : r • f = 0 := by rw [← hf, smul_smul, h1, zero_smul]
    have h3 : r * (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) = r := by rw [mul_sub, h1, mul_one, sub_zero]
    rw [hw, smul_sub, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, smul_smul, h3,
      ← smul_assoc, h2, zero_smul, smul_zero, sub_self]
  · intro u₁ u₂ hu₁ hu₂
    have hact : actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (f • u₂) (f • u₁) := by
      unfold actB
      rw [hw, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, one_sub_smul hu₁,
        one_sub_smul hu₂, zero_add, add_zero]
    have hneg : ∀ u : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → u.map (piW t) = 0 → f • u = -u := by
      intro u hu h0
      have := smul_eq_of_piW h t hu (f + 1)
        (fun i j => by rw [show piW t (u i j) = 0 from congrFun (congrFun h0 i) j, mul_zero])
        (fun i j => by rw [map_add (f := _), htσ, map_one, neg_add_cancel, zero_mul])
      rwa [add_smul, one_smul, add_eq_zero_iff_eq_neg] at this
    have hpos : ∀ u : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → f • u = u := by
      intro u hu h0
      have := smul_eq_of_piW h t hu (f - 1)
        (fun i j => by rw [map_sub, ht, map_one, sub_self, zero_mul])
        (fun i j => by rw [show piW (t.comp σ) (u i j) = 0 from congrFun (congrFun h0 i) j, mul_zero])
      rwa [sub_smul, one_smul, sub_eq_zero] at this
    exact ⟨fun h1 h2 => by rw [hact, hneg _ hu₁ h1, hneg _ hu₂ h2],
      fun h1 h2 => by rw [hact, hpos _ hu₁ h1, hpos _ hu₂ h2]⟩

end GlobalTheory.SwapAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorLeftPartialPure
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section
namespace GlobalTheory.DblEval.PartLStr

theorem mul_blocks_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {κ κ' : Type} {a : (κ → X) → ℂ} {b : (κ' → X) → ℂ}
    (ha : a ∈ SB (κ → X)) (hb : b ∈ SB (κ' → X)) :
    (fun z : κ ⊕ κ' → X => a (z ∘ Sum.inl) * b (z ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → X) := by
  have hc : Continuous fun p : (κ → X) × (κ' → X) => Sum.elim p.1 p.2 :=
    continuous_pi fun k => by
      cases k
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]
  refine ⟨(ha.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inl) (by fun_prop)).mul
    (hb.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inr) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((ha.2.isCompact.prod hb.2.isCompact).image hc) fun z hz => ?_
  by_cases h1 : z ∘ Sum.inl ∈ tsupport a
  · by_cases h2 : z ∘ Sum.inr ∈ tsupport b
    · exact absurd ⟨(z ∘ Sum.inl, z ∘ Sum.inr), ⟨h1, h2⟩, Sum.elim_comp_inl_inr z⟩ hz
    · simp only [image_eq_zero_of_notMem_tsupport h2, mul_zero]
  · simp only [image_eq_zero_of_notMem_tsupport h1, zero_mul]

theorem glue_sumComm {R κ κ' : Type} (a : κ' → R) (x : κ → R) :
    GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') a x = Sum.elim x a := by
  funext k; cases k <;> rfl

theorem exists_partL_pureA : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ']
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e →
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ₁ ⊕ κ' → Af F),
      ∀ f : SInf F (κ ⊕ κ'), partL e (pureA F f g) = pureA F (P f) g₁ := by
  intro F _ _ κ κ₁ κ' _ _ _ e he
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨ei, ev, hSB, hstd, hpure⟩ := he
  let eq₀ : (κ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.sumArrowLequivProdArrow κ κ' ℝ _).toContinuousLinearEquiv
  let eq₁ : (κ₁ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ₁ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.sumArrowLequivProdArrow κ₁ κ' ℝ _).toContinuousLinearEquiv
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.schwartz_operator_parametric_extension (V' := κ' → mixedEmbedding.mixedSpace F) ei
  let P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ') := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₁).comp
    (P₀.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₀.symm))
  have hP : ∀ (f : SInf F (κ ⊕ κ')) (y : κ₁ → mixedEmbedding.mixedSpace F) (x' : κ' → mixedEmbedding.mixedSpace F)
      (h : SInf F κ), (∀ x, h x = f (Sum.elim x x')) → P f (Sum.elim y x') = ei h y := by
    intro f y x' h hh
    have h1 : eq₁ (Sum.elim y x') = (y, x') := rfl
    simp only [P, ContinuousLinearMap.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h1]
    exact hP₀ _ x' h (fun x => (hh x).trans rfl) y
  refine ⟨P, fun g hg => ?_⟩
  have hE : ∀ (z : AF F) (v : Pl (F := F)), evFin F v z = evalV F v z.2 := fun _ _ => rfl
  obtain ⟨m, a, b, ha, hb, hab⟩ := GlobalTheory.T.schwartz_bruhat_sum_split_tensor g hg
  choose n φ hφSB hφstd hφ using fun k => GlobalTheory.T.adelic_schwartz_function_factorizable_sum (a k) (ha k)
  let g₁ : (κ₁ ⊕ κ' → Af F) → ℂ := ∑ k, ∑ j : Fin (n k), fun z =>
    (∏ᶠ v, ev v (φ k j v) fun i => evalV F v (z (Sum.inl i))) * b k (z ∘ Sum.inr)
  have hev : ∀ k j, ∀ᶠ v in cofinite, ev v (φ k j v) = stdInd F κ₁ v := fun k j => by
    filter_upwards [hstd, hφstd k j] with v h1 h2
    rw [h2, h1]
  refine ⟨g₁, Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ =>
    mul_blocks_mem_SB (GlobalTheory.AdelicCoordSB.finprod_mem_SB F κ₁ _ (fun v => hSB v _ (hφSB k j v)) (hev k j)) (hb k), ?_⟩
  intro f
  funext y
  obtain ⟨T, hT⟩ := GlobalTheory.ThK.Adapt.exists_slice (κ := κ ⊕ κ') (κ₁ := κ) (Equiv.sumComm κ κ')
    (fun i => evI F (y (Sum.inr i)))
  have hh : ∀ x, T f x = f (Sum.elim x fun i => evI F (y (Sum.inr i))) := fun x => by
    rw [hT, glue_sumComm]
  have hslice : (fun x : κ → AF F => pureA F f g (Sum.elim x (y ∘ Sum.inr))) =
      ∑ k, ∑ j : Fin (n k), b k (fun i => (y (Sum.inr i)).2) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) (φ k j) := by
    funext x
    have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (Sum.elim x (y ∘ Sum.inr) i).1) =
        Sum.elim (fun i => evI F (x i)) fun i => evI F (y (Sum.inr i)) := by
      funext i; cases i <;> rfl
    have e2 : (fun i => (Sum.elim x (y ∘ Sum.inr) i).2) = Sum.elim (fun i => (x i).2) fun i => (y (Sum.inr i)).2 := by
      funext i; cases i <;> rfl
    simp only [pureA, e1, e2, hab, hφ, ← hh, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hE]
    ring
  have ey : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) =
      Sum.elim (fun i => evI F (y (Sum.inl i))) fun i => evI F (y (Sum.inr i)) := by
    funext i; cases i <;> rfl
  show e (fun x => pureA F f g (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl) = pureA F (P f) g₁ y
  rw [hslice]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hpure (T f) _ (hφSB _ _) (hφstd _ _), pureA, ey,
    hP f _ _ (T f) hh, g₁, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hE, Function.comp_def]
  ring
end GlobalTheory.DblEval.PartLStr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixAdelicDecompositionAtFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_adelic_decomposition_at_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → Y.L.IsFullLattice E → ∀ (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) z → ∃ X₀ : Matrix (Fin n) (Fin d) E, z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  first
  | exact @GlobalTheory.LatPtDecomp.decomp
  | intro F E _ _ _ _ _ n d X Y hX hY v z hz
    exact GlobalTheory.LatPtDecomp.decomp F E X Y hX.toIsLattice hY.toIsLattice v z hz
end

