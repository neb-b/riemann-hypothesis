module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
section
set_option autoImplicit false
noncomputable section
open Module

namespace GlobalTheory.PolExistsRing

theorem mem_of_annihilates {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (ψ : LinearMap.BilinForm R V) [hψ : ψ.IsPerfPair] (W W' : Submodule R V) (hc : IsCompl W W')
    [Module.Finite R W'] [Module.Projective R W'] [Module.Finite R (Dual R W)]
    [Module.Projective R (Dual R W)]
    (hrk : ∀ p : PrimeSpectrum R, rankAtStalk W' p = rankAtStalk (Dual R W) p)
    (hiso : ∀ f ∈ W, ∀ g ∈ W, ψ f g = 0) (f : V) (hf : ∀ g ∈ W, ψ f g = 0) : f ∈ W := by
  let Φ : W' →ₗ[R] Dual R W := W.subtype.dualMap ∘ₗ ψ ∘ₗ W'.subtype
  let e := Submodule.prodEquivOfIsCompl W W' hc
  have hdec : ∀ v : V, (((e.symm v).1 : W) : V) + ((e.symm v).2 : V) = v := fun v ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' W W' hc, LinearEquiv.apply_symm_apply]
  have hΦ' : ∀ v : V, ∀ g : W, Φ (e.symm v).2 g = ψ v g := by
    intro v g
    have h := congrArg (fun u ↦ ψ u g) (hdec v)
    simp only [map_add (f := _), LinearMap.add_apply] at h
    rw [hiso _ (Submodule.coe_mem _) g g.2, zero_add] at h
    simpa [Φ] using h
  have hΦ : Function.Surjective Φ := by
    intro l
    obtain ⟨v, hv⟩ := hψ.bijective_left.2 (l ∘ₗ W.projectionOnto W' hc)
    refine ⟨(e.symm v).2, LinearMap.ext fun g ↦ ?_⟩
    rw [hΦ' v g, hv]
    simp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Φ LinearMap.id hΦ
  have hsinj : Function.Injective s := fun x y h ↦ by
    have := congrArg Φ h
    rwa [← LinearMap.comp_apply, hs, ← LinearMap.comp_apply, hs] at this
  have hc2 : IsCompl (LinearMap.range s) (LinearMap.ker Φ) := by
    have h := LinearMap.isCompl_of_proj (f := s.rangeRestrict ∘ₗ Φ) (fun x ↦ by
      obtain ⟨_, y, rfl⟩ := x
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply]
      rw [← LinearMap.comp_apply Φ s, hs, LinearMap.id_apply])
    have hk : LinearMap.ker s.rangeRestrict = ⊥ := by
      rw [LinearMap.ker_rangeRestrict]; exact LinearMap.ker_eq_bot.2 hsinj
    rwa [LinearMap.ker_comp_of_ker_eq_bot _ hk] at h
  let ep := Submodule.prodEquivOfIsCompl _ _ hc2
  let es : Dual R W ≃ₗ[R] LinearMap.range s := LinearEquiv.ofInjective s hsinj
  haveI : Module.Finite R (LinearMap.range s) := Module.Finite.equiv es
  haveI : Module.Projective R (LinearMap.range s) := Module.Projective.of_equiv es
  let pr : W' →ₗ[R] LinearMap.ker Φ := LinearMap.snd R _ _ ∘ₗ ep.symm.toLinearMap
  have hpr : pr ∘ₗ (LinearMap.ker Φ).subtype = LinearMap.id := LinearMap.ext fun x ↦ by
    simp [pr, ep, Submodule.prodEquivOfIsCompl_symm_apply_right]
  haveI : Module.Finite R (LinearMap.ker Φ) :=
    Module.Finite.of_surjective pr (fun x ↦ ⟨x, by simpa using congrArg (fun m ↦ m x) hpr⟩)
  haveI : Module.Projective R (LinearMap.ker Φ) := Module.Projective.of_split _ _ hpr
  have hr0 : rankAtStalk (R := R) (LinearMap.ker Φ) = 0 := by
    have h1 := rankAtStalk_eq_of_equiv ep
    rw [rankAtStalk_prod, rankAtStalk_eq_of_equiv es.symm] at h1
    funext p
    have := congrFun h1 p
    simp only [Pi.add_apply] at this
    rw [hrk p] at this
    simp only [Pi.zero_apply]
    omega
  haveI := (rankAtStalk_eq_zero_iff_subsingleton).1 hr0
  have hb : (e.symm f).2 ∈ LinearMap.ker Φ := LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ by
    rw [hΦ' f g]; exact hf g g.2)
  have h0 : (e.symm f).2 = 0 := by
    have := Subsingleton.elim (⟨_, hb⟩ : LinearMap.ker Φ) 0
    simpa using congrArg Subtype.val this
  rw [← hdec f, h0]
  simp

theorem mem_of_annihilates_dual {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ψ : LinearMap.BilinForm R (Dual R M)) [ψ.IsPerfPair] (F N : Submodule R M) (hc : IsCompl F N)
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R F] [Module.Projective R F] (g : ℕ)
    (hM : ∀ p : PrimeSpectrum R, rankAtStalk M p = 2 * g)
    (hF : ∀ p : PrimeSpectrum R, rankAtStalk F p = g)
    (hiso : ∀ f ∈ F.dualAnnihilator, ∀ h ∈ F.dualAnnihilator, ψ f h = 0) (f : Dual R M)
    (hf : ∀ h ∈ F.dualAnnihilator, ψ f h = 0) : f ∈ F.dualAnnihilator := by
  let e := Submodule.prodEquivOfIsCompl F N hc
  have hdec : ∀ x : M, (((e.symm x).1 : F) : M) + ((e.symm x).2 : M) = x := fun x ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' F N hc, LinearEquiv.apply_symm_apply]
  have hc' : IsCompl F.dualAnnihilator N.dualAnnihilator := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro φ ⟨h1, h2⟩
      rw [Submodule.mem_bot]
      refine LinearMap.ext fun x ↦ ?_
      rw [← hdec x, map_add (f := _), (Submodule.mem_dualAnnihilator _).1 h1 _ (Submodule.coe_mem _),
        (Submodule.mem_dualAnnihilator _).1 h2 _ (Submodule.coe_mem _)]
      simp
    · rw [codisjoint_iff_le_sup]
      intro φ _
      rw [Submodule.mem_sup]
      refine ⟨φ ∘ₗ N.subtype ∘ₗ LinearMap.snd R F N ∘ₗ e.symm.toLinearMap, ?_,
        φ ∘ₗ F.subtype ∘ₗ LinearMap.fst R F N ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine LinearMap.ext fun x ↦ ?_
        conv_rhs => rw [← hdec x]
        simp [add_comm]
  let eW' : Dual R F ≃ₗ[R] N.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl N F hc.symm).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator N)
  let eW : Dual R N ≃ₗ[R] F.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl F N hc).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator F)
  have hpN : (N.projectionOnto F hc.symm) ∘ₗ N.subtype = LinearMap.id :=
    LinearMap.ext fun x ↦ Submodule.projectionOnto_apply_left hc.symm x
  haveI : Module.Projective R N := Module.Projective.of_split _ _ hpN
  haveI : Module.Finite R N := Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective hc.symm)
  let eN : Dual R F.dualAnnihilator ≃ₗ[R] N := eW.dualMap.trans (Module.evalEquiv R N).symm
  haveI : Module.Finite R N.dualAnnihilator := Module.Finite.equiv eW'
  haveI : Module.Projective R N.dualAnnihilator := Module.Projective.of_equiv eW'
  haveI : Module.Finite R (Dual R F.dualAnnihilator) := Module.Finite.equiv eN.symm
  haveI : Module.Projective R (Dual R F.dualAnnihilator) := Module.Projective.of_equiv eN.symm
  refine mem_of_annihilates ψ _ _ hc' (fun p ↦ ?_) hiso f hf
  rw [← rankAtStalk_eq_of_equiv eW', rankAtStalk_eq_of_equiv eN, GlobalTheory.TopExt.rankAtStalk_dual F p, hF p]
  have h1 := congrFun (rankAtStalk_eq_of_equiv e) p
  rw [rankAtStalk_prod, Pi.add_apply, hM p, hF p] at h1
  omega

end GlobalTheory.PolExistsRing

namespace GlobalTheory.PolExistsRing

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem polForm_exists : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  intro P E _ _ _ H Dw l Xo S _ x A _ π hπ
  open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits
    CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
  have hA : IsAbelianScheme A := by
    have hG := ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hcomm : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
        ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hcomm, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 S A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso S ⊥ (dp0 S) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 S) (𝟙 _) A
    rw [show prim (dp0 S) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 S) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 S) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (GlobalTheory.PolExists.isGen_self hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 S A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩

  obtain ⟨hfin, hproj, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, ⟨N, hN⟩, hFfin, hFproj, hFrk⟩ := P.2.1 S A _ hA gA
  exact mem_of_annihilates_dual (wedgeForm (dp0 S) (𝟙 _) A a' b') (PrimitiveSubmodule A) N hN _ hrk hFrk hiso f hf

end GlobalTheory.PolExistsRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScal
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.ScalApprox

variable {K : Type} [Field K] [NumberField K]

theorem mem_pow_iff (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) (n : ℕ) :
    r ∈ w.asIdeal ^ n ↔ (n : ℤ) ≤ vAdd w (r : K) := by
  have h0 : w.intValuation r ≠ 0 := w.intValuation_ne_zero r hr
  rw [← w.intValuation_le_pow_iff_mem, vAdd, HeightOneSpectrum.valuation_of_algebraMap]
  conv_lhs => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp]
  omega

theorem vAdd_div (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x / y) = vAdd w x - vAdd w y := by
  have hx' : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : w.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [vAdd, vAdd, vAdd, map_div₀, WithZero.log_div hx' hy']
  ring

end GlobalTheory.RefSum.ScalApprox

namespace GlobalTheory.RefSum.ScalApprox

variable {K : Type} [Field K] [NumberField K]

theorem exists_scal : ∀ (K : Type) [Field K] [NumberField K] (ρ : HeightOneSpectrum (𝓞 K) → ℝ),
    (Function.support ρ).Finite → ∀ w : HeightOneSpectrum (𝓞 K), ∃ a : K, a ≠ 0 ∧
      (vAdd w a : ℝ) = -(⌊ρ w⌋ : ℝ) ∧ ∀ w', 0 ≤ (vAdd w' a : ℝ) + ρ w' := by
  intro K _ _ ρ hρ w
  classical
  set S : Finset (HeightOneSpectrum (𝓞 K)) := insert w hρ.toFinset with hS

  have hne : ∀ v : HeightOneSpectrum (𝓞 K), ∃ e : 𝓞 K, e ∈ v.asIdeal ∧ e ≠ 0 := fun v =>
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose e he he0 using hne
  set N : ℕ := ∑ v ∈ S, (⌊ρ v⌋).toNat with hN
  set c : 𝓞 K := (∏ v ∈ S, e v) ^ N with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun v _ => he0 v)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hcS : ∀ v ∈ S, -⌊ρ v⌋ + vAdd v (c : K) ≥ 0 := by
    intro v hv
    have h1 : ∏ u ∈ S, e u ∈ v.asIdeal := by
      obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem e hv
      rw [ht]; exact Ideal.mul_mem_right _ _ (he v)
    have h2 : c ∈ v.asIdeal ^ N := Ideal.pow_mem_pow h1 N
    have h3 := (mem_pow_iff v hc0 N).1 h2
    have h4 : (⌊ρ v⌋).toNat ≤ N := Finset.single_le_sum (f := fun u => (⌊ρ u⌋).toNat)
      (fun _ _ => Nat.zero_le _) hv
    have h5 : ⌊ρ v⌋ ≤ ((⌊ρ v⌋).toNat : ℤ) := Int.self_le_toNat _
    omega
  have hfc := GlobalTheory.FlatLine.finite_vAdd hcK
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ hfc.toFinset with hT
  set E : HeightOneSpectrum (𝓞 K) → ℕ := fun v => (-⌊ρ v⌋ + vAdd v (c : K)).toNat with hE
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπpow : ∀ n : ℕ, w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := fun n => by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have hwT : w ∈ T := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v => v.asIdeal) (fun v => if v = w then E w + 1 else E v)
    (fun v _ => v.prime) (fun v _ u _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 K)) = w then π ^ E w else 0)
  have hbw := hb w hwT
  simp only [if_true] at hbw
  have hπE : π ^ E w ∈ w.asIdeal ^ E w := (w.intValuation_le_pow_iff_mem _ _).1 (le_of_eq (hπpow _))
  have hπE1 : π ^ E w ∉ w.asIdeal ^ (E w + 1) := by
    rw [← w.intValuation_le_pow_iff_mem, hπpow, WithZero.exp_le_exp]
    push_cast; omega
  have hbw1 : b ∈ w.asIdeal ^ E w := by
    have := Ideal.pow_le_pow_right (I := w.asIdeal) (Nat.le_succ (E w)) hbw
    simpa using add_mem this hπE
  have hbw2 : b ∉ w.asIdeal ^ (E w + 1) := fun h => hπE1 (by simpa using sub_mem h hbw)
  have hb0 : b ≠ 0 := by rintro rfl; exact hbw2 (Submodule.zero_mem _)
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have hvw : vAdd w (b : K) = E w := by
    have h1 := (mem_pow_iff w hb0 _).1 hbw1
    have h2 := mt (mem_pow_iff w hb0 (E w + 1)).2 hbw2
    push_cast at h2; omega
  have hball : ∀ v, (E v : ℤ) ≤ vAdd v (b : K) := by
    intro v
    by_cases hv : v ∈ T
    · by_cases hvw' : v = w
      · subst hvw'; rw [hvw]
      · have := hb v hv
        simp only [hvw', if_false, sub_zero] at this
        exact (mem_pow_iff v hb0 _).1 this
    · have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
      have hρv : ρ v = 0 := by
        by_contra h; exact hvS (Finset.mem_insert_of_mem (hρ.mem_toFinset.2 h))
      have hcv : vAdd v (c : K) = 0 := by
        by_contra h
        exact hv (Finset.mem_union_right _ (hfc.mem_toFinset.2 (by simpa using h)))
      have : E v = 0 := by simp [hE, hρv, hcv]
      rw [this]; exact (mem_pow_iff v hb0 0).1 (by simp)
  refine ⟨(b : K) / c, div_ne_zero hbK hcK, ?_, fun v => ?_⟩
  · rw [vAdd_div w hbK hcK, hvw]
    have := hcS w (Finset.mem_insert_self _ _)
    have h6 : ((E w : ℕ) : ℤ) = -⌊ρ w⌋ + vAdd w (c : K) := Int.toNat_of_nonneg this
    rw [h6]; push_cast; ring
  · rw [vAdd_div v hbK hcK]
    have h1 := hball v
    have h2 : -⌊ρ v⌋ + vAdd v (c : K) ≤ ((E v : ℕ) : ℤ) := Int.self_le_toNat _
    have h3 : -⌊ρ v⌋ ≤ vAdd v (b : K) - vAdd v (c : K) := by omega
    have h4 : (⌊ρ v⌋ : ℝ) ≤ ρ v := Int.floor_le _
    have h5 : ((-⌊ρ v⌋ : ℤ) : ℝ) ≤ ((vAdd v (b : K) - vAdd v (c : K) : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h5 ⊢
    linarith

end GlobalTheory.RefSum.ScalApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGenerated
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory


open GlobalTheory.ZeroDimSystem in
theorem exists_sec_nonzero_on_finite_of_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∀ S : Set X, S.Finite → ∃ s : L.Sec, ∀ x ∈ S, x ∈ nonzeroLocus s := by
  intro k _ _ X _ p L _ n u hu S hS
  classical
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hne : ∀ x ∈ hS.toFinset, vanishAt (k := k) u x ≠ ⊤ := fun x _ h => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
    exact single_notMem_vanishAt (k := k) u hi (h.symm ▸ Submodule.mem_top)
  have h := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (E := Fin n → k)
    (s := hS.toFinset.image (vanishAt (k := k) u)) (by
      rw [Finset.mem_image]
      rintro ⟨x, hx, h⟩
      exact hne x hx h)
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 h
  refine ⟨comb u c, fun x hx => ?_⟩
  by_contra hxc
  exact hc (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hS.mem_toFinset.2 hx)))
    ((mem_vanishAt u x c).2 hxc))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisation
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.CovTop.SupImage

theorem linearIndependent_of_form {K L V : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module L V]
    [IsScalarTower K L V] {S : Submodule K V} {n : ℕ} {b : Fin n → V} (hK : LinearIndependent K b)
    (hS : Submodule.span K (Set.range b) = S) (hL : LinearIndependent L b) {ι : Type} {c : ι → S}
    (hc : LinearIndependent K c) : LinearIndependent L fun k => (c k : V) := by
  subst hS
  let B := (Module.Basis.span hK).baseChange L
  let φ : L ⊗[K] Submodule.span K (Set.range b) →ₗ[L] V := (Submodule.span K (Set.range b)).subtype.liftBaseChange L
  have hB : φ ∘ B = b := by
    funext k
    simp [B, φ, Module.Basis.span_apply]
  have hφ : Function.Injective φ :=
    LinearMap.injective_of_linearIndependent (by rw [B.span_eq]) (hB ▸ hL)
  have h1 : LinearIndependent L fun k => (1 : L) ⊗ₜ[K] c k := Module.Flat.linearIndependent_one_tmul hc
  have h2 := h1.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have h3 : (φ ∘ fun k => (1 : L) ⊗ₜ[K] c k) = fun k => (c k : V) := by
    funext k
    simp [φ]
  exact h3 ▸ h2


set_option maxHeartbeats 1000000 in
theorem exists_emb_image_latW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), ∃ ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL), (∀ (f : VK fw i), ∃ h : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ι f = ((fw.e i ⟨f, h⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) ∧ (∀ (n : ℕ) (b : Fin n → VK fw i), LinearIndependent T.Q.c.F b → LinearIndependent D.what₂.LL (fun k => ι (b k))) ∧ ι '' (latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) : Set (VK fw i)) = ((R.FW i).MK : Set (Fin (R.nW i) → D.what₂.LL)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i
  have hE : VK fw i = T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := cuspW_wtZ _ _
  let e : VK fw i ≃ₗ[T.Q.c.F] (R.FW i).WK := (LinearEquiv.ofEq _ _ hE).trans (fw.e i)
  have he : ∀ f : VK fw i, e f = fw.e i ⟨f, hE ▸ f.2⟩ := fun _ => rfl
  let ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL) :=
    { toFun := fun f => (e f : Fin (R.nW i) → D.what₂.LL)
      map_add' := fun f g => by rw [map_add (f := _)]; rfl
      map_smul' := fun a f => by rw [map_smul, algebraMap_smul]; rfl }
  have key : ∀ f : VK fw i, f ∈ latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) ↔ ι f ∈ (R.FW i).MK := fun f => by
    have en := fun la y => fw.nrm_eq i la y ⟨f.1, hE ▸ f.2⟩
    constructor
    · intro hf
      refine ⟨(e f).2, fun la y => (en la y).trans_le ?_⟩
      exact (T.nrmM_le_one_iff _ la _ _).2 (hf la _ (fw.pt i la y).2)
    · rintro ⟨_, hf⟩ la v hv
      obtain ⟨y, hy⟩ := (fw.pt i la).surjective ⟨v, hv⟩
      have h2 := (en la y).symm.trans_le (hf la y)
      rw [hy] at h2
      exact (T.nrmM_le_one_iff _ la ⟨v, hv⟩ _).1 h2
  refine ⟨ι, fun f => ⟨hE ▸ f.2, rfl⟩, fun n b hb => ?_, ?_⟩
  · obtain ⟨m, c, -, h1, h2, h3, -⟩ := fw.ks i
    exact linearIndependent_of_form h1 h2 h3 (hb.map' e.toLinearMap e.ker)
  · ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (key f).1 hf
    · intro hx
      obtain ⟨f, hf⟩ := e.surjective ⟨x, hx.1⟩
      have hx' : ι f = x := congrArg Subtype.val hf
      exact ⟨f, (key f).2 (hx' ▸ hx), hx'⟩

end GlobalTheory.CovTop.SupImage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledEigenfunctionsLineVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_doubledEigenfunctions_line_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → ∃ c : ℂ, φ = c • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))) := by
  first | exact @GlobalTheory.VDblLine.vdbl_line | exact GlobalTheory.VDblLine.vdbl_line | (intros; apply GlobalTheory.VDblLine.vdbl_line <;> assumption)
end

