module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiCompEndomorphismEqPowOfPullbackIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpDualNumber
section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem rigidity_dualNumber {K : Type} [Field K] (A₀ : Over (Sp K)) (A' G' : Over (Sp (DualNumber K))) [GrpObj A']
    [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hj : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI := subsingleton_sp_dualNumber K
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [Field K] {x₀ : Sp K ⟶ Xo.X} {x' : Sp (DualNumber K) ⟶ Xo.X}
  {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {π : A.left ⟶ Xo.univ.t.G.left}
  {π' : A'.left ⟶ Xo.univ.t.G.left} {i : A.left ⟶ A'.left} {q : A'.left ⟶ A.left}

theorem act_const (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg : g ≫ π' = m.cm.F) (hgw : g ≫ A'.hom = o.t.G.hom) (a : 𝓞 E) :
    (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ x₀ := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' : IsAbelianScheme A' := by
    have hG := ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hc : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ'.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hπ'.2 T x y (pushPt hπ'.1.w x) (pushPt hπ'.1.w y) rfl rfl,
        ← hπ'.2 T y x (pushPt hπ'.1.w y) (pushPt hπ'.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ'.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ'.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ'.1 hG.geomConnected⟩
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := rigidity_dualNumber A A' A' i α δ hA' hi.1 (e1.trans e2.symm)
    (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]

theorem cub_const (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg1 : g ≫ π' = m.cm.F) (hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π)) :
    (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K x₀ x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

theorem objMap_const (c : Coeff l) [Algebra c.F K] (hx : GlobalTheory.DeRham.epsRed K ≫ x' = x₀)
    (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') : Nonempty (ObjMap o Xo.univ (constPt x')) := by
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ x₀ = constPt x' := by
    rw [← hx]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := act_const hi hπ hπ' hiπ hiq hq o m g hg hgw
    lin := cub_const c hi hπ hπ' hiπ hiq hq o m g hg hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

theorem eq_constPt (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q) : x' = constPt x' := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  exact Xo.unram K x' o ⟨m⟩ (objMap_const c rfl hi (hi.comp hπ') hπ' rfl hiq hq o m)

end GlobalTheory.InteriorKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySignsTwoTorsionRelationOfLbIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SignSym

section Move
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_gen_onA (U : UnifPre I D A G) {n : ℕ} (fG : Fin n → (G ⟶ G)) (fA : Fin n → (A.A ⟶ A.A))
    (hf : ∀ k, (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = U.gen.hom ≫ fA k) (ε : Fin n → ℤ)
    (φ : Fin n → (G.left ⟶ G.left)) (hφ : ∀ k, φ k = (fG k).left)
    (φA : Fin n → (A.A.left ⟶ A.A.left)) (hφA : ∀ k, φA k = (fA k).left)
    (t : LB.Gen (LB.LinComb U.LG.L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb A.L φA ε), a.IsGen := by
  obtain ⟨w, hw⟩ := U.ext
  let π : A.A ⟶ (Over.pullback (jK R)).obj G := U.gen.inv
  obtain ⟨a, ha, -⟩ := H1.exists_gen_move U.LG.isLB (DVR.linComb_isLB _ A.isLB _ _) w ((isGen_iff w).1 hw)
    φ (fun k => (π ≫ (Over.pullback (jK R)).map (fG k)).left) ε (π.left ≫ pullback.fst G.hom (jK R))
    (fun k => by
      rw [hφ k]
      exact (Category.assoc _ _ _).trans ((congrArg (π.left ≫ ·) (pullback.lift_fst _ _ _)).trans
          (Category.assoc _ _ _).symm)) t ht
  obtain ⟨b, hb⟩ := PsiPull.exists_gen_flat _ _ _ a ha
  obtain ⟨α, hα, -⟩ := exists_gen A.isLB (φ' := φA) (ε' := ε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => by
      have e : π ≫ (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = fA k := by
        rw [hf k, ← Category.assoc, U.gen.inv_hom_id, Category.id_comp]
      rw [hφA k]
      exact congrArg (fun q : A.A ⟶ A.A => h q.left ^ ε k) e) b hb
  exact ⟨α, hα⟩

end Move
end GlobalTheory.SignSym

namespace GlobalTheory.SignSym

theorem sign_sym : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) ∧ ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), x ^ 2 = 1 → ∀ z J, Good A.L z J → val σ (x * (x ≫ oA.act w)).left z J = val σ x.left z J ^ 2 * val σ (x ≫ oA.act w).left z J := by
  intro R _ _ _ I hI D A G _ _ hG U O _ _ _ o oA oG hlin w hw
  have hL := GlobalTheory.firstFiveLaws
  have hGF := hL.1.globalFns
  have := U.gen_hom
  haveI := oG.hom w
  haveI := oA.hom w
  obtain ⟨-, E, eG, eA, -, -, -⟩ := IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U
  have rId : (Over.pullback (jK R)).map (𝟙 G) ≫ U.gen.hom = U.gen.hom ≫ 𝟙 A.A := by
    rw [(Over.pullback (jK R)).map_id, Category.id_comp, Category.comp_id]
  have rW : (Over.pullback (jK R)).map (oG.act w) ≫ U.gen.hom = U.gen.hom ≫ oA.act w := hlin.ext w
  have rInv : (Over.pullback (jK R)).map (ι[G]) ≫ U.gen.hom = U.gen.hom ≫ ι[A.A] := by
    have h := E.ext
    rw [eG, eA, Hom.inv_def, Hom.inv_def, Category.id_comp, Category.id_comp] at h
    exact h
  have rOne : (Over.pullback (jK R)).map (1 : G ⟶ G) ≫ U.gen.hom = U.gen.hom ≫ (1 : A.A ⟶ A.A) := by
    rw [(Over.pullback (jK R)).map_one, MonObj.one_comp, MonObj.comp_one]
  have rSum : (Over.pullback (jK R)).map (𝟙 G * oG.act w) ≫ U.gen.hom = U.gen.hom ≫ (𝟙 A.A * oA.act w) := by
    rw [(Over.pullback (jK R)).map_mul, MonObj.mul_comp, MonObj.comp_mul, rId, rW]

  obtain ⟨σ₀, hσ₀⟩ := exists_gen_onA U.toUnifPre ![ι[G], 𝟙 G] ![ι[A.A], 𝟙 A.A]
    (fun k => by fin_cases k; exacts [rInv, rId]) ![1, -1] _ (fun k => by fin_cases k <;> rfl)
    ![(ι[A.A]).left, 𝟙 A.A.left] (fun k => by fin_cases k <;> rfl) U.symG U.symG_gen
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hw
  obtain ⟨β, hβ⟩ := exists_gen_onA U.toUnifPre ![𝟙 G, 𝟙 G * oG.act w, 𝟙 G, oG.act w, 1]
    ![𝟙 A.A, 𝟙 A.A * oA.act w, 𝟙 A.A, oA.act w, 1]
    (fun k => by fin_cases k; exacts [rId, rSum, rId, rW, rOne]) GlobalTheory.JetSer.primε (GlobalTheory.JetSer.primφ (oG.act w)) (fun k => by fin_cases k <;> rfl)
    (GlobalTheory.JetSer.primφ (oA.act w)) (fun k => by fin_cases k <;> rfl) ρ hρ

  let z₀ : A.A ⟶ A.A := 1
  have o₁ : z₀.left ≫ (ι[A.A]).left = z₀.left := by
    rw [← Over.comp_left, ← Hom.inv_def, inv_one]
  have o₂ : z₀.left ≫ 𝟙 A.A.left = z₀.left := Category.comp_id _
  obtain ⟨σ, hσ, vσ⟩ := exists_gen A.isLB (φ' := ![(ι[A.A]).left, 𝟙 A.A.left]) (ε' := ![1, -1])
    (fun V _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, o₁, o₂]
      rw [neg_neg, ← zpow_add, neg_add_cancel, zpow_zero, _root_.mul_one])
    (LB.mulGen A.L _ _ _ _ σ₀ (LB.invGen A.L _ _ (LB.pullGen A.L _ _ σ₀ z₀.left)))
    (mulGen_isGen _ _ _ _ _ _ _ hσ₀ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hσ₀ _)))
  have vσ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) z J, Good A.L z J →
      val σ r z J = val σ₀ r z J * (val σ₀ (r ≫ z₀.left) z J)⁻¹ :=
    fun Z r z J hJ => (vσ Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A) = η[A.A] := by simp [Hom.one_def]
  have e₀ : eSec A.A ≫ z₀.left = eSec A.A := by
    show η[A.A].left ≫ (1 : A.A ⟶ A.A).left = η[A.A].left
    rw [← Over.comp_left, MonObj.comp_one, e₁]
  have hσ1 : ∀ y J, Good A.L y J → val σ (eSec A.A) y J = 1 := fun y J hJ => by
    rw [vσ' _ _ y J hJ, e₀, mul_inv_cancel]
  have hσn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) :=
    corr_of_val A.isLB fun y J hJ => by
      rw [val_pull hJ, Category.id_comp, val_one]
      exact hσ1 y J hJ
  refine ⟨σ, hσ, hσn, fun T x hx z J hJ => ?_⟩

  have hY : Function.Surjective A.A.hom.appTop.hom := (hGF _ _ A.isAb).2
  have hι : ι[A.A] = (𝟙 A.A)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  have hinv : ∀ {Y : Over (Spec (CommRingCat.of (FractionRing R)))} (f : Y ⟶ A.A), f ≫ ι[A.A] = f⁻¹ := fun f => by
    rw [Hom.inv_def]
  have c₁ : ι[A.A] ≫ oA.act w = oA.act w ≫ ι[A.A] := by
    have := IntEnd.id_zpow_comm (oA.act w) (-1)
    rw [zpow_neg_one, ← hι] at this
    exact this
  have c₂ : ι[A.A] ≫ (𝟙 A.A * oA.act w) = (𝟙 A.A * oA.act w) ≫ ι[A.A] := by
    rw [MonObj.comp_mul, Category.comp_id, c₁, hinv, hinv, mul_inv, hι]
  have nv : ∀ y I, Good A.L y I → val σ (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A).left y I = 1 :=
    fun y I hI => by rw [e₁]; exact hσ1 y I hI
  have H := ((SymFrame.hasGen_pull hβ (𝟙 A.A)).mul (SymFrame.hasGen_pull hβ (ι[A.A])).inv).unique A.isLB
    ((((SymFrame.hasGen_pull hσ (𝟙 A.A * oA.act w)).mul (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul
      (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul (SymFrame.hasGen_pull hσ (oA.act w)).inv)
    (fun V _ h => ?_) hY 1 (fun y I hI => ?_) T x z J hJ
  · have xi : x ≫ ι[A.A] = x := by
      rw [hinv]; exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)
    have xs : x ≫ (𝟙 A.A * oA.act w) = x * (x ≫ oA.act w) := by rw [MonObj.comp_mul, Category.comp_id]
    rw [xi, xs, Category.comp_id, mul_inv_cancel] at H
    apply Additive.ofMul.injective
    have a := congrArg Additive.ofMul H
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a ⊢
    calc _ = (Additive.ofMul (val σ (x * x ≫ oA.act w).left z J) + -Additive.ofMul (val σ x.left z J) +
          -Additive.ofMul (val σ x.left z J) + -Additive.ofMul (val σ (x ≫ oA.act w).left z J)) +
          (2 • Additive.ofMul (val σ x.left z J) + Additive.ofMul (val σ (x ≫ oA.act w).left z J)) := by abel
      _ = _ := by rw [← a, zero_add]
  · simp only [GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, Fin.prod_univ_five, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
      Over.id_left, Category.id_comp, Category.comp_id, ← Over.comp_left, c₁, c₂, MonObj.comp_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  · rw [Category.comp_id, hinv, inv_one, MonObj.comp_mul, Category.comp_id, MonObj.one_comp, _root_.mul_one,
      mul_inv_cancel, nv y I hI]
    simp

end GlobalTheory.SignSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapInjectiveCardCokerOfIsogeny
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem tmap_injective_card_coker_of_isIsogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧
      Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  intro K _ l _ hl A B f hf
  have hsurj : Function.Surjective (ptMap f) := (surjective_iff_ptMap_surjective K A B f).1 hf.2
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hdiv : ∀ x : A.Pt, ∃ y, y ^ l = x := pt_divisible K A l (Fact.out : l.Prime).ne_zero
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.tate_map_coker_card l A.Pt B.Pt (ptMap f) hdiv hsurj hfin
  exact ⟨h1, h2.trans (GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree K l hl A B f hf)⟩

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageOfClosedPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartDer

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X)
    (V : X.Opens) (h : f (closedPoint R) ∈ V) : ⊤ ≤ f ⁻¹ᵁ V := by
  intro p _
  have hp : p ⤳ closedPoint R := (PrimeSpectrum.le_iff_specializes p (closedPoint R)).1 (le_maximalIdeal p.2.ne_top)
  exact hp.mem_open (f ⁻¹ᵁ V).2 h

end GlobalTheory.ChartDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TvELeft
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.VertCoeffRing
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def tvE (u : TanM (𝟙 (Sp R)) G) : epsR R ⟶ G := Over.homMk (tv u).left (by
  have := Over.w (tv u)
  simpa using this)

theorem tvE_left (u : TanM (𝟙 (Sp R)) G) : (tvE u).left = (tv u).left := rfl

end GlobalTheory.VertCoeffRing
end
end

