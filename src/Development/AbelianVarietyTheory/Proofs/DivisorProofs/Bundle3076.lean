module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorCommutingPeriods
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

theorem GlobalTheory.heat_commuting_periods_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hmon ht D hD
  obtain ⟨h, w, π, π', hb, hdef⟩ := _root_.GlobalTheory.HeatEx.exists_basic_heat_polyDefect R Dd O oa Y n v dd hv m t gam hmon ht D hD
  have hcoc := _root_.GlobalTheory.HeatDefect.defect_cocycle R Dd O oa Y n v dd hv D h _ hb hdef
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.cocycle_polynomial_defect R Dd.toPre.X w π π' hcoc
  exact _root_.GlobalTheory.HeatMod.exists_heat_defect_zero R Dd O oa Y n v dd hv D h w π π' hb hdef h1 h2 h3 h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

theorem GlobalTheory.GSep.twistAtEach_exists : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg⟩ := GlobalTheory.GSep.torusChar_eq_weil_gen I X₁ z₁ act
  refine ⟨sg, ?_, hsg⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c τ hτ
  obtain ⟨χ, hχN, hχo⟩ := GlobalTheory.GSep.TorPt.exists_torus_char I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.GSep.TwistTranslate.twistSum_translate I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab hlab T hT c τ hτ χ hχN hχo
  exact ⟨e, GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv)
    (GlobalTheory.GSep.GMem.exists_yy I X₁ z₁ act V ev X t δ 𝔪) (hsg V ev X t δ 𝔪 τ χ hχN hχo) he⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreTorsionRationalOfBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem torsRat_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD
  haveI : CharZero R := hR.2
  have hadm : AdmBase R (maximalIdeal R) := hR.1
  have hn : 1 ≤ l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  haveI := P.U.gen_hom
  refine GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed t.G t.G P.A P.U.gen (𝟙 _) (𝟙 _) l.M' P.U.gen_hom
    inferInstance inferInstance (Category.comp_id _) hn ?_
  intro σ x hx
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ t.G, y = x := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj t.G,
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ l.M' = 1 := by rw [hy0]; exact hx
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ l.M' = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A.A, a = h ≫ P.U.gen.hom := ⟨_, rfl⟩
  have ha : a ^ l.M' = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) l.M' hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨⟨p', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom l.M' hn p
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p' a a' hext ha').1 ((hT.1 p a).2 hp.symm)
  have heq := _root_.GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom L R hR t P iw s ε e hε hs hD σ p p' hext
  have haa : a' = a := ((hT.1 p' a').1 h2).trans (((hT.2.2.1 p p').2 heq).symm.trans hp)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app t.G).left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app t.G := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ P.U.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ P.U.gen.hom P.U.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  rw [hy0] at hyx
  simpa using hyx

end GlobalTheory.UCanon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailExtra
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LowDat.exists_lower : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
  GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R, 1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    GlobalTheory.LowDat.IsLower Dw D' Z f ∧ D'.p = Dw.p - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    D'.q = Dw.q - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : GlobalTheory.LowDat.LowTate C D' o' F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I ∧
          GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨Z, hZ, hrk, tK, m1, m2, hI⟩ := GlobalTheory.T.exists_isotropic_saturated_weight_filtration Xo c R hR C hr
  obtain ⟨D', f, hf, hp, hq⟩ := _root_.GlobalTheory.LowDat.exists_lowerDatum Dw Z hZ
  obtain ⟨o', φB, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry Xo c R hR C Z D' f hZ hf hrk hp hq tK m1 m2 hI
  refine ⟨Z, D', f, o', φB, hZ, hrk, hf, hrk ▸ hp, hrk ▸ hq, h1, h2, h3, tK, m1, m2, ?_⟩
  intro F _ _ _
  obtain ⟨I, hI1, hI2⟩ := hI F
  obtain ⟨I', hI'⟩ := h4 F I hI1 hI2
  exact ⟨I, I', hI1, hI2, hI'⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualAbelianSchemePoincareSwap
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BidualAbelian

theorem isAdditive_swap_swap {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left}
    (hP : P.IsLB) (h : IsAdditive P) : IsAdditive (swap (swap P)) := by
  have hs : (swap P).IsLB := pull_isLB hP _
  have hss : (swap (swap P)).IsLB := pull_isLB hs _
  refine (isAdditive_iff hss).2 fun Y a a' t ↦ ?_
  rw [evc_swap hs hss, evc_swap hs hss, evc_swap hs hss, evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]
  exact (isAdditive_iff hP).1 h Y a a' t

theorem fibre_isIso : ∀ (S : Scheme.{0}) (A B C : Over S) [GrpObj A] [GrpObj B] [GrpObj C] (P : LB (A ⊗ B).left)
    (Q : LB (B ⊗ C).left) (κ : A ⟶ C), IsAbelianScheme A → IsAbelianScheme B → IsAbelianScheme C → DimLe A B →
    DimLe B C → IsDual A B P → IsDual B C Q → IsMonHom κ → LBIso (swap P) (ev Q (fst B A) (snd B A ≫ κ)) →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso ((Over.pullback t).map κ) := by
  intro S A B C _ _ _ P Q κ hA hB hC hAB hBC hd hQ hm e Ω _ _ t
  have hA' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t A hA
  have hB' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t B hB
  have hC' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t C hC
  obtain ⟨g, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim Ω ((Over.pullback t).obj A) hA'
  have hgB : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom := hAB g (Sp Ω) t hgA
  have hgC : SmoothOfRelativeDimension g ((Over.pullback t).obj C).hom := hBC g (Sp Ω) t hgB
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback t).map a).left ≫ pullback.fst Y.hom t = pullback.fst X.hom t ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback t).obj A ⊗ (Over.pullback t).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback t) A B).left ≫ pullback.fst (A ⊗ B).hom t
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback t).obj A) ((Over.pullback t).obj B)).left ≫
      pullback.fst A.hom t := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback t) A B ≫ (Over.pullback t).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback t).obj A) ((Over.pullback t).obj B)).left ≫
      pullback.fst B.hom t := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback t) A B ≫ (Over.pullback t).map (snd A B) = snd _ _ by simp]
  have hP' : (P.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual _ _ (P.pull h) := IsDual.baseChange (isGrpPullback_pullback A t) (isGrpPullback_pullback B t)
    h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have ker := _root_.GlobalTheory.DualKer.leftKer_eq_one Ω _ _ g (P.pull h) hA' hB' hgA hgB hd'
  have hs : (swap P).IsLB := pull_isLB hd.isLB _
  have hE : (ev Q (fst B A) (snd B A ≫ κ)).IsLB := pull_isLB hQ.isLB _
  have ce : cls _ hs = cls _ hE := (cls_eq_iff hs hE).2 e
  have mono : Mono ((Over.pullback t).map κ) := by
    constructor
    intro T x y hxy
    have z1 : (x * y⁻¹) ≫ (Over.pullback t).map κ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
    have tr : Triv (ev (P.pull h) (fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹)) (snd T ((Over.pullback t).obj B))) := by
      refine (triv_ev_iff hP' _ _).2 ?_
      let a : Over.mk (T ⊗ (Over.pullback t).obj B).hom ⟶ (Over.pullback t).obj A :=
        fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹)
      let b : Over.mk (T ⊗ (Over.pullback t).obj B).hom ⟶ (Over.pullback t).obj B := snd T _
      let a₀ := pushP (isGrpPullback_pullback A t) (s₀ := (T ⊗ (Over.pullback t).obj B).hom ≫ t) rfl a
      let b₀ := pushP (isGrpPullback_pullback B t) (s₀ := (T ⊗ (Over.pullback t).obj B).hom ≫ t) rfl b
      have e1 : evc hP' a b = evc hd.isLB a₀ b₀ := evc_eq h₁ h₂ hd.isLB hP' ((cls_eq_iff hP' hP').1 rfl) a b a₀ b₀ rfl rfl
      refine e1.trans ?_
      have one : a₀ ≫ κ = 1 := by
        apply Over.OverMorphism.ext
        rw [Over.comp_left]
        show (a.left ≫ pullback.fst A.hom t) ≫ κ.left = _
        rw [Category.assoc, ← key, ← Category.assoc, ← Over.comp_left]
        show (fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹) ≫ (Over.pullback t).map κ).left ≫ _ = _
        rw [z1, MonObj.comp_one]
        exact one_left_comp (isGrpPullback_pullback C t) rfl
      have e2 : evc hs b₀ a₀ = evc hE b₀ a₀ := by unfold evc; rw [ce]
      rw [← evc_swap hd.isLB hs, e2, evc_ev hQ.isLB, lift_fst, lift_snd_assoc, one, evc_one_right hQ.isLB hQ.zero]
    have hz := ker T (x * y⁻¹) tr
    calc x = x * y⁻¹ * y := (inv_mul_cancel_right x y).symm
      _ = y := by rw [hz, _root_.one_mul]
  exact GlobalTheory.AbMonoIso.isIso_of_mono (Sp Ω) _ _ hA' hC' g g hgA hgC le_rfl _ inferInstance mono

theorem isDual_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left),
    IsAbelianScheme A → IsAbelianScheme B → DimLe A B → IsDual A B P → IsDual B A (swap P) := by
  intro S A B _ _ P hA hB hAB hd
  obtain ⟨C, _, Q, hC, hBC, hQ⟩ := _root_.GlobalTheory.DualExist.exists_dual S B hB
  have hs : (swap P).IsLB := pull_isLB hd.isLB _
  have ha : IsAdditive (swap P) := isDual_isAdditive_swap S A B P hB hd
  obtain ⟨κ, e, -⟩ := hQ.univ A (swap P) hs ha
  have hm : IsMonHom κ := isMonHom_of_classifying S B A C (swap P) Q hQ
    (isDual_isAdditive_swap S B C Q hC hQ) hs (isAdditive_swap_swap hd.isLB hd.additive) κ e
  have hi : IsIso κ := isIso_of_isIso_pullback hA hC κ fun Ω _ _ t ↦
    fibre_isIso S A B C P Q κ hA hB hC hAB hBC hd hQ hm e Ω t
  exact transport S B A C (swap P) Q hQ hs κ hi hm e

end GlobalTheory.BidualAbelian
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyAndPrimeDvdDegOfDvdNorm
section
open CategoryTheory GlobalTheory.AV GlobalTheory.AV.AbVar NumberField Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.DegNorm

theorem dvd_algebraMap_norm {S : Type} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S] (x : S) :
    x ∣ algebraMap ℤ S (Algebra.norm ℤ x) := by
  classical
  let b := Module.Free.chooseBasis ℤ S
  let M := Algebra.leftMulMatrix b x
  have h0 : aeval x M.charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact Matrix.aeval_self_charpoly M
  have hsplit : aeval x M.charpoly = x * aeval x M.charpoly.divX + algebraMap ℤ S (M.charpoly.coeff 0) := by
    conv_lhs => rw [← X_mul_divX_add M.charpoly]
    rw [map_add (f := _), map_mul, aeval_X, aeval_C]
  rw [h0] at hsplit
  refine ⟨-(algebraMap ℤ S ((-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ S)) * aeval x M.charpoly.divX), ?_⟩
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_eq_sign_charpoly_coeff, map_mul]
  linear_combination (-(algebraMap ℤ S ((-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ S)))) * hsplit

theorem isIsogeny_and_deg_ne_zero {K : Type} [Field K] (A : AbVar K) {F : Type} [Field F] [NumberField F]
    (ι : 𝓞 F →+* End A) (z : 𝓞 F) (hz : z ≠ 0) :
    IsIsogeny (ι z).asHom ∧ deg (ι z).asHom ≠ 0 := by
  obtain ⟨y, hy⟩ := dvd_algebraMap_norm z
  have hN : Algebra.norm ℤ z ≠ 0 := by
    intro h
    have h1 := Algebra.coe_norm_int z
    rw [h, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at h1
    exact hz (by exact_mod_cast h1)
  have hc : (ι y).asHom ≫ (ι z).asHom = Algebra.norm ℤ z • 𝟙 A := by
    rw [← End.mul_asHom]
    rw [← map_mul, ← hy, algebraMap_int_eq, Int.coe_castRingHom, map_intCast, ← zsmul_one]
    rfl
  have h := isIsogeny_comp_iff_and_deg_comp K A A A (ι y).asHom (ι z).asHom rfl rfl
  obtain ⟨hi, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A _ hN
  rw [hc] at h
  refine ⟨(h.1.1 hi).2, fun h0 => ?_⟩
  rw [h0, mul_zero] at h
  rw [h.2] at hd
  exact pow_ne_zero _ (Int.natAbs_ne_zero.2 hN) hd.symm

end GlobalTheory.AV.AbVar.DegNorm

namespace GlobalTheory.AV.AbVar.DegNorm

theorem charpoly_eq_minpoly_pow {K : Type} [Field K] (A : AbVar K) (hA : A.dim ≠ 0) {F : Type} [Field F]
    [NumberField F] (ι : 𝓞 F →+* End A) (x : 𝓞 F) :
    ∃ k : ℕ, 0 < k ∧ (charpoly (ι x)).map (Int.castRingHom ℚ) = minpoly ℚ (x : F) ^ k := by
  first
  | exact @_root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow
  | exact _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow
  | (apply _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow ..)

end GlobalTheory.AV.AbVar.DegNorm

namespace GlobalTheory.AV.AbVar.DegNorm

open IntermediateField

end GlobalTheory.AV.AbVar.DegNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassFromIntegralStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_class_from_integral : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧ ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  first | (exact @GlobalTheory.EtC.LiftWitness.lift_witness) | (exact GlobalTheory.EtC.LiftWitness.lift_witness) | (intros; apply GlobalTheory.EtC.LiftWitness.lift_witness  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UCoverLab

theorem jK_mono (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  haveI : Scheme.Spec.IsRightAdjoint := ΓSpec.adjunction.isRightAdjoint
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))).op) := inferInstance
  exact this

theorem gp_mono {R : Type} [CommRing R] [IsDomain R] (M : Modif R) : Mono M.gp := by
  have : Mono (M.gp ≫ M.π) := by rw [M.gp_π]; exact jK_mono R
  exact mono_of_mono M.gp M.π

theorem mono_α {R : Type} [CommRing R] [IsDomain R] {M : Modif R} {X : Over M.S} [GrpObj X]
    {A : Over (Sp (FractionRing R))} [GrpObj A] {α : A.left ⟶ X.left} (h : IsGrpPullback A X M.gp α) : Mono α := by
  haveI := gp_mono M
  refine ⟨fun u v huv => h.1.hom_ext huv ?_⟩
  apply (cancel_mono M.gp).1
  rw [Category.assoc, Category.assoc, ← h.1.w, ← Category.assoc, huv, Category.assoc]

end GlobalTheory.Mum.UCoverLab


open GlobalTheory.Mum.UCoverLab GlobalTheory.Mum.CoverFin in
theorem GlobalTheory.Mum.UCover.labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  intro R _ _ _ hB D C lab n hn ho hu hone hgal
  refine ⟨{ toModif := C.toModif
            G := C.G
            semi := C.semi
            P := C.P
            A := C.A
            α := C.α
            α_cart := C.α_cart
            α_lb := C.α_lb
            n := n
            n_prime := hn
            n_odd := ho
            n_unit := hu
            lab := fun j => lab (n ^ j)
            trait := ?_ }⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G', _, _, β, D', A', U', hW', hio, hfin, hcart, hlb⟩ := C.trait W hW φ ξ hφ hξ
  haveI : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  have hsemi : IsSemiAbelian G' := semiAbelian_of_pull hcart C.semi
  have hγ : IsGrpPullback A'.A G' (jK W') (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) :=
    GlobalTheory.ThetaBaseChange.grp_generic U'.toUnifPre
  have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' _).comp (hio.comp hφ)
  obtain ⟨ga, hga, hy⟩ := GlobalTheory.T.exists_factor_field_point_through_generic_point R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ) hinj (by
    rw [Category.assoc, Category.assoc, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)
  have hcomp : IsGrpPullback A'.A C.G (spMap ga ≫ C.gp) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β) :=
    (hγ.comp hcart).congr hy rfl
  let a : A'.A.left ⟶ C.A.A.left := C.α_cart.1.lift ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)
    (A'.A.hom ≫ spMap ga) (by rw [hcomp.1.w, Category.assoc])
  have ha : a ≫ C.α = (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β := C.α_cart.1.lift_fst _ _ _
  have ha2 : a ≫ C.A.A.hom = A'.A.hom ≫ spMap ga := C.α_cart.1.lift_snd _ _ _
  have hcart' : IsGrpPullback A'.A C.A.A (spMap ga) a := IsGrpPullback.cancel C.α_cart (hcomp.congr rfl ha.symm) ha2
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hA' : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W'))) :=
    LBIso.chartPull (h := U'.gen.inv.left) (chartPullSec A'.L _ _ hgi)
      (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W')) _ _ fun _ => rfl) U'.ext
  have h2 : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')))
      (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.chartPull (chartPullPull U'.LG.L _) (chartPullSame C.P.L.L _ _ _ _ fun _ => rfl) hlb
  have h3 : LBIso A'.L (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB C.P.L.isLB _) hA' h2
  have hfib : IsFib (io.comp φ) C.A A' a :=
    ⟨ga, fun r => hga r, hcart', lbIso_factor C.P.L.isLB C.A.isLB A'.isLB ha C.α_lb h3⟩
  obtain ⟨hD, hind⟩ := _root_.GlobalTheory.Mum.Recognition.pullDeg_induces R hB D C.A lab n hn ho hu hone hgal W' hW' (io.comp φ) (hio.comp hφ)
    inferInstance G' D' A' U' a hsemi hfib
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G', inferInstance, inferInstance, β, D', A', U', hD, hW',
    hio, hfin, hcart, hlb, ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hind j F em hF p p₁ p' x' h₁ h₂ h₃ ?_
  haveI := mono_α C.α_cart
  rw [← cancel_mono C.α, Category.assoc, ha]
  simpa only [Category.assoc] using h₄
end
end

