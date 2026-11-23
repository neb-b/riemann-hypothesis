module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constants_torus_translates_twisted_sums : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : (Fin 8 → X) → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h)) := by
  first | exact @GlobalTheory.Poinc.Sep.twistSum_translate | exact GlobalTheory.Poinc.Sep.twistSum_translate | (intros; apply GlobalTheory.Poinc.Sep.twistSum_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsFrameExponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.FrameExpEx
open GlobalTheory.Poinc.TorsRatio

theorem torsFrame_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V))) (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' → ∃ l : FractionRing V, l ^ (N ^ 2) = 1 ∧ ∀ z J, Good A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val := by
  intro V _ _ A ρA _ N _ x e e' H H'
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  obtain ⟨l, hl0, hl⟩ := frame_ratio he he'
  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J →
      Geo.Tor.val α r z J = Geo.Tor.val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J hJ using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ : Good A.L z J := hJ
  have q : Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : Geo.Tor.val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : Geo.Tor.val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have hlN : l ^ (N ^ 2) = 1 := by
    have q' := congrArg Units.val q
    rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hl z J hJ, mul_pow, ← map_pow] at q'
    have hu : IsUnit ((Geo.Tor.val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
    have h1 : cstK z (l ^ (N ^ 2)) = cstK z 1 := by
      rw [map_one]
      exact hu.mul_left_inj.1 (by rw [_root_.one_mul]; exact q'.symm)
    exact (cstK z).injective h1
  exact ⟨l, hlN, hl⟩

end GlobalTheory.GSep.FrameExpEx

namespace GlobalTheory.GSep.FrameExpEx
open GlobalTheory.GSep.TwistTranslate


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_frExp : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a ha τ hτ
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.GSep.exists_terms_single I X₁ z₁ act x₀ hdiv V ev Y t δ 𝔪 a ha
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, -⟩ := hT
  obtain ⟨χ₀, hχ₀, hyp⟩ := GlobalTheory.T.exists_level_killed_char_of_torus_label I X₁ z₁ act V ev Y t δ 𝔪 τ hτ
  have hT₀ : GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ₀ := ⟨hχ₀, hyp⟩
  obtain ⟨ρA, hρA, htors⟩ := exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ₀ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ₀)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' ()) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w₂, hw₂g, hw₂v⟩ : ∃ w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 (g' () + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)).b,
      w₂.IsGen ∧ ∀ z J, val w₂ (𝟙 _) z J = val (w ()) (𝟙 _) z J := by
    revert hb
    generalize (g' () + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)).b = b
    rintro rfl
    exact ⟨w (), (hc ()).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := over_translate 𝔪 w₀ hw₀ ρA hρA (x a) (fr a) (htors _)
    (g' ()) (w ()) (hc ()).1 (hc ()).2.1 (hc ()).2.2 χ₀ hχ₀ _ hg₀ p xτ hpy hpg hq _ hadd w₂ (fun z J _ => hw₂v z J)
    (x (a + τ)) (x_add 𝔪 x hx a τ xτ hxτ)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  obtain ⟨l, hl, hlv⟩ := torsFrame_ratio V 𝔪.A ρA hρA _ hN _ _ _ he₂ (htors (a + τ))
  obtain ⟨e, he⟩ := eq_yK_zeta_pow 𝔪 l hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hl
    exact zero_ne_one hl
  refine ⟨e, ⟨χ₀, hT₀⟩, x, fr, th, w₀, s, g' (), w (), hx, hfr, hth, hw₀, hs, (hc ()).1, (hc ()).2.1, (hc ()).2.2, ?_⟩
  intro χ hχ g₀ hg₀' g'' hadd'' w'' _ hval
  obtain rfl : χ₀ = χ := _root_.GlobalTheory.GSep.TorCharUnique.torChar_unique I X₁ z₁ act V ev Y t δ 𝔪 τ χ₀ χ hT₀ hχ
  obtain rfl : g₀ = GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀) :=
    (GlobalTheory.TorusExt.isTorusPtF_iff_eq g₀ χ₀).1 ((isTor_iff _ _).1 hg₀')
  obtain rfl := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hadd''
  refine GlobalTheory.T.thetaMember_lies_over_rescale_frames I X₁ z₁ act V ev Y t δ 𝔪 w₀ _ w₂ w'' (x (a + τ)) e₂ (fr (a + τ)) l hl0 hlv (fun z J hJ => ?_) hov
  rw [hw₂v, hval z J hJ, he]

end GlobalTheory.GSep.FrameExpEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelIntegralClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classSums_deeper_level_integralClosure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1 : ℤ)] t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 1 → Φ.X y), ∀ S : Finset (Fin 1 → Φ.X y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (a : 𝓞 E) x, CongMod N (γ (a • x)) (a • γ x)) ∧ (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.UPoinc.ClassCore.classSums_core | exact GlobalTheory.UPoinc.ClassCore.classSums_core | (intros; apply GlobalTheory.UPoinc.ClassCore.classSums_core <;> assumption)
end

