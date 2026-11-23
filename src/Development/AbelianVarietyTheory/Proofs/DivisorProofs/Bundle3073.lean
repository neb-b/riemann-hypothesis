module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsAffineTwoMembers
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
namespace GlobalTheory.Poinc.Sep

theorem sumF_comp_equiv {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix Jx : Type} {x : Ix → K} {s : K} (e : Jx ≃ Ix) (h : SumF I K x s) :
    SumF I K (fun j => x (e j)) s := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  refine ⟨N, hN, hs, fun j => hx _, fun k => ?_⟩
  classical
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have hsub : S ⊆ T.map e.toEmbedding := by
    intro a ha
    have := hT (Finset.mem_map_of_mem e.symm.toEmbedding ha)
    exact Finset.mem_map.2 ⟨e.symm a, this, by simp⟩
  have := hS _ hsub
  rwa [Finset.sum_map] at this

theorem sum_terms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (c : C), SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem (lab c)⟩) := by
  intro g n F W Z i X₁ z₁ act x₀ _ V _ _ _ ev X _ m t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hexp, hg', hTe⟩ := hT
  have hO := (hg' c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hg' c).2.1 th s _ hexp (hth (lab c))
  have := sumF_comp_equiv 𝔪.e₈.toEquiv hO
  convert this using 1
  funext mu
  exact hTe mu c

theorem twistSum_of_transExp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) (sg : ℤˣ)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ)
    (hW : ∀ (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), TorChar 𝔪 τ χ →
      ∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))
    {C : Type} (lab : C → X₁.S.Gam) (hlab : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁) (T : (Fin 8 → X) → C → V)
    (hT : 𝔪.Terms x₀ lab T) (c : C) (τ : X₁.S.Gam) (hτ : τ ∈ X₁.S.TT X₁.M z₁) (e : ℕ)
    (hE : TransExp 𝔪 x₀ (lab c) τ e) : TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  obtain ⟨χ, hχ1, hχ2⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨T', hT'⟩ := _root_.GlobalTheory.Poinc.Sep.TermsExt.exists_terms_translate g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 C lab hlab T hT c τ hτ
  have hprop := hE χ ⟨hχ1, hχ2⟩ C lab T hT c rfl Unit _ T' hT' () rfl
  have hsum := sumF_const_mul (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)))
    (sum_terms g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 Unit (fun _ => lab c + τ) T' hT' ())
  refine GlobalTheory.Poinc.TwistSum₂.twistSum_of_sumF g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab T sg c τ χ e
    (UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hd)
    (UMem.exists_yy g n F W Z i X₁ z₁ act V ev X m t δ 𝔪) (hW τ χ ⟨hχ1, hχ2⟩) ?_
  convert hsum using 1
  funext mu
  rw [← _root_.mul_assoc, hprop mu, _root_.mul_assoc]

theorem twistSum_exp_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y2) → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro g n F W Z i X₁ z₁ act x₀ hd sg _ hW V1 _ _ _ ev1 Y1 _ m1 t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ m2 t2 δ2 𝔪2
  classical
  have hA := _root_.GlobalTheory.Poinc.Sep.trans_exp_affine g n F W Z i X₁ z₁ act x₀ hd V1 ev1 Y1 m1 t1 δ1 𝔪1 V2 ev2 Y2 m2 t2 δ2 𝔪2
  choose! F1 F2 hF1 hF2 hAff using hA
  refine ⟨fun a τ => F1 τ a, fun a τ => F2 τ a, ?_, ?_, fun τ hτ => hAff τ hτ⟩
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪1 (fun τ χ hχ => hW V1 ev1 Y1 m1 t1 δ1 𝔪1 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF1 τ hτ (lab c) (hlab c))
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪2 (fun τ χ hχ => hW V2 ev2 Y2 m2 t2 δ2 𝔪2 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF2 τ hτ (lab c) (hlab c))

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaPowerResidueDividingLabel
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
namespace GlobalTheory.Poinc.Sep.TwistResid

theorem twist_resid : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  classical
  intro g n F W Z i X₁ z₁ act x₀ hx₀ V _ _ _ ev Y _ m t δ 𝔪 C lab hlab T hT c hc τ hτ sg e hTw s u hs hu
  have hcd : X₁.M.Div X₁.S.th (lab c) z₁ := hc
  have hqO : X₁.S.th (lab c) / X₁.S.th x₀ ∈ X₁.M.O z₁ := hx₀.2 (lab c)
  let r := (X₁.M.stalkEquiv z₁).symm ⟨_, hqO⟩
  have hr : X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have hrU : IsUnit r := ((RatModel.isUnit_O_iff (⟨_, hqO⟩ : X₁.M.O z₁)).2
    ⟨div_ne_zero hcd.1 hx₀.1, by rw [inv_div]; exact hcd.2 x₀⟩).map (X₁.M.stalkEquiv z₁).symm
  obtain ⟨zt, hzt⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  obtain ⟨wt, hwt⟩ := _root_.GlobalTheory.Poinc.Sep.WtWd.wt_wd g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 sg τ hτ
  let wt' : (Fin 8 → Y) → ZMod (X₁.S.r * X₁.S.N) := fun mu => if mu = 0 then 0 else wt mu
  have hwt' : ∀ a mu, 𝔪.YY a mu → wt' mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
    intro a mu h
    by_cases h0 : mu = 0
    · subst h0
      have ha : a ∈ X₁.S.HH X₁.M z₁ := (_root_.GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 a).2 h
      have h1 : eStd X₁.S.g _ τ a = 0 := hτ a ha
      simp only [wt', if_pos rfl, h1, smul_zero]
    · simp only [wt', if_neg h0]
      exact hwt a mu h
  have hh : X₁.M.stalkHom z₁ (s * u * r) = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := by
    rw [map_mul, map_mul, hs, hu, hr]
    field_simp [hcd.1, hx₀.1]
  obtain ⟨N, -, -, -, hN⟩ := hTw zt (s * u * r) hzt hh wt' hwt'
  obtain ⟨S, hS⟩ := hN 1
  have h1 := hS (insert 0 S) (Finset.subset_insert _ _)
  have hle : maximalIdeal V ^ 1 • N ≤ (maximalIdeal V : Submodule V V) :=
    Submodule.smul_le.2 fun a ha b _ => by
      rw [smul_eq_mul]; exact Ideal.mul_mem_right b _ (by simpa using ha)
  have h2 := hle h1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self 0 S)] at h2
  have h3 : ∑ mu ∈ (insert 0 S).erase 0, ev zt ^ (wt' mu).val * T mu c ∈ maximalIdeal V :=
    Ideal.sum_mem _ fun mu hmu => Ideal.mul_mem_left _ _
      (_root_.GlobalTheory.Poinc.Sep.HighTerms.term_mem_maximalIdeal g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 C lab hlab T hT c mu (Finset.ne_of_mem_erase hmu))
  have h0 : ev zt ^ (wt' 0).val * T 0 c = T 0 c := by simp [wt']
  rw [h0] at h2
  have h4 : ev (s * u * r) - T 0 c ∈ maximalIdeal V := by
    have := Ideal.add_mem _ h2 h3
    simpa [sub_add_eq_sub_sub, sub_add_cancel] using this
  have h5 := _root_.GlobalTheory.Poinc.Sep.UMem.const_term_sub_mem g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 C lab hlab T hT c r hr
  have h6 : (ev (s * u) - 1) * ev r ∈ maximalIdeal V := by
    have := Ideal.sub_mem _ h4 h5
    rw [map_mul] at this
    convert this using 1; ring
  exact (Ideal.mul_unit_mem_iff_mem _ (hrU.map ev)).1 h6

end GlobalTheory.Poinc.Sep.TwistResid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLineBundleDescendsGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.LBGal
open GlobalTheory.Mum.LBDesc

theorem lemD : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := _root_.GlobalTheory.Mum.InvUnit.invariant_units

theorem lemF : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := _root_.GlobalTheory.Mum.unif_lb_frames_gal

theorem eq_of_gm_inj {Z Y : Scheme.{0}} (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Injective (p.app V).hom) {O : Y.Opens}
    {a b : Γ(Y, O)ˣ} (h : ∀ z : Z, p z ∈ O → gm (𝟙 Z ≫ p) z O a = gm (𝟙 Z ≫ p) z O b) : a = b := by
  have e : pullU p O a = pullU p O b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 Z) p z O hz a, gm_pull (𝟙 Z) p z O hz b]
    exact h z hz
  exact Units.ext ((hp O) (congrArg Units.val e))

theorem isLB_descLB_inj {Z Y : Scheme.{0}} (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Injective (p.app V).hom)
    (L' : LB Z) (hL' : L'.IsLB)
    (V : Y → Y.Opens) (hyV : ∀ y, y ∈ V y) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descLB V g).IsLB := {
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  g_self := fun y => eq_of_gm_inj p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [gm_res (𝟙 Z ≫ p) z _ hz, map_one]
    exact (key (𝟙 Z) z y y k hz hz hk).trans (mul_inv_cancel _)
  cocycle := fun a b c => eq_of_gm_inj p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [map_mul, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz,
      key (𝟙 Z) z a b k hz.1.1 hz.1.2 hk, key (𝟙 Z) z b c k hz.1.2 hz.2 hk,
      key (𝟙 Z) z a c k hz.1.1 hz.2 hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel }

end GlobalTheory.Mum.LBGal

namespace GlobalTheory.Mum
open GlobalTheory.Mum.LBDesc GlobalTheory.Mum.LBGal

theorem unif_lb_descend_gal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ L : LB G.left, L.IsLB ∧ LBIso U'.LG.L (L.pull β) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hG' U' a G _ _ β hGs hβ hact
  have hDl := lemD R hR R' ρ hρ hG G' G β a.act hGs hβ a.cart hact
  obtain ⟨V, T, hyV, hT, hinv⟩ := lemF R hR R' ρ hρ hG D D' hD A' G' hG' U' a G β hGs hβ hact
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hc : ∀ (y : G.left) {W : Scheme.{0}} (f : W ⟶ G'.left) (w : W) (k k' : U'.LG.L.ι), f w ∈ β ⁻¹ᵁ V y →
      f w ∈ U'.LG.L.U k → f w ∈ U'.LG.L.U k' →
      gm f w _ (T y k) = gm f w (U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * gm f w _ (T y k') :=
    fun y _ f w k k' h hk hk' => gm_compat U'.LG.L _ (T y) (hT y) f w k k' h hk hk'
  choose r hr using fun y y' => ratio β U'.LG.L hL' (T y) (T y') (hc y) (hc y')
  have hri : ∀ y y' σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))),
      ((a.act σ).appLE _ _ h).hom (r y y').val = (r y y').val :=
    fun y y' => hinv y y' (r y y') (fun z k hz hk => hr y y' (𝟙 _) z k hz hk)
  choose g hg using fun y y' => (hDl (V y ⊓ V y')).2 (r y y') (hri y y')
  have key : ∀ {W : Scheme.{0}} (f : W ⟶ G'.left) (w : W) (y y' : G.left) (k : U'.LG.L.ι), β (f w) ∈ V y →
      β (f w) ∈ V y' → f w ∈ U'.LG.L.U k →
      gm (f ≫ β) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹ := by
    intro W f w y y' k h1 h2 hk
    exact (gm_pull f β w (V y ⊓ V y') ⟨h1, h2⟩ (g y y')).symm.trans
      ((congrArg _ (hg y y')).trans (hr y y' f w k ⟨h1, h2⟩ hk))
  exact ⟨descLB V g, isLB_descLB_inj β (fun O => (hDl O).1) U'.LG.L hL' V hyV T g key, descIso β U'.LG.L V T g,
    isGen_descIso β U'.LG.L V T g hc key⟩

end GlobalTheory.Mum
end

