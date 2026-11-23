module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleConstantAlongDeformationOfClauses
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.KeyTop

theorem levelPoint_cast {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {u₁ u₂ : Γ(S, ⊤)ˣ} (h : u₁ = u₂)
    (l : Out.Level P M u₁) {g : ℕ} (hg : P.g = g) : levelPoint (h ▸ l) hg = levelPoint l hg := by
  subst h; rfl

theorem exhaust {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {M : ℕ} {ze : Γ(Sp K, ⊤)ˣ}
    (lev : Out.Level P M ze) {g : ℕ} (hg : P.g = g) (z : baseOver (Sp K) ⟶ P.A) (hz : z ^ M = 1) :
    ∃ a, levelPoint lev hg a = z := by
  subst hg
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) z hz
  refine ⟨fun i => ((c i : ℕ) : ZMod M), ?_⟩
  rw [levelPoint_rfl, Out.Level.toPt, ← hc]
  congr 1
  funext i; exact ZMod.val_cast_of_lt (c i).isLt

end GlobalTheory.MBLow.KeyTop

namespace GlobalTheory.MBLow.KeyTop

theorem transfer_of_rule4 : ∀ κ : Rule, Rule4 κ → Transfer κ := by
  intro κ hκ g n hn hodd
  obtain ⟨j₁, hj₁⟩ := _root_.GlobalTheory.MBLow.exists_family_of_two_fibres g n hn hodd
  refine ⟨max j₁ 1, fun j hj C _ _ _ _ _ e x hg ζ lev k hD => ?_⟩
  have hj1 : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj2 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hm3 : 3 ≤ n ^ j := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := fun h => by subst h; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have := Nat.le_self_pow (show j ≠ 0 by omega) n
    omega
  obtain ⟨Θ, Γ, π, b, hπ, hb, hJ, ε, hε, hD'⟩ := hD
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  let Φ : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) ⊕ (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) × Fin g → PowerSeries C :=
    Sum.elim Θ (fun p => Γ p.1 p.2)
  let c : Fin 2 → C := ![(ζ : C), k]
  have hbΦ : ∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b := by
    rintro (a | ⟨a, i⟩) n
    · exact (hb a n).1
    · exact (hb a n).2 i
  have hsΦ : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖ := by
    intro u hu hu'
    obtain ⟨hs, -⟩ := hD' u hu hu'
    rintro (a | ⟨a, i⟩)
    · exact (hs a).1
    · exact (hs a).2 i
  obtain ⟨u, o, _, _, jo, c₀, hu0, huε, hc₀, W, _, _, _, _, _, _, β, i₀, i₁, φ, hinj, h0, h1, hunit, hprime, hφ⟩ :=
    _root_.GlobalTheory.MBLow.ring_of_deformation C e _ (Fin 2) Φ c π b ε hπ hε hbΦ hsΦ
  obtain ⟨-, x₀, hg₀, lev₀, hJ₀, hκ₀⟩ := hD' u hu0 huε
  have hc0 : jo (c₀ 0) = ζ := hc₀ 0
  have hc1 : jo (c₀ 1) = k := hc₀ 1
  have hζ0 : c₀ 0 ≠ 0 := fun h => ζ.ne_zero (by rw [← hc0, h, map_zero])
  let ζ₀ : oˣ := Units.mk0 (c₀ 0) hζ0
  have hu₁ : Units.map (i₁.comp β).toMonoidHom ζ₀ = ζ := Units.ext (by
    show (i₁.comp β) (c₀ 0) = ζ
    rw [h1, hc0])
  have hu₀ : Units.map (i₀.comp β).toMonoidHom ζ₀ = Units.map e.toMonoidHom ζ := Units.ext (by
    show (i₀.comp β) (c₀ 0) = e ζ
    rw [h0, RingHom.comp_apply, hc0])
  have hl₀ := (congrArg unitOn hu₀).symm
  have hl₁ := (congrArg unitOn hu₁).symm
  let l₀ := hl₀ ▸ lev₀
  let l₁ := hl₁ ▸ lev
  have eϑ₀ : (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n) = fun a => i₀ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).1).symm
  have eJ₀ : (fun a i => ∑' n, e (PowerSeries.coeff n (Γ a i)) * u ^ n) = fun a i => i₀ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).1).symm
  have eϑ₁ : (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n) = fun a => i₁ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).2).symm
  have eJ₁ : (fun a i => ∑' n, PowerSeries.coeff n (Γ a i) * π ^ n) = fun a i => i₁ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).2).symm
  rw [eϑ₀, eJ₀, ← levelPoint_cast hl₀ lev₀ hg₀] at hJ₀
  rw [eϑ₁, eJ₁, ← levelPoint_cast hl₁ lev hg] at hJ
  have hθ₀ := _root_.GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet ℂ x₀ g hg₀ (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ₀
  have hθ₁ := _root_.GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet C x g hg (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ
  obtain ⟨P, pt, φ₀, φ₁, hPg, hpt, hpb₀, hpb₁, hL₀, hL₁, hc₀', hc₁'⟩ :=
    hj₁ j hj1 o ζ₀ W β (fun a => φ (Sum.inl a)) ℂ C i₀ i₁ hprime x₀.P x.P hg₀ hg l₀ l₁ hθ₀ hθ₁
  have hk₀ : (κ ℂ x₀ : ℂ) = i₀ (β (c₀ 1)) := by
    rw [hκ₀, ← RingHom.comp_apply i₀ β, h0, RingHom.comp_apply, hc1]
  have := _root_.GlobalTheory.MBLow.keyValue_twoFibres κ hκ W ℂ C i₀ i₁ hinj hunit P x₀ x g hg₀ hg (n ^ j) hPg hmodd hm3 _ pt
    (levelPoint l₀ hg₀) (levelPoint l₁ hg) φ₀ φ₁ hpt hpb₀ hpb₁ hL₀ hL₁ hc₀' hc₁'
    (fun z hz => exhaust l₁ hg z hz) _ _ (β (c₀ 1)) hJ₀ hJ hk₀
  rw [this, ← RingHom.comp_apply i₁ β, h1, hc1]

end GlobalTheory.MBLow.KeyTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.QkClosure

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀]
  [Field F] [Algebra (FractionRing R) F] (f : F₀ →+* F)
  (hf : f.comp (algebraMap (FractionRing R) F₀) = algebraMap (FractionRing R) F)

theorem val_eq_of_ext {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TF (R := R) F₀).left ⟶ D.P.A.left)}
    {ε : K → ℤ} {φ' : K' → ((TF (R := R) F₀).left ⟶ D.P.A.left)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (t' : LB.Gen (LB.LinComb D.P.L φ' ε'))
    (h : ∀ z J, Good D.P.L z J → val t (extMap (R := R) f hf).left z J = val t' (extMap (R := R) f hf).left z J)
    {y J} (hJ : Good D.P.L y J) : val t (𝟙 _) y J = val t' (𝟙 _) y J :=
  val_corr hJ (GlobalTheory.corr_of_val_field_extension _ _ f _ D.P.L D.P.isLB _ _ _ _ _ _ t t' h) _

theorem val_tau_ext (x χ : D.X) {z J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀)) (extMap (R := R) f hf).left z J = tauVal D F x χ z J := by
  rw [val_pull hJ, tauVal, ← extMap_jFK f hf]


include f hf in
theorem exists_isIota_of_ext {x : D.X} {h' : GtPtF D F} (hh' : GtPtF.IsIota x h') : ∃ g : GtPtF D F₀, GtPtF.IsIota x g := by
  obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 hh'
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀))
      (𝟙 (TF (R := R) F₀).left) y J = tauVal D F₀ x χ y J := fun χ y J hJ => val_pull hJ _ _ _
  obtain ⟨g, hb, hv⟩ := exists_gt (F := F₀) (cP D _ x) (fun χ => LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀))
    (fun χ => pullGen_isGen _ _ _ _ (tau_isGen D x χ) _) (fun χ U _ h => by
      have a : ∀ w : D.X, jFK (R := R) F₀ ≫ ptK (D.c w) = (cP D (TF (R := R) F₀) w).left := fun w =>
        (Category.assoc _ _ _).symm
      have a₀ : jFK (R := R) F₀ ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F₀ ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      rw [prod_gt, ← cPoint_add, add_comm χ x, ← a, ← a, ← a, ← a₀]
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one]
      rw [mul_right_comm _ (h _) (h _)]) (fun y J hJ => by
      refine (val_eq_of_ext f hf _ (LB.oneGen D.P.L) (fun z J' hJ' => ?_) hJ).trans (val_one _)
      exact (val_tau_ext f hf x 0 hJ').trans ((v' 0 z J' hJ').symm.trans ((charVal_zero h' hJ').trans (val_one _).symm)))
    (fun χ χ' y J hJ => by
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans
        ((val_eq_of_ext f hf _ _ (fun z J' hJ' => ?_) hJ).trans (val_mul hJ _ _ _))
      have c := val_cub D.cub (extMap (R := R) f hf) hJ' (cP D _ χ) (cP D _ χ') (cP D _ x)
      rw [comp_cP, comp_cP, comp_cP] at c
      have e := charVal_add h' hJ' χ χ'
      rw [b', v' _ _ _ hJ', v' _ _ _ hJ', v' _ _ _ hJ'] at e
      refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
      exact (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') c).trans
        (e.trans (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') (val_tau_ext f hf _ _ hJ')).symm))
  exact ⟨g, (isIota_iff_val _ _).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩⟩

end GlobalTheory.QkClosure

namespace GlobalTheory.QkClosure

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀]
  [Field F] [Algebra (FractionRing R) F] (f : F₀ →+* F)
  (hf : f.comp (algebraMap (FractionRing R) F₀) = algebraMap (FractionRing R) F) {k : ℕ}

include hf

theorem isIota_gtExt {x : D.X} {h : GtPtF D F₀} (hh : GtPtF.IsIota x h) : GtPtF.IsIota x (gtExt D f hf h) := by
  obtain ⟨b, -⟩ := (isIota_iff_val _ _).1 hh
  refine (isIota_iff_val _ _).2 ⟨by rw [gtExt_b, b, comp_cP], fun χ y J hJ => ?_⟩
  rw [gtExt_val f hf _ χ hJ, tauVal, ← extMap_jFK f hf]
  exact (val_corr hJ (hh.2 χ) _).trans (val_pull hJ _ _ _)

theorem exists_qkExt (p : QkPt D F₀ k) : ∃ p' : QkPt D F k, QkExt f p p' := by
  obtain ⟨h, h₁, h₂⟩ := p.eq
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h₁
  exact ⟨⟨p.y, gtExt D f hf p.g, gtExt D f hf (k • p.g), (isNsmul_iff_eq _ _ _).2 (map_nsmul _ _ _),
    isIota_gtExt f hf h₂⟩, rfl, (eq_gtExt_iff f hf _ _).1 rfl⟩

theorem qkExt_unique {p : QkPt D F₀ k} {p₁ p₂ : QkPt D F k} (h₁ : QkExt f p p₁) (h₂ : QkExt f p p₂) : p₁ = p₂ :=
  qk_ext (h₁.1.trans h₂.1.symm) (((eq_gtExt_iff f hf _ _).2 h₁.2).trans ((eq_gtExt_iff f hf _ _).2 h₂.2).symm)

theorem qkExt_inj {p₁ p₂ : QkPt D F₀ k} {p' : QkPt D F k} (h₁ : QkExt f p₁ p') (h₂ : QkExt f p₂ p') : p₁ = p₂ :=
  qk_ext (h₁.1.symm.trans h₂.1)
    (GlobalTheory.ArcExt.gtExt_injective f hf (((eq_gtExt_iff f hf _ _).2 h₁.2).symm.trans ((eq_gtExt_iff f hf _ _).2 h₂.2)))

theorem exists_qkExt_descent [IsAlgClosed F₀] [IsAlgClosed F] (hk : (k : F₀) ≠ 0) (p' : QkPt D F k) :
    ∃ p : QkPt D F₀ k, QkExt f p p' := by
  have hL : Laws := GlobalTheory.allSixLaws.1
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  obtain ⟨h', h₁', h₂'⟩ := p'.eq
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h₁'
  obtain ⟨h₀, hh₀⟩ := exists_isIota_of_ext f hf h₂'
  have e₀ : gtExt D f hf h₀ = k • p'.g := isIota_unique (isIota_gtExt f hf hh₀) h₂'
  obtain ⟨g₀, hg₀⟩ := exists_nsmul_eq hL.mulN (Or.inr hL.polBaseChange) hk0 h₀
  have ht' : k • (p'.g - gtExt D f hf g₀) = 0 := by
    rw [nsmul_sub, ← map_nsmul, hg₀, e₀, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.ArcExt.exists_gtExt_of_torsion f hf hL hk _ ht'
  have ht0 : k • t = 0 := GlobalTheory.ArcExt.gtExt_injective f hf (by rw [map_nsmul, ht, ht', map_zero])
  have e : p'.g = gtExt D f hf (g₀ + t) := by rw [map_add (f := _), ht, add_sub_cancel]
  refine ⟨⟨p'.y, g₀ + t, h₀, (isNsmul_iff_eq _ _ _).2 ?_, hh₀⟩, rfl, (eq_gtExt_iff f hf _ _).1 e⟩
  rw [nsmul_add, ht0, add_zero, hg₀]

end GlobalTheory.QkClosure

namespace GlobalTheory.Mum

theorem qkPt_algClosure_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → (∀ p : QkPt D (Kb R) N, ∃! p' : QkPt D F N, QkExt em.toRingHom p p') ∧ ∀ p' : QkPt D F N, ∃! p : QkPt D (Kb R) N, QkExt em.toRingHom p p' := by
  intro R _ _ _ D F _ _ _ em N hN
  have hf := em.comp_algebraMap
  have : CharZero (Kb R) := (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  have hk : (N : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨fun p => ?_, fun p' => ?_⟩
  · obtain ⟨p', hp'⟩ := GlobalTheory.QkClosure.exists_qkExt em.toRingHom hf p
    exact ⟨p', hp', fun q hq => GlobalTheory.QkClosure.qkExt_unique em.toRingHom hf hq hp'⟩
  · obtain ⟨p, hp⟩ := GlobalTheory.QkClosure.exists_qkExt_descent em.toRingHom hf hk p'
    exact ⟨p, hp, fun q hq => GlobalTheory.QkClosure.qkExt_inj em.toRingHom hf hq hp⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LevelSecDesc

theorem levelSections_descend : ∀ (O : Type) [Ring O] (La : Type) [AddCommGroup La] [Module O La] (N : ℕ) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A) (act₀ : OActN O A₀) (eta : La → (𝟙_ (Over X) ⟶ A)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ a y, (eta y).left ≫ ν a = ρ a ≫ (eta y).left) → (∀ x y, eta (x + y) = eta x * eta y) → (∀ (c : O) x, eta (c • x) = eta x ≫ act.act c) → (∀ x, eta (N • x) = 1) → ∃ eta₀ : La → (𝟙_ (Over Y) ⟶ A₀), (∀ x y, eta₀ (x + y) = eta₀ x * eta₀ y) ∧ (∀ (c : O) x, eta₀ (c • x) = eta₀ x ≫ act₀.act c) ∧ (∀ x, eta₀ (N • x) = 1) ∧ ∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left := by
  intro O _ La _ _ N X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act act₀ eta hπ gp hφ hact heq hadd hlin htor
  have := hπ.etale
  have := hπ.onto
  have : Epi π := Flat.epi_of_flat_of_surjective π
  have desc : ∀ y, ∃ e : 𝟙_ (Over Y) ⟶ A₀, (eta y).left ≫ φ = π ≫ e.left := fun y => by
    obtain ⟨g, hg, -⟩ := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hπ).1 A₀.left ((eta y).left ≫ φ) fun a => by
      rw [← Category.assoc, ← heq a y, Category.assoc, hφ.inv a]
    exact GlobalTheory.ObjDesc.exists_sec gp (eta y) g hg
  choose eta₀ heta using desc
  have hse : ∀ y, GlobalTheory.ObjPull.secPull gp (eta₀ y) = eta y := fun y => GlobalTheory.ObjDesc.secPull_eq gp (heta y)
  refine ⟨eta₀, fun x y => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_mul, hse, hse, hse, hadd]),
    fun c x => ?_, fun x => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_one, hse, htor]), heta⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi π, ← heta, hlin, Over.comp_left, Over.comp_left, Category.assoc, hact c, ← Category.assoc,
    heta, Category.assoc]

end GlobalTheory.LevelSecDesc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicitiesGeometricPointsDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieDesc

theorem lieMult_descend : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∀ i, LieMult (act₀.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ hG _ _ hpb hact hX k _ _ x β hx i
  haveI : Surjective π := hG.onto
  haveI : IsFinite π := hG.fin
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  have hc : ∀ c, ((act.toF D).act c).left ≫ φ = φ ≫ ((act₀.toF D).act c).left := fun c => hact _
  exact (GlobalTheory.LiePull.lieMult_pull _ _ _ A₀ A π φ (act₀.toF D) (act.toF D) hpb hc k y _ D.m).1
    (hX k y β (by rw [← Category.assoc]; exact hx) i)

end GlobalTheory.LieDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompPartialSumPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section
namespace GlobalTheory.MumFam
variable {R : Type} [CommRing R] [IsDomain R]

section
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G)

theorem padd_eq_mul' (x y : T ⟶ G) : padd G x y = x * y := rfl
theorem pzero_eq_one' : pzero G T = 1 := rfl

theorem psum_pair_01 : psum G ![u, v] {0, 1} = u * v := by
  have hl : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_0 : psum G ![u, v] {0} = u := by
  have hl : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_1 : psum G ![u, v] {1} = v := by
  have hl : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_e : psum G ![u, v] ∅ = 1 := by
  have hl : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  rw [psum, hl]
  simp [pzero_eq_one']
end

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFinite
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RetractionLiftSection

theorem exists_retraction {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) :
    ∃ σ : A →+* R, (algebraMap R K).comp σ = ψ ∧ σ.comp φ = RingHom.id R := by
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have key : ∀ a : A, ∃ r : R, algebraMap R K r = ψ a := by
    intro a
    obtain ⟨f, hf, hfa⟩ := hφ a
    have hi : IsIntegral R (ψ a) := by
      refine ⟨f, hf, ?_⟩
      rw [← h, ← Polynomial.hom_eval₂, hfa, map_zero]
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hi
  choose s hs using key
  let σ : A →+* R :=
    { toFun := s
      map_one' := inj (by rw [hs, map_one, map_one])
      map_mul' := fun a b => inj (by rw [map_mul, hs, hs, hs, map_mul])
      map_zero' := inj (by rw [hs, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [map_add (f := _), hs, hs, hs, map_add (f := _)]) }
  refine ⟨σ, RingHom.ext hs, RingHom.ext fun r => inj ?_⟩
  exact (hs (φ r)).trans (RingHom.congr_fun h r)

theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {W : Scheme.{0}} (q : W ⟶ Spec (CommRingCat.of R)) [IsFinite q]
    (y : Spec (CommRingCat.of K) ⟶ W) (h : y ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ W, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = y ∧ s ≫ q = 𝟙 _ := by
  haveI : IsAffine W := isAffine_of_isAffineHom q
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ q)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ W.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, h]
  obtain ⟨σ, h₁, h₂⟩ := exists_retraction (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ W.isoSpec.inv, ?_, ?_⟩
  · have e : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h₁
    rw [← Category.assoc, ← Spec.map_comp]
    erw [e]
    rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · have e : φ ≫ CommRingCat.ofHom σ = 𝟙 _ := CommRingCat.hom_ext h₂
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    erw [e]
    rw [Spec.map_id]

theorem exists_lift {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z P : Scheme.{0}} (p : Z ⟶ P) [IsFinite p] (x : Spec (CommRingCat.of R) ⟶ P)
    (y : Spec (CommRingCat.of K) ⟶ Z) (h : y ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x) :
    ∃ ξ : Spec (CommRingCat.of R) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ ξ = y ∧ ξ ≫ p = x := by
  obtain ⟨s, h₁, h₂⟩ := exists_section (K := K) (pullback.snd p x) (pullback.lift y _ h) (pullback.lift_snd _ _ _)
  refine ⟨s ≫ pullback.fst p x, ?_, ?_⟩
  · rw [← Category.assoc, h₁, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]

theorem lift_finite : ∀ (R : Type) [inst : CommRing R] [IsDomain R] [IsIntegrallyClosed R] (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ P) (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing R) ⟶ Z), AlgebraicGeometry.IsFinite p → CategoryTheory.CategoryStruct.comp y p = CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Out.jK R) ξ₀ → ∃ (ξ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Out.jK R) ξ = y ∧ CategoryTheory.CategoryStruct.comp ξ p = ξ₀ :=
  fun R _ _ _ _ _ p x y _ h => exists_lift (R := R) (K := FractionRing R) p x y h

end GlobalTheory.RetractionLiftSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongSmallExtensionOfDualNumberLifting
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem smallLift_of_tanLift : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) [Smooth U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → SmallLift A M := by
  intro S _ A _ hA U _ M hM hI hT C _ _ e he hk s N hN u₀ h
  have hsq : (Ideal.span {e}) ^ 2 = ⊥ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, sq]
    exact hk e he
  obtain ⟨v, hv, hp⟩ := GlobalTheory.T.smooth_exists_point_lift_squareZero_localRing U.left S U.hom C (Ideal.span {e}) hsq s u₀.left (Over.w u₀)
  let u' : Over.mk s ⟶ U := Over.homMk v hp
  have hu : u₀ = ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u' := by
    ext1
    exact hv.symm
  by_cases h0 : e = 0
  · have hb : Function.Bijective (Ideal.Quotient.mk (Ideal.span {e})) := by
      refine ⟨?_, Ideal.Quotient.mk_surjective⟩
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_eq_bot]
      exact h0
    have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) :=
      (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
    have : IsIso (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))).left :=
      inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e})))))
    have : IsIso ((Over.forget S).map (ptMap s (Ideal.Quotient.mk (Ideal.span {e})))) := this
    have : IsIso (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) := isIso_of_reflects_iso _ (Over.forget S)
    have h' := (_root_.GlobalTheory.FamCalc.famCalc S A).2.2.2.1 _ _ _ _ N M _ _ (inv (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))))
      hN.isLB hM.isLB h
    rw [IsIso.inv_hom_id] at h'
    exact ⟨_, h'⟩
  · exact _root_.GlobalTheory.DualOpen.exists_same_of_smallExt S A hA U M hM hI hT C e he hk h0 s N hN u' (hu ▸ h)

end GlobalTheory.DualOpen
end

