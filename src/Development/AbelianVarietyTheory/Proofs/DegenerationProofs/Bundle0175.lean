module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesIdentityPrincipleComplexPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ArcIdentity

theorem exists_form {O O' : Type} [CommRing O] [CommRing O'] {N : NumD O} {N' : NumD O'} (e : N.X ≃+ N'.X) {k : ℕ}
    (β : N'.Form k) : ∃ b : N.Form k, ∀ y z, b.be y z = β.be (e y) (e z) := by
  refine ⟨⟨β.be.compl₁₂ e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap, fun y z => ?_,
    fun y hy => ?_, fun y z => ?_⟩, fun y z => ?_⟩
  · simpa using β.symm (e y) (e z)
  · simpa using β.pos (e y) (fun h => hy (e.injective (by rw [h, map_zero])))
  · simpa using β.dvd (e y) (e z)
  · simp

theorem arcTx_qEq {O : Type} [CommRing O] (N : NumD O) (be : LinearMap.BilinForm ℤ N.X) {m : ℕ} (ho : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.arcTx be m p' = N.arcTx be m p := by
  obtain ⟨z, h1, h2⟩ := h
  ext n
  simp only [NumD.arcTx, PowerSeries.coeff_mk]
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (m • z))]
  refine finsum_congr fun χ => ?_
  have hx : p'.1.1.toAdd + m • χ = p.1.1.toAdd + m • (χ + m • z) := by
    rw [h1, smul_add, smul_smul, ← pow_two]
    abel
  simp only [Equiv.coe_addRight, hx, (_root_.GlobalTheory.Ex.txT_shift O N m ho p p' χ).1 z h1 h2]

private theorem map_finsum_of_injective' {α M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (φ : M →+ M')
    (hφ : Function.Injective φ) (g : α → M) : φ (∑ᶠ a, g a) = ∑ᶠ a, φ (g a) := by
  by_cases h : (Function.support g).Finite
  · exact map_finsum φ h
  · have hs : Function.support (fun a => φ (g a)) = Function.support g := by
      ext a
      simp only [Function.mem_support, ne_eq]
      exact ⟨fun h1 h2 => h1 (by rw [h2, map_zero]), fun h1 h2 => h1 (hφ (by rw [h2, map_zero]))⟩
    have h' : (Function.support (fun a => φ (g a))).Infinite := by
      rw [hs]
      exact h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', map_zero]

private theorem unit_mul_map_finsum {α F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : F'ˣ) (g : α → F) :
    (c : F') * f (∑ᶠ a, g a) = ∑ᶠ a, (c : F') * f (g a) := by
  refine map_finsum_of_injective' ((AddMonoidHom.mulLeft (c : F')).comp f.toAddMonoidHom) ?_ g
  intro a b hab
  have hab' : (c : F') * f a = (c : F') * f b := hab
  exact f.injective (mul_left_cancel₀ c.ne_zero hab')

private theorem unit_mul_map_finsum_prop {F F' : Type*} [Field F] [Field F'] (f : F →+* F') (c : F'ˣ) (P : Prop)
    (x : F) : (c : F') * f (∑ᶠ (_ : P), x) = ∑ᶠ (_ : P), (c : F') * f x := by
  classical
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem arcTx_hom {F F' : Type} [Field F] [Field F'] {f : F →+* F'} {N : NumD F} {N' : NumD F'} (I : NumD.Hom f N N')
    (be : LinearMap.BilinForm ℤ N.X) (be' : LinearMap.BilinForm ℤ N'.X) (hb : ∀ y z, be y z = be' (I.e y) (I.e z))
    {m : ℕ} (ho : Odd m) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h1 : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (h2 : I.Rel p.1.2 p'.1.2) :
    N'.arcTx be' m p' = PowerSeries.C (I.lam : F') * PowerSeries.map f (N.arcTx be m p) := by
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  simp only [NumD.arcTx, PowerSeries.coeff_mk, unit_mul_map_finsum f I.lam, unit_mul_map_finsum_prop f I.lam]
  conv_lhs => rw [← finsum_comp_equiv I.e.toEquiv]
  refine finsum_congr fun χ => ?_
  have hx : p'.1.1.toAdd + m • I.e χ = I.e (p.1.1.toAdd + m • χ) := by
    rw [h1, map_add (f := _), map_nsmul]
  have hχ : I.e.toEquiv χ = I.e χ := rfl
  rw [hχ]
  simp only [hx, ← hb, I.txT_eq ho p p' h1 h2 χ]

private theorem eval2_smul_of_isHomogeneous {J S T : Type*} [CommSemiring S] [CommSemiring T] (g : S →+* T) (c : T)
    (w : J → T) {G : MvPolynomial J S} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.eval₂ g (fun x => c * w x) G = c ^ d * MvPolynomial.eval₂ g w G := by
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hG.degree_eq_sum_deg_support hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem aeval_smul_map {J S F F' : Type} [CommRing S] [CommRing F] [CommRing F'] (f : F →+* F') (c : S →+* F)
    (l : F') (v : J → PowerSeries F) {G : MvPolynomial J S} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.aeval (fun x => PowerSeries.C l * PowerSeries.map f (v x)) (MvPolynomial.map (f.comp c) G) =
      PowerSeries.C l ^ d * PowerSeries.map f (MvPolynomial.aeval v (MvPolynomial.map c G)) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
    eval2_smul_of_isHomogeneous _ _ (fun x => PowerSeries.map f (v x)) hG, MvPolynomial.eval₂_comp_left]
  have hr : (PowerSeries.map f).comp ((algebraMap F (PowerSeries F)).comp c) =
      (algebraMap F' (PowerSeries F')).comp (f.comp c) :=
    RingHom.ext fun a => by simp [PowerSeries.map_C]
  rw [hr]
  rfl

theorem cf_comp {F F' : Type} [CommRing F] [CommRing F'] (f : F →+* F') (a b : F) :
    cf (f a) (f b) = f.comp (cf a b) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
  {R' : Type} [CommRing R'] [IsDomain R'] {F' : Type} [Field F'] [Algebra (FractionRing R') F']

theorem over_iff {f : F →+* F'} {A : ArcF D R F} {A' : ArcF D R' F'} (h : A.Over f A') :
    ∃ e : A.N.X ≃+ A'.N.X, ∀ (k : ℕ) (β : A.N.Form k) (β' : A'.N.Form k), (∀ y z, β.be y z = β'.be (e y) (e z)) →
      (A.Bal β ↔ A'.Bal β') ∧ ∀ m : ℕ, Odd m → ∀ (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) (d : ℕ),
        G.IsHomogeneous d →
        (MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x))
            (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 ↔
          MvPolynomial.aeval (fun x => A'.N.arcTx β'.be m (A'.q _ x))
            (MvPolynomial.map (cf (A'.I.ζ (m ^ 2) : F') A'.ρ) G) = 0) := by
  obtain ⟨I, hρ, hζ, hact, hq⟩ := h
  refine ⟨I.e, fun k β β' hbe => ⟨?_, fun m hm G d hG => ?_⟩⟩
  · constructor
    · intro hB a y' z'
      obtain ⟨y, rfl⟩ := I.e.surjective y'
      obtain ⟨z, rfl⟩ := I.e.surjective z'
      have h1 := hB a y z
      rw [hbe, hbe, hact, hact] at h1
      exact h1
    · intro hB a y z
      rw [hbe, hbe, hact, hact]
      exact hB _ _ _
  · have hpos : 0 < m ^ 2 := pow_pos hm.pos 2
    have hv : ∀ x, A'.N.arcTx β'.be m (A'.q _ x) =
        PowerSeries.C (I.lam : F') * PowerSeries.map f (A.N.arcTx β.be m (A.q (m ^ 2) x)) := by
      intro x
      obtain ⟨p', h1, h2, h3⟩ := hq (m ^ 2) x hpos
      rw [arcTx_qEq A'.N β'.be hm h3]
      exact arcTx_hom I β.be β'.be hbe hm h1 h2
    have hcf : cf (A'.I.ζ (m ^ 2) : F') A'.ρ = f.comp (cf (A.I.ζ (m ^ 2) : F) A.ρ) := by
      rw [← hρ, ← hζ _ hpos, cf_comp]
    simp only [hv, hcf]
    rw [aeval_smul_map f (cf (A.I.ζ (m ^ 2) : F) A.ρ) (I.lam : F') (fun x => A.N.arcTx β.be m (A.q (m ^ 2) x)) hG]
    have hC : PowerSeries.C (I.lam : F') ^ d ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero_iff _ PowerSeries.C_injective).mpr I.lam.ne_zero)
    constructor
    · intro h0
      rw [h0, map_zero, mul_zero]
    · intro h0
      have h0' := (mul_eq_zero.mp h0).resolve_left hC
      exact PowerSeries.map_injective f f.injective (by rw [h0', map_zero])

theorem aeval_arcTx_eq_zero_of_vanishC : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F) (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ m : ℕ, m ^ 2 ∣ k → Odd m → Compat H (m ^ 2) (A.I.ζ (m ^ 2) : F) A.ρ → ∀ G, VanishC D m G → MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x)) (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 := by
  intro hHV h6 hU hE hT hEnd hTU
  have hHV' := hHV
  obtain ⟨⟨hL, hL2, -⟩, -⟩ := hHV'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hWp := GlobalTheory.WeilValues.weil_eq_values hGt (GlobalTheory.Ex.brFam hL hL2)
  have hC4400 := _root_.GlobalTheory.Ex.Arch.exists_full_of_small hHV h6 hU hE hT hEnd hTU
  have hdown := GlobalTheory.FieldPull.exists_countable_model hL hGt hWp
  have hup := GlobalTheory.ArcExt.exists_arcF_over hL hGt hWp
  unfold AllD at hC4400 hdown hup ⊢
  intro E _ _ _ H D R _ _ F _ _ _ _ A k β hB m hmk hm hC G hV
  obtain ⟨-, ⟨d, hG⟩, hVan⟩ := hV
  have hpos : 0 < m ^ 2 := pow_pos hm.pos 2
  obtain ⟨R₁, F₁, _, _, _, _, _, _, f, A₁, hA₁⟩ := hdown E H D R F A
  haveI : CharZero F₁ := A₁.charZero
  obtain ⟨e₁, he₁⟩ := over_iff hA₁
  obtain ⟨β₁, hβ₁⟩ := exists_form e₁ β
  have h1 := he₁ k β₁ β hβ₁
  rw [← h1.2 m hm G d hG]
  obtain ⟨I₁, hρ₁, hζ₁, _, _⟩ := hA₁
  have hC₁ : Compat H (m ^ 2) (A₁.I.ζ (m ^ 2) : F₁) A₁.ρ := by
    intro c hc
    have h0 := hC c hc
    rw [← hρ₁, ← hζ₁ _ hpos, cf_comp, RingHom.comp_apply] at h0
    exact f.injective (by rw [h0, map_zero])
  have halg : ∀ i, IsAlgebraic ℚ (![zeta (m ^ 2), H.rt0] i) := by
    intro i
    fin_cases i
    · show IsAlgebraic ℚ (zeta (m ^ 2))
      have hz : IsPrimitiveRoot (zeta (m ^ 2)) (m ^ 2) := by
        unfold zeta
        exact Complex.isPrimitiveRoot_exp _ hpos.ne'
      refine IsIntegral.isAlgebraic (IsIntegral.of_pow hpos ?_)
      rw [hz.pow_eq_one]
      exact isIntegral_one
    · show IsAlgebraic ℚ H.rt0
      refine IsIntegral.isAlgebraic (IsIntegral.of_pow (n := 2) two_pos ?_)
      rw [H.sqrt_neg_disc_sq]
      have hd := isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := -(H.d : ℚ))
      simpa using hd
  obtain ⟨g, hg⟩ := GlobalTheory.exists_ringHom_complex_of_countable_of_relations F₁
    ![(A₁.I.ζ (m ^ 2) : F₁), A₁.ρ] ![zeta (m ^ 2), H.rt0] halg hC₁
  have hg0 : g (A₁.I.ζ (m ^ 2) : F₁) = zeta (m ^ 2) := by simpa using hg 0
  have hg1 : g A₁.ρ = H.rt0 := by simpa using hg 1
  letI : Algebra (FractionRing R₁) ℂ := (g.comp (algebraMap (FractionRing R₁) F₁)).toAlgebra
  obtain ⟨A₂, -, hA₂⟩ := hup E H D R₁ F₁ ℂ g (fun x => rfl) A₁
  obtain ⟨e₂, he₂⟩ := over_iff hA₂
  obtain ⟨β₂, hβ₂⟩ := exists_form e₂.symm β₁
  have hb12 : ∀ y z, β₁.be y z = β₂.be (e₂ y) (e₂ z) := by
    intro y z
    rw [hβ₂]
    simp
  have h2 := he₂ k β₁ β₂ hb12
  rw [h2.2 m hm G d hG]
  obtain ⟨I₂, hρ₂, hζ₂, _, _⟩ := hA₂
  have hρ₂' : A₂.ρ = H.rt0 := by rw [← hρ₂, hg1]
  have hζ₂' : (A₂.I.ζ (m ^ 2) : ℂ) = zeta (m ^ 2) := by rw [← hζ₂ _ hpos, hg0]
  have hB₂ : A₂.Bal β₂ := h2.1.mp (h1.1.mpr hB)
  obtain ⟨ε, hε, hsmall⟩ := hC4400 E H D R₁ A₂ hρ₂' k β₂ hB₂ m hmk hm
  rw [hζ₂', hρ₂']
  refine GlobalTheory.Ex.ArcForm.aeval_arcTx_eq_zero A₂.N k β₂ m hmk hm D.La (fun x => A₂.q _ x) _ ε hε
    fun u hu => ⟨(hsmall u hu).1, ?_⟩
  obtain ⟨o, hoρ, hoζ, hθ⟩ := (hsmall u hu).2
  rw [MvPolynomial.eval_map]
  exact hVan o hoρ (by rw [hoζ]; exact hζ₂') _ hθ

end GlobalTheory.ArcIdentity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemBaseSectionValueChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

def GV (c : S.J → Ω) (a : Q.L.L.ι) (K : Type) [Field K] (x : Sp K ⟶ Q.G.left) (v : K) : Prop :=
  ∀ (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left)
    (jP : ρ.P.L.ι), g ≫ Q.φ = x → g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt →
    r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
    ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP →
    ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v

variable {K : Type} [Field K] {c : S.J → Ω} {a a' : Q.L.L.ι}

theorem le_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a) :
    ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U (fun _ => jP, fun _ => a) :=
  le_inf' (le_wchart _ _ _ fun _ => h) (le_wchart _ _ _ fun _ => h')

theorem val_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a)
    (k : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP') (k' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a') :
    valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val =
      valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (ρ.P.L.g jP jP').val * (valF (g ≫ Q.φ) _ (Q.L.L.g a a').val)⁻¹ *
        valF g _ (Q.w.s (fun _ => jP', fun _ => a')).val := by
  refine (val_gen Q.w_gen g (le_w Q h h') (le_w Q k k')).trans (congrArg (· * _) ?_)
  refine (val_div_g _ _ _ _ g (le_w Q h h') (le_w Q k k')).trans ?_
  exact congrArg₂ (fun x y => x * y⁻¹) ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h k).trans (zpow_one _))
    ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h' k').trans (zpow_one _))

omit Q in
theorem thetaSystem_baseSection_value_chart {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP)
    (k : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP') (i : S.J) :
    valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) _ (ρ.P.L.g jP jP').val ^ (S.N : ℤ) *
        valF r _ ((ρ.s i).f (fun _ => jP')) :=
  (val_sec (ρ.s i) r (j := fun _ => jP) (k := fun _ => jP') (le_wchart _ _ _ fun _ => h)
    (le_wchart _ _ _ fun _ => k)).trans (congrArg (· * _) (val_linComb_g (I := Fin 1) _ _ _ _ _ r h k))

theorem exists_data (hU : (U₀ : Set M.Z).Nonempty) {Y : Scheme.{0}} (x : Y ⟶ Q.G.left) (κ : Y ⟶ Sp Ω)
    (h : x ≫ Q.G.hom = κ ≫ M.pt) : ∃ (g : Y ⟶ pullback ρ.P.A.hom Q.u₀) (r : Y ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = κ ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ := by
  have hr : Set.range (κ ≫ M.pt) ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := κ w) trivial
  let y : Y ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (κ ≫ M.pt) hr
  have hy : y ≫ U₀.ι = κ ≫ M.pt := IsOpenImmersion.lift_fac _ _ _
  let g : Y ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift x y (h.trans hy.symm)
  have hg2 : g ≫ pullback.snd _ _ = y := Q.cart.1.lift_snd x y _
  refine ⟨g, pullback.lift ((g ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _)
    (Category.comp_id _), Q.cart.1.lift_fst x y _, ?_, pullback.lift_snd _ _ _⟩
  rw [← Category.assoc, hg2, hy]

theorem exists_data' (hU : (U₀ : Set M.Z).Nonempty) (x : Sp K ⟶ Q.G.left) (β : Ω →+* K)
    (h : x ≫ Q.G.hom = spMap β ≫ M.pt) : ∃ (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ ∧
      ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP := by
  obtain ⟨g, r, h1, h2, h3⟩ := exists_data Q hU x _ h
  obtain ⟨jP, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ρ.P.isLB.cover
  exact ⟨g, r, jP, h1, h2, h3, hj⟩

variable {Q} {x : Sp K ⟶ Q.G.left} {v v' : K}

theorem GV.unique (hU : (U₀ : Set M.Z).Nonempty) {β : Ω →+* K} (h : x ≫ Q.G.hom = spMap β ≫ M.pt)
    (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (H : GV Q c a K x v) (H' : GV Q c a K x v') : v = v' := by
  obtain ⟨g, r, jP, rfl, h2, h3, hj⟩ := exists_data' Q hU x β h
  exact mul_left_cancel₀ (zpow_ne_zero _ (val_unit_ne g (le_w Q hj ha) _))
    ((H β g r jP rfl h2 h3 hj).symm.trans (H' β g r jP rfl h2 h3 hj))

theorem GV.chart (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (ha' : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a') (H : GV Q c a K x v) :
    GV Q c a' K x (valF x _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * v) := by
  rintro β g r jP rfl h2 h3 hj
  have h0 := zpow_ne_zero (S.N : ℤ) (val_unit_ne _ (le_inf' ha' ha) (Q.L.L.g a' a))
  rw [H β g r jP rfl h2 h3 hj, val_w Q hj ha' hj ha, val_g_self ρ.P.isLB _ hj, _root_.one_mul, mul_zpow, inv_zpow]
  field_simp

theorem GV.of_one {β : Ω →+* K} {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀}
    {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP : ρ.P.L.ι} (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (h1 : g ≫ Q.φ = x)
    (h2 : g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt)
    (h3 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _)
    (hj : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP)
    (H : ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v) : GV Q c a K x v := by
  intro β' g' r' jP' k1 k2 k3 kj
  have : Mono Q.φ := (MorphismProperty.monomorphisms _).of_isPullback Q.cart.1.flip
    (inferInstanceAs (Mono U₀.ι))
  have := EndoExtend.isPreimmersion_pt M
  have : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left := inferInstanceAs (Mono (pullback.snd (𝟙 _) ρ.P.A.hom))
  obtain rfl : g' = g := (cancel_mono Q.φ).1 (k1.trans h1.symm)
  obtain rfl : r' = r := (cancel_mono _).1 (k3.trans h3.symm)
  obtain rfl : β' = β := congrArg (·.hom) (Spec.map_injective ((cancel_mono M.pt).1 (k2.symm.trans h2)))
  subst h1
  rw [val_w Q kj ha hj ha, val_g_self Q.L.isLB _ ha, inv_one, _root_.mul_one, mul_zpow, _root_.mul_assoc, ← H,
    Finset.mul_sum, ← h3]
  rw [← h3] at kj hj
  exact Finset.sum_congr rfl fun i _ => by rw [thetaSystem_baseSection_value_chart kj hj, mul_left_comm]

section Ratio

theorem exists_pt {X : Scheme.{0}} (y : X) : ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ X), ∀ w, g w = y :=
  ⟨X.residueField y, inferInstance, X.fromSpecResidueField _, fun _ => Scheme.fromSpecResidueField_apply _ _⟩

theorem exists_ne {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec} (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (h : Sp K ⟶ P) {k : O.ι} (hk : ⊤ ≤ h ⁻¹ᵁ O.U k) : ∃ i, valF h _ ((τ i).f k) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top h hτ
  obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 ((le_preimage_iff h _).1 hi)
  have h1 := (le_preimage_iff h _).2 hk'
  have h2 := le_preimage_mono h (P.basicOpen_le _) h1
  refine ⟨i, ?_⟩
  rw [val_sec (τ i) h hk h2]
  exact mul_ne_zero (val_unit_ne h (le_inf' hk h2) _) ((le_preimage_basicOpen_iff h h2 _).1 h1).ne_zero

theorem exists_mem_basicOpen {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec}
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (y : P) {k : O.ι} (hk : y ∈ O.U k) : ∃ i, y ∈ P.basicOpen ((τ i).f k) := by
  obtain ⟨F, _, g, hg⟩ := exists_pt y
  have h1 : ⊤ ≤ g ⁻¹ᵁ O.U k := fun w _ => show g w ∈ O.U k from Set.mem_of_eq_of_mem (hg w) hk
  obtain ⟨i, hi⟩ := exists_ne hτ g h1
  exact ⟨i, Set.mem_of_eq_of_mem (hg (IsLocalRing.closedPoint F)).symm
    ((le_preimage_basicOpen_iff g h1 _).2 hi.isUnit trivial)⟩

variable (Q) {P : Scheme.{0}} (ν : P ⟶ Q.G.left) {O : LB P} (τ : S.J → O.Sec) (b : S.J → S.J → Ω)

def Ratio (a : Q.L.L.ι) (k : O.ι) (K : Type) [Field K] (h : Sp K ⟶ P) (v : K) : Prop :=
  v ≠ 0 ∧ ∀ i, GV Q (b i) a K (h ≫ ν) (v * valF h _ ((τ i).f k))

variable {Q ν τ b} {k k' : O.ι} {h : Sp K ⟶ P}

theorem Ratio.unique (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) {β : Ω →+* K}
    (e : (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt) (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (H : Ratio Q ν τ b a k K h v) (H' : Ratio Q ν τ b a k K h v') : v = v' := by
  obtain ⟨i, hi⟩ := exists_ne hτ h hk
  exact mul_right_cancel₀ hi ((H.2 i).unique hU e ha (H'.2 i))

theorem Ratio.chart (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (ha' : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a') (hk' : ⊤ ≤ h ⁻¹ᵁ O.U k') (H : Ratio Q ν τ b a k K h v) :
    Ratio Q ν τ b a' k' K h
      (valF (h ≫ ν) _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * (valF h _ (O.g k' k).val)⁻¹ * v) := by
  have h1 := val_unit_ne _ (le_inf' hk' hk) (O.g k' k)
  refine ⟨mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (val_unit_ne _ (le_inf' ha' ha) _)) (inv_ne_zero h1)) H.1,
    fun i => ?_⟩
  convert (H.2 i).chart ha ha' using 1
  rw [val_sec (τ i) h hk' hk]
  field_simp

theorem exists_unit (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (hp : ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ P), (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt →
      ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a → ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v, Ratio Q ν τ b a k K h v)
    {Y : Scheme.{0}} [IsIntegral Y] (J : Y ⟶ P) (κ : Y ⟶ Sp Ω) (hJ : (J ≫ ν) ≫ Q.G.hom = κ ≫ M.pt)
    (V : Y.Opens) (hV : V ≤ (J ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hV' : V ≤ J ⁻¹ᵁ O.U k) :
    ∃ t : Γ(Y, V)ˣ, ∀ (K : Type) [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V →
      Ratio Q ν τ b a k K (h ≫ J) (valF h V t.val) := by
  have hβ : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), spMap (Spec.preimage (h ≫ κ)).hom = h ≫ κ := fun h =>
    Spec.map_preimage _
  have he : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y),
      ((h ≫ J) ≫ ν) ≫ Q.G.hom = spMap (Spec.preimage (h ≫ κ)).hom ≫ M.pt := fun h => by
    rw [hβ, Category.assoc h κ, ← hJ]; simp only [Category.assoc]
  have ha : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ ((h ≫ J) ≫ ν) ⁻¹ᵁ Q.L.L.U a :=
    fun h hh => le_preimage_mono h hV hh
  have hk : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ (h ≫ J) ⁻¹ᵁ O.U k :=
    fun h hh => le_preimage_mono h hV' hh
  obtain ⟨F, _, ξ, hξ⟩ := exists_generic Y
  obtain ⟨g, r, g1, g2, g3⟩ := exists_data Q hU _ κ hJ
  obtain ⟨f, hf⟩ := exists_glue V (fun K _ h v => Ratio Q ν τ b a k K (h ≫ J) v) ξ hξ
    (fun hh v v' H H' => H.unique hU hτ (he ξ) (ha ξ hh) (hk ξ hh) H') (fun y hy => by
      obtain ⟨jP, hj⟩ := exists_chart ρ.P.isLB ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) y)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen hτ (J y) (hV' hy)
      have m1 : r y ∈ (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).U (fun _ => jP) :=
        Set.mem_iInter.2 fun _ => by rw [← g3] at hj; exact hj
      have m2 : g y ∈ (pullback ρ.P.A.hom Q.u₀).basicOpen (Q.w.s (fun _ => jP, fun _ => a)).val := by
        rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]
        have := hV hy
        rw [← g1] at this
        exact ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => this⟩
      obtain ⟨W, f, hW, hf⟩ := ((Reg.sum Finset.univ fun l => (Reg.val κ (U := ⊤)
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (b i l)) trivial).mul (Reg.val r ((ρ.s l).f _) m1)).mul
        ((Reg.inv g _ m2).pow S.N)).mul (Reg.inv J _ hi)
      refine ⟨W ⊓ ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP ⊓ J ⁻¹ᵁ P.basicOpen ((τ i).f k)),
        resG Y inf_le_left f, ⟨hW, hj, hi⟩, fun K _ h h1 h2 => ?_⟩
      obtain ⟨v, hv⟩ := hp K _ _ (he h) (ha h h2) (hk h h2)
      have n1 : ⊤ ≤ ((h ≫ g) ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP :=
        le_preimage_mono h (inf_le_right.trans inf_le_left) h1
      have n2 : ⊤ ≤ (h ≫ J) ⁻¹ᵁ P.basicOpen ((τ i).f k) := le_preimage_mono h (inf_le_right.trans inf_le_right) h1
      have n3 : (h ≫ g) ≫ Q.φ = (h ≫ J) ≫ ν := by rw [Category.assoc, g1, Category.assoc]
      have e := hv.2 i _ (h ≫ g) (h ≫ r) jP n3 (by rw [Category.assoc, g2, hβ, Category.assoc])
        (by rw [Category.assoc, g3, Category.assoc]) n1
      have z1 : valF (h ≫ J) _ ((τ i).f k) ≠ 0 := ((le_preimage_basicOpen_iff _ (hk h h2) _).1 n2).ne_zero
      have z2 := val_unit_ne (h ≫ g) (le_w Q n1 (n3 ▸ ha h h2)) (Q.w.s (fun _ => jP, fun _ => a))
      convert hv using 1
      refine (valR_res h _ h1 _).trans ((hf K h (le_preimage_mono h inf_le_left h1)).trans ?_)
      rw [zpow_natCast] at e
      have key : ∀ (A w t : K), w ≠ 0 → t ≠ 0 → A = w ^ S.N * (v * t) → A * (w⁻¹) ^ S.N * t⁻¹ = v := by
        rintro _ w t h1 h2 rfl
        rw [inv_pow]
        field_simp
      refine key _ _ _ z2 z1 (Eq.trans (Finset.sum_congr rfl fun l _ => ?_) e)
      rw [preimage_apply (h ≫ κ) (b i l)]
      rfl)
  exact ⟨(isUnit_of_val f fun K _ h hh => (hf K h hh).1).unit, hf⟩

end Ratio

end GlobalTheory.ZH.PowSec
end

