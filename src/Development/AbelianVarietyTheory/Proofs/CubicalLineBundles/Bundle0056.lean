module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCMPairingFamilyOfPolarisationDiagonalComplex
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CurveAdjoint

theorem linear_eq_of_ex {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (G z)) : F = G := by
  have hD : ∀ z, (F - G) z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h1 := u.ex_add (G z) ((F - G) z)
    have e : G z + (F - G) z = F z := by simp
    rw [e, h z] at h1
    exact mul_left_cancel (a := u.ex (G z)) (by rw [_root_.mul_one]; exact h1.symm)
  refine LinearMap.ext fun z => ?_
  have hc : Continuous (fun t : ℝ => (⟨(F - G) ((t : ℂ) • z), hD _⟩ : u.Λ)) :=
    Continuous.subtype_mk ((F - G).continuous_of_finiteDimensional.comp
      (Complex.continuous_ofReal.smul continuous_const)) _
  haveI := u.discrete
  have h2 := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0))
  simp only [Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, map_zero] at h2
  exact sub_eq_zero.mp h2

theorem exists_scalar {g : ℕ} (hg : g = 1) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : ∃ c : ℂ, ∀ z, F z = c • z := by
  subst hg
  refine ⟨F (fun _ => 1) 0, fun z => ?_⟩
  have hz : z = z 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
    funext i
    rw [Subsingleton.elim i 0]
    simp
  rw [hz, map_smul]
  funext i
  rw [Subsingleton.elim i 0]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem map_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (j : OK H →+* ℂ) (x y : OK H)
    (h : (y : 𝓞 E) = H.bar x) : j y = starRingEnd ℂ (j x) := by
  obtain ⟨-, huniq, ⟨br, hbr, hw, -⟩, hquad, -⟩ := OK_isDedekindDomain_and_projective E H
  have hy : y = br x := Subtype.ext (h.trans (hbr x).symm)
  have hbw : br (wK H) = 1 - wK H := eq_sub_of_add_eq' hw
  obtain ⟨⟨m₁, m₂⟩, hx, -⟩ := huniq x
  have hN : (1 : ℝ) ≤ (((1 + H.d) / 4 : ℕ) : ℝ) := by
    have := H.d_mod
    exact_mod_cast (by omega : 1 ≤ (1 + H.d) / 4)
  have hq := congrArg j hquad
  simp only [j.map_add, j.map_pow, map_natCast j] at hq
  have hz : starRingEnd ℂ (j (wK H)) = 1 - j (wK H) := by
    have e := congrArg Complex.re hq
    have f := congrArg Complex.im hq
    simp [pow_two] at e f
    have ha : (j (wK H)).re = 1 / 2 := by
      rcases eq_or_ne (j (wK H)).im 0 with h0 | h0
      · exfalso
        rw [h0] at e
        nlinarith [sq_nonneg ((j (wK H)).re - 1 / 2)]
      · have h2 : 2 * (j (wK H)).re = 1 := by
          apply mul_left_cancel₀ h0
          linear_combination f
        linarith
    apply Complex.ext <;> simp <;> linarith
  rw [hy, hx]
  simp only [br.map_add, br.map_mul, map_intCast br, hbw, j.map_add, j.map_mul,
    map_intCast j, j.map_sub, j.map_one, map_add (starRingEnd ℂ),
    map_mul (starRingEnd ℂ), map_intCast (starRingEnd ℂ), hz]

theorem lamEq_act_bar : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (a : OAct (OK H) P.A), Function.Injective σ → P.g = 1 → ∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) := by
  intro hT hL E _ _ _ H R _ _ σ P a hσ hg x y hxy
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨Q, φ, hQg, hφ, hLφ⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange σ P
  haveI : IsCommMonObj Q.A := Q.isAb.comm
  have hQ1 : Q.g = 1 := hQg.trans hg
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, hend, -⟩ := hT Q rig hrig
  have hex : ∀ r : OK H, ∃ c : ℂ, ∃ w' : Q.A ⟶ Q.A, IsMonHom w' ∧ w'.left ≫ φ = φ ≫ (a.act r).left ∧
      ∀ z, u.ex (c • z) = u.ex z ≫ w' := by
    intro r
    haveI := a.hom r
    obtain ⟨w', hw'm, hw'⟩ := GlobalTheory.PairingFibre.exists_hom hφ hφ (a.act r)
    obtain ⟨F, hF⟩ := hend w' hw'm
    obtain ⟨c', hc'⟩ := exists_scalar hQ1 F
    exact ⟨c', w', hw'm, hw', fun z => by rw [← hc' z, hF z]⟩
  choose c w hmon hcomm hlift using hex
  have hcomm' : ∀ r {Z : Scheme.{0}} (h : P.A.left ⟶ Z), (w r).left ≫ φ ≫ h = φ ≫ (a.act r).left ≫ h := by
    intro r Z h
    rw [← Category.assoc, hcomm r, Category.assoc]
  have huniq : ∀ r (c' : ℂ) (w' : Q.A ⟶ Q.A), w'.left ≫ φ = φ ≫ (a.act r).left →
      (∀ z, u.ex (c' • z) = u.ex z ≫ w') → c' = c r := by
    intro r c' w' hw' hl
    have hww : w' = w r := by
      apply Over.OverMorphism.ext
      apply hφ.1.hom_ext
      · rw [hw', hcomm r]
      · rw [Over.w w', Over.w (w r)]
    subst hww
    have he := linear_eq_of_ex u (c' • LinearMap.id) (c r • LinearMap.id) (fun z => by
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [hl, hlift r])
    have he' := congrFun (LinearMap.congr_fun he (fun _ => 1)) ⟨0, by omega⟩
    simpa using he'
  have hone : c 1 = 1 :=
    (huniq 1 1 (𝟙 Q.A) (by rw [a.one]; simp) (fun z => by simp)).symm
  have hmul : ∀ r s, c (r * s) = c r * c s := by
    intro r s
    refine (huniq (r * s) (c r * c s) (w r ≫ w s) ?_ ?_).symm
    · simp only [a.mul, Over.comp_left, Category.assoc, hcomm, hcomm']
    · intro z
      rw [← Category.assoc, ← hlift r z, ← hlift s (c r • z), smul_smul, _root_.mul_comm]
  have hadd : ∀ r s, c (r + s) = c r + c s := by
    intro r s
    refine (huniq (r + s) (c r + c s) (w r * w s) ?_ ?_).symm
    · let jm : Over.mk (Q.A.hom ≫ spMap σ) ⟶ P.A := Over.homMk φ hφ.1.w
      have h := hφ.2 Q.A (w r) (w s) (jm ≫ a.act r) (jm ≫ a.act s) (by simp [jm, hcomm r]) (by simp [jm, hcomm s])
      rw [← h, ← MonObj.comp_mul, ← a.add, Over.comp_left]
      simp [jm]
    · intro z
      rw [add_smul, u.ex_add, hlift r, hlift s, MonObj.comp_mul]
  let j : OK H →+* ℂ := RingHom.mk' ⟨⟨c, hone⟩, hmul⟩ hadd
  have hj : c y = starRingEnd ℂ (c x) := map_bar H j x y hxy
  have hQ : WeilEq Q.L (w x) (𝟙 Q.A) Q.L (𝟙 Q.A) (w y) (𝟙 (Sp ℂ)) := by
    rw [_root_.GlobalTheory.CM.weilEq_iff_hermForm_eq hT hL Q Q Q Q u u u u Hm Hm χ χ hAH hAH (w x) (𝟙 Q.A) (𝟙 Q.A) (w y)
      (c x • LinearMap.id) LinearMap.id LinearMap.id (c y • LinearMap.id)
      (fun z => by simpa using hlift x z) (fun z => by simp) (fun z => by simp) (fun z => by simpa using hlift y z)]
    intro z v
    simp [hermForm, hj, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, star_smul]
  have hP : WeilEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) (spMap σ) := by
    have hb := (GlobalTheory.PairingFibre.weilEq_iff hφ hφ hφ hφ P.isLB P.isLB Q.isLB Q.isLB (LBIso.symm hLφ) (LBIso.symm hLφ)
      (f₁ := a.act x) (f₂ := 𝟙 P.A) (g₁ := 𝟙 P.A) (g₂ := a.act y)
      (f₁' := w x) (f₂' := 𝟙 Q.A) (g₁' := 𝟙 Q.A) (g₂' := w y)
      (hcomm x) (by simp) (by simp) (hcomm y) (𝟙 (Sp ℂ))).mp hQ
    rwa [Category.id_comp] at hb
  exact (GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hL R P P P P (a.act x) (𝟙 P.A) (𝟙 P.A) (a.act y)
    (a.hom x) inferInstance inferInstance (a.hom y) ℂ σ).2 inferInstance hσ hP

end GlobalTheory.CurveAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.PairingScheme

theorem exists_unitOn {K : Type} [CommRing K] (c : Γ(Sp K, ⊤)ˣ) : ∃ z : Kˣ, unitOn z = c := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c, ?_⟩
  ext
  simp [unitOn]

theorem comp_pow_eq_one {S : Scheme.{0}} {T X A : Over S} [GrpObj X] [GrpObj A] (f : X ⟶ A) [IsMonHom f]
    {x : T ⟶ X} {k : ℕ} (hx : x ^ k = 1) : (x ≫ f) ^ k = 1 := by
  rw [← MonObj.pow_comp, hx, MonObj.one_comp]

theorem pull_pow_eq_one {S : Scheme.{0}} {T T' X : Over S} [GrpObj X] (t : T' ⟶ T)
    {x : T ⟶ X} {k : ℕ} (hx : x ^ k = 1) : (t ≫ x) ^ k = 1 := by
  rw [← MonObj.comp_pow, hx, MonObj.comp_one]

theorem weilIs_iff_of_lamEq : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → ∀ (T : Over (Sp R)) (k : ℕ) (x : T ⟶ X.A) (y : T ⟶ Y.A) (c : Γ(T.left, ⊤)ˣ), 0 < k → x ^ k = 1 → y ^ k = 1 → (Out.WeilIs A.A A.L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs B.A B.L k (x ≫ g₁) (y ≫ g₂) c) := by
  intro hL R _ _ _ X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hlam T k x y c hk hx hy
  have hN : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  obtain ⟨T₀, x₀, y₀, hx₀, hy₀, huniv, hsep⟩ := _root_.GlobalTheory.LamF.exists_universal_torsion_pair hL R X Y k hk
  obtain ⟨a, ha, -⟩ := (hL.weil (Sp R) A k T₀).1 _ _ (comp_pow_eq_one f₁ hx₀) (comp_pow_eq_one f₂ hy₀)
  obtain ⟨b, hb, -⟩ := (hL.weil (Sp R) B k T₀).1 _ _ (comp_pow_eq_one g₁ hx₀) (comp_pow_eq_one g₂ hy₀)
  have hab : a = b := by
    apply Units.ext
    refine hsep _ _ fun k' _ _ _ β t => ?_
    have hw := (_root_.GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hL R X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ k' β).1 hlam
    have ha' := CommPairing.weilIs_pull hL.globalFns A.isAb A.isLB t ha
    have hb' := CommPairing.weilIs_pull hL.globalFns B.isAb B.isLB t hb
    obtain ⟨z, hz⟩ := exists_unitOn (K := k') (Units.map t.left.appTop.hom.toMonoidHom a)
    have hx' := pull_pow_eq_one t hx₀
    have hy' := pull_pow_eq_one t hy₀
    rw [← Category.assoc, ← Category.assoc] at ha' hb'
    have h₁ := (hw k (t ≫ x₀) (t ≫ y₀) z hk hx' hy').1 (by rw [hz]; exact ha')
    rw [hz] at h₁
    have h₂ := ((hL.weil (Sp R) B k _).1 _ _ (comp_pow_eq_one g₁ hx') (comp_pow_eq_one g₂ hy')).unique h₁ hb'
    exact congrArg Units.val h₂
  subst hab
  obtain ⟨t, rfl, rfl⟩ := huniv T x y hx hy
  have ha' := CommPairing.weilIs_pull hL.globalFns A.isAb A.isLB t ha
  have hb' := CommPairing.weilIs_pull hL.globalFns B.isAb B.isLB t hb
  rw [← Category.assoc, ← Category.assoc] at ha' hb'
  constructor
  · intro H
    rw [((hL.weil (Sp R) A k _).1 _ _ (comp_pow_eq_one f₁ hx) (comp_pow_eq_one f₂ hy)).unique H ha']
    exact hb'
  · intro H
    rw [((hL.weil (Sp R) B k _).1 _ _ (comp_pow_eq_one g₁ hx) (comp_pow_eq_one g₂ hy)).unique H hb']
    exact ha'

end GlobalTheory.PairingScheme
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurveHomFamilyToFibreAtPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem two_mul_sub_one_sq_of_ringHom (τ : OK H →+* ℂ) : (2 * τ (wK H) - 1) ^ 2 = -(H.d : ℂ) := by
  have h : (2 * wK H - 1) ^ 2 = -(H.d : OK H) := by
    apply Subtype.ext
    have e : 2 * H.w0 - 1 = H.rt := by rw [H.two_weight_eq_one_add_root]; ring
    have := H.rt_sq
    rw [← e] at this
    have e2 : ((2 : OK H) : 𝓞 E) = 2 := rfl
    simpa [wK, e2] using this
  have := congrArg (fun x : OK H => τ x) h
  set_option synthInstance.maxHeartbeats 200000 in
    simpa only [map_pow, map_sub, map_mul, map_ofNat, map_neg, map_natCast, map_intCast, map_one] using this

theorem exists_hermitianPairing_eq_im_mul_pureType {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty Pe) {ω : ℂ} {x : D.La} (hx : x ∈ PureType.lat hP (2 * ω - 1)) (h0 : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ω.im * r := by
  obtain ⟨Hm, hH, hpos, hEF⟩ := hP.2.2.2.2
  have hw0 : Pe (H.w0 • x) = ω • Pe x := by
    have e : (2 : ℂ) • Pe (H.w0 • x) = (2 : ℂ) • ω • Pe x := by
      rw [two_smul, ← map_add (f := _), ← add_smul, ← two_mul, H.two_weight_eq_one_add_root, add_smul, one_smul, map_add (f := _),
        PureType.period_rt_smul hP hx]
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact smul_right_injective _ two_ne_zero e
  have hne : Pe x ≠ 0 := fun h => h0 (hP.2.1 (by rw [h, map_zero]))
  refine ⟨_, hpos _ hne, ?_⟩
  have := PureTypeVector.hermForm_smul_smul Hm ω 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [← hEF, hw0, this]
  simp [PureTypeVector.hermForm_self_im hH]

theorem exists_isFam_complex : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (ω : ℂ) (C : Ell H ℂ ω) (u₀ : HolUnif C.P.A C.P.L C.P.g) (c : ℂ) (T : PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t (FU.u i Pe)) (ε : ℤˣ) (h : (FU.Di i).La → (FU.Di i).La → OK H), PureType.IsThetaUnif u₀ → c ≠ 0 → PureType.IsQuadLattice u₀.Λ H.d c → 0 < ((ε : ℤ) : ℝ) * ω.im → IsKForm (FU.Di i) ε h →
  ∃ ψ : PureType.lat hP (2 * ω - 1) → (C.P.A ⟶ T.t.G), IsFam C T h _ ψ ∧ ∀ a (z : ℂ), (u₀.ex (fun _ => c * z) ≫ ψ a).left ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  intro hT hL E _ _ _ H D l Xo g ty FU i Pe hP ω C u₀ c T m ε h hu hc hΛ hε hh
  obtain ⟨τ, hτ, -⟩ := _root_.GlobalTheory.CM.LieChar.ell_char E H ℂ ω C
  have hρ : (2 * ω - 1) ^ 2 = -(H.d : ℂ) := hτ ▸ two_mul_sub_one_sq_of_ringHom τ
  obtain ⟨φ, hφ, hφe⟩ := PureType.exists_isHomFamily_complex hT hL.weil FU i hP m u₀ C.dim hu hc hΛ hρ
  refine ⟨φ, _root_.GlobalTheory.CM.FamPairing.isFam_of_isHomFamily hT hL E H ω C _ ε h T _ φ hh (fun x hx h0 => ?_) (hφ _ (C.basis.1 0)), fun a z => ?_⟩
  · obtain ⟨r, hr, e⟩ := exists_hermitianPairing_eq_im_mul_pureType hP hx h0
    have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((FU.Di i).EF (H.w0 • x) x : ℤ) := by
      rw [e, ← _root_.mul_assoc]
      exact mul_pos hε hr
    exact_mod_cast this
  · rw [Over.comp_left, Category.assoc]
    exact hφe a z

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamEqOfWeilIsAllPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

private theorem pnsmulPt_eq_pow {S : Scheme.{0}} {G T : Over S} [GrpObj G] (n : ℕ) (a : T ⟶ G) :
    pnsmulPt n a = a ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem lamEq_of_weilIs_all_points : Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A) (g : A.A ⟶ A.A), IsMonHom f → IsMonHom g → (∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k → pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] → (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ g) y c)) → LamEq B.L f f A.L g (𝟙 A.A) := by
  intro laws K _ _ A B f g hf hg H
  have hβ : Function.Injective ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)) :=
    (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective (𝓞 K) K)
  refine (_root_.GlobalTheory.PairingFibre.lamEq_weilEq_over_ring laws (𝓞 K) A A B A f f g (𝟙 A.A) hf hf hg inferInstance (AlgebraicClosure K)
    ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K))).2 inferInstance hβ ?_
  intro n p q c hn hp hq
  rw [Category.comp_id]
  refine H _ n p q (unitOn c) hn ?_ ?_
  · rw [pnsmulPt_eq_pow, hp]; rfl
  · rw [pnsmulPt_eq_pow, hq]; rfl

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → (∀ b, IsUnit (g b).det) → LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → ∀ (b : E →+* ℂ) (j k : Fin (Dw.mult b)) (cl : z.K), IsLocGen p cl (z.ℓ (z.e ⟨b, j⟩)).I → iK cl * (g b)⁻¹ j k ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis | exact GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis | (intros; apply GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormalisedDegreeCmEigenLineEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem splits_of_injective_label {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    {lab : (E →+* ℂ) → (E →+* K)} (hl : Function.Injective lab) : GlobalTheory.CM.Splits E K := by
  rw [GlobalTheory.CM.splits_iff_card]
  refine le_antisymm GlobalTheory.CM.card_ringHom_le_finrank ?_
  have h1 : Nat.card (E →+* ℂ) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ
  rw [← h1]
  exact Nat.card_le_card_of_injective lab hl

theorem ndeg_vecLine_eq : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), IsFibreOf A x (gmap K) φ → Function.Injective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → ∀ (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ℓ.ndeg = (logOm E χ).re / 2 := by
  intro hD hU hL E _ _ _ _ H _ χ hχ hstar K _ _ A oa x φ S τ lab ρ hfib hl hρ hS hLie i ℓ hℓ
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (GlobalTheory.LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).1 hfib
  have hoa : ∃ act : OAct (𝓞 E) A.A, act.act = oa.act := by
    exact (GlobalTheory.LamF.ringAct_iff_oAct (𝓞 E) _ A.A).1 oa.1
  obtain ⟨act, hact⟩ := hoa
  have hsplit : GlobalTheory.CM.Splits E K := splits_of_injective_label hl
  have htype : HasType H act ρ 1 0 :=
    GlobalTheory.LamF.LieType.hasType_of_isLieType E H K A x φ hf oa act S τ lab ρ hact hl hS hLie
  have hlam : ∀ a, LamEq A.L (act.act a) (𝟙 A.A) A.L (𝟙 A.A) (act.act (H.bar a)) := by
    intro a
    have hr := oa.rosati a
    rw [← hact, hstar] at hr
    exact (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hL.globalFns _ A (act.act a) (act.act (H.bar a))
      (act.hom a) (act.hom (H.bar a))).1 hr
  set F : GenFib A := GenFib.mk x.P φ hf x.v x.basis with hF
  obtain ⟨⟨h, hh⟩, -⟩ := GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL K A F
  set t : 𝓞 E →+* 𝓞 K := RingOfIntegers.mapRingHom (lab (τ i)) with ht
  have htv : ∀ a : 𝓞 E, (t a : K) = lab (τ i) (a : E) := fun a => rfl
  have hti : t H.rt = ρ := by
    apply RingOfIntegers.ext
    rw [htv]
    exact (hS (τ i)).1 (τ i).2
  have hdeg := _root_.GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV hD hU hL E H χ hχ K ρ A act hlam hsplit hρ htype F h hh t hti
  have hline : deg h (F.eigLat act t) = ℓ.ndeg := by
    refine GlobalTheory.LamF.deg_eq_ndeg_of_line K (Fin x.P.g → K) h (F.eigLat act t) (Pi.single i 1) ℓ ?_ hℓ.1 ?_ ?_
    · intro h0
      have := congrFun h0 i
      simp at this
    · intro z
      rw [GlobalTheory.LamF.EigLine.mem_eigLat_iff E K A x φ hf oa act S τ lab hact hl hLie i t htv z]
      constructor
      · rintro ⟨hz, r, rfl⟩
        refine ⟨r, ?_, ?_⟩
        · exact (_root_.GlobalTheory.LamF.isVecLine_mem_iff_mem_lieLat K A x φ hf i ℓ hℓ r).2 hz
        · ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
      · rintro ⟨c, hc, rfl⟩
        refine ⟨?_, c, ?_⟩
        · have := (_root_.GlobalTheory.LamF.isVecLine_mem_iff_mem_lieLat K A x φ hf i ℓ hℓ c).1 hc
          convert this using 1
          ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
        · ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
    · exact GlobalTheory.CM.LieMetric.vecLine_norm_sq_eq_form hU hL K A x φ hf h hh i ℓ hℓ
  have hre := congrArg Complex.re hdeg
  rw [Complex.ofReal_re] at hre
  rw [← hline]
  linarith

end GlobalTheory.LamF
end

