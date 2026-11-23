module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsLocalRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicAndBlockOneNondegenerate
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.GmAicDeg1

theorem cast_eq_zero_iff {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) :
    x.cast hn hi = 0 ↔ x = 0 := by
  subst hn; subst hi; exact Iff.rfl

theorem cast_nsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (k : ℕ) (x : Ht q E n i) :
    (k • x).cast hn hi = k • x.cast hn hi := by
  subst hn; subst hi; rfl

theorem inv_sp (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) : Inv q (sp A) := fun U ⟨x⟩ => by
  have h := (hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).map
    (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom
  simpa only [map_natCast] using h

theorem dvd_of_T_eq_pow {T : Type} [CommRing T] [IsDomain T] (q n : ℕ) (w : LaurentPolynomial T)
    (hw : (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial T) = w ^ q) : q ∣ n := by
  obtain ⟨k, f, hf⟩ := LaurentPolynomial.exists_T_pow w
  have h : Polynomial.toLaurent (f ^ q) = Polynomial.toLaurent (Polynomial.X ^ (n + k * q) : Polynomial T) := by
    rw [map_pow, hf, mul_pow, ← hw, Polynomial.toLaurent_X_pow, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring
  have h2 := congrArg Polynomial.natDegree (Polynomial.toLaurent_injective h)
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at h2
  have h3 : q ∣ n + k * q := ⟨f.natDegree, h2.symm⟩
  exact (Nat.dvd_add_left (dvd_mul_left q k)).mp h3

theorem kum_pow (q : ℕ) [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) (m : ℕ) :
    kum q (u ^ m) = m • kum q u := by
  have hadd : ∀ u v : (Γ(X, ⊤))ˣ, IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 :=
    fun u v h => (GlobalTheory.T.chernClass_kummerClass_additive q).2 u v h
  have h1 : kum q (1 : (Γ(X, ⊤))ˣ) = 0 := by
    have h := (hadd 1 1 hX).1
    rw [mul_one] at h
    simpa using h
  induction m with
  | zero => rw [pow_zero, zero_smul, h1]
  | succ m ih => rw [pow_succ, (hadd _ _ hX).1, ih, succ_nsmul]

theorem laurentVar_val (T : Type) [CommRing T] :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial T))).hom.hom ((laurentVar T : Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))) =
      LaurentPolynomial.T 1 := by
  simp [laurentVar, laurentVarUnit]

end GlobalTheory.EtC.GmAicDeg1

namespace GlobalTheory.EtC.GmAicDeg1

theorem eq_zero_of_cup_kum (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (hT : AIC T)
    (hq : IsUnit (q : T)) (b : Ht q (sp T) 0 0)
    (hb : cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 b) (kum q (laurentVar T)) = 0) :
    b = 0 := by
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q T (GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hT) hq 0
  have hrep : ∀ x : Ht q (sp T) 0 0, x = (e x).val • e.symm 1 := fun x => by
    apply e.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply, nsmul_one, ZMod.natCast_zmod_val]
  have hqL : IsUnit (q : LaurentPolynomial T) := by simpa using hq.map (LaurentPolynomial.C : T →+* LaurentPolynomial T)
  have hqΓ := GmPhiNat.isUnit_gamma q T hq
  have hκ : ∀ (m : ℕ) (x : Ht q (sp T) 0 0),
      cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 (m • x)) (kum q (laurentVar T)) =
        m • cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 x) (kum q (laurentVar T)) := by
    intro m x
    rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]
  have hone : pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 (one q (sp T)) =
      one q (sp (LaurentPolynomial T)) := (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.1 _ (inv_sp q T hq)
  have hunit := (GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q (sp (LaurentPolynomial T))).1 (inv_sp q _ hqL) (kum q (laurentVar T))
  have h1 := hκ (e (one q (sp T))).val (e.symm 1)
  rw [← hrep, hone, hunit] at h1
  have h2 := hκ (e b).val (e.symm 1)
  rw [← hrep, hb] at h2
  have h3 : (e b).val • (kum q (laurentVar T)).cast (by ring) (by ring) = (0 : Ht q (sp (LaurentPolynomial T)) (0 + 1) (0 + 1)) := by
    rw [h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_zero]
  rw [← cast_nsmul, cast_eq_zero_iff] at h3
  have h5 : kum q (laurentVar T ^ (e b).val) = 0 := by rw [kum_pow q hqΓ, h3]
  obtain ⟨v, hv⟩ := GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero q (LaurentPolynomial T) hqL _ h5
  have h6 := congrArg (fun u : (Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial T))).hom.hom (u : Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))) hv
  simp only [Units.val_pow_eq_pow_val, map_pow] at h6
  rw [laurentVar_val, LaurentPolynomial.T_pow, mul_one] at h6
  have h7 := dvd_of_T_eq_pow q (e b).val _ h6
  have h8 : (e b).val = 0 := Nat.eq_zero_of_dvd_of_lt h7 (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h8
  exact e.map_eq_zero_iff.1 h8

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  intro q _ T _ _ _ hT hq i
  have hinj : Function.Injective (gmPhi q T i) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at ha
    rw [cast_eq_zero_iff] at ha
    obtain ⟨z, hz⟩ : ∃ z : T, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
      obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
        (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
      exact ⟨a, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]; exact ha⟩
    let ζ : Prim q Γ(Spec (CommRingCat.of T), ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ⟨z, hq, hz⟩
    let τ := Untwist.twistEquiv ζ (inv_sp q T hq) 0 (i - 1) 0
    have hτ : τ a = 0 := by
      apply eq_zero_of_cup_kum q T hT hq
      show cup q (pull _ _ _ 0 ((cup q (rootClass (0 - (i - 1)) ζ) a).cast (zero_add 0) (by ring))) (kum q (laurentVar T)) = 0
      rw [GmPhiNat.pull_cast, Untwist.cup_cast_left, cast_eq_zero_iff, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1,
        (GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q _).2.1, cast_eq_zero_iff, ha, map_zero]
    exact τ.map_eq_zero_iff.1 hτ
  obtain ⟨e0⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q T (GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hT) hq (i - 1)
  obtain ⟨e1⟩ := (GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q T hT hq 1 i).2
  haveI : Finite (Ht q (sp (LaurentPolynomial T)) 1 i) := Finite.of_equiv _ e1.symm.toEquiv
  exact hinj.bijective_of_nat_card_le (by rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv])

end GlobalTheory.EtC.GmAicDeg1

theorem GlobalTheory.EtC.gmPhi_bijective_of_aic : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) :=
  GlobalTheory.EtC.GmAicDeg1.main
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpressionValuesAtDescendedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

theorem unit_of_val {K S : Type} [Field K] [CommRing S] [Nontrivial S] (f : K →+* S) {u v : Sˣ} {c : K}
    (h : u.val = v.val * f c) : ∃ m : Kˣ, (m : K) = c ∧ u = v * Units.map f.toMonoidHom m := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at h
    exact u.ne_zero h
  exact ⟨Units.mk0 c hc, rfl, Units.ext (by rw [h, Units.val_mul]; rfl)⟩

theorem toStk_surj' {K : Type} [Field K] (z : Sp K) : Function.Surjective (toStk z) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp K).presheaf.germ_exist s
  exact ⟨_, (toStk_valF_gs (𝟙 _) U z hU a).trans (gs_eq _ _ _ hU _)⟩

theorem units_identity {U : Type} [CommGroup U] (gO gB gP gC gCn R M2 M3 M4 M5 : U) :
    (gO⁻¹ * gB * M2) ^ 2 * (gP * gC⁻¹ * gB⁻¹ * gO * M3) ^ 2 * (gCn⁻¹ * gC * M4) *
        (gO * gC⁻¹ * gCn⁻¹ * gO * M5)⁻¹ * (R ^ 2)⁻¹ =
      gP ^ 2 * (gO⁻¹ ^ 2 * (R ^ 2)⁻¹) * (M2 ^ 2 * M3 ^ 2 * M4 * M5⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem sq_cancel {S : Type} [CommRing S] (a b c d f : S) (h : a * c = 1) :
    (a * b) ^ 2 * (c ^ 2 * d * f) = b ^ 2 * (d * f) := by
  linear_combination (a * c + 1) * b ^ 2 * d * f * h

theorem c_zero_eta {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) : D.c 0 = η[D.P.A] := by
  rw [GlobalTheory.Poinc.ThetaOne.c_zero]
  rfl

theorem ev_values : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X)
    (τ₀ : GlobalTheory.UChart.Gens D) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)), (∀ c, b c ^ N₁ = 1) →
    ∀ (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))),
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) →
    ∀ (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε)),
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) →
    ∀ (G : X → C → V₁),
      (∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) →
    ∃ Λ : K, ∀ mu c, ∃ r ∈ k₀, ev (G mu c) = Λ * r := by
  intro N₁ hN V₁ _ _ _ hV hunit D X C _ e τ₀ θ hθ b hb t ht χt hχt G hG K _ _ ev k₀ hk₀ W₀ _ ib hB hib
  obtain ⟨B₀, iG, M₀, c₀, τ₁, β, w, hFB⟩ := (fromBase_iff D τ₀ ib).1 hB
  have hM₀ : M₀.IsLB := hFB.2.1
  let z : Sp K := IsLocalRing.closedPoint K
  choose J hJ using fun ψ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J₀ hJ₀ using fun ψ : Sp K ⟶ B₀.left => exists_chart hM₀ (ψ z)
  have gJ : Good D.P.L z J := hJ
  have gJ₀ : Good M₀ z J₀ := hJ₀
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.thetaGenerator_values_scalar_mul_localUnit V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ θ hθ
  set r : Sp K ⟶ Sp V₁ := spMap ev with hr
  set U0 : ((Sp K).presheaf.stalk z)ˣ := (gwx w z J J₀ (r ≫ (D.c 0).left))⁻¹ ^ 2 * (rigV D r z J ^ 2)⁻¹ with hU0
  have hO : r ≫ (η[D.P.A]).left = r ≫ (D.c 0).left := by rw [c_zero_eta]
  have key : ∀ mu c, ∃ q ∈ k₀, toStk z (ev (G mu c)) = toStk z (κ ^ 2 * q) * U0.val := by
    intro mu c
    obtain ⟨hBd, -, hPd, -⟩ := GlobalTheory.T.torsionPoints_projections_defined_over_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib N₁ (by omega)
      (b c) (hb c) (e mu)
    obtain ⟨c1, hc1, e1⟩ := hκ (b c * D.c (e mu)) hPd
    obtain ⟨c2, hc2, e2⟩ := GlobalTheory.T.torsionFrame_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (b c) (hb c) hBd (t c) (ht c)
    obtain ⟨c3, hc3, e3⟩ := GlobalTheory.T.characterValue_mem_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (e mu) (b c) (hb c) hBd (χt mu c) (hχt mu c)
    obtain ⟨c4, hc4, e4⟩ := GlobalTheory.T.symmetryGenerator_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ (e mu)
    obtain ⟨c5, hc5, e5⟩ := GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀
      (e mu) (-e mu)
    have hPP : r ≫ (D.c (e mu) * b c).left = r ≫ (b c * D.c (e mu)).left := by rw [mul_comm]
    have h00 : r ≫ (D.c (e mu + -e mu)).left = r ≫ (D.c 0).left := by rw [add_neg_cancel]
    rw [hO] at e2 e3
    rw [hPP] at e3
    rw [h00] at e5
    obtain ⟨m2, rfl, u2⟩ := unit_of_val (toStk z) e2
    obtain ⟨m3, rfl, u3⟩ := unit_of_val (toStk z) e3
    obtain ⟨m4, rfl, u4⟩ := unit_of_val (toStk z) e4
    obtain ⟨m5, rfl, u5⟩ := unit_of_val (toStk z) e5
    have h1 := hG mu c (Sp K) r z J gJ
    rw [u2, u3, u4, u5, e1, units_identity, ← hU0] at h1
    have hL : gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) = toStk z (ev (G mu c)) := by
      have := GlobalTheory.RatioVal.gs_specMap ev z ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c))
      rw [Iso.inv_hom_id_apply] at this
      exact this
    refine ⟨c1 ^ 2 * ((m2 : K) ^ 2 * (m3 : K) ^ 2 * (m4 : K) * (m5 : K)⁻¹),
      k₀.mul_mem (k₀.pow_mem hc1 2) (k₀.mul_mem (k₀.mul_mem (k₀.mul_mem (k₀.pow_mem hc2 2) (k₀.pow_mem hc3 2)) hc4)
        (k₀.inv_mem hc5)), ?_⟩
    rw [← hL, h1, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
      sq_cancel _ _ _ _ _ (Units.inv_mul _)]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← map_inv, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, Units.val_inv_eq_inv_val, map_mul, map_pow]
    ring
  obtain ⟨lam, hlam⟩ := toStk_surj' z U0.val
  refine ⟨κ ^ 2 * lam, fun mu c => ?_⟩
  obtain ⟨q, hq, eq⟩ := key mu c
  refine ⟨q, hq, (toStk z).injective ?_⟩
  rw [eq, ← hlam, ← map_mul]
  congr 1
  ring

end GlobalTheory.USep.EvG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyFiniteKilling
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.GmKill

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

theorem subsingleton_of_ringEquiv (q : ℕ) (d i : ℤ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Subsingleton (Ht q (sp A) d i)] : Subsingleton (Ht q (sp B) d i) := by
  constructor
  intro x y
  have h : ∀ z : Ht q (sp B) d i,
      pull _ (spMap (e : A →+* B)) _ _ (pull _ (spMap (e.symm : B →+* A)) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  rw [← h x, ← h y, Subsingleton.elim (pull _ (spMap (e.symm : B →+* A)) _ _ x) (pull _ _ _ _ y)]

theorem subsingleton_prod (q : ℕ) (d i : ℤ) (A B : Type) [CommRing A] [CommRing B]
    [Subsingleton (Ht q (sp A) d i)] [Subsingleton (Ht q (sp B) d i)] :
    Subsingleton (Ht q (sp (A × B)) d i) := by
  constructor
  intro x y
  exact (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B d i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem subsingleton_of_subsingleton_ring (q : ℕ) (d i : ℤ) (A : Type) [CommRing A] [Subsingleton A] :
    Subsingleton (Ht q (sp A) d i) := by
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A A d i).2 (a, b)
  have hfs : RingHom.fst A A = RingHom.snd A A := RingHom.ext fun _ => Subsingleton.elim _ _
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2, hfs]

def piFinSuccRingEquiv (n : ℕ) (B : Fin (n + 1) → Type) [∀ j, CommRing (B j)] :
    (∀ j, B j) ≃+* B 0 × ∀ j : Fin n, B j.succ where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem subsingleton_pi (q : ℕ) (d i : ℤ) : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)],
    (∀ j, Subsingleton (Ht q (sp (B j)) d i)) → Subsingleton (Ht q (sp (∀ j, B j)) d i) := by
  intro n
  induction n with
  | zero =>
    intro B _ _
    exact subsingleton_of_subsingleton_ring q d i _
  | succ n ih =>
    intro B _ hB
    have := ih (fun j => B j.succ) (fun j => hB j.succ)
    have := hB 0
    have := subsingleton_prod q d i (B 0) (∀ j : Fin n, B j.succ)
    exact subsingleton_of_ringEquiv q d i (piFinSuccRingEquiv n B).symm

theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x :=
  _root_.GlobalTheory.IntegralPi.main x hx

theorem isLocalRing_closure (A : Type) [CommRing A] [HenselianLocalRing A] (P : Ideal A) [P.IsPrime] :
    IsLocalRing (integralClosure (A ⧸ P) (AlgebraicClosure (FractionRing (A ⧸ P)))) := by
  haveI : IsLocalRing (A ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  haveI : HenselianLocalRing (A ⧸ P) := GlobalTheory.henselianLocalRing_of_finite A (A ⧸ P)
  exact GlobalTheory.EtC.Psi.isLocalRing_integralClosure _ _

theorem main : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ (n i : ℤ), 2 ≤ n → ∀ x : Ht q (sp (LaurentPolynomial A)) n i,
  ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Module.Finite A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
    pull _ (spMap (laurentMap (algebraMap A A'))) _ _ x = 0 := by
  classical
  intro q _ A _ _ hA hq n i hn x
  obtain ⟨hHens, -⟩ := hA
  let ι := {p : Ideal A // p ∈ minimalPrimes A}
  haveI : Finite ι := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  letI : Fintype ι := Fintype.ofFinite ι
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P : Fin (Fintype.card ι) → Ideal A := fun k => (σ k).1
  haveI hP : ∀ k, (P k).IsPrime := fun k => (σ k).2.1.1
  let T : Fin (Fintype.card ι) → Type := fun k =>
    integralClosure (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k)))
  letI : ∀ k, Algebra A (T k) := fun k => ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).toAlgebra
  have hint : ∀ k (s : T k), IsIntegral A s := by
    intro k s
    have h : ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).IsIntegral :=
      RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
        (fun s => Algebra.IsIntegral.isIntegral s)
    exact h s
  haveI : Algebra.IsIntegral A (∀ k, T k) := ⟨fun s => isIntegral_pi s (fun k => hint k (s k))⟩
  have hS : Subsingleton (Ht q (sp (LaurentPolynomial (∀ k, T k))) n i) := by
    have hT : ∀ k, Subsingleton (Ht q (sp (LaurentPolynomial (T k))) n i) := by
      intro k
      haveI := isLocalRing_closure A (P k)
      have hqk : IsUnit (q : T k) := by simpa using hq.map (algebraMap A (T k))
      exact (GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q (T k) (GlobalTheory.aic_integralClosure_algebraicClosure (A ⧸ P k)) hqk n i).1 hn
    haveI := subsingleton_pi q n i _ (fun k => LaurentPolynomial (T k)) hT
    exact subsingleton_of_ringEquiv q n i (RingEquiv.ofBijective _ (GlobalTheory.T.laurent_pi_bijective _ T)).symm
  have hx0 : pull _ (spMap (laurentMap (algebraMap A (∀ k, T k)))) _ _ x = 0 := Subsingleton.elim _ _
  obtain ⟨t, ht⟩ := GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra q A (∀ k, T k) hq n i x hx0
  refine ⟨Algebra.adjoin A (t : Set (∀ k, T k)), inferInstance, inferInstance,
    GlobalTheory.EtC.IntAcyc.finite_finDiag A (∀ k, T k) t, ?_, ht⟩
  intro a ha
  rw [RingHom.mem_ker] at ha
  have ha' : algebraMap A (∀ k, T k) a = 0 := by
    have := congrArg Subtype.val ha
    exact this
  have hmem : ∀ k, a ∈ P k := by
    intro k
    have h1 : algebraMap A (T k) a = 0 := congrFun ha' k
    have h2 : algebraMap (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k))) (Ideal.Quotient.mk (P k) a) = 0 :=
      congrArg Subtype.val h1
    rw [IsScalarTower.algebraMap_eq (A ⧸ P k) (FractionRing (A ⧸ P k)) (AlgebraicClosure (FractionRing (A ⧸ P k))),
      RingHom.comp_apply] at h2
    have h3 := (IsFractionRing.injective (A ⧸ P k) (FractionRing (A ⧸ P k)))
      ((algebraMap (FractionRing (A ⧸ P k)) _).injective (h2.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3
  change a ∈ (⊥ : Ideal A).radical
  rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro p hp
  obtain ⟨k, hk⟩ := σ.surjective ⟨p, hp⟩
  have := hmem k
  simp only [P, hk] at this
  exact this

end GlobalTheory.EtC.GmKill

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerDatumObjectComesFromBaseOfLinearPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem lowBase_of_linearPoints : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (L : LowBase D' c) (θ₀ : L.W →+* V) (e : X ≃ₗ[𝓞 E] L.D.X) (m : ObjMap o' L.o (spMap θ₀)), IsLocalHom θ₀ ∧ θ₀.comp L.b = bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ ≫ L.φB = spMap θ₀ ≫ (L.D.c (e y)).left := by
  intro E _ _ _ H D' l c V _ _ _ bV o' X _ _ _ _ x hadd hlin
  obtain ⟨W, _, _, _, b, o, x₀, θ₀, m, hft, hadd₀, hlin₀, hloc, hcomp, hx, ⟨fR, fE⟩, hdim⟩ :=
    GlobalTheory.T.exists_localRing_linearHomScheme_lowerObject D' c V bV o' X x hadd hlin
  haveI : IsProper o.t.G.hom := o.proper
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim W o.t.G
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_of_proper _ o.t.semi)
  obtain ⟨D, hmod, oa, φB, e, hev, hbi, hgen, hw0, hab, hc⟩ :=
    GlobalTheory.T.exists_generating_degenerationData_principalTriple W o.t o.proper o.ample o.ktriv ⟨g, hg⟩ X x₀ hadd₀ hlin₀
  letI := hmod
  haveI hiso : IsIso φB := hab.1.1.isIso_fst_of_isIso
  refine ⟨⟨W, b, hft, o, D, oa, hev, hbi, hgen, hw0, φB, hab, ?_, ?_, ?_⟩, θ₀, e, m, hloc, hcomp, ?_⟩
  · intro A _ _ f₁ f₂ hf o'' m₁ m₂ z h₁ h₂ hz
    refine fR A f₁ f₂ hf o'' m₁ m₂ (fun y => z (e y)) (fun y => ?_) (fun y => ?_) (fun y => hz (e y))
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₁ (e y)
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₂ (e y)
  · intro k _ f o'' m₁ m₂ z h₁ h₂ hz
    refine fE k f o'' m₁ m₂ (fun y => z (e y)) (fun y => ?_) (fun y => ?_) (fun y => hz (e y))
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₁ (e y)
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₂ (e y)
  · obtain ⟨a, t, h1, h2, h3⟩ := hdim
    exact ⟨a, t, h1, h2, by rw [h3, LinearEquiv.finrank_eq e]⟩
  · intro y
    show (x y).left ≫ m.toSABMap.φ ≫ φB = spMap θ₀ ≫ (D.c (e y)).left
    rw [← hc y, ← Category.assoc, hx y, Category.assoc]

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityOfHodgeDeRhamDualStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareDeRhamDuality_of_hodgeDeRham_dual : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge | exact GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge | (intros; apply GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge <;> assumption)
end

