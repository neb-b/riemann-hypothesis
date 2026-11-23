module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedLatticeDataClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem cpl_isIntegrallyClosed : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsIntegrallyClosed (M.Z.presheaf.stalk x) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsIntegrallyClosed R := by
  intro o' Ω _ _ _ hA M x hic R _ _ _ j hC
  obtain ⟨e, -⟩ := hC
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI := hic
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  exact IsIntegrallyClosed.of_equiv e

theorem exists_cong_of_cast {N n : ℕ} (v w : Fin n → ℤ) (h : ∀ i, ((v i : ℤ) : ZMod N) = ((w i : ℤ) : ZMod N)) :
    ∃ k : Fin n → ℤ, v = w + N • k := by
  have : ∀ i, ∃ k : ℤ, v i = w i + N * k := fun i => by
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (w i) (v i) N).1 (h i).symm
    exact ⟨k, by linarith⟩
  choose k hk using this
  exact ⟨k, funext fun i => by simp [hk i, nsmul_eq_mul]⟩

theorem be_le_of_dvd {R V' X : Type} [CommRing R] [CommRing V'] [IsDomain V'] [AddCommGroup X] (g' : R →+* V') {w : V'}
    (hw : Irreducible w) (be : LinearMap.BilinForm ℤ X) {a b : X} {r s : R}
    (ha : 0 ≤ be a a ∧ Associated (g' r ^ 2) (w ^ (be a a).toNat))
    (hb : 0 ≤ be b b ∧ Associated (g' s ^ 2) (w ^ (be b b).toNat)) (hrs : r ∣ s) : be a a ≤ be b b := by
  have h0 : g' r ^ 2 ∣ g' s ^ 2 := pow_dvd_pow_of_dvd (map_dvd g' hrs) 2
  have h1 : w ^ (be a a).toNat ∣ w ^ (be b b).toNat :=
    (ha.2.dvd_iff_dvd_left).1 ((hb.2.dvd_iff_dvd_right).1 h0)
  have h2 := (pow_dvd_pow_iff hw.ne_zero hw.not_isUnit).1 h1
  have := Int.toNat_of_nonneg ha.1
  have := Int.toNat_of_nonneg hb.1
  omega

theorem exists_lattice_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X) (_ : Module.Projective (𝓞 E) X) (n : ℕ) (eb : X ≃ₗ[ℤ] (Fin n → ℤ)) (b₀ : LinearMap.BilinForm ℤ X) (μ : (Fin n → ZMod X₁.S.N) → X) (e : (Fin n → ZMod X₁.S.N) → X₁.Ω₁), Module.finrank (𝓞 E) X ≤ min Dw.p Dw.q ∧ b₀ ∈ balForms H.bar X ∧ (∀ y, y ≠ 0 → 0 < b₀ y y) ∧ (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod X₁.S.N) = cl i) ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) ∧ (∀ cl, e cl ≠ 0 ∧ ∃ (T₀ : AddSubgroup X₁.S.Gam) (c' : T₀ →+ ZMod X₁.S.N) (κ : X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) (x₀ : X₁.S.Gam), X₁.S.IsoFree T₀ ∧ e cl = X₁.S.FF T₀ c' κ / X₁.S.th x₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : X →ₗ[𝓞 E] T.P.D.toPre.X, Function.Surjective π ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → T.be (π (μ cl)) (π (μ cl)) ≤ T.be (π α) (π α)) ∧ ∀ cl, UOrdEq M T ξ (e cl ^ (2 * X₁.S.N)) (T.be (π (μ cl)) (π (μ cl))).toNat := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm hEE x hx
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hpb, hL, hPsi⟩ :=
    GlobalTheory.Poinc.CompletedStalk.exists_completion_unif X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big M U₀ EE out hAdm hEE x hx
  obtain ⟨f, hfm, hfT⟩ := _root_.GlobalTheory.UPoinc.oAct_along_traits E H Dw l Xo c C X₁ M U₀ EE out hAdm
  have hR := fun a => _root_.GlobalTheory.UPoinc.exists_endChar_pull X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ M U₀ EE out x R j hB G gm hpb D A U (f a) (hfm a)
  choose fR m hfR using hR
  obtain ⟨T₀, ξ₀, hT₀, hξ₀⟩ := _root_.GlobalTheory.UTraitCen.exists_uTrait_cen E H Dw l Xo c C X₁ M U₀ EE out hAdm x hx
  have tr := _root_.GlobalTheory.UPoinc.TraitAtClosed.exists_trait_lattice_map E H Dw l Xo c C X₁ M U₀ EE out hAdm f hfm hfT x hx R j hB hC G gm hpb D A U hL hPsi m
    (fun a => ⟨fR a, hfR a⟩)
  obtain ⟨V₀, _, _, _, h₀, g₀, ρ₀, -, hirr₀, hsq₀, hsurj₀, hco₀, hlin₀⟩ :=
    tr T₀ ξ₀ hT₀ (by rw [hξ₀])
  haveI : CharZero R := hB.2
  haveI : IsIntegrallyClosed R := cpl_isIntegrallyClosed X₁.o₁ X₁.Ω₁ M x (hAdm.1.normal x).2 R j hC
  have hco : ∀ y, ∃ r, PsiCoord D.toPre y r ∧ (y ≠ 0 → r ∈ maximalIdeal R) := fun y => by
    obtain ⟨r, h1, -, h3, -⟩ := (GlobalTheory.PsiCoordLocal.main R D inferInstance y).1
    exact ⟨r, h1, h3⟩
  obtain ⟨hdvr₀, -, -⟩ := T₀.cdvr
  haveI := hdvr₀
  haveI : IsLocalHom g₀ := _root_.GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square X₁.o₁ X₁.Ω₁ M x R j hC T₀.V T₀.ϖ V₀ h₀ g₀ ξ₀ hirr₀ hξ₀ hsq₀
  have hinj : Function.Injective ρ₀ := by
    refine (injective_iff_map_eq_zero ρ₀).2 fun y h0 => by_contra fun hy => ?_
    obtain ⟨r, hr, hrm⟩ := hco y
    obtain ⟨-, has⟩ := hco₀ y r hr
    simp only [h0, map_zero, LinearMap.zero_apply, Int.toNat_zero, pow_zero] at has
    have hu : IsUnit (g₀ r) := (isUnit_pow_iff two_ne_zero).1 (has.isUnit_iff.2 isUnit_one)
    exact (mem_maximalIdeal r |>.1 (hrm hy)) ((isUnit_map_iff g₀ r).1 hu)
  let e₀ : D.toPre.X ≃+ T₀.P.D.toPre.X := AddEquiv.ofBijective ρ₀ ⟨hinj, hsurj₀⟩
  have he₀ : ∀ y, e₀ y = ρ₀ y := fun _ => rfl
  obtain ⟨hbal, hposdef, hfin, hproj, n, ⟨eb⟩⟩ := _root_.GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice E H Dw l Xo c T₀
  let ℓ : ZMod X₁.S.N → ℤ := Function.surjInv ZMod.intCast_surjective
  have hℓ : ∀ z, ((ℓ z : ℤ) : ZMod X₁.S.N) = z := Function.surjInv_eq _
  let α₀ : (Fin n → ZMod X₁.S.N) → D.toPre.X := fun cl => e₀.symm (eb.symm (fun i => ℓ (cl i)))
  have hq := fun cl => _root_.GlobalTheory.QUnit.main X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big M U₀ EE out hAdm hEE x hx R j hB hC G gm hpb D A U hL
    hPsi (α₀ cl)
  choose mu hmu1 hmu2 e a he hFF hae hja using hq

  have hcong : ∀ cl (α : T₀.P.D.toPre.X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) →
      CongMod X₁.S.N (e₀.symm α) (α₀ cl) := by
    intro cl α hα
    obtain ⟨k, hk⟩ := exists_cong_of_cast (N := X₁.S.N) (eb α) (fun i => ℓ (cl i)) (fun i => by rw [hα, hℓ])
    refine ⟨e₀.symm (eb.symm k), e₀.injective (eb.injective ?_)⟩
    simp only [α₀, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hk
  refine ⟨T₀.P.D.toPre.X, inferInstance, inferInstance, hfin, hproj, n, eb, T₀.be, fun cl => ρ₀ (mu cl), e,
    UTrait.finrank_le_min E H Dw l Xo c T₀, hbal, hposdef, ?_, ?_, fun cl => ⟨he cl, hFF cl⟩, ?_⟩
  · intro cl i
    obtain ⟨w, hw⟩ := hmu1 cl
    show ((eb (ρ₀ (mu cl)) i : ℤ) : ZMod X₁.S.N) = cl i
    rw [← he₀, hw, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
    simp [hℓ, nsmul_eq_mul]
  · intro cl α hα
    obtain ⟨r, hr, -⟩ := hco (mu cl)
    obtain ⟨s, hs, -⟩ := hco (e₀.symm α)
    have := be_le_of_dvd g₀ hirr₀ T₀.be (hco₀ _ r hr) (hco₀ _ s hs) (hmu2 cl _ (hcong cl α hα) r s hr hs)
    rwa [← he₀ (e₀.symm α), AddEquiv.apply_symm_apply] at this
  · intro T ξ hT hsp
    obtain ⟨V', _, _, _, h, g', ρT, hh, hirr, hsq, hsurjT, hcoT, hlinT⟩ := tr T ξ hT hsp
    have hsm : ∀ (c' : 𝓞 E) (z : T₀.P.D.toPre.X), ρT (e₀.symm (c' • z)) = c' • ρT (e₀.symm z) := by
      intro c' z
      obtain ⟨a', rfl⟩ := H.bar.surjective c'
      have hz : H.bar a' • z = e₀ (m a' (e₀.symm z)) := by
        rw [he₀, hlin₀, ← he₀, AddEquiv.apply_symm_apply]
      rw [hz, AddEquiv.symm_apply_apply, hlinT]
    let π : T₀.P.D.toPre.X →ₗ[𝓞 E] T.P.D.toPre.X :=
      { toFun := fun z => ρT (e₀.symm z)
        map_add' := fun y z => by simp only [map_add (f := _)]
        map_smul' := fun c' z => hsm c' z }
    have hπ : ∀ y, π (ρ₀ y) = ρT y := fun y => by
      show ρT (e₀.symm (ρ₀ y)) = ρT y
      rw [← he₀, AddEquiv.symm_apply_apply]
    refine ⟨π, fun z => ?_, ?_, ?_⟩
    · obtain ⟨y, rfl⟩ := hsurjT z
      exact ⟨ρ₀ y, hπ y⟩
    · intro cl α hα
      obtain ⟨r, hr, -⟩ := hco (mu cl)
      obtain ⟨s, hs, -⟩ := hco (e₀.symm α)
      have := be_le_of_dvd g' hirr T.be (hcoT _ r hr) (hcoT _ s hs) (hmu2 cl _ (hcong cl α hα) r s hr hs)
      rwa [hπ, show π α = ρT (e₀.symm α) from rfl]
    · intro cl
      obtain ⟨r, hr, -⟩ := hco (mu cl)
      obtain ⟨-, has⟩ := hcoT (mu cl) r hr
      rw [hπ]
      have hord := _root_.GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated E H Dw l Xo c X₁.o₁ X₁.Ω₁ M x T ξ hsp R j V' h g' hh hirr hsq (a cl ^ 2) _
        (by rw [map_pow, map_pow]; exact (((hja cl r hr).map g').pow_pow (n := 2)).trans has)
      rwa [map_pow, hae cl, ← pow_mul, mul_comm] at hord

end GlobalTheory.UPoinc.ClosedPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompletionUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GPeriods

theorem exists_completion_unif {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)
    (hO : S.Over₀ M U₀) (x : M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R)
      (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R))
      (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsSemiAbelian G ∧
      IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧
      ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _, IsSemiAbelian.pullback ξ FinalForm.G FinalForm.semi,
    isGrpPullback_pullback _ _, hL, hP⟩

end GlobalTheory.UPoinc.GPeriods

theorem GlobalTheory.UPoinc.GPeriods.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = T.be (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hpt x
  obtain ⟨f, hf, hab, hβ⟩ := _root_.GlobalTheory.UPoinc.oAct_along_traits_of_over E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hS, hG, hL, hP⟩ :=
    GlobalTheory.UPoinc.GPeriods.exists_completion_unif out hO x
  have hm : ∀ a : 𝓞 E, ∃ m : D.toPre.X →+ D.toPre.X, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧
      EndChar U fR m := by
    intro a
    haveI := hf a
    obtain ⟨fR, hfR, e⟩ := GlobalTheory.PullAction.exists_lift_end hG (f a)
    obtain ⟨m, hm⟩ := GlobalTheory.Poinc.Eq8.endChar_exists_of_isMonHom R hB G hS D A U fR hfR
    exact ⟨m, fR, hfR, e, hm⟩
  choose m hm using hm
  have key := fun (T : UTrait Xo c) (ψ : R →+* T.V) (hψ : IsLocalHom ψ) hc =>
    _root_.GlobalTheory.UPoinc.TraitCompare.exists_trait_lattice_equiv E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt f hf hab hβ x R j hB hC G gm hS hG D A U hL hP m hm T ψ hψ hc
  haveI : CharZero R := hB.2
  have hco : ∀ y : D.toPre.X, ∃ s, PsiCoord D.toPre y s := fun y =>
    ((GlobalTheory.PsiCoordLocal.main R D hB.1.2.2.1 y).1).imp fun _ h => h.1
  choose s hs using hco
  by_cases hex : ∃ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ ∧
      jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i
  · obtain ⟨T₀, ψ₀, hψ₀, hc₀⟩ := hex
    obtain ⟨ρ₀, -, hρ₀⟩ := key T₀ ψ₀ hψ₀ hc₀
    refine ⟨R, inferInstance, inferInstance, inferInstance, j, T₀.P.D.toPre.X, inferInstance, inferInstance,
      fun y => s (ρ₀.symm y) ^ 2, hB, hC, ?_⟩
    intro T ψ hψ hc
    obtain ⟨ρT, hord, heq⟩ := key T ψ hψ hc
    have hsymm : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), ρ₀.symm (H.bar a • v) = m a (ρ₀.symm v) := fun a v => by
      apply ρ₀.injective
      rw [AddEquiv.apply_symm_apply, hρ₀, AddEquiv.apply_symm_apply]
    let e₀ : T₀.P.D.toPre.X ≃+ T.P.D.toPre.X := ρ₀.symm.trans ρT
    have hlin : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), e₀ (a • v) = a • e₀ v := fun a v => by
      obtain ⟨b, rfl⟩ := H.bar.surjective a
      show ρT (ρ₀.symm (H.bar b • v)) = H.bar b • ρT (ρ₀.symm v)
      rw [hsymm, heq]
    refine ⟨{ e₀ with map_smul' := hlin }, fun y => ?_⟩
    obtain ⟨h0, hA⟩ := hord (ρ₀.symm y) (s (ρ₀.symm y)) (hs _)
    refine ⟨(T.be (ρT (ρ₀.symm y)) (ρT (ρ₀.symm y))).toNat, Int.toNat_of_nonneg h0, ?_⟩
    rw [map_pow]
    exact hA
  · refine ⟨R, inferInstance, inferInstance, inferInstance, j, PUnit, inferInstance, inferInstance, fun _ => 0, hB, hC,
      fun T ψ hψ hc => (hex ⟨T, ψ, hψ, hc⟩).elim⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoverLinkedThetaSystems
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory.UCovSep

namespace GlobalTheory.UCovSep


set_option maxHeartbeats 1000000 in
theorem exists_linked_cov : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Xo.XF c), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (yM : Sp K ⟶ X₁.M.Z), GlobalTheory.GSep.ULink C X₁ act u π ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ (∃ (U : C.Z.Opens) (g' : X₁.M.Z ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = π ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧ yM ≫ π = y' ≫ q ≫ C.i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro E _ _ _ H Dw hpq l Xo c C n hn ho j₀
  classical
  haveI : Finite (genericPoints (Xo.XF c)) := (_root_.GlobalTheory.XScov.genericPoints_XF_finite E H Dw l Xo c).to_subtype
  letI : Fintype (genericPoints (Xo.XF c)) := Fintype.ofFinite _
  choose g₀ hA using fun τ : genericPoints (Xo.XF c) => _root_.GlobalTheory.UCovSep.GenModel.exists_genModel E H Dw hpq l Xo c C τ.1 n hn ho
  choose k j₁ hk _hB hj₁ big using fun τ : genericPoints (Xo.XF c) =>
    GlobalTheory.UPoinc.GSetup.exists_big_level (g₀ τ) n hn.two_le 0
  set J := j₀ + ∑ τ, (k τ + j₁ τ) + 1 with hJ
  have hkJ : ∀ τ, k τ + j₁ τ + j₀ + 1 ≤ J := fun τ => by
    have := Finset.single_le_sum (f := fun τ => k τ + j₁ τ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    omega
  choose o₁ Ω i₁ i₂ i₃ i₄ ze uτ A₁ lev M U g hAg hun hx hUO hpt hMn hMp hgf hrange using fun τ => hA τ (4 * J)
  obtain ⟨Y, q, hqf, hqs, hY⟩ := _root_.GlobalTheory.FinCover.exists_finite_surjective_cover (Xo.XF c) C.Z C.i (genericPoints (Xo.XF c)) (fun τ => (M τ).Z) U g hgf
    (fun τ => by
      rintro _ ⟨x, rfl⟩
      exact hrange τ ⟨C.iF x, rfl⟩)
    (fun x => by
      obtain ⟨τ, hτ, hsp⟩ := GlobalTheory.exists_mem_genericPoints_specializes x
      refine ⟨⟨τ, hτ⟩, (M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩)), ?_⟩
      have h₁ : (g ⟨τ, hτ⟩ ≫ (U ⟨τ, hτ⟩).ι) ((M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩))) = C.i τ := by
        refine (congrArg (fun χ : Sp (Ω ⟨τ, hτ⟩) ⟶ C.Z => χ (closedPoint (Ω ⟨τ, hτ⟩))) (hpt ⟨τ, hτ⟩)).trans ?_
        exact congrArg C.i (hx ⟨τ, hτ⟩ (closedPoint (Ω ⟨τ, hτ⟩)))
      rw [h₁]
      exact hsp.map C.i.continuous)
  refine ⟨J, Y, q, by omega, hqf, hqs, fun K _ y' => ?_⟩
  obtain ⟨t, yM, hyM⟩ := hY K y'
  letI := i₁ t
  letI := i₂ t
  letI := i₃ t
  haveI := i₄ t
  obtain ⟨R, P, act, u, 𝔭, hRfg, hfr, hPg, hS, ⟨levR⟩, hact, hUA, hu, h𝔭, hreg𝔭⟩ :=
    _root_.GlobalTheory.UCovSep.LocalSpread.exists_local_spread E H Dw hpq l Xo c C (o₁ t) (Ω t) (M t) (g t ≫ (U t).ι) (uτ t) (hMn t) (hpt t)
      (A₁ t) (n ^ (4 * J)) (ze t) (by rw [Nat.cast_pow]; exact (hun t).pow _) (hUO t) (lev t) K yM (y' ≫ q)
      (by rw [Category.assoc]; simpa only [Category.assoc] using hyM)
  have e : (n ^ (2 * J - 2 * k t) * (n ^ k t) ^ 2) ^ 2 = n ^ (4 * J) := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  obtain ⟨S, ρ, hR, φ, hreg, -, hN, hr, hgS, hpb, hL, -⟩ := _root_.GlobalTheory.ThetaRealAt.exists_thetaSys_real_at (o₁ t) (Ω t) R hRfg hfr 𝔭 h𝔭 P n (k t)
    (2 * J - 2 * k t) (ze t) hn ho (hk t) (by have := hkJ t; omega) (hun t) hS (e ▸ levR)
  obtain ⟨act', hact', -, hUA'⟩ := _root_.GlobalTheory.UCovSep.uAct_baseChange E H Dw l Xo c (o₁ t) (Ω t) R S.R hR P ρ.P φ hpb hL act u hact hUA
  have hu' : spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u = uτ t := by
    rw [← hu, ← Category.assoc, ← Spec.map_comp]; rfl
  have hgen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) w ∈
      genericPoints (Xo.XF c) := fun w => by rw [hu', hx t w]; exact t.2
  have hptS : (M t).pt ≫ (g t ≫ (U t).ι) =
      spMap (ratHull S.R).val.toRingHom ≫ (spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) ≫ C.i := by
    rw [hpt t, ← hu', Category.assoc]
  have hbig : S.Big := big t _ (by have := hkJ t; omega) (o₁ t) (Ω t) S (hgS.trans (hPg.trans (hAg t))) hN hr
  let X₁ : GlobalTheory.GSep.GSet :=
    { o₁ := o₁ t, Ω₁ := Ω t, S := S, ρ := ρ, big := hbig, M := M t, normal := hMn t, projM := hMp t,
      div := C.thetaInt (o₁ t) (Ω t) S ρ _ hUA'.uOver hgen (M t) (g t ≫ (U t).ι)
        (hMn t) hptS }
  refine ⟨X₁, act', spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u, g t ≫ (U t).ι, yM,
    ⟨hact', hUA', hgen, hptS⟩, ?_, ⟨U t, g t, hgf t, rfl, hrange t⟩, by simpa only [Category.assoc] using hyM, ?_⟩
  · show S.r * S.N = _
    rw [hr, hN, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  · intro a ha
    obtain ⟨a', b', hb', rfl⟩ := hreg a ha
    exact hreg𝔭 a' b' hb'

end GlobalTheory.UCovSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtSqrtUniformiserCompleteDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep


open Polynomial in
theorem exists_finite_ext_sq_eq_uniformiser : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsPrincipalIdealRing V → ∀ ϖ : V, Irreducible ϖ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (t : V'), IsCN V' ∧ IsPrincipalIdealRing V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ t ^ 2 = f ϖ := by
  intro V _ _ _ hV hP ϖ hϖ
  let K₀ := FractionRing V
  let p : K₀[X] := X ^ 2 - C (algebraMap V K₀ ϖ)
  let L := p.SplittingField
  have hdeg : (p.map (algebraMap K₀ L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]
    norm_num
  obtain ⟨s, hs⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero hdeg
  have hs2 : s ^ 2 = algebraMap K₀ L (algebraMap V K₀ ϖ) := by
    simpa [p, sub_eq_zero] using hs
  obtain ⟨V₁, _, _, _, ρ, σ, hCN, hinj, hfin, hloc, hcomp⟩ :=
    GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local V hV L
  obtain ⟨hN₁, hIC₁, _, _⟩ := hCN

  have hy2 : (σ s) ^ 2 = algebraMap V₁ (FractionRing V₁) (ρ ϖ) := by
    rw [← map_pow, hs2, hcomp]
  have hint : IsIntegral V₁ (σ s) := by
    refine ⟨X ^ 2 - C (ρ ϖ), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [eval₂_sub, hy2, Algebra.algebraMap_eq_smul_one]
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have ht2 : t ^ 2 = ρ ϖ := by
    apply IsFractionRing.injective V₁ (FractionRing V₁)
    rw [map_pow, ht, hy2]

  letI : Algebra V V₁ := ρ.toAlgebra
  haveI : Module.Finite V V₁ := hfin
  haveI : Algebra.IsIntegral V V₁ := Algebra.IsIntegral.of_finite V V₁
  have hϖ0 : ρ ϖ ≠ 0 := by
    intro h; apply hϖ.ne_zero; apply hinj; simpa using h
  have hϖnu : ¬ IsUnit (ρ ϖ) := fun h => hϖ.not_isUnit ((isUnit_map_iff ρ ϖ).mp h)
  have hnf : ¬ IsField V₁ := by
    intro hF
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hϖ0
    exact hϖnu (IsUnit.of_mul_eq_one _ hb)
  have hdvr : IsDiscreteValuationRing V₁ := by
    have h03 := (IsDiscreteValuationRing.TFAE V₁ hnf).out 1 4
    refine h03.mpr ⟨hIC₁, ⟨maximalIdeal V₁, ⟨?_, inferInstance⟩, ?_⟩⟩
    · intro h
      apply hϖnu
      by_contra hu
      have : ρ ϖ ∈ maximalIdeal V₁ := hu
      rw [h] at this
      exact hϖ0 ((Submodule.mem_bot _).mp this)
    · rintro P ⟨hP0, hPp⟩
      obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
      have hc : P.comap (algebraMap V V₁) ≠ ⊥ :=
        Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
      haveI : (P.comap (algebraMap V V₁)).IsPrime := Ideal.IsPrime.comap _
      have hm : (P.comap (algebraMap V V₁)).IsMaximal := IsPrime.to_maximal_ideal hc
      have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := V) P hm
      exact IsLocalRing.eq_maximalIdeal hPm
  exact ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, t, ⟨hN₁, hIC₁, by assumption, by assumption⟩,
    inferInstance, hinj, hloc, hfin, ht2⟩

end GlobalTheory.USep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShearStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_extending_isotropic_shear : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ), 0 < N → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' → ∀ t : Z →ₗ[𝓞 E] D.La,
    (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) → (∀ z z' : Z, D.EF (t z) (t z') = 0) →
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧ ∀ z : Z, g z = t z := by
  first | exact @GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | exact GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | (intros; apply GlobalTheory.LowFilt.IsOpp.exists_isometry_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaClassSumTermsRootsOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaClassSum_terms_rootsOfUnity : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ) := by
  first | exact @GlobalTheory.Poinc.GSum.terms_and_sums | exact GlobalTheory.Poinc.GSum.terms_and_sums | (intros; apply GlobalTheory.Poinc.GSum.terms_and_sums <;> assumption)
end

