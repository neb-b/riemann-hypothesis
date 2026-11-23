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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfValR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPoint
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

theorem exists_sum_smul {F R : Type} [CommRing F] [CommRing R] [Algebra F R] [Algebra.Smooth F R]
    (D : Derivation ℤ R R) (hD : ∀ a, D (algebraMap F R a) = 0) (m : Ideal R) (hm : ∀ r, D r ∈ m) :
    ∃ (n : ℕ) (c : Fin n → R) (δ : Fin n → Derivation ℤ R R), (∀ k, c k ∈ m) ∧
      (∀ k a, δ k (algebraMap F R a) = 0) ∧ D = ∑ k, c k • δ k := by
  let DF : Derivation F R R :=
    { toFun := D
      map_add' := map_add D
      map_smul' := fun a r => by simp [Algebra.smul_def, hD]
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  let L : Ω[R⁄F] →ₗ[R] R := DF.liftKaehlerDifferential
  have hL : ∀ r, L (KaehlerDifferential.D F R r) = D r := fun r => DF.liftKaehlerDifferential_comp_D r
  have hLm : ∀ w, L w ∈ m := by
    intro w
    have hw : w ∈ Submodule.span R (Set.range (KaehlerDifferential.D F R)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    refine (Submodule.span_le (p := Submodule.comap L m)).2 ?_ hw
    rintro _ ⟨r, rfl⟩
    show L _ ∈ m
    rw [hL]; exact hm r
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R Ω[R⁄F]
  refine ⟨n, fun k => L (p (Pi.single k 1)),
    fun k => (((LinearMap.proj k : (Fin n → R) →ₗ[R] R) ∘ₗ i).compDer (KaehlerDifferential.D F R)).restrictScalars ℤ,
    fun k => hLm _, fun k a => by simp, ?_⟩
  ext r
  have e : KaehlerDifferential.D F R r = ∑ k, i (KaehlerDifferential.D F R r) k • p (Pi.single k 1) := by
    have e0 := LinearMap.congr_fun hpi (KaehlerDifferential.D F R r)
    rw [LinearMap.comp_apply, LinearMap.id_apply, pi_eq_sum_univ' (i _)] at e0
    simpa using e0.symm
  have hs : ∀ δ : Fin n → Derivation ℤ R R, (∑ k, δ k) r = ∑ k, δ k r := fun δ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    rfl
  rw [← hL, e, hs]
  simp [mul_comm]

theorem mem_smul_top {F : Type} [CommRing F] {X : Scheme.{0}} (s : X ⟶ Sp F) [Smooth s] (I : X.IdealSheafData)
    (U : X.affineOpens) (D : logDer s I U) (m : Ideal Γ(X, U.1)) (hm : m.IsMaximal) (h : Γ(X, U.1)) (hI : h ∈ I.ideal U)
    (hh : h ∉ m) (hD : ∀ r, D.1 r ∈ m) : D ∈ m • (⊤ : Submodule Γ(X, U.1) (logDer s I U)) := by
  let φ : F →+* Γ(X, U.1) := (s.appLE ⊤ U.1 (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hφ : φ.Smooth := by
    refine RingHom.Smooth.comp ?_ (Smooth.smooth_appLE s (isAffineOpen_top _) U.2 _)
    exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv)
  letI := φ.toAlgebra
  haveI : Algebra.Smooth F Γ(X, U.1) := hφ
  obtain ⟨n, c, δ, hc, hδ, e⟩ := exists_sum_smul (F := F) D.1 D.2.1 m hD
  obtain ⟨y, z, hz, hyz⟩ := hm.exists_inv hh
  let δ' : Fin n → logDer s I U := fun k => ⟨(y * h) • δ k, fun a => by
    have : δ k (constFn s U.1 a) = 0 := hδ k a
    simp [this], fun f _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hI)⟩
  have e' : D = z • D + ∑ k, c k • δ' k := by
    apply Subtype.ext
    have : (∑ k, c k • δ' k : logDer s I U).1 = (y * h) • D.1 := by
      rw [e, Finset.smul_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Submodule.coe_add, this, Submodule.coe_smul, ← add_smul, add_comm, hyz, one_smul]
  rw [e']
  exact add_mem (Submodule.smul_mem_smul hz trivial) (sum_mem fun k _ => Submodule.smul_mem_smul (hc k) trivial)

def dualConst {k R : Type} [Field k] [CommRing R] (ρ : R →+* DualNumber k) : R →+* DualNumber k :=
  (algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)

theorem constPt_spMap {K R : Type} [Field K] [CommRing R] (ψ : R →+* DualNumber K) :
    constPt (spMap ψ) = spMap (dualConst ψ) := by
  rw [constPt, spMap_comp', spMap_comp']
  rfl

theorem chart_comp {F : Type} [CommRing F] {X : Scheme.{0}} (s : X ⟶ Sp F) (U : X.affineOpens) :
    ∃ σ : F →+* Γ(X, U.1), (∀ a, σ a = constFn s U.1 a) ∧ chart U ≫ s = spMap σ := by
  refine ⟨(s.appLE ⊤ U.1 (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom, fun _ => rfl, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (CommRingCat.of F))) U.2 (fun _ _ => trivial)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h.symm

theorem snd_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens)
    {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (D : Γ(Y.X, U.1) → Γ(Y.X, U.1))
    (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hKS : IsKS Y.t (interior Y) U v D Θ) {K : Type} [Field K] (φ : Γ(Y.X, U.1) →+* DualNumber K)
    (hφ : ∀ r, (φ r).snd = (φ (D r)).fst) (hΘ : ∀ a b, (φ (Θ a b)).fst = 0)
    (hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ interior Y) (hc : ∀ a, (φ (constFn Y.s U.1 a)).snd = 0) (r : Γ(Y.X, U.1)) :
    (φ r).snd = 0 := by
  obtain ⟨y', hy'⟩ : ∃ y' : Sp (DualNumber K) ⟶ Xo.XF c, y' ≫ Y.j = spMap φ ≫ chart U :=
    ⟨_, IsOpenImmersion.lift_fac Y.j _ (by rintro _ ⟨p, rfl⟩; exact hV (Set.mem_univ p))⟩
  obtain ⟨σ, hσ, hcs⟩ := chart_comp Y.s U
  letI : Algebra c.F K := ((TrivSqZeroExt.fstHom K K K).toRingHom.comp (φ.comp σ)).toAlgebra
  obtain ⟨A', _, lam, hlam⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Y.oF.t.G y'
  obtain ⟨A₀, _, i, hi⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ' := hlam.comp Y.m0.cart
  have hι' : IsGrpPullback A' Y.t.G (spMap φ ≫ chart U) _ := (hlam.comp Y.m.cart).congr hy' rfl
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  obtain ⟨ρ, hρ, -, hiρ⟩ := exists_isConstK Y.t (interior Y) U v D Θ hv hKS φ hφ hΘ hV A₀ A' _ i hA' hι' hi
  have e₁ := eq_constPt c hi hπ' hiρ hρ
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ := by
    have h0 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h0, Category.comp_id]
  have e₂ : y' ≫ pullback.snd _ _ = spMap (φ.comp σ) := by
    rw [← hjs, reassoc_of% hy', hcs, spMap_comp']
  have e₃ : y' = constPt y' := by
    refine pullback.hom_ext e₁ ?_
    show _ = constPt (y' ≫ pullback.snd _ _)
    rw [e₂, constPt_spMap]
    congr 1
    ext a
    · simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl, hσ, hc]
  have e₄ : spMap φ ≫ chart U = spMap (dualConst φ) ≫ chart U := by
    rw [← constPt_spMap]
    show _ = constPt (spMap φ ≫ chart U)
    rw [← hy']
    exact congrArg (· ≫ Y.j) e₃
  have hU : IsAffineOpen U.1 := U.2
  haveI : Mono (chart U) := inferInstanceAs (Mono hU.fromSpec)
  have e₅ : φ = dualConst φ := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e₄))
  rw [e₅]
  simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl]


set_option maxHeartbeats 1000000 in
theorem mem_smul_top_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ interior Y, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y _ hs _ _ U n v A hv _ _ D Θ m hm ⟨x, hxi, hxU, hx⟩ hKS hΘ
  have hs' := smooth_gen_iff.1 hs
  haveI : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim Y.s
  have hU : IsAffineOpen U.1 := U.2
  obtain ⟨h, hle, hxh⟩ := hU.exists_basicOpen_le (V := interior Y) ⟨x, hxi⟩ hxU
  have hh : h ∉ m := fun hh => hx h hh hxh
  have hI : h ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hn
    refine hp (hle ?_)
    have : p ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen h := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hn
    exact this
  refine mem_smul_top Y.s _ U D m hm h hI hh fun r => ?_
  obtain ⟨K, _, π, hπ⟩ : ∃ (K : Type) (_ : Field K) (π : Γ(Y.X, U.1) →+* K), ∀ r, π r = 0 ↔ r ∈ m :=
    ⟨Γ(Y.X, U.1) ⧸ m, Ideal.Quotient.field m, Ideal.Quotient.mk m, fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
  obtain ⟨φ, hf, hsn⟩ : ∃ φ : Γ(Y.X, U.1) →+* DualNumber K, (∀ r, (φ r).fst = π r) ∧ ∀ r, (φ r).snd = π (D.1 r) :=
    ⟨(dualMap π).comp (epsHom D.1), fun r => by simp [epsHom, dualMap], fun r => by simp [epsHom, dualMap]⟩
  have hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ interior Y := by
    intro p _
    refine hle ?_
    have : spMap φ p ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen h := by
      rw [hU.fromSpec_preimage_basicOpen]
      intro hp
      have hu : IsUnit (φ h) := by
        rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf]
        exact Ne.isUnit fun h0 => hh ((hπ h).1 h0)
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
    exact this
  rw [← hπ, ← hsn]
  exact snd_eq_zero Y U v D.1 Θ hv hKS φ (fun r => (hsn r).trans (hf _).symm)
    (fun a b => (hf _).trans ((hπ _).2 (hΘ a b))) hV (fun a => by rw [hsn, D.2.1 a, map_zero]) r

end GlobalTheory.InteriorKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSZeroDer

theorem isInvDer_of_isInv {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    {v : TanM (𝟙 (Sp K)) A} {u : epsR K ⟶ A} (hu : u.left = (tv v).left) (ht : IsTangent u)
    {dd : Fld A.left} (hd : IsInv A v dd) : GlobalTheory.KS.IsInvDer u dd :=
  _root_.GlobalTheory.InvDerBridge.isInvDer_of_isInv K A v u dd hu ht hd

theorem pbT_id_le {X : Scheme.{0}} {O₀ O : X.Opens} (h : O ≤ O₀) (s : Γ(X, O₀)) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT, rsT, dite_eq_left (show O ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ O₀ from h), dite_eq_left h]
  rfl

theorem constFn_zero_fn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (O : X.Opens) :
    constFn q O 0 = 0 := by
  rw [constFn, map_zero, map_zero]

theorem id_app_apply {X : Scheme.{0}} (O : X.Opens) (s : Γ(X, O)) : ((𝟙 X : X ⟶ X).app O).hom s = s := by
  simp only [Scheme.Hom.id_app]
  rfl

theorem rsT_mul_le {X : Scheme.{0}} {O₀ O : X.Opens} (h : O ≤ O₀) (s t : Γ(X, O₀)) : rsT (s * t) O = rsT s O * rsT t O := by
  rw [rsT, rsT, rsT, dite_eq_left h, dite_eq_left h, dite_eq_left h, map_mul]

theorem dlg_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (L : LB A.left)
    (δ : Fld A.left) (hf : IsField ⊤ δ) (i i' : L.ι) (ψ : Γ(A.left, L.U i ⊓ L.U i'))
    (hψ : (L.g i i').val * ψ = δ (L.U i ⊓ L.U i') (L.g i i').val) (O : A.left.Opens) (hO : O ≤ L.U i ⊓ L.U i') :
    dlg A (𝟙 _) L δ i i' O = rsT ψ O := by
  rw [dlg, pbT_id_le hO, pbT_id_le hO]
  have e2 := congrArg (fun s => rsT s O) hψ
  have e3 : rsT (δ (L.U i ⊓ L.U i') (L.g i i').val) O = δ O (rsT (L.g i i').val O) := by
    rw [rsT, rsT, dite_eq_left hO, dite_eq_left hO]
    exact (hf.2.2 _ O hO le_top _).symm
  rw [rsT_mul_le hO, e3] at e2
  rw [← e2, mul_comm (rsT (L.g i i').val O), _root_.mul_assoc, ← rsT_mul_le hO, Units.mul_inv]
  have e4 : rsT (1 : Γ(A.left, L.U i ⊓ L.U i')) O = 1 := by rw [rsT, dite_eq_left hO, map_one]
  rw [e4, _root_.mul_one]

theorem main : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ M : Matrix (Fin n) (Fin n) K, KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) M → M = 0 := by
  intro K _ _ P₀ n v dd hdd M hM
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  obtain ⟨u, hu, hul⟩ := GlobalTheory.Heat.DlogIndep.exists_isLieBasis v
  have hinv : ∀ a, GlobalTheory.KS.IsInvDer (u a) (dd a) := fun a => isInvDer_of_isInv (hul a) (hu.1 a) (hdd a)
  have hiso := GlobalTheory.SiegLower.lbIso_pull_id P₀.isLB
  obtain ⟨⟨φ, hφ⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hinv _ (𝟙 _) P₀.L P₀.isLB hiso
  obtain ⟨J, W, j, d, hcov, hWj, hl, hdiff⟩ := hM
  have hcv : ∀ z : P₀.A.left, ∃ i, (𝟙 P₀.A.left : P₀.A.left ⟶ P₀.A.left) z ∈ W i := fun z => by
    have h2 : z ∈ ⨆ i, W i := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  have hpb : IsPullback (𝟙 P₀.A.left) P₀.A.hom P₀.A.hom (𝟙 (Sp K)) := IsPullback.of_horiz_isIso ⟨by simp⟩
  refine GlobalTheory.KSUniq.theta_eq_fibre P₀ u hu dd hinv P₀.A.hom (𝟙 _) (𝟙 _) hpb (U := ⊤) (isAffineOpen_top _) P₀.L
    P₀.isLB hiso (fun _ => 0) M 0 W W j j d (fun _ _ _ => 0) (fun _ => le_top) (fun _ => le_top) hWj hWj hcv hcv
    (fun i => (hl i).1) (fun _ => isField_zero _) ?_ ?_ φ hφ ?_ ?_
  · intro i h r
    have e : r = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r) := by
      simp
    have := (hl i).2 (W i) le_rfl ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r)
    show _ = (P₀.A.hom.appLE ⊤ (W i) h).hom 0
    rw [map_zero]
    conv_lhs => rw [e]
    exact this.trans (by simp [constFn])
  · intro k h r
    show (0 : Γ(P₀.A.left, W k)) = (P₀.A.hom.appLE ⊤ (W k) h).hom 0
    rw [map_zero]
  · intro i i' O hO f
    rw [id_app_apply, id_app_apply, hdiff i i' O hO f]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have p : pbT (𝟙 P₀.A.left) (P₀.L.g (j i) (j i')).val
        ((𝟙 P₀.A.left) ⁻¹ᵁ P₀.L.U (j i) ⊓ (𝟙 P₀.A.left) ⁻¹ᵁ P₀.L.U (j i')) = (P₀.L.g (j i) (j i')).val :=
      GlobalTheory.Heat.DlogIndep.pbT_id (X := P₀.A.left) (P₀.L.U (j i) ⊓ P₀.L.U (j i')) _
    have hψ := hφ b (j i) (j i')
    rw [p] at hψ
    rw [dlg_eq P₀.L (dd b) (hdd b).1 (j i) (j i') (φ b (j i) (j i')) hψ O
      (fun z hz => ⟨hWj i (hO hz).1, hWj i' (hO hz).2⟩)]
    rfl
  · intro k k' O hO f
    rw [id_app_apply]
    simp only [Matrix.zero_apply, constFn_zero_fn, zero_mul, Finset.sum_const_zero, sub_self]
    rfl

end GlobalTheory.KSZeroDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilKernel

theorem triv_slice_of_forall_weilIs_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ b : Over.mk x ⟶ A, b ^ n = 1 → Out.WeilIs (G2 A) P (n : ℤ) (lift a 1) (lift 1 b) 1) → (∃ t : (P.pull (lift (snd A (Over.mk x) ≫ a) (fst A (Over.mk x))).left).Gen, t.IsGen) := by
  intro S A _ _ P hA hL h1 h2 k _ _ p n hn a ha hpair
  have hB : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have ht2 : Triv (AbDual.ev P (𝟙 A) (1 : A ⟶ A)) := h2
  obtain ⟨r, hr⟩ : Triv (P.pull (eSec (A ⊗ A))) := by
    have e := (AbDual.triv_ev_iff hL _ _).2 (AbDual.evc_one_right hL ht2 (1 : 𝟙_ (Over S) ⟶ A))
    have e' : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = η[A ⊗ A] := by
      ext <;> simp [Hom.one_def]
    rw [AbDual.ev, e'] at e
    exact e
  obtain ⟨t, ht⟩ := WeilIntegral.triv_theta CubeTop.cubeTheorem hB hL
  obtain ⟨t', ht', hn'⟩ := AbLaw.Cube.exists_normalised hL t ht
  let M : RigLB (A ⊗ A) := ⟨P, r, hL, hr⟩
  have c : CubicalStr (A ⊗ A) M := AbLaw.Cube.cubicalOfNormalised globalFns_holds hB M t' ht' hn'
  have ha' : (lift a (1 : Over.mk p ⟶ A)) ^ n = 1 := WeilIntegral.lift_pow ha (one_pow n)

  have s1 : ∀ b : Over.mk p ⟶ A, b ^ n = 1 → CubWeil c n (lift a 1) (lift 1 b) 1 := fun b hb =>
    (cubWeil_iff_weilIs (c := c) globalFns_holds hB ha' (WeilIntegral.lift_pow (one_pow n) hb) 1).2 (hpair b hb)

  have s2 : ∀ b : Over.mk p ⟶ A, b ^ n = 1 → CubWeil c n (lift b 1) (lift a 1) 1 := by
    intro b hb
    have h := RaynaudAxis.cubWeil_one_of_triv_pull S (A ⊗ A) A (lift (𝟙 A) 1) hA inferInstance M c h2 n
      (Over.mk p) b a hb ha
    simpa using h

  have s3 : ∀ z : Over.mk p ⟶ A ⊗ A, z ^ n = 1 → CubWeil c n (lift a 1) z 1 := by
    intro z hz
    have e : lift (z ≫ fst A A) 1 * lift 1 (z ≫ snd A A) = z := by
      ext <;> simp [MonObj.mul_comp]
    have hz1 : (z ≫ fst A A) ^ n = 1 := by rw [← MonObj.pow_comp, hz]; simp
    have hz2 : (z ≫ snd A A) ^ n = 1 := by rw [← MonObj.pow_comp, hz]; simp
    have h := ((s2 _ hz1).mul_left (s1 _ hz2).symm).symm
    rw [e] at h
    simpa using h

  have ht := OrthKer.mem_kernel_of_cubWeil_orthogonal k S p (A ⊗ A) hB M c n hn (lift a 1) ha' s3
  have hD : (translDiff (A ⊗ A) P (lift a 1)).IsLB := LB.isLB_linComb hL _ _
  have h0 : CechPic.cls _ hD = 0 := (CechPic.cls_eq_zero_iff hD).2 ht

  have e := AbDual.pull_translDiff hL (lift a 1) hD (snd A (Over.mk p)) (lift 1 (fst A (Over.mk p)))
  rw [h0, map_zero] at e
  have k1 : (snd A (Over.mk p) ≫ lift a 1) * lift 1 (fst A (Over.mk p)) =
      lift (snd A (Over.mk p) ≫ a) (fst A (Over.mk p)) := by
    ext <;> simp [MonObj.mul_comp]
  have k2 : CechPic.pull (lift (1 : A ⊗ Over.mk p ⟶ A) (fst A (Over.mk p))).left (CechPic.cls P hL) = 0 := by
    have e1 : AbDual.evc hL (1 : A ⟶ A) (𝟙 A) = 0 := (AbDual.triv_ev_iff hL _ _).1 h1
    have e2 : lift (1 : A ⊗ Over.mk p ⟶ A) (fst A (Over.mk p)) =
        fst A (Over.mk p) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      ext <;> simp
    have e3 : CechPic.pull (lift (1 : A ⟶ A) (𝟙 A)).left (CechPic.cls P hL) = 0 := e1
    rw [e2, Over.comp_left, CechPic.pull_comp, e3, map_zero]
  rw [k1, k2, sub_zero] at e
  exact (AbDual.triv_ev_iff hL _ _).2 e.symm

end GlobalTheory.WeilKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleThickeningSquareTheorem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.TowerStep
variable (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (e : ℕ)

theorem isGrpPullback_thickMap_factor : IsGrpPullback (thickObj R (maximalIdeal R) e B) (thickObj R (maximalIdeal R) (e + 1) B)
    (spMap (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ maximalIdeal R ^ (e + 1 + 1) →+* R ⧸ maximalIdeal R ^ (e + 1))) (thickMap R (maximalIdeal R) e B) :=
  GlobalTheory.WtTower.isGrpPullback_thickMap (maximalIdeal R) B e

theorem thickMap_fst : thickMap R (maximalIdeal R) e B ≫ pullback.fst B.hom (thick R (maximalIdeal R) (e + 1)) =
    pullback.fst B.hom (thick R (maximalIdeal R) e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem isAbelianScheme_thickObj (hB : IsAbelianScheme B) : IsAbelianScheme (thickObj R (maximalIdeal R) (e + 1) B) :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (thick R (maximalIdeal R) (e + 1)))

theorem exists_isSquare_thickMap : ∃ i₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left,
    IsSquare (thickMap R (maximalIdeal R) e B) i₂ :=
  GlobalTheory.ZM.SiegPull.exists_isSquare (G := thickObj R (maximalIdeal R) (e + 1) B) (G' := thickObj R (maximalIdeal R) e B)
    (f := thickTrans R (maximalIdeal R) e) (pullback.lift_snd _ _ _)

theorem ker_factor_sq {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2 = 0 := by
  have hle : RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ≤
      (I ^ (e + 1)).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul, le_bot_iff, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

theorem isSquare_fst_comp {i₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left}
    {b₂' : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left}
    (si : IsSquare (thickMap R (maximalIdeal R) e B) i₂)
    (sb : IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂') :
    IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) (i₂ ≫ b₂') := by
  have h := GlobalTheory.ZM.SiegPull.isSquare_comp si sb
  rwa [thickMap_fst] at h

end GlobalTheory.TowerStep


open GlobalTheory.TowerStep in
theorem GlobalTheory.TowerStep.step : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (P : LB (G2 B).left), P.IsLB → (∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) → ∀ (e : ℕ) (L : LB (thickObj R (maximalIdeal R) e B).left), L.IsLB → (∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)) → ∃ L' : LB (thickObj R (maximalIdeal R) (e + 1) B).left, L'.IsLB ∧ (∀ b₂ : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) (e + 1) B) L') (P.pull b₂)) ∧ LBIso (L'.pull (thickMap R (maximalIdeal R) e B)) L := by
  intro R _ _ B _ _ hB P hP h₁ h₂ e L hL hyp
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R e
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R (e + 1)
  have hπ := Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) :
    maximalIdeal R ^ (e + 1 + 1) ≤ maximalIdeal R ^ (e + 1))
  have gp₁ := isGrpPullback_pullback B (thick R (maximalIdeal R) (e + 1))
  have hab₁ := isAbelianScheme_thickObj R B e hB
  have hgp := isGrpPullback_thickMap_factor R B e
  obtain ⟨b₂', sb⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare gp₁.1.w
  obtain ⟨i₂, si⟩ := exists_isSquare_thickMap R B e
  have s₀ := isSquare_fst_comp R B e si sb
  have hP' : (P.pull b₂').IsLB := pull_isLB hP _
  have hLam : (abelian₂ (thickObj R (maximalIdeal R) e B) L).IsLB := DVR.linComb_isLB _ hL _ _
  have k : LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) ((P.pull b₂').pull i₂) :=
    LBIso.trans hLam (pull_isLB hP _) (pull_isLB hP' _) (hyp _ s₀)
      (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GtBaseChange.lbIso_refl hP') i₂).symm
  obtain ⟨L', hL', hLL⟩ := _root_.GlobalTheory.LBObs.exists_lift_of_lam_iso_pull _ _ _ hπ (ker_factor_sq (maximalIdeal R) e) (thickObj R (maximalIdeal R) (e + 1) B)
    (thickObj R (maximalIdeal R) e B) (thickMap R (maximalIdeal R) e B) i₂ hab₁ hgp si (P.pull b₂') L hP' hL k
  obtain ⟨a₁, a₂⟩ := _root_.GlobalTheory.AxisTriv.axes_pull _ _ B P hP h₁ h₂ (thick R (maximalIdeal R) (e + 1)) (thickObj R (maximalIdeal R) (e + 1) B) _ b₂' gp₁ sb
  have rig := _root_.GlobalTheory.PolRigid.lbIso_lam_of_quotient _ _ _ hπ (thickObj R (maximalIdeal R) (e + 1) B) (thickObj R (maximalIdeal R) e B)
    (thickMap R (maximalIdeal R) e B) i₂ hab₁ hgp si (P.pull b₂') hP' a₁ a₂ L' L hL' hL hLL k
  refine ⟨L', hL', fun b₂ hb => ?_, hLL⟩
  rw [GlobalTheory.ZM.SiegPull.isSquare_unique hb sb rfl]
  exact rig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueRelationSectionsThroughGeneratingIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_relation_sections_through_generating_iso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  first | exact @GlobalTheory.GermVal.valR_linComb_germ | exact GlobalTheory.GermVal.valR_linComb_germ | (intros; apply GlobalTheory.GermVal.valR_linComb_germ <;> assumption)
end

