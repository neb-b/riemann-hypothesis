module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthOfSpanningCombinations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem growth_bound_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g r J _ R x u hspan hb
  choose C k hC using hb
  have hsingle : ∀ m : Fin r, ∃ a : J → ℝ, ∑ i, a i • u i = Pi.single m 1 := by
    intro m
    have hmem : (Pi.single m (1:ℝ) : Fin r → ℝ) ∈ Submodule.span ℝ (Set.range u) := by
      rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  choose a ha using hsingle
  refine ⟨∑ m, ∑ i, |a m i| * max (C i) 0, ∑ i, k i, ?_⟩
  intro s hs
  have h1 : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hpow : ∀ i, (1 + ‖s‖) ^ (k i) ≤ (1 + ‖s‖) ^ (∑ j, k j) := fun i =>
    pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
  have hm : ∀ m, ‖x s m‖ ≤ (∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
    intro m
    have hid : x s m = ∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m' := by
      have e := congrFun (ha m)
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hc : ∀ m', ∑ i, ((a m i : ℂ) * (u i m' : ℂ)) • x s m'
          = (((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℝ) : ℂ) • x s m' := by
        intro m'
        rw [← Finset.sum_smul]
        congr 1
        have h2 := e m'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
        rw [← h2]; push_cast; rfl
      rw [Finset.sum_congr rfl (fun m' _ => hc m')]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [hid]
    calc ‖∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖
        ≤ ∑ i, ‖(a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖ := norm_sum_le _ _
      _ ≤ ∑ i, |a m i| * (max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ C i * (1 + ‖s‖) ^ (k i) := hC i s hs
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (k i) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j) :=
              mul_le_mul_of_nonneg_left (hpow i) (le_max_right _ _)
      _ = _ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have hnn : ∀ m, 0 ≤ ∑ i, |a m i| * max (C i) 0 := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ => hnn m) (by positivity))).2 fun m => ?_
  calc ‖x s m‖ ≤ _ := hm m
    _ ≤ (∑ m, ∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (f := fun m => ∑ i, |a m i| * max (C i) 0)
        (fun j _ => hnn j) (Finset.mem_univ m)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProperOfAbelianFibres
open IsLocalRing

theorem apply_genericPoint_of_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    [Flat f] : f (genericPoint X) = genericPoint Y := by
  obtain ⟨x', hx', hfx'⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  refine (Specializes.antisymm ?_ ?_).eq
  · rw [← hfx']
    exact (genericPoint_specializes x').map f.continuous
  · exact genericPoint_specializes _

theorem isProper_dvr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V]
    [IsDomain V] [IsLocalRing V] (hW : GlobalTheory.LN.CDvr V) (t : SAB H (Sp V)) (hP : GlobalTheory.LN.PolAt t (jK V))
    (hab : abLocus t.G = Set.univ) : IsProper t.G.hom := by
  haveI := hW.1
  haveI := hW.2.2
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have ht : ∀ z, z ∈ abLocus t.G := fun z => hab ▸ Set.mem_univ z
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H V hW t hP (GlobalTheory.GoodTrait.splitOver_of_abLocus t.G t.semi ht)
  have hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick V (maximalIdeal V) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom
  exact (GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hW.2.1 P.D P.A t.G t.semi P.U hs).proper

theorem isProper_of_polAt_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) →
    abLocus t.G = Set.univ → IsProper t.G.hom := by
  intro E _ _ _ H R _ _ _ _ t hP hab
  haveI : IsSemiAbelian t.G := t.semi
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  haveI := t.semi.smooth
  haveI : IsIntegral t.G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian t.G
  refine _root_.GlobalTheory.TraitProper.isProper_of_lift_genericPoint R t.G.left t.G.hom ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* V, spMap φ = y := ⟨(Spec.preimage y).hom, by simp [spMap]⟩

  let p₀ : Sp K := (⊥ : PrimeSpectrum K)
  have h₁ : x p₀ = genericPoint t.G.left := hx ⟨p₀, rfl⟩
  have h₂ : (x ≫ t.G.hom) p₀ = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, h₁, apply_genericPoint_of_flat]
    exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
  rw [hxy] at h₂
  have h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥ := congrArg PrimeSpectrum.asIdeal h₂
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) := by simp [ha]
    rw [h₃] at this
    simpa using this
  haveI : CharZero V := charZero_of_injective_ringHom hinj

  obtain ⟨tV, ⟨m⟩⟩ := exists_sab (spMap φ) t
  have hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hinj
  let ψ : FractionRing R →+* FractionRing V := IsFractionRing.lift hinj'
  have hg : spMap ψ ≫ jK R = jK V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [ψ, IsFractionRing.lift_algebraMap]
  have hPV : GlobalTheory.LN.PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull m hP (jK V) (spMap ψ) hg
  have habV : abLocus tV.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi m.cart.1 z).1 (hab ▸ Set.mem_univ _)
  have hpV : IsProper tV.G.hom := isProper_dvr V ⟨inferInstance, inferInstance, inferInstance⟩ tV hPV habV

  let xV : Sp K ⟶ tV.G.left := m.cart.1.lift x (spMap (algebraMap V K)) hxy
  have hE : ValuativeCriterion.Existence tV.G.hom := by
    have h : UniversallyClosed tV.G.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq tV.G.hom :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by simp [xV, spMap]⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  refine ⟨l.l ≫ m.cm.F, ?_⟩
  rw [← Category.assoc]
  have := l.fac_left
  change spMap (algebraMap V K) ≫ l.l = xV at this
  rw [this]
  exact m.cart.1.lift_fst _ _ _

end GlobalTheory.ProperOfAbelianFibres
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtFam

open GlobalTheory.CechPic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem relAmple_iff_of_cls {S : Scheme.{0}} {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) : Out.RelAmple A M ↔ Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hL, relAmple_iff_isAmpleLB A hM]
  refine forall_congr' fun U => forall_congr' fun hU => ?_
  refine Iff.trans (isAmpleLB_congr (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)
    ((cls_eq_iff (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)).1 ?_)) (isAmpleLB_pow_iff (pull_isLB hL _) hd)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

section OneModel

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

theorem exists_keyAt (M : GChart Y) {R : Type} [CommRing R] {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hd : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, θ, ⟨hw, hr⟩, hθ, hne⟩ :=
    exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  have cast : ∀ (p q : Sp R ⟶ Y.X) (_ : p = q) (n : SABMap t Y.t p), ∃ n' : SABMap t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ _ (FlagMod.spMap_ev z M.hU hz).symm m
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp R) :=
    { A := t.G, g := M.n, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := hA, ktriv := hK
      isAb := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ _) m.base)
  have hrig : ∀ (e : Sp R ⟶ Y.X) (_ : m.cm.e = e) (he : eSec t.G ≫ m.φ = e ≫ eSec Y.t.G),
      rigPullOf m.φ e he Y.t.PP.L Y.t.PP.rig = m.cm.rigPull Y.t.PP.L Y.t.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨⟨P, hn, t.PP.rig, t.PP.rigGen, θ, fun s => ?_, v, hb⟩, rfl, m.φ, he, w, rfl, m.cart, hw, ?_,
    fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hne s
    exact ⟨g, hg, Opens.mem_iSup.2 ⟨i, hi⟩⟩
  · rw [hrig z m.base he]
    exact hr
  · exact (hθ (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))
  · rw [← hm']
    exact hv i

theorem exists_keyAt_of_point (M : GChart Y) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U) {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) {K : Type} [Field K] [CharZero K] (f : R →+* K) {x₀ : KeyIn K}
    (h₀ : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x₀) :
    ∃ x : KeyIn R, x.P.g = x₀.P.g ∧ KeyAt M z hz x := by
  obtain ⟨φ, -, w, hg, hc, hw, -⟩ := h₀
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : x₀.P.A.left ⟶ t.G.left, ψ ≫ m.φ = φ ∧ ψ ≫ t.G.hom = x₀.P.A.hom ≫ spMap f :=
    ⟨m.cart.1.lift φ (x₀.P.A.hom ≫ spMap f) (by rw [hc.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _,
      m.cart.1.lift_snd _ _ _⟩
  subst h₁
  have g : IsGrpPullback x₀.P.A t.G (spMap f) ψ := m.cart.cancel hc h₂
  have e : LBIso x₀.P.L (t.PP.L.pull ψ) :=
    LBIso.trans x₀.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB t.PP.isLB _) ⟨w, hw⟩
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ rfl).symm
  have hG : IsAbelianScheme t.G := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
  have q : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hK⟩ := KTrivGlob.exists_open t.PP.isLB x₀.P.isLB hG hA g e x₀.P.ktriv q
  have : CharZero R := f.charZero
  have : CharZero Γ(Sp R, ⊤) := charZero_of_injective_ringHom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  have kt := KTrivSpread.kTriv_of_open_integral GlobalTheory.firstFiveLaws.1 (Sp R) (fun n hn => Nat.cast_ne_zero.2 hn) U
    ⟨_, hU⟩ t.G t.PP t.cub hG hA hK
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (spMap f q))
  obtain rfl : d = M.n := (H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g.1 hd)
    x₀.P.smoothDim (eSec x₀.P.A q)).trans hg
  obtain ⟨x, hx, h⟩ := exists_keyAt M hz m hp hA kt hd (hg ▸ x₀.g_pos)
  exact ⟨x, hx.trans hg.symm, h⟩

end OneModel

end GlobalTheory.KeyAtFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.logDom_chart_props : ∀ (n a : ℕ), IsOpen (GlobalTheory.ShFam.Hor.logDom n a) ∧ Convex ℝ (GlobalTheory.ShFam.Hor.logDom n a) ∧ (∀ s, AnalyticAt ℂ (GlobalTheory.ShFam.Hor.logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧ Set.MapsTo (GlobalTheory.ShFam.Hor.logExp a) (GlobalTheory.ShFam.Hor.logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) := by
  intro n a
  have hEq : GlobalTheory.ShFam.Hor.logDom n a = ⋂ k : Fin n, (fun s : Fin n → ℂ => s k) ⁻¹' (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
    ext s
    simp only [GlobalTheory.ShFam.Hor.logDom, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    refine forall_congr' fun k => ?_
    split_ifs <;> simp [Metric.mem_ball, dist_zero_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hEq]
    refine isOpen_iInter_of_finite fun k => ?_
    refine IsOpen.preimage (continuous_apply k) ?_
    split_ifs
    · exact isOpen_lt Complex.continuous_re continuous_const
    · exact Metric.isOpen_ball
  · rw [hEq]
    refine convex_iInter fun k => ?_
    have hc : Convex ℝ (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
      split_ifs
      · exact convex_halfSpace_lt (f := Complex.re) Complex.reLm.isLinear 0
      · exact convex_ball 0 1
    exact hc.linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k)
  · intro s
    rw [analyticAt_pi_iff]
    intro k
    show AnalyticAt ℂ (fun s : Fin n → ℂ => if (k : ℕ) < a then Complex.exp (s k) else s k) s
    have hp : AnalyticAt ℂ (fun s : Fin n → ℂ => s k) s :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt s
    split_ifs
    · exact analyticAt_cexp.comp hp
    · exact hp
  · intro s hs
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
    intro k
    have hk := hs k
    simp only [GlobalTheory.ShFam.Hor.logExp]
    split_ifs at hk ⊢ with h
    · rw [Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hk
    · exact hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatLinearIndependentCoordsOfRealIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rowsInd_rat_of_real : ∀ (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ), LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) := by
  intro g r r₀ lam u A hu hA
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro c hc i
  have hc' : ∀ m, ∑ i, (c i : ℝ) * (A i m : ℝ) = 0 := by
    intro m
    have h1 := congrFun hc m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
    push_cast at h2
    exact h2
  have hsum : ∑ i, (c i : ℝ) • u i = 0 := by
    have e : ∀ i, (c i : ℝ) • u i = ∑ m, ((c i : ℝ) * (A i m : ℝ)) • lam m := by
      intro i
      rw [hA i, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hc', zero_smul, Finset.sum_const_zero]
  have h3 := hu (fun i => (c i : ℝ)) hsum i
  exact_mod_cast h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.riemann_relations_period_matrix : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin d → Fin g → ℂ) (τ : Fin d → Fin d → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) ∧ ∀ i j, τ i j - τ j i = ((hermForm Hm (F i) (F j)).im : ℂ) := by
  intro g d Hm E F τ hH hpos hF hA hFE
  have hexp : ∀ z w : Fin g → ℂ, hermForm Hm z w = ∑ x, ∑ y, z x * Hm x y * star (w y) := by
    intro z w; unfold hermForm; simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [Pi.star_apply]; ring
  have lin1 : ∀ (c : Fin d → ℂ) (w : Fin g → ℂ),
      hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
    intro c w
    unfold hermForm
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have symm : ∀ z w : Fin g → ℂ, hermForm Hm w z = star (hermForm Hm z w) := by
    intro z w
    simp only [hexp, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show star (Hm x y) = Hm y x from hH.apply y x]; ring
  have lin2 : ∀ (c : Fin d → ℂ) (z : Fin g → ℂ),
      hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
    intro c z
    rw [symm, lin1, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul', ← symm]
  set a : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hA])
  have asymm : aᵀ = a := by
    ext i k; simp only [a, Matrix.transpose_apply, Matrix.of_apply]; rw [symm]; simp
  set Y : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).im with hY
  set X : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).re with hX
  have hYA : Yᵀ * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hF j, lin1] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero] at h
    simpa [Matrix.mul_apply, Matrix.one_apply, Y] using h
  have hAY : a * Y = 1 := by
    have h := congrArg Matrix.transpose hYA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, asymm, Matrix.transpose_one] at h
  have hYs : Yᵀ = Y := by
    calc Yᵀ = Yᵀ * (a * Y) := by rw [hAY, Matrix.mul_one]
    _ = (Yᵀ * a) * Y := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hYA, Matrix.one_mul]
  have e1 : ∀ i m, ∑ p, Y p i * a p m = if i = m then 1 else 0 := fun i m => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hYA i) m
  have e2 : ∀ p j, ∑ m, a p m * Y m j = if p = j then 1 else 0 := fun p j => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hAY p) j
  have ys : ∀ i j, Y i j = Y j i := fun i j => by
    simpa using (congrFun (congrFun hYs j) i)
  refine ⟨fun v hv => ?_, fun i j => ?_⟩
  · have him : (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im = v ⬝ᵥ (Y *ᵥ v) := by
      simp only [Complex.im_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Y, Complex.mul_im]; ring
    rw [him]
    set w := Y *ᵥ v with hw
    have hAw : a *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hAY, Matrix.one_mulVec]
    set Q : Fin g → ℂ := ∑ i, ((w i : ℝ) : ℂ) • E i with hQ
    have hQE : ∀ k, (hermForm Hm Q (E k)).re = v k := by
      intro k
      rw [hQ, lin1, ← hAw]
      simp only [hAr, Complex.re_sum, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Complex.mul_re]
      rw [show a k i = a i k from by simpa using congrFun (congrFun asymm i) k]; ring
    have hQQ : (hermForm Hm Q Q).re = v ⬝ᵥ w := by
      have hl := lin2 (fun i => (w i : ℂ)) Q
      rw [← hQ] at hl
      rw [hl]
      simp only [Complex.re_sum, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hQE k]; simp [Complex.mul_re]; ring
    have hQ0 : Q ≠ 0 := by
      intro h; apply hv; funext k; rw [← hQE k, h]; simp [hermForm]
    rw [← hQQ]; exact hpos Q hQ0
  · have key : (hermForm Hm (F i) (F j)).im = X i j - X j i := by
      rw [hF i, lin1]
      simp only [hF j, lin2, hAr, Complex.im_sum, Finset.mul_sum]
      have h1 : ∀ p m, ((τ p i) * (star (τ m j) * (a p m : ℂ))).im
          = Y p i * a p m * X m j - X p i * (a p m * Y m j) := fun p m => by
        simp [Y, X, Complex.mul_im, Complex.mul_re]; ring
      simp only [h1, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, e1, e2]
      simp [X]
    apply Complex.ext
    · simp [key, X]
    · simp [Y] at ys; simp [ys j i]
end

