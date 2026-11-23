module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_isModelAt : Out.SecTwistSt → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ p : HeightOneSpectrum (𝓞 K), ∃ M, IsModelAt A x φ p M := by
  intro hT K _ _ A x φ hx p
  have hg : x.P.g = A.g := ((isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) A x φ).1 hx).1
  have hφ : IsGrpPullback x.P.A A.A (spMap (algebraMap (𝓞 K) K)) φ := hx.1
  let R := (p.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => p.valuation_le_one r
  have hf : spMap (algebraMap R K) ≫ spMap f = spMap (algebraMap (𝓞 K) K) := (Spec.map_comp _ _).symm
  obtain ⟨y, ψ, w₀, hg₀, hψ, hw₀⟩ := KeyPow.exists_keyIn_pullback hT f A (hg ▸ x.g_pos)
  have sq : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap f := by rw [Category.assoc, hf, hφ.1.w]
  obtain ⟨φ', rfl, h₂⟩ : ∃ φ' : x.P.A.left ⟶ y.P.A.left, φ' ≫ ψ = φ ∧
      φ' ≫ y.P.A.hom = x.P.A.hom ≫ spMap (algebraMap R K) := ⟨hψ.1.lift _ _ sq, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap (algebraMap R K)) φ' := hψ.cancel (hφ.congr hf.symm rfl) h₂
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq' : ∀ i, (spMap (Chart.dualMapR (algebraMap R K)) ≫ (y.v i).left) ≫ y.P.A.hom =
      (epsR K).hom ≫ spMap (algebraMap R K) := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR K ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq' i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ' = spMap (Chart.dualMapR (algebraMap R K)) ≫ (y.v i).left :=
    fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange (algebraMap R K) h y.basis hv'
  have e : y.P.g = x.P.g := hg₀.trans hg.symm
  obtain ⟨a, M, -, hM⟩ := KeyPow.exists_scalar_matrix hT x.P x.th x.th x.th_ne x.basis (hb e.symm)
  have hd : Formalism.L2.Pj.dualMap (algebraMap R K) = Chart.dualMapR (algebraMap R K) := by
    ext a <;> simp [Chart.dualMapR, Formalism.L2.Pj.dualMap]
  refine ⟨M, R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsFractionRing (p.valuation K).valuationSubring K), f, y, ψ, e, rfl,
    fun z => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩, ⟨hψ, w₀, (isGen_iff _).2 hw₀⟩,
    (((LieComb.lieComb_algebra K x.P.A _ x.v x.basis.1).2.2.2.2 M _ x.basis hM).1 (hb e.symm)).ne_zero,
    fun k => ⟨_, hM k, ?_⟩⟩
  rw [hd, ← Category.assoc, hv', Category.assoc]

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem exists_polAV_latticeFamily : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) := by
  intro hU hB R _ W hΔ
  obtain ⟨P, v, hg, hv, hbc, hs⟩ := _root_.GlobalTheory.WeierstrassCurve.exists_polAV_invariants R W hΔ
  have hex : ∀ s : R →+* ℂ, ∃ L : PeriodPair, s W.c₄ = 12 * L.g₂ ∧ s W.c₆ = 216 * L.g₃ ∧
      s W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := fun s => by
    obtain ⟨P', φ, h⟩ := exists_isPolFibre hB s P
    obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.2.1.1 v
    obtain ⟨rig, hrig⟩ := P'.rigid
    obtain ⟨u, Hm, χ, -, -, -, hd, -⟩ := hU P' rig hrig
    obtain ⟨w, hw, -⟩ := hd v' (hv'.isTangent h.2.1 (hv.1 0))
    obtain ⟨-, L, -, hL⟩ := hs s P' φ v' u w h hv' hw
    exact ⟨L, hL⟩
  choose Lf hLf using hex
  refine ⟨P, v, Lf, ⟨hg, hv, hbc, fun s P' φ v' u w h hv' hw => ?_⟩, hLf⟩
  obtain ⟨hw0, L, hL, h4, h6, -⟩ := hs s P' φ v' u w h hv' hw
  have e : (Lf s).lattice = L.lattice :=
    lattice_eq_of_g₂_eq_of_g₃_eq
      (mul_left_cancel₀ (by norm_num : (12 : ℂ) ≠ 0) ((hLf s).1.symm.trans h4))
      (mul_left_cancel₀ (by norm_num : (216 : ℂ) ≠ 0) ((hLf s).2.1.symm.trans h6))
  exact ⟨hw0, fun z => e ▸ hL z⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqNsmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.RationalTorsion

theorem section_ext {K k : Type} [Field K] [Field k] (t : Sp k ⟶ Sp K) {G : Over (Sp K)}
    {s s' : 𝟙_ (Over (Sp K)) ⟶ G} (h : toUnit (Over.mk t) ≫ s = toUnit (Over.mk t) ≫ s') : s = s' := by
  have h1 : Surjective t := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have h2 : Flat t := inferInstance
  have h3 : Epi t := Flat.epi_of_flat_of_surjective t
  have h4 : (toUnit (Over.mk t)).left = t := by simp
  have h5 : Epi (toUnit (Over.mk t)).left := by rw [h4]; exact h3
  have h6 : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_add_smul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a c : D.La) :
    I.ev n (a + n • c) = I.ev n a := by
  rw [I.add, (I.ker n hn _).2 ⟨c, rfl⟩, _root_.mul_one]

theorem exists_eq_nsmul (D : Datum H) (l : Level H) {J J' : Ideal (𝓞 E)}
    (hJ : J * J' = Ideal.span {(l.M : 𝓞 E)}) {e : 𝓞 E} (he : e ∈ J) {a : D.La}
    (ha : a ∈ J' • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c, e • a = l.M • c := by
  have h1 : e • a ∈ (J * J') • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he ha
  rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨c, -, hc⟩ := h1
  exact ⟨c, by rw [← hc, Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.CM.RationalTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory

theorem exists_inverse_isogeny_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → Surjective Φ.left → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  intro hU hL K _ σ P P' Φ hg hΦ hs
  obtain ⟨hf, hfl, n, hn, hk⟩ := isogeny_of_surjective_polAV hU hL K σ P P' Φ hg hΦ hs
  have := P.isAb.comm
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 P.A ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 P.A ^ m) (𝟙 P.A) ≫ μ[P.A]))
  have hm := hpow n
  obtain ⟨⟨ψ, hψ, e⟩, hE⟩ := exists_monHom_factor_of_flat_surjective _ P.A P'.A P.A Φ (𝟙 P.A ^ n) hΦ hm hfl hs inferInstance
    (fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hk T x hx])
  refine ⟨n, ψ, hn, hψ, e, ?_⟩
  rw [← cancel_epi Φ, reassoc_of% e, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp,
    Category.comp_id]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem exists_restrict_ringHom {R K V F : Type} [CommRing R] [CommRing K] [CommRing V] [CommRing F]
    (a : R →+* K) (b : V →+* F) (hb : Function.Injective b) (i : K →+* F)
    (h : ∀ r : R, i (a r) ∈ Set.range b) : ∃ ψ : R →+* V, b.comp ψ = i.comp a := by
  choose ψ hψ using h
  refine ⟨⟨⟨⟨ψ, hb ?_⟩, fun x y => hb ?_⟩, hb ?_, fun x y => hb ?_⟩, RingHom.ext fun r => hψ r⟩ <;>
    simp [hψ]

theorem exists_isLieBasis_locMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A → ∃ vV : Fin z.Φ.T.g → (epsR T.V ⟶ M.G.t.G), IsLieBasis vV ∧ ∀ k, ∃ wK : epsR z.K ⟶ z.Φ.T.t.G, IsLieComb (A k) z.Φ.v wK ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ M.n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ wK.left ≫ z.m'.φ := by
  intro E _ _ _ H Dw l Xo c _ z p T iK M hT A hA
  obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hR, ⟨hfib, -⟩, -, hv⟩ := hA
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ⟩ := exists_restrict_ringHom (algebraMap R z.K) (algebraMap T.V T.Fr) hinj iK
    (fun r => (hT _).2 ((hR _).1 ⟨r, rfl⟩))
  have hρψ : M.ρ = ψ.comp ρ := by
    refine RingHom.ext fun x => hinj ?_
    have h₁ := RingHom.congr_fun M.hρ x
    have h₂ := RingHom.congr_fun hψ (ρ x)
    have h₃ := RingHom.congr_fun hρ x
    simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  have hp : IsGrpPullback xR.P.A z.B.t.G (spMap ρ) φR := hfib
  have e : spMap M.ρ = spMap ψ ≫ spMap ρ := by rw [hρψ]; exact spMap_comp ρ ψ
  have hn : IsGrpPullback M.G.t.G z.B.t.G (spMap M.ρ) M.n.φ := M.n.cart
  have w : M.n.φ ≫ z.B.t.G.hom = (M.G.t.G.hom ≫ spMap ψ) ≫ spMap ρ := by rw [hn.1.w, e, Category.assoc]
  have hq : IsGrpPullback M.G.t.G xR.P.A (spMap ψ) (hp.1.lift _ _ w) :=
    IsGrpPullback.cancel hp (hn.congr e (hp.1.lift_fst _ _ w).symm) (hp.1.lift_snd _ _ w)
  have := xR.P.isAb.comm
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ _ _ _ hq xR.P.isAb.smooth _ xR.v xR.basis
  have hb' : ∀ (k : ℕ) (hk : xR.P.g = k), IsLieBasis fun i : Fin k => v' (i.cast hk.symm) := by
    rintro k rfl
    exact hb
  refine ⟨fun k => v' (k.cast hg.symm), hb' _ hg, fun k => ?_⟩
  obtain ⟨wK, hw, hw'⟩ := hv k
  refine ⟨wK, hw, ?_⟩
  have ed : (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (Chart.dualMapR ψ) =
      (Formalism.L2.Pj.dualMap iK).comp (Formalism.L2.Pj.dualMap (algebraMap R z.K)) := by
    refine RingHom.ext fun x => ?_
    have h₁ := RingHom.congr_fun hψ x.fst
    have h₂ := RingHom.congr_fun hψ x.snd
    simp only [RingHom.comp_apply] at h₁ h₂
    refine TrivSqZeroExt.ext ?_ ?_
    · simpa [Formalism.L2.Pj.dualMap, Chart.dualMapR] using h₁
    · simp only [Formalism.L2.Pj.dualMap, Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact h₂
  have es : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (Chart.dualMapR ψ) =
      spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap R z.K)) := by
    rw [← spMap_comp, ← spMap_comp, ed]
  have e₁ : (v' (k.cast hg.symm)).left ≫ M.n.φ =
      spMap (Chart.dualMapR ψ) ≫ (xR.v (k.cast hg.symm)).left ≫ φR := by
    rw [← Category.assoc, ← hv', Category.assoc, hp.1.lift_fst]
  exact (congrArg (_ ≫ ·) e₁).trans <| (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) es).trans <|
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hw'.symm)

end GlobalTheory.LamT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCmPeriodLattice
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.PointAlg

section Points

variable {S S' X : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem prod_left (h : IsGrpPullback G' G f φ) {t' : X ⟶ S'} {t : X ⟶ S} (e : t' ≫ f = t) {n : ℕ}
    (x' : Fin n → (Over.mk t' ⟶ G')) (x : Fin n → (Over.mk t ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = (x i).left) :
    (List.ofFn x').prod.left ≫ φ = (List.ofFn x).prod.left := by
  subst e
  have h1 := map_list_prod (pushHom h (Over.mk t')) (List.ofFn x')
  rw [List.map_ofFn] at h1
  have h2 : (pushHom h (Over.mk t')) ∘ x' = x := funext fun i => Over.OverMorphism.ext (hx i)
  rw [h2] at h1
  exact congrArg (fun z => z.left) h1


omit [GrpObj G] [GrpObj G'] in
theorem exists_lift_pt (h : IsPullback φ G'.hom G.hom f) {t' : X ⟶ S'} (x : X ⟶ G.left) (e : x ≫ G.hom = t' ≫ f) :
    ∃ x' : Over.mk t' ⟶ G', x'.left ≫ φ = x :=
  ⟨Over.homMk (h.lift x t' e) (h.lift_snd _ _ _), h.lift_fst _ _ _⟩


omit [GrpObj G] [GrpObj G'] in
theorem pt_ext (h : IsPullback φ G'.hom G.hom f) {T : Over S'} {x y : T ⟶ G'} (e : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

theorem exists_lift_hom {H : Over S} {H' : Over S'} [GrpObj H] [GrpObj H'] {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G f φ) (hH : IsGrpPullback H' H f ψ) (w : G ⟶ H) [IsMonHom w] :
    ∃ w' : G' ⟶ H', IsMonHom w' ∧ w'.left ≫ ψ = φ ≫ w.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hG (isGrpPullback_pullback G f)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H f) hH
  refine ⟨a.hom ≫ (Over.pullback f).map w ≫ b.hom, inferInstance, ?_⟩
  have e : ((Over.pullback f).map w).left ≫ pullback.fst H.hom f = pullback.fst G.hom f ≫ w.left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', e, ← Category.assoc, ha']

theorem onto_lift {B : Over S} {B' : Over S'} {β : B'.left ⟶ B.left} (hB : IsPullback β B'.hom B.hom f)
    (hG : IsGrpPullback G' G f φ) {n : ℕ} (w : Fin n → (B ⟶ G)) (w' : Fin n → (B' ⟶ G'))
    (hw : ∀ i, (w' i).left ≫ φ = β ≫ (w i).left) {t' : X ⟶ S'} {t : X ⟶ S} (e : t' ≫ f = t)
    (h : ∀ y : Over.mk t ⟶ G, ∃ x : Fin n → (Over.mk t ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod)
    (y : Over.mk t' ⟶ G') : ∃ x : Fin n → (Over.mk t' ⟶ B'), y = (List.ofFn fun i => x i ≫ w' i).prod := by
  subst e
  obtain ⟨x, hx⟩ := h (pushPt hG.1.w y)
  choose x' hx' using fun i => exists_lift_pt hB (t' := t') (x i).left (Over.w (x i))
  refine ⟨x', pt_ext hG.1 ?_⟩
  rw [prod_left hG rfl _ (fun i => x i ≫ w i) fun i => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hw, ← Category.assoc, hx'], ← hx]
  rfl

end Points

theorem isAbelianScheme_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    ∀ n : ℕ, IsAbelianScheme (Out.powObj G n)
  | 0 => by
    have := hG.comm
    have : IsIso (Out.powObj G 0).hom := inferInstanceAs (IsIso (𝟙 S))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstanceAs (GeometricallyConnected (𝟙 S))⟩
  | n + 1 => AbelianSchemeGerms.isAbelianScheme_powObj G hG n

theorem onto_of_onto {R : Type} [CommRing R] [IsDomain R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {n : ℕ}
    (w : Fin n → (B ⟶ A))
    (h : ∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Fin n → (Over.mk (spMap σ) ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod)
    (t : Sp ℂ ⟶ Sp R) (y : Over.mk t ⟶ A) :
    ∃ x : Fin n → (Over.mk t ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod := by
  have := hA.comm
  have key : ∀ {T : Over (Sp R)} (x : T ⟶ Out.powObj B n),
      x ≫ (List.ofFn fun i => Out.powPr B i ≫ w i).prod = (List.ofFn fun i => (x ≫ Out.powPr B i) ≫ w i).prod := by
    intro T x
    have h1 := map_list_prod (preHom (G := A) x) (List.ofFn fun i => Out.powPr B i ≫ w i)
    rw [List.map_ofFn] at h1
    refine h1.trans ?_
    congr 2
  obtain ⟨x, hx⟩ := (OntoSurj.surjective_of_onto_complex_points R σ hσ A (Out.powObj B n)
    (List.ofFn fun i => Out.powPr B i ≫ w i).prod hA (isAbelianScheme_pow B hB n) fun y => by
      obtain ⟨x, hx⟩ := h y
      refine ⟨(Out.powIsLimit B n).lift (Fan.mk _ x), ?_⟩
      rw [key, hx]
      congr 2
      funext i
      exact congrArg (· ≫ w i) ((Out.powIsLimit B n).fac (Fan.mk _ x) ⟨i⟩).symm).2 ℂ t y
  exact ⟨fun i => x ≫ Out.powPr B i, by rw [hx, key]⟩

theorem map_sum_eq_prod {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    {n : ℕ} (z : Fin n → V) : e (∑ i, z i) = (List.ofFn fun i => e (z i)).prod := by
  induction n with
  | zero =>
    have := he 0 0
    rw [add_zero] at this
    simpa using this.symm
  | succ n ih => rw [Fin.sum_univ_succ, he, ih, List.ofFn_succ, List.prod_cons]


set_option maxHeartbeats 1000000 in
theorem exists_numberField_point_of_cmLat : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ), Nonempty (CMLat hP p q) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe := by
  intro hC hPt hT hL E _ _ _ H D l Xo g ty FU i Pe hP p q ⟨Z⟩
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, hv, -, hcm, -⟩ := hC H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  have := PureType.finiteDimensional_base l
  let k : IntermediateField ℚ ℂ := M ⊔ KA l
  have hk : KA l ≤ k := le_sup_right
  have hfin : FiniteDimensional ℚ k := inferInstance
  let f : 𝓞 M →+* k := (IntermediateField.inclusion (le_sup_left : M ≤ k)).toRingHom.comp (algebraMap (𝓞 M) M)
  obtain ⟨P₀, π, hg₀, hπ, hL₀⟩ := PureType.exists_baseChange hL.polBaseChange (spMap f) P
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := PureType.exists_baseChange hL.polBaseChange (spMap (algebraMap k ℂ)) P₀
  obtain ⟨v₀, hv₀, -⟩ := PureType.exists_tangent_over f hπ (hv.1 0)
  obtain ⟨u₀, hu⟩ := PureType.exists_isThetaUnif hT PC
  have hLL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀)
  obtain ⟨c, hc0, hc⟩ := hcm PC (ψ ≫ π) ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp_spMap _ _) rfl, hLL.symm⟩ u₀
  rw [hw] at hc
  obtain ⟨R, hR, -, y, t, m, vR, φ, hy, hj, -, -, hφ⟩ := hPt E H D l Xo g ty FU i Pe hP k hk hfin P₀ v₀ (hg₀.trans hg) hv₀
    PC ψ u₀ c (hgC.trans (hg₀.trans hg)) hψ hLC hu hc0 hc (fun _ => ∅) (fun _ => Set.finite_empty) ⊥ Subalgebra.fg_bot
  obtain ⟨ε, a, ha⟩ := exists_pure_vectors_periods_span E H _ g ty Pe hP p q Z
  have hρ : ∀ ρ : R →ₐ[k] ℂ, spMap ρ.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k ℂ) := fun ρ =>
    (spMap_comp_spMap _ _).trans (congrArg _ ρ.comp_algebraMap)
  have hB := isGrpPullback_pullback P₀.A (spMap (algebraMap k R))
  have hA : IsAbelianScheme t.G := by
    have := Xo.univ.proper
    have : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 this
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ t.semi
  have onto := onto_of_onto R.val.toRingHom Subtype.val_injective hA
    (Out.TLinPf.isAb_pullback (spMap (algebraMap k R)) P₀.A P₀.isAb) (fun n => φ (ε n) (a n)) fun y' => by
      obtain ⟨z, hz⟩ := FU.ex_onto i Pe hP (Over.homMk (y'.left ≫ m.φ) (by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w y']
        exact hj))
      obtain ⟨b, rfl⟩ := ha z
      choose x hx using fun n => exists_lift_pt (G := P₀.A) (G' := (Over.pullback (spMap (algebraMap k R))).obj P₀.A) hB.1 (t' := spMap R.val.toRingHom)
        ((u₀.ex fun _ => c * b n).left ≫ ψ) (by
          rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, hρ]
          exact Category.id_comp _)
      refine ⟨x, pt_ext m.cart.1 ?_⟩
      rw [prod_left m.cart hj _ (fun n => FU.ex i Pe (b n • Pe (a n))) fun n =>
        (Category.assoc _ _ _).trans ((hφ (ε n)).2 (a n) (b n) (x n).left (hx n) (Over.w (x n))),
        ← map_sum_eq_prod _ (FU.ex_add i Pe hP), hz]
      rfl
  have hs : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨K₁, hk₁, y₁, h₁, h₂, h₃⟩ := exists_numberField_point_of_countable k R hR (KA l)
    (IntermediateField.inclusion hk).toRingHom Xo.X Xo.s y hy (by
      refine (countable_points_of_onto hT hL E H D l Xo g ty FU PC).mono ?_
      rintro _ ⟨ρ, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, hy, spMap_comp_spMap]
        exact congrArg spMap (RingHom.ext fun x => ρ.commutes _)
      obtain ⟨t', ⟨m'⟩⟩ : ∃ t' : SAB H (Sp ℂ), Nonempty (SABMap t' Xo.univ.t (spMap ρ.toRingHom ≫ y)) := by
        obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull (spMap ρ.toRingHom ≫ y) Xo.univ.t
        exact ⟨_, ⟨m'⟩⟩
      let κ := m.cart.1.lift m'.φ (t'.G.hom ≫ spMap ρ.toRingHom) (by rw [m'.cart.1.w, Category.assoc])
      have hγ : IsGrpPullback t'.G t.G (spMap ρ.toRingHom) κ :=
        m.cart.cancel (m'.cart.congr rfl (m.cart.1.lift_fst _ _ _).symm) (m.cart.1.lift_snd _ _ _)
      let β := hB.1.lift ψ (PC.A.hom ≫ spMap ρ.toRingHom) (by rw [hψ.1.w, Category.assoc, hρ])
      have hβ : IsGrpPullback PC.A _ (spMap ρ.toRingHom) β :=
        hB.cancel (hψ.congr (hρ ρ).symm (hB.1.lift_fst _ _ _).symm) (hB.1.lift_snd _ _ _)
      choose w' hw₁ hw₂ using fun n => @exists_lift_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hβ hγ (φ (ε n) (a n))
        ((hφ (ε n)).1.1 (a n))
      refine ⟨t', m', _, w', hw₁, fun y' => ?_⟩
      obtain ⟨x, hx⟩ := onto_lift hβ.1 hγ _ w' hw₂ (Category.id_comp _) (onto _) y'
      exact ⟨_, id, x, hx⟩)
  exact ⟨K₁, hk.trans hk₁, y₁, h₁, h₂, h₃.trans hj⟩

end GlobalTheory.PointAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueHomOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem existsUnique_hom_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G G₁ : Over S) (G' G₁' : Over S') [GrpObj G] [GrpObj G'] [GrpObj G₁] [GrpObj G₁'] (φ : G'.left ⟶ G.left) (φ₁ : G₁'.left ⟶ G₁.left), IsGrpPullback G' G f φ → IsGrpPullback G₁' G₁ f φ₁ → ∀ F : G ⟶ G₁, (∃! F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left) ∧ ∀ F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left → IsMonHom F → IsMonHom F' := by
  intro S S' f G G₁ G' G₁' _ _ _ _ φ φ₁ h h₁ F
  refine ⟨⟨Over.homMk (h₁.1.lift (φ ≫ F.left) G'.hom ?_) (h₁.1.lift_snd _ _ _),
    h₁.1.lift_fst _ _ _, fun F' hF' => ?_⟩, fun F' hF' hF => ?_⟩
  · rw [Category.assoc, Over.w F]
    exact h.1.w
  · apply Over.OverMorphism.ext
    apply h₁.1.hom_ext
    · exact hF'.trans (h₁.1.lift_fst _ _ _).symm
    · exact (Over.w F').trans (h₁.1.lift_snd _ _ _).symm
  · have hmul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ F' = (x ≫ F') * (y ≫ F') := by
      intro T x y
      obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
      obtain ⟨Φ₁, hΦ₁⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G₁ G₁' φ₁ h₁ T
      have key : ∀ z : T ⟶ G', Φ₁ (z ≫ F') = Φ z ≫ F := fun z => by
        apply Over.OverMorphism.ext
        rw [hΦ₁, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc, hF']
      apply Φ₁.injective
      rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]
    have hone : (1 : 𝟙_ (Over S') ⟶ G') ≫ F' = 1 := by
      have h1 := hmul (𝟙_ (Over S')) 1 1
      rw [_root_.mul_one] at h1
      exact _root_.left_eq_mul.mp h1
    refine ⟨?_, ?_⟩
    · simpa [Hom.one_def] using hone
    · have h2 := hmul (G' ⊗ G') (fst G' G') (snd G' G')
      simpa [Hom.mul_def] using h2

end GlobalTheory.LamF
end

