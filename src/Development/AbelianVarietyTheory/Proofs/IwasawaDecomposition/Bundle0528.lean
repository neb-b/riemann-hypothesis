module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0875
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlane
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeoOfLevels
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie.CuspLev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem heckeIs_of_levels (Z : GlobalTheory.SeriesTie.ExportTie YS v₀) (hev : fw.Evaluates)
    (hLev : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hHW : Rl.toRealDat.models_HW) (hU : Rl.toRealDat.LUnif) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (hRd' : ∀ hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j,
      GlobalTheory.HeckeSup.ReadsCusp T0 Rl.toRealDat κ j (res T0 (sg0 D A3.A)) hV)
    (hS : ∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)))
    (hHT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P) :
    ∃ (c : FractionRing (D.ntw.O i)),
      Z.ρ.e i b c = (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) ^ k ∧ (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
      ‖embC YS iC b (hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV)‖ = 1 ∧
      HeckeIs YS fw iC b j k P ((iC c)⁻¹ * embC YS iC b (hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV)) := by
  obtain ⟨hk1, hkr, hPs, hPS0⟩ := hk

  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun c => congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)
  have hres : res T0 (sg0 D A3.A) = T0.σ₀ := by
    rw [hsg]; exact res_embLL T0 fw.alg_eq fw.laws.pins.2.2.1
  have hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j :=
    fw.laws.spaceW _ (inR j) _ (base_embedding_good T0 Rl.toRealDat fw.alg_eq fw.laws.pins.2.2.1)
  have hRd := hRd' hV
  have hν : Z.ν i j b ≠ 0 := (Z.scalar i j b).ne
  have hinj : Function.Injective (Z.rd i j b) :=
    (GlobalTheory.SeriesTie.realRd_faithful D Γ Pl0 I0 T1 A3 T0.Q.c.F Rl cG S YS v₀ Z.ρ Z.good i j b (Z.ν i j b) hν hU
      hHW (Z.vec j) hK).injective

  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hPS0 (D.ntw.placesOver_subset_exceptional i 0 h)
    · exact hPS0 (D.ntw.placesOver_subset_exceptional i 1 h)
  have hoff : ¬ charAt P ∣ T0.Q.l.M' := GlobalTheory.HeckeSup.not_dvd_level fw.laws (charAt_mem P) hg
  have hso := hS P hPs hPS0
  have hsplit : P.asIdeal ⊔ P.asIdeal.map (T0.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ :=
    GlobalTheory.HeckeSup.split_of_ne hso.1
  have hSO : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.IsSplitOff T0.Q.l P.asIdeal (charAt P) :=
    ⟨P.isMaximal, hsplit, charAt_prime P, charAt_mem P, hoff⟩
  have hHP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P) :=
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsplit, charAt_prime P, charAt_mem P, hoff⟩

  have hn : (κ j).n = D.R.nV := (fw.kap j (D.eTau.symm 1)).2.2
  set cq : T0.Q.c.F := ((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2) with hcq
  set s : T0.Q.c.F := hkScal T0.Q.c cq P.asIdeal k D.R.nV with hs
  have htr : ∀ x : NX.FmK S ((j : ℕ) + 1), ∃ g ∈ T0.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) g := by
    intro x
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hHT GlobalTheory.HeckePointLaw.heckePointLaws fw.laws j hSO hkr cq
      (dom_wtA (κ j)) _ (cuspOf YS fw j x).2
    rw [show hkScal T0.Q.c cq P.asIdeal k (κ j).n = s by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose G hG hGt using htr
  let x' : NX.FmK S ((j : ℕ) + 1) → NX.FmK S ((j : ℕ) + 1) := fun x => (cuspOf YS fw j).symm ⟨G x, hG x⟩
  have hx' : ∀ x, (cuspOf YS fw j (x' x) : T0.R ((j : ℕ) + 1)) = G x := fun x => by
    simp only [x', AddEquiv.apply_symm_apply]

  obtain ⟨α₀, R₀, z₀, d₀⟩ := GlobalTheory.HeckeDatumExists.exists_isHeckeDatum D D.nd D.ntw Z.ρ Z.good i j b k P ⟨hk1, hkr, hPs, hPS0⟩
  obtain ⟨c, hc, N, hN, hcN⟩ := exists_delta_root Z.good i j b z₀
  have hPg : Bridge.SplitOff P (((Z.ρ.B i j b).G.Pg : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main Z.good i _ (fun P' hP' => by
      obtain ⟨k', hk'⟩ := Z.good.Pg i j b P' hP'
      exact D.ntw.placesOver_subset_exceptional i k' hk') P hPs hPS0
  have hdQ : Bridge.SplitOff P (((Z.ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main Z.good i _ (fun P' hP' => by
      rw [Z.good.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (GlobalTheory.SeriesTie.mem_half.1 hP').1) P hPs hPS0

  have hPgS : GlobalTheory.ExportSeries.SplitSet (Z.ρ.B i j b).G.Pg := by
    obtain ⟨Q', hPgQ, -, hQs⟩ := (Z.good.base i j b).places.split
    exact hQs.mono hPgQ
  have hde : ∀ α R z, Z.ρ.IsHeckeDatum i j b k P α R z → (((Z.ρ.B i j b).de.chi z : Circle) : ℂ) = Z.ρ.e i b c :=
    fun α R z d => by
      rw [hc, GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z (Z.pin.delta i j b) (Z.good.base i j b).de.unram
          (Z.good.base i j b).de.split hdQ d.elt d.det,
        GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (Z.pin.delta i j b) (Z.good.base i j b).de.unram
          (Z.good.base i j b).de.split hdQ d₀.elt d₀.det]
  have hchr' : ChrEq (Z.ρ.B i j b).mu0 (Rl.C.mu0 j) := by rw [Z.pin.mu0 i j b]; exact hLev.mu0 j
  have hmu0 : ∀ α R z, Z.ρ.IsHeckeDatum i j b k P α R z →
      (((Z.ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k :=
    fun α R z d => GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z hchr' (Z.good.base i j b).unram hPgS hPg d.elt d.det
  have hrank : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hdiv : k * D.R.nV / 2 = k * (D.R.nV / 2) := Nat.mul_div_assoc _ (even_iff_two_dvd.1 (kapDom D).2)

  have hkey : ∀ (a : NX.KB S i b) (x : NX.FmK S ((j : ℕ) + 1)),
      D.nexp.hkF i _ b k P ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x)) = c⁻¹ • (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x' x) := by
    intro a x
    refine GlobalTheory.SeriesTie.HeckeTie.eq (Z.hecke i j b) hinj ⟨hk1, hkr, hPs, hPS0⟩ d₀ ?_
    intro α R z d
    have hdc := d.reps
    rw [GlobalTheory.SeriesTie.levK_eq_levG_triv Rl Z.pin i j b] at hdc
    have hset : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T0 Rl.toRealDat j P (charAt P) k α R :=
      ⟨hso, charAt_prime P, charAt_mem P, hoff, hkr, d.elt, hdc⟩
    have hread := hRd P (charAt P) k α R ⟨hso, hg, hkr, d.elt, hdc⟩ hset _ (cuspOf YS fw j x).2 _ (hG x) (hGt x)
    simp only [← GlobalTheory.HeckeSup.hkC_eq (T := T0)] at hread
    funext h
    rw [GlobalTheory.SeriesTie.Setup.hecke_apply, map_smulₛₗ]
    simp only [GlobalTheory.SeriesTie.ExportTie.rd, Pi.smul_apply, smul_eq_mul]
    rw [realRd_eq_phiC YS fw Z.good i j b (Z.ν i j b) hV hev, realRd_eq_phiC YS fw Z.good i j b (Z.ν i j b) hV hev]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx', hread, GlobalTheory.ExportSeries.Base.mu, MonoidHom.mul_apply, Circle.coe_mul, hmu0 α R z d, hde α R z d,
      show Formalism.ConjugateSelfDual.normV P = Nat.card (kP P) from rfl, hrank, ← hdiv, map_inv₀, ← Finset.mul_sum]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt]
    ring
  have hsn : ‖embC YS iC b s‖ = 1 := by
    obtain ⟨p', f', hp', hp'P, hq'⟩ := GlobalTheory.HeckeSup.exists_prime_under P
    have hl : p' ≠ D.ntw.l i := by
      rintro rfl
      exact hPS0 (D.ntw.twistExcludedPlaces_contains_residueChar i hp'P)
    have e1 : Ideal.absNorm P.asIdeal = p' ^ f' := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq']
    have e2 : Nat.card (kP P) = p' ^ f' := hq'
    have hp1 : ‖((p' : ℕ) : ℂ_[D.ntw.l i])‖ = 1 := by
      rw [← map_natCast (algebraMap ℚ_[D.ntw.l i] ℂ_[D.ntw.l i]) p', norm_algebraMap', Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes (Fact.out : (D.ntw.l i).Prime) hp').2 (Ne.symm hl)
    rw [hs, hkScal, hcq, e1, e2]
    simp only [map_mul, map_pow, map_inv₀, map_natCast, norm_mul, norm_pow, norm_inv, Nat.cast_pow, hp1, one_pow, inv_one,
      mul_one]
  refine ⟨c, hc.trans (GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (Z.pin.delta i j b) (Z.good.base i j b).de.unram
    (Z.good.base i j b).de.split hdQ d₀.elt d₀.det), ⟨N, hN, hcN⟩, hsn, ?_⟩
  intro z quot hq f
  have hfin : Finite (HkKer P.asIdeal (charAt P) k z.1) :=
    GlobalTheory.HeckePointLaw.heckePointLaws.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hHP _ z.1
  obtain ⟨y, rfl⟩ := (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm.surjective f
  rw [LinearEquiv.apply_symm_apply]
  have key : ∀ y : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      valAt YS fw j z.1 (YS.eF i _ b (Nat.le_add_left _ _) j.2
        (D.nexp.hkF i _ b k P ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y))) =
        (iC c)⁻¹ * embC YS iC b s * ∑ᶠ C, valAt YS fw j (quot C) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have e0 : (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 :=
        map_zero _
      have e1 : ∀ C, valAt YS fw j (quot C) (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 := fun C => map_zero _
      rw [e0, map_zero, map_zero, map_zero, finsum_congr e1, finsum_zero, mul_zero]
    | add y y' hy hy' =>
      have ea : (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (y + y') =
          (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y + (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y' := map_add _ _ _
      have eb : ∀ C, valAt YS fw j (quot C) (y + y') = valAt YS fw j (quot C) y + valAt YS fw j (quot C) y' :=
        fun C => map_add _ _ _
      rw [ea, map_add (f := _), map_add (f := _), map_add (f := _), hy, hy', finsum_congr eb, finsum_add_distrib (Set.toFinite _) (Set.toFinite _),
        mul_add]
    | tmul a x =>
      have ea : (YS.eF i _ b (Nat.le_add_left _ _) j.2) ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x' x)) =
          a ⊗ₜ[S.Ks] x' x := LinearEquiv.apply_symm_apply _ _
      rw [hkey, map_smul, ea]
      refine (valAt_smul YS fw j z.1 c⁻¹ _).trans ?_
      rw [valAt_tmul, hx',
        valC_geoHecke YS iC b j hHP s (cuspOf_mem_sec YS fw j x) (hGt x) z.1 quot hq]
      simp only [valAt_tmul]
      rw [← mul_finsum, map_inv₀]
      ring
  exact key y

theorem heckeGeo_of_levels (Z : GlobalTheory.SeriesTie.ExportTie YS v₀) (hev : fw.Evaluates)
    (hLev : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hHW : Rl.toRealDat.models_HW) (hU : Rl.toRealDat.LUnif) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (hRd : ∀ hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j,
      GlobalTheory.HeckeSup.ReadsCusp T0 Rl.toRealDat κ j (res T0 (sg0 D A3.A)) hV)
    (hS : ∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)))
    (hHT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)
    (hδ : ∀ P, P ∉ D.ntw.S0 i → ∃ s : T0.Q.c.F,
      D.what₂.embLL (algebraMap T0.Q.c.F D.what₂.LL s) = (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)) :
    HeckeGeo YS fw iC b j := by
  intro k P hk
  obtain ⟨c, hc, ⟨N, hN, hcN⟩, hsn, h⟩ := heckeIs_of_levels YS fw iC b j Z hev hLev hHW hU hK hRd hS hHT hk
  obtain ⟨s₁, hs₁⟩ := hδ P hk.2.2.2
  have hs : Z.ρ.e i b (sideK YS i b (s₁ ^ k)) = Z.ρ.e i b c := by
    obtain ⟨a, rfl⟩ := (eKs YS).surjective s₁
    rw [hc, ← hs₁, map_pow, map_pow, sideK_eKs, eKs_LL, ← S.kKs_spec]
    exact congrArg (· ^ k) (Z.good.e_LL0 i b (S.kKs a))
  have hcs : embC YS iC b (s₁ ^ k) = iC c := congrArg iC ((Z.ρ.e i b).injective hs)
  have h1 : ‖iC c‖ ^ N = 1 := by rw [← norm_pow, ← map_pow, hcN, map_one, norm_one]
  have hc1 : ‖iC c‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).1 h1
  refine ⟨(s₁ ^ k)⁻¹ * hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV, ?_, ?_⟩
  · rw [map_mul, map_inv₀, norm_mul, norm_inv, hcs, hc1, hsn, inv_one, one_mul]
  · rw [map_mul, map_inv₀, hcs]
    exact h

end GlobalTheory.GeoTie.CuspLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameOrbitIsotropicVectorShort
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.OrbitShort

theorem quad_bound {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℂ → V → ℝ) (T : ℝ) (M : ℕ) (hM : 0 < M) (b ξ : V)
    (h0 : ∀ w : ℂ, T < w.im → ∀ v, 0 ≤ m w v)
    (hsm : ∀ (w : ℂ) (k : ℕ) (v : V), m w ((k : ℂ) • v) = (k : ℝ) ^ 2 * m w v)
    (hpar : ∀ (w : ℂ) (u v : V), m w (u + v) + m w (u - v) = 2 * m w u + 2 * m w v)
    (hH : ∀ w w' : ℂ, T < w.im → T < w'.im → ∀ v,
      m w' v ≤ (2 + ‖w - w'‖ ^ 2 / ((w.im - T) * (w'.im - T))) * m w v)
    (hξ : ∀ w : ℂ, T < w.im → m (w + M) ξ = m w ξ)
    (hb : ∀ w : ℂ, T < w.im → ∀ k : ℕ, m (w + M) (b + ((k + 1 : ℕ) : ℂ) • ξ) = m w (b + (k : ℂ) • ξ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, T + 1 < w.im → m w ξ * (w.im - T) ≤ A := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hξk : ∀ (k : ℕ) (w : ℂ), T < w.im → m (w + k * M) ξ = m w ξ := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      have e : w + ((k + 1 : ℕ) : ℂ) * M = (w + k * M) + M := by push_cast; ring
      rw [e, hξ _ (by simpa using hw), ih]
  have hbk : ∀ (k : ℕ) (w : ℂ), T < w.im → m (w + k * M) (b + (k : ℂ) • ξ) = m w b := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      have e : w + ((k + 1 : ℕ) : ℂ) * M = (w + k * M) + M := by push_cast; ring
      rw [e, hb _ (by simpa using hw), ih]
  set w0 : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hw0
  have hw0im : w0.im = T + 1 := by simp [hw0]
  have hw0re : w0.re = 0 := by simp [hw0]
  have hm0 : 0 ≤ m w0 b := h0 _ (by rw [hw0im]; linarith) _
  refine ⟨(M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * m w0 b)), by positivity, ?_⟩
  have strip : ∀ w : ℂ, T + 1 < w.im → 0 ≤ w.re → w.re < M → m w ξ * (w.im - T) ≤
      (M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * m w0 b)) := by
    intro w hw hr0 hr1
    have hw' : T < w.im := by linarith
    obtain ⟨y, hy⟩ : ∃ y, y = w.im - T := ⟨_, rfl⟩
    have hy1 : 1 < y := by linarith
    have hy0 : 0 < y := by linarith
    rw [← hy]

    have g1 : m w b ≤ (3 + (M : ℝ) ^ 2) * y * m w0 b := by
      refine (hH w0 w (by rw [hw0im]; linarith) hw' b).trans (mul_le_mul_of_nonneg_right ?_ hm0)
      have e1 : ‖w0 - w‖ ^ 2 = w.re ^ 2 + (y - 1) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hw0im, hw0re, hy]; ring
      rw [e1, hw0im, ← hy, show (T + 1 - T) * y = y by ring]
      have : (w.re ^ 2 + (y - 1) ^ 2) / y ≤ (1 + (M : ℝ) ^ 2) * y := by
        rw [div_le_iff₀ hy0]
        have a1 : w.re ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
        have a2 : (M : ℝ) ^ 2 * 1 ≤ (M : ℝ) ^ 2 * (y * y) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        nlinarith
      nlinarith
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, y ≤ k * M ∧ (k : ℝ) * M ≤ y + M := by
      refine ⟨⌈y / M⌉₊, ?_, ?_⟩
      · rw [← div_le_iff₀ hMr]; exact Nat.le_ceil _
      · have := (Nat.ceil_lt_add_one (a := y / M) (by positivity)).le
        have h2 := mul_le_mul_of_nonneg_right this hMr.le
        rwa [add_mul, div_mul_cancel₀ _ hMr.ne', one_mul] at h2
    have hwk : T < (w + k * M).im := by simpa using hw'
    have hmb : 0 ≤ m w b := h0 _ hw' _
    have g2 : m (w + k * M) b ≤ (2 + (1 + (M : ℝ)) ^ 2) * m w b := by
      refine (hH w (w + k * M) hw' hwk b).trans (mul_le_mul_of_nonneg_right ?_ hmb)
      have e1 : ‖w - (w + k * M)‖ ^ 2 = ((k : ℝ) * M) ^ 2 := by
        rw [show w - (w + k * M) = -(k * M) by ring, norm_neg, norm_mul]; simp
      have e2 : (w + k * M).im = w.im := by simp
      rw [e1, e2, ← hy]
      have : ((k : ℝ) * M) ^ 2 / (y * y) ≤ (1 + (M : ℝ)) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have a1 : (k : ℝ) * M ≤ (1 + M) * y := by nlinarith
        have a2 := pow_le_pow_left₀ (by positivity) a1 2
        nlinarith
      linarith
    have g3 : (k : ℝ) ^ 2 * m w ξ ≤ (6 + 2 * (1 + (M : ℝ)) ^ 2) * m w b := by
      have p := hpar (w + k * M) (b + (k : ℂ) • ξ) b
      rw [show b + (k : ℂ) • ξ - b = (k : ℂ) • ξ by abel, hsm, hξk k w hw', hbk k w hw'] at p
      have := h0 _ hwk (b + (k : ℂ) • ξ + b)
      linarith
    have hmξ : 0 ≤ m w ξ := h0 _ hw' _
    have g4 : y ^ 2 * m w ξ ≤ ((k : ℝ) * M) ^ 2 * m w ξ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy0.le hk1 2) hmξ
    have g5 : (M : ℝ) ^ 2 * ((k : ℝ) ^ 2 * m w ξ) ≤
        (M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * y * m w0 b)) :=
      mul_le_mul_of_nonneg_left (g3.trans (mul_le_mul_of_nonneg_left g1 (by positivity))) (by positivity)
    refine le_of_mul_le_mul_left ?_ hy0
    nlinarith
  intro w hw
  have hper : Function.Periodic (fun s : ℝ => m ((s : ℂ) + (w.im : ℂ) * Complex.I) ξ) (M : ℝ) := by
    intro s
    have e : ((s + (M : ℝ) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = ((s : ℂ) + (w.im : ℂ) * Complex.I) + M := by
      push_cast; ring
    show m _ ξ = m _ ξ
    rw [e, hξ _ (by simp; linarith)]
  obtain ⟨s, hs, hse⟩ := hper.exists_mem_Ico₀ hMr w.re
  simp only [Complex.re_add_im] at hse
  have := strip ((s : ℂ) + (w.im : ℂ) * Complex.I) (by simpa using hw) (by simpa using hs.1) (by simpa using hs.2)
  rw [hse]
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (X : Data E N)


open ReciprocityTheory.ChartRestriction.G.FD in
theorem maj_natCast_smul (x : Frame X.Ψ N) (τ : X.Ψ) (k : ℕ) (v : Fin N → ℂ) :
    X.maj x τ ((k : ℂ) • v) = (k : ℝ) ^ 2 * X.maj x τ v := by
  unfold Data.maj Data.posPart
  have e : ∀ a b c : ℂ, (k : ℂ) * a * b * ((k : ℂ) * c) = (((k : ℝ) ^ 2 : ℝ) : ℂ) * (a * b * c) := by
    intro a b c; push_cast; ring
  have e' : ∀ a : ℂ, (k : ℂ) * ((k : ℂ) * a) = (((k : ℝ) ^ 2 : ℝ) : ℂ) * a := by
    intro a; push_cast; ring
  simp only [hermC_smul_left, hermC_smul_right, map_mul, map_natCast, e, e', ← Finset.mul_sum,
    Complex.re_ofReal_mul]
  ring


open ReciprocityTheory.ChartRestriction.G.FD in
theorem maj_parallelogram (x : Frame X.Ψ N) (τ : X.Ψ) (u v : Fin N → ℂ) :
    X.maj x τ (u + v) + X.maj x τ (u - v) = 2 * X.maj x τ u + 2 * X.maj x τ v := by
  have hs : u - v = u + (-1 : ℂ) • v := by simp [sub_eq_add_neg]
  have hp : X.posPart x τ (u + v) + X.posPart x τ (u - v) = 2 * X.posPart x τ u + 2 * X.posPart x τ v := by
    unfold Data.posPart
    rw [two_mul, two_mul]
    simp only [← Complex.add_re, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hs, hermC_add_left, hermC_smul_left, map_add (f := _), map_mul, map_neg, map_one]
    ring
  have hh : hermC τ.1 X.Gm (u + v) (u + v) + hermC τ.1 X.Gm (u - v) (u - v) =
      hermC τ.1 X.Gm u u + hermC τ.1 X.Gm u u + (hermC τ.1 X.Gm v v + hermC τ.1 X.Gm v v) := by
    simp only [hs, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, map_neg, map_one]
    ring
  have hh' := congrArg Complex.re hh
  simp only [Complex.add_re] at hh'
  unfold Data.maj
  linarith

end GlobalTheory.OrbitShort


open GlobalTheory.OrbitShort in
theorem GlobalTheory.orbit_unipotent_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ((γ : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → γ ≠ 1 → ∃ (ξ : Fin N → E) (c : ℝ), X.IsIso ξ ∧ 0 < c ∧ ∀ w : ℂ, T + 1 < w.im → ∀ τ, c * (w.im - T) ≤ X.tt ξ (x w) τ := by
  intro E _ _ _ N X T M γ x ⟨hM, hγ, hd, hdom, hsh⟩ hsq hne
  have hst := X.Γ_stab γ hγ
  obtain ⟨b, hbΛ, hb⟩ : ∃ b ∈ X.Λ, Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) b ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hne
    have hz : Matrix.toLin' ((γ : Matrix (Fin N) (Fin N) E) - 1) = 0 := by
      refine LinearMap.ext_on X.Λ_span fun v hv => ?_
      rw [Matrix.toLin'_apply, hc v hv]; rfl
    have hz' : (γ : Matrix (Fin N) (Fin N) E) - 1 = 0 := Matrix.toLin'.map_eq_zero_iff.1 hz
    exact Units.ext (sub_eq_zero.1 hz')
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) b := ⟨_, rfl⟩
  rw [← hξ] at hb
  have hγb : Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) b = b + ξ := by
    rw [hξ, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hγξ : Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) ξ = ξ := by
    have : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) ξ = 0 := by
      rw [hξ, Matrix.mulVec_mulVec, ← sq, hsq, Matrix.zero_mulVec]
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  have hξΛ : ξ ∈ X.Λ := by
    have h1 := (hst.2 b).1 hbΛ
    rw [hγb] at h1
    simpa using X.Λ.sub_mem h1 hbΛ
  have hiso : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ = 0 := by
    have h1 := hst.1 ξ b
    rw [hγb, hγξ] at h1
    have h2 : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ (b + ξ) =
        ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ b + ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ := by
      simp [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, mul_add, Finset.sum_add_distrib]
    rw [h2] at h1
    simpa using h1
  have hemb : ∀ (τ : X.Ψ) (v : Fin N → E),
      Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 v) =
        Data.emb τ.1 (Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) v) := by
    intro τ v
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hshift : ∀ w : ℂ, T < w.im → ∀ (τ : X.Ψ) (v : Fin N → ℂ),
      X.maj (x (w + M)) τ (Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) v) = X.maj (x w) τ v := by
    intro w hw τ v
    obtain ⟨β, hβ, -, he⟩ := hsh w hw
    rw [he, GlobalTheory.MajInv.maj_rmul X (GlobalTheory.MajInv.lact_mem_dom X hst (hdom w hw)) hβ, GlobalTheory.MajInv.maj_lact X hst]
  have hA : ∀ τ : X.Ψ, ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, T + 1 < w.im →
      X.maj (x w) τ (Data.emb τ.1 ξ) * (w.im - T) ≤ A := by
    intro τ
    have eξ : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ := by
      rw [hemb, hγξ]
    have eb : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 b) =
        Data.emb τ.1 b + Data.emb τ.1 ξ := by
      rw [hemb, hγb]; funext i; simp [Data.emb]
    refine quad_bound (fun w v => X.maj (x w) τ v) T M hM (Data.emb τ.1 b) (Data.emb τ.1 ξ) ?_
      (fun w k v => maj_natCast_smul X _ τ k v) (fun w u v => maj_parallelogram X _ τ u v)
      (fun w w' hw hw' v => _root_.GlobalTheory.maj_harnack E N X T x hd hdom w w' hw hw' τ v) ?_ ?_
    · intro w hw v
      by_cases hv : v = 0
      · have := maj_natCast_smul X (x w) τ 0 v
        subst hv
        rw [smul_zero, Nat.cast_zero, sq, zero_mul, zero_mul] at this
        exact this.ge
      · exact (X.maj_pos (hdom w hw) τ hv).le
    · intro w hw
      have := hshift w hw τ (Data.emb τ.1 ξ)
      rwa [eξ] at this
    · intro w hw k
      have := hshift w hw τ (Data.emb τ.1 b + (k : ℂ) • Data.emb τ.1 ξ)
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, eξ, eb] at this
      rw [← this]
      congr 1
      push_cast
      rw [add_smul, one_smul]; abel
  choose A hA0 hA using hA
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero_iff τ.1 τ.1.injective).2 X.ξ0_ne
    unfold Data.c
    positivity
  have hK0 : 0 ≤ ∑ τ, X.c τ * A τ := Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ).le (hA0 τ)
  refine ⟨ξ, 1 / (1 + ∑ τ, X.c τ * A τ), ⟨hξΛ, hiso, hb⟩, by positivity, fun w hw τ => ?_⟩
  have hv : Data.emb τ.1 ξ ≠ 0 := fun h => hb (funext fun a =>
    (map_eq_zero_iff τ.1 τ.1.injective).1 (congrFun h a))
  have hp := X.maj_pos (hdom w (by linarith)) τ hv
  have hle : X.c τ * A τ ≤ ∑ τ, X.c τ * A τ :=
    Finset.single_le_sum (f := fun τ => X.c τ * A τ) (fun τ _ => mul_nonneg (hc τ).le (hA0 τ)) (Finset.mem_univ τ)
  have h1 := mul_le_mul_of_nonneg_left (hA τ w hw) (hc τ).le
  unfold Data.tt
  rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (mul_pos (hc τ) hp)]
  nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertibleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigCoord GlobalTheory.LieLocBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (ψ : R →+* R'), IsLocalRing R' → f.Stable → x' = spMap ψ ≫ x → φ' = ψ.comp φ → (∀ g : EigFrame Z φ' x', (∃! A : Mat Dw.mult R', f.Coord ψ g A) ∧ ∀ A, f.Coord ψ g A → ∀ τ, IsUnit (A τ).det) ∧ ∀ A : Mat Dw.mult R', (∀ τ, IsUnit (A τ).det) → ∃ g : EigFrame Z φ' x', f.Coord ψ g A := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' ψ _ hf hx' hφ'
  subst hx' hφ'
  obtain ⟨g₀, hg₀⟩ := hf R' ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t (spMap ψ ≫ x)
  choose B₀ hB₀ using exists_basis hx g₀
  have hv : ∀ τ, (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g₀.v τ := fun τ => funext fun k => (hg₀ τ k).symm
  have key : ∀ (g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x))
      (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R' (eig c (ψ.comp φ) hx τ)),
      (∀ τ i, g.v τ i = vec Z.t _ xc (B τ i)) → ∀ A : Mat Dw.mult R',
        f.Coord ψ g A ↔ ∀ τ i, B τ i = ∑ j, A τ i j • B₀ τ j := fun g B hB A => by
    simp only [EigFrame.Coord, true_and]
    refine forall_congr' fun τ => forall_congr' fun i => ?_
    rw [hv, hB, show g₀.v τ = fun j => vec Z.t _ xc (B₀ τ j) from funext (hB₀ τ), comb_iff hx, Subtype.ext_iff]
    simp
  refine ⟨fun g => ⟨?_, fun A hA τ => ?_⟩, fun A hA => ?_⟩
  · choose A hA hu using fun τ i => g₀.basis τ (g.v τ i) (g.tan τ i) (g.eig τ i)
    refine ⟨A, ⟨rfl, rfl, fun τ i => by rw [hv]; exact hA τ i⟩, fun A' hA' => ?_⟩
    funext τ i
    exact hu τ i _ (by have := hA'.2.2 τ i; rwa [hv] at this)
  · choose B hB using exists_basis hx g
    exact isUnit_det_of_basis (B₀ τ) (B τ) (A τ) ((key g B hB A).1 hA τ)
  · choose B hB using fun τ => exists_basis_of_isUnit (B₀ τ) (A τ) (hA τ)
    obtain ⟨g, hg⟩ := exists_frame hx B
    exact ⟨g, (key g B hg A).2 hB⟩
end

