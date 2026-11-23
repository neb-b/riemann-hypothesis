module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrime
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommonDenominatorOfValuationLeOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_common_denominator_of_valuation_le_one {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (a : Fin n → K) (ha : ∀ m, p.valuation K (a m) ≤ 1) :
    ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∀ m, ∃ b : 𝓞 K, s • a m = algebraMap (𝓞 K) K b := by
  choose nn dd hnd using fun m => p.exists_primeCompl_mul_eq_of_integer (a m) (ha m)
  have hs : (∏ m, (dd m : 𝓞 K)) ∈ p.asIdeal.primeCompl := prod_mem fun m _ => (dd m).2
  refine ⟨∏ m, (dd m : 𝓞 K), hs, fun m => ?_⟩
  refine ⟨nn m * ∏ j ∈ Finset.univ.erase m, (dd j : 𝓞 K), ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Algebra.smul_def]
  simp only [map_mul]
  rw [← hnd m]
  ring

theorem IsModelAt.rows_span_lieLat {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) {p : HeightOneSpectrum (𝓞 K)}
    {M : Matrix (Fin x.P.g) (Fin x.P.g) K} (hM : IsModelAt A x φ p M) :
    (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat) ∧
      ∀ c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧
        s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  have hdet : M.det ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ := hM
    exact h
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have key := isModelAt_integral_iff_mem_lieLat K A x φ hf p M hM
  refine ⟨fun i => (key (M i)).mp fun m => ?_, fun c hc => ?_⟩
  · have h1 : Matrix.vecMul (M i) M⁻¹ m = (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i m := by
      rw [← Matrix.mul_nonsing_inv (A := M) hu]
      rfl
    rw [h1, Matrix.one_apply]
    split_ifs <;> simp
  · have hone : (1 : 𝓞 K) ∉ p.asIdeal := fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    have hv := (key c).mpr ⟨1, hone, by simpa using hc⟩
    obtain ⟨s, hs, hb⟩ := exists_common_denominator_of_valuation_le_one p (Matrix.vecMul c M⁻¹) hv
    choose b hb using hb
    refine ⟨s, hs, ?_⟩
    have hc' : c = ∑ m, Matrix.vecMul c M⁻¹ m • M m := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul (A := M) hu, Matrix.vecMul_one]
    rw [hc', Finset.smul_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [← smul_assoc, hb m, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

theorem exists_keyLines : Out.SecTwistSt → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∃ T abelian₂ : MLine K, T.Good ∧ abelian₂.Good ∧ (∀ p, KeyLocAt x T abelian₂ p) ∧ (∀ σ, KeyArchAt x T abelian₂ σ) ∧ ∀ p, ∃ M, IsModelAt A x φ p M ∧ IsLocGen p M.det abelian₂.I := by
  intro hT hU _hL hH K _ _ A x φ hfib
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).mp hfib
  let F : GenFib A := GenFib.mk x.P φ hf x.v x.basis
  obtain ⟨hFG, hspan⟩ := _root_.GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K A F
  obtain ⟨IL, hIL0, hIL⟩ := _root_.GlobalTheory.LamF.exists_detIdeal_isLocGen K x.P.g F.lieLat hFG hspan
  obtain ⟨δ, oa, nth, hloc, -, hsupp, -⟩ :=
    GlobalTheory.ThetaDegree.exists_isThetaDeg hT hU K A F x.g_pos x.rig x.rig_gen x.th x.6
  obtain ⟨IT, hIT0, hIT⟩ := _root_.GlobalTheory.LamF.exists_fractionalIdeal_isLocGen_of_valuation K oa hsupp
  choose t n ht hn hArch using fun σ => _root_.GlobalTheory.LamF.KeyArch.exists_pos_keyArchAt hU K x σ
  refine ⟨⟨IT, t⟩, ⟨IL, n⟩, And.intro hIT0 ht, And.intro hIL0 hn, fun p => ?_,
    fun σ => hArch σ _ _ rfl rfl, fun p => ?_⟩
  · obtain ⟨a, M, hM, hva⟩ := hloc p
    have hrows := _root_.GlobalTheory.CM.lieLat_of_isLocalModel hH K A F x.g_pos x.rig x.rig_gen x.th x.6 p a M hM
    exact _root_.GlobalTheory.LamF.keyLocAt_of_isLocalModel K x ⟨IT, t⟩ ⟨IL, n⟩ p a M hM (hIT p a hva) (hIL p M hrows.1 hrows.2)
  · obtain ⟨M, hM⟩ := _root_.GlobalTheory.LamF.exists_isModelAt hT K A x φ hfib p
    have hrows := hM.rows_span_lieLat hf
    exact ⟨M, hM, hIL p M hrows.1 hrows.2⟩

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → (∃ g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr), (∀ b, IsUnit (g b).det) ∧ ∀ (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg g a y y' → LieInt T io m1 m2 y'.u) ∧ (LieInt T io m1 m2 y.u → ∀ (X : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.V)) (a : T.Fr) (y' : FrPt Xo c T.Fr), (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T.V T.Fr)) a y y' → LieInt T io m1 m2 y'.u) := by
  first | exact @GlobalTheory.LamT.lieInt_exists_and_change | exact GlobalTheory.LamT.lieInt_exists_and_change | (intros; apply GlobalTheory.LamT.lieInt_exists_and_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLattices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.GenFib


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat (K : Type) [Field K]
    [NumberField K] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (𝓞 K))) (F : _root_.GlobalTheory.CM.GenFib P) (O : Type)
    [CommRing O] (act : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O P.A) :
    ∃ r : O →+* Module.End K (Fin F.P₀.g → K),
      (∀ a, F.IsDiffOf F (act.act a) (r a)) ∧
      ∀ (τ : O →+* 𝓞 K) c, (c ∈ F.eigLat act τ ↔
          c ∈ F.lieLat ∧ ∀ a, r a c = τ a • c) ∧
        (c ∈ Submodule.span K (F.eigLat act τ :
            Set (Fin F.P₀.g → K)) ↔ ∀ a, r a c = τ a • c) := by
  obtain ⟨hex, hinj, -, -, hlie, heig⟩ := _root_.GlobalTheory.CM.integral_tangent_coordinates K P F
  have hcoord : ∀ {u c c'}, F.IsCoord u c → F.IsCoord u c' → c = c' := fun h h' =>
    (hex _ h.1).unique h h'
  have hdiff : ∀ a, ∃! M, F.IsDiffOf F (act.act a) M := fun a =>
    (_root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F (act.act a) (act.hom a)).1
  choose R hR using fun a => (hdiff a).exists
  have huniq : ∀ a M, F.IsDiffOf F (act.act a) M → R a = M :=
    fun a M h => (hdiff a).unique (hR a) h
  have hone : R 1 = 1 := huniq 1 1 (by
    intro u c h
    simpa [act.one] using h)
  have hmul : ∀ a b, R (a * b) = R a * R b := fun a b => by
    rw [mul_comm a b]
    refine huniq _ _ ?_
    intro u c h
    rw [act.mul, ← Category.assoc]
    exact hR a _ _ (hR b u c h)
  have hadd : ∀ a b, R (a + b) = R a + R b := fun a b => by
    refine huniq _ _ ?_
    intro u c h
    rw [act.add, comp_mul]
    exact _root_.GlobalTheory.CM.IntCoord.isCoord_mul F (hR a u c h) (hR b u c h)

  have hspan : Submodule.span K (F.lieLat :
      Set (Fin F.P₀.g → K)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφ0 (LinearMap.ext h)
    have hM : F.IsDiffOf F (act.act 1) (1 + φ.smulRight x) := by
      intro u c h
      have hφc : φ c = 0 := LinearMap.mem_ker.1 (hle (Submodule.subset_span ((hlie c).2 ⟨u, h⟩)))
      simpa [act.one, hφc] using h
    have h1 := LinearMap.congr_fun (hone.symm.trans (huniq 1 _ hM)) x
    simp at h1
    rcases h1 with h1 | h1
    · exact hx h1
    · exact hx (by simp [h1])
  have hlat : ∀ τ : O →+* 𝓞 K, ∀ c, c ∈ F.eigLat act τ ↔
      c ∈ F.lieLat ∧ ∀ a, R a c = τ a • c := by
    intro τ c
    rw [heig O act τ c, hlie c]
    constructor
    · rintro ⟨u, hu, hcomb⟩
      exact ⟨⟨u, hu⟩, fun a =>
        hcoord (hR a u c hu) (_root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu (hcomb a))⟩
    · rintro ⟨⟨u, hu⟩, hc⟩
      refine ⟨u, hu, fun a => ?_⟩
      have hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb ![τ a] ![u] (_root_.GlobalTheory.CM.IntCoord.sc (τ a) ≫ u) :=
        (_root_.GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl
      have he := hinj _ _ _ (hR a u c hu)
        (by rw [hc a]; exact _root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu hs)
      rw [he]
      exact hs
  refine ⟨RingHom.mk' ⟨⟨R, hone⟩, hmul⟩ hadd, fun a => hR a, fun τ c => ⟨hlat τ c, ?_⟩⟩
  show _ ↔ ∀ a, R a c = τ a • c
  constructor
  · intro hc
    refine Submodule.span_induction (p := fun c _ => ∀ a, R a c = τ a • c) ?_ ?_ ?_ ?_ hc
    · exact fun x hx a => ((hlat τ x).1 hx).2 a
    · intro a
      simp
    · intro x y _ _ hx hy a
      rw [map_add (f := _), hx, hy, smul_add]
    · intro k x _ hx a
      rw [map_smul, hx, smul_comm]
  · intro hc
    have hcspan : c ∈ Submodule.span K (F.lieLat :
        Set (Fin F.P₀.g → K)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 K))).1 hcspan
    rw [Submodule.span_eq] at hy
    have hzy : (z : 𝓞 K) • (IsLocalization.mk' K (1 : 𝓞 K) z • y) = y := by
      rw [← smul_assoc, Algebra.smul_def (z : 𝓞 K) (IsLocalization.mk' K (1 : 𝓞 K) z),
        IsLocalization.mk'_spec', map_one, one_smul]
    have hyeig : ∀ a, R a y = τ a • y := fun a => by
      rw [← hzy, LinearMap.map_smul_of_tower, hc a, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hlat τ y).2 ⟨hy, hyeig⟩))

end GlobalTheory.CM.GenFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetrisedLineOfLieVector
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_fractionalIdeal_single_mem {K : Type} [Field K] [NumberField K] {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K))
    (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (i : Fin n) :
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ c : K, c ∈ I ↔ Pi.single i c ∈ Λ := by
  let J : Submodule (𝓞 K) K := Λ.comap (LinearMap.single (𝓞 K) (fun _ : Fin n => K) i)
  have hle : J ≤ Λ.map (LinearMap.proj i) := fun c hc => ⟨_, hc, by simp⟩
  have hJ : J.FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ (hfg.map (LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin n => K) i))
    exact isNoetherian_submodule.1 this _ hle
  refine ⟨⟨J, FractionalIdeal.isFractional_of_fg hJ⟩, fun h0 => ?_, fun c => Iff.rfl⟩
  have h1 : (Pi.single i 1 : Fin n → K) ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ h1
  rw [Submodule.span_eq] at ht
  have h2 : algebraMap (𝓞 K) K t ∈ J := by
    change Pi.single i _ ∈ Λ
    rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul]
    exact ht
  have h3 : J = ⊥ := (congrArg FractionalIdeal.coeToSubmodule h0).trans FractionalIdeal.coe_zero
  rw [h3, Submodule.mem_bot] at h2
  exact nonZeroDivisors.coe_ne_zero t (FaithfulSMul.algebraMap_injective _ K (h2.trans (map_zero _).symm))

theorem exists_length_of_lieVec (hU : ThetaUnifAV) {K : Type} [Field K] (x : KeyIn K) (i : Fin x.P.g) (σ : K →+* ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∃ (xσ : KeyIn ℂ) (u : HolUnif xσ.P.A xσ.P.L xσ.P.g) (Hm : Matrix (Fin xσ.P.g) (Fin xσ.P.g) ℂ)
      (χ : u.Λ → ℂ) (W : Fin xσ.P.g → ℂ) (hg : xσ.P.g = x.P.g),
      KeyPB xσ x σ ∧ u.IsAH Hm χ ∧ u.IsDiff W (xσ.v (i.cast hg.symm)) ∧
      r ^ 2 = Real.pi * (W ⬝ᵥ Hm.mulVec (star W)).re := by
  obtain ⟨xσ, hx⟩ := KeyPow.exists_keyPB x σ
  have hg : xσ.P.g = x.P.g := by
    obtain ⟨_, _, _, hg, _⟩ := hx
    exact hg
  obtain ⟨u, Hm, χ, -, hA, -, hd, hd', -⟩ := hU xσ.P xσ.rig xσ.rig_gen
  choose W hW using fun i => (hd _ (xσ.basis.1 i)).exists
  have hne := (LieMetric.linearIndependent_of_isLieBasis u hd' xσ.basis hW).ne_zero (i.cast hg.symm)
  have hpos := mul_pos Real.pi_pos (hA.2.1 _ hne)
  exact ⟨_, Real.sqrt_pos.2 hpos, xσ, u, Hm, χ, _, hg, hx, hA, hW _, Real.sq_sqrt hpos.le⟩

theorem exists_isVecLine : Out.SecTwistSt → ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ i : Fin x.P.g, ∃ ℓ : MLine K, IsVecLine A x φ i ℓ := by
  intro hT hU _ K _ _ A x φ hφ i
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ := (isFibreOf_iff_isPolFibre _ _ _ A x φ).1 hφ
  obtain ⟨hfg, hsp⟩ := _root_.GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K A (GenFib.mk x.P φ hf x.v x.basis)
  obtain ⟨I, hI, hmem⟩ := exists_fractionalIdeal_single_mem _ hfg hsp i
  choose r hr H using exists_length_of_lieVec hU x i
  refine ⟨⟨I, r⟩, ⟨hI, hr⟩, fun p => ?_, H⟩
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.LamF.exists_isModelAt hT K A x φ hφ p
  obtain ⟨⟨cl, -, hcl⟩, hiff⟩ := (local_global_ideal_lattice K).2.1 I p hI
  refine ⟨M, cl, hM, hcl, fun c => ?_⟩
  rw [((hiff cl).1 hcl).2 c, ← Matrix.smul_vecMul, isModelAt_integral_iff_mem_lieLat K A x φ hf p M hM]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [hmem, Pi.single_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.HermHom

theorem isTangent_of_isLieComb {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g n : ℕ} (u : HolUnif A L g)
    {W : Fin n → (Fin g → ℂ)} {v : Fin n → (epsR ℂ ⟶ A)} {c : Fin n → ℂ} {w : epsR ℂ ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (h : ∀ i, u.IsDiff (W i) (v i)) (hw : IsLieComb c v w) : IsTangent w := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff] at hw
  subst hw
  rw [← ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff]
  exact (GlobalTheory.UnifDifferential.isDiff_prod u (fun i => c i • W i) _
    (fun i => ReciprocityTheory.ChartRestriction.G.Chart.isTan_scale _ ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 (hv i)))
    (fun i => GlobalTheory.UnifDifferential.isDiff_scale u (h i) _)).1

theorem map_comb {K : Type} [Field K] (s : K →+* ℂ) {A A' : Over (Sp K)} [GrpObj A] [GrpObj A']
    {B B' : Over (Sp ℂ)} [GrpObj B] [GrpObj B'] {ψ : B.left ⟶ A.left} {ψ' : B'.left ⟶ A'.left}
    (hψ : IsGrpPullback B A (spMap s) ψ) (hψ' : IsGrpPullback B' A' (spMap s) ψ')
    {L : LB B.left} {L' : LB B'.left} {g g' n n' : ℕ} (u : HolUnif B L g) (u' : HolUnif B' L' g')
    {v : Fin n → (epsR K ⟶ A)} {v' : Fin n' → (epsR K ⟶ A')}
    (hv : ∀ i, IsTangent (v i)) (hv' : ∀ i, IsTangent (v' i))
    {t : Fin n → (epsR ℂ ⟶ B)} {t' : Fin n' → (epsR ℂ ⟶ B')}
    {W : Fin n → Fin g → ℂ} {W' : Fin n' → Fin g' → ℂ}
    (hW : ∀ i, IsVecOver s ψ (v i) (t i) ∧ u.IsDiff (W i) (t i))
    (hW' : ∀ i, IsVecOver s ψ' (v' i) (t' i) ∧ u'.IsDiff (W' i) (t' i))
    (hu : ∀ x, IsTangent x → ∃! w, u'.IsDiff w x)
    {f : A ⟶ A'} {f₁ : B ⟶ B'} (e : f₁.left ≫ ψ' = ψ ≫ f.left) {Φ : (Fin g → ℂ) → (Fin g' → ℂ)}
    (hΦ : ∀ w x, IsTangent x → u.IsDiff w x → IsTangent (x ≫ f₁) ∧ u'.IsDiff (Φ w) (x ≫ f₁))
    {c : Fin n → K} {c' : Fin n' → K} (hc : ∀ w, IsLieComb c v w → IsLieComb c' v' (w ≫ f)) :
    Φ (∑ i, s (c i) • W i) = ∑ i, s (c' i) • W' i := by
  have ht : ∀ i, IsTangent (t i) := fun i => (hW i).1.isTangent hψ (hv i)
  have ht' : ∀ i, IsTangent (t' i) := fun i => (hW' i).1.isTangent hψ' (hv' i)
  have hw : IsLieComb c v (ReciprocityTheory.ChartRestriction.G.Chart.prodPts c v) :=
    (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff c v _).2 rfl
  have hx : IsLieComb (fun i => s (c i)) t (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t) :=
    (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff _ t _).2 rfl
  have hxo : IsVecOver s ψ (ReciprocityTheory.ChartRestriction.G.Chart.prodPts c v)
      (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t) :=
    (GlobalTheory.lieComb_baseChange _ _ s _ _ ψ hψ _ v _ c t _ (fun j => (hW j).1) hw).2 hx
  have hxT := isTangent_of_isLieComb u ht (fun i => (hW i).2) hx
  have hxD := GlobalTheory.UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W t _ _ ht (fun i => (hW i).2) hx
  obtain ⟨hfT, hfD⟩ := hΦ _ _ hxT hxD
  have hyo := GlobalTheory.NormHom.isVecOver_comp hxo e
  have hy : IsLieComb (fun i => s (c' i)) t' (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t ≫ f₁) :=
    (GlobalTheory.lieComb_baseChange _ _ s _ _ ψ' hψ' _ v' _ c' t' _ (fun j => (hW' j).1) (hc _ hw)).1 hyo
  have hyD := GlobalTheory.UnifDifferential.isDiff_of_isLieComb _ _ _ _ u' W' t' _ _ ht' (fun i => (hW' i).2) hy
  exact (hu _ hfT).unique hfD hyD

private lemma hermForm_sum_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) {J : Type*} (S : Finset J)
    (a : J → ℂ) (z : J → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i ∈ S, a i • z i) w = ∑ i ∈ S, a i * hermForm Hm (z i) w := by
  simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]

private lemma hermForm_sum_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) {J : Type*}
    (S : Finset J) (a : J → ℂ) (w : J → Fin g → ℂ) :
    hermForm Hm z (∑ i ∈ S, a i • w i) = ∑ i ∈ S, starRingEnd ℂ (a i) * hermForm Hm z (w i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [hermForm]
  · intro i S hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp only [hermForm, star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    simp [Complex.star_def]

private lemma hermFam_form_apply_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (x : V) : h.form σ x 0 = 0 := by
  have hx := h.add_right σ x 0 0
  rw [add_zero] at hx
  linear_combination -hx

private lemma form_sum_smul_right {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (x : V) {J : Type*} (S : Finset J) (a : J → K) (y : J → V) :
    h.form σ x (∑ i ∈ S, a i • y i) = ∑ i ∈ S, σ (a i) * h.form σ x (y i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [hermFam_form_apply_zero]
  · intro i S hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, h.add_right, h.smul_right, ih]

private lemma form_sum_smul_left {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (y : V) {J : Type*} (S : Finset J) (a : J → K) (x : J → V) :
    h.form σ (∑ i ∈ S, a i • x i) y = ∑ i ∈ S, starRingEnd ℂ (σ (a i)) * h.form σ (x i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h.conj_symm σ y, form_sum_smul_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.conj_symm]

theorem form_eq {K : Type} [Field K] {n g : ℕ} (h : HermFam K (Fin n → K)) (s : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (r : ℂ)
    (hh : ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = r * hermForm Hm (W j) (W i)) (c c' : Fin n → K) :
    h.form s c c' = r * hermForm Hm (∑ i, s (c' i) • W i) (∑ i, s (c i) • W i) := by
  classical
  have hb : ∀ d : Fin n → K, d = ∑ i, d i • (Pi.single i 1 : Fin n → K) := fun d => by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hb c, hb c']
  rw [form_sum_smul_left]
  simp_rw [form_sum_smul_right, hh, hermForm_sum_smul_left, hermForm_sum_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_diff_eq : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)) (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → F.IsDiffOf F' f M → F.IsDiffOf F g N → ∀ s c c', h'.form s (M c) (M c') = h.form s c (N c') := by
  intro hT hL K _ _ P F P' F' h h' f g M N hh hh' hf hg hl hM hN s c c'
  obtain ⟨Q, ψ, v, u, Hm, χ, W, hQ, hAH, hW, hF⟩ := hh s
  obtain ⟨Q', ψ', v', u', Hm', χ', W', hQ', hAH', hW', hF'⟩ := hh' s
  obtain ⟨-, f₀, hf₀, ef₀, hc₀⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P' F' f hf
  obtain ⟨-, g₀, hg₀, eg₀, hcg₀⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F g hg
  haveI := hf₀
  haveI := hg₀
  obtain ⟨f₁, hf₁, ef₁⟩ := GlobalTheory.NormHom.exists_monHom_lift hQ.2.1 hQ'.2.1 f₀
  obtain ⟨g₁, hg₁, eg₁⟩ := GlobalTheory.NormHom.exists_monHom_lift hQ.2.1 hQ.2.1 g₀
  obtain ⟨-, -, -, -, tu1, tu2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT Q Q.g u Hm χ hAH
  obtain ⟨-, -, -, -, tu1', tu2', -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT Q' Q'.g u' Hm' χ' hAH'
  obtain ⟨Φ, hΦex, -, hΦ, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g
    u u' tu1' tu2' f₁ hf₁
  obtain ⟨Γ, hΓex, -, hΓ, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g
    u u tu1 tu2 g₁ hg₁
  have e1 : ∀ d : Fin F.P₀.g → K, Φ (∑ i, s (d i) • W i) = ∑ i, s (M d i) • W' i := fun d =>
    map_comb s hQ.2.1 hQ'.2.1 u u' (fun i => F.basis.1 i) (fun i => F'.basis.1 i) hW hW' tu1' ef₁ hΦ
      (fun w hw => hc₀ M hM d w hw)
  have e2 : ∀ d : Fin F.P₀.g → K, Γ (∑ i, s (d i) • W i) = ∑ i, s (N d i) • W i := fun d =>
    map_comb s hQ.2.1 hQ.2.1 u u (fun i => F.basis.1 i) (fun i => F.basis.1 i) hW hW tu1 eg₁ hΓ
      (fun w hw => hcg₀ N hN d w hw)
  have lam1 : LamEq F'.P₀.L f₀ f₀ F.P₀.L g₀ (𝟙 F.P₀.A) :=
    GlobalTheory.CM.lamEq_baseChange _ _ _ P.A P.A P'.A P.A F.P₀.A F.P₀.A F'.P₀.A F.P₀.A F.φ F.φ F'.φ F.φ
      F.fib.2.1.1.w F.fib.2.1.1.w F'.fib.2.1 F.fib.2.1 P'.L P.L F'.P₀.L F.P₀.L P'.isLB P.isLB F'.P₀.isLB
      F.P₀.isLB F'.fib.2.2 F.fib.2.2 f f g (𝟙 _) f₀ f₀ g₀ (𝟙 _) ef₀ ef₀ eg₀ (by simp) hl
  have lam2 : LamEq Q'.L f₁ f₁ Q.L g₁ (𝟙 Q.A) :=
    GlobalTheory.CM.lamEq_baseChange _ _ _ F.P₀.A F.P₀.A F'.P₀.A F.P₀.A Q.A Q.A Q'.A Q.A ψ ψ ψ' ψ
      hQ.2.1.1.w hQ.2.1.1.w hQ'.2.1 hQ.2.1 F'.P₀.L F.P₀.L Q'.L Q.L F'.P₀.isLB F.P₀.isLB Q'.isLB Q.isLB
      hQ'.2.2 hQ.2.2 f₀ f₀ g₀ (𝟙 _) f₁ f₁ g₁ (𝟙 _) ef₁ ef₁ eg₁ (by simp) lam1
  have hweil := GlobalTheory.CM.weilEq_of_lamEq hL ℂ Q Q Q' Q f₁ f₁ g₁ (𝟙 _) hf₁ hf₁ hg₁ inferInstance lam2
  have hherm := (_root_.GlobalTheory.CM.weilEq_iff_hermForm_eq hT hL Q Q Q' Q u u u' u Hm' Hm χ' χ hAH' hAH f₁ f₁ g₁ (𝟙 _) Φ Φ Γ LinearMap.id
    hΦex hΦex hΓex (fun z => by simp)).1 hweil
  rw [form_eq h' s Hm' W' _ hF' (M c) (M c'), form_eq h s Hm W _ hF c (N c'), ← e1 c, ← e1 c', ← e2 c', hherm]
  rfl

end GlobalTheory.HermHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MemLieVectorLineIdealIffMemLieLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isVecLine_mem_iff_mem_lieLat : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ c : K, c ∈ ℓ.I ↔ (Pi.single i c : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  intro K _ _ A x φ hf i ℓ h c
  obtain ⟨hgood, hp, -⟩ := h
  choose M cl hM hcl hc using hp
  obtain ⟨h1, -, h3⟩ := local_global_ideal_lattice K
  refine (h1 ℓ.I cl hgood.1 hcl c).trans (Iff.trans ?_ (h3 _ _ _).symm)
  refine forall_congr' fun p => ?_
  refine (hc p c).symm.trans (Iff.trans ?_ (isModelAt_integral_iff_mem_lieLat K A x φ hf p (M p) (hM p) _))
  have e : (Pi.single i c : Fin x.P.g → K) = c • (Pi.single i 1 : Fin x.P.g → K) := by
    rw [← Pi.single_smul', smul_eq_mul, _root_.mul_one]
  rw [e, Matrix.smul_vecMul]

end GlobalTheory.LamF
end

