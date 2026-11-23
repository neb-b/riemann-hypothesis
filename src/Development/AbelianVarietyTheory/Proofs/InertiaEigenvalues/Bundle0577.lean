module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0469
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem map_ne_top_of_isLoc_ff {l : ℕ} {R : Type} [CommRing R] {B L C : Obj l R} (s : B.A) (h : Hom B L)
    (hL : IsLoc s h) (e : Hom L C) (he : (qmap e 1).FaithfullyFlat) (𝔪 : Ideal B.A) (hm : 𝔪.IsMaximal)
    (hs : s ∉ 𝔪) : 𝔪.map (e.comp h).f ≠ ⊤ := by
  have hJ : adI B ^ 1 ≤ 𝔪 := by
    rw [pow_one]
    haveI := B.complete
    exact le_trans (IsAdicComplete.le_jacobson_bot (adI B)) fun x hx => Ideal.mem_sInf.1 hx ⟨bot_le, hm⟩
  haveI : 𝔪.IsPrime := hm.isPrime
  have hp : (𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hs' : Ideal.Quotient.mk (adI B ^ 1) s ∉ 𝔪.map (Ideal.Quotient.mk (adI B ^ 1)) := by
    rwa [Ideal.mem_quotient_iff_mem hJ]
  letI := (qmap h 1).toAlgebra
  haveI := hL.away 1
  have h1 : ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (Ideal.Quotient.mk (adI B ^ 1) s))
      (L.A ⧸ adI L ^ 1) _ hp ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).2 hs')
  have h2 : ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1)).map (qmap e 1) ≠ ⊤ := by
    intro htop
    apply h1.ne_top
    letI := (qmap e 1).toAlgebra
    haveI : Module.FaithfullyFlat (L.A ⧸ adI L ^ 1) (C.A ⧸ adI C ^ 1) := he
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C.A ⧸ adI C ^ 1)
      ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1))]
    change Ideal.comap (qmap e 1) (Ideal.map (qmap e 1) _) = ⊤
    rw [htop, Ideal.comap_top]
  intro htop
  apply h2
  rw [Ideal.map_map, Ideal.map_map]
  have : ((qmap e 1).comp (qmap h 1)).comp (Ideal.Quotient.mk (adI B ^ 1)) =
      (Ideal.Quotient.mk (adI C ^ 1)).comp (e.comp h).f := RingHom.ext fun _ => rfl
  rw [this, ← Ideal.map_map, htop, Ideal.map_top]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem map_ne_top_of_comp {l : ℕ} {R : Type} [CommRing R] {B Q C : Obj l R} (c : Hom B Q) (π : Hom Q C)
    (a : Hom B C) (hc : π.comp c = a) (𝔪 : Ideal B.A) (ha : 𝔪.map a.f ≠ ⊤) : 𝔪.map c.f ≠ ⊤ := by
  subst hc
  intro htop
  apply ha
  change Ideal.map (π.f.comp c.f) 𝔪 = ⊤
  rw [← Ideal.map_map, htop, Ideal.map_top]

theorem exists_cover_receiving_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)),
    ∃ (C : Obj l ↥(OL K)) (h : Hom B C), Nonempty (Hom bk.prism C) ∧ Cover h := by
  intro l _ K bk B
  obtain ⟨n, s, t, hspan, hst⟩ := _root_.GlobalTheory.BSP.invertible_ideal_principal_on_cover B.A B.I B.inv
  have hga : ∀ i, GenAway B (s i) (t i) := fun i => ⟨(hst i).1, fun x hx => by
    obtain ⟨c, hc⟩ := (hst i).2 x hx
    exact ⟨1, by rw [pow_one, hc]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩⟩
  choose L h hL hLI using fun i => _root_.GlobalTheory.BSP.exists_isLoc l (↥(OL K)) B (s i) (t i) (hga i)
  have hfr : ∀ i, ∃ p, IsFrame bk (L i) ((h i).f (t i)) p := fun i => by
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ((L i).str (bk.str.symm (Ideal.Quotient.mk _ X)))
    exact ⟨p, hLI i, hp⟩
  choose p hp using hfr
  have En : ∀ i, Env bk (L i) ((h i).f (t i)) (p i) := fun i => (_root_.GlobalTheory.BSP.nonempty_env l K bk (L i) _ _ (hp i)).some
  obtain ⟨Q, π, hbij, -, huniv⟩ := _root_.GlobalTheory.Prism.finite_product_oriented l (↥(OL K)) n (fun i => (En i).Q) fun i => ⟨_, (En i).I_eq⟩
  obtain ⟨c, hc⟩ := huniv B fun i => (En i).inl.comp (h i)
  obtain ⟨g, -⟩ := huniv bk.prism fun i => (En i).inr
  refine ⟨Q, c, ⟨g⟩, ?_⟩
  have hcov : ∀ i, Cover (En i).inl := fun i => _root_.GlobalTheory.BSP.env_inl_cover l K bk (L i) _ _ (hp i) (En i)
  have hstab : ∀ i, Stable ((π i).comp c) := fun i => by
    rw [hc i]
    exact _root_.GlobalTheory.BSP.stable_comp l _ B (L i) (En i).Q (h i) (En i).inl
      (_root_.GlobalTheory.BSP.stable_of_isLoc l _ B (L i) (s i) (h i) ⟨t i, (hga i).1, (hga i).2⟩ (hL i)) (hcov i).stable
  refine _root_.GlobalTheory.BSP.cover_of_stable_of_map_ne_top l _ B Q c (_root_.GlobalTheory.ProdStable.prodStable l _ n _ (fun i => ⟨_, (En i).I_eq⟩) Q π hbij B c hstab) ?_
  intro 𝔪 hm
  obtain ⟨i, hi⟩ : ∃ i, s i ∉ 𝔪 := by
    by_contra hall
    push_neg at hall
    exact hm.ne_top (eq_top_iff.2 (hspan ▸ Ideal.span_le.2 (Set.range_subset_iff.2 hall)))
  exact map_ne_top_of_comp c (π i) _ (hc i) 𝔪
    (map_ne_top_of_isLoc_ff (s i) (h i) (hL i) (En i).inl ((hcov i).ff 1) 𝔪 hm hi)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionLatticeIsCrysTameTypeWithJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.ExtGood

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l}
  [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l)

abbrev ext (T : QLat LL) (z : ↥(latticeCocycles T.L)) : QLat LL :=
  GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z

theorem aeval_mul_eq_zero {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (A : Module.End K M)
    (p q : Polynomial K) (x : M) (h : Polynomial.aeval A q x = 0) : Polynomial.aeval A (p * q) x = 0 := by
  rw [map_mul, Module.End.mul_apply, h, map_zero]

theorem isGood_mono (T : QLat LL) {Sig : Finset (ZMod e)} {U : Finset ℤ} (h : IsGood a ϖ Pl T {0} {0})
    (hS : (0 : ZMod e) ∈ Sig) (hU : (0 : ℤ) ∈ U) : IsGood a ϖ Pl T Sig U := by
  refine ⟨h.crys, fun g hg w hw x hx => ?_, fun τ j hj => ?_⟩
  · have h1 := h.type g hg w hw x hx
    rw [Finset.prod_singleton] at h1
    rw [← Finset.prod_erase_mul _ _ hS]
    exact aeval_mul_eq_zero _ _ _ _ h1
  · have h2 := h.jumps τ j hj
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at h2
    subst h2
    exact hU

def incl (T : QLat LL) (z : ↥(latticeCocycles T.L)) : LatHom T.L (ext T z).L where
  f := LinearMap.inl ↥LL.1 T.V ↥LL.1
  equiv g x := by
    change ((T.ρ g x, 0) : T.V × ↥LL.1) = (T.ρ g x + (0 : ↥LL.1) • (z : Gl l → T.V) g, 0)
    simp
  cont := continuous_id.prodMk continuous_const
  T_le x hx := ⟨hx, 0, map_zero _⟩

def proj (T : QLat LL) (z : ↥(latticeCocycles T.L)) : LatHom (ext T z).L (unitLat (Gl l) : QLat LL).L where
  f := LinearMap.snd ↥LL.1 T.V ↥LL.1
  equiv g x := rfl
  cont := continuous_snd
  T_le x hx := hx.2

theorem extLat_isGood : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ), (0 : ZMod e) ∈ Sig → (0 : ℤ) ∈ U → IsGood a ϖ Pl (unitLat (Gl l) : QLat LL) Sig U ∧ ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ (Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L) (v : Tp.V), IsSESLat (Qp := ℚ_[l]) f g ∧ v ∈ Tp.L.T ∧ g.f v = (1 : ↥LL.1) ∧ (∀ h, Tp.ρ h v - v = f.f (c h)) ∧ IsGood a ϖ Pl Tp Sig U := by
  intro _ l _ a e _ _ ϖ LL _ _ Pl AI hstd Sig U hS hU
  refine ⟨isGood_mono ϖ Pl _ (UnitModel.isGood_of_trivial ϖ Pl _ fun _ _ => rfl) hS hU, fun T hT c hc => ?_⟩
  let z : ↥(latticeCocycles T.L) := ⟨c, hc.1⟩
  have hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := hc.2
  have hcr := GlobalTheory.T.crystalline_of_extension_lattice ϖ Pl T hT.crys z hz
  refine ⟨ext T z, incl T z, proj T z, ((0 : T.V), (1 : ↥LL.1)), ⟨LinearMap.inl_injective,
    fun y => ⟨(0, y), rfl⟩, fun y hy => ?_, fun x => ?_, fun y hy => ?_⟩, ⟨zero_mem _, 1, (algebraMap (OL LL) LL.1).map_one⟩, rfl,
    fun h => ?_, ⟨hcr, GlobalTheory.T.tame_type_of_extension_lattice ϖ Pl T Sig hS hT.type z hz, GlobalTheory.T.crystalline_extension_of_jumps ϖ Pl AI hstd T U hU hT.crys hT.jumps z hcr⟩⟩
  · obtain ⟨o, rfl⟩ := hy
    exact ⟨(0, Algebra.linearMap _ _ o), ⟨zero_mem _, o, rfl⟩, rfl⟩
  · change x.2 = 0 ↔ ∃ y, ((y, 0) : T.V × ↥LL.1) = x
    exact ⟨fun h0 => ⟨x.1, Prod.ext rfl h0.symm⟩, fun ⟨y, hy⟩ => by rw [← hy]⟩
  · exact hy.1
  · change ((T.ρ h 0 + (1 : ↥LL.1) • (z : Gl l → T.V) h, (1 : ↥LL.1)) : T.V × ↥LL.1) - (0, 1) = (c h, 0)
    simp only [map_zero, zero_add, one_smul]
    exact Prod.ext (sub_zero _) (sub_self _)

end GlobalTheory.ExtGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPair
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerCharH1

theorem le_of_pow_le {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  push_neg at hab
  have key : ∀ r : ℕ, q ^ r ≤ C := by
    intro r
    have h1 := h r
    have hpos : 0 < q ^ (r * b) := pow_pos (by omega) _
    have : q ^ (r * a) ≥ q ^ (r * b) * q ^ r := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    have : q ^ (r * b) * q ^ r ≤ C * q ^ (r * b) := le_trans this h1
    rw [mul_comm (q ^ (r * b))] at this
    exact Nat.le_of_mul_le_mul_right this hpos
  have h2 := key C
  have h3 : C < 2 ^ C := Nat.lt_two_pow_self
  have h4 : 2 ^ C ≤ q ^ C := Nat.pow_le_pow_left hq C
  omega

theorem stableSub_span_smul {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (c : O) :
    StableSub L (Ideal.span {c} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  rw [Submodule.ideal_span_singleton_smul] at hx ⊢
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨actT L g y, Submodule.mem_top, (map_smul _ _ _).symm⟩

end GlobalTheory.EulerCharH1

namespace GlobalTheory.EulerCharH1

theorem natCast_not_isUnit (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (hint : ∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔
      RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) :
    ¬ IsUnit ((l : ℕ) : O) := by
  rintro ⟨u, hu⟩
  have hl0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hy : algebraMap O LL ((u⁻¹ : Oˣ) : O) = algebraMap ℚ_[l] LL (((l : ℕ) : ℚ_[l])⁻¹) := by
    rw [map_inv₀, map_natCast]
    have h1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_natCast] at h1
    exact eq_inv_of_mul_eq_one_left h1
  obtain ⟨p, hpm, hp⟩ := (hint _).mp ⟨_, hy⟩
  rw [← Polynomial.hom_eval₂] at hp
  have hp' : p.eval₂ (algebraMap ℤ_[l] ℚ_[l]) (((l : ℕ) : ℚ_[l])⁻¹) = 0 :=
    (algebraMap ℚ_[l] LL).injective (by rw [hp, map_zero])
  have hI : IsIntegral ℤ_[l] (((l : ℕ) : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI
  have hlw : ((l : ℕ) : ℤ_[l]) * w = 1 := by
    apply IsFractionRing.injective ℤ_[l] ℚ_[l]
    rw [map_mul, hw, map_natCast, map_one, mul_inv_cancel₀ hl0]
  exact PadicInt.p_nonunit (IsUnit.of_mul_eq_one _ hlw)

end GlobalTheory.EulerCharH1

namespace GlobalTheory.EulerCharH1

theorem two_le_card (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) : 2 ≤ Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) := by
  obtain ⟨hint, -, hfin, -⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  have hf : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by
    simpa using hfin 1
  have : Nontrivial (O ⧸ Ideal.span {((l : ℕ) : O)}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit l LL O hint)
  exact Finite.one_lt_card

theorem eq_of_bounds {q a h0 h0' d C1 C2 C3 C4 : ℕ} (X Y H H' : ℕ → ℕ) (hq : 2 ≤ q)
    (hX : ∀ r, q ^ (r * a) ≤ X r ∧ X r ≤ C1 * q ^ (r * a))
    (hY : ∀ r, X r ≤ Y r ∧ Y r ≤ C2 * X r)
    (hE : ∀ r, Y r = H r * H' r * q ^ (r * d))
    (hH : ∀ r, q ^ (r * h0) ≤ H r ∧ H r ≤ C3 * q ^ (r * h0))
    (hH' : ∀ r, q ^ (r * h0') ≤ H' r ∧ H' r ≤ C4 * q ^ (r * h0')) :
    a = h0 + h0' + d := by
  have key : ∀ r : ℕ, q ^ (r * a) ≤ C3 * C4 * q ^ (r * (h0 + h0' + d)) ∧
      q ^ (r * (h0 + h0' + d)) ≤ C2 * C1 * q ^ (r * a) := by
    intro r
    obtain ⟨hX1, hX2⟩ := hX r
    obtain ⟨hY1, hY2⟩ := hY r
    obtain ⟨hH1, hH2⟩ := hH r
    obtain ⟨hH1', hH2'⟩ := hH' r
    have hpow : q ^ (r * (h0 + h0' + d)) = q ^ (r * h0) * q ^ (r * h0') * q ^ (r * d) := by
      rw [← pow_add, ← pow_add]; ring_nf
    constructor
    · calc q ^ (r * a) ≤ X r := hX1
        _ ≤ Y r := hY1
        _ = H r * H' r * q ^ (r * d) := hE r
        _ ≤ (C3 * q ^ (r * h0)) * (C4 * q ^ (r * h0')) * q ^ (r * d) := by
          gcongr
        _ = C3 * C4 * q ^ (r * (h0 + h0' + d)) := by rw [hpow]; ring
    · calc q ^ (r * (h0 + h0' + d)) = q ^ (r * h0) * q ^ (r * h0') * q ^ (r * d) := hpow
        _ ≤ H r * H' r * q ^ (r * d) := by gcongr
        _ = Y r := (hE r).symm
        _ ≤ C2 * X r := hY2
        _ ≤ C2 * (C1 * q ^ (r * a)) := by gcongr
        _ = C2 * C1 * q ^ (r * a) := by ring
  have h1 := le_of_pow_le hq (fun r => (key r).1)
  have h2 := le_of_pow_le hq (fun r => (key r).2)
  omega

theorem finite_and_finrank_H1V : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL],
    GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m →
    Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) +
      finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  intro hTD hEC l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨LA, LA', hLL, -⟩ := GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm
  have hfinT : Module.Finite O (LatticeCohomology LA) := GlobalTheory.T.finite_H1_period_datum hTD l P K LL O hO A LA
  obtain ⟨hfinV, C1, -, hX⟩ := GlobalTheory.T.H1_lattice_rank_growth_of_goodO l K LL O hO A LA hfinT
  obtain ⟨C2, -, hY⟩ := GlobalTheory.T.H1_reduction_index_bound_of_tateDuality hTD l P K LL O hO A A' LA LA' m hLL
  obtain ⟨C3, -, hH⟩ := GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice l K LL O hO A LA
  obtain ⟨C4, -, hH'⟩ := GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice l K LL O hO A' LA'
  exact ⟨hfinV, eq_of_bounds _ _ _ _ (two_le_card l LL O hO) hX
    (fun r => hY r (stableSub_span_smul LA _))
    (fun r => GlobalTheory.T.H1_lattice_index_growth_of_tateDuality_eulerChar hTD hEC l P K LL O hO A A' LA LA' m hLL r
      (stableSub_span_smul LA _) (stableSub_span_smul LA' _))
    (fun r => hH r (stableSub_span_smul LA _)) (fun r => hH' r (stableSub_span_smul LA' _))⟩

end GlobalTheory.EulerCharH1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisSubValueMemFilZeroOfMonodromyZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

theorem GlobalTheory.BKGal.sub_sub_xi_mem_Man : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ σ : D.MMl, D.conn σ.1 = D.zeta y → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), σ.1 - y - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ ι _ _ η H D y hyY hMon σ hσ m
  have hyM : E K l e ^ η • y ∈ D.M := mem_divE.1 hyY.1
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  have hv : σ.1 - y ∈ divE l e η D.Man := by
    rw [mem_divE, smul_sub]
    exact sub_mem (D.Mext_mono (invL_S_le_Rpi l e) hσM) (D.M_le_Man hyM)
  have hEN : D.EN (σ.1 - y) ∈ D.Man := by
    have h0 : D.EN y - E K l e • D.zeta y ∈ D.Man := by
      rw [← D.cls_eq_zero_iff, ← D.Mon_apply]; exact hMon
    have h1 : D.EN (σ.1 - y) = -(D.EN y - E K l e • D.zeta y) := by
      rw [map_sub, D.EN_apply σ.1, hσ]; abel
    rw [h1]; exact neg_mem h0
  exact _root_.GlobalTheory.HorizPole.main O K l e a ι η H D η _ hv hEN m

theorem GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon hy σ hσinv hconn b₂ hb₂ g hg C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  obtain ⟨m₀, hxi⟩ := _root_.GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero l a e O K t ϖ hl2 ι η H D T R
  obtain ⟨w, hw, hr, hN⟩ := GlobalTheory.BKGal.sub_sub_xi_mem_Man l a e O K ι η H D y hyY hMon σ hconn m₀
  have hwM : D.xiExt w ∈ D.MMl :=
    ((_root_.GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι D.toPhiMod).2 w).2 (D.Mext_mono (away_mono (A_le_S l e) rfl) hw)
  set ξw : D.MMl := ⟨D.xiExt w, hwM⟩ with hξw
  have hr' : (σ - ξw).1 - y ∈ D.Man := by
    have : (σ - ξw).1 - y = σ.1 - y - D.xiExt w := by
      rw [Submodule.coe_sub, hξw]; abel
    rw [this]; exact hr
  have h3 := _root_.GlobalTheory.BKGal.value_hat_mem_filZero l a e O K t ϖ hl2 ι η H D T R (σ - ξw) y hy hr' b₂ hb₂ C
  have h4 := _root_.GlobalTheory.BKGal.FilStable.fil_zero_stable l O K T g C _ h3
  have h2 := hxi w hw hN hwM g hg C
  have key : R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ = R.jB (toBcris t ϖ D.toPhiMod ξw) +
      (R.jB (toBcris t ϖ D.toPhiMod (σ - ξw)) - b₂) := by
    rw [map_sub, map_sub]; abel
  rw [key, map_add (f := _)]
  convert add_mem h2 (sub_mem h4 h3) using 1
  abel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLaws
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem finite_natDegree_eq {R : Type} [Semiring R] [Finite R] (n : ℕ) :
    {f : R[X] | f.natDegree = n}.Finite := by
  refine Set.Finite.of_finite_image (f := fun p : R[X] => fun i : Fin (n + 1) => p.coeff i)
    (Set.toFinite _) ?_
  intro p hp q hq hpq
  have hp' : p.natDegree = n := hp
  have hq' : q.natDegree = n := hq
  ext i
  by_cases hi : i ≤ n
  · exact congrFun hpq ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem eSerC_eq_sum {g : ℕ} [Fact g.Prime] (L : LabelDatum g) (n : ℕ)
    (hfin : {χ : Gn g n → ℂ | IsIrr χ}.Finite) (f : (ZMod g)[X]) :
    eSerC L n f = ∑ χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f), zOf χ := by
  have hset : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} =
      ↑(hfin.toFinset.filter (fun χ => HasLabel L χ f)) := by
    ext χ
    simp [Set.Finite.mem_toFinset]
  rw [eSerC, hset, finsum_mem_coe_finset]

theorem eSerC_laws : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ n : ℕ, (∀ f, eSerC L n f * eSerC L n f = eSerC L n f) ∧ (∀ f a, eSerC L n f * a = a * eSerC L n f) ∧ (∀ f f', f ≠ f' → eSerC L n f * eSerC L n f' = 0) ∧ (∀ f, ¬ (f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) → eSerC L n f = 0) ∧ ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, eSerC L n f = 1 := by
  intro g _ L hg hG n
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  obtain ⟨huniq, hprops, -⟩ := _root_.GlobalTheory.GLq.Label.label_main g L hg hG n
  have horth := _root_.GlobalTheory.GLq.ZOrth.zorth (Gn g n)
  have he : ∀ f, eSerC L n f = ∑ χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f), zOf χ :=
    fun f => eSerC_eq_sum L n hfin f
  have hmem : ∀ f χ, χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f) ↔ IsIrr χ ∧ HasLabel L χ f := by
    intro f χ
    simp [Set.Finite.mem_toFinset]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [he f, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hχi := ((hmem f χ).1 hχ).1
    rw [Finset.sum_congr rfl fun χ' hχ' => (horth χ χ' hχi ((hmem f χ').1 hχ').1).1,
      Finset.sum_ite_eq, if_pos hχ]
  · intro f a
    rw [he f, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ hχ =>
      (horth χ χ ((hmem f χ).1 hχ).1 ((hmem f χ).1 hχ).1).2.1 a
  · intro f f' hff'
    rw [he f, he f', Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun χ hχ => Finset.sum_eq_zero fun χ' hχ' => ?_
    obtain ⟨hi, hl⟩ := (hmem f χ).1 hχ
    obtain ⟨hi', hl'⟩ := (hmem f' χ').1 hχ'
    rw [(horth χ χ' hi hi').1, if_neg]
    rintro rfl
    exact hff' ((huniq χ hi).unique hl hl')
  · intro f hf
    rw [he f]
    exact Finset.sum_eq_zero fun χ hχ => absurd (hprops χ f ((hmem f χ).1 hχ).2) hf
  · have hS := finite_natDegree_eq (R := ZMod g) n
    have hSmem : ∀ f, f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0) ↔
        f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
      intro f
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      tauto
    refine ⟨_, hSmem, ?_⟩
    calc ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0), eSerC L n f
        = ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0),
            ∑ χ ∈ hfin.toFinset, if HasLabel L χ f then zOf χ else 0 := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [he f, Finset.sum_filter]
      _ = ∑ χ ∈ hfin.toFinset, ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0),
            if HasLabel L χ f then zOf χ else 0 := Finset.sum_comm
      _ = ∑ χ ∈ hfin.toFinset, zOf χ := by
          refine Finset.sum_congr rfl fun χ hχ => ?_
          have hi : IsIrr χ := hfin.mem_toFinset.1 hχ
          obtain ⟨f0, hf0, hu⟩ := huniq χ hi
          rw [Finset.sum_eq_single f0]
          · rw [if_pos hf0]
          · intro b _ hb
            rw [if_neg]
            exact fun h => hb (hu b h)
          · intro h0
            exact absurd ((hSmem f0).2 (hprops χ f0 hf0)) h0
      _ = 1 := by
          rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
          exact hsum

end GlobalTheory.GLq
end

