module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.InFibreLoc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0250
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0237
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0020

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.AbelianPartIntegralPointBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt
open LevelTowerAlt.LocalPrimeBound
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem abelian_part_integral_point_bis : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), 1 ≤ D.p + D.q → (∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → 𝔐.IsLinPtOf z P MV A → ∀ s, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • 𝔐.FibLat (𝔐.V s) z P MV ≤ A.eig s ∧ 𝔞 • A.eig s ≤ 𝔐.FibLat (𝔐.V s) z P MV ∧ Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ 2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E) := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P V _ _ _ _ MV A hpq hdisc hfree hA s
  classical
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  obtain ⟨hact, hlab, hΛ, -⟩ := hA
  obtain ⟨ML, hML⟩ := (LieMove.main L 𝔐.X (spMap (algebraMap (𝓞 L) L) ≫ z) 𝔐.t.G P.tK.G P.m.φ V P.m.cart).2 MV
  have hactL : ML.IsActOf 𝔐.t.act.act A.ρ := fun a x => Over.OverMorphism.ext (by
    rw [← hML, hact a x, Over.comp_left, Over.comp_left, Category.assoc, P.m.act, ← hML, Category.assoc])
  let jE : CMType H ⊕ CMType H → (E →+* L) := fun s => IsFractionRing.lift (A.σ_inj s)
  let σ₀ : CMType H ⊕ CMType H → (𝓞 E →+* 𝓞 L) := fun s => RingOfIntegers.mapRingHom (jE s)
  have hσ₀ : ∀ s, (algebraMap (𝓞 L) L).comp (σ₀ s) = A.σ s := fun s => RingHom.ext fun a =>
    IsFractionRing.lift_algebraMap (A.σ_inj s) a
  have hσ : ∀ s a, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (𝔐.emb s a) (algebraMap (𝓞 L) L (σ₀ s a)) :=
    fun s a => by
      have h := hlab s a
      rw [← hσ₀] at h
      exact h
  have hinj : Function.Injective fun s => (algebraMap (𝓞 L) L).comp (σ₀ s) := by
    simpa only [hσ₀] using A.σ_bij.1
  have hex : ∀ p : ℕ, ∃ (κ : Ω) (k : 𝓞 L), p ∈ S → (HT.HTFree 𝔐 p ∧ HT.Sandwich 𝔐 p κ ∧
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) κ (algebraMap (𝓞 L) L k)) ∧ k ≠ 0 ∧
      Real.log (Ideal.absNorm (Ideal.span {k})) ≤ Module.finrank ℚ L * (2 * (Real.log p / ((p : ℝ) - 1))) := by
    intro p
    by_cases hpS : p ∈ S
    swap
    · exact ⟨0, 0, fun h => absurd h hpS⟩
    have hp := 𝔐.S_prime p hpS
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨κ, hκ, hS⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree hG.2.2.2.2.2.2.1 E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq (hfree p hpS)
    have hne : Ideal.span {(p : 𝓞 L)} ≠ ⊤ := fun h => by
      have h1 := congrArg Ideal.absNorm h
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, RingOfIntegers.rank] at h1
      exact (Nat.one_lt_pow Module.finrank_pos.ne' hp.one_lt).ne' h1
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpQ : (p : 𝓞 L) ∈ Q := hle (Ideal.mem_span_singleton_self _)
    have h1 := (hS _ (inFibre_loc 𝔐 z Q hpQ)).1
    have hq : (⟨centre (spMap (algebraMap (𝓞 L) (Localization.AtPrime Q)) ≫ z), 𝔐.all _⟩ : Cpt 𝔐.ξ) =
        ⟨z (⟨Q, hQ.isPrime⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩ := Subtype.ext (centre_loc z Q)
    rw [hq] at h1
    obtain ⟨r, -, -, hr, -⟩ := PtHt.FinFrame.reg_value z hξ ⟨Q, hQ.isPrime⟩ (𝔐.all _) h1
    obtain ⟨a1, a2⟩ := value_cp hξ hp hκ hr
    obtain ⟨k, rfl, b1, b2⟩ := const_int hp a1 a2
    exact ⟨κ, k, fun _ => ⟨⟨hfree p hpS, hS, hr⟩, b1, b2⟩⟩
  choose κ k hk using hex
  obtain ⟨n1, n2⟩ := norm_bound (jE s) S k fun p hp => (hk p hp).2
  have hset : ∀ 𝔭 : PrimeSpectrum (𝓞 L), {x' : V | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩,
      ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
      𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (MV.pt x').left ≫ P.m.φ = v.left} =
      {x' | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun 𝔭 => by
    ext x'
    constructor
    · rintro ⟨e, he, v, hv, h⟩
      have e' : v = ML.pt x' := Over.OverMorphism.ext (h.symm.trans (hML _))
      exact ⟨e, he, e' ▸ hv⟩
    · rintro ⟨e, he, hv⟩
      exact ⟨e, he, _, hv, hML _⟩
  have hF : ∀ x, x ∈ 𝔐.FibLat (𝔐.V s) z P MV ↔ ∀ 𝔭 : PrimeSpectrum (𝓞 L), ∃ t ∉ 𝔭.asIdeal, t • x ∈
      Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun x => by
    simp only [HodgeCpt.FibLat, hset, Submodule.mem_iInf]
    exact forall_congr' fun 𝔭 => PtHt.FinFrame.span_sat_iff 𝔭.asIdeal le_rfl
      (fun u hu => ⟨1, (Ideal.ne_top_iff_one _).1 𝔭.isPrime.ne_top, by rwa [one_smul]⟩) x
  have hcc : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime], ∃ cc : Localization.AtPrime Q →+* L,
      cc.comp (algebraMap (𝓞 L) _) = algebraMap (𝓞 L) L := fun Q _ => by
    have hunit : ∀ d : Q.primeCompl, IsUnit (algebraMap (𝓞 L) L d) := fun d =>
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2
        fun e => d.2 (e ▸ Q.zero_mem))
    exact ⟨IsLocalization.lift (M := Q.primeCompl) hunit, IsLocalization.lift_comp hunit⟩
  have hloc := fun (Q : Ideal (𝓞 L)) [Q.IsPrime] cc hc =>
    loc 𝔐 z ML A.ρ hactL σ₀ hσ hinj κ k (fun p hp => (hk p hp).1) hdisc s Q cc hc
  rw [hσ₀] at hloc
  refine ⟨_, n1, Submodule.smul_le.2 fun a ha x hx => ?_, Submodule.smul_le.2 fun a _ x hx => ?_, n2⟩
  · have hx' := (hF x).1 hx
    have key : ∀ d ∈ differentIdeal ℤ (𝓞 E), (∏ p ∈ S, k p) • σ₀ s d • x ∈ A.eig s := fun d hd => by
      refine ⟨(hΛ _).2 ?_, ?_⟩
      · let MB := LiePull.extModel (g := algebraMap (𝓞 L) L) (x := z) (FaithfulSMul.algebraMap_injective _ _) rfl ML
        obtain ⟨e, he⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_lifts_of_local (𝓞 L) L 𝔐.X z 𝔐.t.G _ MB (ML.pt ((∏ p ∈ S, k p) • σ₀ s d • x)) (ML.tan _)
          fun Q hQ cc hc => ((hloc Q cc hc).2 x (hx' ⟨Q, hQ.isPrime⟩) d hd).2
        exact ⟨MB.pt e, MB.tan e, (hML _).trans ((Category.comp_id _).symm.trans he)⟩
      · obtain ⟨cc, hc⟩ := hcc ⊥
        exact ((hloc ⊥ cc hc).2 x (hx' ⟨⊥, Ideal.isPrime_bot⟩) d hd).1
    have h1 : (differentIdeal ℤ (𝓞 E)).map (σ₀ s) ≤
        (A.eig s).comap (LinearMap.toSpanSingleton (𝓞 L) V ((∏ p ∈ S, k p) • x)) :=
      Ideal.map_le_iff_le_comap.2 fun d hd => by
        show σ₀ s d • (∏ p ∈ S, k p) • x ∈ A.eig s
        rw [smul_comm]
        exact key d hd
    have h2 : (differentIdeal ℤ (𝓞 E)).map (σ₀ s) * Ideal.span {∏ p ∈ S, k p} ≤
        (A.eig s).comap (LinearMap.toSpanSingleton (𝓞 L) V x) :=
      Ideal.mul_le.2 fun r hr t ht => by
        obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
        show (r * (u * ∏ p ∈ S, k p)) • x ∈ A.eig s
        rw [mul_left_comm, mul_smul, mul_smul]
        exact Submodule.smul_mem _ _ (h1 hr)
    exact h2 ha
  · refine Submodule.smul_mem _ _ ((hF x).2 fun 𝔭 => ?_)
    obtain ⟨cc, hc⟩ := hcc 𝔭.asIdeal
    obtain ⟨v, hv, hxv⟩ := (hΛ x).1 hx.1
    exact (hloc 𝔭.asIdeal cc hc).1 x hx.2 ⟨v, hv, (hML x).symm.trans hxv⟩

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LvExtCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OmLink

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem lv_ext_cancel {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} {k : Type} [Field k]
    (i : Ω →+* k) {x x' : Over.mk ξ ⟶ G} (h : GenWeilModel.ext i ≫ x = GenWeilModel.ext i ≫ x') : x = x' := by
  apply Over.OverMorphism.ext
  have h1 := congrArg (fun f => Over.Hom.left f) h
  simp only [Over.comp_left, GenWeilModel.ext, Over.homMk_left] at h1
  have := epi_sp i
  exact (cancel_epi _).1 h1

section obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {s : Sp Ω ⟶ Sp B}

theorem lv_push_pow {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S'} (a : T ⟶ G') (n : ℕ) :
    pushPt hp.1.w (a ^ n) = pushPt hp.1.w a ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact push_one hp T
  | succ n ih => rw [pow_succ, pow_succ, push_mul hp, ih]

theorem lv_div (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) (y : Over.mk ξ ⟶ t.G) (hy : y ^ n = 1) :
    ∃ x : Over.mk ξ ⟶ t.G, x ^ (n * r) = 1 ∧ x ^ r = y := by
  classical
  have hp := m.cart
  let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
  obtain ⟨a, ha, hpa⟩ := pull_point hp i y hy
  obtain ⟨T⟩ := exists_tate o i
  obtain ⟨α, rfl⟩ := (T.onto n hn a).1 ha
  have hnr : 0 < n * r := Nat.mul_pos hn hr
  obtain ⟨y', -, hy'a⟩ := desc hp hf i (T.ev (n * r) α) ((T.onto (n * r) hnr _).2 ⟨α, rfl⟩)
  let x : Over.mk ξ ⟶ t.G := Over.homMk (y'.left ≫ m.cm.F) (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w y']
    simp)
  have hx : GenWeilModel.ext i ≫ x = pushPt hp.1.w (T.ev (n * r) α) := by
    apply Over.OverMorphism.ext
    rw [hy'a]
    simp [x, pushPt, GenWeilModel.ext, ex]
  have hcp : ∀ j : ℕ, GenWeilModel.ext i ≫ x ^ j = (GenWeilModel.ext i ≫ x) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  refine ⟨x, lv_ext_cancel i ?_, lv_ext_cancel i ?_⟩
  · rw [hcp, hx, ← lv_push_pow hp, (T.onto (n * r) hnr _).2 ⟨α, rfl⟩, push_one hp, MonObj.comp_one]
  · rw [hcp, hx, ← lv_push_pow hp, T.tower n r hn hr α, hpa]

theorem lv_down [CharZero Ω] (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V)
    (x : Over.mk ξ ⟶ t.G) (hx : x ^ (n * r) = 1) (q : Cpt ξ) (w : Module.Dual Ω V)
    (h : M.IsHTAt t.PP.L (n * r) x q w) : M.IsHTAt t.PP.L n (x ^ r) q w := by
  obtain ⟨h0, W, f, h1, h2, h3⟩ := h
  refine ⟨h0, W, f, h1, fun k _ _ i xk g c hW hxk hg hc => ?_, fun e v hev hv => ?_⟩
  · have hp := m.cart
    have hg' : g ^ (n * r) = 1 := by rw [pow_mul, hg, one_pow]
    obtain ⟨g₀, hg₀⟩ := hf k i g hg'
    have hg₁ : g = GenWeilModel.ext i ≫ g₀ := Over.OverMorphism.ext hg₀
    have hg₂ : g₀ ^ n = 1 := lv_ext_cancel i (by rw [MonObj.comp_pow, ← hg₁, hg, MonObj.comp_one])
    obtain ⟨a, ha, hpa⟩ := pull_point hp i x hx
    obtain ⟨a', ha', hpa'⟩ := pull_point hp i g₀ hg₂
    have e1 : a'.left ≫ m.φ = g.left := (congrArg (fun z => z.left) hpa').trans hg₀.symm
    have e2 : a.left ≫ m.φ = (GenWeilModel.ext i ≫ x).left := congrArg (fun z => z.left) hpa
    have e3 : (a ^ r).left ≫ m.φ = xk.left := by
      have h4 := lv_push_pow hp a r
      have h5 : pushPt hp.1.w (a ^ r) = GenWeilModel.ext i ≫ x ^ r := by
        rw [MonObj.comp_pow]
        exact h4.trans (congrArg (· ^ r) hpa)
      exact (congrArg (fun z => z.left) h5).trans hxk.symm
    refine h2 k i (GenWeilModel.ext i ≫ x) g c hW rfl hg' ?_
    rw [← _root_.GlobalTheory.CompanionTheory.Ar.WeilPull.main E H X (Sp Ω) t o.t ξ m k (spMap i) a a' _ g (n * r) c e2 e1]
    rw [← _root_.GlobalTheory.CompanionTheory.Ar.WeilPull.main E H X (Sp Ω) t o.t ξ m k (spMap i) (a ^ r) a' xk g n c e3 e1] at hc
    have hk : CharZero k := charZero_of_injective_ringHom i.injective
    have hu : IsUnit ((n * r : ℕ) : Γ((Over.mk (spMap i)).left, ⊤)) := by
      have h6 : IsUnit ((n * r : ℕ) : k) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hr).ne').isUnit
      have h7 := h6.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      rwa [map_natCast] at h7
    have h8 := ((GlobalTheory.PairingLawZeroCounterexample.laws.1 _ (GlobalTheory.Obj.toPolAV o) n (Over.mk (spMap i))).2.2.2 r a a' (unitOn c) hu ha ha').2 hc
    rw [Nat.cast_mul]
    exact h8
  · obtain ⟨u, hu, he⟩ := h3 e v hev hv
    refine ⟨r * u, mul_mem (natCast_mem _ r) hu, ?_⟩
    rw [he]
    push_cast
    ring

end obj

theorem lv_kappa {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (q : Cpt ξ)
    (hq : IsIntegrallyClosed (X.presheaf.stalk q.1)) {p : ℕ} (hp : p.Prime) {κ : Ω} (h : HT.IsCp p κ) :
    ∃ a ∈ regAt ξ q, ((p ^ 4 : ℕ) : Ω) = a * κ := by
  classical
  unfold HT.IsCp at h
  split_ifs at h with h2
  · subst h2 h
    refine ⟨4, ?_, by norm_num⟩
    simp
  · obtain ⟨ζ, hζ, rfl⟩ := h
    have hfact : Fact p.Prime := ⟨hp⟩
    have hmem : ζ ∈ primitiveRoots p Ω := (mem_primitiveRoots hp.pos).2 hζ
    have hc := congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at hc
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hc
    rw [← Finset.mul_prod_erase _ _ hmem] at hc
    refine ⟨-((p : Ω) ^ 3) * ∏ z ∈ (primitiveRoots p Ω).erase ζ, (1 - z), ?_, ?_⟩
    · apply _root_.GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk X Ω ξ q hξ hq
      refine IsIntegral.mul (IsIntegral.neg (IsIntegral.pow (isIntegral_natCast p) 3)) ?_
      refine IsIntegral.prod _ fun z hz => IsIntegral.sub isIntegral_one ?_
      exact ((mem_primitiveRoots hp.pos).1 (Finset.mem_of_mem_erase hz)).isIntegral hp.pos
    · push_cast
      rw [pow_succ, hc]
      ring

theorem levelFree : LevelFree := by
  intro hF E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 p hpS hpq hfree q hq
  have hp := 𝔐.S_prime p hpS
  haveI := Fact.mk hp
  have : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have := c.fin
    have : NumberField c.F := {}
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    infer_instance
  obtain ⟨x₀, hx₀'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open E H D l Xo c _ _ Y S Ω K J y 𝔐 hmono
  have hx₀ : 𝔐.ξ ≫ 𝔐.f = (spMap 𝔐.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hx₀']
    exact 𝔐.fn_over
  obtain ⟨s0, o, ⟨m⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at E H D l Xo c _ _ Y 𝔐.X 𝔐.f 𝔐.t 𝔐.m Ω 𝔐.ξ _ hx₀
  have hno := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω 𝔐.ξ ℤ _ _ 𝔐.tie).2 𝔐.all).1
  have hnc := (_root_.GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal _ Ω 𝔐.ξ 𝔐.tie.gen 𝔐.all).2.2 𝔐.normal
  obtain ⟨κ, hκ, hS⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree hF E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq hfree
  have hR : p ^ 𝔐.R p = p ^ 4 * p ^ (𝔐.R p - 4) := by
    rw [← pow_add, Nat.add_sub_cancel' (𝔐.R_ge p hpS)]
  have hsw := (hS q hq).2.2.1
  have hf := 𝔐.tors p hpS
  unfold HT.omP at hsw
  rw [hR] at hsw hf ⊢
  obtain ⟨a, ha, hae⟩ := lv_kappa 𝔐.tie.gen q (𝔐.normal _).2 hp hκ
  have hn : 0 < p ^ 4 := pow_pos hp.pos _
  have hr : 0 < p ^ (𝔐.R p - 4) := pow_pos hp.pos _
  generalize p ^ (𝔐.R p - 4) = r at *
  generalize p ^ 4 = n at *
  have hf' : FullTorsion 𝔐.t.G 𝔐.ξ n := fun k _ i g hg => hf k i g (by rw [pow_mul, hg, one_pow])
  have hw : ∀ N, 0 < N → FullTorsion 𝔐.t.G 𝔐.ξ N → ∃ e, GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ N e := fun N hN hfN => by
    have := _root_.GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj GlobalTheory.PairingLawZeroCounterexample.laws.1 E H D l _ _ (Sp Ω) _ s0 o 𝔐.t 𝔐.ξ m Ω (𝟙 _) N hN
      (by rwa [Category.id_comp]) (root o 𝔐.t m hfN hN hpq)
    rwa [Category.id_comp] at this
  obtain ⟨e, he⟩ := hw n hn hf'
  obtain ⟨e', he'⟩ := hw _ (Nat.mul_pos hn hr) hf
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro w ⟨z, hz, hw⟩
    obtain ⟨x, hx, rfl⟩ := lv_div o 𝔐.t m hn hr hf z hz
    obtain ⟨U, hU, w', hw'⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ (Nat.mul_pos hn hr) hf e' he'
      _ 𝔐.M q).1
    have h1 := hw' x hx q hU
    obtain ⟨u, hu, rfl⟩ := ((_root_.GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ hn hf' e he _ 𝔐.M q).2 _ _ w hz
      (lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q _ h1)).1 hw
    refine add_mem (Submodule.subset_span ⟨x, hx, h1⟩) ?_
    have h2 : n • u = (⟨a, ha⟩ : regAt 𝔐.ξ q) • κ • u := by
      rw [← Nat.cast_smul_eq_nsmul Ω, hae, mul_smul]
      rfl
    exact h2 ▸ Submodule.smul_mem _ _ (hsw u hu)
  · rintro w ⟨x, hx, hw⟩
    exact Submodule.subset_span ⟨x ^ r, by rw [← pow_mul, Nat.mul_comm, hx], lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q w hw⟩

end LevelTowerAlt.Comparison₂
end
end

