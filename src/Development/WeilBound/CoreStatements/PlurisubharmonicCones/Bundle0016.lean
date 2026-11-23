module

public import Mathlib
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PhiTransport
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TorusExpEqOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0244
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGlueOverPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TorusModelCochar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalHermitianFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHeightBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0211
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0216
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesOfFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.CentreIdent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {t : SAB H (Sp R)}
  {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem centre_ident (e : FamExp t.G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (P : AbPart t (spMap (ψ b)))
    (hP : IsPrincipal P.tB) (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left))
    {V : Type} [AddCommGroup V] [Module ℂ V] (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρ : 𝓞 E →+* Module.End ℂ V) (I : AddSubgroup V) (hf : V → V → ℂ) (hact : MV.IsActOf P.tK.act.act ρ)
    (hI : P.IsCochars MV I)
    (hh : ∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hf x x'))
    (Bb : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hB : ∀ c x, e.ex b (Bb c x) = e.ex b x ≫ t.act.act c)
    (Hb : Matrix (Fin g) (Fin g) ℂ) (hH : Hb.IsHermitian)
    (hW : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, ∃ k : ℤ, (y ⬝ᵥ Hb *ᵥ star y').im = k ∧ ∀ (N : ℕ) (ζ : ℂˣ), 0 < N →
      (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (k : ℂ) / N) →
      CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ))
    (I' : Set (Fin g → ℂ)) (hI' : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ∀ y ∈ e.per b, (p ⬝ᵥ Hb *ᵥ star y).im = 0)
    (hrad : ∀ p ∈ I', Hb *ᵥ star p = 0) :
    ∃ Φ : V ≃ₗ[ℂ] (Fin g → ℂ), (∀ x, (Mz.pt (Φ x)).left = (MV.pt x).left ≫ P.m.φ) ∧
      (∀ a x, Bb a (Φ x) = Φ (ρ a x)) ∧ (∀ x x', hf x x' = Real.pi * (Φ x' ⬝ᵥ Hb *ᵥ star (Φ x))) ∧
      ∀ p, p ∈ I' ↔ ∃ x ∈ I, p = (2 * Real.pi * Complex.I : ℂ) • Φ x := by
  letI := P.τ.addCommGroup
  obtain ⟨Φ, hΦ⟩ := lie_equiv P.m.cart MV Mz
  obtain ⟨d, β, h, t1, t2, t3⟩ := torus_lift e hb P Mz hL
  have key : ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g')
      (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)),
      IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsAbLift e b P φ u ℓ →
      (∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0) ∧ ∀ p q, ℓ p ⬝ᵥ Hm *ᵥ star (ℓ q) = p ⬝ᵥ Hb *ᵥ star q := by
    intro A iA φ g' u Hm χ ℓ hφ hAH hℓ
    obtain ⟨hin, honto⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ
    obtain ⟨H', hH1, hH2, hH3⟩ := exists_pull_form ℓ Hm hAH.1
    have hE : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, (y ⬝ᵥ Hb *ᵥ star y').im = (ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im := by
      intro y hy y' hy'
      obtain ⟨k, hk, hc⟩ := hW y hy y' hy'
      rw [hk]
      refine eq_of_forall_exp fun N hN => ?_
      have := _root_.GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ N _ y y' hN hy hy'
        (hc N (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (k : ℂ) / N))) hN rfl)
      rw [Units.val_mk0] at this
      have c : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; rfl
      rw [c]
      exact this
    have k1 : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0 := fun p => by
      rw [hI']
      refine and_congr_right fun hp => ⟨fun h0 => ?_, fun h0 y hy => ?_⟩
      · refine eq_zero_of_im_lattice Hm u.Λ u.full hAH.2.1 _ fun q hq => ?_
        obtain ⟨y, hy, rfl⟩ := honto q hq
        rw [← hE p hp y hy, h0 y hy]
      · rw [hE p hp y hy, h0]
        simp
    refine ⟨k1, fun p q => ?_⟩
    rw [← hH2]
    congr 2
    refine herm_unique H' Hb hH1 hH (e.per b) {y | ℓ y = 0} (fun x hx y hy => by rw [hH2, hE x hx y hy]) hH3
      (fun y hy => ?_) (fun p => ?_)
    · obtain ⟨z, rfl⟩ := (t3 A φ g' u ℓ hφ hℓ y).1 hy
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      have e1 : z = ∑ a, (z a / (2 * Real.pi * Complex.I)) • (Pi.single a (2 * Real.pi * Complex.I) : Fin d → ℂ) := by
        ext c
        simp [Finset.sum_apply, Pi.single_apply, h2]
      have e2 : ∀ a, Hb *ᵥ star (h (Pi.single a (2 * Real.pi * Complex.I))) = 0 := fun a => by
        refine hrad _ ((k1 _).2 ⟨(t2 _).2 ⟨(β.coord a).toAddMonoidHom, funext fun c => ?_⟩,
          (t3 A φ g' u ℓ hφ hℓ _).2 ⟨_, rfl⟩⟩)
        by_cases hc : c = a
        · subst hc; simp
        · simp [hc, Finsupp.single_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, map_sum, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [map_smul, star_smul, Matrix.mulVec_smul, e2, smul_zero]
    · have hp : ℓ p ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)) := by rw [u.full]; trivial
      have : ∀ w ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)), ∃ r ∈ Submodule.span ℝ (e.per b), ℓ r = w := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨y, hy, rfl⟩ := honto x hx
          exact ⟨y, Submodule.subset_span hy, rfl⟩
        | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
        | add x y _ _ hx hy =>
          obtain ⟨r, hr, rfl⟩ := hx
          obtain ⟨r', hr', rfl⟩ := hy
          exact ⟨r + r', Submodule.add_mem _ hr hr', map_add _ _ _⟩
        | smul c x _ hx =>
          obtain ⟨r, hr, rfl⟩ := hx
          exact ⟨c • r, Submodule.smul_mem _ _ hr, ℓ.map_smul_of_tower c r⟩
      obtain ⟨r, hr, hrp⟩ := this _ hp
      exact ⟨r, hr, by show ℓ (p - r) = 0; rw [map_sub, hrp, sub_self]⟩
  refine ⟨Φ, hΦ, fun a x => ?_, fun x x' => ?_, fun p => ?_⟩
  · have d1 := GlobalTheory.FibreDeriv.isDerivAt0_comp (DiffL.isDerivAt0_pt e hb Mz hL (Φ x)) (t.act.act a).left
    have d2 := PerGram.isDerivAt0_comp_linMap (PerSpan.isHolTo_ex_slice e hb) (Bb a)
      (DiffL.isDerivAt0_pt e hb Mz hL (Bb a (Φ x)))
    have e1 : (fun z => (e.ex b (Bb a z)).left) = fun z => (e.ex b z).left ≫ (t.act.act a).left :=
      funext fun z => by rw [hB, Over.comp_left]
    rw [e1] at d2
    refine Mz.inj (Over.OverMorphism.ext ?_)
    rw [GlobalTheory.VerticalDeriv.isDerivAt0_unique d2 d1, hΦ, hΦ, hact a x, Over.comp_left, Category.assoc, Category.assoc,
      P.m.act]
  · obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, hv', hw', ha', hb', hc⟩ := hh x x'
    obtain ⟨ℓ, hℓ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
    have e1 : a' = ℓ (Φ x) := DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _
      v' a' (hΦ x).symm hv' ha'
    have e2 : b' = ℓ (Φ x') := DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _
      w' b' (hΦ x').symm hw' hb'
    rw [hc, e1, e2, ← (key A φ g' u Hm χ ℓ hφ hAH hℓ).2]
  · obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, -⟩ := hh 0 0
    obtain ⟨ℓ, hℓ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
    obtain ⟨MT, hMT, hI⟩ := hI
    have k2 : ∀ x (δ : P.τ.X →+ ℤ), MV.pt x = MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i ↔
        Φ x = h fun a => (δ (β a) : ℂ) := fun x δ => by
      have a1 := t1 MT hMT ((Int.castAddHom ℂ).comp δ)
      constructor
      · intro hx
        refine Mz.inj (Over.OverMorphism.ext ?_)
        rw [hΦ, hx]
        exact a1.symm
      · intro hx
        refine Over.OverMorphism.ext (P.m.cart.1.hom_ext ?_ ?_)
        · rw [← hΦ, hx]
          exact a1
        · rw [Over.w (MV.pt x), Over.w (MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i)]
    have k3 : ∀ δ : P.τ.X →+ ℤ, h (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) =
        (2 * Real.pi * Complex.I : ℂ) • h fun a => (δ (β a) : ℂ) := fun δ => by
      rw [← map_smul]
      rfl
    rw [(key A φ g' u Hm χ ℓ hφ hAH hℓ).1, t3 A φ g' u ℓ hφ hℓ]
    constructor
    · rintro ⟨hp, z, rfl⟩
      obtain ⟨δ, rfl⟩ := (t2 z).1 hp
      refine ⟨Φ.symm (h fun a => (δ (β a) : ℂ)), (hI _).2 ⟨δ, (k2 _ δ).2 (Φ.apply_symm_apply _)⟩, ?_⟩
      rw [Φ.apply_symm_apply, k3]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨δ, hδ⟩ := (hI x).1 hx
      rw [(k2 x δ).1 hδ, ← k3]
      exact ⟨(t2 _).2 ⟨δ, rfl⟩, _, rfl⟩

theorem per_small (e : FamExp t.G M B ψ) {b₀ : Fin n → ℂ} (hb : b₀ ∈ B) (hB : B ∈ 𝓝 b₀) :
    ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.2 ∈ e.per bz.1 → bz.2 = 0 := by
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b₀ hb
  have hB' : ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.1 ∈ B :=
    (continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually_mem hB
  have hc : Continuous fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (bz.1, (0 : Fin g → ℂ)) := by fun_prop
  have hL0 := (hc.tendsto (b₀, 0)).eventually hL
  filter_upwards [hL, hL0, hB'] with bz h1 h2 h3 hper
  have h0 : e.ex bz.1 0 = 1 := by
    have h4 := e.add bz.1 h3 0 0
    rw [add_zero] at h4
    simpa using h4.symm
  have hx : e.ex bz.1 bz.2 = e.ex bz.1 0 := by
    rw [h0]
    exact hper
  rw [← h1, hx]
  exact h2

end LevelTowerAlt.Val
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ComponentDataHeightIdentity
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

theorem component_data_height_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ), (∀ p ∈ S₀ ∪ Dc.SB B, p.Prime) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, 4 ≤ Or.𝔐.R p) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, FullTorsion Or.𝔐.t.G Or.𝔐.ξ (p ^ Or.𝔐.R p)) ∧ ∀ s, (Or.𝔐.VS (S₀ ∪ Dc.SB B) s).IsVB (labelRk D s) (Or.𝔐.Vgen s) := by
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B
  have hS : ∀ p ∈ Dc.SB B, p ∈ Dc.S := fun p hp => (Finset.mem_filter.1 hp).1
  have hpr : ∀ p ∈ S₀ ∪ Dc.SB B, p.Prime := fun p hp => (Finset.mem_union.1 hp).elim (Or.𝔐.S_prime p)
    fun h => Dc.S_prime p (hS p h)
  refine ⟨hpr, fun p hp => (Finset.mem_union.1 hp).elim (Or.𝔐.R_ge p) fun h => Or.R_ge p (hS p h),
    fun p hp => (Finset.mem_union.1 hp).elim (Or.𝔐.tors p) fun h => Or.tors p (hS p h), fun s => ?_⟩
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : IsLocallyNoetherian Or.𝔐.X :=
    GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.isLocallyNoetherian_of_coordTie Or.𝔐.ξ _ Or.𝔐.tie Or.𝔐.all
  have hvb : (Or.𝔐.V s).IsVB (labelRk D s) (Or.𝔐.Vgen s) := Or.𝔐.vb s
  obtain ⟨L, hL, h0, h1⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lat_glue Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (Dc.SB B) (Or.𝔐.V s) (fun p => Or.𝔐.HT p s)
    (labelRk D s) (Or.𝔐.Vgen s) Or.𝔐.tie.gen (fun p hp => Dc.S_prime p (hS p hp))
    (fun q _ => by
      obtain ⟨U, hU, b, hb, hf⟩ := hvb q trivial
      exact ⟨U, hU, b, hb, fun q' _ h => hf q' trivial h⟩)
    (fun p hp => Or.ht_vb p (hS p hp) s)
    (fun p hp q hq => by
      obtain ⟨e1, e2, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l (Xo l) c _ _ Y S₀ Ω K J Dc.y Or.𝔐
        (FaithfulSMul.algebraMap_injective _ _) q hq
      rw [e1 s]; exact e2 p (Dc.S_prime p (hS p hp)) s)
  have e : Or.𝔐.VS (S₀ ∪ Dc.SB B) s = L := by
    funext q
    have P := _root_.GlobalTheory.CompanionTheory.Ar.Lat.patch_values Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (S₀ ∪ Dc.SB B) (Or.𝔐.dR s) (fun p => Or.𝔐.HT p s) q hpr
    have P₀ := _root_.GlobalTheory.CompanionTheory.Ar.Lat.patch_values Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li S₀ (Or.𝔐.dR s) (fun p => Or.𝔐.HT p s) q Or.𝔐.S_prime
    by_cases h : ∃ p ∈ Dc.SB B, InFibre Or.𝔐.ξ p q
    · obtain ⟨p, hp, hq⟩ := h
      rw [h1 p hp q hq]
      exact P.2 p (Finset.mem_union_right _ hp) hq
    · push Not at h
      rw [h0 q h]
      by_cases h' : ∃ p ∈ S₀, InFibre Or.𝔐.ξ p q
      · obtain ⟨p, hp, hq⟩ := h'
        exact (P.2 p (Finset.mem_union_left _ hp) hq).trans (P₀.2 p hp hq).symm
      · push Not at h'
        exact (P.1 fun p hp => (Finset.mem_union.1 hp).elim (h' p) (h p)).trans (P₀.1 h').symm
  rw [e]; exact hL

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.IntegralPointExtendsCompact
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt

theorem integral_point_extends_compact : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L₀ : Type) [Field L₀] [NumberField L₀], 1 ≤ D.p + D.q → ∀ w ∈ Small.ptsOver L₀ (mCoordIdeal y), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L) (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V) (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) ∧ 𝔐.IsLinPtOf z P MV A ∧ (∀ s, Module.finrank L (eigSp A.ρ (A.σ s)) = labelRk D s) ∧ Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L₀ _ _ hpq w hw
  classical
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨h⟩ := _root_.GlobalTheory.CompanionTheory.Ar.MetricAny.exists_lieMetric 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.Li 𝔐.M
  obtain ⟨K₀, -, hQ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotUnif.main hG.2.2.2.2.1 E H D l Xo c Y S Ω K J y 𝔐 h hpq
  obtain ⟨z₀, hz₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.algebraicPoint_extends_to_integers 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie L₀ w hw
  obtain ⟨L₁, _, _, e₁, ⟨P₁⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.abPart_exists E H 𝔐.X 𝔐.t L₀ (spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀)
  obtain ⟨σ₁⟩ : Nonempty (L₁ →+* ℂ) := inferInstance
  obtain ⟨P₁c, _, mBc, _, _⟩ := _root_.GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange E H 𝔐.X 𝔐.t L₁ ℂ _ P₁ σ₁
  have hpr : IsPrincipal P₁.tB := (_root_.GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field E H L₁ ℂ σ₁ P₁.tB P₁c.tB mBc).1 (hQ _ P₁c).1
  obtain ⟨L, _, _, e₂, t', tK, ⟨m₁⟩, ⟨mP⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SabModel.exists_sab_model hG.1.2.1 hG.1.1 E H L₁ P₁.tB hpr
    (_root_.GlobalTheory.CompanionTheory.Ar.AbPartConst.lieMult_constant_along_cmType E H D l Xo c Y S Ω K J y 𝔐 L₁ _ P₁)
  let z : Sp (𝓞 L) ⟶ 𝔐.X := spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀
  have hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ (spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀) := by
    have e : spMap (algebraMap (𝓞 L) L) ≫ spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) =
        spMap e₂ ≫ spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    simp only [z]
    rw [← Category.assoc, e]
    simp only [Category.assoc]
  have hco : CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => (e₂.comp e₁) (w p)) := by
    rw [hz]
    exact RootHt.PullCoords.coordsAt_field e₂ (RootHt.PullCoords.coordsAt_field e₁ hz₀)
  obtain ⟨P, hP, ⟨m'⟩⟩ : ∃ P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z), IsPrincipal P.tB ∧
      Nonempty (SABMap P.tB t' (spMap (algebraMap (𝓞 L) L))) := by
    rw [hz]
    obtain ⟨P₂, -, mB2, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange E H 𝔐.X 𝔐.t L₁ L _ P₁ e₂
    refine ⟨P₂, (_root_.GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field E H L₁ L e₂ P₁.tB P₂.tB mB2).2 hpr, ?_⟩
    obtain ⟨n⟩ : Nonempty (SABMap P₂.tB P₁.tB (𝟙 _ ≫ spMap e₂)) := by
      rw [Category.id_comp]
      exact ⟨mB2⟩
    obtain ⟨n', -⟩ := sabCancel pullCubCancel E H _ _ _ P₁.tB tK P₂.tB _ _ mP n
    obtain ⟨n'', -⟩ := sabComp pullCubComp E H _ _ _ t' tK P₂.tB _ _ m₁ n'
    rw [← Category.id_comp (spMap (algebraMap (𝓞 L) L))]
    exact ⟨n''⟩
  obtain ⟨B, MB, hB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeFibre.exists_hermitianBundle E H L t' P.tB m' hP
  obtain ⟨σ, hlab, -, hbij, hinj, hcard, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal E H D l Xo c Y S Ω K J y 𝔐 L
    (spMap (algebraMap (𝓞 L) L) ≫ z)
  obtain ⟨V, _, _, _, _, MV, A, rfl, hact, hΛ, hI, ⟨MB', hB', hf⟩, hrk⟩ :=
    Lin.exists_lin 𝔐.t z P t' m' hP B MB hB σ hbij hinj
  obtain ⟨hV, -, hlat⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐
    (FaithfulSMul.algebraMap_injective _ _) ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩
    (fun r hr => PtHt.FrameVal.not_inFibre _ _ r hr)
  have hb : ∀ s, ∃ sL : Fin (labelRk D s) → V, LinearIndependent L sL ∧
      Submodule.span L (Set.range sL) = eigSp A.ρ (A.σ s) := fun s => by
    obtain ⟨U, hU, b, -, hfr⟩ := 𝔐.vb s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ trivial
    have h1 : (𝔐.V s).IsFrameAt b ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ := hfr _ trivial hU
    obtain ⟨sL, -, h2⟩ := PtHt.FrameVal.values_core 𝔐 _ P.tK P.m MV A.ρ A.σ A.σ_bij.1 hact hlab hlat s b
      ⟨h1.1, (hV s).symm.trans h1.2⟩
    exact ⟨sL, h2⟩
  choose sL hli hsp using hb
  refine ⟨L, inferInstance, inferInstance, e₂.comp e₁, z, P, V, inferInstance, inferInstance, inferInstance,
    inferInstance, MV, A, hco, ⟨hact, hlab, hΛ, hI, hP, t', m', MB', hB', hf⟩, fun s => ?_, hrk.trans ?_⟩
  · rw [← hsp s, finrank_span_eq_card (hli s), Fintype.card_fin]
  · have htop := iSup_eigSp_eq_top A.ρ A.σ A.σ_bij.1 (by rw [Fintype.card_sum, ← hcard]; ring)
    have hs : Submodule.span L (Set.range fun p : (Σ s, Fin (labelRk D s)) => sL p.1 p.2) = ⊤ := by
      rw [eq_top_iff, ← htop]
      refine iSup_le fun s => ?_
      rw [← hsp s]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨⟨s, i⟩, rfl⟩)
    refine (finrank_le_of_span_eq_top hs).trans ?_
    simp [Fintype.card_sigma, Fintype.sum_sum_type, mul_add]

end LevelTowerAlt
end
end

