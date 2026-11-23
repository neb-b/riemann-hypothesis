module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalOfWeil
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimes
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyNormalFormDetRatioTwoTorsionTranslate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open Filter Topology
open scoped Matrix

namespace GlobalTheory.ThetaValueCont

open GlobalTheory.LocLift GlobalTheory.TangentOrigin

theorem isHolTo_spMap {V A : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing A] {B : Set V} (hB : IsOpen B)
    (ev : V → (A →+* ℂ)) (h : ∀ a, DifferentiableOn ℂ (fun b => ev b a) B) : IsHolTo B fun b => spMap (ev b) := by
  intro U f
  have key : ∀ b₀ ∈ B, ⊤ ≤ spMap (ev b₀) ⁻¹ᵁ U → (∀ᶠ b in 𝓝 b₀, b ∈ B ∧ ⊤ ≤ spMap (ev b) ⁻¹ᵁ U) ∧
      DifferentiableAt ℂ (fun b => valAt' (spMap (ev b)) U f) b₀ := by
    intro b₀ hb₀ h₀
    obtain ⟨r, a, hr, H⟩ := HolLieFrame.exists_fraction (𝟙 (Sp A)) U f (ev b₀) (by rwa [Category.comp_id])
    have d := fun a => (h a).differentiableAt (hB.mem_nhds hb₀)
    have hev : ∀ᶠ b in 𝓝 b₀, ⊤ ≤ spMap (ev b) ⁻¹ᵁ U ∧ valAt' (spMap (ev b)) U f = ev b a * (ev b r)⁻¹ := by
      filter_upwards [(d r).continuousAt.eventually_ne hr] with b hb
      obtain ⟨h₁, h₂⟩ := H ℂ (ev b) hb.isUnit
      rw [← valAt'_eq_evalPt] at h₂
      rw [Category.comp_id] at h₁ h₂
      exact ⟨h₁, (eq_mul_inv_iff_mul_eq₀ hb).2 h₂⟩
    exact ⟨(hev.mono fun b hb => hb.1).and (hB.mem_nhds hb₀) |>.mono fun b hb => ⟨hb.2, hb.1⟩,
      ((d a).mul ((d r).inv hr)).congr_of_eventuallyEq (hev.mono fun b hb => hb.2)⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun b hb => (key b hb.1 hb.2).1,
    fun b hb => (key b hb.1 hb.2).2.differentiableWithinAt⟩

theorem differentiableAt_tangent {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g m : ℕ}
    {B : Set (Fin m → ℂ)} {b₀ : Fin m → ℂ} (hB : B ∈ 𝓝 b₀) (ev : (Fin m → ℂ) → (R →+* ℂ))
    (hev : ∀ c, DifferentiableAt ℂ (fun b => ev b c) b₀) {e : ∀ b, (Fin g → ℂ) → (Over.mk (spMap (ev b)) ⟶ G)}
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : IsExp (spMap (ev b₀)) (e b₀)) (ψ : Sp (DualNumber R) ⟶ G.left) {W : (Fin m → ℂ) → Fin g → ℂ}
    (hW : ∀ b ∈ B, IsDerivAt0 (fun z => (e b z).left) (W b) (spMap (Chart.dualMapR (ev b)) ≫ ψ)) :
    DifferentiableAt ℂ W b₀ := by
  have hb₀ := mem_of_mem_nhds hB
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ (e b₀ 0).left ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (e b₀ z).left O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (e b z).left O f) 0)
      (HolLieFrame.differentiableAt_fderiv (e := fun b z => (e b z).left) hol hb₀ O f hO) ?_
    obtain ⟨F, hF, hF'⟩ := HolLieFrame.exists_hol_snd ψ ev b₀ hev O f
      ((top_le_preimage_iff _ O).2 (by rw [(hW b₀ hb₀).1]; exact hO))
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [hF', hB] with b ⟨h, e⟩ hb
    exact ((hW b hb).2 O h f).symm.trans e
  have d₁ := LocalLift.isDerivAt0_const (fun z => (e b₀ z).left) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => (e b₀ z).left) 0 fun _ _ _ => map_zero _
  let v₀ : epsPt (spMap (ev b₀)) ⟶ G :=
    Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (e b₀ 0).left)
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (e b₀ 0))))
  exact (he.2.2.2.2 v₀ d₁.1).unique d₁ d₀

theorem exists_exp_fibre (hT : ThetaUnifAV) {S : Type} [CommRing S] (y : KeyIn S) (f : S →+* ℂ) (x : KeyIn ℂ)
    (hx : KeyPB x y f) : ∃ (e : (Fin y.P.g → ℂ) → (Over.mk (spMap f) ⟶ y.P.A)) (Λ : Submodule ℤ (Fin y.P.g → ℂ))
      (EF : LinearMap.BilinForm ℤ Λ) (bs : Module.Basis (Fin y.P.g ⊕ Fin y.P.g) ℤ Λ), IsExp (spMap f) e ∧
      IsSymplecticBasis (-EF) bs ∧ Submodule.span ℝ (Λ : Set (Fin y.P.g → ℂ)) = ⊤ ∧ (∀ z, e z = 1 ↔ z ∈ Λ) ∧
      ∀ (k : ℕ) (a a₂ : Λ) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
        Out.WeilIs y.P.A y.P.L k (e ((k : ℂ)⁻¹ • (a : Fin y.P.g → ℂ))) (e ((k : ℂ)⁻¹ • (a₂ : Fin y.P.g → ℂ)))
          (unitOn c) := by
  obtain ⟨φ, -, w, hg, -, hφ, hw, -⟩ := hx
  obtain ⟨⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩, gp, rig, rg, th, tn, v, vb⟩ := y
  obtain rfl : x.P.g = g := hg
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push_iff _ x.P hφ ⟨w, hw⟩
  obtain ⟨u, Hm, χ, Ef, hAH, -, h₁, h₂, -, -, hE, hbij, hW⟩ := hT x.P x.rig x.rig_gen
  have := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have halt : Ef.IsAlt := fun l => by
    have h1 := congrArg Complex.im (SiegelNormalForm.form_conj hAH.1 (l : Fin x.P.g → ℂ) l)
    have h2 := hE l l
    simp only [Complex.star_def, Complex.conj_im] at h1
    rw [hermForm] at h2
    have : (Ef l l : ℝ) = 0 := by linarith
    exact_mod_cast this
  have hrank : Module.finrank ℤ u.Λ = 2 * x.P.g := by
    rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg (bijective_neg_bilinForm hbij) hrank
  exact ⟨fun z => Φ (u.ex z), u.Λ, Ef, bs, PointUnif.isExp_push hφ u h₁ h₂ Φ hΦ, hbs, u.full,
    fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z), fun k a a₂ c hk hc => (hΦW _ _ _ _).1 (hW k a a₂ c hk hc)⟩

theorem continuousAt_frame_constant {X : Scheme.{0}} {G : Over X} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    (rig : LB.Gen (L.pull (eSec G))) (sec : L.Sec) {g m : ℕ} {C : Set (Fin m → ℂ)} (hCo : IsOpen C) {b₀ : Fin m → ℂ}
    (hC₀ : b₀ ∈ C) {pt : (Fin m → ℂ) → (Sp ℂ ⟶ X)} (hy : IsHolTo C pt)
    {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} (e0 : e b₀ 0 = pt b₀ ≫ eSec G)
    (hol : IsHolTo (C ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2))
    {p q : Fin g → (Fin m → ℂ) → (Fin g → ℂ)} (hp : ∀ k, DifferentiableOn ℂ (p k) C)
    (hq : ∀ k, DifferentiableOn ℂ (q k) C) {h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {κ : (Fin m → ℂ) → (Fin g → ℝ) × (Fin g → ℝ)} {c : (Fin m → ℂ) → ℂ} (f₁ : (τ b₀).IsSymm)
    (f₂ : ∀ b ∈ C, ((τ b).map Complex.im).PosDef ∧
      ∀ i, h b *ᵥ p i b = Pi.single i 1 ∧ h b *ᵥ q i b = τ b *ᵥ Pi.single i 1)
    (f₃ : ∀ b ∈ C, (∀ i, (κ b).1 i = 0 ∨ (κ b).1 i = 1 / 2) ∧ ∀ i, (κ b).2 i = 0 ∨ (κ b).2 i = 1 / 2)
    (f₅ : ∀ b ∈ C, ∀ j z, ⊤ ≤ e b z ⁻¹ᵁ L.U j → ∃ ρ : (Fin g → ℂ) → ℂ, ρ z ≠ 0 ∧
      (z = 0 → ρ 0 = c b * valAt' (pt b) ((L.pull (eSec G)).U fun _ => j) (rig.s fun _ => j).val) ∧
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧
        ρ w * thetaChar (τ b) (fun i => ((κ b).1 i : ℂ)) (fun i => ((κ b).2 i : ℂ)) (h b *ᵥ w) =
          valAt' (e b w) (L.U j) (sec.f j)) : ContinuousAt c b₀ := by
  have half : ∀ {a : Fin g → ℝ}, (∀ i, a i = 0 ∨ a i = 1 / 2) → ∀ i, (a i : ℂ) = 0 ∨ (a i : ℂ) = 1 / 2 :=
    fun ha i => (ha i).imp (fun h => by simp [h]) (fun h => by simp [h])
  have fin : (Set.pi Set.univ fun _ : Fin g => ({0, 1 / 2} : Set ℝ)).Finite := Set.Finite.pi fun _ => Set.toFinite _
  have hK : {k : (Fin g → ℝ) × (Fin g → ℝ) |
      (∀ i, k.1 i = 0 ∨ k.1 i = 1 / 2) ∧ ∀ i, k.2 i = 0 ∨ k.2 i = 1 / 2}.Finite :=
    (fin.prod fin).subset fun k hk => ⟨fun i _ => hk.1 i, fun i _ => hk.2 i⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : (Fin g → ℝ) × (Fin g → ℝ) → (Fin m → ℂ) × (Fin g → ℂ) → ℂ, ∀ k, θ k = fun bz =>
    thetaChar (τ bz.1) (fun i => (k.1 i : ℂ)) (fun i => (k.2 i : ℂ)) (h bz.1 *ᵥ bz.2) := ⟨_, fun _ => rfl⟩
  have th := fun (k : (Fin g → ℝ) × (Fin g → ℝ)) (h₁ : ∀ i, k.1 i = 0 ∨ k.1 i = 1 / 2)
    (h₂ : ∀ i, k.2 i = 0 ∨ k.2 i = 1 / 2) => ThetaFamily.thetaChar_family hp hq f₂ (half h₁) (half h₂)
  refine continuousAt_constant (B := C) hK (κ := κ) (θ := θ)
    (W := fun j => {bz ∈ C ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e bz.1 bz.2 ⁻¹ᵁ L.U j})
    (f := fun j bz => valAt' (e bz.1 bz.2) (L.U j) (sec.f j))
    (r := fun j b => valAt' (pt b) ((L.pull (eSec G)).U fun _ => j) (rig.s fun _ => j).val)
    (fun j => (hol (L.U j) 0).1) (fun j w hw => hw.1.1) (fun j => (hol (L.U j) (sec.f j)).2)
    (fun k hk j => ?_) (fun k hk => ?_) f₃ (fun j b z hz => ?_) (hCo.mem_nhds hC₀) (fun z => ?_)
    (fun k hk ρ h1 h2 h3 => ?_) fun j hj => ?_
  · rw [hθ]
    exact (th k hk.1 hk.2).1.mono fun w hw => hw.1
  · rw [hθ]
    exact (th k hk.1 hk.2).2
  · rw [hθ]
    exact f₅ b hz.1.1 j z hz.2
  · obtain ⟨j, hj⟩ := exists_chart hL (e b₀ z (default : PrimeSpectrum ℂ))
    exact ⟨j, ⟨hC₀, trivial⟩, (top_le_preimage_iff_mem _ _).2 hj⟩
  · have hinv : h b₀ * Matrix.of (fun i k => p k b₀ i) = 1 := by
      ext i k
      have := congrFun ((f₂ b₀ hC₀).2 k).1 i
      rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
      rfl
    generalize Matrix.of (fun i k => p k b₀ i) = N at hinv
    have dl : Differentiable ℂ (fun w : Fin g → ℂ => N *ᵥ w) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin N)).differentiable
    obtain ⟨e₁, e₂⟩ := ThetaPoint.half_char_unique f₁ (f₂ b₀ hC₀).1 (f₃ b₀ hC₀).1 (f₃ b₀ hC₀).2 hk.1 hk.2
      (h1.comp dl) (fun z => h2 _) fun z => by
        have := h3 (N *ᵥ z)
        simp only [hθ, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, CanTh.thetaChar_eq_theta] at this
        exact this.symm
    exact Prod.ext e₁ e₂
  · have h0 : ⊤ ≤ pt b₀ ⁻¹ᵁ (L.pull (eSec G)).U fun _ => j := by
      have : ⊤ ≤ e b₀ 0 ⁻¹ᵁ L.U j := hj.2
      rw [e0] at this
      exact fun p hp => mem_pull.2 (this hp)
    exact ⟨(LocalLift.hol_differentiableAt hy hC₀ h0 _).continuousAt, valAt'_unit_ne_zero _ h0 _⟩

theorem continuousOn_value : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (y : KeyIn S) (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)) (t : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → (∀ p ∈ B, ∃ x : KeyIn ℂ, KeyPB x y (s p).toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t p = M.det ^ 4 / c ^ 8)) → ContinuousOn t B := by
  intro hL hT hI S _ _ _ y m B s t hB hs ht b₀ hb₀
  choose x hx hv using ht
  let ev : (Fin m → ℂ) → (S →+* ℂ) := fun b => (s b).toRingHom
  let pt : (Fin m → ℂ) → (Sp ℂ ⟶ Sp S) := fun b => spMap (ev b)
  have hy : IsHolTo B pt := isHolTo_spMap hB ev hs
  obtain ⟨e₀, Λ, EF, bs, he₀, hbs, hfull, k₀, w₀⟩ := exists_exp_fibre hT y _ _ (hx b₀ hb₀)
  have hft : LocallyOfFiniteType (spMap (algebraMap ℂ S)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  have := y.P.isAb.proper
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, rfl, hr, hol, he, hl⟩ := RelExp.exists_relative_exp ℂ (RingHom.id ℂ) (Sp S)
    (spMap (algebraMap ℂ S)) y.P.A y.P.g m B pt b₀ e₀ hft y.P.isAb y.P.smoothDim hB hb₀ (fun b _ => by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun a => (s b).commutes a) hy he₀
  change HasLifts B₁ pt e at hl
  change ∀ b ∈ B₁, IsExp (pt b) (e b) ∧ _ at he
  have := Module.Free.of_basis bs
  have := Module.Finite.of_basis bs
  obtain ⟨P, hP₀, hP⟩ := exists_periods latContinuation hB₁ hb₁ (isHolTo_mono hy hB₁ hB₁B) hr hol he hl
    Λ.subtype.toAddMonoidHom Subtype.val_injective
    (by rw [← hfull]; congr 1; exact Subtype.range_val) (fun z => (k₀ z).trans
      ⟨fun h => ⟨⟨z, h⟩, rfl⟩, fun ⟨l, h⟩ => h ▸ l.2⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hCn := hCo.mem_nhds hC₀
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hCB : C ⊆ B := hC₁.trans hB₁B
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb => ((hball b hb).1.1 x).differentiableWithinAt
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'),
      hk1 b hb]
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs y.P.A y.P.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (torsion_eq_and_weilIs_of_isHolTo hL (Sp S) y.P m k C pt
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk
      (isUnit_natCast_of_over (spMap (algebraMap ℂ S)) hk) hCo hCc hC₀ (htor k a) (htor k a₂)
      fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2 (by rw [hP₀]; exact w₀ k a a₂ c hk hc) b hb
  have fib := fun b (hb : b ∈ C) => exists_normal_fibre hT hL.mulN y (ev b) _ (hx b (hCB hb)) (e b)
    (he b (hC₁ hb)).1.1 (he b (hC₁ hb)).1.2.1 (he b (hC₁ hb)).1.2.2.1 EF bs hbs (P b) (hball b hb).1.2.1 (hwe b hb)
  choose! h τ κ c W f₁ f₂ f₃ f₄ f₅ f₆ f₇ using fib
  have ht : ∀ b ∈ C, t b = (Matrix.of fun i => (2 * Real.pi * Complex.I : ℂ) • h b *ᵥ W b i).det ^ 4 / c b ^ 8 :=
    fun b hb => _root_.GlobalTheory.NormalUnique.thetaFrame_value_unique hT hI _ _ _ (hv b (hCB hb)) (f₇ b hb)
  have hinv : ∀ b ∈ C, h b * Matrix.of (fun i k => P b (bs (.inl k)) i) = 1 := fun b hb => by
    ext i k
    have := congrFun ((f₂ b hb).2 k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  have dh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) C :=
    ThetaFamily.differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hPd _) i) hinv
  have holC := isHolTo_mono hol (hCo.prod isOpen_univ) (Set.prod_mono hC₁ le_rfl)
  have cc : ContinuousAt c b₀ := continuousAt_frame_constant y.P.isLB y.rig y.th hCo hC₀ (isHolTo_mono hy hCo hCB)
    (e := fun b z => (e b z).left) ((congrArg (·.left) (hom_zero (he b₀ hb₁).1.1)).trans (one_left _)) holC
    (p := fun k b => P b (bs (.inl k))) (q := fun k b => P b (bs (.inr k))) (fun k => hPd _) (fun k => hPd _)
    (f₁ b₀ hC₀) f₂ f₃ f₅
  have cW : ∀ i, ContinuousAt (fun b => W b i) b₀ := fun i =>
    (differentiableAt_tangent hCn ev (fun a => (hs a).differentiableAt (hB.mem_nhds hb₀)) holC (he b₀ hb₁).1
      (y.v i).left fun b hb => f₆ b hb i).continuousAt
  have cM : ContinuousAt (fun b => Matrix.of fun i => (2 * Real.pi * Complex.I : ℂ) • h b *ᵥ W b i) b₀ := by
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact continuousAt_const.mul (tendsto_finsetSum _ fun l _ =>
      ((dh j l).differentiableAt hCn).continuousAt.mul (continuousAt_pi.1 (cW i) l))
  refine ContinuousAt.continuousWithinAt (ContinuousAt.congr ?_ (Filter.eventuallyEq_of_mem hCn ht).symm)
  exact ((continuous_id.matrix_det.continuousAt.comp cM).pow 4).div (cc.pow 8) (pow_ne_zero _ (f₄ b₀ hC₀))

end GlobalTheory.ThetaValueCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_symmetric_linearised_bundle : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over S) ⟶ A)) (L : LB A.left), L.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ c, i c ≫ ψ = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), (∀ x : Over.mk t ⟶ A, x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∀ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])) (j : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, -1])), ((∀ c, (u c).IsGen) ∧ (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) ∧ j.IsGen ∧ ∀ c (T : Over S) (x : T ⟶ A) (z : T.left) (J), Good L z J → val (u c) x.left z J * val j ((toUnit T ≫ i c) * x).left z J = val j x.left z J * val (u c⁻¹) (x⁻¹).left z J) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) ∧ LBIso M (M.pull (GrpObj.inv : B ⟶ B).left) := by
  first | exact @GlobalTheory.LinDescent.exists_descent_symmetric | exact GlobalTheory.LinDescent.exists_descent_symmetric | (intros; apply GlobalTheory.LinDescent.exists_descent_symmetric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ellipticKeyData_value_eq_discriminant : ThetaUnifAV → ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic], ∃ x : KeyIn R, x.P.g = 1 ∧ ∀ (s : R →+* ℂ) (x' : KeyIn ℂ) (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), KeyPB x' x s → charHalf x'.P.g a b → c ≠ 0 → NormalAt x' τ M a b c → M.det ^ 4 / c ^ 8 = s W.Δ := by
  first | exact @GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant | exact GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant | (intros; apply GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataNearTwoPrimes
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_keyIn_polPB {R R₁ R' : Type} [CommRing R] [CommRing R₁] [CommRing R'] (Q : Out.PolAV (Sp R))
    (hg : 1 ≤ Q.g) (f₁ : R →+* R₁) (g : R₁ →+* R') (f : R →+* R') (hf : g.comp f₁ = f) (th : Q.L.Sec)
    (hth : ∀ s : Sp R', ∃ x : Q.A.left, Q.A.hom x = spMap f s ∧ x ∈ Out.nonzeroLocus th)
    (v : Fin Q.g → (epsR R₁ ⟶ (Over.pullback (spMap f₁)).obj Q.A)) (hv : IsLieBasis v) :
    ∃ (y : KeyIn R') (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap f) φ := by
  have h := isGrpPullback_pullback Q.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj Q.A).left ⟶ Q.A.left := pullback.fst Q.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := LB.isLB_pull Q.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj Q.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) Q.A Q.isAb
      g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := Q.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h Q.rigid
      sym := PolBaseChange.sym_pull h Q.sym
      ample := relAmple_pull h.1 Q.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample
      ktriv := kTriv_pull h Q.isLB hL' hw Q.ktriv }
  obtain ⟨rig, hr⟩ := P'.rigid
  obtain ⟨th', hth'⟩ := sec_pull_down hw Q.isLB hL' th
  have h₁ := isGrpPullback_pullback Q.A (spMap f₁)
  have hA₁ := Out.TLinPf.isAb_pullback (spMap f₁) Q.A Q.isAb
  have c₁ := hA₁.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  have e : spMap g ≫ spMap f₁ = spMap f := by
    rw [← hf, ← Spec.map_comp]; rfl
  have w : φ ≫ Q.A.hom = P'.A.hom ≫ spMap g ≫ spMap f₁ := by rw [e]; exact h.1.w
  have w₁ : φ ≫ Q.A.hom = (P'.A.hom ≫ spMap g) ≫ spMap f₁ := by rw [Category.assoc]; exact w
  have h₂ : IsGrpPullback P'.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (h.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange R₁ R' g _ P'.A _ h₂ hA₁.smooth Q.g v hv
  refine ⟨⟨P', hg, rig, hr, th', fun s => ?_, v', hb'⟩, φ, h, rfl, ⟨idIso _, idIso_isGen hL'⟩⟩
  obtain ⟨z, hz, hz'⟩ := hth s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem exists_keyIn_near_two : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), 1 ≤ Q.g → ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ (y : KeyIn (Localization.Away r)) (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap (algebraMap R (Localization.Away r))) φ := by
  intro hL hL₂ R _ _ Q p q hg
  obtain ⟨th, a, ap, aq, ha⟩ := _root_.GlobalTheory.TwoPrimeSection.main hL hL₂ R Q p q
  have c : IsCommMonObj Q.A := Q.isAb.comm
  obtain ⟨b, bp, bq, v, hv⟩ := _root_.GlobalTheory.LieTwo.lie_free_near_two_primes R Q.A Q.g Q.smoothDim p q
  refine ⟨b * a, fun h => (p.isPrime.mem_or_mem h).elim bp ap, fun h => (q.isPrime.mem_or_mem h).elim bq aq, ?_⟩
  refine exists_keyIn_polPB Q hg (algebraMap R (Localization.Away b))
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away b) (P := Localization.Away (b * a)) b a) _
    (RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away b) b a x) th
    (fun s => ha _ fun h => ?_) v hv
  have h' : algebraMap R (Localization.Away (b * a)) a ∈ s.asIdeal := h
  have u : IsUnit (algebraMap R (Localization.Away (b * a)) (b * a)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at u
  exact s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (isUnit_of_mul_isUnit_right u))

end GlobalTheory.KeyFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyDatumKnownValueRat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem Val.pow {x y : KeyIn ℂ} {j : ℕ} {t : ℂ} (hp : IsKeyPow y x j) (h : Val x t) : Val y (t ^ j) := by
  obtain ⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hN, rfl⟩ := h
  have ea : a = fun k => (((a k).re : ℝ) : ℂ) := by
    funext k
    rcases ha k with h | h <;> rw [h] <;> norm_num
  have eb : b = fun k => (((b k).re : ℝ) : ℂ) := by
    funext k
    rcases hb k with h | h <;> rw [h] <;> norm_num
  rw [ea, eb] at hN
  obtain ⟨e, τ', M', hdet, hN'⟩ := normalAt_pow x y j τ M _ _ c hp hN
  refine ⟨τ', M', _, _, c ^ j, ⟨fun p => ?_, fun p => ?_⟩, pow_ne_zero _ hc, hN', ?_⟩
  · rw [← congrFun ea]; exact ha _
  · rw [← congrFun eb]; exact hb _
  · rw [hdet, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm 4, Nat.mul_comm 8]

theorem isElliptic_cube_sub : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic := by
  refine ⟨Ne.isUnit ?_⟩
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem exists_known_rat : Out.Laws → ThetaUnifAV → ∀ g : ℕ, 1 ≤ g → ∃ y : KeyIn ℚ, y.P.g = g ∧ Known ℚ y := by
  intro _ hU g hg
  have := isElliptic_cube_sub
  obtain ⟨y₁, h₁, hval⟩ := EllipticKey.exists_keyIn_value_eq_discriminant hU ℚ ⟨0, 0, 0, -1, 0⟩
  obtain ⟨y, hy⟩ := exists_isKeyPow ℚ y₁ g hg
  refine ⟨y, ?_, (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ ^ g, fun e x hx => ?_⟩
  · obtain ⟨-, h, -⟩ := hy
    rw [← h, h₁, Nat.mul_one]
  · obtain ⟨x₁, hx₁⟩ := exists_keyPB_ring y₁ e
    obtain ⟨⟨τ, M, a, b, c, hab, hc, -, hN⟩, -⟩ := KeyNormalExists.exists_normalAt hU x₁
    have hv₁ : Val x₁ (e (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ) :=
      ⟨τ, M, a, b, c, hab, hc, hN, (hval e x₁ τ M a b c hx₁ hab hc hN).symm⟩
    obtain ⟨x', hx'⟩ := exists_isKeyPow ℂ x₁ g hg
    have hpb := keyPB_of_isKeyPow ℚ ℂ e y₁ y x₁ x' g hx₁ hy hx'
    have hid : KeyPB x x' (RingHom.id ℂ) := KeyCancel.keyPB_cancel ℚ ℂ ℂ y x' x e (RingHom.id ℂ) hpb hx
    rw [map_pow]
    exact ((_root_.GlobalTheory.KeyIsoNormal.val_iff_and_nrm_iff x' x hid).1 _).1 (hv₁.pow hx')

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOfKeyFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamOfExact

theorem keyFam_of_keyFormula : KeyFormula → KeyFam fun _ => 1 := fun h => by
  obtain ⟨κ, h1, h2, h3, h4, h5⟩ := keyFormula_iff.1 h
  exact ⟨κ, h1, h2, h3, h4, h5, GlobalTheory.KeyFamUnit.famUnit κ h2 h3,
    GlobalTheory.KeyFamHomog.famHomog_of_homog _ κ h1, _root_.GlobalTheory.KeyValUnit.valUnit κ h2 h3⟩

end GlobalTheory.KeyFamOfExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyNormalFormDetRatioTwoTorsionTranslateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyNormalFormDetRatio_twoTorsion_translate : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (p : 𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) (ν : ℂˣ) (t : ℂ), IsTrl x' x p ν → Val x t → Val x' (t * (ν : ℂ) ^ 2) := by
  first | exact @GlobalTheory.KeyEq.val_of_isTrl | exact GlobalTheory.KeyEq.val_of_isTrl | (intros; apply GlobalTheory.KeyEq.val_of_isTrl <;> assumption)
end

