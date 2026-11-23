module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanMarkedFormUniqueInCell
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExistsMarkedFormInCell
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionLinearOnCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.EqOfOrbitMarkInCellCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell

theorem eq_of_orbMark_of_inRCone_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), IsTwG w0 φ → IsTwG w0 lab →
  SimpLab bar q φ lab →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        (OrbMark.orbFun O w0 v).evalZ β = 1 → (OrbMark.orbFun O w0 v).evalZ β' = 1 →
        InRCone γ β → InRCone γ β' → β = β' := by
  intro O _ _ _ _ bar w0 hb q φ lab hφ hlab hS X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt X _ _ _ _ hX m γ hγ β hβ hβn β' hβ' hβ'n
    hm hm' hin hin'
  obtain ⟨m', δ, hδ, hδli, hδinj, hγδ⟩ := hS.2 X hX m γ hγ
  have hcδ : ∀ j, InRCone δ (γ j) := hγδ
  obtain ⟨c, hc, hβc⟩ := inRCone_trans hcδ hin
  obtain ⟨c', hc', hβc'⟩ := inRCone_trans hcδ hin'
  obtain ⟨p, hp, hpi, hpc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces.exists_pieces_match O bar w0 hb φ hφ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt β hm
  obtain ⟨p', hp', hpi', hpc'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces.exists_pieces_match O bar w0 hb φ hφ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt β' hm'
  have hlabray : ∀ (x : LinearMap.BilinForm ℤ X) (j : Fin m') (d : ℝ), 0 < d → x ∈ balForms bar X →
      (∀ y, 0 ≤ x y y) → toReal x = d • toReal (δ j) → lab.evalZ x = lab.evalZ (δ j) := by
    intro x j d hd hxb hxn hx
    obtain ⟨a, b, ha, hb', hab⟩ := GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm x (δ j) d hd (hδli.ne_zero j) hx
    have h1 := hS.1 X hX x hxb hxn a ha
    have h2 := hS.1 X hX (δ j) (hδ.mem j) (hδ.nonneg j) b hb'
    rw [← h1, ← h2, hab]
  have hpeq : ∀ i, 0 < t i → p i = p' i := by
    intro i hti
    obtain ⟨hpb, hpn, hpp, hpl⟩ := hpi i hti
    obtain ⟨hpb', hpn', hpp', hpl'⟩ := hpi' i hti
    obtain ⟨j, -, d, hd, hpd⟩ := (hpc m' δ hδ hδli c hc hβc).1 i hti
    obtain ⟨j', -, d', hd', hpd'⟩ := (hpc' m' δ hδ hδli c' hc' hβc').1 i hti
    have hjj : j = j' := hδinj (by
      show lab.evalZ (δ j) = lab.evalZ (δ j')
      rw [← hlabray _ j d hd hpb hpn hpd, ← hlabray _ j' d' hd' hpb' hpn' hpd', hpl lab hlab, hpl' lab hlab])
    subst hjj
    have : toReal (p i) = (d / d') • toReal (p' i) := by
      rw [hpd, hpd', smul_smul, div_mul_cancel₀ _ hd'.ne']
    exact (_root_.GlobalTheory.PrimRay.eq_of_toReal_eq_smul (p i) (p' i) (d / d') (div_pos hd hd') hpp hpp' this).1
  apply toReal_injective
  rw [hp, hp']
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (ht i).lt_or_eq with h | h
  · rw [hpeq i h]
  · rw [← h, zero_smul, zero_smul]

end GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsMarkingCentreFunction
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction

theorem exists_markFun_props_gen : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → ∃ w : InvFun O, IsTwG w0 w ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  intro O _ _ _ _ bar w0 hb q ψ lab i hD hψ htψ htlab hlab
  classical
  obtain ⟨w, hw⟩ := GlobalTheory.PolFan.Mark.exists_markFun bar ψ lab i
  have ev := fun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) => GlobalTheory.PolFan.Mark.evalZ_markFun hw (X := X) β
  have mk : ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
      (β : LinearMap.BilinForm ℤ X), w.evalZ β = 1 → GlobalTheory.PolFan.Mark.IsMarked bar ψ lab i X β := fun β h => by
    rw [ev] at h
    split_ifs at h with h'
    · exact h'
    · norm_num at h
  refine ⟨w, fun σ hσ n B => by rw [hw, hw]; exact _root_.GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist O bar w0 hb ψ lab i htψ htlab σ hσ n B, ?_⟩
  intro X _ _ _ _ hX
  refine ⟨fun β _ _ => ?_, fun β _ _ h1 => (mk β h1).2.2.1, fun β _ _ h1 => (mk β h1).2.2.2.1,
    fun m v hv hle β _ _ β' _ _ h1 h1' hc hc' =>
      _root_.GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces.eq_of_isMarked_of_inRCone O bar hb q ψ lab i hD hψ hlab X hX m v hv hle β β' (mk β h1) (mk β' h1') hc hc',
    fun m v hv β hβ hp hc hl => ?_⟩
  · rw [ev]
    split_ifs <;> simp
  · obtain ⟨β₀, h0, hc0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone.exists_isMarked_inRCone O bar hb q ψ lab i hD hψ hlab X hX m v hv β hβ hp hc hl
    exact ⟨β₀, h0.1, h0.2.1, by rw [ev, if_pos h0], hc0⟩

end GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsStarSubdivision
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision

theorem isTwG_starFun {O : Type} [CommRing O] [Module.Finite ℤ O] {bar : O → O} {w0 : O} {ψ w : InvFun O}
    (hψ : IsTwG w0 ψ) (hd : IsTwG w0 (starDepth bar ψ w)) (K D : ℕ) :
    IsTwG w0 (starFun bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

theorem exists_starSubdivision : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 w → IsCentreSet bar q ψ w → ∃ ψ' : InvFun O, IsPolyFan bar q ψ' ∧ IsTwG w0 ψ' ∧ Subordinate bar q ψ' ψ ∧ IsStarOf bar q ψ w ψ' := by
  intro O _ _ _ _ bar w0 hb q ψ w hDom hψ htψ htw hW
  obtain ⟨K, D, hK, hD, hint, hs1, hs2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StrictStarFunction.exists_starFun_strict O bar hb q ψ w hDom hψ hW
  obtain ⟨hl1, hl2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn O bar hb q ψ w K D hW
  have c1 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) →
        IsCell bar (starFun bar ψ w K D) γ :=
    fun X _ _ _ _ hX m γ hγ hno => ⟨hγ.mem, hγ.nonneg, hl1 X hX m γ hγ hno, hs1 X hX m γ hγ hno⟩
  have c2 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
        ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
        IsCell bar (starFun bar ψ w K D) (Fin.cons β₀ fun j => γ (s j)) := by
    intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos
    refine ⟨fun i => ?_, fun i y => ?_, hl2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos,
      hs2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hβ₀
      · simpa using hγ.mem (s j)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp y
      · simpa using hγ.nonneg (s j) y
  have hstar : IsStarOf bar q ψ w (starFun bar ψ w K D) := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses.isStarOf_of_clauses O bar hb q ψ w _ hψ hW c1 c2
  have hpos : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 →
        0 < (starFun bar ψ w K D).evalZ β := by
    intro X _ _ _ _ hX β hβ hp h0
    rw [starFun_evalZ]
    have h1 := (hψ X hX).pos β hβ hp h0
    have h2 : 0 ≤ (starDepth bar ψ w).evalZ β := starDepth_eval_nonneg _
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  exact ⟨starFun bar ψ w K D, _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan.isPolyFan_star O bar hb q ψ w _ hψ hW hstar hint hpos,
    isTwG_starFun htψ (_root_.GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist.isTwG_starDepth O bar w0 hb ψ w htψ htw) K D, _root_.GlobalTheory.PolFan.subordinate_of_isStarOf _ bar q ψ w _ hstar, hstar⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OrbitMarkCoordinateLtOne
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound

theorem orbMark_coord_lt_one : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun O w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  intro O _ _ _ _ bar w0 hb φ hφ X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvsum X _ _ _ m δ h hli hprim
    β _ _ hβ1 c hc hβsum j
  obtain ⟨p, -, hpos, hcells⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces.exists_pieces_match O bar w0 hb φ hφ δ₀ h₀ hli₀ hprim₀ v t hv (fun i => (ht i).1) hvsum β hβ1
  rcases (hc j).lt_or_eq with hcj | hcj
  · obtain ⟨i, hti, d, hd, hpd, hcd⟩ := (hcells m δ h hli c hc hβsum).2 j hcj
    have hpi := (hpos i hti).2.2.1
    have hδj := _root_.GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq bar (δ j) (h.mem j) (hprim j)
    have hd1 := (_root_.GlobalTheory.PrimRay.eq_of_toReal_eq_smul (p i) (δ j) d hd hpi hδj hpd).2
    rw [hcd, hd1, mul_one]
    exact (ht i).2
  · rw [← hcj]; exact zero_lt_one

end GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbits
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_vorFun_cells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar (vorFun O g) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro O _ _ _ _ bar g hcov X _ _ _ _
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' ℤ X
  obtain ⟨k, nP, P, hPs, hPp, hPc⟩ := hcov X
  have hcls : ∀ (j : Fin k) (y : Fin n → ZMod (1 + 1)), ∃ F : Finset (Fin n → ℤ), (∀ a ∈ F, redV 1 a = y) ∧
      ∀ B ∈ rcone (P j), ∃ a ∈ F, ∀ a', redV 1 a' = y → B (r a) (r a) ≤ B (r a') (r a') := by
    intro j y
    obtain ⟨F, hF⟩ := GlobalTheory.dickson_finite_below_every (ι := {a : Fin n → ℤ // redV 1 a = y}) (nP j)
      fun a i => (P j i (r a.1) (r a.1)).toNat
    refine ⟨F.map (Function.Embedding.subtype _), fun a ha => ?_, ?_⟩
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha
      exact a.2
    · rintro B ⟨t, ht, rfl⟩
      have hval : ∀ a : Fin n → ℤ, (∑ i, t i • toReal (P j i)) (r a) (r a) = ∑ i, t i * (P j i (r a) (r a) : ℝ) := fun a => by
        simp [LinearMap.sum_apply]
      obtain ⟨a0, ha0, -⟩ := hF ⟨_, (redV_surjective 1 n y).choose_spec⟩
      obtain ⟨a1, ha1, hmin⟩ := Finset.exists_min_image (F.map (Function.Embedding.subtype _))
        (fun a => (∑ i, t i • toReal (P j i)) (r a) (r a)) ⟨_, Finset.mem_map_of_mem _ ha0⟩
      refine ⟨a1, ha1, fun a ha => ?_⟩
      obtain ⟨a', ha', hle⟩ := hF ⟨a, ha⟩
      refine (hmin _ (Finset.mem_map_of_mem _ ha')).trans ?_
      simp only [Function.Embedding.subtype_apply, hval]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
      have h1 := hle i
      have h2 := hPp j i (r a'.1)
      have h3 := hPp j i (r a)
      simp only at h1
      exact_mod_cast (by omega : P j i (r a'.1) (r a'.1) ≤ P j i (r a) (r a))
  choose F hFred hFmin using hcls
  have hred : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)) (y : Fin n → ZMod (1 + 1)), redV 1 (c y).1 = y :=
    fun j c y => hFred j y _ (c y).2
  have cell : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)), ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X),
      IsCell bar (vorFun O g) γ ∧ (contact bar fun y => r (c y).1) ⊆ rcone γ := by
    intro j c
    have hcv := (vorFun_value_le O bar g X n r (fun y => (c y).1) hr (hred j c)).1
    obtain ⟨s, γ, h1, h2, h3, h4⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact O bar hcov X _ _ hcv
    exact ⟨s, γ, _root_.GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact O bar g X n r _ hr (hred j c) s γ h1 h2 h3 h4, h4⟩
  choose s γ hγ hγc using cell
  refine ⟨⋃ j, ⋃ c, Set.range (γ j c), Set.finite_iUnion fun j => Set.finite_iUnion fun c => Set.finite_range _,
    fun B hB => ?_⟩
  obtain ⟨e, j, c, hc0, hce⟩ := hPc B hB
  have hB' : pullR e.toLinearMap B ∈ psdCone (bar := bar) (X := X) := pullR_mem_psdCone e.surjective hB
  have hBP : pullR e.toLinearMap B ∈ rcone (P j) := ⟨c, hc0, hce⟩
  choose a0 ha0F ha0 using fun y => hFmin j y _ hBP
  let d : ∀ y, ↥(F j y) := fun y => ⟨a0 y, ha0F y⟩
  have hcon : pullR e.toLinearMap B ∈ contact bar fun y => r (d y).1 := by
    refine ⟨hB', fun y x => ?_⟩
    obtain ⟨b, rfl⟩ := hr x
    have hb : redV 1 (a0 y + (b + b)) = y := by
      have h2 : a0 y + (b + b) = a0 y + (((1 : ℕ) : ℤ) + 1) • b := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [h2, redV_add_smul]
      exact hFred j y _ (ha0F y)
    simpa only [map_add (f := _)] using ha0 y _ hb
  obtain ⟨c', hc', hBc⟩ := hγc j d hcon
  exact ⟨e, _, γ j d, c', hγ j d, fun i => Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨d, i, rfl⟩⟩, hc', hBc⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionMultLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity

theorem starMult : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan bar q ψ' → Subordinate bar q ψ' φ → IsStarOf bar q φ w ψ' → ∀ M : ℕ, maxMult bar q φ ≤ M →
    maxMult bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar ψ' M δ →
          IsMultCell bar φ M δ ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  intro O _ _ _ _ bar hCM q φ lab w ψ' hDom hφ hlab hw hc1 hψ' hsub hstar M hM
  obtain ⟨hs1, hs2, hs3⟩ := hstar
  have key : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        (∃ (_ : IsCell bar φ γ'), (cellMult bar fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) ≤ M ∧
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1) ∨
        (cellMult bar fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) < M := by
    intro X _ _ _ _ hX n γ' hγ' hli hpr
    rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hw0, hin⟩ |
        ⟨m, γ, β₀, m', s, h, hγ, hβ₀, hpsd, hw1, hcone, hcut, hpos, hin⟩
    · left
      exact _root_.GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity.starOld_cell_mult_le O bar hCM q φ lab w ψ' hDom hφ hlab M hM X hX n γ' hγ' hli hpr m γ hγ
        (hs1 X hX m γ hγ hw0) hw0 hin
    · right
      exact _root_.GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity.cellMult_lt_of_star_new O bar hCM q φ lab w ψ' hlab hw hc1 M hM X hX n γ' hγ' hli hpr m γ β₀ m' s h
        hγ hβ₀ hpsd hw1 hcone hcut hpos (hs2 X hX m γ hγ β₀ hβ₀ hpsd hw1 hcone m' s h hcut hpos) hin
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.PolFan.maxMult
    refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hX => iSup_le fun n => iSup_le fun γ' => iSup_le fun hγ' => iSup_le fun hli =>
      iSup_le fun hpr => ?_
    rcases key X hX n γ' hγ' hli hpr with ⟨_, hle, _⟩ | hlt
    · exact_mod_cast hle
    · exact_mod_cast hlt.le
  · intro X _ _ _ _ hX m δ hδ
    obtain ⟨hc, hli, hpr, hEq⟩ := hδ
    rcases key X hX m δ hc hli hpr with ⟨hφ', _, hno⟩ | hlt
    · exact ⟨⟨hφ', hli, hpr, hEq⟩, hno⟩
    · exact absurd hEq (ne_of_lt hlt)

end GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity
end

