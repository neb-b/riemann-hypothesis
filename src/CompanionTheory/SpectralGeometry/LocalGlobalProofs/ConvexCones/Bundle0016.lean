module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionBarycentreCellNextStage
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BarycentricStageExtension
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision

theorem baryStep : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab φ : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → IsTwG w0 φ → IsBaryStage bar q ψ lab φ (i + 1) → ∃ φ' : InvFun O, IsTwG w0 φ' ∧ IsBaryStage bar q ψ lab φ' i := by
  intro O _ _ _ _ bar w0 hO q ψ lab φ i hdom hψ hψt hlt hcar hφt hst
  obtain ⟨w, hwt, hw⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction.exists_markFun_props_gen O bar w0 hO q ψ lab i hdom hψ hψt hlt hcar
  obtain ⟨hφp, hφs, hφc⟩ := hst
  have hcen : IsCentreSet bar q φ w := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4, -⟩ := hw X hX
    refine ⟨h1, h2, fun m γ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc' => ?_⟩
    obtain ⟨b, a, v, u, -, hv, hcov, -, -, hvl, hoff, -⟩ := hφc X hX m γ hγ
    have inv : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → InRCone γ β → InRCone v β := by
      intro β hβ hp hw1 hc
      by_contra hn
      have := hoff β hβ hp (inRCone_trans hcov hc) hn
      rw [h3 β hβ hp hw1] at this
      exact lt_irrefl _ this
    exact h4 b v hv hvl β hβ hp β' hβ' hp' hw1 hw2 (inv β hβ hp hw1 hc) (inv β' hβ' hp' hw2 hc')
  obtain ⟨φ', hp', ht', hsub, hs1, hs2, hs3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision.exists_starSubdivision O bar w0 hO q φ w hdom hφp hφt hwt hcen
  refine ⟨φ', ht', hp', hsub.trans hφs, fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw X hX
  have hnat : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n :=
    fun β hβ hp => ⟨_, hcar X hX β hβ hp⟩
  have core : ∀ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
      IsCell bar φ (Fin.append v u) → IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) →
      (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β →
        ((i + 1 : ℕ) : ℝ) < lab.evalZ β) →
      (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) →
      ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone (Fin.append v u) β₀ →
      ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
        IsFaceCut (Fin.append v u) s h → 0 < h β₀ →
      ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X),
        IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧
        (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → _) k)) ∧
        Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β →
          (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
    intro b a v u hγ hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0
    exact _root_.GlobalTheory.PolFan.star_cell_bary_step O bar ψ lab φ' w i X b a v u hv hinj hlu hvl hoff hind hnat
      (fun m' s h hh => _root_.GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hO q ψ hψ X hX (hdom X) b v hv m' s h hh) h5
      (fun β hβ hp β' hβ' hp' hw1 hw2 hc hc' => (hcen X hX).2.2 _ _ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc')
      (fun β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e =>
        _root_.GlobalTheory.PolFan.carrierDim_le_of_add_cell O bar q ψ lab hcar X hX b v hv β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e)
      β₀ hb0 hp0 hw0 (h3 β₀ hb0 hp0 hw0) hin0
      (fun m' s h hh hpos => hs2 X hX _ _ hγ β₀ hb0 hp0 hw0 hin0 m' s h hh hpos)
  rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hno, hcov'⟩ | ⟨m, δ, β₀, m', s, h, hδ, hb0, hp0, hw0, hin0, hcut, hpos, hcov'⟩
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m γ hγ
    by_cases hc : ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone (Fin.append v u) β₀
    · obtain ⟨β₀, hb0, hp0, hw0, hin0⟩ := hc
      have hnin : ¬ InRCone γ β₀ := fun hh => by
        have := hno β₀ hb0 hp0 hh
        rw [hw0] at this
        exact one_ne_zero this
      obtain ⟨m', s, h, hcut, hpos, hsub'⟩ := reduce_of_not_mem hG hγ hcov hb0 hp0 hin0 hnin
      obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0 m' s h hcut hpos
      exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_cons_of (n := 0) β₀
        (inRCone_trans hsub' (hcov' j))), r4, r5, r6, r7, r8⟩
    · push_neg at hc
      have hw0 : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → w.evalZ β = 0 :=
        fun β hβ hp hin => (h1 β hβ hp).resolve_right fun e => hc β hβ hp e hin
      refine ⟨b, a, v, u, hs1 X hX _ _ hG hw0, hv, fun j => inRCone_trans hcov (hcov' j), hinj,
        fun j => ?_, fun β hβ hp hin => ?_, fun β hβ hp hin hn => ?_, hind⟩
      · have := hlu j; push_cast at this ⊢; linarith
      · obtain ⟨k, hk⟩ := hnat β hβ hp
        have hle := hvl β hβ hp hin
        rw [hk] at hle ⊢
        have hle' : k ≤ i + 1 := by exact_mod_cast hle
        rcases hle'.lt_or_eq with hl | hl
        · exact_mod_cast Nat.lt_succ_iff.1 hl
        · obtain ⟨β₁, hb1, hp1, hw1, hin1⟩ := h5 b v hv β hβ hp hin (by rw [hk, hl])
          exact absurd (inRCone_append_left v u hin1) (hc β₁ hb1 hp1 hw1)
      · have := hoff β hβ hp hin hn; push_cast at this ⊢; linarith
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m δ hδ
    obtain ⟨m'', s', h', hcut', hpos', hsub'⟩ := reduce_of_mem hG hδ hcov hin0 hcut hpos
    obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
      core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 (inRCone_trans hcov hin0) m'' s' h' hcut' hpos'
    exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_trans (inRCone_cons_mono β₀ hsub') (hcov' j)),
      r4, r5, r6, r7, r8⟩

end GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedCentreSet
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres

theorem isTwG_orbFun {O : Type} [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (w0 : O)
    (v : LinearMap.BilinForm ℤ X₀) : IsTwG w0 (OrbMark.orbFun O w0 v) := by
  intro τ hτ n B
  rw [OrbMark.orbFun_toFun, OrbMark.orbFun_toFun]
  congr 2
  apply propext
  constructor
  · rintro ⟨σ, hσ, s, hs, h⟩
    exact ⟨σ.trans τ, by simp [hσ, hτ], s, hs, fun a b x y hx hy => h a b x y hx hy⟩
  · rintro ⟨σ, hσ, s, hs, h⟩
    refine ⟨σ.trans τ.symm, by simp [hσ, RingEquiv.symm_apply_eq, hτ], s, hs, fun a b x y hx hy => ?_⟩
    have := h a b x y hx hy
    show B (OrbMark.twv τ (OrbMark.twv (σ.trans τ.symm) a)) (OrbMark.twv τ (OrbMark.twv (σ.trans τ.symm) b)) = _
    rw [OrbMark.twv_twv, OrbMark.twv_twv]
    convert this using 3 <;> ext i <;> simp

theorem centres_exists : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult bar q φ ≤ M → ∀ c : FormFamily O,
    ∃ w : InvFun O, IsTwG w0 w ∧ IsCentreSet bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  intro O _ _ _ _ bar w0 hb q φ lab _hdom _hfan hφ hlab hsl M hM _hmax c
  classical
  by_cases hex : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module O X) (_ : Module.Finite O X)
      (_ : Module.Projective O X), Module.finrank O X ≤ q ∧
      ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ ∧ c.Carries δ
  · obtain ⟨X₀, _, _, _, _, -, m₀, δ₀, hM₀, hc₀⟩ := hex
    obtain ⟨v, hv, hvp, hvn, t, ht, htv⟩ := _root_.GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac bar φ M δ₀ hM₀ hM
    obtain ⟨h₀, hli, hpr, -⟩ := hM₀
    have hv0 : v ≠ 0 := fun h => by
      have e : (⟨v, hv⟩ : balForms bar X₀) = 0 := Subtype.ext h
      rw [e] at hvp
      exact not_isPrim_zero hvp
    refine ⟨OrbMark.orbFun O w0 v, isTwG_orbFun w0 v,
      fun X _ _ _ _ hX => ⟨fun β _ _ => OrbMark.orbFun_eval_eq_zero_or_one _ _ _,
        fun β _ _ h1 => _root_.GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one bar w0 v hv hvp β h1,
        fun m γ hγ β hβ hβp β' hβ' hβp' h1 h1' hc hc' =>
          _root_.GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell.eq_of_orbMark_of_inRCone_cell O bar w0 hb q φ lab hφ hlab hsl δ₀ h₀ hli hpr v t hv0 (fun i => (ht i).1) htv X hX m γ hγ β hβ hβp β' hβ' hβp'
            h1 h1' hc hc'⟩,
      fun X _ _ _ _ _ m δ _ hδ => ?_,
      fun X _ _ _ _ _ m δ h hδ hδp β hβ hβp h1 c' hc' hβc =>
        _root_.GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound.orbMark_coord_lt_one O bar w0 hb φ hφ δ₀ h₀ hli hpr v t hv0 ht htv X m δ h hδ hδp β hβ hβp h1 c' hc' hβc⟩
    obtain ⟨β, hβ, hβp, h1, hin⟩ := _root_.GlobalTheory.PolFan.carries_exists_marked bar w0 c δ₀ v t hv hv0 hvn hc₀ (fun i => (ht i).1) htv X m δ hδ
    exact ⟨β, hβ, hβp, h1, hin⟩
  · refine ⟨GlobalTheory.PolFan.zeroFun O, fun _ _ _ _ => rfl, fun X _ _ _ _ _ =>
      ⟨fun β _ _ => Or.inl (zeroFun_evalZ β), fun β _ _ h => by simp at h,
        fun _ _ _ β _ _ _ _ _ h => by simp at h⟩,
      fun X _ _ _ _ hX m δ hδ hc => (hex ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, hX, m, δ, hδ, hc⟩).elim,
      fun X _ _ _ _ _ m δ _ _ _ β _ _ h => by simp at h⟩

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbitsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.psd_cone_finitely_many_orbits : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar (vorFun O g) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells <;> assumption)
end

