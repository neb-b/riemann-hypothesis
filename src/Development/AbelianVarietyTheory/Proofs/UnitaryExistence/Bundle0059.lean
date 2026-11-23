module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspPairingIntIffHermitianExponentIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmUnitPowFourIdempotentModEight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroNoetherianBase
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.FrameGenerator

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem scal_eq_constFn {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) :
    scal x a i = constFn (fst (Over.mk x) Xo.univ.t.G).left _ a := rfl

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  rw [scal_eq_constFn]
  exact (congrArg _ (map_one _)).trans (map_one _)

theorem isPullback_gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) :
    IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
  (IsPullback.of_hasPullback _ _).flip

theorem secGen_of_secNZ (hS : Out.SecBaseChangeSt) {T : Type} [CommRing T] (x : Sp T ⟶ Xo.X)
    (θ : LB.Sec (PPx x)) (h : SecNZ x θ) : SecGen x θ := by
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  intro s
  have hw : LBIso (PPx x) (Xo.univ.t.PP.L.pull (snd (Over.mk x) Xo.univ.t.G).left) :=
    exists_iso_linComb Xo.univ.t.PP.isLB _ _ fun _ _ _ => by simp
  refine SectionBaseChange.generates hS (Obj.toPolAV Xo.univ) (isPullback_gx x)
    (DVR.linComb_isLB _ Xo.univ.t.PP.isLB _ _) hw θ (fun y => ?_) s
  obtain ⟨q, i, hq, hi⟩ := h y
  exact ⟨q, hq, TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩⟩

theorem secNZ_of_secBC {R T : Type} [CommRing R] [CommRing T] {ψ : R →+* T} {j : Sp R ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    {θ : LB.Sec (PPx j)} {θ' : LB.Sec (PPx x')} (h : SecNZ j θ) (hx : x' = spMap ψ ≫ j)
    (hb : SecBC ψ 1 j x' θ θ') : SecNZ x' θ' := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := hb
  have sq : IsPullback pm (fst (Over.mk x') Xo.univ.t.G).left (fst (Over.mk j) Xo.univ.t.G).left (spMap ψ) :=
    IsPullback.of_right (by rw [h₁, ← hx]; exact isPullback_gx x') h₂ (isPullback_gx j)
  intro p
  obtain ⟨q, i, hq, hi⟩ := h (spMap ψ p)
  obtain ⟨q', rfl, e₂⟩ := Scheme.exists_preimage_of_isPullback sq q p hq
  have le : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx j).U i := fun y hy => Set.mem_iInter.2 fun k => by
    have : (snd (Over.mk x') Xo.univ.t.G).left y ∈ Xo.univ.t.PP.L.U (i k) := Set.mem_iInter.1 hy k
    rw [← h₁] at this; exact this
  have mem : q' ∈ (PPx x').U i := Set.mem_iInter.2 fun k => by
    have : (snd (Over.mk j) Xo.univ.t.G).left (pm q') ∈ Xo.univ.t.PP.L.U (i k) :=
      Set.mem_iInter.1 ((Gx j).basicOpen_le _ hi) k
    show (snd (Over.mk x') Xo.univ.t.G).left q' ∈ Xo.univ.t.PP.L.U (i k)
    rw [← h₁]; exact this
  refine ⟨q', i, e₂, ?_⟩
  rw [← h₃ i le, scal_one', _root_.one_mul, Scheme.basicOpen_appLE]
  exact ⟨mem, hi⟩

theorem secGen_of_secNZ_baseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsNoetherianRing R] (j : Sp R ⟶ Xo.X) (θ : LB.Sec (PPx j)), SecNZ j θ → ∀ (T : Type) [CommRing T] (ψ : R →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ j → SecBC ψ 1 j x' θ θ' → SecGen x' θ' :=
  fun hS _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ x' θ' hx hb => secGen_of_secNZ hS x' θ' (secNZ_of_secBC h hx hb)

end GlobalTheory.FrameGenerator
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExpoModels

theorem exists_equiv_of_stab {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : IsUStab G Λ γ) :
    ∃ e : Λ ≃ₗ[𝓞 E] Λ, ∀ v : Λ, (e v : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) := by
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨{ toFun := fun v => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E), (h.2 _).1 v.2⟩
            invFun := fun v => ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E),
              (h.2 _).2 (by rw [hri]; exact v.2)⟩
            map_add' := fun x y => Subtype.ext (by simp [Matrix.mulVec_add])
            map_smul' := fun a x => Subtype.ext (by simp [Matrix.mulVec_smul])
            left_inv := fun v => Subtype.ext (hli _)
            right_inv := fun v => Subtype.ext (hri _) }, fun v => rfl⟩

theorem mem_gamma_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {F : FamilyUnif Xo σ' ty} {r : ℕ} {M : ModelsOf F r} (hM : ModelBase M) (hA : l.A = 1) (k : Fin F.n)
    (γ : GL (Fin r) E) :
    γ ∈ (M.X k).Γ ↔ IsUStab (M.X k).Gm (M.X k).Λ γ ∧ ∀ v ∈ (M.X k).Λ, ∃ w ∈ (M.X k).Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + l.M • w := by
  rw [hM.gam k γ]
  refine and_congr_right fun hs => ?_
  obtain ⟨e, he⟩ := exists_equiv_of_stab _ _ γ hs
  constructor
  · rintro ⟨h1, -⟩ v hv
    let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans (e.trans (M.φ k).symm)
    have hg : ∀ a, (M.φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
      intro a
      simp only [gam, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he]
    have key := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di k) l gam
      (fun a b => by
        have h2 := hM.ef k (gam a) (gam b)
        rw [hg, hg, hs.1, ← hM.ef k a b] at h2
        exact_mod_cast h2)
      (fun a ha => by
        obtain ⟨b, hb⟩ := h1 a ha
        refine ⟨b, (M.φ k).injective (Subtype.ext ?_)⟩
        rw [hg, hb, map_add (f := _), map_nsmul]
        rfl)
    obtain ⟨b, hb⟩ := key ((M.φ k).symm ⟨v, hv⟩)
    refine ⟨M.φ k b, (M.φ k b).2, ?_⟩
    have h3 := hg ((M.φ k).symm ⟨v, hv⟩)
    rw [hb, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply] at h3
    exact h3.symm
  · intro h
    refine ⟨fun a _ => ?_, fun a => ?_⟩
    · obtain ⟨w, hw, h2⟩ := h _ (M.φ k a).2
      refine ⟨(M.φ k).symm ⟨w, hw⟩, ?_⟩
      rw [LinearEquiv.apply_symm_apply]
      exact h2
    · refine ⟨(M.φ k).symm (e (M.φ k a) - M.φ k a), ?_⟩
      rw [LinearEquiv.apply_symm_apply, hA, one_smul, ← he]
      simp

theorem expoMatch_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ρ : ℕ), ModelBase M → l.A = 1 → FJ.ExpoMatch M.X 1 ρ l.M := by
  intro E _ _ _ H Dw l Xo σ' g ty F r M ρ hM hA cu₀
  obtain ⟨k, cu₀⟩ := cu₀
  obtain ⟨cu, P, cc', hP, hPe, hne, hΛ⟩ := _root_.GlobalTheory.exists_cusp_pseudoBasis E r ρ (M.X k) cu₀
  refine _root_.GlobalTheory.CuspBasis.expoMatch_of_basis_change E r ρ l.M (M.X k) cu₀ cu P hP hPe ?_
  intro χ hχ
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hr : LinearMap.range φ = (M.X k).Λ := by
    simp only [φ, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hz := _root_.GlobalTheory.CuspCentre.mem_zGam_principal_iff E H r ρ (M.X k) l.M (F.Di k) φ cu cc' hr
    ⟨Subtype.val_injective.comp (M.φ k).injective,
      by rw [← LinearMap.coe_range, hr]; exact (M.X k).Λ_span,
      (M.X k).Gm_herm, (M.X k).Gm_det, hM.ef k⟩ (mem_gamma_iff hM hA k) hΛ
  have hd := _root_.GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted E r ρ (M.X k) cu cc' hΛ
  have ht := _root_.GlobalTheory.ExponentTrace.prE_int_iff_values_integral E H r ρ (M.X k) l.M cc' χ (by have := l.three_le; omega) hne hχ
  constructor
  · intro h u hu m hm
    exact ht.1 (fun β h1 h2 => h β ((hz β).2 ⟨h1, h2⟩)) u m ((hd u).1 hu) ((hd m).1 hm)
  · intro h β hβ
    exact ht.2 (fun u m hu hm => h u ((hd u).2 hu) m ((hd m).2 hm)) β ((hz β).1 hβ).1 ((hz β).1 hβ).2

end GlobalTheory.ExpoModels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaFrameDetMulSqInvariant
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem thetaFrame_det_mul_sq_invariant : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → Out.SecTwistSt → (∀ (g : ℕ) (ga : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), ga ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct ga τ z) (spAct ga τ) ^ 2 = ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut ga τ).det * eC (expArg ga τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ a a', (U.Di i).EF (bas a) (bas a') = -omegaStd a a') → (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P b' (gam a) = h₀ *ᵥ P b a) → ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → (h b).det * (thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) ^ 2 = (h b').det * h₀.det * (thetaChar (τ b') c₁ c₂ (h b' *ᵥ (h₀ *ᵥ z)) * fr j (b', h₀ *ᵥ z)) ^ 2 := by
  intro hMink hT hlaw E _ _ _ H D l Xo σ g ty U i m B P bas h τ c₁ c₂ fr hP hbas hw hn h₁ h₂ hd hne hc h0 hs
    b hb b' hb' gam h₀ hiso hhalf hA hPP j z hz
  have riem : ∀ b ∈ B, IsUnit (h b).det ∧ τ b ∈ SiegelH (Fin g) := fun b hb => by
    obtain ⟨h', τ', -, hu, hsy, hpos, huniq⟩ :=
      (RiemannRel.riemann_relations E H (U.Di i) g ty bas hbas).1 (P b) (hP b hb)
    obtain ⟨e1, e2⟩ := huniq _ _ (hn b hb)
    rw [e1, e2]
    exact ⟨hu, hsy, hpos⟩
  obtain ⟨hu, hτ⟩ := riem b hb
  obtain ⟨hu', hτ'⟩ := riem b' hb'
  obtain ⟨hu₀, hpt, hex⟩ := _root_.GlobalTheory.FamRigid.ex_eq_of_level_group hMink E H D l Xo σ g ty U i (P b) (P b') gam h₀ (hP b hb)
    (hP b' hb') hiso hhalf hA hPP
  have hθ : ∀ b ∈ B, (fun z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) ≠ 0 := fun b hb hz => by
    obtain ⟨hu, hτ⟩ := riem b hb
    obtain ⟨n, rfl⟩ := ThetaRatio.exists_eq_halfVec h₁
    obtain ⟨n', rfl⟩ := ThetaRatio.exists_eq_halfVec h₂
    refine theta_ne_zero hτ (halfVec n) (halfVec n') (funext fun w => ?_)
    have := congrFun hz ((h b)⁻¹ *ᵥ w)
    simp only [ThetaRatio.thetaChar_ofRealVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mulVec] at this
    exact this
  obtain ⟨ρ, κ, hρd, hρ0, hρ1, hκ, hrel, hfr⟩ := thetaFrame_ratio hT E H D l Xo σ g ty U i m B P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) fr hP hd hne hc h0 hs b hb b' hb' h₀
    (hθ b hb) (hθ b' hb') hu₀ hpt hex
  have hfull := LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hhalf
  have hiso' : ∀ a b, (U.Di i).EF (gam.symm a) (gam.symm b) = (U.Di i).EF a b := fun a b => by
    rw [← hiso, gam.apply_symm_apply, gam.apply_symm_apply]
  have hfull' : ∀ a, ∃ e, gam.symm a = a + l.M • e := fun a => by
    obtain ⟨e, he⟩ := hfull (gam.symm a)
    rw [gam.apply_symm_apply] at he
    refine ⟨-e, ?_⟩
    rw [smul_neg]
    exact eq_add_neg_of_add_eq he.symm
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => bas.symm (gam.symm (bas (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := AdaptedDet.blocks_det_mod_eight E H (U.Di i) g l.M bas gam.symm N hw
    l.three_le hiso' hfull' (fun _ _ => rfl)
  have hcomp : ∀ a, (h b' * h₀) *ᵥ P b (gam.symm a) = h b' *ᵥ P b' a := fun a => by
    rw [← Matrix.mulVec_mulVec, ← hPP, gam.apply_symm_apply]
  obtain ⟨ga, hga, hgae, hτe, hhe, hde⟩ := PeriodChange.period_change E H (U.Di i) g bas gam.symm N
    (P b) ((P b).comp gam.symm.toLinearMap.toAddMonoidHom) (h b) (h b' * h₀) (τ b) (τ b') hbas hiso'
    (fun _ _ => rfl) (fun _ => rfl) (hn b hb)
    (fun k => ⟨(hcomp _).trans (hn b' hb' k).1, (hcomp _).trans (hn b' hb' k).2⟩) hτ hτ' hu
  have h8ga : ∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j) :=
    fun i j => by
      rw [hgae]
      exact h8 j i
  have hχ : ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have e : ga.toBlocks₂₂.det = N.toBlocks₁₁.det := by
      rw [hgae, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]
    have e' : ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) = 1 := by
      have h4 : ((4 : ℕ) : ℤ) ∣ N.toBlocks₁₁.det - 1 := Dvd.dvd.trans (by norm_num) hdet
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      rw [e, this]
    rw [e', map_one, Int.cast_one]
  have hl := hlaw g ga hga h8ga
  rw [hχ] at hl
  have dl : Differentiable ℂ (fun w : Fin g → ℂ => (h b)⁻¹ *ᵥ w) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h b)⁻¹)).differentiable
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g ga hga h8ga hl c₁ c₂ h₁ h₂ (τ b) hτ
    (fun w => ρ ((h b)⁻¹ *ᵥ w)) κ (hρd.comp dl) (fun w => hρ0 _)
    (by simp only [Matrix.mulVec_zero, hρ1]) hκ (fun w => by
      have := hrel ((h b)⁻¹ *ᵥ w)
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at this
      rw [hhe, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hτe] at this
      exact this)
  have e := hrel z
  rw [hfr j z hz, hde, Matrix.det_mul, ← hκ2, ← mul_assoc (thetaChar (τ b') c₁ c₂ _), e]
  ring

end GlobalTheory
end
end

