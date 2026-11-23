module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import ReciprocityTheory.GaloisValuations.GlobalB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Formalism.LocalToGlobal.SiegelLatticeTheory.EFSymmCont
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroups
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBounded
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.RowRhoInt

theorem isRepOf_conj (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (P : GL (Fin a) (Qbar l)) (hρ : ∀ g, ρ' g = P⁻¹ * ρ g * P)
    (h : IsRepOf D l ι π s ρ) : IsRepOf D l ι π s ρ' := by
  have hcoe : ∀ g, ((ρ' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) =
      ((P⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
        ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) * (P : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g; rw [hρ g, Units.val_mul, Units.val_mul]
  refine ⟨?_, Formalism.MainNotions.SumRepresentations.isSSRep_conj ρ ρ' P hρ h.2.1, ?_⟩
  · simp only [hcoe]
    exact (continuous_const.matrix_mul h.1).matrix_mul continuous_const
  · filter_upwards [h.2.2] with w hw B σ hB hσ
    rw [hcoe, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    exact hw B σ hB hσ

theorem isRepOf_map (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (τ : Qbar l ≃ₐ[ℚ_[l]] Qbar l)
    (h : IsRepOf D l (τ.toRingEquiv.trans ι) π s ρ) : IsRepOf D l ι π s (mapRep τ.toRingEquiv.toRingHom ρ) := by
  have hcoe : ∀ g, ((mapRep τ.toRingEquiv.toRingHom ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) =
      ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).map τ.toRingEquiv.toRingHom := fun _ => rfl
  have hnorm : ∀ x : Qbar l, ‖τ x‖ = ‖x‖ := fun x => (spectralNorm_eq_of_equiv τ x).symm
  have hcont : Continuous (τ : Qbar l → Qbar l) := (AddMonoidHomClass.isometry_of_norm τ hnorm).continuous
  refine ⟨?_, GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ _ _ ρ h.2.1, ?_⟩
  · simp only [hcoe]
    exact h.1.matrix_map hcont
  · filter_upwards [h.2.2] with w hw B σ hB hσ
    rw [hcoe, Matrix.charpoly_map, Polynomial.map_map, ← hw B σ hB hσ]
    congr 1

theorem isRepOf_of_read (D : D7) (l : ℕ) [Fact l.Prime] (ι₀ ι₁ : Qbar l ≃+* ℂ) (j : ↥D.LL0 →+* Qbar l)
    (h0 : ∀ x, ι₀ (j x) = embLL0 D x) (h1 : ∀ x, ι₁ (j x) = embLL0 D x) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (h : IsRepOf D l ι₀ π s ρ)
    (hp : ∀ᶠ w in Filter.cofinite, ∃ p : Polynomial ↥D.LL0,
      p.map (embLL0 D) = galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)) :
    IsRepOf D l ι₁ π s ρ := by
  have e0 : ι₀.toRingHom.comp j = embLL0 D := RingHom.ext h0
  have e1 : ι₁.toRingHom.comp j = embLL0 D := RingHom.ext h1
  refine ⟨h.1, h.2.1, ?_⟩
  filter_upwards [h.2.2, hp] with w hw hpw B σ hB hσ
  obtain ⟨p, hp⟩ := hpw
  have e := hw B σ hB hσ
  have hc : ((ρ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = p.map j := by
    apply Polynomial.map_injective ι₀.toRingHom ι₀.injective
    rw [e, Polynomial.map_map, e0, hp]
  rw [hc, Polynomial.map_map, e1, hp]

theorem isRepOf_of_split (D : D7) (hC : GlobalTheory.RowTie.ChebSplit D.nd) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (π π' : D.naut.CG a) (s : ℝ) (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (h : IsRepOf D l ι π s ρ) (h' : IsRepOf D l ι π' s ρ')
    (hs : ∀ w, IsSplitPl D.host w → D.naut.locG π w = D.naut.locG π' w) : IsRepOf D l ι π' s ρ := by
  obtain ⟨c₁, s₁, f₁⟩ := h
  obtain ⟨c₂, s₂, f₂⟩ := h'
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ ρ' c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, hsp, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 B g hB hg, hw.2 B g hB hg, hs w hsp])
  refine ⟨c₁, s₁, ?_⟩
  filter_upwards [f₂] with w hw B σ hB hσ
  rw [hcp σ]
  exact hw B σ hB hσ

theorem subtype_mapMatrix_injective {K : Type} [CommRing K] (S : Subring K) {a : ℕ} :
    Function.Injective (S.subtype.mapMatrix : Matrix (Fin a) (Fin a) S →+* Matrix (Fin a) (Fin a) K) :=
  fun M N h => Matrix.ext fun i k => Subtype.ext (congrFun (congrFun h i) k)

def restrictRep {K : Type} [CommRing K] (S : Subring K) {Γ : Type} [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) K)
    (hS : ∀ g i k, ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) i k ∈ S) : Γ →* GL (Fin a) S where
  toFun g := ⟨Matrix.of fun i k => ⟨_, hS g i k⟩, Matrix.of fun i k => ⟨_, hS g⁻¹ i k⟩, by
      apply subtype_mapMatrix_injective S
      rw [map_mul, map_one]
      change ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) * ((ρ g⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) = 1
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one], by
      apply subtype_mapMatrix_injective S
      rw [map_mul, map_one]
      change ((ρ g⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]⟩
  map_one' := by
    ext i k
    change ((ρ 1 : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) i k = (1 : Matrix (Fin a) (Fin a) S) i k
    rw [map_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' g h := by
    ext i k
    change ((ρ (g * h) : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) i k =
      ((Matrix.of fun i k => (⟨_, hS g i k⟩ : S)) * Matrix.of fun i k => (⟨_, hS h i k⟩ : S)) i k
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply]
    simp

theorem intOf_mono {l : ℕ} [Fact l.Prime] {K K' : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : K ≤ K') :
    Formalism.L2.TwC.intOf l K ≤ Formalism.L2.TwC.intOf l K' := fun _ hx => ⟨h hx.1, hx.2⟩

end GlobalTheory.HeightCounting.RowRhoInt

namespace GlobalTheory.HeightCounting.RowRhoInt

theorem twistEx : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE),
    GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π →
      ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l),
        IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := _root_.GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw

theorem conjIntegral : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)),
    Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) →
    ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k,
      ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := _root_.GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf

end GlobalTheory.HeightCounting.RowRhoInt

namespace GlobalTheory.HeightCounting.RowRhoInt

theorem core (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : SideA D cf jE) (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
    (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT)
    (hσ : ∃ k, 1 ≤ k ∧ k ≤ D.R.m ∧ D.what₂.isot k σ ≠ ⊥) (hg : D.nd.goodRow σ) :
    ∃ (L : Loc.FinExt l) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l)),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l))) ∧
      (∀ g i k, ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l)) i k ∈
        Formalism.L2.TwC.intOf l L.1) ∧
      ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ ι : Qbar l ≃+* ℂ, (∀ x, ι (j x) = embLL0 D x) →
          IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  obtain ⟨k, hk1, hk2, hk⟩ := hσ
  obtain ⟨π₀, hc₀, hr₀, hl₀, hp₀⟩ := hR k hk1 hk2 σ hk hg
  obtain ⟨ι₀, hι₀⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq l ↥D.LL0 j (embLL0 D)
  have h0 : ∀ x, ι₀ (j x) = embLL0 D x := fun x => RingHom.congr_fun hι₀ x
  obtain ⟨ρG, hρG⟩ := twistEx hA D cf jE A hG l ι₀ π₀ hc₀ hr₀
  obtain ⟨L, P, hP⟩ := conjIntegral l (G D.host.E D.nd.Om) D.R.r ρG hρG.1
  let ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l) := (MulAut.conj P⁻¹).toMonoidHom.comp ρG
  have hρ : ∀ g, ρ g = P⁻¹ * ρG g * P := fun g => by simp [ρ, MulAut.conj_apply]
  have hρ0 : IsRepOf D l ι₀ (D.naut.tw π₀ D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ :=
    isRepOf_conj D l ι₀ _ _ ρG ρ P hρ hρG
  refine ⟨L, ρ, hρ0.1, fun g i k => by rw [hρ]; exact hP g i k, fun π hc hr hl ι hι => ?_⟩
  have h1 := isRepOf_of_read D l ι₀ ι j h0 hι _ _ ρ hρ0 hp₀
  obtain ⟨ρ', hρ'⟩ := twistEx hA D cf jE A hG l ι π hc hr
  refine isRepOf_of_split D hC l ι _ _ _ ρ ρ' h1 hρ' (fun w hw => ?_)
  rw [D.naut.locG_tw, D.naut.locG_tw, hl₀ w hw, hl w hw]

end GlobalTheory.HeightCounting.RowRhoInt

namespace GlobalTheory.HeightCounting.RowRhoInt

section Pick

variable (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE)
  (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)

def GoodOcc (σ : D.what₂.FT) : Prop :=
  (∃ k, 1 ≤ k ∧ k ≤ D.R.m ∧ D.what₂.isot k σ ≠ ⊥) ∧ D.nd.goodRow σ


open Classical in
def pickL (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) : Loc.FinExt l :=
  if h : GoodOcc D σ then (core hA D cf jE A hG hR hC l j σ h.1 h.2).choose else ⟨⊥, inferInstance⟩


def starRestrictSubfield (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) : ↥D.LL0 →+* ↥D.LL0 where
  toFun x := ⟨star (x : D.what₂.LL), hstar x⟩
  map_one' := Subtype.ext (star_one _)
  map_mul' x y := Subtype.ext (star_mul' (x : D.what₂.LL) (y : D.what₂.LL))
  map_zero' := Subtype.ext (star_zero _)
  map_add' x y := Subtype.ext (star_add (x : D.what₂.LL) (y : D.what₂.LL))

def jSide (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l)
    (b : Bool) : ↥D.LL0 →+* PadicAlgCl l :=
  if b then j else j.comp (starRestrictSubfield D hstar)

end Pick

end GlobalTheory.HeightCounting.RowRhoInt

namespace GlobalTheory.HeightCounting.RowRhoInt

section HidaSetting

variable {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd}

def kap (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) : FractionRing (T.O0 i) →+* PadicAlgCl (T.l i) :=
  IsFractionRing.lift (g := (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1).subtype.comp (Sp.eO0 i).toRingHom)
    (Subtype.val_injective.comp (Sp.eO0 i).injective)

theorem kap_alg (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (y : T.O0 i) :
    kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) y) = (Sp.eO0 i y : PadicAlgCl (T.l i)) :=
  IsFractionRing.lift_algebraMap _ _

theorem twistFractionFieldToPadicAlgebraicClosure_padicInt (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (z : ℤ_[T.l i]) :
    kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i)) (z : ℚ_[T.l i]) := by
  rw [kap_alg]; exact Sp.ringSpec_baseIntegersEquiv_algebraMap i z

theorem kap_emb0 (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (x : ↥D.LL0) : kap Sp i (T.emb0 i x) = Sp.j0 i x := by
  obtain ⟨y, z, hz, e⟩ := IsFractionRing.div_surjective (A := T.O0 i) (T.emb0 i x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap (T.O0 i) (FractionRing (T.O0 i)) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hz0
  have h1 : T.emb0 i x * algebraMap (T.O0 i) (FractionRing (T.O0 i)) z = algebraMap (T.O0 i) (FractionRing (T.O0 i)) y := by
    rw [← e, div_mul_cancel₀ _ hz1]
  have h2 := (Sp.ringSpec_baseEmbedding_compatible i x y z hz0).mp h1
  have hz2 : ((Sp.eO0 i z : _) : PadicAlgCl (T.l i)) ≠ 0 := by
    intro h; apply hz0; apply (map_eq_zero_iff (Sp.eO0 i) (Sp.eO0 i).injective).1; exact Subtype.ext h
  rw [← e, map_div₀, kap_alg, kap_alg, ← h2, mul_div_cancel_right₀ _ hz2]

end HidaSetting


end GlobalTheory.HeightCounting.RowRhoInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedRootsPerturbedPolynomial
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem eq_of_perturbed_pow_sub_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (y z u : R) (m : ℕ) (h : Polynomial ℤ)
    (hy : y ^ m - 1 = u * Polynomial.aeval y h) (hz : z ^ m - 1 = u * Polynomial.aeval z h)
    (hu : u ∈ IsLocalRing.maximalIdeal R) (hzy : z - y ∈ IsLocalRing.maximalIdeal R)
    (hm : (m : R) ∉ IsLocalRing.maximalIdeal R) : z = y := by
  by_contra hne
  have hne' : z - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, hk⟩ : z - y ∣ Polynomial.aeval z h - Polynomial.aeval y h := by
    have := Polynomial.sub_dvd_eval_sub z y (h.map (algebraMap ℤ R))
    simpa only [Polynomial.eval_map_algebraMap] using this
  have hS := Commute.geom_sum₂_mul (Commute.all z y) m
  have hS' : (∑ i ∈ Finset.range m, z ^ i * y ^ (m - 1 - i)) = u * k := by
    apply mul_right_cancel₀ hne'
    rw [hS]
    linear_combination hz - hy + u * hk
  have hu0 : IsLocalRing.residue R u = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hu
  have hzy0 : IsLocalRing.residue R z = IsLocalRing.residue R y := by
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hzy
    rwa [map_sub, sub_eq_zero] at this
  have hm0 : (m : IsLocalRing.ResidueField R) ≠ 0 := by
    intro h0
    apply hm
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, h0]
  have hmpos : m ≠ 0 := by
    rintro rfl
    simp at hm0
  have hy1 : (IsLocalRing.residue R y) ^ m = 1 := by
    have := congrArg (IsLocalRing.residue R) hy
    rwa [map_sub, map_mul, hu0, zero_mul, map_pow, map_one, sub_eq_zero] at this
  have hy0 : IsLocalRing.residue R y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hmpos] at hy1
    exact zero_ne_one hy1
  have := congrArg (IsLocalRing.residue R) hS'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, hu0, zero_mul, hzy0] at this
  rw [geom_sum₂_self] at this
  exact mul_ne_zero hm0 (pow_ne_zero _ hy0) this

theorem exists_roots_fixed_of_mem_Ine (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A' : ValuationSubring Ω) (σ : G E Ω)
    (hσ : σ ∈ Ine (F := E) A') (b e : Ω) (m : ℕ) (f : Polynomial ℤ) (he : IsIntegral ℤ e)
    (hσe : σ e = e) (hv : A'.valuation (1 - e) < 1) (hm : A'.valuation (m : Ω) = 1)
    (hf : f.Monic) (hfm : f.natDegree = m) (hb : Polynomial.aeval b f = 0) :
    ∃ ys : Multiset Ω, Multiset.card ys = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧
      e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  set h : Polynomial ℤ := X ^ m - C 1 - f with hh
  have hdeg : h.degree < (m : WithBot ℕ) := by
    have h1 : (X ^ m - C 1 : Polynomial ℤ).Monic := Polynomial.monic_X_pow_sub_C 1 hm0
    have h2 : (X ^ m - C 1 : Polynomial ℤ).degree = m :=
      Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hm0) 1
    have h3 : f.degree = m := by rw [Polynomial.degree_eq_natDegree hf.ne_zero, hfm]
    rw [← h2]
    exact Polynomial.degree_sub_lt (h2.trans h3.symm) h1.ne_zero
      (by rw [h1.leadingCoeff, hf.leadingCoeff])
  let R := integralClosure ℤ Ω
  let e0 : R := ⟨e, he⟩
  let g0 : Polynomial R := f.map (algebraMap ℤ R) + C e0 * h.map (algebraMap ℤ R)
  have hf0 : (f.map (algebraMap ℤ R)).Monic := hf.map _
  have hf0d : (f.map (algebraMap ℤ R)).degree = m := by
    rw [hf.degree_map, Polynomial.degree_eq_natDegree hf.ne_zero, hfm]
  have hlt : (C e0 * h.map (algebraMap ℤ R)).degree < (f.map (algebraMap ℤ R)).degree := by
    rw [hf0d, ← Polynomial.smul_eq_C_mul]
    exact lt_of_le_of_lt ((Polynomial.degree_smul_le _ _).trans Polynomial.degree_map_le) hdeg
  have hg0 : g0.Monic := hf0.add_of_left hlt
  have hg0d : g0.degree = m := by
    rw [← hf0d]; exact Polynomial.degree_add_eq_left_of_degree_lt hlt
  have hev : ∀ y : Ω, Polynomial.aeval y g0 = Polynomial.aeval y f + e * Polynomial.aeval y h := by
    intro y
    simp only [g0, map_add (f := _), map_mul, Polynomial.aeval_map_algebraMap, Polynomial.aeval_C]
    rfl
  have hhev : ∀ y : Ω, Polynomial.aeval y h = y ^ m - 1 - Polynomial.aeval y f := by
    intro y
    simp [hh]
  let g : Polynomial Ω := g0.map (algebraMap R Ω)
  have hg : g.Monic := hg0.map _
  have hgd : g.natDegree = m := by
    rw [hg0.natDegree_map, Polynomial.natDegree_eq_of_degree_eq_some hg0d]
  have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨g.roots, hcard.trans hgd, ?_, ?_⟩
  · intro y hy
    have hy0 : Polynomial.aeval y g0 = 0 := by
      have := (Polynomial.mem_roots hg.ne_zero).mp hy
      rwa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at this
    have hyint : IsIntegral ℤ y := by
      have : IsIntegral R y := ⟨g0, hg0, hy0⟩
      exact isIntegral_trans y this
    refine ⟨hyint, ?_⟩
    have hyA : y ∈ A' := mem_of_isIntegral_int A' hyint
    have hσ' := mem_Ine.mp hσ
    have hzA : σ y ∈ A' := (apply_mem_iff_of_mem_Dec hσ'.1 y).mpr hyA
    have huA : 1 - e ∈ A' := (A'.valuation_le_one_iff _).mp hv.le
    have e1 : y ^ m - 1 = (1 - e) * Polynomial.aeval y h := by
      rw [hev] at hy0
      linear_combination hy0 - hhev y
    have e2 : (σ y) ^ m - 1 = (1 - e) * Polynomial.aeval (σ y) h := by
      have := congrArg σ e1
      rw [map_sub, map_pow, map_one, map_mul, map_sub, map_one, hσe] at this
      rw [this]
      congr 1
      exact (Polynomial.aeval_algHom_apply (σ : Ω →+* Ω).toIntAlgHom y h).symm
    have hae : ∀ x : A', ((Polynomial.aeval x h : A') : Ω) = Polynomial.aeval (x : Ω) h :=
      fun x => (Polynomial.aeval_algHom_apply A'.subtype.toIntAlgHom x h).symm
    have := eq_of_perturbed_pow_sub_one (R := A') ⟨y, hyA⟩ ⟨σ y, hzA⟩ ⟨1 - e, huA⟩ m h
      (Subtype.ext (by simpa [hae] using e1)) (Subtype.ext (by simpa [hae] using e2))
      ((A'.valuation_lt_one_iff _).mpr hv)
      ((A'.valuation_lt_one_iff _).mpr (hσ'.2 y ((A'.valuation_le_one_iff _).mpr hyA)))
      (fun hh' => by
        have := (A'.valuation_lt_one_iff _).mp hh'
        rw [show ((m : A') : Ω) = m from by simp, hm] at this
        exact lt_irrefl _ this)
    exact congrArg Subtype.val this
  · have := congrArg (Polynomial.eval b)
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hg hcard)
    rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_map_algebraMap, hev,
      hhev, hb] at this
    simp only [Function.comp_def, eval_sub, eval_X, eval_C] at this
    rw [this]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
section
noncomputable section

namespace GlobalTheory.Mem.SProv

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top

theorem conjF_invol (B : Pre) (x : B.host.E) : B.conjF (B.conjF x) = x := by
  rw [B.conjF_eq, B.conjF_eq]
  simpa [Examples₂.conjF_apply] using Examples₂.conjF_conjF B.host x

theorem exists_sStage_true : ∀ (K : Ctx) (B : Base) (C : Cols B) (W : RowsRest B C) (cd : CDHaar), K.Over B.toPre →
    SpectralModel.ColsPos C → W.Drows ≤ W.Dall → ∃ S : SStage B C W, S.s.Del = (Delv K.s K.cD : ℚ) ∧
      S.s.cdScale = Vol.trueScale cd ∧ (∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)) ∧
      ∀ (V : DivStage B C W) (N : NStage B C W) (G : GJStage B C) p,
        Nonempty (Formalism.L2.S.LocIso ((assemble B C W V S N G).s.atP p) (Formalism.L2.S.locC (assemble B C W V S N G) p)) := by
  intro K B C W cd h h2 h3
  obtain ⟨S, a, b, c, d⟩ := exists_sStage_loc K B C W cd h h2 h3
    (fun p => Examples₂.locAtC B.toPre.conjF (conjF_invol B.toPre) (Examples₂.finrank_FE B.host) p)
  exact ⟨S, a, b, c, fun V N G => Formalism.L2.S.loc_of_adj (assemble B C W V S N G) d⟩

end GlobalTheory.Mem.SProv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroupsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistRings_characters_classGroups : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (J : ∀ (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 ↥D.LL0)), ((l : ℕ) : 𝓞 ↥D.LL0) ∈ w.asIdeal → (↥D.LL0 →+* PadicAlgCl l)), (∀ (l : ℕ) [Fact l.Prime] w h (x : 𝓞 ↥D.LL0), x ∈ w.asIdeal ↔ ‖J l w h x‖ < 1) → ValLL0 D cf → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → ∃ (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), ∀ i, Sp.j0 i = J (T.l i) (Sp.eTw i) (Sp.pl_emb i).1 ∧ Sp.K0 i = b0 (T.l i) (Sp.j0 i) ∧ Sp.Lw i = b1 (T.l i) (Sp.j0 i) := by
  first | exact @GlobalTheory.TwRing.exists_ringSpec | exact GlobalTheory.TwRing.exists_ringSpec | (intros; apply GlobalTheory.TwRing.exists_ringSpec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalAlgClosureExistsPosPowApplyEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem galAlgClosure_exists_pos_pow_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (σ : G E Ω) (t : Ω), ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
  intro E Ω _ _ _ _ _ σ t
  have hint : IsIntegral E t :=
    ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic t).isIntegral
  have hmem : ∀ i : ℕ, (σ ^ i) t ∈ (minpoly E t).rootSet Ω := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ i : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    rw [minpoly.aeval, map_zero] at h
    exact h
  haveI : Finite ((minpoly E t).rootSet Ω) := ((minpoly E t).rootSet_finite Ω).to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨(σ ^ i) t, hmem i⟩ : (minpoly E t).rootSet Ω))
  have heq' : (σ ^ i) t = (σ ^ j) t := congrArg Subtype.val heq
  have key : ∀ a b : ℕ, a < b → (σ ^ a) t = (σ ^ b) t → ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
    intro a b hab h
    refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
    apply (σ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact h.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq'
  · exact key j i h heq'.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem Dec_valuation_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : G E Ω), σ ∈ Dec (F := E) A → ∀ t : Ω, A.valuation (σ t) = A.valuation t := by
  first
  | exact @_root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq
  | exact _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq
  | (apply _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq ..)

end GlobalTheory
end

