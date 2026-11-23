module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0001
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGenEqOneOfFrOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExpone
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.LengthH0Bound

theorem toNat_div_le (A B : ℕ∞) (r c : ℕ) (h : A ≤ (r : ℕ∞) * (c : ℕ∞) * B) :
    ((A.toNat : ℚ) / (B.toNat : ℚ)) ≤ (r : ℚ) * c := by
  rcases eq_or_ne B ⊤ with hB | hB
  · rw [hB, ENat.toNat_top, Nat.cast_zero, div_zero]; positivity
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB
  have h' : A ≤ ((r * c * b : ℕ) : ℕ∞) := by push_cast; exact h
  obtain ⟨a, ha, hle⟩ := ENat.le_natCast_iff.mp h'
  subst ha
  rw [ENat.toNat_coe, ENat.toNat_coe]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.cast_zero, div_zero]; positivity
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast hle

theorem lenUnit_le_of_kill {O : Type} [CommRing O] [IsDomain O] (k p c : ℕ)
    (hp : algebraMap O (FractionRing O) (p : O) ≠ 0) (W : Submodule O (KOG O k))
    (hW : ∀ x ∈ W, (p : O) ^ c • x = 0) :
    lenUnit (O := O) p ↥W ≤ (k : ℚ) * c := by
  have hlen := length_le_of_killed (LL := FractionRing O) (stdG O (FractionRing O) k) _
    (GlobalTheory.FiniteTwistInvariants.stdG_eq_span k) (p : O) hp c W hW
  exact toNat_div_le _ _ k c hlen

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem locM_entry {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (i j : Fin k) :
    Br.locM Bw M g i j = Br.toLLK Bw (algebraMap O (FractionRing O) (M (Br.ι Bw g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec' {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS Bw k ((mapM (algebraMap O (FractionRing O)) M (Br.ι Bw g)).mulVec u) =
      (Br.locM Bw M g).mulVec (Br.vecS Bw k u) := by
  funext i
  change Br.toLLK Bw (∑ j, algebraMap O (FractionRing O) (M (Br.ι Bw g) i j) * u j) =
    ∑ j, Br.locM Bw M g i j * Br.toLLK Bw (u j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, locM_entry]


set_option synthInstance.maxHeartbeats 400000 in
theorem phi_eq_zero {k : ℕ} (z : KOG O k) (hz : Br.phi Bw k z = 0) : z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change (Submodule.Quotient.mk (Br.vecS Bw k y) :
    (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) = 0 at hz
  rw [Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨b, hb⟩ := hz
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨fun j => Bw.eO.symm (b j), funext fun j => ?_⟩
  apply (Br.toLLK Bw).injective
  have hbj := congrFun hb j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply] at hbj ⊢
  rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  exact hbj


set_option synthInstance.maxHeartbeats 400000 in
theorem actD_phi {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ)
    (gK : ↥(GK Bw.Kw)) (x : KOG O k) :
    actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k ((WKG M).comp f (Br.ι Bw gK) x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := vecS_mulVec' Bw (M.comp f) gK y
  change (Submodule.Quotient.mk (((Br.locM Bw (M.comp f)) gK).mulVec (Br.vecS Bw k y)) :
      (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) =
    Submodule.Quotient.mk (Br.vecS Bw k
      (((mapM (algebraMap O (FractionRing O)) (M.comp f)) (Br.ι Bw gK)).mulVec y))
  rw [h]


set_option synthInstance.maxHeartbeats 400000 in
theorem inv_killed {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ) (p c : ℕ)
    (h : ∀ y : (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k,
      (∀ gK, actD (Br.lat Bw (M.comp f)) gK y = y) → ((p : Br.Ow Bw) ^ c) • y = 0) :
    ∀ x ∈ Representation.invariants ((WKG M).comp f), (p : O) ^ c • x = 0 := by
  intro x hx
  have hfix : ∀ gK, actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k x := by
    intro gK
    rw [actD_phi, hx (Br.ι Bw gK)]
  have hk := h _ hfix
  apply phi_eq_zero Bw
  rw [LinearMap.map_smulₛₗ]
  simp only [map_pow, map_natCast]
  exact hk


include Bw in
theorem natCast_ne_zero : algebraMap O (FractionRing O) ((l : ℕ) : O) ≠ 0 := by
  intro h
  have h2 := congrArg (Br.toLLK Bw) h
  rw [map_natCast, map_natCast, map_zero] at h2
  have hQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  apply hQ
  apply (algebraMap ℚ_[l] (Br.LLw Bw)).injective
  rw [map_natCast, map_zero]
  exact h2

end Bridge


set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
    (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) (c : ℕ),
    let S := LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs;
    ∀ T : LocLat S.G S.Qp S.LL S.O, T = GlobalTheory.HubX.wLat D i ρ π u hu hc →
    (∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ c) • x = 0) →
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * c := by
  intro D HW i ρ π u hu s hs hc c S T hT hkill
  subst hT
  have hp : LocalSituation.ell S = D.nd.l i := (D.loc (D.nd.l i)).PD_p _
  have hK := inv_killed (D.nbr i u hu) (WpO D.nd i ρ π) (decS D.nd u) (D.nd.l i) c (fun y hy => by
    have := hkill y hy
    rwa [hp] at this)
  have hq := lenUnit_le_of_kill D.R.r (D.nd.l i) c (natCast_ne_zero (D.nbr i u hu)) _ hK
  exact_mod_cast hq

end GlobalTheory.LengthH0Bound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverComponentReadingsUnitModulusScalar
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFrameMod

open CategoryTheory

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (u : Sˣ) :
    wchar (ex Dw a n) (fun i : Ix Dw => Option.elim i u (fun _ => 1)) = (u : S) ^ n := by
  unfold wchar
  rw [Fintype.prod_option]
  simp [ex]

end Weight

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

def midEmb (C : Cover T j σ) : C.c'.F →+* ℂ := C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)


set_option maxHeartbeats 1600000 in
theorem exists_scalar (C : Cover T j σ) (hσ : C.σ₂.comp C.inc = σ) (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ))
    (y₂ : FrPt C.d.Xo₂ C.d.c₂ (CAt C.σ₂))
    (hx : (y₂.x : Sp ℂ ⟶ C.d.Xo₂.X) ≫ C.d.r = (y.x : Sp ℂ ⟶ (T.Q.Xo j).X))
    (hu : ∀ τ i, (y₂.u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) ≫ C.d.m.φ =
      (y.u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left)) :
    ∃ t : ℂ, t ≠ 0 ∧
      (∀ (σ' : KA T.Q.l →+* ℂ) (σ₂' : KA C.d.l₂ →+* ℂ) (g : ℕ) (ty ty₂ : Fin g → (D.host.E →+* ℂ))
        (F : FamilyUnif (T.Q.Xo j) σ' ty) (F₂ : FamilyUnif C.d.Xo₂ σ₂' ty₂) (i : Fin F.n)
        (i₂ : Fin F₂.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P₂ : (F₂.Di i₂).La →+ (Fin g → ℂ)),
        IsPeriod (F.Di i) ty P → IsPeriod (F₂.Di i₂) ty₂ P₂ → y.x = F.u i P →
        y₂.x = F₂.u i₂ P₂ → GlobalTheory.GeoLevel.NormPin F i P y → GlobalTheory.GeoLevel.NormPin F₂ i₂ P₂ y₂ → ‖t‖ = 1) ∧
      ∀ (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ : Rul C.d.Xo₂ C.d.c₂,
        C.IsPull f f₂ → toC (evR C.d.Xo₂ C.d.c₂ f₂ y₂) = t ^ n * toC (evR (T.Q.Xo j) T.Q.c f y) := by
  letI a₂ : Algebra C.d.c₂.F (CAt (midEmb C)) := RingHom.toAlgebra (R := C.d.c₂.F) (S := CAt (midEmb C)) C.σ₂
  letI a₀ : Algebra T.Q.c.F (CAt (midEmb C)) := RingHom.toAlgebra (R := T.Q.c.F) (S := CAt (midEmb C)) σ
  have hov : AlgOver T.Q.c C.c' C.hle (CAt (midEmb C)) := fun a => DFunLike.congr_fun hσ a
  have hc : ∀ a : C.c'.F, algebraMap C.d.c₂.F (CAt (midEmb C)) (C.d.eF a) = algebraMap C.c'.F (CAt (midEmb C)) a :=
    fun _ => rfl
  let y₀ : FrPt (T.Q.Xo j) T.Q.c (CAt (midEmb C)) := y
  let z : FrPt (T.Q.Xo j) C.c' (CAt (midEmb C)) := FrPt.ext C.hle hov y₀
  let w : FrPt C.d.Xo₂ C.d.c₂ (CAt (midEmb C)) := y₂
  obtain ⟨y', hy'⟩ := GlobalTheory.CoverSec.exists_frOver_below C.d hc w
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (T.Q.Xo j).s) hx).trans z.x_over))
  obtain ⟨t₀, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen z y' (hy'.1.symm.trans hx)
    (funext fun τ => funext fun i => (hy'.2.1 τ i).symm.trans (hu τ i))
  refine ⟨toC (t₀ : CAt (midEmb C)), Units.ne_zero (M₀ := ℂ) t₀, ?_, fun n a f hf f₂ hp => ?_⟩
  · intro σ' σ₂' g ty ty₂ F F₂ i i₂ P P₂ p p₂ e e₂ N N₂
    exact norm_gen_eq_one_of_frOver C.d F₂ F i₂ i P₂ P y₂ z y' _ p₂ p e₂ e N₂ N hy' ht
  · have h1 := @hp (CAt (midEmb C)) (inferInstanceAs (Field ℂ)) a₀
      (inferInstanceAs (Algebra C.c'.F (CAt (midEmb C)))) a₂ hov hc w y' hy'
    have hb : FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y₀ (y'.res C.hle hov) := ht
    have h2 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.2.2.2
      (CAt (midEmb C)) (inferInstanceAs (IsReduced ℂ)) a n f hf _ _ _ hb
    rw [wchar_gen] at h2
    exact h1.trans h2


set_option maxHeartbeats 1600000 in
theorem comp_over_comp_norm : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ((∀ τ i, ‖dmin (C.U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  intro D T hT j hj σ hσ C hC k₂
  obtain ⟨h₀, rfl⟩ := GlobalTheory.CoverOnto.exists_dict₂_comp D T hT j hj σ hσ C hC k₂
  obtain ⟨γ, hΛ, hiso, hfr⟩ := GlobalTheory.CoverFrameMove.frames_differ D T hT j hj σ hσ C hC h₀
  refine ⟨(T.dict j σ h₀).1, γ, hΛ, hiso, fun h hh => GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hT j hj σ hσ C hC h h₀ hh,
    fun x x' hx hxx' => ?_⟩
  have hU := hT.unf j hj σ hσ
  have hU₂ := hC.2.2.2.1
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ :=
    fun τ => ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hx' : x' ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ γ ((hU.2.1 _).1.trans (hU₂.2.1 _).1.symm) hΨ hiso x x' hx hxx'
  obtain ⟨o₁, o₂⟩ := _root_.GlobalTheory.CoverFrameOver.un_over D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr x x' hx hx' hxx'
  obtain ⟨t, ht, hn, hr⟩ := exists_scalar C hC.2.2.1 _ _ o₁ o₂
  refine ⟨hx', t, ht, fun hd => ?_, fun n a _ f hf f₂ _ hp => ?_⟩
  · have hd' : ∀ τ i, ‖dmin ((T.U j σ).X (T.dict j σ h₀).1).Gm x' τ i‖ = 1 := by
      rintro ⟨τ, h₁⟩ i
      rw [← hd ⟨τ, (hΨ τ).1 h₁⟩ i]
      unfold dmin
      rw [hxx' τ ((hΨ τ).1 h₁) h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso τ]
    obtain ⟨g, e, F, ik, φ, -, hP⟩ := hU.2.2.2.2.2
    obtain ⟨g₂, e₂, F₂, ik₂, φ₂, -, hP₂⟩ := hU₂.2.2.2.2.2
    obtain rfl : g₂ = g := Fin.equiv_iff_eq.1 ⟨e₂.trans e.symm⟩
    obtain ⟨P, -, p, u, -, N⟩ := hP _ ⟨x', hx'⟩
    obtain ⟨P₂, -, p₂, u₂, -, N₂⟩ := hP₂ _ ⟨x, hx⟩
    exact hn _ _ _ _ _ F F₂ _ _ P P₂ p p₂ u u₂ (N hd') (N₂ hd)
  · have e : rdU (T.U j σ) f (T.dict j σ h₀).1 x' =
        toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un (T.dict j σ h₀).1 ⟨x', hx'⟩)) := dif_pos hx'
    rw [e]
    exact (dif_pos hx).trans (hr n a f hf f₂ hp)

end GlobalTheory.CoverFrameMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UseLoc

section Gen
variable {l : ℕ} [Fact l.Prime]

def incO {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥(OL LL) →+* ↥(OL LL') where
  toFun x := ⟨IntermediateField.inclusion h x, by
    have := x.2
    exact IsIntegral.map ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) this⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def incV {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) : (Fin k → ↥LL.1) →+ (Fin k → ↥LL'.1) :=
  (AddMonoidHom.compLeft (IntermediateField.inclusion h).toRingHom.toAddMonoidHom (Fin k))

def liftQ {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) :
    (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k →+ (Fin k → ↥LL'.1) ⧸ stdG ↥(OL LL') ↥LL'.1 k :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (stdG ↥(OL LL') ↥LL'.1 k).toAddSubgroup).comp (incV h k)) (by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨fun j => incO h (u j), rfl⟩)

theorem liftQ_mk {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) (v : Fin k → ↥LL.1) :
    liftQ h k (Submodule.Quotient.mk v) = Submodule.Quotient.mk (incV h k v) := rfl

end Gen
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

def locOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL) :=
  mapM (incO C.le) (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)))

def chiOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  (Units.map ((incO C.le).comp (D.nbr i w hw).eO.toRingHom).toMonoidHom).comp
    ((χ.comp (decS D.nd w)).comp (Br.iota D.nbr i w hw))

abbrev repV (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Representation ↥C.LL.1 (Br.G D.nbr i w hw) (Fin k → ↥C.LL.1) :=
  matRep (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) N)

def latC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Lattice (O := ↥(OL C.LL)) (repV C N) :=
  stdLatG Subtype.val_injective N

def chiT (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) :
    Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) * θ

def embC (HW : HWOf D.loc) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) :=
  ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hA.2.2).emb

end AtW
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}


open Module in
def SetC (HW : HWOf D.loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
    (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
    (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ) : Prop :=
  tableLineDegreeTwo.TopHyp (Br.PD D.loc D.nbr i w hw) (embC HW C hA) D.R.t h w' η typ U
                     (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) ∧
    ∀ x, tableLineDegreeTwo.IsFull (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
      (repV C (twistM (locOC C (rTwO D.nd i r x)) θ))

end AtW
end GlobalTheory.UseLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaAboveDetOne
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.lintegral_theta_above_det_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ,
      ∫⁻ g in 𝓕 ∩ {g | 1 ≤ GlobalTheory.RSnm.detAbs g}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ' φ' hφ' G hG μ _ 𝓕 h𝓕 x
  have hd := GlobalTheory.MSpanDecay.Good.decays
    (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ' hφ')
  obtain ⟨C, hC⟩ := (GlobalTheory.SBThetaUpper.isSmallKernel_sq_mul hd hG).tsum_le
    (N := ⌈x⌉₊ + 1) (by omega)
  have hI := ((GlobalTheory.RSTheta.integrableOn_absDet_rpow_neg (Nat.succ_pos m) μ h𝓕
    (s := (⌈x⌉₊ + 1 : ℕ) - x) (by push_cast; linarith [Nat.le_ceil x])).const_mul C).lintegral_lt_top
  refine ne_top_of_le_ne_top hI.ne (lintegral_mono fun g => ?_)
  obtain ⟨hs, hle⟩ := hC g
  have h0 := GlobalTheory.RSnm.detAbs_pos g
  change _ ≤ C * GlobalTheory.RSnm.detAbs g ^ _ at hle
  change _ ≤ ENNReal.ofReal (C * GlobalTheory.RSnm.detAbs g ^ _)
  rw [← ENNReal.tsum_mul_left]
  simp only [← eNorm_pow, ← eNorm_mul]
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs,
    ← ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _), neg_sub, sub_eq_neg_add,
    Real.rpow_add h0, ← mul_assoc]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (by positivity))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogCardLevelGroupLeScalePowMulLength
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem log_card_levelGroup_le_scale_pow_mul_length : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C * x ^ C * (Fm.L x i).sc.L := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_levelGroup_le_and_level_large eps Fm
  refine ⟨15, max x0 1, fun x hx hx1 i => ?_⟩
  have h := (hx0 x (le_trans (le_max_left _ _) hx) hx1 i).1
  have h1x : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hL : 1 ≤ (Fm.L x i).sc.L := Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hp : (0 : ℝ) ≤ x ^ (15 : ℝ) := Real.rpow_nonneg (by linarith) _
  unfold Formalism.BasicNotions.lam0 at h
  calc Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ x ^ (15 : ℝ) := h
    _ ≤ 15 * x ^ (15 : ℝ) := by linarith
    _ = 15 * x ^ (15 : ℝ) * 1 := by ring
    _ ≤ 15 * x ^ (15 : ℝ) * (Fm.L x i).sc.L := by gcongr

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialCoeffGoodOfCuspidal
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coeff_good_of_cuspidal : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    Good (GlobalTheory.StdCharConductor.psi E) m (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  first | (exact @GlobalTheory.PartialBlock.good_partialCoeff_blockGL) | (exact GlobalTheory.PartialBlock.good_partialCoeff_blockGL) | (intros; apply GlobalTheory.PartialBlock.good_partialCoeff_blockGL  <;> assumption)
end

