module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Formalism.FockGram.Bundle0001
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90TensorPadicUnramifiedExtension
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

section HilbertNinety

theorem iterate_groupEndomorphism_inv_apply {H : Type*} [Group H] (θ : H →* H) (i : ℕ) (x : H) :
    (⇑θ)^[i] x⁻¹ = ((⇑θ)^[i] x)⁻¹ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_inv]

theorem twistedNormProductIterate_succ_mul_iterate {H : Type} [Group H] (θ : H →* H) (n : ℕ) (δ : H) :
    nrmG θ (n + 1) δ = nrmG θ n δ * (⇑θ)^[n] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem units_map_ringHom_iterate_val {A : Type*} [CommRing A] (f : A →+* A) (i : ℕ) (u : Aˣ) :
    (((⇑(Units.map f.toMonoidHom))^[i] u : Aˣ) : A) = (⇑f)^[i] (u : A) := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ← ih] <;> rfl

theorem iterate_twisted_ringHom_mul_inv_eq_norm {A : Type} [CommRing A] (f : A →+* A) (a : Aˣ) (i : ℕ) (v : A) :
    (fun x => f x * ((a⁻¹ : Aˣ) : A))^[i] v =
      (⇑f)^[i] v * (((nrmG (Units.map f.toMonoidHom) i a)⁻¹ : Aˣ) : A) := by
  induction i generalizing v with
  | zero => simp [nrmG]
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [ih, twistedNormProductIterate_succ_mul_iterate, _root_.mul_inv_rev, Units.val_mul, ← iterate_groupEndomorphism_inv_apply, units_map_ringHom_iterate_val,
      ← RingHom.coe_pow, map_mul]
    ring

variable (p : ℕ) [Fact p.Prime]

theorem unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate (r : ℕ) (hr : 0 < r) (i : ℕ) (y : Qr p r) :
    (frobQEquiv p r hr ^ i) y = (⇑(frobQ p r))^[i] y := by
  induction i generalizing y with
  | zero => rfl
  | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply] <;> rfl

theorem padicUnramifiedFrobenius_iterate_degree_apply_eq (r : ℕ) (hr : 0 < r) (y : Qr p r) : (⇑(frobQ p r))^[r] y = y := by
  have h1 : frobQEquiv p r hr ^ r = 1 := by
    have := pow_orderOf_eq_one (frobQEquiv p r hr)
    rwa [orderOf_frobQEquiv] at this
  rw [← unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate p r hr, h1]
  rfl

theorem exists_ne_padicUnramifiedFrobenius_iterate_lt_degree (r : ℕ) (hr : 0 < r) (i : ℕ) (hi0 : 0 < i) (hir : i < r) :
    ∃ y : Qr p r, (⇑(frobQ p r))^[i] y ≠ y := by
  by_contra h
  push_neg at h
  have h1 : frobQEquiv p r hr ^ i = 1 := AlgEquiv.ext fun y => by
    rw [unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate, h y]; rfl
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_frobQEquiv] at h2
  exact absurd (Nat.le_of_dvd hi0 h2) (not_le.2 hir)

variable (B : Type) [CommRing B] [Algebra ℚ_[p] B]

theorem tensorMap_padicUnramifiedFrobenius_iterate_tmul (r i : ℕ) (b : B) (y : Qr p r) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)))^[i] (b ⊗ₜ y) =
      b ⊗ₜ (⇑(frobQ p r))^[i] y := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp

theorem tensorMap_padicUnramifiedFrobenius_iterate_degree (r : ℕ) (hr : 0 < r) (x : B ⊗[ℚ_[p]] Qr p r) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)))^[r] x = x := by
  change ((Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom ^ r) x = x
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul b y =>
    rw [RingHom.coe_pow]
    exact (tensorMap_padicUnramifiedFrobenius_iterate_tmul p B r r b y).trans (by rw [padicUnramifiedFrobenius_iterate_degree_apply_eq p r hr])
  | add x y hx hy => rw [map_add (f := _), hx, hy]

end HilbertNinety

end GlobalTheory.LKMid

namespace GlobalTheory.LKMid

theorem hilbert90_frobenius_tensor_unramified_padic : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ (B : Type) [CommRing B] [Algebra ℚ_[p] B]
    [Module.Finite ℚ_[p] B] (a : (B ⊗[ℚ_[p]] Qr p r)ˣ),
    nrmG (Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom) r a = 1 →
    ∃ g : (B ⊗[ℚ_[p]] Qr p r)ˣ, a = g⁻¹ *
      Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom g := by
  intro p _ r hr B _ _ _ a ha
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  let σ := Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)
  let τ : B ⊗[ℚ_[p]] Qr p r → B ⊗[ℚ_[p]] Qr p r := fun x => σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _)
  have hτr : ∀ v, τ^[r] v = v := by
    intro v
    have := iterate_twisted_ringHom_mul_inv_eq_norm σ.toRingHom a r v
    rw [ha, inv_one, Units.val_one, mul_one] at this
    exact this.trans (tensorMap_padicUnramifiedFrobenius_iterate_degree p B r hr v)

  let W : Submodule ℚ_[p] (B ⊗[ℚ_[p]] Qr p r) :=
    { carrier := {v | τ v = v}
      add_mem' := by
        intro x y hx hy
        show σ (x + y) * _ = x + y
        rw [map_add (f := _), add_mul]
        rw [show σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = x from hx,
          show σ y * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = y from hy]
      zero_mem' := by
        show σ 0 * _ = 0
        rw [map_zero, zero_mul]
      smul_mem' := by
        intro c x hx
        show σ (c • x) * _ = c • x
        rw [map_smul, smul_mul_assoc]
        rw [show σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = x from hx] }

  let e : (Qr p r ⊗[ℚ_[p]] B) ≃ₐ[ℚ_[p]] (B ⊗[ℚ_[p]] Qr p r) := Algebra.TensorProduct.comm ℚ_[p] (Qr p r) B
  have he_smul : ∀ (c : Qr p r) (w : Qr p r ⊗[ℚ_[p]] B), e (c • w) = ((1 : B) ⊗ₜ c) * e w := by
    intro c w
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.comm_tmul] <;> rfl
  let s : Qr p r ≃+* Qr p r := (frobQEquiv p r hr).toRingEquiv
  have hs : ∀ y, s y = frobQ p r y := fun _ => rfl
  let F : (Qr p r ⊗[ℚ_[p]] B) →+ (Qr p r ⊗[ℚ_[p]] B) :=
    { toFun := fun w => e.symm (τ (e w))
      map_zero' := by simp [τ]
      map_add' := fun x y => by simp only [τ, map_add (f := _), add_mul] }
  have hFe : ∀ w, e (F w) = τ (e w) := fun w => AlgEquiv.apply_symm_apply e _
  have hF : ∀ (c : Qr p r) (w : Qr p r ⊗[ℚ_[p]] B), F (c • w) = s c • F w := by
    intro c w
    apply e.injective
    rw [hFe, he_smul, he_smul, hFe, hs]
    simp only [τ, σ, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, mul_assoc]
  have hFi : ∀ (i : ℕ) (w : Qr p r ⊗[ℚ_[p]] B), F^[i] w = e.symm (τ^[i] (e w)) := by
    intro i
    induction i with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      apply e.injective
      rw [hFe, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have hFr : ∀ w, F^[r] w = w := by
    intro w
    rw [hFi, hτr, AlgEquiv.symm_apply_apply]
  have hsr : ∀ x, (⇑s)^[r] x = x := fun x => padicUnramifiedFrobenius_iterate_degree_apply_eq p r hr x
  have hsi : ∀ i, 0 < i → i < r → ∃ x, (⇑s)^[i] x ≠ x := fun i h0 h1 => exists_ne_padicUnramifiedFrobenius_iterate_lt_degree p r hr i h0 h1
  have hspan := GlobalTheory.semilinear_fixed_span (Qr p r) s r hr hsr hsi (Qr p r ⊗[ℚ_[p]] B) F hF hFr

  have hkey : ∀ m : Ideal (B ⊗[ℚ_[p]] Qr p r), m.IsMaximal → ∃ w ∈ W, w ∉ m := by
    intro m hm
    by_contra h
    push_neg at h
    let I' : Submodule (Qr p r) (Qr p r ⊗[ℚ_[p]] B) :=
      { carrier := {v | e v ∈ m}
        add_mem' := by
          intro x y hx hy
          show e (x + y) ∈ m
          rw [map_add (f := _)]
          exact m.add_mem hx hy
        zero_mem' := by
          show e 0 ∈ m
          rw [map_zero]
          exact m.zero_mem
        smul_mem' := by
          intro c x hx
          show e (c • x) ∈ m
          rw [he_smul]
          exact m.mul_mem_left _ hx }
    have hle : Submodule.span (Qr p r) {v | F v = v} ≤ I' := by
      rw [Submodule.span_le]
      intro v hv
      have hv' : τ (e v) = e v := by
        have h2 : e (F v) = e v := congrArg e hv
        rwa [hFe] at h2
      exact h _ hv'
    rw [hspan] at hle
    have h1 : e 1 ∈ m := hle Submodule.mem_top
    rw [map_one] at h1
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  haveI : IsArtinianRing (B ⊗[ℚ_[p]] Qr p r) := IsArtinianRing.of_finite ℚ_[p] (B ⊗[ℚ_[p]] Qr p r)
  have hfin := IsArtinianRing.setOf_isMaximal_finite (B ⊗[ℚ_[p]] Qr p r)
  let fS : Ideal (B ⊗[ℚ_[p]] Qr p r) → Subspace ℚ_[p] W := fun I => (I.restrictScalars ℚ_[p]).comap W.subtype
  have htop : (⊤ : Subspace ℚ_[p] W) ∉ hfin.toFinset.image fS := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨I, hI, hIt⟩ := hmem
    rw [Set.Finite.mem_toFinset] at hI
    obtain ⟨w, hwW, hwI⟩ := hkey I hI
    have : (⟨w, hwW⟩ : W) ∈ fS I := by rw [hIt]; exact Submodule.mem_top
    exact hwI this
  obtain ⟨w, hw⟩ := (Set.ne_univ_iff_exists_notMem _).1 (Subspace.biUnion_ne_univ_of_top_notMem htop)
  have hunit : IsUnit (w : B ⊗[ℚ_[p]] Qr p r) := by
    by_contra hu
    obtain ⟨I, hI, hwI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
    apply hw
    rw [Set.mem_iUnion₂]
    exact ⟨fS I, Finset.mem_image.2 ⟨I, (Set.Finite.mem_toFinset _).2 hI, rfl⟩, hwI⟩
  have hfix : σ (w : B ⊗[ℚ_[p]] Qr p r) * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = w := w.2
  have hσ : σ (hunit.unit : B ⊗[ℚ_[p]] Qr p r) = (hunit.unit : B ⊗[ℚ_[p]] Qr p r) * a := by
    rw [IsUnit.unit_spec]
    calc σ (w : B ⊗[ℚ_[p]] Qr p r)
        = σ (w : B ⊗[ℚ_[p]] Qr p r) * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) * a := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = w * a := by rw [hfix]
  refine ⟨hunit.unit, Units.ext ?_⟩
  rw [Units.val_mul, Units.coe_map]
  show (a : B ⊗[ℚ_[p]] Qr p r) = _ * σ _
  rw [hσ, Units.inv_mul_cancel_left]

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev l2 {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (φ₁ φ₂ : X → ℂ) : ℂ := Lift.pet μ 𝓕 φ₁ φ₂

abbrev Upq (W : HSp D) (ρ : D.what₂.Tau) : Type := UpqT (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2

abbrev Frames (W : HSp D) : Type :=
  ∀ ρ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D ρ)).1 ⊕ Fin (W.sig (tauE D ρ)).2) (Fin W.rank) ℂ

def IsFrames (W : HSp D) (A : Frames W) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * A ρ = gramAt D W ρ

def conjFrame {p q n : ℕ} (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q * b * A : Matrix (Fin n) (Fin n) ℂ)

def realMat (W : HSp D) (A : Frames W) (ρ : D.what₂.Tau) (b : Upq W ρ) : Matrix (Fin W.rank) (Fin W.rank) ℂ :=
  conjFrame (gramAt D W ρ) (A ρ) (UpqT.mat b)

def realElt (θ : Datum.InfFam D) (W : HSp D) (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : GA D W :=
  ((Finset.univ : Finset D.what₂.Tau).toList.map fun ρ => atTau θ W ρ (g ρ)).prod

abbrev FinCos (W : HSp D) (K : Subgroup (GA D W)) : Type := GfC W ⧸ K.subgroupOf (GfC W)

def FinCos.rep {W : HSp D} {K : Subgroup (GA D W)} (c : FinCos W K) : GA D W := (c.out : GfC W)


open Classical in
def quadSign (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ :=
  if (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 then 1 else -1

def quadTerm (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : ℕ) : ℝ :=
  quadSign D v ^ i / (Ideal.absNorm v.asIdeal : ℝ) ^ i

def dLoc (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ := ∏ i ∈ Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D v i)⁻¹

def dOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ℝ :=
  ∏' p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D p.1.1 p.2.1)⁻¹

def eulerOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ) : ℂ :=
  ∏' p : {w : HeightOneSpectrum (𝓞 D.host.E) // OffS D S w} × Fin D.R.r, (1 - x p.1.1 p.2)⁻¹


variable (D) in
def degAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ :=
  ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levW (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

abbrev levV (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    Subgroup (GL (Fin (Vc D i).rank) (Lev.EAf D)) := lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)

abbrev petW (i : Fin D.R.m) (F₁ F₂ : GA D (Wc D i) → ℂ) : ℂ := l2 (R.νW i) (R.fdW i) F₁ F₂

def upLift (i : Fin D.R.m) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (F : GA D (Wc D i) → ℂ) (h : GA D (Vc D i)) : ℂ :=
  petW R i (fun g => Datum.thetaKO ω h g φ) F

def IsLiftData (F : Face D A) (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ)
    (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  R.Char F ∧ PrimeToHost R t ∧ IsEmbOverK D σ s ∧ IsLocalLevel P ∧ IsConjChars R i t s cμ cη m ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω ∧
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) ∧
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f ∧
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) ∧ c.Is ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io




variable (D) in
def DeltaNorm : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) =
    ∏ ρ : D.what₂.Tau, ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℂ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℂ))




variable (D) in
def MassLower : Prop :=
  ∀ i : Fin D.R.m, (Vc D i).IsPosDef → 1 / ((NumberField.Units.torsionOrder D.host.E : ℝ) ^ D.R.nV * (D.R.nV.factorial : ℝ)) ≤
    GlobalTheory.Mass.unitaryMass D.sp.cm.sig (Vc D i).gram (GlobalTheory.Mass.Levels.latStab (Vc D i))

end GlobalTheory.AdelicScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerWordNeZeroReversedWordNeZero
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.SignInnerAdjoint

theorem sgn_sq_one {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    (Formalism.REAL.sgn ε a b : ℂ) * (Formalism.REAL.sgn ε a b : ℂ) = 1 := by
  unfold Formalism.REAL.sgn; split_ifs <;> norm_num

theorem sgn_symm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.sgn ε b a = Formalism.REAL.sgn ε a b := by
  unfold Formalism.REAL.sgn; split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem inner_E_right {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E)
    (a b : Fin n) (w y : V) :
    ⟪w, E a b y⟫_ℂ = (Formalism.REAL.sgn ε a b : ℂ) * ⟪E b a w, y⟫_ℂ := by
  rw [hU b a w y, sgn_symm, ← mul_assoc, sgn_sq_one, one_mul]

theorem word_adj {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E)
    (l : List (Fin n × Fin n)) : ∃ c : ℂ, c ≠ 0 ∧ ∀ w x : V,
      ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ =
        c * ⟪((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w, x⟫_ℂ := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, fun w x => by simp⟩
  | cons p t ih =>
    obtain ⟨c, hc, h⟩ := ih
    refine ⟨(Formalism.REAL.sgn ε p.1 p.2 : ℂ) * c, mul_ne_zero ?_ hc, fun w x => ?_⟩
    · intro h0; have := sgn_sq_one ε p.1 p.2; rw [h0] at this; simp at this
    · simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.map_nil, List.prod_append, List.prod_nil, mul_one, Module.End.mul_apply,
        Prod.fst_swap, Prod.snd_swap] at h ⊢
      rw [inner_E_right hU, h, mul_assoc]

end GlobalTheory.SignInnerAdjoint

theorem GlobalTheory.SignInnerAdjoint.main : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), IsUnitary ε E → ∀ (l : List (Fin n × Fin n)) (w x : V), ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 → ⟪x, ((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 := by
  intro n ε V _ _ E hU l w x hne
  obtain ⟨c, hc, h⟩ := GlobalTheory.SignInnerAdjoint.word_adj hU l
  rw [h] at hne
  have h2 := right_ne_zero_of_mul hne
  intro h3; exact h2 (inner_eq_zero_symm.mp h3)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirections
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartAct

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart GlobalTheory.LawLog

theorem logOf_eq {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} (G : Germ.FGLaw k d) (i : Fin d) :
    GlobalTheory.FormalLog.logOf G i = ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i := rfl

theorem subst_act_log {k O : Type} [CommRing k] [Algebra ℚ k] [CommRing O] {d : ℕ} (G : Germ.FGLaw k d)
    (A : Germ.OAct O G) (a : O) (b : Fin d) :
    subst (fun i => subst (oneVar k d) (A.act a i)) (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G b)) =
      ∑ j, coeff (Finsupp.single ((0 : Fin 1), j) 1) (A.act a b) •
        (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G j) : MvPowerSeries (Fin d) k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subst_oneVar _ cc_oneVar _ (A.const a), logOf_eq, GlobalTheory.TwistCheck.log_act, ← coe_substAlgHom hs_oneVar, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem isIntHom_actX_and_eigen (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (a : 𝓞 E) :
    IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧
      ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  refine ⟨⟨fun b => ?_, fun b α => ?_, fun b => ?_⟩, fun ℓ => ?_⟩
  · refine constantCoeff_subst_eq_zero hs_oneVar cc_oneVar ?_
    rw [constantCoeff_map, (GlobalTheory.IntChartCheck.const_zero Ch).2 a b, map_zero]
  · have e : actX Ch X a b = map (jX X) (subst (oneVar T.V _) (Ch.actT a b)) := by
      rw [actX, map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact isIntV_jX X _
  · let _ := io.toAlgebra
    let A : Germ.OAct (𝓞 E) (lawX Ch X) := GlobalTheory.FBMap.mapAct X.ιF Ch.ch.B.A
    have hA : ∀ i, A.act a i = map (jX X) (Ch.actT a i) := fun i => by
      show map X.ιF (Ch.ch.B.A.act a i) = _
      rw [Ch.gen.1.2.1 a i, jX, map_comp]; rfl
    have h := subst_act_log (lawX Ch X) A a b
    simp only [hA, coeff_map] at h
    exact h
  · obtain ⟨χ, hχ⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir.exists_char c T io ℓ.1
    have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a (χ a) (hχ a)
    have hz : embX io X ℓ.1 a = jX X (χ a) := by
      rw [jX, RingHom.comp_apply, hχ]; rfl
    funext i
    have h2 := congrArg (jX X) (congrFun h i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply, smul_eq_mul] at h2
    rw [hz]
    simpa only [Matrix.mulVec, dotProduct, tanX, lieVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] using h2

end GlobalTheory.ChartAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesTer
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (X : Set (AF F ⊗[F] E)), IsCompact X → IsClosed (SUSupp σ J ε) → (∀ g ∈ SUSupp σ J ε, ∀ i j, ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ X) → IsCompact (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppCompact.isCompact_SUSupp | exact GlobalTheory.SUSuppCompact.isCompact_SUSupp | (intros; apply GlobalTheory.SUSuppCompact.isCompact_SUSupp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaarStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_specialUnitary_eq_smul_haar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (ν : Measure (realSU X.Ψ X.Gm)), 1 ≤ r → IsOrth X x → ν.IsHaarMeasure → (∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x) → riemHaar X.Ψ X.Gm x = ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  first | exact @GlobalTheory.RiemConst.riemHaar_eq_smul | exact GlobalTheory.RiemConst.riemHaar_eq_smul | (intros; apply GlobalTheory.RiemConst.riemHaar_eq_smul <;> assumption)
end

