module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMvPolynomialOfIteratedBackwardDifferenceVa

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOne
section
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.ExpFrame.CharUnit

open NumberField Polynomial in
private theorem le_one_of_forall_pow_le {a C : ℝ} (h : ∀ n : ℕ, a ^ n ≤ C) : a ≤ 1 := by
  by_contra ha
  push_neg at ha
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ha
  exact absurd (h n) (not_le.mpr hn)


open NumberField Polynomial in
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [NormedField K] (χ : Γ →* Kˣ) (hc : Continuous fun g => ((χ g : Kˣ) : K)) (g : Γ) :
    ‖((χ g : Kˣ) : K)‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hb : ∀ h : Γ, ∀ n : ℕ, ‖((χ h : Kˣ) : K)‖ ^ n ≤ C := fun h n => by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow]
    exact hC _ ⟨h ^ n, rfl⟩
  have h1 := le_one_of_forall_pow_le (hb g)
  have h2 := le_one_of_forall_pow_le (hb g⁻¹)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ g : Kˣ) : K)‖ := norm_pos_iff.mpr (χ g).ne_zero
  have : 1 ≤ ‖((χ g : Kˣ) : K)‖ := by
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ hpos |>.mpr hlt
    linarith
  linarith


open NumberField Polynomial in
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (PadicAlgCl l)ˣ), Continuous (_root_.GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ χ hχ g
  refine _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact χ ?_ g
  have h := (Units.continuous_val.comp hχ).matrix_elem 0 0
  convert h using 1
  funext x
  simp [_root_.GlobalTheory.TripleGal.rk1]

end GlobalTheory.ExpFrame.CharUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCompactModCentralizerSeparableLocal
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.OrbitCptW

theorem orbit_cpt_w : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := by
  intro E _ _ _ _ n w N hN C hC
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  obtain ⟨C', hC', hC'g⟩ := GlobalTheory.OrbCpt.gl_orbit_cpt (k := w.adicCompletion E) N.val hN
    ((fun y : GLw n w => (y : Matrix (Fin n) (Fin n) (w.adicCompletion E))) '' C)
    (hC.image Units.continuous_val)
  refine ⟨(fun y => y⁻¹) '' C', hC'.image continuous_inv, fun x hx => ?_⟩
  obtain ⟨c, hc, t, ht, hxt⟩ := hC'g x⁻¹ ⟨_, hx, by simp [mul_assoc]⟩
  refine ⟨t⁻¹, ?_, c⁻¹, ⟨c, hc, rfl⟩, ?_⟩
  · have h1 : t * N = N * t := Units.ext ht
    calc t⁻¹ * N = t⁻¹ * (N * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * N) * t⁻¹ := by rw [h1]
      _ = N * t⁻¹ := by group
  · rw [← _root_.mul_inv_rev, ← hxt, inv_inv]

end GlobalTheory.OrbitCptW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalComplementHyperbolicPlaneLatticeSelfDu
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkewDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  unfold form
  have : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + (fun i => σ (c i)) := by
    funext i; simp
  rw [this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) (s : E) :
    form σ J a (s • b) = σ s * form σ J a b := by
  unfold form
  have : (fun i => σ ((s • b) i)) = σ s • (fun i => σ (b i)) := by
    funext i; simp
  rw [this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_restrict (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (u u' : Fin n₁ → E) : form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  unfold form
  have h : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ (fun i => σ (u' i)) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) ι u' i
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end GlobalTheory.PlaneSkewDual

namespace GlobalTheory.PlaneSkewDual

theorem lowLat_selfDual (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) :
    ∀ u, u ∈ lowLat ι L ↔ ∀ u' ∈ lowLat ι L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E (o * form σ (ιᵀ * J * ι.map σ) u u')) := by
  intro u
  simp only [mem_lowLat, form_restrict]
  constructor
  · intro hu u' hu' o
    exact (hL _).1 hu _ hu' o
  · intro h
    refine (hL _).2 fun z hz o => ?_
    obtain ⟨s, t, u', -, -, hu', rfl⟩ := hsplit z hz
    have hz' : form σ J (ι *ᵥ u) (s • x + ι *ᵥ u' + t • y) = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
      rw [form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1, (horth u).2]
      ring
    rw [hz']
    exact h u' hu' o

end GlobalTheory.PlaneSkewDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateFirst
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem phiC_congr {D : D7} (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem alg_step {l c a a' x y : ℂ} (h1 : x = l * a) (h2 : a = c * a') (h3 : y = l * a') : x = c * y := by
  rw [h1, h2, h3]; ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem baseEmbedding_restriction_eq_coefficientInclusion (fw : FWTie T R κw v₀) : res T (sg0 D A) = T.σ₀ :=
  (congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)

theorem ev_base (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (f : Cu T κw i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κw i)) : ℂ) *
        (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = (O i).s0 := (baseEmbedding_restriction_eq_coefficientInclusion T R κw v₀ fw).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans (O i).hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have h2 := phiC_congr T e hV (O i).hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1))
  have h3 := phi_cE T R O i (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) h
  exact (congrFun (h1.trans h2) h).trans h3.symm

end GlobalTheory.GalLift.BaseEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightInvariantFormGroupConj
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold

theorem cxF_smul_conj_gen : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F)
    (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ),
    (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t), ∀ (η : grp G β) (a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') (y : grp G β),
    GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (η • a) (η * y * η⁻¹) =
      GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a y := by
  intro p _ G v wt Kf f hf K' f' hf' β x t hx η a y

  have ha1 : (η • a).1 = LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K')
      (((toAfF G β x t hx).prod (toP1 G β)) η *
        LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1) := by
    show η • a.1 = _
    conv_lhs => rw [← LeftCosets.mk_rep a.1]
    rfl
  obtain ⟨k, hk, hrep⟩ := LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β))
    (K := Kf.prod K') (((toAfF G β x t hx).prod (toP1 G β)) η *
        LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1)
  rw [← ha1] at hrep
  rw [Subgroup.mem_prod] at hk
  have hF : f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1⁻¹ *
        toAfF G β x t hx (η * y * η⁻¹) *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1) =
      f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
        toAfF G β x t hx y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1) := by
    rw [hrep, ← hf k.1 hk.1 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
        toAfF G β x t hx y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1)]
    congr 1
    simp only [Prod.fst_mul, MonoidHom.prod_apply, map_mul, map_inv]
    group
  have hF' : f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2⁻¹ *
        toP1 G β (η * y * η⁻¹) *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2) =
      f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ *
        toP1 G β y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2) := by
    rw [hrep, ← hf' k.2 hk.2 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ *
        toP1 G β y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2)]
    congr 1
    simp only [Prod.snd_mul, MonoidHom.prod_apply, map_mul, map_inv]
    group

  have hM : minpoly G.F ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      minpoly G.F ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    have e : ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (((η : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *
          ((((η : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C) := by
      simp [Units.val_mul]
    rw [e, minpoly_units_conj]

  obtain ⟨c, hc, hrepl⟩ := rep_smul G v β η a.2
  have hcond : (0 < (star (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β (η * y * η⁻¹)
        (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))) ↔
      (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))) := by
    change (0 < (star (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β (η * y * η⁻¹)
        (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))) ↔ _
    rw [hrepl, fixL_smul_iff G v β _ _ c hc, ← fixL_conj_iff p G v β y η,
      ← pos_iff_smul_toV p G v β η _ c hc]
  unfold cxF
  by_cases hca : (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))))
  · rw [if_pos hca, if_pos (hcond.2 hca), hF, hF', hM]
  · rw [if_neg hca, if_neg (mt hcond.1 hca)]

end GlobalTheory.CxUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.FibreProj

variable {ι : Type} [Fintype ι]


open Classical in
def pol (φ : (ι → ℤ) → ℝ) : ℝ := ∑ S : Finset ι, (-1 : ℝ) ^ S.card * φ fun i => if i ∈ S then -1 else 0


set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.FibreProj.pol_sum {J : Type} (T : Finset J)
    (φ : J → (ι → ℤ) → ℝ) :
    _root_.GlobalTheory.FibreProj.pol (fun n => ∑ j ∈ T, φ j n) =
      ∑ j ∈ T, _root_.GlobalTheory.FibreProj.pol (φ j) := by
  unfold _root_.GlobalTheory.FibreProj.pol
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
private theorem sum_pow_eq_sum_words_prod {R : Type} [CommRing R] (c : ι → R) (D : ℕ) :
    (∑ i, c i) ^ D = ∑ f : Fin D → ι, ∏ k, c (f k) := by
  rw [← Fin.prod_const, Fintype.prod_sum]

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_neg_one_pow_card_range_subset_eq_ite_surjective {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (f : Fin D → ι) :
    ∑ S : Finset ι, (-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0) =
      if Function.Surjective f then (-1) ^ D else 0 := by
  have hr : ∀ t : Finset ι, (∏ i ∈ t, (-1 : R)) *
      ∏ i ∈ Finset.univ \ t, (if i ∉ Set.range f then (1 : R) else 0) =
        (-1) ^ t.card * (if ∀ k, f k ∈ t then 1 else 0) := by
    intro t
    rw [Finset.prod_const, Finset.prod_ite_zero, Finset.prod_const_one]
    have hiff : (∀ i ∈ Finset.univ \ t, i ∉ Set.range f) ↔ ∀ k, f k ∈ t := by
      constructor
      · intro h k
        by_contra hk
        exact h (f k) (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hk⟩) ⟨k, rfl⟩
      · rintro h i hi ⟨k, rfl⟩
        exact (Finset.mem_sdiff.1 hi).2 (h k)
    simp only [hiff]
  calc ∑ S : Finset ι, (-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0)
      = ∑ t ∈ (Finset.univ : Finset ι).powerset, (∏ i ∈ t, (-1 : R)) *
          ∏ i ∈ Finset.univ \ t, (if i ∉ Set.range f then (1 : R) else 0) := by
        rw [Finset.powerset_univ]
        exact Finset.sum_congr rfl fun t _ => (hr t).symm
    _ = ∏ i, ((-1 : R) + if i ∉ Set.range f then 1 else 0) := (Finset.prod_add _ _ _).symm
    _ = _ := by
        split_ifs with hs
        · have h1 : ∀ i, ((-1 : R) + if i ∉ Set.range f then 1 else 0) = -1 := fun i => by
            rw [if_neg (show ¬(i ∉ Set.range f) from not_not.2 (hs i)), add_zero]
          simp only [h1, Finset.prod_const, Finset.card_univ, hD]
        · simp only [Function.Surjective, not_forall] at hs
          obtain ⟨i, hi⟩ := hs
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos (show i ∉ Set.range f from fun h => hi h)]; ring)

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_surjective_words_prod_eq_factorial_prod {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (w : ι → R) :
    ∑ f : Fin D → ι, (∏ k, w (f k)) * (if Function.Surjective f then (-1 : R) ^ D else 0) =
      (-1) ^ D * D.factorial * ∏ i, w i := by
  have hbij : ∀ f : Fin D → ι, Function.Surjective f → Function.Bijective f := fun f hf =>
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨hf, by rw [Fintype.card_fin, hD]⟩
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hprod : ∀ f ∈ Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f),
      (∏ k, w (f k)) * (-1 : R) ^ D = (∏ i, w i) * (-1) ^ D := by
    intro f hf
    rw [← Equiv.prod_comp (Equiv.ofBijective f (hbij f (Finset.mem_filter.1 hf).2)) w]
    rfl
  have e : Fin D ≃ ι := (Fintype.equivFinOfCardEq hD).symm
  have hcard : (Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f)).card =
      D.factorial := by
    calc (Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f)).card
        = (Finset.univ.map ⟨fun σ : Fin D ≃ ι => (σ : Fin D → ι),
            DFunLike.coe_injective⟩).card := by
          congr 1
          ext f
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Function.Embedding.coeFn_mk]
          constructor
          · intro hf
            exact ⟨Equiv.ofBijective f (hbij f hf), rfl⟩
          · rintro ⟨σ, rfl⟩
            exact σ.surjective
      _ = Fintype.card (Fin D ≃ ι) := by rw [Finset.card_map, Finset.card_univ]
      _ = D.factorial := by rw [Fintype.card_equiv e, Fintype.card_fin]
  rw [Finset.sum_congr rfl hprod, Finset.sum_const, hcard, nsmul_eq_mul]
  ring

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_neg_one_pow_card_mul_sum_pow_eq_factorial_prod {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (w : ι → R) :
    ∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then w i else 0) ^ D =
      (-1) ^ D * D.factorial * ∏ i, w i := by
  calc ∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then w i else 0) ^ D
      = ∑ S : Finset ι, ∑ f : Fin D → ι,
          (∏ k, w (f k)) * ((-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [sum_pow_eq_sum_words_prod, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.prod_ite_zero]
        simp only [Finset.mem_univ, true_implies]
        split_ifs <;> ring
    _ = ∑ f : Fin D → ι, (∏ k, w (f k)) *
          (if Function.Surjective f then (-1 : R) ^ D else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.mul_sum, sum_neg_one_pow_card_range_subset_eq_ite_surjective hD f]
    _ = _ := sum_surjective_words_prod_eq_factorial_prod hD w


set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
theorem _root_.GlobalTheory.FibreProj.pol_pow {R : Type} [CommRing R]
    [Algebra ℝ R] (z : ι → R) (Φ : R →ₗ[ℝ] ℝ) {D : ℕ} (hD : Fintype.card ι = D) :
    _root_.GlobalTheory.FibreProj.pol (fun n => Φ ((∑ i, (n i : ℝ) • z i) ^ D)) =
      D.factorial * Φ (∏ i, z i) := by
  unfold _root_.GlobalTheory.FibreProj.pol
  have hsum : ∀ S : Finset ι, (∑ i, (((if i ∈ S then -1 else 0 : ℤ) : ℝ)) • z i) =
      ∑ i, if i ∈ S then -z i else 0 := by
    intro S
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp only [hsum]
  have hterm : ∀ (k : ℕ) (x : R), Φ ((-1 : R) ^ k * x) = (-1 : ℝ) ^ k * Φ x := by
    intro k x
    rw [← smul_eq_mul ((-1 : ℝ) ^ k), ← map_smul, Algebra.smul_def, map_pow, map_neg, map_one]
  have h1 : ((-1 : R) ^ D) * (-1) ^ D = 1 := by rw [← mul_pow]; simp
  have hfinal : Φ ((-1 : R) ^ D * D.factorial * ∏ i, -z i) = D.factorial * Φ (∏ i, z i) := by
    rw [Finset.prod_neg, Finset.card_univ, hD]
    calc Φ ((-1) ^ D * D.factorial * ((-1) ^ D * ∏ i, z i))
        = Φ ((D.factorial : ℝ) • ∏ i, z i) := by
          congr 1
          rw [Algebra.smul_def, map_natCast]
          linear_combination (↑D.factorial * ∏ i, z i) * h1
      _ = _ := by rw [map_smul, smul_eq_mul]
  calc ∑ S : Finset ι, (-1 : ℝ) ^ S.card * Φ ((∑ i, if i ∈ S then -z i else 0) ^ D)
      = Φ (∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then -z i else 0) ^ D) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [hterm]
    _ = Φ ((-1 : R) ^ D * D.factorial * ∏ i, -z i) :=
        congrArg Φ (sum_neg_one_pow_card_mul_sum_pow_eq_factorial_prod hD fun i => -z i)
    _ = _ := hfinal

end GlobalTheory.FibreProj
end
end

