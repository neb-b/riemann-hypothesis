module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCompletionIntegersLeIntAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Export

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)


variable {YS v₀ i j b} in
theorem mem_range_realRd_of_sum {ν : ℂ} (hν : ν ≠ 0) {g : GA D (Wc D j) → ℂ} {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ k, ∃ y, ρ.e i b y = z k) (x : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h : ν • g = ∑ k, z k • evW YS v₀ j (Subtype.val (x k))) : g ∈ Set.range (realRd YS v₀ hρ i j b ν) := by
  choose y hy using hz
  exact (mem_range_realRd_iff YS v₀ hρ i j b hν g).2 ⟨n, y, x, h.trans (Finset.sum_congr rfl fun k _ => by rw [← hy k])⟩


variable (ρ) in
def UnrComb (Φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (k L : Type) (_ : Field k) (_ : NumberField k) (_ : Field L) (_ : NumberField L) (_ : Algebra k L)
    (ι : k →+* FractionRing (D.ntw.O i)) (σ : L →+* ℂ), Normal k L ∧
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime], ((D.ntw.l i : ℕ) : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 k) P) ∧
    (∀ a, σ (algebraMap k L a) = ρ.e i b (ι a)) ∧
    ∃ (n : ℕ) (a : Fin n → L) (x : Fin n → NX.FmK S ((j : ℕ) + 1)), Φ = ∑ c, σ (a c) • evW YS v₀ j (Subtype.val (x c))


variable {YS v₀ i j b}

end Export

section Any

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}


variable (ρ Y i j b) in
def xiLin (Q : Finset (Pl D.host.E)) (M : ℕ) (h : GA D (Vc D j)) (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ) where
  toFun P := ρ.xi i j b Y Q M h P a
  map_add' P P' := by funext g; simp only [Base.xiCoef_apply, map_add (f := _), Pi.add_apply]
  map_smul' c P := by funext g; simp only [Base.xiCoef_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem Faithful.mem_range_of_smul {rd : Rd ρ Y i j b} (hF : Faithful rd) {g : GA D (Wc D j) → ℂ} (hg : g ≠ 0) {u : ℂ}
    (h1 : g ∈ Set.range rd) (h2 : u • g ∈ Set.range rd) : ∃ y, ρ.e i b y = u := by
  obtain ⟨f, rfl⟩ := h1
  obtain ⟨f', h2⟩ := h2
  have hf : f ≠ 0 := fun h => hg (by rw [h, map_zero])
  have hdep : ¬ LinearIndependent (FractionRing (X.O i)) ![f, f'] := fun h => by
    have h3 : LinearIndependent ℂ ![rd f, rd f'] := by
      convert hF 2 _ h using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h3 u (-1) (by rw [h2]; simp)).2
    simp at this
  rw [LinearIndependent.pair_iff' hf] at hdep
  push Not at hdep
  obtain ⟨y, rfl⟩ := hdep
  rw [map_smulₛₗ] at h2
  exact ⟨y, smul_left_injective ℂ hg h2⟩

theorem mem_range_of_small (rd : Rd ρ Y i j b) (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → Φ P ∈ Set.range rd)
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (ρ.eO i b).range h) :
    Φ P ∈ Set.range rd := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ Φ P' ∈ Set.range rd := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, 0, by rw [map_zero, map_zero]⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂, e2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, f₁ + f₂, by rw [map_add (f := _), map_add (f := _), e1, e2]⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, o • f₁, by rw [rd_smul, map_smul, e1]⟩
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Any

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

variable {YS v₀ i j b}

end Main

section Core
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem exists_evW_eq_phiC (t : FWTie T Rl.toRealDat κ v₀) (ht : t.Evaluates) (j : Fin D.R.m)
    (hσ : GoodEmb T.Q.c (res T (sg0 D A3.A))) (hV : T.V ((j : ℕ) + 1) (res T (sg0 D A3.A)) = Wc D j) (f : Cu T κ j) :
    ∃ x : NX.FmK S ((j : ℕ) + 1), evW YS v₀ j (Subtype.val x) = phiC T hV (wtA (κ j)) (f : T.R ((j : ℕ) + 1)) := by
  have hx : (YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) ∈ (S.A ((j : ℕ) + 1)).WK := by
    refine ((YS.fi j).wk _).2 ?_
    have e1 : (YS.fi j).e ((YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)) =
        ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) := LinearEquiv.apply_symm_apply _ _
    rw [e1]
    exact (t.e j f).2
  refine ⟨⟨_, hx⟩, Eq.trans ?_ (ht j (sg0 D A3.A) hσ hV f)⟩
  have e2 := LinearEquiv.apply_symm_apply (YS.fi j).e ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [e2]
  rfl

end Core
end GlobalTheory.SeriesTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddSumEqProd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConst

theorem one_add_sum_eq_prod {R ι : Type} [CommRing R] [DecidableEq ι] (s : Finset ι) (f a : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    1 + ∑ i ∈ s, f i * (a i - 1) = ∏ i ∈ s, (1 + f i * (a i - 1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj,
      ← ih fun k hk l hl hkl => h k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl]
    have h0 : f j * (a j - 1) * ∑ k ∈ s, f k * (a k - 1) = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hne : j ≠ k := fun e => hj (e ▸ hk)
      have := h j (Finset.mem_insert_self j s) k (Finset.mem_insert_of_mem hk) hne
      calc f j * (a j - 1) * (f k * (a k - 1)) = (f j * f k) * ((a j - 1) * (a k - 1)) := by ring
        _ = 0 := by rw [this, zero_mul]
    linear_combination (-1 : R) * h0

theorem chr_inv_val {D : D7} (c : (AE D)ˣ →* Circle) (x : (AE D)ˣ) : ((c x⁻¹ : Circle) : ℂ) = ((c x : Circle) : ℂ)⁻¹ := by
  rw [map_inv, Circle.coe_inv]

theorem chrW_val {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t' : T0) (x : (AE D)ˣ) :
    (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ) =
      ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.xi t' x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹ := by
  unfold Lift.chrTh LevCh.mu Lift.tup
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]

end GlobalTheory.FlatConst


open GlobalTheory.FlatConst in
theorem GlobalTheory.FlatConst.flat_const : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E) (n : ℕ) (x : (AE D)ˣ), (∀ PP ∈ R.Q t, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ R.Q t, es PP) * cA D (∑ PP ∈ R.Q t, es PP) = 0 → (∀ PP ∈ R.Q t, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ n - 1) → ∃ b : ℂ, (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ (b * ∏ PP ∈ R.Q t, (((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹) ^ n) = b * ∏ PP ∈ R.Q t, (((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹) ^ n) ∧ (∀ t' : T0, (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ = b * ((R.xi t' x⁻¹ : Circle) : ℂ)) ∧ (∀ (t' : T0) (S : Finset (Pl D.host.E)), S ⊆ R.Q t' → ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, ∃ s : (AE D)ˣ, ∏ PP ∈ S, ((R.xiR t' PP (u PP) : ℂˣ) : ℂ) = ((R.xi t' s : Circle) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F hC i t es ϖ n x hes hc hϖ hx
  set Q := R.Q t with hQ

  have hidem : ∀ PP ∈ Q, cA D (es PP) * cA D (es PP) = cA D (es PP) := fun PP hP =>
    Formalism.IndefR.Fin.LevelGroupLemmas.isIdem_cA (hes PP hP).1.1
  have hϖ0 : ∀ PP ∈ Q, star ((ϖ PP : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun PP hP h0 => by
    have : (ϖ PP : D.host.E) = 0 := by rw [← star_star ((ϖ PP : 𝓞 D.host.E) : D.host.E), h0, star_zero]
    exact (hϖ PP hP).2 (by rw [show ϖ PP = 0 from RingOfIntegers.ext this]; exact zero_mem _)
  let y : Q → (AE D)ˣ := fun P =>
    Formalism.L2.JoinChr.locU (hidem P.1 P.2) ((Units.mk0 (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) (hϖ0 P.1 P.2)) ^ n)
  have hyv : ∀ P : Q, ((y P : (AE D)ˣ) : AE D) = 1 + cA D (es P.1) * (incA D (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) ^ n - 1) := by
    intro P
    show Formalism.L2.JoinChr.locE D _ _ = _
    unfold Formalism.L2.JoinChr.locE
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
  have horth : ∀ P ∈ Q.attach, ∀ P' ∈ Q.attach, P ≠ P' → cA D (es P.1) * cA D (es P'.1) = 0 := by
    intro P _ P' _ hne
    rw [← map_mul, Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_orth hes rfl hc P.2 P'.2 (fun e => hne (Subtype.ext e)), map_zero]
  have hxy : x = ∏ P ∈ Q.attach, y P := by
    apply Units.ext
    rw [Units.coe_prod, hx]
    simp only [hyv]
    rw [← Finset.sum_attach Q (fun PP => cA D (es PP) * (incA D (star ((ϖ PP : 𝓞 D.host.E) : D.host.E)) ^ n - 1))]
    exact one_add_sum_eq_prod Q.attach (fun P => cA D (es P.1)) (fun P => incA D (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) ^ n) horth

  have hg : ∀ PP ∈ Q, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hP =>
    GlobalTheory.StdFrames.g_not_mem (hC.lev.Q_pl t) hP
  have hgc : ∀ PP ∈ Q, ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    intro PP hP k hk
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have : Formalism.L2.DIV.starOHom ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hk
      rwa [map_natCast] at this
    apply hg PP hP
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk'
  have unrM : ∀ PP ∈ Q, (R.C.mu0 i).UnrAt (Formalism.L2.DIV.conjPl PP) := fun PP hP =>
    (R.C.isMu0 i).unr _ fun k => hgc PP hP k
  have unrE : ∀ PP ∈ Q, R.C.eta.UnrAt (Formalism.L2.DIV.conjPl PP) := fun PP _ => R.C.isEta.unr _

  have hvM : ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = ∏ PP ∈ Q, (((R.C.mu0 i).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
    have := map_prod (Circle.coeHom.comp (R.mu0 ((i : ℕ) + 1))) y Q.attach
    rw [← hxy] at this
    show (Circle.coeHom.comp (R.mu0 ((i : ℕ) + 1))) x = _
    rw [this, ← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact _root_.GlobalTheory.ConjLocVal.value_at_conj_place D P.1 (es P.1) (ϖ P.1) _ _ n (y P) (hes P.1 P.2) (hϖ P.1 P.2).1 (hϖ P.1 P.2).2 (hC.lev.mu0 i)
      (unrM P.1 P.2) (hyv P)
  have hvE : ((R.eta x : Circle) : ℂ) = ∏ PP ∈ Q, ((R.C.eta.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
    have := map_prod (Circle.coeHom.comp R.eta) y Q.attach
    rw [← hxy] at this
    show (Circle.coeHom.comp R.eta) x = _
    rw [this, ← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact _root_.GlobalTheory.ConjLocVal.value_at_conj_place D P.1 (es P.1) (ϖ P.1) _ _ n (y P) (hes P.1 P.2) (hϖ P.1 P.2).1 (hϖ P.1 P.2).2 hC.lev.eta
      (unrE P.1 P.2) (hyv P)
  set sq : Pl D.host.E → ℂ := fun PP => ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) with hsq
  set v : Pl D.host.E → ℂ := fun PP => (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) with hv
  refine ⟨(((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹)⁻¹, ?_, ?_, ?_⟩
  · intro τ hτ
    have key : (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹)⁻¹ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n =
        ∏ PP ∈ Q, ((v PP * sq PP)⁻¹) ^ n := by
      rw [hvM, hvE]
      simp only [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [hv, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      ring
    show τ (_ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n) = _ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n
    rw [key, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [map_pow, map_inv₀]
    congr 2
    exact GlobalTheory.T.fixesUntwistedLiftData_conjugatePrime_value_sqrtNorm T R i τ PP hτ (hg PP hP)
  · intro t'
    have h1 := chrW_val R i t' x
    have h2 := chr_inv_val (R.xi t') x
    simp only [h1, h2]
    ring
  · intro t' S hS u
    exact GlobalTheory.FlatConj.prod_val (R.xi t') S (fun PP => ((R.xiR t' PP (u PP) : ℂˣ) : ℂ))
      fun PP hP => GlobalTheory.FlatConj.xiR_val hC t' PP (hS hP) (u PP)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBall
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BallSup

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem nrm_le_one_of_mem_locBall {f : NX.FmK S ((j : ℕ) + 1)} (hf : f ∈ locBall YS fw iC b j)
    (y : (Rl.FW j).Pt (placeC YS iC b)) :
    (Rl.FW j).nrm (placeC YS iC b) y (fw.e j (cuspOf YS fw j f)) ≤ 1 := by
  rw [fw.nrm_eq, Core.nrmM_le_one_iff]
  obtain ⟨q, hq⟩ := (fw.pt j (placeC YS iC b) y).2
  rcases q with ⟨qv, T, io, e, ho, y', hy', eta, heta, rfl⟩
  obtain ⟨k, hk⟩ := ReadExist.exists_isReading (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io e ho hy'
  obtain ⟨z, hz⟩ := PtC.exists_of_reading hk y' hy'
  have h1 := hf z
  rw [hz _ _ _ (cuspOf_mem_sec YS fw j f)] at h1
  obtain ⟨a, ha⟩ := (hk.int _).1 h1
  rw [← hq]
  change 0 ≤ nval T.V e (evI y' _)
  by_cases hx : evI y' (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) = 0
  · rw [hx, nval_zero]; exact le_top
  · rw [nval_of_ne hx]
    exact EReal.coe_nonneg.2 (div_nonneg (Int.cast_nonneg
      ((GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff _).1 ⟨a, ha⟩)) (Nat.cast_nonneg _))

theorem one_tmul_mem_Bsup_of_mem_locBall
    (hiC : ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range)
    (f : NX.FmK S ((j : ℕ) + 1)) (hf : f ∈ locBall YS fw iC b j) :
    (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall D.what₂.LL T0.Q.c.F _ _ _ (Rl.FW j)
    (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).2 (placeC YS iC b) (fw.e j (cuspOf YS fw j f))
    (nrm_le_one_of_mem_locBall YS fw iC b j hf)
  rw [e_cuspOf] at hsM
  set c : S.Ks := (YS.fi j).eK.symm (s : T0.Q.c.F) with hcdef
  have hc : (YS.fi j).e (c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1) = s • (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := by
    rw [← algebraMap_smul D.what₂.LL c, LinearEquiv.map_smul, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply,
      algebraMap_smul]
    exact (algebraMap_smul T0.Q.c.F s _)
  have hcM : c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK := by
    rw [(YS.fi j).mkK, hc]; exact hsM

  have hgen : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) ∈ NX.Bsup S i ((j : ℕ) + 1) b :=
    Submodule.subset_span ⟨c • f, hcM, rfl⟩
  have heK : eKs YS c = (s : T0.Q.c.F) := by
    apply (algebraMap T0.Q.c.F D.what₂.LL).injective
    rw [eKs_LL, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ : ∃ x : FractionRing (D.ntw.O i), x = NX.ιK S i b c := ⟨_, rfl⟩
  have hn1 : ‖iC x‖ = 1 := by
    rw [hx]
    change ‖embS S iC b c‖ = 1
    rw [← embC_eKs YS iC b, heK]
    refine le_antisymm (norm_int_le_one _ s) (not_lt.1 fun h => hs ?_)
    exact (mem_placeAt _ s).2 h
  have hne : x ≠ 0 := fun h => by
    rw [h, map_zero, norm_zero] at hn1; exact zero_ne_one hn1
  obtain ⟨u, hu⟩ := (hiC x⁻¹).1 (by rw [map_inv₀, norm_inv, hn1, inv_one])
  have key : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) =
      u • (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) := by
    rw [← algebraMap_smul (FractionRing (D.ntw.O i)) u, hu]
    have h1 : (c • (1 : NX.KB S i b)) = (show NX.KB S i b from x) := by
      rw [Algebra.smul_def, mul_one, hx]; rfl
    change (1 : NX.KB S i b) ⊗ₜ[S.Ks] f =
      (show NX.KB S i b from x⁻¹) • ((1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f) : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1))
    rw [← TensorProduct.smul_tmul, h1, TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    exact (inv_mul_cancel₀ hne).symm
  rw [key]
  exact Submodule.smul_mem _ u hgen

end BallSup

theorem one_tmul_mem_Bsup : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j f hf
  exact one_tmul_mem_Bsup_of_mem_locBall YS fw iC b j hiC f hf

end GlobalTheory.GeoTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormsDetTwistMulRational
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistRat

theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N → ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := GlobalTheory.TwistRat.Field.curveOver_of_rayIn

theorem twist_mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := GlobalTheory.TwistValues.mem_fieldRange

theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := GlobalTheory.TwistFinPart.twist_eq_of_finHom

theorem twist_mul_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := GlobalTheory.TwistLeft.twist_left

theorem twist_mul_right : ∀ (D : D7) (V : HSp D) (M pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsAuxiliarySplitSquarefreeLevel D M pd → IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ u : GA D V, Formalism.L2.Pj.gLat V u = ↑(Formalism.L2.Pj.latHat V) → GlobalTheory.Member.FinCong V (M * pd) u → ∀ h : GA D V, dd (h * u) = dd h := GlobalTheory.TwistRat.Right.dd_mul_right

theorem muVal_cast {D : D7} {V W : HSp D} (h : V = W) (χ : (AE D)ˣ →* Circle) (dd : GA D W → ℂ) (hd : MuVal W χ dd) :
    MuVal V χ (castDict h.symm dd) := by
  subst h; exact hd

theorem castDict_mul {D : D7} {V W : HSp D} (h : V = W) (dd : GA D W → ℂ) (φ : GA D V → ℂ) :
    castDict h (fun g => castDict h.symm dd g * φ g) = fun g => dd g * castDict h φ g := by
  subst h; rfl

theorem isRat_twist : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd →
      ∀ φ : GA D (Wc D i) → ℂ, IsRat T i hV C (κ i) φ → IsRat T i hV C (κ i) (fun g => dd g * φ g) := by
  intro hRF D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hGC δ δc hTw dd hdd φ hφ
  obtain ⟨hU, -, hAux, -, hRay⟩ := hGC
  obtain ⟨φ', hφ', rfl⟩ := hφ
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hpd : 0 < C.d.pd := hAux.1.pos
  have hN3 : 3 ≤ T.Q.l.M * C.d.pd := le_trans T.Q.l.three_le (Nat.le_mul_of_pos_right _ hpd)
  have hcurve : GlobalTheory.CompRat.CurveOver T.Q.H C.d.c₂.F (T.Q.l.M * C.d.pd) :=
    curveOver_of_rayIn hRF D T.Q hL.pins.1 _ hN3 C.d.c₂.F C.σ₂ hRay
  set dd' : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm dd with hdd'
  have hdd2 : MuVal _ δc dd' ∨ MuVal _ δc⁻¹ dd' :=
    hdd.imp (muVal_cast hV δc dd) (muVal_cast hV δc⁻¹ dd)
  have hval := twist_mem_fieldRange D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2
  choose w hw using fun g => RingHom.mem_fieldRange.1 (hval g)
  have hinj : ∀ g g', dd' g = dd' g' → w g = w g' := fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL ((i : ℕ) + 1) ⟨Nat.succ_pos _, i.2⟩ T.σ₀ rfl C hU
    (T.Q.l.M * C.d.pd) (Nat.mul_pos (by have := T.Q.l.three_le; omega) hpd) (by rw [hlev]) (Or.inr hcurve) w
    (fun h h' hh => hinj _ _ (twist_eq_of_finHom D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 h h' hh))
    (fun γ hγ h => hinj _ _ (twist_mul_left D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 γ hγ h))
    (fun u hu1 hu2 h => hinj _ _ (twist_mul_right D _ T.Q.l.M C.d.pd _ C.σ₂ δ δc hAux hTw dd' hdd2 u hu1 (hlev ▸ hu2) h))
    (wtA (κ i)) (κ i).n).1 φ' hφ'
  refine ⟨_, key, ?_⟩
  simp only [hw]
  exact castDict_mul hV dd φ'

end GlobalTheory.TwistRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_character_artin_tame_galois_eq_tame_value : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (rc : Recip D D.nd.Om), rc.Good → ∀ (R : Type) [CommRing R] (f : R →+* ℂ) (φ : G D.host.E D.nd.Om →* Rˣ), IsOpen (φ.ker : Set (G D.host.E D.nd.Om)) → ∀ (PP : Pl D.host.E) (m : ℕ), ((m : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A PP → ∀ σ ∈ Ine (F := D.host.E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) → Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP → ∀ c : (kP PP)ˣ →* Circle, IsResAt (GlobalTheory.SeriesTie.charOf rc f φ) PP c → ∀ (e : ℤ) (u : 𝓞 D.host.E), u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((c z : Circle) : ℂ) ^ e = f (NX.tameVal φ PP e u).1 := by
  first | exact @GlobalTheory.TameResRead.res_zpow_eq_tameVal | exact GlobalTheory.TameResRead.res_zpow_eq_tameVal | (intros; apply GlobalTheory.TameResRead.res_zpow_eq_tameVal <;> assumption)
end

