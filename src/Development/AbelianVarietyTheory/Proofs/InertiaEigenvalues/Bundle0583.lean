module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotient
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameHeightOfJumpsLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.Lower

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem evW_E_ne_zero (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) : bk.evW bk.E ≠ 0 := by
  intro h
  have h0 : bk.ev bk.E = 0 := inclW_injective (h.trans (map_zero _).symm)
  have hu := (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1
  have h1 := hτ.1
  rw [h0, zero_mul] at h1
  have h2 := (hu.map (frobW l)).ne_zero
  rw [frobW_inclW, h1, map_zero] at h2
  exact h2 rfl

theorem map_smul' {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

def raise (bk : BK K) {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (k : ℕ) :
    Frame bk (N + k) d ρ where
  T := F.T
  unit := F.unit
  A := bk.E ^ k • F.A
  A' := bk.E ^ k • F.A'
  A_mul := by
    rw [Matrix.smul_mul, Matrix.mul_smul, F.A_mul, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2; ring
  φ := by
    rw [map_smul', Matrix.mul_smul, ← F.φ, smul_smul, ← map_pow, ← map_pow, ← map_mul, ← pow_add, add_comm]
  fix := F.fix
  ε := F.ε
  gal := F.gal

def lower (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {N₀ k d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (F : Frame bk (N₀ + k) d ρ) (A₀ A₀' : Matrix (Fin d) (Fin d) bk.S) (hA : F.A = bk.E ^ k • A₀)
    (hA' : F.A' = bk.E ^ k • A₀') : Frame bk N₀ d ρ where
  T := F.T
  unit := F.unit
  A := A₀
  A' := A₀'
  A_mul := by
    have h := F.A_mul
    rw [hA, hA', Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
    refine Matrix.ext fun i j => ?_
    have h2 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
    have hE : bk.E ^ k * bk.E ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ bk.E_ne_zero) (pow_ne_zero _ bk.E_ne_zero)
    apply mul_left_cancel₀ hE
    rw [h2]; ring
  φ := by
    have h := F.φ
    rw [hA, map_smul', Matrix.mul_smul] at h
    refine Matrix.ext fun i j => ?_
    have h2 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
    have hE : bk.evW (bk.E ^ k) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (evW_E_ne_zero bk hτ)
    apply mul_left_cancel₀ hE
    rw [← h2, map_pow]; ring
  fix := F.fix
  ε := F.ε
  gal := F.gal

theorem exists_frame_of_jumps_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N N₀ d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ), F.IsDR → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → ∃ F₀ : Frame bk N₀ d ρ, F₀.T = F.T ∧ F₀.ε = F.ε := by
  intro l _ K bk τ hτ C hC N N₀ d ρ F hF H hH
  rcases le_total N N₀ with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨raise bk F k, rfl, rfl⟩
  · obtain ⟨Y, Y', hY, -⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N d ρ F.toPre
    obtain ⟨hdA, hdA'⟩ := (GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles l K bk τ hτ C hC N d ρ F Y hF hY H).2 N₀ h hH
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left] at hdA hdA'
    choose A₀ hA₀ using hdA
    choose A₀' hA₀' using hdA'
    refine ⟨lower bk hτ F (Matrix.of A₀) (Matrix.of A₀') ?_ ?_, rfl, rfl⟩
    · ext i j; simp [hA₀ i j]
    · ext i j; simp [hA₀' i j]

end GlobalTheory.BKLim.Lower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
  GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OChoose

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
    rw [show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap] at h1
    have h2 := Int.isUnit_iff_natAbs_eq.1 h1
    have h3 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases Nat.pow_eq_one.1 h2 with h | h
    · exact hp.one_lt.ne' h
    · exact h3.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

theorem exists_wild_inertia_cyclotomic_generator (D : D7) (i : D.nd.Loc) : ∃ g0, IsWildInertiaCyclotomicElement D.nd i g0 := by
  by_cases ht : ∃ k, D.nd.l i = D.host.g k
  · obtain ⟨k, hk⟩ := ht
    obtain ⟨g0, h1, h2, h3⟩ := GlobalTheory.T.exists_wildInertia_generating_cyclotomicValue D i k hk
    exact ⟨g0, ⟨h1, h2⟩, fun _ => h3⟩
  · obtain ⟨w, hw⟩ := placesOver_nonempty D.host.E (D.nd.l i) (D.nd.lPrime i).out
    obtain ⟨g, hg, hc⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
    exact ⟨g, ⟨⟨w, hw, hg⟩, 1, by simpa using hc⟩, fun h => absurd h ht⟩

theorem exists_fin_roots {p : ℂ[X]} {t : ℕ} (hm : p.Monic) (hd : p.natDegree = t) :
    ∃ α : Fin t → ℂ, (∀ c, α c ∈ p.roots) ∧ p = ∏ c, (X - C (α c)) := by
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hp := (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard).symm
  obtain ⟨l, hl⟩ : ∃ l : List ℂ, (l : Multiset ℂ) = p.roots := Quotient.exists_rep _
  have hlen : l.length = t := by rw [← hd, ← hcard, ← hl, Multiset.coe_card]
  subst hlen
  refine ⟨fun c => l.get c, fun c => hl ▸ Multiset.mem_coe.2 (List.get_mem l c), ?_⟩
  conv_lhs => rw [hp, ← hl]
  rw [Multiset.map_coe, Multiset.prod_coe]
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

theorem blockPol_iota (D : D7) (i : D.nd.Loc) {rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i)) {π : D.nd.X i} {g0 : GE D.nd}
    {L : ℕ} {eB e1 X0 : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hc : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice D.R.t (D.nd.T i) rep ρ (D.nd.chi i) π g0 L eB e1 X0) (x : D.nd.X i) :
    ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO D.nd D.naut i)).Monic ∧
      ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO D.nd D.naut i)).natDegree = D.R.t := by
  obtain ⟨hr, -, -, hX1, hX2, -⟩ := GlobalTheory.ConsExists.choice_facts hS.1 hS.2.2.2.1 hc
  obtain ⟨hm, hd⟩ := GlobalTheory.ConsExists.blockPol_monic (congrFun hc.1.2.2.1 x) (hr x) (congrFun hX1 x) (congrFun hX2 x)
  have hinj : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.toFr (D.nd.O i)) :=
    IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have hm' := Polynomial.monic_of_injective hinj hm
  rw [Polynomial.natDegree_map_eq_of_injective hinj] at hd
  exact ⟨hm'.map _, (hm'.natDegree_map _).trans hd⟩

end GlobalTheory.OChoose

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveDescentPrismCover
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.CoverDesc

def solSub {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C) (p q : Hom C D)
    (hpq : p.comp h = q.comp h) (E : Matrix (Fin d) (Fin d) D.A) :
    letI := h.f.toAlgebra; Submodule B.A (Fin d → C.A) :=
  letI := h.f.toAlgebra
  { carrier := {z | (fun i => p.f (z i)) = E.mulVec fun i => q.f (z i)}
    add_mem' := by
      intro a b ha hb
      change (fun i => p.f (a i + b i)) = E.mulVec fun i => q.f (a i + b i)
      have e1 : (fun i => p.f (a i + b i)) = (fun i => p.f (a i)) + fun i => p.f (b i) := by
        funext i; exact map_add _ _ _
      have e2 : (fun i => q.f (a i + b i)) = (fun i => q.f (a i)) + fun i => q.f (b i) := by
        funext i; exact map_add _ _ _
      rw [e1, e2, Matrix.mulVec_add]
      exact congrArg₂ (· + ·) ha hb
    zero_mem' := by
      change (fun i => p.f 0) = E.mulVec fun i => q.f 0
      simp only [map_zero]
      exact (Matrix.mulVec_zero _).symm
    smul_mem' := by
      intro b z hz
      change (fun i => p.f (h.f b * z i)) = E.mulVec fun i => q.f (h.f b * z i)
      have hc : p.f (h.f b) = q.f (h.f b) := congrArg (fun k : Hom B D => k.f b) hpq
      have e1 : (fun i => p.f (h.f b * z i)) = p.f (h.f b) • fun i => p.f (z i) := by
        funext i; exact map_mul _ _ _
      have e2 : (fun i => q.f (h.f b * z i)) = p.f (h.f b) • fun i => q.f (z i) := by
        funext i; rw [map_mul, ← hc]; rfl
      rw [e1, e2, Matrix.mulVec_smul]
      exact congrArg _ hz }

theorem lift_mod {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {B C D : Obj l ↥(OL K)}
    (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hc : Cover h) (hpo : IsPO h h p q)
    (v : Fin d → C.A ⧸ adI C ^ 1)
    (hv : (fun i => qmap p 1 (v i)) =
      ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ 1))).mulVec fun i => qmap q 1 (v i)) :
    ∃ z : Fin d → C.A, (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) ∧
      ∀ i, Ideal.Quotient.mk (adI C ^ 1) (z i) = v i := by
  choose z₀ hz₀ using fun i => Ideal.Quotient.mk_surjective (I := adI C ^ 1) (v i)
  obtain rfl : (fun i => Ideal.Quotient.mk (adI C ^ 1) (z₀ i)) = v := funext hz₀
  have hyp : ∀ i, p.f (z₀ i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z₀ j)) i ∈ adI D ^ 1 := by
    intro i
    rw [← Ideal.Quotient.eq]
    have e := congrFun hv i
    simp only [qmap_mk] at e
    exact e.trans (RingHom.map_mulVec _ _ _ i).symm
  have H := GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal l K bk d S B C D h f p q hc hpo z₀ hyp
  exact ⟨H.choose, H.choose_spec.2, fun i => Ideal.Quotient.eq.2 (H.choose_spec.1 i)⟩


set_option maxHeartbeats 1600000 in
theorem exists_descent : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B.A P) (_ : Module.Finite B.A P) (_ : Module.Projective B.A P) (u : P →ₛₗ[h.f] (Fin d → C.A)), SemiBC u ∧ ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i) := by
  intro l _ K bk d S B C h f hc
  obtain ⟨D, p₀, q₀, hpo⟩ := hc.stable.po C h
  have hcomm : ∀ b, p₀.f (h.f b) = q₀.f (h.f b) := fun b => congrArg (fun k : Hom B D => k.f b) hpo.comm
  letI : Algebra (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := (qmap h 1).toAlgebra
  obtain ⟨N₁, hN₁, hfin, hproj, hbc⟩ := GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p₀ q₀ hc hpo 1
  haveI hcB : IsAdicComplete (adI B ^ 1) B.A := by rw [pow_one]; exact B.complete
  obtain ⟨P, _, _, _, _, u₁, hu₁⟩ := _root_.GlobalTheory.BSP.LiftProj.exists_lift B.A (adI B ^ 1) ↥N₁
  letI : Algebra B.A C.A := h.f.toAlgebra
  haveI : IsScalarTower B.A (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := IsScalarTower.of_algebraMap_eq (fun b => rfl)
  have hs : ∀ (b : B.A) (y : ↥N₁), (Ideal.Quotient.mk (adI B ^ 1) b) • y = b • y := fun b y => Subtype.ext rfl
  let u₁' : P →ₗ[B.A] ↥N₁ := { toFun := fun x => u₁ x, map_add' := fun x y => u₁.map_add x y, map_smul' := fun b x => (u₁.map_smulₛₗ b x).trans (hs b (u₁ x)) }
  have hb1 : IsBaseChange (B.A ⧸ adI B ^ 1) u₁' := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A (B.A ⧸ adI B ^ 1) P ↥N₁ u₁ u₁' (fun x => rfl)).1 hu₁
  have hb2 := hb1.comp hbc
  let M := solSub h p₀ q₀ hpo.comm (S.ε (p₀.comp f) (q₀.comp f))
  have memM : ∀ z, z ∈ M ↔ (fun i => p₀.f (z i)) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec fun i => q₀.f (z i) := fun z => Iff.rfl
  have memN : ∀ z : Fin d → C.A, z ∈ M → (fun i => Ideal.Quotient.mk (adI C ^ 1) (z i)) ∈ N₁ := by
    intro z hz
    rw [hN₁]
    funext i
    simp only [qmap_mk]
    have e : p₀.f (z i) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec (fun j => q₀.f (z j)) i := congrFun ((memM z).1 hz) i
    exact (congrArg (Ideal.Quotient.mk (adI D ^ 1)) e).trans (RingHom.map_mulVec _ _ _ i)
  let π : M →ₗ[B.A] ↥N₁ :=
    { toFun := fun z => ⟨fun i => Ideal.Quotient.mk (adI C ^ 1) (z.1 i), memN z.1 z.2⟩
      map_add' := fun a b => Subtype.ext (funext fun i => map_add _ _ _)
      map_smul' := fun b z => Subtype.ext (funext fun i => map_mul _ _ _) }
  have hπ : Function.Surjective π := by
    intro n
    have H := lift_mod S h f p₀ q₀ hc hpo n.1 ((hN₁ n.1).1 n.2)
    exact ⟨⟨H.choose, (memM _).2 H.choose_spec.1⟩, Subtype.ext (funext H.choose_spec.2)⟩
  have HG := Module.projective_lifting_property π u₁' hπ
  let g := HG.choose
  have hg : π ∘ₗ g = u₁' := HG.choose_spec
  let u' : P →ₗ[B.A] (Fin d → C.A) := M.subtype ∘ₗ g
  let u : P →ₛₗ[h.f] (Fin d → C.A) :=
    { toFun := fun x => u' x, map_add' := fun x y => u'.map_add x y, map_smul' := fun b x => u'.map_smul b x }
  have huM : ∀ x, u x ∈ M := fun x => (g x).2
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, u, ?_, ?_⟩
  · haveI := C.complete
    have hV : IsBaseChange C.A u' := by
      have hgq := (IsBaseChange.linearMap C.A (C.A ⧸ adI C ^ 1)).finitePow (Fin d)
      refine _root_.GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient B.A C.A (adI C ^ 1) ?_ P (Fin d → C.A) _ u' _ hgq ?_
      · exact le_trans (Ideal.pow_le_self one_ne_zero) (IsAdicComplete.le_jacobson_bot _)
      · have heq : ((Algebra.linearMap C.A (C.A ⧸ adI C ^ 1)).compLeft (Fin d)).restrictScalars B.A ∘ₗ u' =
            (N₁.subtype.restrictScalars B.A).comp u₁' := by
          refine LinearMap.ext fun x => funext fun i => ?_
          exact congrArg (fun y : ↥N₁ => y.1 i) (LinearMap.congr_fun hg x)
        rw [heq]; exact hb2
    exact (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A C.A P (Fin d → C.A) u u' (fun x => rfl)).2 hV
  · intro Q p q hpq x
    have HC := GlobalTheory.T.prismPushoutModAdicPow_universal l _ B C C D h h p₀ q₀ hpo Q p q hpq
    obtain ⟨c, ⟨hcp, hcq⟩, -⟩ := HC
    subst hcp hcq
    have hx := (memM _).1 (huM x)
    rw [show (c.comp p₀).comp f = c.comp (p₀.comp f) from rfl, show (c.comp q₀).comp f = c.comp (q₀.comp f) from rfl,
      ← S.ε_nat c]
    funext i
    change c.f (p₀.f (u x i)) = _
    have e : p₀.f (u x i) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec (fun j => q₀.f (u x j)) i := congrFun hx i
    rw [e, RingHom.map_mulVec]
    rfl

end GlobalTheory.BSP.CoverDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWitt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedF

variable {l : ℕ} [Fact l.Prime]

theorem aw_injective (C : Core l) (a : ℕ) [NeZero a] :
    Function.Injective ((Per.aB l).comp (wA l a).toRingHom) := by
  haveI : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  haveI : Nontrivial (Per.Bcris l) := C.ι.domain_nontrivial
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (((l : ℕ) : Per.Bcris l) ^ m * ((Per.aB l).comp (wA l a).toRingHom) (b : Wq l a)) :=
    ((isUnit_l_Bcris l).pow m).mul (b.isUnit.map _)
  exact hu.ne_zero hx

theorem clear_den {d : ℕ} {R : Type} [CommRing R] (f : R →+* Per.Bcris l)
    (G : Matrix (Fin d) (Fin d) (Per.Bcris l))
    (h : ∀ i j, ∃ (n : ℕ) (w : R), ((l : ℕ) : Per.Bcris l) ^ n * G i j = f w) :
    ∃ (k : ℕ) (F : Matrix (Fin d) (Fin d) R), ((l : ℕ) : Per.Bcris l) ^ k • G = F.map f := by
  choose n w hw using h
  refine ⟨Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2),
    Matrix.of fun i j => ((l : ℕ) : R) ^ (Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) - n i j) * w i j, ?_⟩
  ext i j
  have hle : n i j ≤ Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) :=
    Finset.le_sup (f := fun p : Fin d × Fin d => n p.1 p.2) (Finset.mem_univ (i, j))
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, map_natCast, smul_eq_mul,
    ← hw]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem inv_entries {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hρ : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l)) = U' * U.map (Per.φB l) ∧
    (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l)) = U'.map (Per.φB l) * U := by
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hR : (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := hρ g
  have hσ1 : U.map (Per.σB (g : GQ l)) * U'.map (Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hσU' : U'.map (Per.σB (g : GQ l)) = U' * (ρ g).map (Per.zB l) := by
    calc U'.map (Per.σB (g : GQ l))
        = (U' * (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) * U'.map (Per.σB (g : GQ l)) := by
          rw [mul_assoc U', hR, hU'U, one_mul]
      _ = U' * (ρ g).map (Per.zB l) := by rw [mul_assoc, hσ1, mul_one]
  have hφR : ((ρ g).map (Per.zB l)).map (Per.φB l) = (ρ g).map (Per.zB l) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.1, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1]
  have hcomm : ∀ M : Matrix (Fin d) (Fin d) (Per.Bcris l),
      (M.map (Per.φB l)).map (Per.σB (g : GQ l)) = (M.map (Per.σB (g : GQ l))).map (Per.φB l) := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact ((ActLaws.act_laws l).2.2.2.2.1 _ _).symm
  constructor
  · calc (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l))
        = U'.map (Per.σB (g : GQ l)) * (U.map (Per.σB (g : GQ l))).map (Per.φB l) := by
          rw [Matrix.map_mul, hcomm]
      _ = U' * (((ρ g).map (Per.zB l)).map (Per.φB l) * (U.map (Per.σB (g : GQ l))).map (Per.φB l)) := by
          rw [hσU', hφR, mul_assoc]
      _ = U' * U.map (Per.φB l) := by rw [← Matrix.map_mul, hR]
  · calc (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l))
        = (U'.map (Per.σB (g : GQ l))).map (Per.φB l) * U.map (Per.σB (g : GQ l)) := by
          rw [Matrix.map_mul, hcomm]
      _ = U'.map (Per.φB l) * ((ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) := by
          rw [hσU', Matrix.map_mul, hφR, mul_assoc]
      _ = U'.map (Per.φB l) * U := by rw [hR]

theorem frob_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvB →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) →
    ∃ (c₁ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)),
      F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧
      (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
  intro l _ K bk C hC d ρ U U' hUU hρ
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hent : ∀ G : Matrix (Fin d) (Fin d) (Per.Bcris l), (∀ g : ↥(GK K), G.map (Per.σB (g : GQ l)) = G) →
      ∀ i j, ∃ (n : ℕ) (w : Wq l bk.a),
        ((l : ℕ) : Per.Bcris l) ^ n * G i j = ((Per.aB l).comp (wA l bk.a).toRingHom) w := by
    intro G hG i j
    obtain ⟨x, hxK, hx⟩ := hC K (G i j) fun g hg => by
      have := congrFun (congrFun (hG ⟨g, hg⟩) i) j
      simpa only [Matrix.map_apply] using this
    obtain ⟨n, w, hw⟩ := _root_.GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB l K bk C x hxK
    exact ⟨n, w, by rw [← hx, hw]; rfl⟩
  obtain ⟨k, F, hF⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).1)
  obtain ⟨k', F', hF'⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).2)
  have hGG : (U' * U.map (Per.φB l)) * (U'.map (Per.φB l) * U) = 1 := by
    rw [mul_assoc, ← mul_assoc (U.map _), ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _),
      one_mul, hU'U]
  refine ⟨k, k + k', F, F', ?_, ?_⟩
  · apply Matrix.map_injective (aw_injective C bk.a)
    change (F * F').map ((Per.aB l).comp (wA l bk.a).toRingHom) =
      (((l : ℕ) : Wq l bk.a) ^ (k + k') • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))).map
        ((Per.aB l).comp (wA l bk.a).toRingHom)
    rw [Matrix.map_mul, ← hF, ← hF', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, hGG]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  · rw [← hF, Matrix.mul_smul, ← mul_assoc, hUU, one_mul]

end GlobalTheory.SeedF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponent
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_split_loc : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (g : GA E a), ∃ (h : GA E a) (gw : GL (Fin a) (w.adicCompletion E)),
      g = h * finGL E a (locGL E a w gw) ∧
        ∀ u : GL (Fin a) (w.adicCompletion E),
          h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  intro E _ _ _ a w g
  obtain ⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := ⟨_, rfl⟩
  refine ⟨g * (finGL E a (locGL E a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w)
      (GeneralLinearGroup.map (pFin E) (g * (finGL E a (locGL E a w gw))⁻¹)) = 1 := by
    rw [map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]
  generalize g * (finGL E a (locGL E a w gw))⁻¹ = k at hk ⊢
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_finGL, one_mul, mul_one]
  · rw [map_mul, map_mul, pFin_finGL]
    exact LocUniq.comm_locGL w hk u

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPairStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_H1_dual_pair : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  first | exact @GlobalTheory.EulerCharH1.finite_and_finrank_H1V | exact GlobalTheory.EulerCharH1.finite_and_finrank_H1V | (intros; apply GlobalTheory.EulerCharH1.finite_and_finrank_H1V <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotientStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ Fs : Finset (↥(OL LL))ˣ, (∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → uU W ^ (-(a + j)) ∈ Fs) → ∀ x ∈ invN W T (W.Q ^ y), Polynomial.aeval (W.γ T) (∏ c ∈ Fs, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x ∈ W.N T := by
  first | exact @GlobalTheory.NL.KillLevels.annihilate | exact GlobalTheory.NL.KillLevels.annihilate | (intros; apply GlobalTheory.NL.KillLevels.annihilate <;> assumption)
end

