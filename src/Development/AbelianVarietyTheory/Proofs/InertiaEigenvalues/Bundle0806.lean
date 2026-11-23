module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqOfTwistConditionA
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdmAll

theorem admissibleConjugatePairPlaces_eq_of_twist_condition : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X),
  GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → admissibleConjugatePairPlaces X i Q M = Q := by
  intro D N X Y hY i k Q M χ hT
  classical
  refine Finset.Subset.antisymm (admissibleConjugatePairPlaces_subset i Q M) fun v hv => ?_
  by_contra hna
  obtain ⟨A, hA⟩ := exists_isPlaceOver N.Om v
  obtain ⟨σ, hσ, hne⟩ := (hT.2.2.2.2.2.1 v A hA).2 hv
  apply hne
  have h1 : Y.delU i Q M σ = 1 := by
    apply Multiplicative.toAdd.injective
    funext w
    by_cases hw : w.1 ∈ admissibleConjugatePairPlaces X i Q M
    · rw [delU_on hY σ w hw]
      have hvp : v ∉ GalChar.pair D.host w.1 := by
        rintro (h | hc)
        · exact hna (h ▸ hw)
        · exact hna (conj_mem_admissibleConjugatePairPlaces hw hc)
      rw [(GalChar.delOf_laws D.host X.cc (X.l i) M _).2.2.2 v hvp A hA σ hσ]
      rfl
    · rw [delU_off hY (twSet_of_twOK hT) σ w hw]
      rfl
  rw [MonoidHom.comp_apply, h1, map_one]

end GlobalTheory.AdmAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead

variable {D : D7}

def IdFrame {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∃ hn : V.rank = n, ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
    (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

variable {S T : HSp D} {n : ℕ}

def RatMatch (φ : GAf D.host.E n ≃* Bridge.Gf S) : Prop :=
  (∀ γ : ReciprocityTheory.Aut.GQ D.host.E n, ∃ γ', Bridge.ratF S γ' = φ γ) ∧
    ∀ γ', ∃ γ : ReciprocityTheory.Aut.GQ D.host.E n, Bridge.ratF S γ' = φ γ

def WtMap (B : Base S T) (φ : GAf D.host.E n ≃* Bridge.Gf S) (R : Type) [CommRing R] [IsDomain R] (e : FractionRing R →+* ℂ)
    {W : Type} [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W)
    (ω : W →ₛₗ[e] PolF D T.rank S.rank) : Prop :=
  Function.Injective ω ∧ (∀ w, ω w ∈ B.valSpace) ∧
    (∀ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ S), Bridge.ratF S γ' = φ γ →
      ∀ w, ω (ρ γ w) = B.act (γ' : GA D S) (ω w)) ∧
    (∀ h, ∀ x ∈ B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range h, x ∈ Set.range ω) ∧
    ∀ h w, ∃ c : R, c ≠ 0 ∧
      ω (algebraMap R (FractionRing R) c • w) ∈ B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range h

def LevMatch (B : Base S T) (t : Twist D Circle) (φ : GAf D.host.E n ≃* Bridge.Gf S) {K : Type} [Field K] (e : K →+* ℂ)
    (J : Subgroup (GAf D.host.E n)) (χ : J →* Kˣ) : Prop :=
  (∀ g, g ∈ J ↔ φ g ∈ B.levJ t) ∧
    ∀ g (h : g ∈ J) (h' : φ g ∈ B.levJ t), e ((χ ⟨g, h⟩ : Kˣ) : K) = ((B.levLam t ⟨φ g, h'⟩ : ℂˣ) : ℂ)

theorem finite_kP (P : Pl D.host.E) : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot

theorem isOfFinOrder_levFn {m : ℕ} (β : GL (Fin m) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ m) (x : GL (Fin m) (Lev.EAf D)) :
    IsOfFinOrder (levFn β L x) := by
  haveI : ∀ P : Pl D.host.E, Finite (kP P) := finite_kP
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℂˣ), (∀ i ∈ s, IsOfFinOrder (f i)) → IsOfFinOrder (∏ i ∈ s, f i) :=
    fun s f h => Finset.prod_induction f IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one h
  unfold levFn
  refine (IsOfFinOrder.mul ?_ (hprod _ _ fun P _ => hprod _ _ fun c _ => ?_)).mul (hprod _ _ fun P _ => ?_)
  · unfold ext1
    split_ifs with h
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact IsOfFinOrder.one
  · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

theorem mem_range_of_finOrder {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (e : FractionRing R →+* ℂ)
    {x : FractionRing R} {z : ℂˣ} (hz : IsOfFinOrder z) (h : e x = z) : (z : ℂ) ∈ (e.comp (algebraMap R (FractionRing R))).range := by
  obtain ⟨m, hm, h1⟩ := hz.exists_pow_eq_one
  have h2 : x ^ m = 1 := e.injective (by rw [map_pow, h, ← Units.val_pow_eq_pow_val, h1, map_one, Units.val_one])
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (R := R) hm (h2 ▸ isIntegral_one))
  exact ⟨y, by rw [RingHom.comp_apply, hy, h]⟩

theorem read_abstract {G G' Γ' R W P I V : Type} [Group G] [Group G'] [Group Γ'] [CommRing R] [IsDomain R] [AddCommGroup W]
    [Module (FractionRing R) W] [AddCommGroup P] [Module ℂ P] [Finite I] [AddCommGroup V] [Module (FractionRing R) V]
    (φ : G ≃* G') (Γ J : Subgroup G) (J' : Subgroup G') (ι : Γ' → G') (e : FractionRing R →+* ℂ) (ρ : Γ → W → W) (χ : J → FractionRing R)
    (act : Γ' → P → P) (lam : J' → ℂ) (ω : W →ₛₗ[e] P) (val : Set P)
    (L : G' → Submodule (e.comp (algebraMap R (FractionRing R))).range P)
    (A : Submodule (FractionRing R) (G → W))
    (hA : ∀ f, f ∈ A ↔ (∀ (γ : Γ) g, f (γ * g) = ρ γ (f g)) ∧ ∀ (κ : J) g, f (g * κ) = χ κ • f g)
    (M : Set (G' → P))
    (hM : ∀ F, F ∈ M ↔ ((∀ h, F h ∈ val) ∧ ∀ γ h (k : J'), F (ι γ * h * k) = lam k • act γ (F h)) ∧ ∀ h, F h ∈ L h)
    (h1 : ∃ γ, ι γ = 1 ∧ ∀ x, act γ x = x) (hl1 : lam 1 = 1)
    (hr1 : ∀ γ : Γ, ∃ γ', ι γ' = φ γ) (hr2 : ∀ γ', ∃ γ : Γ, ι γ' = φ γ)
    (hinj : Function.Injective ω) (hval : ∀ w, ω w ∈ val) (heq : ∀ (γ : Γ) γ', ι γ' = φ γ → ∀ w, ω (ρ γ w) = act γ' (ω w))
    (hrange : ∀ h, ∀ x ∈ L h, x ∈ Set.range ω) (hden : ∀ h w, ∃ c : R, c ≠ 0 ∧ ω (algebraMap R (FractionRing R) c • w) ∈ L h)
    (hJ1 : ∀ g, g ∈ J ↔ φ g ∈ J') (hJ2 : ∀ g (h : g ∈ J) (h' : φ g ∈ J'), e (χ ⟨g, h⟩) = lam ⟨φ g, h'⟩)
    (hlam : ∀ k, lam k ∈ (e.comp (algebraMap R (FractionRing R))).range)
    (hact : ∀ γ h (k : J'), ∀ x ∈ L h, act γ x ∈ L (ι γ * h * k))
    (y : I → G') (hy : ∀ h, ∃ i γ, ∃ k : J', h = ι γ * y i * k) (real : V ≃ₗ[FractionRing R] A) :
    ∃ r : V →ₛₗ[e] (G' → P), Function.Injective r ∧ (∀ F ∈ M, F ∈ Set.range r) ∧
      Submodule.span (FractionRing R) {f | r f ∈ M} = ⊤ ∧ ∀ f g, r f (φ g) = ω ((real f).1 g) := by
  let r : V →ₛₗ[e] (G' → P) :=
    { toFun := fun f h => ω ((real f).1 (φ.symm h))
      map_add' := fun f f' => by funext h; simp
      map_smul' := fun c f => by funext h; simp [map_smulₛₗ] }
  have hr_apply : ∀ f g, r f (φ g) = ω ((real f).1 g) := fun f g => by
    change ω ((real f).1 (φ.symm (φ g))) = _
    rw [φ.symm_apply_apply]
  have hlaw : ∀ f γ h (k : J'), r f (ι γ * h * k) = lam k • act γ (r f h) := fun f γ' h k => by
    obtain ⟨γ, hγ⟩ := hr2 γ'
    obtain ⟨g, rfl⟩ := φ.surjective h
    obtain ⟨k, hk⟩ := k
    obtain ⟨κ, rfl⟩ := φ.surjective k
    have hκ := (hJ1 κ).2 hk
    change r f (ι γ' * φ g * φ κ) = _
    have h2 := (hA _).1 (real f).2
    rw [hγ, ← map_mul, ← map_mul, hr_apply, hr_apply, h2.2 ⟨κ, hκ⟩, h2.1, map_smulₛₗ, heq γ γ' hγ, hJ2 κ hκ hk]
  refine ⟨r, fun f f' h => ?_, fun F hF => ?_, ?_, hr_apply⟩
  · refine real.injective (Subtype.ext (funext fun g => hinj ?_))
    rw [← hr_apply, ← hr_apply, h]
  · obtain ⟨⟨-, hF3⟩, hF2⟩ := (hM F).1 hF
    choose u hu using fun g => hrange (φ g) _ (hF2 (φ g))
    have hmem : u ∈ A := by
      refine (hA u).2 ⟨fun γ g => hinj ?_, fun κ g => hinj ?_⟩
      · obtain ⟨γ', hγ⟩ := hr1 γ
        have := hF3 γ' (φ g) 1
        rw [heq γ γ' hγ, hu, hu, map_mul, ← hγ]
        simpa [hl1] using this
      · have hk := (hJ1 κ).1 κ.2
        obtain ⟨γ, hγ, hγ'⟩ := h1
        have := hF3 γ (φ g) ⟨φ κ, hk⟩
        rw [map_smulₛₗ, hu, hu, map_mul, hJ2 κ κ.2 hk]
        simpa [hγ, hγ'] using this
    refine ⟨real.symm ⟨u, hmem⟩, funext fun h => ?_⟩
    obtain ⟨g, rfl⟩ := φ.surjective h
    rw [hr_apply, real.apply_symm_apply, hu]
  · refine eq_top_iff.2 fun f _ => ?_
    haveI := Fintype.ofFinite I
    classical
    choose c hc0 hcm using fun i => hden (y i) ((real f).1 (φ.symm (y i)))
    have hd : algebraMap R (FractionRing R) (∏ i, c i) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact Finset.prod_ne_zero_iff.2 fun i _ => hc0 i
    have hm : r (algebraMap R (FractionRing R) (∏ i, c i) • f) ∈ M := by
      refine (hM _).2 ⟨⟨fun h => hval _, hlaw _⟩, fun h => ?_⟩
      obtain ⟨i, γ, k, rfl⟩ := hy h
      have e1 : r (algebraMap R (FractionRing R) (∏ i, c i) • f) (y i) =
          e (algebraMap R (FractionRing R) (∏ j ∈ Finset.univ.erase i, c j)) •
            ω (algebraMap R (FractionRing R) (c i) • (real f).1 (φ.symm (y i))) := by
        rw [← map_smulₛₗ, smul_smul, ← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        change ω ((real (_ • f)).1 _) = _
        rw [map_smul]
        rfl
      have h2 : r (algebraMap R (FractionRing R) (∏ i, c i) • f) (y i) ∈ L (y i) := by
        rw [e1]
        exact Submodule.smul_mem _ (⟨_, _, rfl⟩ : (e.comp (algebraMap R (FractionRing R))).range) (hcm i)
      rw [hlaw]
      exact Submodule.smul_mem _ (⟨_, hlam k⟩ : (e.comp (algebraMap R (FractionRing R))).range) (hact γ _ k _ h2)
    have := Submodule.smul_mem _ (algebraMap R (FractionRing R) (∏ i, c i))⁻¹ (Submodule.subset_span (R := FractionRing R)
      (s := {f | r f ∈ M}) hm)
    rwa [inv_smul_smul₀ hd] at this

theorem read_cell (B : Base S T) (hB : B.Good) (t : Twist D Circle) (φ : GAf D.host.E n ≃* Bridge.Gf S) (R : Type) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] (e : FractionRing R →+* ℂ)
    (hc : IsCoefRing (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range)
    {W : Type} [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W)
    (J : Subgroup (GAf D.host.E n)) (χ : J →* (FractionRing R)ˣ) (ω : W →ₛₗ[e] PolF D T.rank S.rank)
    (hr : RatMatch φ) (hω : WtMap B φ R e ρ ω) (hJ : LevMatch B t φ e J χ) {I : Type} [Finite I] (y : I → Bridge.Gf S)
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) {V : Type} [AddCommGroup V] [Module (FractionRing R) V]
    (real : V ≃ₗ[FractionRing R] NX.TypeSpF D.host.E n (FractionRing R) ρ J χ) :
    ∃ r : V →ₛₗ[e] (Bridge.Gf S → PolF D T.rank S.rank), Function.Injective r ∧
      (∀ F ∈ B.mtLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range t, F ∈ Set.range r) ∧
      Submodule.span (FractionRing R)
        {f | r f ∈ B.mtLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range t} = ⊤ ∧
      ∀ f g, r f (φ g) = ω ((real f).1 g) := by
  refine read_abstract φ (ReciprocityTheory.Aut.GQ D.host.E n) J (B.levJ t) (Bridge.ratF S) e (fun γ => ρ γ) (fun κ => (χ κ : FractionRing R))
    (fun γ => B.act (γ : GA D S)) (fun k => ((B.levLam t k : ℂˣ) : ℂ)) ω B.valSpace
    (B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range) _ (fun _ => Iff.rfl) _
    (fun F => (B.mem_mtLat _ _ _).trans (and_congr_left' B.mem_formsC)) ⟨1, MonoidHom.map_one _, fun x => ?_⟩ ?_ hr.1 hr.2
    hω.1 hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2 hJ.1 hJ.2 (fun k => ?_)
    (fun γ h k x hx => Base.act_mem_coefLat hB.frame hc γ h k (Base.mem_St_of_mem_levJ k.2) hx) y
    (fun h => (hy h).exists.imp fun _ h => h) real
  · change B.act 1 x = x
    rw [MonoidHom.map_one]
    rfl
  · change ((B.levLam t 1 : ℂˣ) : ℂ) = 1
    rw [MonoidHom.map_one]
    rfl
  · obtain ⟨k, hk⟩ := k
    obtain ⟨κ, rfl⟩ := φ.surjective k
    exact mem_range_of_finOrder e (isOfFinOrder_levFn _ _ _) (hJ.2 κ ((hJ.1 κ).2 hk) hk)

theorem admissible_twist_of_twisting_character {i : D.ntw.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : NX.AdmTw D i k Q ψ := by
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := h
  have hS : ∀ P ∈ Q, P ∉ D.ntw.S0 i := fun P hP => Finset.disjoint_left.1 hdisj hP
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  refine ⟨fun P hP => ⟨hsplit P hP, fun h => hS P hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)⟩,
    fun P hP => ⟨fun h => hS P hP (D.ntw.primes_subset_exceptional i h), fun k' h => hS P hP (D.ntw.placesOver_subset_exceptional i k' h)⟩, hopen, hanti, fun σ => ⟨k, ?_⟩,
    fun P hP A hA σ hσ => ?_⟩
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · by_contra h
    exact hP ((hram P A hA).1 ⟨σ, hσ, h⟩)

theorem eq_of_infOf_eq {m : ℕ} {a b : Fin m → ℤ} (ha : Antitone a) (hb : Antitone b) (h : NG.infOf a = NG.infOf b) : a = b := by
  have key : ∀ c : Fin m → ℤ, NG.infOf c =
      (Finset.univ.val.map fun i : Fin m => c i - (i : ℕ)).map fun z : ℤ => (z : ℂ) + ((m : ℂ) - 1) / 2 := fun c => by
    rw [NG.infOf, Multiset.map_map]
    congr 1
    funext i
    simp only [Function.comp_apply]
    push_cast
    ring
  rw [key, key] at h
  have h2 := Multiset.map_injective (fun x y hxy => by exact_mod_cast add_right_cancel hxy) h
  have sa : ∀ c : Fin m → ℤ, Antitone c → StrictAnti fun i : Fin m => c i - (i : ℕ) := fun c hc i j hij => by
    have := hc hij.le
    have h3 : (i : ℕ) < j := hij
    beta_reduce
    omega
  have hr : Set.range (fun i : Fin m => a i - (i : ℕ)) = Set.range fun i : Fin m => b i - (i : ℕ) := by
    ext z
    have := congrArg (z ∈ ·) h2
    simpa using this
  have h4 := ((sa a ha).range_inj (sa b hb)).1 hr
  funext i
  have := congrFun h4 i
  omega

end GlobalTheory.MtRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinMapSplitPlaceUniformiserEqFrobeniusInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie

noncomputable section

namespace GlobalTheory.SeriesTie

theorem Recip.pull_locUnif : ∀ (D : D7) (Ω : Type) [Field Ω] [Algebra D.host.E Ω] (A : Type) [CommGroup A] (a : Recip D Ω), a.Good → ∀ φ : G D.host.E Ω →* A, IsOpen (φ.ker : Set (G D.host.E Ω)) → ∀ (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ B : ValuationSubring Ω, IsPlaceOver B P → (∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) B (normV P) σ → a.pull φ x = (φ σ)⁻¹ := by
  intro D Ω _ _ A _ a ha φ hφ P e he ϖ hϖP hϖP2 x hx B hB hine σ hσ
  have hv := GlobalTheory.HeckeDetChar.val_unif hϖP hϖP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  let ϖU : D.host.Eˣ := Units.mk0 (ϖ : D.host.E) hϖ0
  have hκ : a.κ (x : AE D) = ((Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P ϖU) : Neutral.B1.Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
    rw [← ha.loc P e (GlobalTheory.HeckeDetChar.isPlIdem he) ϖU, hx, Formalism.L2.JoinChr.locE]
    congr 1
    show _ = 1 + e * (incA D (ϖ : D.host.E) - 1)
    ring
  have hsym : a.sym x = a.art (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P ϖU)) := by
    rw [Recip.sym, MonoidHom.comp_apply]
    congr 1
    exact Units.ext hκ
  have hunif : Valued.v ((Formalism.L2.Host.atFin P ϖU : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) =
      WithZero.exp (-1 : ℤ) := by
    show Valued.v (((ϖ : D.host.E) : P.adicCompletion D.host.E)) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hv]
  obtain ⟨y, hy, hyσ⟩ := (ha.artin.frob P B hB _).mpr ⟨σ, hσ, rfl⟩
  have hu : Valued.v (((Formalism.L2.Host.atFin P ϖU * y⁻¹ : (P.adicCompletion D.host.E)ˣ)) : P.adicCompletion D.host.E) = 1 := by
    have hy' : Valued.v ((y : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ) := hy
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hunif, hy']
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  obtain ⟨τ, hτ, hτu⟩ := (ha.artin.ine P B hB _).mp ⟨_, hu, rfl⟩
  have hs : a.sym x = GlobalTheory.HeckeGal.toAb D.host.E Ω (τ * σ⁻¹) := by
    rw [hsym, show Formalism.L2.Host.atFin P ϖU = (Formalism.L2.Host.atFin P ϖU * y⁻¹) * y by group, map_mul, map_mul, hyσ,
      ← hτu, map_mul]
  rw [a.pull_eq hφ hs, map_mul, hine τ hτ, map_inv, one_mul]

end GlobalTheory.SeriesTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AveragedSeriesFullRankOfComplexSpanGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.RankDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem charZero_frac (i : X.Tw) : CharZero (FractionRing (X.O i)) :=
  (RingHom.charZero_iff ((IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
      (L := FractionRing (X.O i)) (X.O_inj i)).comp (X.emb0 i)).injective).1 inferInstance

theorem eG_eG (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b (Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x) = Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))) (Y.eAlg_idem i b)
  rw [map_mul] at h
  exact LinearMap.congr_fun h x

theorem good_idempotent_fixes_mem_good_type_space (i : X.Tw) (j : ℕ) (b : Bool) {x : Y.Fm i j b} (hx : x ∈ V0 Y i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x = x := by
  obtain ⟨y, -, rfl⟩ := hx
  exact eG_eG Y i j b y


open Formalism.MainNotions.IntegralHeckeForms in
theorem AO_eq (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • eG Y i j b x := by
  show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _
  rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), algebraMap_smul]


open Formalism.MainNotions.IntegralHeckeForms in
theorem thetaSeries_mem_goodTypeForms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (a : Y.Dat i j b) (ha : a ∈ E.Dat0 i j b) :
    Y.th i j b a ∈ Fm0 Y i j b := by
  simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u
  have := E.theta_base_equivariant i j b a ha u
  simp [this]


open Formalism.MainNotions.IntegralHeckeForms in
theorem AO_Th_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) :
    ∀ x ∈ (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b), x ∈ V0 Y i j b := by
  rintro _ ⟨y, hy, rfl⟩
  rw [AO_eq]
  refine Submodule.smul_mem _ _ ⟨y, ?_, rfl⟩
  refine (Submodule.span_le (p := (Fm0 Y i j b).restrictScalars (X.O i))).2 ?_ hy
  rintro _ ⟨a, ha, rfl⟩
  exact thetaSeries_mem_goodTypeForms Y E i j b a ha


open Formalism.MainNotions.IntegralHeckeForms in
theorem fullRk_of_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool)
    (h : V0 Y i j b ≤ Submodule.span (FractionRing (X.O i)) (eG Y i j b '' (Y.th i j b '' E.Dat0 i j b))) :
    FullRk Y E i j b (SgJ Y E i j b) := by
  haveI := charZero_frac (X := X) i
  have hc : ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) ≠ 0 := Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'
  refine ⟨subset_rfl, AO_Th_le Y E i j b, le_antisymm (Submodule.span_le.2 (AO_Th_le Y E i j b)) (h.trans ?_)⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  have e1 : eG Y i j b (Y.th i j b a) = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i))⁻¹ • AO Y i j b (Y.th i j b a) := by
    rw [AO_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨a, ha, rfl⟩, rfl⟩)

section Descent

variable {ρ : Setup X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}

theorem rd_mem_span (rd : Rd ρ Y i j b) (S : Set (Y.Fm i ((j : ℕ) + 1) b)) {y : Y.Fm i ((j : ℕ) + 1) b}
    (hy : y ∈ Submodule.span (FractionRing (X.O i)) S) : rd y ∈ Submodule.span ℂ (rd '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem mem_span_of_faithful {rd : Rd ρ Y i j b} (hf : Faithful rd) (S : Set (Y.Fm i ((j : ℕ) + 1) b))
    {x : Y.Fm i ((j : ℕ) + 1) b} (hx : rd x ∈ Submodule.span ℂ (rd '' S)) :
    x ∈ Submodule.span (FractionRing (X.O i)) S := by
  set W := Submodule.span (FractionRing (X.O i)) S
  by_contra hxW
  let bW := Module.finBasis (FractionRing (X.O i)) W
  let v : Fin (Module.finrank (FractionRing (X.O i)) W) → Y.Fm i ((j : ℕ) + 1) b := fun k => (bW k : Y.Fm i ((j : ℕ) + 1) b)
  have hv : LinearIndependent (FractionRing (X.O i)) v := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span (FractionRing (X.O i)) (Set.range v) = W := by
    have := congrArg (Submodule.map W.subtype) bW.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hli : LinearIndependent (FractionRing (X.O i)) (Fin.cons x v : Fin _ → Y.Fm i ((j : ℕ) + 1) b) :=
    linearIndependent_finCons.2 ⟨hv, by rw [hspan]; exact hxW⟩
  have hC := hf _ _ hli
  have hC' : LinearIndependent ℂ (Fin.cons (rd x) (fun k => rd (v k)) : Fin _ → (GA D (Wc D j) → ℂ)) := by
    convert hC using 1
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  refine (linearIndependent_finCons.1 hC').2 ?_
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨s, hs, rfl⟩
  have hsW : s ∈ Submodule.span (FractionRing (X.O i)) (Set.range v) := by
    rw [hspan]; exact Submodule.subset_span hs
  have := rd_mem_span Y rd _ hsW
  rw [← Set.range_comp] at this
  exact this

end Descent

theorem fullRk_of_spanGood : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro D ρ hρ rd T hF E i hR hall hS j hj b
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine fullRk_of_le D.nexp E i _ b ?_
  intro x hx
  have h1 : rd i j' b x ∈ Submodule.span ℂ (rd i j' b '' (D.nexp.th i _ b '' E.Dat0 i _ b)) := by
    refine Submodule.span_mono ?_ (hS j' b x hx)
    rintro _ ⟨s, h, P, hd, rfl⟩
    obtain ⟨d, -, hc, hp⟩ := (T i j' b).dat_onto s h P hd (hR j' b s h P hd)
    refine ⟨D.nexp.th i _ b d, ⟨d, hall _ hj b d, rfl⟩, ?_⟩
    rw [(T i j' b).th_eq d, hc, hp]
  have h2 := mem_span_of_faithful D.nexp (hF i j' b) _ h1
  rw [← good_idempotent_fixes_mem_good_type_space D.nexp i _ b hx]
  have h3 := Submodule.mem_map_of_mem (f := Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j' : ℕ) + 1) b) h2
  rwa [Submodule.map_span] at h3

end GlobalTheory.RankDescent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PinBase

theorem baseOf_of_pin : ∀ (D : D7) (X : RealSide D) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ → ∀ i j b, GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (ρ.B i j b) := by
  intro D X ρ hρ hp i j b
  have hB := hρ.base i j b
  have hL : X.R.toLevCh.Is X.A3.A.μ0 := X.char.lev
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ X.R.toLevCh X.A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = GlobalTheory.ConjTwist.liftC D j τ := fun τ =>
    GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← GlobalTheory.ConjTwist.liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

end GlobalTheory.PinBase
end

