module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0540
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePair
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace OnePair


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.OnePair.coeff_subst_kill {σ R : Type} [CommRing R] [Finite σ] (p : σ → Prop)
    [DecidablePred p] (c : MvPowerSeries σ R) (γ : σ →₀ ℕ) [Decidable (∀ s, ¬ p s → γ s = 0)] :
    coeff γ (subst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) c) =
      if ∀ s, ¬ p s → γ s = 0 then coeff γ c else 0 := by
  classical
  have hsub : HasSubst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) :=
    hasSubst_of_constantCoeff_zero fun s => by split_ifs <;> simp
  have key : ∀ d : σ →₀ ℕ,
      coeff γ (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
        if d = γ ∧ ∀ s, ¬ p s → γ s = 0 then 1 else 0 := by
    intro d
    by_cases hd : ∀ s, ¬ p s → d s = 0
    · have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
          monomial d 1 := by
        rw [monomial_one_eq]
        refine Finsupp.prod_congr fun s hs => ?_
        have hps : p s := by
          by_contra h
          exact (Finsupp.mem_support_iff.mp hs) (hd s h)
        rw [if_pos hps]
      rw [hprod, coeff_monomial]
      by_cases hγ : γ = d
      · subst hγ
        rw [if_pos rfl, if_pos ⟨rfl, hd⟩]
      · rw [if_neg hγ, if_neg fun h => hγ h.1.symm]
    · push_neg at hd
      obtain ⟨s, hps, hds⟩ := hd
      have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) = 0 := by
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hds) (by rw [if_neg hps, zero_pow hds])
      rw [hprod, map_zero, if_neg]
      rintro ⟨rfl, h⟩
      exact hds (h s hps)
  rw [coeff_subst hsub, finsum_eq_single _ γ]
  · rw [key]
    by_cases h : ∀ s, ¬ p s → γ s = 0 <;> simp [h]
  · intro d hd
    rw [key, if_neg fun h => hd h.1, smul_zero]

end OnePair


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.coeff_at2_single_X_inl_inr (R : Type) [CommRing R] (d : ℕ)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ) :
    coeff γ (_root_.GlobalTheory.Katz.at2 c
      (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m)))) =
      if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  classical
  have hfun : Sum.elim (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m))) = fun s =>
        if (s = Sum.inl m ∨ s = Sum.inr m) then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0 := by
    funext s
    rcases s with i | i <;> by_cases h : i = m <;> simp [h, Pi.single_apply]
  have hiff : (∀ s, ¬ (s = Sum.inl m ∨ s = Sum.inr m) → γ s = 0) ↔
      γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) := by
    constructor
    · intro h
      ext s
      by_cases hs : s = Sum.inl m ∨ s = Sum.inr m
      · rcases hs with rfl | rfl <;> simp [Finsupp.single_apply]
      · push_neg at hs
        rw [h s (not_or.mpr hs)]
        simp [Finsupp.single_apply, Ne.symm hs.1, Ne.symm hs.2]
    · intro h s hs
      push_neg at hs
      rw [h]
      simp [Finsupp.single_apply, Ne.symm hs.1, Ne.symm hs.2]
  unfold _root_.GlobalTheory.Katz.at2
  rw [hfun, _root_.GlobalTheory.OnePair.coeff_subst_kill]
  by_cases hγ : γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (γ (Sum.inr m))
  · rw [if_pos hγ, if_pos (hiff.mpr hγ)]
  · rw [if_neg hγ, if_neg fun h => hγ (hiff.mp h)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstLeadingOfAgreeDegreeOne
section
noncomputable section

namespace GlobalTheory
namespace LeadSubst

open MvPowerSeries

variable {σ τ R : Type*} [CommRing R]

def Near (n : ℕ) (P Q : MvPowerSeries τ R) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((n + 1 : ℕ) : ℕ∞) ≤ (P - Q).order

theorem Near.one : Near 0 (1 : MvPowerSeries τ R) 1 := by
  simp [Near]

theorem Near.mul {n m : ℕ} {P Q P' Q' : MvPowerSeries τ R} (h : Near n P Q)
    (h' : Near m P' Q') : Near (n + m) (P * P') (Q * Q') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast; exact (add_le_add h1 h1').trans le_order_mul
  · push_cast; exact (add_le_add h2 h2').trans le_order_mul
  · have e : P * P' - Q * Q' = P * (P' - Q') + (P - Q) * Q' := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h1 h3')
      push_cast; ring
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h3 h2')
      push_cast; ring

theorem Near.prod {a b : σ → MvPowerSeries τ R}
    (h : ∀ s, Near 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Near d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa using (Near.one : Near 0 (1 : MvPowerSeries τ R) 1)
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add (f := _)]
    exact hf.mul hg
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.degree_single]
    induction n with
    | zero => simpa using (Near.one : Near 0 (1 : MvPowerSeries τ R) 1)
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul (h s)

theorem near_one {u v : MvPowerSeries τ R} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h1 : ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ u = coeff γ v) : Near 1 u v := by
  refine ⟨by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu,
    by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hv, ?_⟩
  refine nat_le_order fun d hd => ?_
  rw [map_sub, sub_eq_zero]
  rcases (show d.degree = 0 ∨ d.degree = 1 by omega) with h | h
  · rw [(Finsupp.degree_eq_zero_iff d).mp h, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hu, hv]
  · exact h1 d h

end LeadSubst


open MvPowerSeries in
theorem coeff_subst_leading :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries τ R) (N : ℕ)
      (f : MvPowerSeries σ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (∀ i (γ : τ →₀ ℕ), γ.degree = 1 → coeff γ (u i) = coeff γ (v i)) →
      (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) →
      ∀ γ : τ →₀ ℕ, (γ.degree < N → coeff γ (subst u f) = 0) ∧
        (γ.degree ≤ N → coeff γ (subst u f) = coeff γ (subst v f)) := by
  intro R _ σ τ _ u v N f hu hv h1 hf γ
  have hn : ∀ s, LeadSubst.Near 1 (u s) (v s) := fun s => LeadSubst.near_one (hu s) (hv s) (h1 s)
  refine ⟨fun hγ => ?_, fun hγ => ?_⟩
  · rw [coeff_subst (hasSubst_of_constantCoeff_zero hu)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : d.degree < N
    · rw [hf d hd, zero_smul]
    · rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega : γ.degree < d.degree))
        (LeadSubst.Near.prod hn d).1), smul_zero]
  · rw [coeff_subst (hasSubst_of_constantCoeff_zero hu),
      coeff_subst (hasSubst_of_constantCoeff_zero hv)]
    refine finsum_congr fun d => ?_
    by_cases hd : d.degree < N
    · rw [hf d hd, zero_smul, zero_smul]
    · congr 1
      have h := coeff_of_lt_order (d := γ) (lt_of_lt_of_le
        (by exact_mod_cast (by omega : γ.degree < d.degree + 1)) (LeadSubst.Near.prod hn d).2.2)
      rwa [map_sub, sub_eq_zero] at h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairs
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section PairNat

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y Y' : Scheme.{0}}
  {φ : X' ⟶ X} {χ : Y' ⟶ Y} {ψ : Y ⟶ X} {ψ' : Y' ⟶ X'}

theorem pre_le_pre (e : ψ' ≫ φ = χ ≫ ψ) {V : Y.Opens} {U : X.Opens} (hp : V ≤ ψ ⁻¹ᵁ U) :
    χ ⁻¹ᵁ V ≤ ψ' ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
  exact fun x hx ↦ hp hx

variable [IsAffineHom φ] [IsAffineHom χ]

def prePairMap (e : ψ' ≫ φ = χ ≫ ψ) (p : Pair ψ) : Pair ψ' :=
  ⟨(preU χ p.1.1, preU φ p.1.2), pre_le_pre e p.2⟩

theorem prePairMap_mono (e : ψ' ≫ φ = χ ≫ ψ) : Monotone (prePairMap e) := fun _ _ h ↦
  show _ ∧ _ from ⟨preU_mono χ (Pair.le_fst h), preU_mono φ (Pair.le_snd h)⟩

def preFun (e : ψ' ≫ φ = χ ≫ ψ) : (Pair ψ)ᵒᵖ ⥤ (Pair ψ')ᵒᵖ := (prePairMap_mono e).functor.op

variable {s' : X' ⟶ Sp R'} {q' : Y' ⟶ Sp R'}


variable (s' q') in
def preCoefPair (e : ψ' ≫ φ = χ ≫ ψ) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) :
    CoefMap (RingHom.id R') (OPre φ s') (pairFst ψ ⋙ OPre χ q') where
  G := pairSnd ψ
  α p := secPull s' q' (prePairMap e p.unop)
  naturality a b := (pairPull w').naturality ((preFun e).map a) b
  smul p := semiHom_secPull w' (prePairMap e p.unop)

end PairNat

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem red_preimage_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by
  intro R R' _ _ σ X X' Y Y' s s' q q' φ χ _ h ψ ψ' w w' e hφ
  haveI := hφ
  have H := _root_.GlobalTheory.AbCoh.red_iff_pre R R' X X' s s' σ φ h
  let m := preCoefPair s' q' e w'
  let Φ := preFun (φ := φ) (χ := χ) e
  have hα : ∀ (p : (Pair ψ)ᵒᵖ) (b : (OAff s).obj ((pairSnd ψ).obj p)),
      m.α p (preα φ s s' ((pairSnd ψ).obj p) b) =
        preα χ q q' ((pairFst ψ).obj p) ((pairPull w).α p b) := by
    intro p b
    have k1 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE ψ' φ _ _ _
      (prePair φ p.unop.1.2).2 (prePairMap e p.unop).2)
    have k2 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE χ ψ _ _ _
      p.unop.2 (prePair χ p.unop.1.1).2)
    have k3 : ∀ (g₁ g₂ : Y' ⟶ X) (_ : g₁ = g₂) (h1 : (preU χ p.unop.1.1).1 ≤ g₁ ⁻¹ᵁ p.unop.1.2.1)
        (h2 : (preU χ p.unop.1.1).1 ≤ g₂ ⁻¹ᵁ p.unop.1.2.1) (x : Γ(X, p.unop.1.2.1)),
        (g₁.appLE _ _ h1).hom x = (g₂.appLE _ _ h2).hom x := by
      rintro _ _ rfl _ _ _; rfl
    refine k1.trans (Eq.trans ?_ k2.symm)
    exact k3 _ _ e _ _ b
  let θ1 : ((preRes φ s').comp m).G ⟶ ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  let θ2 : ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).G ⟶
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  have h1 : ∀ T b, ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T
      (mp (OAff s') (θ1.app T) b) = ((preRes φ s').comp m).α T b := fun T b ↦ by
    exact congrArg (((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T) (mp_id (OAff s') _ b)
  have h2 : ∀ T b, (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T
      (mp (OAff q') (θ2.app T) b) = ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T b :=
    fun T b ↦ by
      exact congrArg ((CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T) (mp_id (OAff q') _ b)
  refine ⟨fun f x hr ↦ ?_, fun v z hr ↦ ?_⟩
  · obtain ⟨c0, hc0, hcl⟩ := (H.1 f x).1 hr
    refine ⟨m.pullbackOneCocycle c0, fun a b u ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc0]; exact hα b _
    · rw [← CoefMap.pullCohomologyOne_class, hcl, ← CoefMap.pullCohomologyOne_comp]
      exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ1 h1 x).trans ((CoefMap.pullCohomologyOne_comp _ _ x).trans
        ((congrArg _ (isPullO_pullHO1 w' x)).trans ((CoefMap.pullCohomologyOne_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ2 h2 _))))
  · obtain ⟨c0, hc0, hcl⟩ := (H.2.1 v z).1 hr
    have k : (pairRes ψ' q').pull2 (pullHO2 w' z) = (pairPull w').pull2 z :=
      (LinearEquiv.ofBijective _ (pairRes_pull2_bijective ψ' q')).apply_symm_apply _
    refine ⟨m.pullbackTwoCocycle c0, fun a b d u u' ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc0]; exact hα d _
    · rw [← CoefMap.pullCohomologyTwo_class, hcl, ← CoefMap.pullCohomologyTwo_comp]
      exact (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ1 h1 z).trans ((CoefMap.pullCohomologyTwo_comp _ _ z).trans
        ((congrArg _ k.symm).trans ((CoefMap.pullCohomologyTwo_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ2 h2 _))))

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRenaming
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.Proof.ColumnInclusionRenaming

theorem fockS_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockS (rename e f) (rename e g) = fockS f g := by
  classical
  unfold fockS
  rw [support_rename_of_injective he, Finset.sum_image (fun _ _ _ _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  congr 2
  unfold mfact
  rw [Finsupp.mapDomain_support_of_injective he, Finset.prod_image (fun _ _ _ _ h => he h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective he]

def colIncl {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (r : ℕ) : Fin r × Fin n₀ → Fin r × Fin n₁ :=
  fun v => (v.1, Fin.castLE h v.2)

theorem rename_lpMinor {n₀ n₁ r : ℕ} (h : n₀ ≤ n₁) (s : ℕ) (hr : s ≤ r) (hs : s ≤ n₀) :
    rename (colIncl h r) (lpMinor ℂ s hr hs) = lpMinor ℂ s hr (hs.trans h) := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [colIncl]

theorem rename_hw {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ) :
    rename (colIncl h n₁) (hw ℂ h ν) = hw ℂ (le_refl n₁) (rowNu (r := n₁) ν) := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < n₀ := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    have : rowNu (r := n₁) ν s = 0 := by simp [rowNu, hs']
    rw [this, Nat.zero_sub, pow_zero]
  · intro s _
    rw [map_pow, rename_lpMinor]
    have e1 : rowNu (r := n₁) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    have e2 : nuNext (rowNu (r := n₁) ν) (Fin.castLE h s) = nuNext ν s := by
      unfold nuNext rowNu
      by_cases h1 : s.val + 1 < n₀
      · have h2 : s.val + 1 < n₁ := by omega
        simp [h1, h2]
      · simp [h1]
    rw [e1, e2]
    rfl

end GlobalTheory.Proof.ColumnInclusionRenaming
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
section
noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {S : Scheme.{0}}

def transl {A : Over S} [GrpObj A] (h : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ h)

def lbPow {X : Scheme.{0}} (L : LB X) (m : ℕ) : LB X :=
  LB.LinComb L (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1)

def sq2 {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    (G2 A).left ⟶ (G2 A').left :=
  (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem eta_zero {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem eta_neg {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (x : D.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, eta_zero]

def heckeSub {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (g : D.La →ₗ[D.O] D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • g x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSub {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (g : D.La →ₗ[D.O] D.La) (N : ℕ)
    (x : D.La) : o.eta (N • g x) ∈ heckeSub o g N := ⟨x, rfl⟩

theorem one_comp_transl {A : Over S} [GrpObj A] (h : 𝟙_ (Over S) ⟶ A) : (1 : 𝟙_ (Over S) ⟶ A) ≫ transl h = h := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (1 ≫ toUnit A) (𝟙 _),
    Category.id_comp, _root_.one_mul]

theorem comp_eq_one_of_transl {A A' : Over S} [GrpObj A] [GrpObj A'] (ψ : A ⟶ A') [IsMonHom ψ]
    (h : 𝟙_ (Over S) ⟶ A) (hh : (transl h).left ≫ ψ.left = ψ.left) : h ≫ ψ = 1 := by
  have e : transl h ≫ ψ = ψ := Over.OverMorphism.ext hh
  rw [← one_comp_transl h, Category.assoc, e, one_comp]

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPhaseFrameSmallAngles
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.RiemConst

lemma exp_I_arg_exp_I (t : ℝ) :
    Complex.exp (Complex.I * ((Complex.exp (Complex.I * (t : ℂ))).arg : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) := by
  have h := Complex.norm_mul_exp_arg_mul_I (Complex.exp (Complex.I * (t : ℂ)))
  have h1 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I t
  rw [h1] at h
  simpa [mul_comm] using h

lemma exp_I_neg_sum {n : ℕ} (f : Fin n → ℝ) :
    Complex.exp (Complex.I * ((-∑ k, f k : ℝ) : ℂ)) =
      (∏ k, Complex.exp (Complex.I * (f k : ℂ)))⁻¹ := by
  push_cast
  rw [mul_neg, Complex.exp_neg, Finset.mul_sum, Complex.exp_sum]

theorem phaseFrame_small_angles : ∀ (E : Type) [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (δ : ℝ), 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ θ : Ψ → Fin (r - 1) → ℝ, (∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η) → ∃ θ' : Ψ → Fin (r - 1) → ℝ, ‖θ'‖ < δ ∧ phaseFrame θ' = phaseFrame θ := by
  intro E _ Ψ r δ hδ
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (Complex.continuousAt_arg (Complex.one_mem_slitPlane)) δ hδ
  refine ⟨η, hη, fun θ hθ => ?_⟩
  refine ⟨fun τ k => (Complex.exp (Complex.I * (θ τ k : ℂ))).arg, ?_, ?_⟩
  · rw [pi_norm_lt_iff hδ]
    intro τ
    rw [pi_norm_lt_iff hδ]
    intro k
    have hk := hθ τ (Fin.castLE (Nat.sub_le r 1) k)
    have hentry : phaseFrame θ τ (Fin.castLE (Nat.sub_le r 1) k) (Fin.castLE (Nat.sub_le r 1) k)
        = Complex.exp (Complex.I * (θ τ k : ℂ)) := by
      simp only [phaseFrame, Matrix.diagonal_apply_eq, angles, Fin.coe_castLE, k.isLt, dif_pos]
    rw [hentry] at hk
    have := hcont (x := Complex.exp (Complex.I * (θ τ k : ℂ))) (by rwa [dist_eq_norm])
    rw [Complex.arg_one, Real.dist_eq, sub_zero] at this
    simpa [Real.norm_eq_abs] using this
  · funext τ
    simp only [phaseFrame]
    congr 1
    funext a
    unfold angles
    split_ifs with h
    · exact exp_I_arg_exp_I _
    · rw [exp_I_neg_sum, exp_I_neg_sum]
      congr 1
      exact Finset.prod_congr rfl fun k _ => exp_I_arg_exp_I _

end GlobalTheory.RiemConst
end

