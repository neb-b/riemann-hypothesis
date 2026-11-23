module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceExistsUnique
section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem smul_smul_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (c : K) (x : L) (ω : DR k K) :
    (c • x) • mapDR k K L ω = x • mapDR k K L (c • ω) := by
  rw [map_smul, smul_assoc, smul_comm]

theorem trDR_isTrDR_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  intro k K L _ _ _ _ _ _ _ _ _
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L
  have uniq : ∀ T T' : DR k L →ₗ[k] DR k K, IsTrDR k K L T → IsTrDR k K L T' → T = T' := by
    intro T T' hT hT'
    refine LinearMap.ext fun y => ?_
    obtain ⟨m, b, ω, rfl⟩ := hspan y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hT, hT']
  let e := Module.finBasis K L
  let n := Module.finrank K L
  let φ : (Fin n → DR k K) →ₗ[k] DR k L :=
    { toFun := fun ω => ∑ j, e j • mapDR k K L (ω j)
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← algebraMap_smul K c (a j), map_smul, algebraMap_smul, smul_comm] }
  have hφ : Function.Bijective φ := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro ω hω
      funext j
      exact hind n e ω e.linearIndependent hω j
    · intro y
      obtain ⟨m, b, ω, rfl⟩ := hspan y
      refine ⟨fun j => ∑ i, e.repr (b i) j • ω i, ?_⟩
      change ∑ j, e j • mapDR k K L (∑ i, e.repr (b i) j • ω i) = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
  let ψ := (LinearEquiv.ofBijective φ hφ).symm
  let g : (Fin n → DR k K) →ₗ[k] DR k K :=
    { toFun := fun ω => ∑ j, Algebra.trace K L (e j) • ω j
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm] }
  have ex : IsTrDR k K L (g ∘ₗ ψ.toLinearMap) := by
    intro b ω
    have hb : b • mapDR k K L ω = φ (fun j => e.repr b j • ω) := by
      change _ = ∑ j, e j • mapDR k K L (e.repr b j • ω)
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
    rw [LinearMap.comp_apply, hb]
    have : ψ (φ (fun j => e.repr b j • ω)) = fun j => e.repr b j • ω :=
      (LinearEquiv.ofBijective φ hφ).symm_apply_apply _
    rw [LinearEquiv.coe_coe, this]
    change ∑ j, Algebra.trace K L (e j) • e.repr b j • ω = _
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    conv_rhs => rw [← e.sum_repr b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have htr : IsTrDR k K L (trDR k K L) := by
    have h : ∃ T, IsTrDR k K L T := ⟨_, ex⟩
    unfold trDR
    rw [dite_eq_left h]
    exact h.choose_spec
  exact ⟨htr, fun T hT => uniq T _ hT htr⟩

end GlobalTheory.W1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueIsTransfer
section
open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlobalTheory.EtC.Tr

variable (R : Type) [CommRing R]

theorem splits_of_splitSieve {Z X S V : Scheme.{0}} {f : Z ⟶ X} {x : S ⟶ X} {v : V ⟶ S} (hv : splitSieve f x v) :
    Splits f (v ≫ x) := by
  obtain ⟨W, w, u, ⟨m, s, hs⟩, rfl⟩ := hv
  refine ⟨m, fun j => w ≫ s j, ?_⟩
  have := GlobalTheory.T.splitBy_baseChange' hs w
  rwa [Category.assoc]

def splitSum {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) (h : Splits f y) : freeSch R V ⟶ freeSch R Z :=
  ∑ j, (free R).map (yoneda.map (h.choose_spec.choose j))

theorem splitSum_eq {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} (h : Splits f y) {m : ℕ} {s : Fin m → (V ⟶ Z)}
    (hs : SplitBy f y s) : splitSum R f y h = ∑ j, (free R).map (yoneda.map (s j)) :=
  GlobalTheory.T.freeSheaf_sum_sections_eq_of_two_splittings R h.choose_spec.choose_spec hs

theorem existsUnique_isTransfer {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] :
    ∃! t, IsTransfer R f t := by
  have hT := _root_.GlobalTheory.EtC.Tr.splitSieve_mem f (𝟙 X)

  let σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ X), splitSieve f (𝟙 X) v → (freeSch R V ⟶ freeSch R Z) :=
    fun V v hv => splitSum R f (v ≫ 𝟙 X) (splits_of_splitSieve hv)
  have hσ : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ X) (hv : splitSieve f (𝟙 X) v) (g : W ⟶ V),
      (free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) ((splitSieve f (𝟙 X)).downward_closed hv g) := by
    intro V W v hv g
    obtain ⟨m, s, hs⟩ := splits_of_splitSieve hv
    have hg := GlobalTheory.T.splitBy_baseChange' hs g
    rw [← Category.assoc] at hg
    simp only [σ, splitSum_eq R _ hs, splitSum_eq R _ hg, Preadditive.comp_sum, ← Functor.map_comp]
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_freeSch_hom_glue_of_etale_covering R (freeSch R Z) _ hT σ hσ
  have key : ∀ t', IsTransfer R f t' → ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ X) (hv : splitSieve f (𝟙 X) v),
      (free R).map (yoneda.map v) ≫ t' = σ v hv := by
    intro t' ht' V v hv
    obtain ⟨m, s, hs⟩ := splits_of_splitSieve hv
    simp only [σ, splitSum_eq R _ hs]
    have := ht'.apply_of_splitBy R hs
    rwa [Category.comp_id] at this
  refine ⟨t, ?_, fun t' ht' => ?_⟩
  · intro S x m s hs hiso
    refine GlobalTheory.T.freeSch_hom_ext_of_etale_covering R (freeSch R Z) _ _ _ (_root_.GlobalTheory.EtC.Tr.splitSieve_mem f x) (fun V v hv => ?_)
    obtain ⟨m', s', hs'⟩ := splits_of_splitSieve hv
    have hvx : splitSieve f (𝟙 X) (v ≫ x) := ⟨V, 𝟙 V, v ≫ x, (show Splits f ((v ≫ x) ≫ 𝟙 X) by rw [Category.comp_id]; exact ⟨m', s', hs'⟩), Category.id_comp _⟩
    have h1 := GlobalTheory.T.splitBy_baseChange' ⟨hs, hiso⟩ v
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ht _ hvx, Preadditive.comp_sum]
    simp only [σ, ← Functor.map_comp]
    rw [splitSum_eq R _ (show SplitBy f ((v ≫ x) ≫ 𝟙 X) (fun j => v ≫ s j) by rw [Category.comp_id]; exact h1)]
  · exact GlobalTheory.T.freeSch_hom_ext_of_etale_covering R (freeSch R Z) _ _ _ hT fun V v hv => by rw [key t' ht' v hv, ht v hv]

end GlobalTheory.EtC.Tr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
variable {k : Type} [CommRing k] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {s'' : X'' ⟶ Sp k} {f : X' ⟶ X} {g : X'' ⟶ X'}

theorem formPull_formPull (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (U : X.Opens) (j : ℕ) (x : OmU s U j) :
    formPull hg (f ⁻¹ᵁ U) j (formPull hf U j x) = formPull hgf U j x := by
  refine SemiHom.mOm_mOm (semiHom_appSec hf U) (semiHom_appSec hg (f ⁻¹ᵁ U))
    (semiHom_appSec hgf U) (fun b ↦ ?_) x
  change (f.app U ≫ g.app (f ⁻¹ᵁ U)).hom b = ((g ≫ f).app U).hom b
  rw [Scheme.Hom.comp_app]
  rfl

theorem omega_hom_ext {j : ℕ} {M : X.Modules} (φ ψ : Omega s j ⟶ M)
    (h : ∀ (U : X.Opens) (x : OmU s U j), φ.val.app (op U) ((toOmega s j).app (op U) x) =
      ψ.val.app (op U) ((toOmega s j).app (op U) x)) : φ = ψ := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
  have e₁ := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) M φ
  have e₂ := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) M ψ
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  ext U x
  exact h U.unop x

theorem omegaPull_comp (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (j : ℕ) :
    omegaPull hgf j = omegaPull hf j ≫ (Scheme.Modules.pushforward f).map (omegaPull hg j) := by
  refine omega_hom_ext _ _ fun U x ↦ ?_
  rw [omegaPull_toOmega]
  change _ = (omegaPull hg j).val.app (op (f ⁻¹ᵁ U)) ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x))
  rw [omegaPull_toOmega, omegaPull_toOmega, formPull_formPull hf hg hgf]
  rfl

theorem hodgePull_comp (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (j q : ℕ) (x : hodgeH s j q) :
    hodgePull hg j q (hodgePull hf j q x) = hodgePull hgf j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ s''
  apply (cohOn.toH' (Omega s'' j) ⊤ q).injective
  have e₁ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hg) (omegaPull hg j)
    (le_refl (g ⁻¹ᵁ ⊤)) (hodgePull hf j q x)
  have e₂ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hf) (omegaPull hf j)
    (le_refl (f ⁻¹ᵁ ⊤)) x
  have e₃ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hgf) (omegaPull hgf j)
    (le_refl ((g ≫ f) ⁻¹ᵁ ⊤)) x
  refine e₁.trans (Eq.trans ?_ e₃.symm)
  refine (congrArg (SheafPull.pull.{0, 0} g.base (toAbSheafPush (omegaPull hg j)) q _) e₂).trans ?_
  refine (SheafPull.pull_pull.{0, 0, 0} f.base g.base _ _ q _ _ _).trans ?_
  rw [omegaPull_comp hf hg hgf]
  rfl

theorem hodgePull_hodgePull {X X' X'' : Scheme.{0}} (s : X ⟶ Sp k) (f : X' ⟶ X)
    (g : X'' ⟶ X') (j q : ℕ) (x : hodgeH s j q) :
    hodgePull (s' := g ≫ f ≫ s) rfl j q (hodgePull (s' := f ≫ s) rfl j q x) =
      hodgePull (f := g ≫ f) (s' := g ≫ f ≫ s) (Category.assoc g f s) j q x :=
  hodgePull_comp rfl rfl (Category.assoc g f s) j q x

end GlobalTheory.HodgeCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweThetaLiftComponents
section
noncomputable section

namespace GlobalTheory.Proof.HoweThetaLiftComponents

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh

theorem mem_of_orthogonal_others {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (htop : ⨆ k, U k = ⊤) (p : ι) (horth : ∀ k, k ≠ p → U k ⟂ U p)
    (x : V) (hx : ∀ k, k ≠ p → ∀ y ∈ U k, inner ℂ y x = 0) : x ∈ U p := by
  have hsup : U p ⊔ (⨆ k ∈ {k | k ≠ p}, U k) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun k => ?_
    by_cases hk : k = p
    · subst hk; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun k (_ : k ∈ {k | k ≠ p}) => U k) k hk le_rfl)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup.symm ▸ Submodule.mem_top : x ∈ U p ⊔ (⨆ k ∈ {k | k ≠ p}, U k))
  have hle : (⨆ k ∈ {k | k ≠ p}, U k) ≤ (ℂ ∙ v)ᗮ := by
    refine iSup₂_le fun k hk y hy => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hv' : v = x - u := by rw [← huv]; abel
    rw [hv', inner_sub_right, hx k hk y hy, (horth k hk).inner_eq hy hu, sub_zero]
  have h0 : inner ℂ v v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hv)
  rw [inner_self_eq_zero] at h0
  rw [← huv, h0, add_zero]
  exact hu

theorem exists_inner_ne_zero {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (htop : ⨆ k, U k = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ k, ∃ y ∈ U k, inner ℂ y x ≠ 0 := by
  by_contra h
  push Not at h
  have hle : (⨆ k, U k) ≤ (ℂ ∙ x)ᗮ := iSup_le fun k y hy =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h k y hy)
  rw [htop] at hle
  exact hx (inner_self_eq_zero.1
    (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle (Submodule.mem_top : x ∈ ⊤))))

theorem eachRowHasThetaLift_of_howe :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix.ThetaGramPositiveScalar N A → (∀ i, HoweUp N A i) →
      (∀ i, TypeOrth N A i) → GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness.EachRowHasThetaLift N A := by
  intro R H what₂ N A hpos hhowe horth
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness.eachRowHasThetaLift_iff]
  rintro i σ ⟨f, hf, hf0⟩
  have hθ : what₂.thetaT (N.mu i) (N.j i) f ≠ 0 := fun h => hf0 (hpos.eq_zero i σ f hf h)
  obtain ⟨P, F, hF, hFf⟩ := exists_inner_ne_zero (A.typeV i) (A.typeV_top i) _ hθ
  refine ⟨P, ⟨f, hf, hθ⟩, fun g hg => ?_⟩
  refine mem_of_orthogonal_others (A.typeV i) (A.typeV_top i) P (fun k hk => horth i k P hk) _
    fun k hk y hy => ?_
  by_contra hne
  exact hk (hhowe i σ k P ⟨g, hg, y, hy, hne⟩ ⟨f, hf, F, hF, hFf⟩)

end GlobalTheory.Proof.HoweThetaLiftComponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoLocAppendSingleton
section
noncomputable section

namespace GlobalTheory.ParUpRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_twist (hL : ParamLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  obtain ⟨hsum, hzero, htw, -, -⟩ := hL w
  have hχ := A.locG_dim χ w
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact (hzero _ hχ).symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum _ _ _ hχ, htw _ _ _ hχ, A.locG_tw]

theorem isoLoc_twist (hL : ParamLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w).2.1 _ hχ).symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist N A hL, (hL w).1 _ _ _ hχ]

theorem isoLoc_append_singleton (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [isoLoc_twist N A hL, isoLoc_append_singleton]
  rfl

theorem ptV_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i) (hP : PtOfLoc N A i)
    {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig) {σ : what₂.FT}
    (hσ : ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w) {P : A.AV i}
    (hθ : thetaOf N A i σ P) : A.ptV i P = some x := by
  obtain ⟨P', hP', hbc⟩ := hx
  refine hP P P' x hP' fun w hw => ?_
  rw [hS σ P hθ w hw.1, ← hσ w hw, ← isoLoc_lift N A hL, hbc.2.2.2.1 w hw.1]

theorem thetaTMapsIntoEigOut (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A)
    (hS : ∀ i, SplitLift N A i) (hP : ∀ i, PtOfLoc N A i) : ThetaTMapsIntoEigOut N A := by
  intro i x Sig _ hx
  have key : MjSigOut N A i Sig ≤ (eigC N A i x).comap (what₂.thetaT (N.mu i) (N.j i)) := by
    unfold MjSigOut
    refine iSup₂_le fun σ hσ => ?_
    by_cases h0 : what₂.isot (N.j i) σ = ⊥
    · rw [h0]; exact bot_le
    obtain ⟨P, hPθ⟩ := hθ i σ h0
    have hpt : A.ptV i P = some x := ptV_of_thetaOf N A hL (hS i) (hP i) hx hσ hPθ
    rw [← Submodule.map_le_iff_le_comap]
    refine hPθ.2.trans ?_
    unfold eigC
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | A.ptV i P = some x}) => A.typeV i P) P hpt le_rfl
  exact fun f hf => key hf

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    EachRowHasThetaLift N A → ParamLaws N A → (∀ i, SplitLift N A i) → (∀ i, PtOfLoc N A i) →
      ThetaTMapsIntoEig N A :=
  fun _ _ _ N A hθ hL hS hP => thetaTMapsIntoEig_of_out N A (thetaTMapsIntoEigOut N A hθ hL hS hP)

end GlobalTheory.ParUpRoad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoSubSpanExtensionOfScalars
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isoSub_span_map : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsInv ρ W₁ → IsInv ρ W₂ → IsoSub ρ W₁ W₂ → IsoSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))) (Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))) := by
  intro k Γ _ _ L _ f a ρ W₁ W₂ h₁ h₂ ⟨e, he⟩
  obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend (W₂.subtype ∘ₗ (e : W₁ →ₗ[k] W₂))
  obtain ⟨g₂, hg₂⟩ := LinearMap.exists_extend (W₁.subtype ∘ₗ (e.symm : W₂ →ₗ[k] W₁))
  have hg₁' : ∀ v : W₁, g₁ v = (e v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₁ v
  have hg₂' : ∀ v : W₂, g₂ v = (e.symm v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₂ v
  have key : ∀ (M : Matrix (Fin a) (Fin a) k) (v : Fin a → k),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v; funext i; exact (RingHom.map_mulVec f M v i).symm
  let φ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₁).map f).mulVecLin
  let ψ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₂).map f).mulVecLin
  have hφ : ∀ w (hw : w ∈ W₁), φ (f ∘ w) = f ∘ (e ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₁).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₁' ⟨w, hw⟩)
  have hψ : ∀ w (hw : w ∈ W₂), ψ (f ∘ w) = f ∘ (e.symm ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₂).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₂' ⟨w, hw⟩)
  set S₁ := (fun v => f ∘ v) '' (W₁ : Set (Fin a → k)) with hS₁
  set S₂ := (fun v => f ∘ v) '' (W₂ : Set (Fin a → k)) with hS₂
  have mφ : ∀ x ∈ Submodule.span L S₁, φ x ∈ Submodule.span L S₂ := by
    intro x hx
    have : Submodule.span L S₁ ≤ (Submodule.span L S₂).comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change φ (f ∘ w) ∈ Submodule.span L S₂
      rw [hφ w hw]
      exact Submodule.subset_span ⟨_, (e ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have mψ : ∀ x ∈ Submodule.span L S₂, ψ x ∈ Submodule.span L S₁ := by
    intro x hx
    have : Submodule.span L S₂ ≤ (Submodule.span L S₁).comap ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change ψ (f ∘ w) ∈ Submodule.span L S₁
      rw [hψ w hw]
      exact Submodule.subset_span ⟨_, (e.symm ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have ψφ : ∀ x ∈ Submodule.span L S₁, ψ (φ x) = x := by
    intro x hx
    have : Set.EqOn (ψ ∘ₗ φ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₁ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hφ w hw, hψ _ (e ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  have φψ : ∀ x ∈ Submodule.span L S₂, φ (ψ x) = x := by
    intro x hx
    have : Set.EqOn (φ ∘ₗ ψ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₂ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hψ w hw, hφ _ (e.symm ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  let φ' : Submodule.span L S₁ →ₗ[L] Submodule.span L S₂ := φ.restrict mφ
  let ψ' : Submodule.span L S₂ →ₗ[L] Submodule.span L S₁ := ψ.restrict mψ
  refine ⟨LinearEquiv.ofLinear φ' ψ'
    (LinearMap.ext fun x => Subtype.ext (φψ x x.2))
    (LinearMap.ext fun x => Subtype.ext (ψφ x x.2)), ?_⟩
  intro g v hv
  show φ (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec v)
      = ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec (φ v)
  have : Set.EqOn (φ ∘ₗ ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin)
      (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin ∘ₗ φ) S₁ := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
    have hgw : (ρ g : Matrix (Fin a) (Fin a) k).mulVec w ∈ W₁ := h₁ g w hw
    rw [key, hφ _ hgw, hφ w hw, key]
    congr 1
    exact he g ⟨w, hw⟩ hgw
  exact LinearMap.eqOn_span' this v.2

end GlobalTheory
end

