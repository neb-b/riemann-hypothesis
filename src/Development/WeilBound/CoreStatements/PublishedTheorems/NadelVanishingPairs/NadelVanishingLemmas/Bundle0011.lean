module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSections
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSectionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.cartier_operator_log_sections : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (𝒜.x j) γ → CartierAt (extD _) γ (fun a => logSec (suppAll E) G a (inter 𝒜.U s)) (fun a => logSec (suppAll E) (p • G + ∑ c, r c • E c) a (inter 𝒜.U s)) := by
  first | exact @_root_.GlobalTheory.cartierAt_atlas_inter | exact _root_.GlobalTheory.cartierAt_atlas_inter | (intros; apply _root_.GlobalTheory.cartierAt_atlas_inter <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SerreVanishingSncAtlasStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.serre_vanishing_snc_atlas : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  first | exact @_root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add | exact _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add | (intros; apply _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutMorphism
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SecDescent

theorem lbSec_descends_to_subring : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X) (hL : L.IsLB) (σ : L.Sec), IsPullback π f f₀ (spMap R₀.subtype) → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ (L₁ : LB X₁) (h₁ : L₁.IsLB) (σ₁ : L₁.Sec), cls L hL = CechPic.pull j (cls L₁ h₁) ∧ SameDiv σ (Cartier.secPull σ₁ j) := by
  intro k _ R₀ X X₀ f f₀ π _ L hL σ hp
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring k R₀ X X₀ f f₀ π L hp hL
  let R' : Subring k := R₀ ⊔ Subring.closure (S : Set k)
  have h' : R₀ ≤ R' := le_sup_left
  have hs' : (S : Set k) ⊆ R' := fun x hx => (le_sup_right : _ ≤ R') (Subring.subset_closure hx)
  let a : Sp R' ⟶ Sp R₀ := spMap (Subring.inclusion h')
  have e₁ : spMap R'.subtype ≫ a = spMap R₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have PX' := IsPullback.of_hasPullback f₀ a
  let j' : X ⟶ pullback f₀ a := PX'.lift π (f ≫ spMap R'.subtype) (by rw [Category.assoc, e₁, hp.w])
  have hj₁ : j' ≫ pullback.fst f₀ a = π := PX'.lift_fst _ _ _
  have hj₂ : j' ≫ pullback.snd f₀ a = f ≫ spMap R'.subtype := PX'.lift_snd _ _ _
  obtain ⟨L', hL', hI⟩ := hS R' h' hs' _ _ _ j' PX' hj₁ hj₂
  have hLj : (L'.pull j').IsLB := LB.isLB_pull hL' j'
  obtain ⟨τ, hστ⟩ := _root_.GlobalTheory.LogPair.exists_sameDiv_of_lbIso X L (L'.pull j') σ hL hLj hI
  have QX : IsPullback j' f (pullback.snd f₀ a) (spMap R'.subtype) :=
    IsPullback.of_right (by rw [hj₁, e₁]; exact hp) hj₂ PX'
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.spread_out_line_bundle k R' X (pullback f₀ a) f (pullback.snd f₀ a) j' L' τ QX hL'
  refine ⟨S ∪ F₂, fun R₁ hR hs X₁ f₁ π₁ j hp₁ hjπ hjf => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hs
  have hle : R' ≤ R₁ := sup_le hR (Subring.closure_le.2 hs.1)
  let b : Sp R₁ ⟶ Sp R' := spMap (Subring.inclusion hle)
  have e₂ : b ≫ a = spMap (Subring.inclusion hR) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e₃ : spMap R₁.subtype ≫ b = spMap R'.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let q : X₁ ⟶ pullback f₀ a := PX'.lift π₁ (f₁ ≫ b) (by rw [Category.assoc, e₂, hp₁.w])
  have hq₁ : q ≫ pullback.fst f₀ a = π₁ := PX'.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd f₀ a = f₁ ≫ b := PX'.lift_snd _ _ _
  have QX₁ : IsPullback q f₁ (pullback.snd f₀ a) b :=
    IsPullback.of_right (by rw [hq₁, e₂]; exact hp₁) hq₂ PX'
  have hjq : j ≫ q = j' := by
    apply PX'.hom_ext
    · rw [Category.assoc, hq₁, hjπ, hj₁]
    · rw [Category.assoc, hq₂, reassoc_of% hjf, e₃, hj₂]
  obtain ⟨τ₁, hτ₁⟩ := hF₂ R₁ hle hs.2 X₁ f₁ q j QX₁ hjq hjf
  refine ⟨L'.pull q, LB.isLB_pull hL' q, τ₁, ?_, GlobalTheory.T.same_divisor_trans X L (L'.pull j') _ σ τ _ hLj hστ hτ₁⟩
  rw [(CechPic.cls_eq_iff hL hLj).2 hI, CechPic.cls_pull hL' j' hLj, CechPic.cls_pull hL' q, ← hjq,
    CechPic.pull_comp]

end GlobalTheory.SecDescent
end

