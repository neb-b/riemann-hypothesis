module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechVanishingFrobeniusDescentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.cech_vanishing_frobenius_descent : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : ℕ → CartierDiv X), Decomp p 𝒜 → (∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c) → ∀ e₀ : ℕ, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e₀) a) b) → ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G 0) a) b := by
  first | exact @_root_.GlobalTheory.LogDR.descend_vanishing | exact _root_.GlobalTheory.LogDR.descend_vanishing | (intros; apply _root_.GlobalTheory.LogDR.descend_vanishing <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem relSnc_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → RelSnc f d L σ → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) := by
  intro R R' _ _ φ X X' f f' π d s L σ hpb h
  refine ⟨fun i => ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (h.isLB i) π, fun x => ?_⟩
  obtain ⟨C, hC⟩ := h.chart (π.base x)
  obtain ⟨C', hC'⟩ := sncChart_baseChange R R' φ X X' f f' π d s L σ C hpb
  exact ⟨C', by rw [hC']; exact hC⟩

end GlobalTheory.LogPair
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SerreVanishingSncAtlas
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem spanForms_eq_bot_of_isCoord {K : Type} [Field K] {n : ℕ} {x : Fin n → Kˣ} (hx : IsCoord x)
    (M : Set K) (H : Set Ω[K⁄ℤ]) {a : ℕ} (ha : n < a) : spanForms M H a = ⊥ := by
  let bs : Module.Basis (Fin n) K Ω[K⁄ℤ] := Module.Basis.mk hx.1 hx.2.ge
  haveI : Module.Finite K Ω[K⁄ℤ] := Module.Finite.of_basis bs
  have hfr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis bs, Fintype.card_fin]
  refine eq_bot_iff.2 ((AddSubgroup.closure_le _).2 ?_)
  rintro η ⟨c, -, v, -, rfl⟩
  have hv : ¬ LinearIndependent K v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, hfr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ v hv, smul_zero]
  exact AddSubgroup.zero_mem _

theorem logAt_eq_bot_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (Z : Set X) (G : CartierDiv X) {a : ℕ} (ha : n < a) (y : X) :
    logAt Z G a y = ⊥ := by
  have hg : genericPoint X ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, -⟩ := (Opens.mem_iSup).1 hg
  exact spanForms_eq_bot_of_isCoord ((𝒜.chart i).chart _ (𝒜.gen i)).coord _ _ ha

theorem cechFam_eq_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) {a : ℕ} (ha : n < a) :
    cechFam 𝒜 G a = cechFam 𝒜 G (n + 1) := by
  funext s
  simp only [cechFam, logSec, latSec, logAt_eq_bot_of_lt 𝒜 _ G ha,
    logAt_eq_bot_of_lt 𝒜 _ G (Nat.lt_succ_self n)]

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem exists_cechZero_cechFam_nsmul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  intro k _ X _ f hf C _ E n ι _ _ 𝒜 H B R hH
  haveI : IsProper f := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  haveI : X.IsSeparated := by
    constructor
    rw [show terminal.from X = f ≫ terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  letI := algebraΓOfHom f
  have key : ∀ (j : Fin B) (a : Fin (n + 2)), ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ b : ℕ, 0 < b →
      DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
    intro j a
    obtain ⟨F, ⟨lm⟩⟩ := GlobalTheory.T.exists_lattice_model X (logAt (suppAll E) (R j) a)
      (fun y g v hg hv => logAt_smul_mem X _ _ _ y g v hg hv)
    haveI : IsFiniteQC F := GlobalTheory.T.log_forms_lattice_finite X E 𝒜 (R j) a F lm
    have hev := eventually_subsingleton_coh_twistZ_of_isProjOver (f := f) (fun _ => rfl) F hf hH
    obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
    refine ⟨q₀, fun q hq b hb => ?_⟩
    obtain ⟨lm'⟩ := nonempty_latModel_twist X (logAt (suppAll E) (R j) a)
      (logAt (suppAll E) (q • H + R j) a) F (q • H) (toLB (q • H)) _ (presents_toLB _)
      (fun y g v hD => by rw [add_comm]; exact logtwist X _ _ _ _ y g v hD) lm
    haveI : IsFiniteQC (twist F (toLB (q • H))) := isFiniteQC_twist (isLB_toLB _)
    have hc := GlobalTheory.T.cech_lattice_cohomology_vanish X (logAt (suppAll E) (q • H + R j) a) (twist F (toLB (q • H))) 𝒜.U lm'
      𝒜.affine 𝒜.gen 𝒜.cover b hb
    refine hc.2 ?_
    haveI hs : Subsingleton (coh (twist F (lbZPow (toLB H) (q : ℤ))) b) := hq₀ q hq b hb
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F (isLB_toLB (q • H)) (isLB_lbZPow (isLB_toLB H) q)
      (by rw [cls_lbZPow (isLB_toLB H), ← toPic_apply, ← toPic_apply, map_nsmul, natCast_zsmul])
    exact (cohOn.mapIso k ⊤ b e).injective.subsingleton
  choose q₁ hq₁ using key
  obtain ⟨Q, hQ⟩ := Finite.exists_le (fun p : Fin B × Fin (n + 2) => q₁ p.1 p.2)
  refine ⟨Q, fun q hq j a b hb => ?_⟩
  by_cases ha : a ≤ n + 1
  · exact hq₁ j ⟨a, by omega⟩ q ((hQ (j, ⟨a, by omega⟩)).trans hq) b hb
  · rw [cechFam_eq_of_lt 𝒜 _ (by omega : n < a)]
    exact hq₁ j ⟨n + 1, by omega⟩ q ((hQ (j, ⟨n + 1, by omega⟩)).trans hq) b hb

end GlobalTheory.LogDR
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_line_bundle : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  first | exact @_root_.GlobalTheory.LogPair.exists_finset_sec_descends | exact _root_.GlobalTheory.LogPair.exists_finset_sec_descends | (intros; apply _root_.GlobalTheory.LogPair.exists_finset_sec_descends <;> assumption)
end

