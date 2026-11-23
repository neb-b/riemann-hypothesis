module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0024
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0023
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleRelativeStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.blowup_ample_relative : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  first | exact @_root_.GlobalTheory.exists_ample_pull_sub_eff | exact _root_.GlobalTheory.exists_ample_pull_sub_eff | (intros; apply _root_.GlobalTheory.exists_ample_pull_sub_eff <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsMultiplierIdeal
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.MultIdealExists

theorem isProper_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem exists_isMultIdeal : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B hη hm hres
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hres.smooth
  haveI : IsProper (s ≫ p) := isProper_of_isProjOver' hres.proj
  haveI : IsProper p := isProper_of_isProjOver' hp
  haveI : QuasiCompact s := QuasiCompact.of_comp s p
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor k Y (s ≫ p) n hres.proj (pullCart s G - m • K) m
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_pushforward_regular_ideal X Y s (-F)
  exact ⟨J, (GlobalTheory.T.multiplier_ideal_independent k X p n hp η m G Y s K B F hη hm hres hF J).2 hJ⟩

end GlobalTheory.MultIdealExists
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreadingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.kawamata_viehweg_spreading : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  first | exact @_root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType | exact _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType | (intros; apply _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierOpenStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.log_resolution_multiplier_open : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  first | exact @_root_.GlobalTheory.Discrepancy.isOpen_kltAt_and_lcAt_of_isLogRes | exact _root_.GlobalTheory.Discrepancy.isOpen_kltAt_and_lcAt_of_isLogRes | (intros; apply _root_.GlobalTheory.Discrepancy.isOpen_kltAt_and_lcAt_of_isLogRes <;> assumption)
end

