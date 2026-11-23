module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

inductive IsSmoothBlowupSeq {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) : ∀ {Y' : Scheme.{0}}, (Y' ⟶ Y) → Prop

  | id : IsSmoothBlowupSeq f B (𝟙 Y)

  | step {Y₁ Y₂ : Scheme.{0}} {s : Y₁ ⟶ Y} (J : Y₁.IdealSheafData) (π : Y₂ ⟶ Y₁) :
      IsSmoothBlowupSeq f B s → Smooth (J.subschemeι ≫ s ≫ f) → (J.support : Set Y₁) ⊆ s ⁻¹' B →
      FinalTheorems.Blowup π J → IsSmoothBlowupSeq f B (π ≫ s)


open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in
theorem _root_.GlobalTheory.IsSmoothBlowupSeq.mono {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B B' : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (hB : B ⊆ B') : _root_.GlobalTheory.IsSmoothBlowupSeq f B' s := by
  induction h with
  | id => exact .id
  | step J π _ hsm hsupp hbl ih =>
    exact .step J π ih hsm (hsupp.trans (Set.preimage_mono hB)) hbl

namespace Principalise


open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in
theorem _root_.GlobalTheory.Principalise.effCartier_comap_of_disjoint {W X : Scheme.{0}} (g : W ⟶ X) (J : X.IdealSheafData)
    (h : ∀ w, g w ∉ J.support) : _root_.ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap g) := by
  have htop : J.comap g = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext w
    simpa using h w
  intro w
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  refine ⟨⟨V, hV⟩, 1, hwV, one_mem _, ?_⟩
  rw [htop, Ideal.span_singleton_one]
  simp [Scheme.IdealSheafData.ideal_top]


open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in
theorem _root_.GlobalTheory.Principalise.isIso_restrict_of_blowup {X X' : Scheme.{0}} {π : X' ⟶ X}
    {J : X.IdealSheafData} (h : _root_.ReciprocityTheory.AnForm.R.FinalTheorems.Blowup π J)
    (U : X.Opens) (hU : ∀ x ∈ U, x ∉ J.support) : IsIso (π ∣_ U) := by
  have hcart : ∀ (W : Scheme.{0}) (k : W ⟶ U.toScheme), _root_.ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap (k ≫ U.ι)) := by
    intro W k
    refine _root_.GlobalTheory.Principalise.effCartier_comap_of_disjoint _ J fun w => hU _ ?_
    rw [Scheme.Hom.comp_apply]
    have hmem : U.ι (k w) ∈ Set.range U.ι := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at hmem
  have hσ' := hcart U.toScheme (𝟙 _)
  rw [Category.id_comp] at hσ'
  obtain ⟨σ, hσ, -⟩ := h.2 U.toScheme U.ι hσ'
  have hsnd : IsIso (pullback.snd π U.ι) := by
    refine ⟨⟨pullback.lift σ (𝟙 _) (by rw [hσ, Category.id_comp]), ?_,
      pullback.lift_snd _ _ _⟩⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      have hg := hcart _ (pullback.snd π U.ι)
      rw [← pullback.condition] at hg
      exact (h.2 _ _ hg).unique (by rw [Category.assoc, hσ, pullback.condition]) rfl
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  rw [morphismRestrict]
  infer_instance

end Principalise


open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in
theorem _root_.GlobalTheory.IsSmoothBlowupSeq.isIso_restrict {S Y Y' : Scheme.{0}} {f : Y ⟶ S}
    {B : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (U : Y.Opens) (hU : ∀ y ∈ U, y ∉ B) : IsIso (s ∣_ U) := by
  induction h with
  | id => infer_instance
  | @step Y₁ Y₂ s J π hs hsm hsupp hbl ih =>
    rw [morphismRestrict_comp]
    have : IsIso (π ∣_ s ⁻¹ᵁ U) :=
      _root_.GlobalTheory.Principalise.isIso_restrict_of_blowup hbl _ fun x hx hxJ => hU _ hx (hsupp hxJ)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ this ih

namespace Principalise


open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in
theorem _root_.GlobalTheory.Principalise.nonempty_compl_support {Y : Scheme.{0}} [IsIntegral Y] {I : Y.IdealSheafData} (hI : I ≠ ⊥) :
    (I.support.compl : Set Y).Nonempty := by
  by_contra hne
  apply hI
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  ext x
  simp only [Set.not_nonempty_iff_eq_empty] at hne
  have : x ∉ (I.support.compl : Set Y) := by simp [hne]
  simpa using this

end Principalise

namespace Published

def Principalisation : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (Y : Scheme.{0}) (f : Y ⟶ Sp k),
    IsIntegral Y → SmoothOfRelativeDimension d f → IsProjOver f →
    ∀ I : Y.IdealSheafData, I ≠ ⊥ →
      ∃ (Y' : Scheme.{0}) (s : Y' ⟶ Y),
        IsIntegral Y' ∧ SmoothOfRelativeDimension d (s ≫ f) ∧ IsProjOver (s ≫ f) ∧
        IsSmoothBlowupSeq f (I.support : Set Y) s ∧ IsIso (s ∣_ I.support.compl) ∧
        FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support)

end Published

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt
section
noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

def PrismaticDieudonneAt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : Prop :=
  ∃ (M : PDivGroup p O → ModuleCat.{0} (Ainf p O))
    (map : ∀ G H : PDivGroup p O, (G ⟶ H) →+ (M H →ₗ[Ainf p O] M G))
    (φ : ∀ G, M G →ₛₗ[(frobenius : Ainf p O →+* Ainf p O)] M G)
    (lie : ∀ G, M G →ₛₗ[fontaineTheta O p] G.dual.Lie)
    (dR : ∀ G, M G →ₛₗ[fontaineTheta O p] G.RigExt),
    (∀ G, Module.Free (Ainf p O) (M G) ∧ Module.Finite (Ainf p O) (M G) ∧
      Module.finrank (Ainf p O) (M G) = G.height ∧
      Function.Injective (φ G) ∧ (∀ m, ∃ n, φ G n = frobenius (xi ε) • m) ∧
      Module.Projective O G.dual.Lie ∧ Function.Surjective (lie G) ∧
      (∀ m, lie G m = 0 ↔ ∃ n, φ G m = frobenius (xi ε) • n) ∧
      Function.Surjective (dR G) ∧ (∀ m, dR G m = 0 ↔ ∃ n, m = xi ε • n) ∧
      map G G (𝟙 G) = LinearMap.id) ∧
    (∀ (G H K : PDivGroup p O) (f : G ⟶ H) (g : H ⟶ K),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M H),
      map G H f (φ H m) = φ G (map G H f m) ∧
      lie G (map G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie H m) ∧
      dR G (map G H f m) = rigExtMap f (dR H m)) ∧
    (∀ G H : PDivGroup p O, Function.Injective (map G H) ∧
      ∀ u : M H →ₗ[Ainf p O] M G, (∀ m, u (φ H m) = φ G (u m)) → ∃ f, map G H f = u) ∧
    ∃ (l : M (PDivGroup.mu p O)) (e : M (const p O)),
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ l) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ e) ∧
      φ _ l = frobenius (xi ε) • l ∧ φ _ e = e ∧
      map _ _ (epsHom (zeta ε) hε.zeta_zero (zeta_succ_pow ε)) l = Sandwich.mu ε • e

def PrismaticDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [NormedAlgebra ℚ_[p] C]
    [CompleteSpace C] [IsAlgClosed C] (O : Type) [CommRing O] [Algebra O C],
    IsIntegers O C →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
      (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), PrismaticDieudonneAt hε

end GlobalTheory.Published
end
end

