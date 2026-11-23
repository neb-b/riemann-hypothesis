module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalFormOfThreeInputs
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

def genA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ s : Finset (↥(GK K) → T₂.V),
      s.card ≤ 2 * ((finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 + 1) * r) ∧
      Submodule.span ↥(OL LL) (s : Set (↥(GK K) → T₂.V)) ⊔ latticeCoboundaries T₂.L = latticeFiniteCocycles (P.PD K) T₂.L

def liftA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ J : Finset ℤ, J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      F.LiftF (P.PD K) (expLift l h J)

def killA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ s h' : ℕ, finrank ↥(K0 K) ↥K.1 * s = l - 1 ∧ 1 ≤ h' ∧ h' ≤ h + S + 1 ∧
      ∃ s₀ : Finset (↥(GK K) → T₂.V),
        s₀.card ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 * (finrank ↥(K0 K) ↥K.1 + 1) * m ∧
        (s₀ : Set (↥(GK K) → T₂.V)) ⊆ latticeFiniteCocycles (P.PD K) T₂.L ∧
        ∀ p ∈ latticeFiniteCocycles (P.PD K) T₂.L,
          (l ^ YA l (finrank ↥(K0 K) ↥K.1) s h' S η : ℕ) • p ∈
            Submodule.span ↥(OL LL) (s₀ : Set (↥(GK K) → T₂.V)) ⊔ F.ImF (P.PD K)

theorem claimA_of_steps (hG : genA P K LL) (hL : liftA P K LL) (hK : killA P K LL) :
    claimA P K LL := by
  intro T₁ T₂ F r S η m h up b hH
  obtain ⟨s, hs, hgen⟩ := hG T₁ T₂ F r S η m h up b hH
  obtain ⟨J, hJ, h0, hlift⟩ := hL T₁ T₂ F r S η m h up b hH
  obtain ⟨σ, h', hes, hh', hle, s₀, hs₀, hsub, hkill⟩ := hK T₁ T₂ F r S η m h up b hH
  refine ⟨σ, h', s.card, J, hes, hh', hle, hJ, h0, hs, s, s₀, le_rfl, hgen, hs₀, hsub, hkill, ?_⟩
  intro p hp
  have hpZ : p ∈ latticeFiniteCocycles (P.PD K) T₂.L := (Submodule.span_le.mpr hsub) hp
  have h1 := hlift p hpZ
  have e1 : ((l ^ expLift l h J : ℕ) : ↥(OL LL)) =
      ((((P.PD K).p : ℕ) : ↥(OL LL))) ^ expLift l h J := by
    rw [P.PD_p K]; push_cast; rfl
  rw [← Nat.cast_smul_eq_nsmul ↥(OL LL), e1]
  exact h1

end Local

def genR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → genA (D.loc l) K LL

def liftR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → liftA (D.loc l) K LL

def killR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → killA (D.loc l) K LL

theorem local_form_of_three_inputs (D : D7) (hG : genR D) (hL : liftR D) (hK : killR D) : LocalTheoremAtGoodExtensions D :=
  fun l _ hl K LL hg =>
    claimA_of_steps (D.loc l) K LL (hG l hl K LL hg) (hL l hl K LL hg) (hK l hl K LL hg)

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RestPt
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure RestPt {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop where

  ng0 : D.nd.l i ≠ D.host.g 0
  ng1 : D.nd.l i ≠ D.host.g 1

  good : GoodR D.nd i r

  chi1 : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)

  block : EmbeddingTypes.ambBlock i r ρ π

  chi : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ), 1 ≤ c → c ≤ D.R.t →
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c)))

  g3 : AbsIrreducibleDistinct D i r

  cont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))

  rho : IsRhoOf D.nd i π (ρ π)

  ss : IsSSRep (rhoChiK D i (ρ π))

  eps : TruncatedSeriesCountingIdentities.CyclotomicInertiaImage i

  shape : TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible i

end Formalism.MainNotions.N

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtBc
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {LL' O' : Type} [Field LL'] [Algebra Qp LL'] [TopologicalSpace LL'] [CommRing O'] [Algebra O' LL']
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem comp_inj {E : Type} [Field E] [Algebra Qp E] (ι : LL →ₐ[Qp] LL') :
    Function.Injective (fun τ : E →ₐ[Qp] LL => ι.comp τ) := by
  intro τ τ' h
  apply AlgHom.ext
  intro x
  exact ι.toRingHom.injective (congrArg (fun f : E →ₐ[Qp] LL' => f x) h)

theorem comp_bij {E : Type} [Field E] [Algebra Qp E] [FiniteDimensional Qp E] (ι : LL →ₐ[Qp] LL')
    (hcard : Nat.card (E →ₐ[Qp] LL) = finrank Qp E) :
    Function.Bijective (fun τ : E →ₐ[Qp] LL => ι.comp τ) :=
  (comp_inj ι).bijective_of_nat_card_le (hcard ▸ card_algHom_le_finrank Qp E LL')

variable [Fintype (K →ₐ[Qp] LL)] [Fintype (K →ₐ[Qp] LL')]

theorem thmELiftAt_bc (ι : LL →ₐ[Qp] LL') (v' : AddValuation LL' (WithTop ℚ))
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hfin : FiniteDimensional Qp LL') (hv' : v' (PD.p : LL') = 1)
    (hO' : ∃ hO : IsDomain O', @IsDiscreteValuationRing O' _ hO ∧ IsFractionRing O' LL')
    (hBC : BCAt PD (LL := LL) (O := O) (O' := O') ι)
    (H : ThmELiftAt PD (O := O') n (fun i => ι.comp (emb i)) v') :
    ThmELiftAt PD (O := O) n emb v := by
  intro hL h5 T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hK hJ hg hS hC hT hb1 hb2
    hW
  obtain ⟨T₁', T₂', F', hc₁', hc₂', hon', hj, -, hlift, -⟩ := hBC T₁ T₂ F hc₁ hc₂ hon
  apply hlift
  have := PD.finK
  have := PD.finK₀
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hL
  have hbK := comp_bij (E := K) ι (by rw [Nat.card_eq_fintype_card]; exact hG.1.2)
  have hbK₀ := comp_bij (E := K₀) ι (by
    rw [← Nat.card_congr (Equiv.ofBijective emb l4), Nat.card_zmod, l3])
  have hL' : Letters PD LL' v' (fun i => ι.comp (emb i)) :=
    ⟨l1, hfin, l3, hbK₀.comp l4, fun i => by
      change (ι.comp (emb (i + 1))).comp PD.σ = ι.comp (emb i)
      rw [AlgHom.comp_assoc, l5], hv'⟩
  have hG' : GoodCoeffs (K := K) (Qp := Qp) (LL := LL') (O := O') (V := T₁'.V) := by
    refine ⟨⟨hfin, ?_⟩, hc₁'.2.1, hO'⟩
    rw [← hG.1.2]
    exact (Fintype.card_of_bijective hbK).symm
  have tr₁ : ∀ (i : ZMod n) (X : Set ℤ), JumpsAtE PD T₁ emb i X →
      JumpsAtE PD T₁' (fun i => ι.comp (emb i)) i X := by
    intro i X hX τ' hτ' a ha
    obtain ⟨τ, rfl⟩ := hbK.2 τ'
    exact hX τ (comp_inj ι (by simpa [AlgHom.comp_assoc] using hτ')) a ((hj τ a).1.1 ha)
  have tr₂ : ∀ (i : ZMod n) (X : Set ℤ), JumpsAtE PD T₂ emb i X →
      JumpsAtE PD T₂' (fun i => ι.comp (emb i)) i X := by
    intro i X hX τ' hτ' a ha
    obtain ⟨τ, rfl⟩ := hbK.2 τ'
    exact hX τ (comp_inj ι (by simpa [AlgHom.comp_assoc] using hτ')) a ((hj τ a).2.1 ha)
  refine H hL' h5 T₁' T₂' F' hG' hc₁' hc₂' hon' j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂
    (fun i => tr₁ i _ (hK i)) ?_ hg hS hC hT (fun i => tr₁ i _ (hb1 i)) (fun i => tr₂ i _ (hb2 i)) hW
  intro τ' a ha
  obtain ⟨τ, rfl⟩ := hbK.2 τ'
  exact hJ τ a ((hj τ a).1.1 ha)

end Formalism.MainNotions.WachCoordinates.Br
end
end

