module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryPlaceFamilyAtLevelMono
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallRingElemOfFractionMapIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem exists_small_ring_elem_of_fraction_map_integral {D : D7} (X : NTw D.R D.host D.what₂ D.LL0 D.nd) (i : X.Tw) (z : FractionRing (X.O0 i))
    (y : X.O i) (h : fracMap X i z = algebraMap (X.O i) (FractionRing (X.O i)) y) :
    ∃ a : X.O0 i, algebraMap (X.O0 i) (FractionRing (X.O0 i)) a = z := by
  haveI := GlobalTheory.TwistChoice.isLocalHom_O (X := X) i
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger (X.O0 i) z with ⟨a, e⟩ | ⟨c, e⟩
  · exact ⟨a, e⟩
  · by_cases hc : IsUnit c
    · obtain ⟨u, rfl⟩ := hc
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap (X.O0 i) (FractionRing (X.O0 i)) (u : X.O0 i) *
          algebraMap (X.O0 i) (FractionRing (X.O0 i)) ((u⁻¹ : (X.O0 i)ˣ) : X.O0 i) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [e] at h1
      rw [← inv_inv z]
      exact (eq_inv_of_mul_eq_one_right h1)
    · exfalso
      have e2 : algebraMap (X.O i) (FractionRing (X.O i)) (y * algebraMap (X.O0 i) (X.O i) c) = 1 := by
        rw [map_mul, ← h, ← fracMap_algebraMap, ← map_mul, e, mul_inv_cancel₀ hz, map_one]
      have e3 : y * algebraMap (X.O0 i) (X.O i) c = 1 :=
        IsFractionRing.injective (X.O i) (FractionRing (X.O i)) (by rw [e2, map_one])
      exact hc (isUnit_of_map_unit (algebraMap (X.O0 i) (X.O i)) c (isUnit_iff_exists_inv.2 ⟨y, by rw [mul_comm]; exact e3⟩))

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem delAt_unr {D : D7} (cf : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hS : P ∉ D.ntw.S0 i) :
    (cf.delAt (D.ntw.l i)).UnrAt P := by
  have hD : P ∉ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := fun h =>
    hS (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq i]; exact h))
  unfold CharFrame.delAt
  split_ifs with h
  · rw [if_pos h] at hD
    exact cf.isDel'.unr P hD
  · rw [if_neg h] at hD
    exact cf.isDel.unr P hD

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem toC_delta {D : D7} (cf : CharFrame D) (i : D.ntw.Tw) {b : Bool} (ρ : GlobalTheory.Triple.Reading D.ntw i b)
    {P : PlE D.host} (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (xd : D.LL0)
    (hxd : D.what₂.embLL (xd : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val P)⁻¹ : ℂˣ).1)
    (hdel : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) =
      D.ntw.emb0 i xd) :
    ρ.toC (((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ)) : D.ntw.O0 i) =
      (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)⁻¹ := by
  set δ : ℂ := (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) with hδ
  have hδ0 : δ ≠ 0 := Units.ne_zero _
  have hz : ‖δ‖ = 1 := cf.delAt_unitary _ _
  rw [Units.val_inv_eq_inv_val] at hxd
  have hread : ρ.toC ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = ρ.ι (ρ.κ (D.ntw.emb0 i xd)) := by
    rw [Reading.toC_apply, ← hdel]; rfl
  cases b
  ·
    have hx0 : (xd : D.what₂.LL) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxd; exact inv_ne_zero hδ0 hxd.symm
    have hstar : ((xd⁻¹ : D.LL0) : D.what₂.LL) = star (xd : D.what₂.LL) := by
      apply D.what₂.embLL.injective
      rw [D.starLL_cx, hxd, ← Complex.inv_eq_conj (by rw [norm_inv, hz, inv_one]), inv_inv]
      rw [IntermediateField.coe_inv, map_inv₀, hxd, inv_inv]
    have e : D.ntw.emb0 i xd = D.ntw.emb0b i xd⁻¹ := (D.ntw.restX_coefficientEmbedding_conj i xd⁻¹ xd ?_).symm
    · have h1 := ρ.read xd⁻¹
      simp only [embSide, Bool.false_eq_true, if_false] at h1
      simp only [Bool.false_eq_true, if_false]
      rw [map_units_inv, hread, e, h1]
      show (D.what₂.embLL ((xd⁻¹ : D.LL0) : D.what₂.LL))⁻¹ = δ⁻¹
      rw [IntermediateField.coe_inv, map_inv₀, hxd, inv_inv]
    · rw [hstar, star_star]
  · have h1 := ρ.read xd
    simp only [embSide, if_true] at h1
    simp only [if_true, hread, h1]
    exact hxd

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem hEig_eq_heckeVal : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → EigTrue D cf Rw Sb eig → ∀ i (s : D.ntw.Sig i) (ρ : GlobalTheory.Triple.Reading D.ntw i (D.ntw.side i s)) (π : D.naut.CG D.R.r), GlobalTheory.EigTie.IsRowPar Rw (Bs.rowS i s) π → ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → ∃ x : D.ntw.O0 i, algebraMap (D.ntw.O0 i) (D.ntw.O i) x = D.ntw.hEig i s k P ∧ ρ.toC x = GlobalTheory.Triple.heckeVal (GlobalTheory.Triple.muBase cf (D.ntw.l i) (GlobalTheory.Triple.jIdx s)) π k P := by
  intro D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hπ k P hk hP hS
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact ⟨1, by rw [map_one, Bs.hEig_zero], by rw [map_one, heckeVal_zero]⟩
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hS (D.ntw.twistExcludedPlaces_contains_residueChar i h)
  obtain ⟨xd, hxd, hdel⟩ := Bs.deltaRead i P hl (delAt_unr cf i hS) _ σ (D.nd.plOm.2 P) hσ
  set u : (D.ntw.O0 i)ˣ := if D.ntw.side i s then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ with hu
  have hc : Bs.cHk i (D.ntw.side i s) P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom u :=
    Bs.cHk_del i (D.ntw.side i s) P hS σ hσ
  set e : ↥D.LL0 := eig (D.ntw.jS i s) (Bs.rowS i s) k P with he
  set z : FractionRing (D.ntw.O0 i) := embSide D.ntw i (D.ntw.side i s) e with hz
  have hrow := Bs.rowS_eig i s k P hk1 hk hP hS
  have hread : (show FractionRing (D.ntw.O i) from readLL0 S i (D.ntw.side i s) e) = fracMap D.ntw i z := rfl
  rw [hread, hc] at hrow
  set A : D.ntw.O0 i →+* FractionRing (D.ntw.O i) :=
    (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)) with hA
  have hcu : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      ((Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom u : (D.ntw.O i)ˣ) : D.ntw.O i) = A u := rfl
  rw [hcu] at hrow
  have hAu : A (u : D.ntw.O0 i) * A ((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]

  have hzO : fracMap D.ntw i z = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      (D.ntw.hEig i s k P * algebraMap (D.ntw.O0 i) (D.ntw.O i) (((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ k)) := by
    rw [map_mul, hrow, map_pow, map_pow]
    change _ = A (u : D.ntw.O0 i) ^ k * fracMap D.ntw i z * A ((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ k
    rw [mul_comm _ (fracMap D.ntw i z), mul_assoc, ← mul_pow, hAu, one_pow, mul_one]
  obtain ⟨a, ha⟩ := exists_small_ring_elem_of_fraction_map_integral D.ntw i z _ hzO
  refine ⟨(u : D.ntw.O0 i) ^ k * a, ?_, ?_⟩
  · apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
    rw [hrow, ← fracMap_algebraMap, map_mul, map_mul, ha, map_pow, map_pow, fracMap_algebraMap]
    rfl
  · have hloc : D.naut.locG π P = Rw.locR (Bs.rowS i s) P := hπ.2 P hP
    obtain ⟨hocc, hgood, -⟩ := Bs.rhoS i s
    have hocc' : D.what₂.isot ((jIdx s).1 + 1) (Bs.rowS i s) ≠ ⊥ := by rwa [jIdx_add_one]
    have hET' := (hET (jIdx s) (Bs.rowS i s) hocc' hgood P hP (fun h => hS (hSb i h))).2 k hk1 hk
    rw [jIdx_add_one] at hET'
    have hδ : ρ.toC (u : D.ntw.O0 i) = _ := toC_delta cf i ρ σ xd hxd hdel
    have hae : ρ.toC a = D.what₂.embLL (e : D.what₂.LL) := by
      rw [Reading.toC_apply]
      change ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) a)) = _
      rw [ha, hz, ρ.read]
      rfl
    rw [map_mul, map_pow, hδ, hae, he, hET', heckeVal, satake, hloc, muBase, HChar.val_mul, Units.val_mul]
    set q : ℂ := ((normV P : ℕ) : ℂ)
    set c : ℂ := (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)⁻¹
    have hmap : (D.naut.frobEig (Rw.locR (Bs.rowS i s) P)).map (fun a =>
        a⁻¹ * ((((cf.mu0 (jIdx s)).val P : ℂˣ) : ℂ) * (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ))⁻¹ * (q ^ (D.R.nV / 2))⁻¹) =
        ((D.naut.frobEig (Rw.locR (Bs.rowS i s) P)).map (fun a =>
          a⁻¹ * (((cf.mu0 (jIdx s)).val P : ℂˣ) : ℂ)⁻¹ * (q ^ (D.R.nV / 2))⁻¹)).map (fun y => c • y) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun a _ => ?_
      simp only [Function.comp_apply, smul_eq_mul, c, mul_inv]
      ring
    rw [hmap, ← Multiset.pow_smul_esymm, smul_eq_mul]
    ring

end GlobalTheory.TwInputs.HEig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTieWithSeries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesInstall

variable {D : D7} {ρ : Setup D.ntw}

abbrev RdV (D : D7) (ρ : Setup D.ntw) : Type :=
  ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k]
    (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)

def rdVLin (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k]
      Via (D.ntw.Ok i k) (ρ.ek i b k) (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank) where
  toFun f := rdV i j b k Q ψ f
  map_add' f g := map_add _ f g
  map_smul' c f := by
    rw [← algebraMap_smul (FractionRing (D.ntw.Ok i k)) c f, map_smulₛₗ]
    rfl


open Classical in
def latI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i n b k Q ψ)
  | 0, b, k, Q, ψ => D.nexp.MtLat i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => if h : n < D.R.m ∧ TwOK i k Q ψ then
      (Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)).comap (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) else D.nexp.MtLat i (n + 1) b k Q ψ

def Onto (ρ : Setup D.ntw) (rdV : RdV D ρ) : Prop :=
  ∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧
    Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤

theorem latI_eq (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) :
    latI rdV i ((j : ℕ) + 1) b k Q ψ = (Via.lat (ρ.mt i j b k Q ψ)).comap (rdVLin rdV i j b k Q ψ) :=
  dif_pos ⟨j.2, h⟩

theorem mem_latI (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) (f) :
    f ∈ latI rdV i ((j : ℕ) + 1) b k Q ψ ↔ rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ := by
  rw [latI_eq rdV j h]; exact Iff.rfl

theorem latI_fg (rdV : RdV D ρ) (hV : Onto ρ rdV) (hL : ρ.LatFG) (i) :
    ∀ n b k Q ψ, (latI rdV i n b k Q ψ).FG
  | 0, b, k, Q, ψ => D.nexp.MtLat_fg i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · rcases hV i ⟨n, h.1⟩ b k Q ψ h.2 with ⟨hinj, hon, _⟩
      refine Submodule.fg_of_fg_map_injective (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) hinj ?_
      rw [Submodule.map_comap_eq_self (f := rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) (q := Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ))
        fun x (hx : x ∈ Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)) => by obtain ⟨y, hy⟩ := hon (Via.out _ _ x) hx; exact ⟨y, hy⟩]
      exact Via.lat_fg (hL i ⟨n, h.1⟩ b k Q ψ h.2)
    · exact D.nexp.MtLat_fg i (n + 1) b k Q ψ

theorem latI_span (rdV : RdV D ρ) (hV : Onto ρ rdV) (i) :
    ∀ n b k Q ψ, Submodule.span (FractionRing (D.ntw.Ok i k)) (latI rdV i n b k Q ψ : Set (D.nexp.MtV i n b k Q ψ)) = ⊤
  | 0, b, k, Q, ψ => D.nexp.MtLat_span i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · exact (hV i ⟨n, h.1⟩ b k Q ψ h.2).2.2
    · exact D.nexp.MtLat_span i (n + 1) b k Q ψ

variable (hρ : ρ.Good) (rd : Rds D.nexp ρ) (hF : ∀ i j b, Faithful (rd i j b))

include hF in
theorem exists_thPI (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    ∃ φ : D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b,
      ∀ f, ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) ∈ Set.range (rdK (rd i j b) hρ k) →
        rdK (rd i j b) hρ k (φ f) = ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) :=
  exists_lift ((ρ.sum i j b k Q ψ).comp (rdV i j b k Q ψ)) (rdK (rd i j b) hρ k) ((hF i j b).injective_rdK hρ k)
    (divisible_baseChange D.nexp i _ b k)

def thPI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ,
    D.nexp.MtV i n b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i n b
  | 0, _, _, _, _ => 0
  | n + 1, b, k, Q, ψ => if h : n < D.R.m then (exists_thPI hρ rd hF rdV i ⟨n, h⟩ b k Q ψ).choose else 0

theorem exists_tie_withSeries : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) → ρ.LevelOf D.nexp → ρ.LatFG → ∀ rdV : ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank), (∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧ Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤) → ∃ Dat th lev thPsi h1 thU thP MtLat h2 h3, (∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, IsEmpty (Dat i j b)) ∧ ∃ t : Comparison₂ hρ (Y := { D.nexp with Dat := Dat, th := th, lev := lev, thPsi := thPsi, thPsi_one := h1, thU := thU, thP := thP, MtLat := MtLat, MtLat_fg := h2, MtLat_span := h3 }) rd, ∀ i j b, (t i j b).rdV = rdV i j b := by
  intro D ρ hρ rd hF hU hL rdV hV
  refine ⟨Model.Dat rd, Model.th rd, Model.lev rd, Model.thPsi hρ rd, Model.thPsi_one hρ rd hF, Model.thU rd,
    thPI hρ rd hF rdV, latI rdV, latI_fg rdV hV hL, latI_span rdV hV, ?_, ?_⟩
  · intro i n hn b
    cases n with
    | zero => exact ⟨fun d => d.elim⟩
    | succ n =>
      refine ⟨fun d => hn (Finset.mem_Icc.2 ⟨Nat.succ_pos n, d.1⟩)⟩
  · refine ⟨fun i j b =>
      { supp := fun d => d.2.s
        cls := fun d => d.2.h
        coef := fun d => d.2.P
        rdV := rdV i j b
        U_eq := hU.U_eq i j b
        psiU_eq := hU.psiU_eq i j b
        dat := fun d => d.2.isDatum
        dat_onto := fun s h P h1 h2 => ⟨⟨j.2, s, h, P, h1, h2⟩, rfl, rfl, rfl⟩
        lev_iff := fun _ _ => Set.Finite.mem_toFinset _
        th_eq := fun d => d.2.rat.choose_spec
        thPsi_iff := fun _ _ _ _ _ _ => Iff.rfl
        thU_eq := fun Q M d hQ x hx => by
          have h : InRange D.ntw i Q ∧ ∀ a, ρ.xi i j b D.nexp Q M d.2.h d.2.P a ∈ Set.range (rd i j b) :=
            ⟨hQ, fun a => ⟨x a, hx a⟩⟩
          refine (dif_pos h).trans (congrArg (grpSum D.nexp (ρ.ch i) Q M) (funext fun a => (hF i j b).injective ?_))
          exact (h.2 a).choose_spec.trans (hx a).symm
        thU_off := fun _ _ _ h => dif_neg h
        rdV_inj := fun k Q ψ h => (hV i j b k Q ψ h).1
        mtLat_iff := fun k Q ψ h F => by
          refine ⟨fun hF' => ?_, fun ⟨f, hf, e'⟩ => ?_⟩
          · obtain ⟨f, rfl⟩ := (hV i j b k Q ψ h).2.1 F hF'
            exact ⟨f, (mem_latI rdV j h f).2 hF', rfl⟩
          · exact e' ▸ (mem_latI rdV j h f).1 hf
        thP_eq := fun k Q ψ _ f hf => by
          have e : thPI hρ rd hF rdV i ((j : ℕ) + 1) b k Q ψ = (exists_thPI hρ rd hF rdV i j b k Q ψ).choose := dif_pos j.2
          exact (congrArg (fun φ => rdK (rd i j b) hρ k (φ f)) e).trans
            ((exists_thPI hρ rd hF rdV i j b k Q ψ).choose_spec f hf) }, fun _ _ _ => rfl⟩

end GlobalTheory.SeriesInstall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFull

theorem baseFrame_one_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (h : Lev.IsBaseFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  ext x
  constructor
  · intro hx
    simpa using h2 x hx
  · intro hx
    simpa using h1 x hx

theorem latAt_isFullLattice : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (h : GA D (Vc D j)), Submodule.IsFullLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) := by
  intro D ρ hρ i j b h
  open Matrix in
  have heq : (ρ.B i j b).latAt (finPt (Vc D j) h) = Bridge.hLat (Vc D j) (finPt (Vc D j) h) := by
    have hΛ := baseFrame_one_eq _ _ _ (hρ.latS i j b)
    have e : Bridge.hLat (Vc D j) (finPt (Vc D j) h) = Submodule.span (𝓞 D.host.E) {x : Fin (Vc D j).rank → D.host.E |
        Matrix.mulVec ((finPt (Vc D j) h).1⁻¹).1 (fun i => (1 : Formalism.L2.Herm.Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
          GlobalTheory.AdLat.hat D.host.F ((ρ.B i j b).F.ΛS : Set (Fin (Vc D j).rank → D.host.E))} := by
      unfold Bridge.hLat
      rw [hΛ]
      rfl
    rw [e, ← Submodule.span_eq ((ρ.B i j b).latAt (finPt (Vc D j) h))]
    congr 1
    ext x
    have e : ((Formalism.UG.bc (Lev.swapAE D) (finPt (Vc D j) h).1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
        fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E ((((finPt (Vc D j) h).1⁻¹).1 *ᵥ (fun i => (1 : Formalism.L2.Herm.Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
      rw [← map_inv]
      funext i
      change _ = Lev.swapAE D _
      rw [RingHom.map_mulVec (Lev.swapAE D)]
      rfl
    change ((Formalism.UG.bc (Lev.swapAE D) (finPt (Vc D j) h).1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (ρ.B i j b).F.ΛS ↔ _
    rw [e]
    constructor
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat (ρ.B i j b).F.ΛS _ hz
      simpa only [Set.mem_setOf_eq, AlgEquiv.symm_apply_apply] using this
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL (ρ.B i j b).F.ΛS _ hz
  rw [heq]
  obtain ⟨-, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D j)
  obtain ⟨Λ, hΛ, hΛfg, hΛspan, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E
    (Vc D j).rank (GlobalTheory.Member.latC (Vc D j)) (finPt (Vc D j) h).1 hfg hspan
  rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat _ _).trans hΛ.symm)]
  exact { toIsLattice := Submodule.IsLattice.of_fg D.host.E hΛfg, span_eq_top := hΛspan }

theorem latAt_isLattice (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (h : GA D (Vc D j)) : Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) :=
  (latAt_isFullLattice D ρ hρ i j b h).toIsLattice

end GlobalTheory.LatFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharacterEqLadicHeckeCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwChiGal

open GlobalTheory.GalChar (IsGal toQ inQ block)

theorem firstTwistCharacter_eq_ladic_heckeCharacter : ∀ (D : D7) (cf : CharFrame D) (chiD : Formalism.L2.NC.NChiData D), Formalism.L2.NC.NormalizedCharacterCompatibility D chiD → (∀ x, chiD.etaT.χ x = cf.eta.1 x) → (∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x) → (∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x) → ValLL0 D cf → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (i : D.ntw.Tw) (b : Bool) (ρ : GlobalTheory.Triple.Reading D.ntw i b) (j : Fin D.R.m), ∃ n, GlobalTheory.GalChar.IsGal art ρ.κ ρ.ι (GlobalTheory.Triple.blockChar cf (D.ntw.l i) j) n (D.ntw.chi1 i (j.1 + 1) b) := by
  intro D cf chiD T hEta hMu hDel hC art ha i b ρ j
  obtain ⟨χ', n, h'⟩ := GlobalTheory.Triple.exists_blockChar ha hC ρ j
  have hj1 : 1 ≤ j.1 + 1 := Nat.le_add_left 1 j.1
  have hj2 : j.1 + 1 ≤ D.R.m := j.2
  obtain ⟨B1, hB1⟩ := T.chi1 i (j.1 + 1) b hj1 hj2
  have hχ : ∀ x, (chiD.firstHeckeCharacter i (j.1 + 1)).χ x = (cf.mu0 j * cf.delAt (D.ntw.l i) * cf.eta⁻¹).1 x := by
    intro x
    change (chiD.mu0 (j.1 + 1)).χ x * (chiD.del i).χ x * (chiD.etaT.χ x)⁻¹ =
      (cf.mu0 j).1 x * (cf.delAt (D.ntw.l i)).1 x * (cf.eta.1 x)⁻¹
    rw [hMu j x, hDel i x, hEta x]
  set χb := GlobalTheory.Triple.blockChar cf (D.ntw.l i) j with hχb
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ B1 := Filter.eventually_cofinite.2 (by simpa using B1.finite_toSet)
  have hc1 : Continuous (inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b)) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.isEmbedding_toQ (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg).continuous.comp
      (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) b))
  have e : inQ ρ.κ χ' = inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b) := by
    refine GlobalTheory.GalChar.eq_of_frob ha (h'.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg) hc1 ?_
    filter_upwards [hev, GlobalTheory.GalChar.unr_ae χb,
      GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero] with v hv hu hl A hA σ hσ
    refine GlobalTheory.ChiLocGal.frob_any (D.nd.plOm.2 v) hA (fun σ' hσ' => ?_) hσ
    obtain ⟨α, hα, x, hx, hσx⟩ := hB1 v hv
    have hval : ((χb.val v : ℂˣ) : ℂ) = (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x)⁻¹ :=
      GlobalTheory.ChiLocGal.val_block (GlobalTheory.ChiLocGal.val_of_at hχ hα) hx
    have e1 := h'.frob ha (Or.inl hl) hu (D.nd.plOm.2 v) hσ'
    rw [hval, inv_inv] at e1
    apply Units.ext
    apply ρ.ι.injective
    show ρ.ι (toQ ρ.κ (χ' σ' : (D.ntw.O0 i)ˣ)) = ρ.ι (toQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b σ' : (D.ntw.O0 i)ˣ))
    rw [e1]
    show Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x = ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
      (D.ntw.chi1 i (j.1 + 1) b σ' : (D.ntw.O0 i)ˣ)))
    rw [hσx σ' hσ']
    exact (ρ.read x).symm
  have : χ' = D.ntw.chi1 i (j.1 + 1) b := MonoidHom.ext fun g => GlobalTheory.GalChar.inQ_inj ρ.κ (DFunLike.congr_fun e g)
  exact ⟨n, this ▸ h'⟩

end GlobalTheory.TwChiGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoefficient_extremal_eq_discreteSeries : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), Formalism.IndefR.FWT.IsExtVec (R.MW i (sg0 D A)) (fun ρ => ((v ρ : (R.MW i (sg0 D A)).sm ρ))) → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  first | exact @GlobalTheory.RawLift.FockCoef.coef_extremal | exact GlobalTheory.RawLift.FockCoef.coef_extremal | (intros; apply GlobalTheory.RawLift.FockCoef.coef_extremal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullDegreeLabelForcesTrivialWildInertia
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WildFull

open Polynomial

theorem main : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.TypeLeaf.WildOne D := by
  intro D T hL k v L hdeg s hsI hsW
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have h1 := hL k v L
  rw [h1, ← T.dim] at hdeg
  rw [T.inePol _ L s hsI, ← T.dim]
  exact GlobalTheory.WeilDeligne.WD.inePol_wild_of_natDegree_lab hdeg hsW

end GlobalTheory.WildFull
end

