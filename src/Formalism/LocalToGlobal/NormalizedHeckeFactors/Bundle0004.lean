module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0003
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
public import ReciprocityTheory.GaloisValuations.GlobalA
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
section
noncomputable section

open Formalism.BasicNotions Module Module.End

namespace Formalism.L2

theorem finrank_eq_of_semilinear {K₁ K₂ M₁ M₂ : Type} [Field K₁] [Field K₂] [AddCommGroup M₁] [Module K₁ M₁]
    [AddCommGroup M₂] [Module K₂ M₂] (σ : K₁ ≃+* K₂) (f : M₁ →ₛₗ[σ.toRingHom] M₂) (P : Submodule K₂ M₂)
    (hinj : Function.Injective f) (hrange : ∀ y, y ∈ P ↔ ∃ z, f z = y) :
    finrank K₁ M₁ = finrank K₂ P := by
  let g : M₁ →+ P :=
    { toFun := fun z => ⟨f z, (hrange _).2 ⟨z, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun a b => Subtype.ext (map_add f a b) }
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨z, hz⟩ := (hrange y).1 y.2
    exact ⟨z, Subtype.ext hz⟩
  have h := rank_eq_of_equiv_equiv σ (AddEquiv.ofBijective g hg) σ.bijective fun r m =>
    Subtype.ext (f.map_smulₛₗ r m)
  unfold finrank
  rw [h]

variable {D : D7} {M : MtFam D}

theorem finite_chooseBasisIndex (j : ℕ) (w : D.what₂.places.Pl) :
    Finite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :=
  (D.what₂.jMt_basis (D.what₂.muTw w) j (Module.Free.chooseBasis D.what₂.LL _)).1.finite

theorem finrank_V (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    FiniteDimensional (FractionRing (B.Oc j w)) (B.V j w) ∧
      finrank (FractionRing (B.Oc j w)) (B.V j w) = finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := by
  have := finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hb := B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  haveI : Module.Finite D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis b
  refine ⟨Module.Finite.of_basis bV, ?_⟩
  rw [Module.finrank_eq_card_basis bV, Module.finrank_eq_card_basis b]

theorem finrank_Mt_eq (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl} {i : D.nd.Loc} (h : i ∈ D.nd.locs j w) :
    finrank (D.nd.O i) (D.nd.Mt i) =
      finrank (FractionRing (T.B.Oc j w)) (NCov.part (heckeAlg T.B j w) (T.mx j w i)) := by
  rw [← Module.finrank_baseChange (R := FractionRing (D.nd.O i)) (S := D.nd.O i) (M' := D.nd.Mt i)]
  exact finrank_eq_of_semilinear (T.phK j w i h) (T.Psi j w i h) _ (T.Psi_inj j w i h) (T.Psi_range j w i h)

theorem gens_hypsTw (B : NLocBase D M) (hstd : HeckeStdTw B) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (hw : LocPl D j w) :
    (∀ a ∈ heckeGens B j w, ∀ b ∈ heckeGens B j w, Commute a b) ∧
      (∀ a ∈ heckeGens B j w, ⨆ μ, a.maxGenEigenspace μ = ⊤) ∧
      (∀ a ∈ heckeGens B j w, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ →
        μ ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨v, k, hvk, rfl⟩ _ ⟨v', k', hvk', rfl⟩
    exact (hstd j w h1 h2 hw).1 v k v' k' hvk hvk'
  · rintro _ ⟨v, k, hvk, rfl⟩
    exact B.split j w v k hvk
  · rintro _ ⟨v, k, hvk, rfl⟩
    exact (hstd j w h1 h2 hw).2 v k hvk

theorem sum_finrank_eq_of (T : NormalizedLocalCompatibility D M) {j : ℕ} {w : D.what₂.places.Pl}
    (hg : (∀ a ∈ heckeGens T.B j w, ∀ b ∈ heckeGens T.B j w, Commute a b) ∧
      (∀ a ∈ heckeGens T.B j w, ⨆ μ, a.maxGenEigenspace μ = ⊤) ∧
      (∀ a ∈ heckeGens T.B j w, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ →
        μ ∈ (algebraMap (T.B.Oc j w) (FractionRing (T.B.Oc j w))).range))
    (hall : ∀ I : Ideal (heckeAlg T.B j w), I.IsMaximal → ∃ i ∈ D.nd.locs j w, T.mx j w i = I) :
    ∑ i ∈ D.nd.locs j w, finrank (D.nd.O i) (D.nd.Mt i) =
      finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := by
  classical
  obtain ⟨hfd, hrk⟩ := finrank_V T.B j w
  haveI := hfd
  rw [← hrk]
  obtain ⟨hS, hsplit, hint⟩ := hg
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  calc ∑ i ∈ D.nd.locs j w, finrank (D.nd.O i) (D.nd.Mt i)
      = ∑ i ∈ D.nd.locs j w,
          finrank (FractionRing (T.B.Oc j w)) (NCov.part (heckeAlg T.B j w) (T.mx j w i)) :=
        Finset.sum_congr rfl fun i hi => finrank_Mt_eq T hi
    _ = ∑ I ∈ (D.nd.locs j w).image (T.mx j w),
          finrank (FractionRing (T.B.Oc j w)) (NCov.part (heckeAlg T.B j w) I) :=
        (Finset.sum_image (f := fun I => finrank (FractionRing (T.B.Oc j w)) (NCov.part (heckeAlg T.B j w) I))
          fun a ha b hb hab => T.mx_inj j w ha hb hab).symm
    _ = finrank (FractionRing (T.B.Oc j w)) (T.B.V j w) :=
        NCov.sum_finrank_part hinj hS hsplit hint _ fun I hI => by
          obtain ⟨i, hi, rfl⟩ := hall I hI
          exact Finset.mem_image_of_mem _ hi

theorem locsCoverTw_of_tie (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) : Formalism.MainNotions.N.LocsCoverTw D :=
  fun j w h1 h2 hw => sum_finrank_eq_of T (gens_hypsTw T.B hstd h1 h2 (Or.inl hw)) (T.mx_all j w h1 h2 hw)

end Formalism.L2
end
end

-- bundled from Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.N NumberField Polynomial

namespace Formalism.L2

open Formalism.L2.NT Formalism.L2.Host

variable (D : D7)

def KQbar (jE : D.host.E →+* Qb) : Fld := D.host.K.map jE.toRatAlgHom

def MrayC (jE : D.host.E →+* Qb) : Fld := rayField (KQbar D jE) (D.host.QS * D.host.q * D.host.d)

def ParC : Type :=
  {Sig : List (Part D.naut.CG) //
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
    (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
    rankIso D.nd D.naut Sig = D.R.r ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r}

structure NormalizedTypesCompatibility (jE : D.host.E →+* Qb) where

  eM : D.ntypes.Mray ≃+* MrayC D jE
  eM_K : ∀ x : D.host.K, ((eM (algebraMap D.host.K D.ntypes.Mray x) : MrayC D jE) : Qb) = jE x

  tA : Fin 2 → ValuationSubring ℂ
  tκ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsLocalRing.ResidueField (tA k) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)
  teichC_def : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsTeich (tA k) (tκ k) (D.ntypes.teichC k)

  iota_loc : ∀ i : D.nd.Loc, haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime :=
      ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ (B : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar (D.nd.w i))),
      (∀ y : D.nd.O i, ∃ h : D.naut.iotaQC i (D.naut.iotaQ i (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) y)) ∈ B,
        fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
          (κ (IsLocalRing.residue B ⟨_, h⟩)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)) ∧
      ∀ k v x, D.ntypes.iota k v (D.nd.w i) x = redThrough B κ (D.ntypes.teichC k x)

  ζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ℕ → Formalism.CyclotomicNorms.Fbar (D.host.g k)
  ζ_gen : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsGenSys (ζ k)

  O : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (ζ k) (ζ_gen k))
  eSer_def : ∀ k f, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.ntypes.eSer k f = eSerO (O k) D.R.r f

  kv : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)

  tg_tame : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (kv k v) (D.ntypes.tg k v) (ζ k)

  O_equiv : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant (O k)

  O_tw : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    LabTwLawO (O k)

  eP : D.ntypes.Par ≃ ParC D
  locPar_def : ∀ σ w, D.ntypes.locPar σ w = isoLoc D.nd D.naut (eP σ).1 w

variable {D}
variable {jE : D.host.E →+* Qb}

namespace NT

end NT

theorem eSer_zero_of_tie (T : NormalizedTypesCompatibility D jE) (k : Fin 2) (f : (ZMod (D.host.g k))[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0)) : D.ntypes.eSer k f = 0 := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rw [T.eSer_def]
  exact eSerO_eq_zero _ _ f hf


variable (D)

variable {D}

theorem lpDim_foldr {w : PlE D.host} {a : ℕ} {β : Type} (π : D.naut.CG a) (L : List β) (f : β → ℝ)
    (z : D.naut.LP w) :
    D.naut.lpDim (L.foldr (fun k acc => D.naut.lpSum (D.naut.lpTw (D.naut.locG π w) (f k)) acc) z) =
      L.length * a + D.naut.lpDim z := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [D.naut.lpDim_sum, D.naut.lpDim_tw, D.naut.locG_dim, ih]
    ring

theorem lpDim_spehLoc (p : Part D.naut.CG) (w : PlE D.host) :
    D.naut.lpDim (spehLoc D.nd D.naut p w) = p.a * p.d := by
  unfold spehLoc
  have h := lpDim_foldr (D := D) p.π (do let a ← List.range p.d; pure (a : ℝ))
    (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) (D.naut.lpZero w)
  rw [h, D.naut.lpDim_zero, add_zero, mul_comm]
  congr 1
  simp

theorem lpDim_isoLoc (Sig : List (Part D.naut.CG)) (w : PlE D.host) :
    D.naut.lpDim (isoLoc D.nd D.naut Sig w) = rankIso D.nd D.naut Sig := by
  induction Sig with
  | nil => simp [isoLoc, rankIso, D.naut.lpDim_zero]
  | cons p Sig ih =>
    unfold isoLoc at ih ⊢
    unfold rankIso at ih ⊢
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [D.naut.lpDim_sum, lpDim_spehLoc, ih]

section Deg

variable {G : Type} [Group G] {g : ℕ} (f₀ : (ZMod g)[X])

end Deg

end Formalism.L2
end
end

