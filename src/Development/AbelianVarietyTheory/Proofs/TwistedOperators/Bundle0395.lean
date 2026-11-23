module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0388
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocLineOfMatches
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HkLiftIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

section Map

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] (h : Sp T ⟶ Z.Hk)

def hkLift {x : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) : Gx x ⟶ Z.o₁.t.G.left :=
  Z.m₁.cart.1.lift (snd (Over.mk x) Xo.univ.t.G).left ((fst (Over.mk x) Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx])

def hkLift₂ {x' : Sp T ⟶ Xo.X} (hx' : x' = h ≫ Z.π₂) : Gx x' ⟶ Z.o₂.t.G.left :=
  Z.m₂.cart.1.lift (snd (Over.mk x') Xo.univ.t.G).left ((fst (Over.mk x') Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx'])

variable {h} {x x' : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)

@[reassoc] theorem hkLift_φ : hkLift Z h hx ≫ Z.m₁.cm.F = (snd (Over.mk x) Xo.univ.t.G).left :=
  Z.m₁.cart.1.lift_fst _ _ _

@[reassoc] theorem hkLift_hom : hkLift Z h hx ≫ Z.o₁.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ h :=
  Z.m₁.cart.1.lift_snd _ _ _

def hkMap : Gx x ⟶ Gx x' :=
  pullback.lift (f := (Over.mk x').hom) (g := Xo.univ.t.G.hom) (fst (Over.mk x) Xo.univ.t.G).left
    (hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F) (by
      simp only [Category.assoc]
      rw [Z.m₂.cart.1.w, Over.w_assoc Z.ψ, hkLift_hom_assoc, ← hx']; rfl)

@[reassoc] theorem hkMap_fst :
    hkMap Z hx hx' ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left :=
  pullback.lift_fst _ _ _

@[reassoc] theorem hkMap_snd :
    hkMap Z hx hx' ≫ (snd (Over.mk x') Xo.univ.t.G).left = hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F :=
  pullback.lift_snd _ _ _

end Map

section Square

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

theorem hkLift_isPullback (hx : x = h ≫ Z.π₁) :
    IsPullback (hkLift Z h hx) (fst (Over.mk x) Xo.univ.t.G).left Z.o₁.t.G.hom h := by
  refine IsPullback.of_right (h₁₂ := Z.m₁.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₁) ?_ (hkLift_hom Z hx)
    Z.m₁.cart.1
  rw [hkLift_φ, ← hx]
  exact (IsPullback.of_hasPullback (Over.mk x).hom Xo.univ.t.G.hom).flip

theorem hkLift₂_isPullback (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift₂ Z h hx') (fst (Over.mk x') Xo.univ.t.G).left Z.o₂.t.G.hom h := by
  have hφ : hkLift₂ Z h hx' ≫ Z.m₂.cm.F = (snd (Over.mk x') Xo.univ.t.G).left :=
    Z.m₂.cart.1.lift_fst _ _ _
  have hhom : hkLift₂ Z h hx' ≫ Z.o₂.t.G.hom = (fst (Over.mk x') Xo.univ.t.G).left ≫ h :=
    Z.m₂.cart.1.lift_snd _ _ _
  refine IsPullback.of_right (h₁₂ := Z.m₂.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₂) ?_ hhom
    Z.m₂.cart.1
  rw [hφ, ← hx']
  exact (IsPullback.of_hasPullback (Over.mk x').hom Xo.univ.t.G.hom).flip

theorem hkMap_isPullback (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift Z h hx) (hkMap Z hx hx') Z.ψ.left (hkLift₂ Z h hx') := by
  have hφ : hkLift₂ Z h hx' ≫ Z.m₂.cm.F = (snd (Over.mk x') Xo.univ.t.G).left :=
    Z.m₂.cart.1.lift_fst _ _ _
  have hhom : hkLift₂ Z h hx' ≫ Z.o₂.t.G.hom = (fst (Over.mk x') Xo.univ.t.G).left ≫ h :=
    Z.m₂.cart.1.lift_snd _ _ _
  have heq : hkMap Z hx hx' ≫ hkLift₂ Z h hx' = hkLift Z h hx ≫ Z.ψ.left :=
    Z.m₂.cart.1.hom_ext (by rw [Category.assoc, hφ, hkMap_snd, Category.assoc])
      (by rw [Category.assoc, hhom, hkMap_fst_assoc, Category.assoc, Over.w Z.ψ, hkLift_hom])
  refine IsPullback.of_bot ?_ heq.symm (hkLift₂_isPullback Z hx')
  rw [hkMap_fst, Over.w Z.ψ]
  exact hkLift_isPullback Z hx

theorem hkMap_etale (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Etale (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Etale) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.1

theorem hkMap_surjective (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Surjective (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Surjective) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.2.1

end Square

section Fibre

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem isCan_hkLift {Ω : Type} [CommRing Ω] {χ : T →+* Ω} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x}
    (hx : x = h ≫ Z.π₁) (hp : IsCan χ pm) (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) :
    pm ≫ hkLift Z h hx = hkLift Z (spMap χ ≫ h) h₁ :=
  Z.m₁.cart.1.hom_ext (by rw [Category.assoc, hkLift_φ, hkLift_φ, hp.2.1])
    (by rw [Category.assoc, hkLift_hom, hkLift_hom, reassoc_of% hp.2.2])

theorem isFib_hkMap {Ω : Type} [CommRing Ω] (χ : T →+* Ω) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)
    {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} (hΨ : IsFib χ (hkMap Z hx hx') Ψ₁) :
    ∃ (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) (h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂), Ψ₁ = hkMap Z h₁ h₂ := by
  obtain ⟨pm, pm', hp, hp', e, f⟩ := hΨ
  have h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁ := by rw [hp.1, hx, Category.assoc]
  have h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂ := by rw [hp'.1, hx', Category.assoc]
  refine ⟨h₁, h₂, GlobalTheory.HeckeFrCompare.gx_ext (f.trans (hkMap_fst Z h₁ h₂).symm) ?_⟩
  rw [hkMap_snd Z h₁ h₂, ← isCan_hkLift_assoc Z hx hp h₁, ← hkMap_snd Z hx hx', ← reassoc_of% e, hp'.2.1]

end Fibre

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutUnitaryPointStabilizesLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentCut_unitaryPoint_stabilizes_lattices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₁ ⊆ S →
      (∀ w ∉ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u * e = 0 ∨ u * e = u) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  first | exact @GlobalTheory.IdemCut.idempotentCut_latticeStabilizer | exact GlobalTheory.IdemCut.idempotentCut_latticeStabilizer | (intros; apply GlobalTheory.IdemCut.idempotentCut_latticeStabilizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFock
section
noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembersRule

section Local

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin)
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

theorem nodup_of_isParam {p q : ℕ} {l₁ l₂ : List ℚ} (h1 : l₁.length = p) (h2 : l₂.length = q)
    (h : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ)) : l₁.Nodup ∧ l₂.Nodup := by
  subst h1 h2
  refine ⟨List.nodup_iff_injective_get.2 fun i j hij => ?_, List.nodup_iff_injective_get.2 fun i j hij => ?_⟩
  · have := @h.1 (.inl i) (.inl j) (by simpa [ofBlocks, List.getD_eq_getElem] using hij)
    simpa using this
  · have := @h.1 (.inr i) (.inr j) (by simpa [ofBlocks, List.getD_eq_getElem] using hij)
    simpa using this

theorem pairing_eq_zero : ∀ (X : ProvA) (p q r s : ℕ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s lam').HK →
    GlobalTheory.PairLift.NoLow X p q lam' → ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q →
    ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (τ : D.what₂.Tau) (ε : Fin V.rank → Bool)
    (e : Ix (p - i) (q - i) ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m' : ℤ) (aS : ℚ)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s lam').U.H) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ))
    (b : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] ℂ), SignCompat ε e → SignCompat (M'.ε τ) e' → (m' : ℚ) = 2 * aS →
    Matches (X.ds r s lam') M' τ (plainMat e') m' U' → GlobalTheory.Chain.IoLift.IsKAct M' τ a' →
    (∀ Y ∈ lieAt W τ, ∀ P y, b (locT ε (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y +
      b P (a' Y y) = 0) → b = 0 := by
  intro X p q r s lam' hadm hlow i hi hip hiq D V W S' M' τ ε e e' m' aS U' a' b he he' hm' h₂ ha hb
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ ε (M'.ε τ) e e' he he'
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm ((X.ds r s lam').ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm ((X.ds r s lam').ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = (X.ds r s lam').ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  let B' : Pol _ _ _ _ →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ :=
    { toFun := fun P => (b (κ.symm P)).comp j
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have hB' : ∀ P v, B' (κ P) v = b P (j v) := fun P v => by simp [B']
  have h0 : B' = 0 := _root_.GlobalTheory.NoLowPairing.no_pairing_of_noLow X p q r s lam' hadm hlow i hi hip hiq B' (fun Y hY P y => by
    obtain ⟨P, rfl⟩ := κ.surjective P
    have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
    have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
    have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j ((X.ds r s lam').HK.act Y y) -
        ((aS : ℂ) * Y.trace) • j y := by
      have h7 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
          j ((X.ds r s lam').HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
        refine Subtype.ext (U'.injective ?_)
        rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
      rw [h7, map_add (f := _), LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
        sub_eq_add_neg, ← neg_smul]
      congr 2
      ring
    have h := hb _ hY' P (j y)
    rw [h6, fr_toFrame, trace_toFrame, h4] at h
    rw [← hκ.2, hB', hB', ← h]
    simp [plainMat])
  refine LinearMap.ext fun P => LinearMap.ext fun z => ?_
  obtain ⟨v, rfl⟩ := hsurj z
  rw [← hB', h0]
  rfl

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.ChainFr GlobalTheory.Chain.IoLift GlobalTheory.Chain.IoLift.FockOrbit GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec maxCpt)
open GlobalTheory.LowerMembers (frame_fock_orbit signCard_signed ptF_zero)
open scoped TensorProduct InnerProductSpace


set_option maxHeartbeats 1000000 in
theorem lowFock : ∀ (D : D7) (X : ProvA), GlobalTheory.PairLift.Inputs D X → GlobalTheory.PairLift.LowFock D X := by
  classical
  intro D X hIn
  have hTB := hIn.bridge.2
  intro S S' aS aT hP i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hf P
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  by_cases f0 : f₀ = 0
  · subst f0
    funext g
    simp [Lift.liftInt, thetaKO, ptF_zero]

  have tgt : ∀ τ, ∃ a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ),
      kFin M' τ ≤ M'.sm τ ∧ IsKAct M' τ a' := fun τ => by
    obtain ⟨p, q, r, s, l₁, l₂, l₁', l₂', -, -, h3, h4, hR, -, e2⟩ := hP τ
    obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W S' M' τ r s l₁' l₂' (aS τ)
      ⟨hR.pos', h3, h4, hR.par', hIn.chosen _ _ _ hR.par', e2⟩
    obtain ⟨U', hU'⟩ := hU' e' he'
    obtain ⟨hsm, a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W _ M' τ _ _ _ _ _ _ _ hU'
    exact ⟨a', hsm, ha'⟩
  choose a' hsm ha' using tgt
  have h' : KSm M' := hsm
  have hMF : IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hF)
  have hM : ∀ F' : MultT θ M' ∅ 1, IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ))) :=
    fun F' => (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F'.2)
  let pt : PolF D W.rank V'.rank →ₗ[ℂ] (WO V' W → ℂ) :=
    pureTensorO ψ θ V' W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f₀
  have hp : ptF ψ θ A (Fr.ofModel M') f₀ = pt := rfl
  have hpt : ∀ φ, IsThetaFunO ψ V' W (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hf.1 φ
  have L := hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hint : ∀ F' : MultT θ M' ∅ 1, ∀ φ x g, IntegrableOn
      (fun h => thetaKO ω' g h (pt φ) * (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ)) x h) 𝓕 ν := fun F' φ x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (L.integ _ _ (hpt φ) ⟨(hM F').aut w, (hM F').cusp w⟩ g 1).const_mul r
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]
      rfl
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, mul_add]; exact hx.add hy
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω' (g, h)) pt (MultT θ M' ∅ 1) hint
  let G : PolF D W.rank V'.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V' → ℂ) :=
    B.compr₂ (LinearMap.applyₗ (⟨F, hF⟩ : MultT θ M' ∅ 1))
  have hG : ∀ φ x, G φ x = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) (F x) := fun φ x => hB φ x ⟨F, hF⟩
  have hcl : ∀ w : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ w)) ∧
      IsCuspFun W (F (PiTensorProduct.tprod ℂ w)) := fun w => ⟨hMF.aut w, hMF.cusp w⟩

  have hT : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω' (1, oneP θ W τ Y t) (pt φ) z)
      (pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ) z) 0 :=
    fun τ Y hY φ z => (hIn.lie V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ (aS τ) (aT τ) hθ hW
      (hexp τ).1 (hexp τ).2 hf).2 Y hY φ z
  have hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (w : M'.Vec) (u : M'.sm τ), (u : M'.H τ) = dRep (M'.rep τ) Y (w τ) →
      G (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ)
        (PiTensorProduct.tprod ℂ w) + G φ (PiTensorProduct.tprod ℂ (Function.update w τ u)) = 0 := by
    intro τ Y hY φ w u hu
    have e1 := GlobalTheory.MultGelf.rder_apply hMF τ w hY (w τ) u hu
    rw [Function.update_eq_self] at e1
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω' τ Y (pt φ) =
        pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ) :=
      funext fun z => (hT τ Y hY φ z).deriv
    funext g
    have := L.derT_add (hpt φ) (hcl w) τ hY g
    rw [e2, add_comm] at this
    rw [Pi.add_apply, hG, hG]
    exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) A g) e1).symm.trans this

  have hav := mem_span_of_average G h' fun τ φ w => by
    obtain ⟨n, φs, c, hc, hφ⟩ := frame_fock_orbit D V' W _ A M' θ ψ ω' f₀ τ (aS τ) (aT τ) hθ
      (hIn.cpt V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ _ _ hθ hW (hexp τ).1 (hexp τ).2 hf f0) φ
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (w τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, ?_⟩
    funext g
    simp only [hG, Finset.sum_apply]
    exact GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V' W _ M' θ ψ χS χT ω' ν 𝓕 hθ hW hν h𝓕 τ n c _ _ _ _
      hc.1 (hpt φ) hφ (hcl w).1.toIsAutFun (fun i x => apply_kMean hMF τ (hc.1 i) w _ rfl x) g
      (hint ⟨F, hF⟩ _ _ g) fun i => hint ⟨F, hF⟩ _ _ g

  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨p, q, r, s, l₁, l₂, l₁', l₂', h1, h2, h3, h4, hR, e1, e2⟩ := hP τ₀
  obtain ⟨p', q', hp', hq', hsig⟩ := hs τ₀
  obtain ⟨hn1, hn2⟩ := nodup_of_isParam h1 h2 hR.par
  have hcard := signCard_signed l₁ l₂ (aT τ₀) hn1 hn2
  rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.1, h1] at hp'
  rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.2, h2] at hq'
  obtain rfl : p' = p - i := by omega
  obtain rfl : q' = q - i := by omega
  obtain ⟨e, he⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').2 A τ₀ _ _ hsig
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W S' M' τ₀ r s l₁' l₂' (aS τ₀)
    ⟨hR.pos', h3, h4, hR.par', hIn.chosen _ _ _ hR.par', e2⟩
  obtain ⟨U', hU'⟩ := hU' e' he'
  have hadm : Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s (ofBlocks l₁' l₂')).HK :=
    (((hIn.hc.admQ5_of_harishChandraModules X _ _ hR.pos').1 (X.ds r s (ofBlocks l₁' l₂')).U
      ⟨(X.ds _ _ _).nontriv, (X.ds _ _ _).irred⟩).2.2 _ (X.ds _ _ _).ι
      ⟨(X.ds _ _ _).ι_inj, (X.ds _ _ _).ι_range, (X.ds _ _ _).der⟩).1
  have kvan : ∀ φ (y : KT M'), G φ (inclK h' y) = 0 := by
    have hz := span_multi (G.compl₂ (inclK h')) fun p y => by
      funext g
      let b := slice (multi ((G.compl₂ (inclK h')).compr₂ (LinearMap.proj g))) τ₀ p y
      have hb0 := pairing_eq_zero X _ _ r s (ofBlocks l₁' l₂') hadm hR.low i hi (by omega) (by omega) D V' W _ M' τ₀
        (A.ε τ₀) e e' m' (aS τ₀) U' (a' τ₀) b he he' hm' hU' (ha' τ₀) (fun Y hY Q z => by
          simp only [b, slice_apply, multi_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
            LinearMap.proj_apply]
          have eq1 : glue (Function.update p τ₀ (locT (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) Q +
              ((aS τ₀ : ℂ) * Y.trace) • Q)) =
              fockT τ₀ (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) (glue (Function.update p τ₀ Q)) +
                ((aS τ₀ : ℂ) * Y.trace) • glue (Function.update p τ₀ Q) := by
            rw [((_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D V'.rank W.rank).2 τ₀ _ _ _).2, Function.update_idem, Function.update_self]
            simp only [← glueM_apply, MultilinearMap.map_update_add, MultilinearMap.map_update_smul,
              RingHom.id_apply]
          have eq2 : Function.update y τ₀ (a' τ₀ Y z) = Function.update (Function.update y τ₀ z) τ₀
              (a' τ₀ Y (Function.update y τ₀ z τ₀)) := by
            rw [Function.update_idem, Function.update_self]
          rw [eq1, eq2, inclK_tprod h' (Function.update y τ₀ z), inclK_update h' (Function.update y τ₀ z) τ₀]
          refine congrFun (hBt τ₀ Y hY _ _ _ ?_) g
          exact ((ha' τ₀).der Y hY _).deriv.symm)
      have := LinearMap.congr_fun₂ hb0 (p τ₀) (y τ₀)
      simpa [b, slice_apply, multi_apply, Function.update_eq_self] using this
    exact fun φ y => LinearMap.congr_fun₂ hz φ y
  have h0 : G P v ∈ (⊥ : Submodule ℂ (GA D V' → ℂ)) :=
    Submodule.span_le.2 (by rintro _ ⟨φ, y, rfl⟩; simp [kvan φ y]) (hav P v)
  rw [Submodule.mem_bot, hG] at h0
  rw [hp]
  exact h0

end Global

end GlobalTheory.LowerMembersRule

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfDiscreteSerie
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

theorem itLine_of_discreteSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  intro hCover hModules D

  rcases _root_.GlobalTheory.RealPlaceTheta.exists_record_theta hCover hModules with ⟨X, hParam, -, -, -, -, hAR3, -⟩

  have hBridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := _root_.GlobalTheory.CoverModel.modelsAreCoverSeries_all hCover hModules D
  have hVac : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := _root_.GlobalTheory.VacuumCharacter.vacChar D
  exact itLine D X hParam hAR3 hVac hBridge hModules

end GlobalTheory.Chain.RealLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverseStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt : (∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) →
      (∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) →
      ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse | exact GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse | (intros; apply GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_at_place_eq_latticeIntertwiner_mul_det_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : Gv T v) (f : GlobalTheory.FinWeilO.thetaSub ψ S T), (IsSplit (E := D.host.E) v → om (1, embV T v a) f = ((locChar χS w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h a)) : ℂˣ) : ℂ) • (Om (1, embV T v a) f : WO S T → ℂ)) ∧ (IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → om (1, embV T v a) f = (Om (1, embV T v a) f : WO S T → ℂ)) := by
  first | exact @GlobalTheory.WeilAtPlace.weilDatum_at_place | exact GlobalTheory.WeilAtPlace.weilDatum_at_place | (intros; apply GlobalTheory.WeilAtPlace.weilDatum_at_place <;> assumption)
end

