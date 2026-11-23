module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0022
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreLast
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LiftOther
end GlobalTheory.LiftOther
namespace GlobalTheory.LiftOther
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ L : G0g D.nd → GAf D.host.E D.R.nV, IsTypeGroupBlockLift D D.R.nV L → ∀ F ∈ D.naut.typeV i PI, ∀ (h : GL (Fin D.R.r) (ZMod (D.host.g k))) (g : G0g D.nd), g ⟨k, v⟩ = h → (∀ kv, kv ≠ ⟨k, v⟩ → g kv = 1) → ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := by
  intro hL D P i PI k v s hs c hc hcs L hLift F hF h g hg1 hg2
  classical
  obtain ⟨x, hxT, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s (s.loc D.R.nV (L g))
  refine ⟨x, hxT, ?_, ?_⟩
  · rw [hxe]
    have := ((hLift g).2 ⟨k, v⟩ s hs)
    rw [hg1] at this
    exact isLiftN_map' s c hc hcs _ _ h _ this
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  let K : Subgroup (GAf D.host.E D.R.nV) := (P.M.loc i).χ.ker.map (P.M.loc i).J.subtype
  set y := x⁻¹ * L g with hy
  have hsv : s.v ∈ PendOf.gPl D := ⟨⟨k, v⟩, by rw [← hs]; exact s.w_under⟩
  have hfin := gPl_finite D
  let T := hfin.toFinset.erase s.v
  have hyT : TrivOutside (T : Set _) y := by
    intro w hw
    rw [map_inv_mul]
    by_cases hws : w = s.v
    · subst hws
      rw [_root_.GlobalTheory.SplitCompat.compAt_map_eq_of_loc_eq s (L g) x hxe.symm]
      exact map_inv_mul_self _ x
    · have hwg : w ∉ PendOf.gPl D := by
        intro hwg; apply hw; simp [T, hws, hwg]
      rw [(hLift g).1 w hwg]
      have hx1 := hxT w (by simpa using hws)
      have e := map_inv_mul_self w x
      rw [hx1, mul_one] at e
      rw [e, mul_one]
  have hyK : y ∈ K := by
    refine _root_.GlobalTheory.TrivOutsideGen.mem_of_trivOutside_of_local K T y hyT fun w hw => ?_
    have hwne : w ≠ s.v := (Finset.mem_erase.1 hw).1
    have hwg : w ∈ PendOf.gPl D := hfin.mem_toFinset.1 (Finset.mem_erase.1 hw).2
    obtain ⟨kv, hkv⟩ := hwg
    obtain ⟨s', hs'⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D kv
    have hs'v : s'.v = w := over_eq s' (by rw [hs']; exact hkv)
    have hkvne : kv ≠ ⟨k, v⟩ := by
      rintro rfl
      apply hwne
      rw [← hs'v]
      exact over_eq s' (by rw [hs', ← hs]; exact s.w_under)
    obtain ⟨p, hpT, hpe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s' (s'.loc D.R.nV y)
    have hloc : s'.loc D.R.nV y = s'.loc D.R.nV (L g) := by
      rw [hy, map_mul]
      have : s'.loc D.R.nV x⁻¹ = 1 := by
        rw [map_inv]
        rw [loc_eq_one_of_compAt' s' x (hxT _ (by rw [hs'v]; simpa using hwne)), inv_one]
      rw [this, one_mul]
    have hlift := (hLift g).2 kv s' hs'
    rw [hg2 kv hkvne, ← hloc, ← hpe] at hlift
    obtain ⟨ψ₀, ξ, hψ, -, hU⟩ := P.H.level.uni i j hj kv.1 kv.2 s' hs'
    obtain ⟨hpJ, hpχ⟩ := _root_.GlobalTheory.UniLevelLift.main (P.M.loc i).J (P.M.loc i).χ s' D.R.r (D.host.g kv.1) (D.host.g_prime kv.1).one_lt
      ψ₀ ξ hψ hU p hpT hlift
    refine ⟨p, ⟨⟨p, hpJ⟩, hpχ, rfl⟩, hs'v ▸ hpT, ?_⟩
    rw [← hs'v]
    exact _root_.GlobalTheory.SplitCompat.compAt_map_eq_of_loc_eq s' p y hpe
  obtain ⟨⟨y', hy'J⟩, hy'χ, hy'e⟩ := hyK
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hfix : NG.rt D.host.E D.R.nV y ((P.M.loc i).real F) = (P.M.loc i).real F := by
    have e := hTS.2 ⟨y', hy'J⟩
    have h1 : (((P.M.loc i).χ ⟨y', hy'J⟩ : ℂˣ) : ℂ) = 1 := by
      rw [show (P.M.loc i).χ ⟨y', hy'J⟩ = 1 from hy'χ]; rfl
    rw [h1, one_smul] at e
    have hy'y : y' = y := hy'e
    rw [← hy'y]; exact e
  have hLg : L g = x * y := by rw [hy, mul_inv_cancel_left]
  rw [hLg]
  funext z
  have e := congrFun hfix (z * x)
  simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at e ⊢
  rw [← mul_assoc, e]
end GlobalTheory.LiftOther
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreSide
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.EigOnto
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main_alt_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  intro hstdP D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB j w h1 h2 hw c hc
  classical
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨-, y, hy, hcy⟩ := hc
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  have hb := Sp.B.iV_basis j w b
  obtain ⟨a⟩ : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply hy
    have hy' : y ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (D.what₂.muTw w) j (b a)) := by
      rw [hjb.2]; exact Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hy'
    exact hy'
  haveI : Nontrivial (Sp.B.V j w) := ⟨⟨Sp.B.iV j w (b a), 0, hb.1.ne_zero a⟩⟩
  obtain ⟨I0, hI0⟩ := Ideal.exists_maximal (heckeAlg Sp.B j w)
  obtain ⟨i0, hi0, -⟩ := Sp.mx_all j w h1 h2 hw I0 hI0
  have hinjC : Function.Injective (Sp.iotaC j w) := by
    intro a1 a2 hab
    obtain ⟨a1', rfl⟩ := (Sp.phO j w i0 hi0).surjective a1
    obtain ⟨a2', rfl⟩ := (Sp.phO j w i0 hi0).surjective a2
    rw [← Sp.iotaC_coh, ← Sp.iotaC_coh] at hab
    congr 1
    exact IsFractionRing.injective _ _ ((Sp.iq i0).injective ((qCast _ _).injective hab))
  let φ : FractionRing (Sp.B.Oc j w) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = Sp.iotaC j w z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (Sp.phK j w i0 hi0).toRingHom =
      (qCast (L.X.nd.w_l i0) (A.pl.ι (L.X.nd.w i0))).toRingHom.comp (Sp.iq i0) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (L.X.nd.O i0))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Sp.phK_alg, hφalg]
    exact (Sp.iotaC_coh j w i0 hi0 z).symm
  have hφ : ∀ x, φ (Sp.B.ec j w x) = D.what₂.embLL x := by
    intro x
    rw [← Sp.phK_emb j w i0 hi0 x, ← Sp.iq_LL i0 x]
    exact congrArg (fun f : FractionRing (L.X.nd.O i0) →+* ℂ => f (L.X.nd.embK i0 x)) hφK
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  obtain ⟨ej, ew⟩ := (L.X.nd.locs_mem j w i0).1 hi0
  have hμ0 : L.X.nd.mu i0 = D.what₂.muTw w := by rw [L.X.nd.mu_w i0, ew]
  have hQk : Hk.cover.B.Qc j w = C.Q w :=
    (Hk.cover.Q_eq j w i0 hi0).symm.trans ((Sp.Q_eq j w i0 hi0).trans (Sp.Qc_eq j w))
  have lin : ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → (M (D.what₂.muTw w) j h1 h2).wt.W),
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k (z • f + f') =
          z • NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f + NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f' := by
    intro v k s ϖ hvk hc hu
    have H := GlobalTheory.LiftPoint.tN_lin (withLoc L) (mtL L M) Hk.hecke Hk.cover (j := j) (w := w) (i := i0) hi0 v k s ϖ
      (by rw [hQk]; exact hvk) hc hu
    exact GlobalTheory.FitHecke.mt_transport M (fun μ jj m => ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → m.wt.W),
        NG.tN m.J s ϖ k (z • f + f') = z • NG.tN m.J s ϖ k f + NG.tN m.J s ϖ k f') hμ0 ej
      (L.X.nd.j_range i0).1 (L.X.nd.j_range i0).2 h1 h2 H
  have hstd : HeckeStdTw Sp.B := heckeStdTw_of_std Sp.std
  have hLoc : LocPl D j w := Or.inl hw
  have hgen : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k := fun v k h => by rw [← Sp.Qc_eq j w]; exact h
  have key : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      ∃ κ : Sp.B.Oc j w, φ (algebraMap _ _ κ) = c v k := by
    intro v k hvk
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
    obtain ⟨tC, htC1, htC2⟩ := GlobalTheory.LiftPoint.tC_exists D M Sp.B hstd j w (D.what₂.muTw w) rfl h1 h2 hLoc φ hφ v k hvk
    have ht0 : tC y = c v k • y := by
      apply (M (D.what₂.muTw w) j h1 h2).real_inj
      rw [← htC2 s ϖ hc hu (lin v k s ϖ (hgen v k hvk) hc hu) y, hcy v k s ϖ (hgen v k hvk) hc hu, map_smul]
    exact htC1 (c v k) y hy ht0
  let κF : PlE D.host → ℕ → Sp.B.Oc j w := fun v k =>
    if hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k then Classical.choose (key v k hvk) else 0
  have hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), φ (algebraMap _ _ (κF v k)) = c v k := by
    intro v k hvk
    simp only [κF, dif_pos hvk]
    exact Classical.choose_spec (key v k hvk)
  obtain ⟨e, hene, he⟩ := GlobalTheory.PtLocalEig.eig_descends D M Sp.B j w (D.what₂.muTw w) h1 h2 rfl φ hφ
    (fun v k => algebraMap _ _ (κF v k)) y hy (by
      intro v k hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
      refine ⟨s, ϖ, hc, hu, lin v k s ϖ (hgen v k hvk) hc hu, ?_⟩
      rw [hcy v k s ϖ (hgen v k hvk) hc hu, hκF v k hvk])
  have hinjK : Function.Injective (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))) :=
    IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens Sp.B j w) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨κF v k, he v k hvk⟩)
  have hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      ψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k := by
    intro v k hvk
    apply hinjK
    have e1 := hψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have e2 := he v k hvk
    change Sp.B.hK j w v k e = _ at e1
    rw [e2] at e1
    exact (smul_left_injective _ hene e1).symm
  have hW : NCov.W (heckeAlg Sp.B j w) (NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3
  obtain ⟨i, hi, hmx⟩ := Sp.mx_all j w h1 h2 hw (NCov.cls ψ) (NCov.cls_isMaximal ψ)
  refine ⟨i, hi, (Sp.ptX j w i hi).symm ⟨ψ, hmx.symm, hW⟩, fun v k hvk => ?_⟩
  have hvk' : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by rw [Sp.Qc_eq j w]; exact hvk
  have e1 : ∀ z, iotaO L.X.nd L.Y.naut i z = Sp.iotaC j w (Sp.phO j w i hi z) := by
    intro z
    unfold iotaO
    rw [RingHom.comp_apply, RingHom.comp_apply, Au.iotaQ i, Au.iotaQC i]
    exact Sp.iotaC_coh j w i hi z
  rw [e1, Sp.ptX_hT j w i hi _ v k hvk', Equiv.apply_symm_apply]
  show Sp.iotaC j w (ψ ⟨Sp.B.hK j w v k, _⟩) = c v k
  rw [hψv v k hvk', ← hφalg, hκF v k hvk']
end GlobalTheory.EigOnto
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreTail
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.TypeVecEig
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  intro hL D P S hT i PI k v s hw hsw c hcont hci F _hF x hx hh
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    exact c.toRingHom.map_det _
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ := hT.mu i s.w hw j hj
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci (S i s.w hw).mu ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar (S i s.w hw).mu h =
      (((S i s.w hw).mu (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar (S i s.w hw).mu h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]
end GlobalTheory.TypeVecEig
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ConjGal
open Formalism.BasicNotions.Loc GlobalTheory.Pst
section Local
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces B)
end Local
end GlobalTheory.ConjGal
namespace GlobalTheory.ConjGal
open Formalism.BasicNotions.Loc
section W
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
end W
theorem main_alt_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → ∀ Pm : GL (Fin a) (Qbar (D.nd.l i)), (∀ g, ρ' g = Pm⁻¹ * ρ g * Pm) → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ' w ↔ D.naut.IsdRW i ρ w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → D.naut.wdOf i ρ' w = D.naut.wdOf i ρ w) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w) → D.naut.jumpsW i ρ' τ = D.naut.jumpsW i ρ τ)) := by
  intro hB hL D P i a ρ ρ' hρ Pm hc
  refine ⟨fun w hw => ?_, fun w h₁ => ?_, fun τ hτ => ?_⟩
  · rw [(P.wdOf i _ ρ' w).2.2.2.1, (P.wdOf i _ ρ w).2.2.2.1]
    exact dR_conj D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc hρ w hw
  · rw [(P.wdOf i _ ρ' w).1, (P.wdOf i _ ρ w).1]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d₁ := (P.wdOf i _ ρ w).2.2.2.1.1 (h₁.resolve_left (not_not.2 hw))
      exact wd_conj_above D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) hB ρ ρ' Pm hc hρ w hw d₁
    · exact wd_conj_away D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc w hw
  · obtain ⟨w₀, -, -⟩ := GlobalTheory.PlaceOfEmb.exists_place_of_emb D (D.nd.l i) τ
    rw [(P.wdOf i _ ρ' w₀).2.2.2.2 τ, (P.wdOf i _ ρ w₀).2.2.2.2 τ]
    exact jumps_conj D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc hρ τ fun w hw =>
      (P.wdOf i _ ρ w).2.2.2.1.1 (hτ w hw)
end GlobalTheory.ConjGal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerBis
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

theorem main_alt_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a b (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ' → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ' w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (D.naut.wdOf i ρ w) (D.naut.wdOf i ρ' w)) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = D.naut.jumpsW i ρ τ + D.naut.jumpsW i ρ' τ)) := by
  intro hB hL D P i a b ρ ρ' hρ hρ'
  refine ⟨fun w hw => ?_, fun w h₁ h₂ => ?_, fun τ hτ => ?_⟩
  · rw [(P.wdOf i _ _ w).2.2.2.1, (P.wdOf i _ ρ w).2.2.2.1, (P.wdOf i _ ρ' w).2.2.2.1]
    exact dR_sum D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' w hw
  · rw [(P.wdOf i _ _ w).1, (P.wdOf i _ ρ w).1, (P.wdOf i _ ρ' w).1]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d₁ := (P.wdOf i _ ρ w).2.2.2.1.1 (h₁.resolve_left (not_not.2 hw))
      have d₂ := (P.wdOf i _ ρ' w).2.2.2.1.1 (h₂.resolve_left (not_not.2 hw))
      exact wd_sum_above D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) hB ρ ρ' hρ hρ' w hw d₁ d₂
    · exact wd_sum_away D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' w hw
  · obtain ⟨w₀, -, -⟩ := exists_place D (D.nd.l i) τ
    rw [(P.wdOf i _ _ w₀).2.2.2.2 τ, (P.wdOf i _ ρ w₀).2.2.2.2 τ, (P.wdOf i _ ρ' w₀).2.2.2.2 τ]
    exact jumps_sum D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' τ fun w hw =>
      ⟨(P.wdOf i _ ρ w).2.2.2.1.1 (hτ w hw).1, (P.wdOf i _ ρ' w).2.2.2.1.1 (hτ w hw).2⟩
end GlobalTheory.SumRepAdd
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIntMember
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty
theorem latInt_member_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → ∀ big L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → (∀ i, (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i)) ∧ ∀ j h1 h2 w, (withLoc L).what₂.muAt w ≠ (withLoc L).what₂.mu0 → LatInt (withLoc L) (mtL L M) (C.Q w) j h1 h2 w := by
  intro D cf jE A M C tup hM big L hB
  obtain ⟨Sp, -, -⟩ := hB
  refine ⟨fun i => ?_, fun j h1 h2 w hw => ?_⟩
  · have h : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i h).trans (Sp.Qc_eq _ _)
  · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h2' : j < D.R.m := h2
    exact ⟨(hM.full w ⟨j, h2'⟩ hw).1, fun v k s ϖ hg hc hu => hM.int w ⟨j, h2'⟩ v k s ϖ hw hg hc hu⟩
end GlobalTheory.CoefDuty
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtSplitOutStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_j_iff_umax_and_chi_eq_one_of_split_out : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hMI : MtInput D M tp.tup C.Q) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → ∀ κ : GAf D.host.E D.R.nV, TrivOutside {s.v} κ → (κ ∈ (mlX M X i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ h : κ ∈ (mlX M X i).J, (mlX M X i).χ ⟨κ, h⟩ = 1 := by
  first | exact @_root_.GlobalTheory.LocLevel.level_at_splitOut_alt | exact _root_.GlobalTheory.LocLevel.level_at_splitOut_alt | (intros; apply _root_.GlobalTheory.LocLevel.level_at_splitOut_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonemptyTwOpenStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_multiplicity_character_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C), Nonempty (TwOpen (withLoc L) (chL L C) (cfL L cf) (tpL L tp) (mtL L M) low) := by
  first | exact @_root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt | exact _root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt <;> assumption)
end
end

