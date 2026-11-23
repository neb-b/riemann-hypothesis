module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0399
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneTmulSmulEqAddOfAlgebraMapEqAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsAdelicGlueVectorOfGlueBaseData

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsFullLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S hS n be be' hL hbe x hx x'
  first
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL hbe x hx x'
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL.toIsLattice hbe x hx x' 
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselHandedFunctionProductEqCoreLiftMulPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandProd

theorem handP_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  intro D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ' Φ₀ h1 h' h0
  have hW₀ : IsWeilDatumO ψ J.W₀ B.V₀ s.χV (χA * χz) s.om₀ := hχ ▸ s.weil₀
  have tt := GlobalTheory.TensorTargetRule.tensorTarget D ψ hb.std B.V₀ B.A B.L B.o J.W₀
  funext h₁
  have hpt : ∀ h₀, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (B.o.boxT J.W₀ Ξ₁ Φ')) (omz (h₀, 1) Φ₀) 0 =
      omb (h₀, h₁) Ξ₁ 0 * thPair vL.μ vL.𝓕 Φ' Φ₀ := by
    intro h₀
    rw [tt.om_box s.χV χA χz s.om₀ omb omz hW₀ hb hz h₀ h₁ 1 Ξ₁ Φ' h1 h',
      ← GlobalTheory.WeilPairing.thPair_om_eq D ψ J.W₀ B.L s.χV χz omz hz vL (h₀, 1) Φ' Φ₀ h' h0]
    have e : (fun v => B.o.boxT J.W₀ (omb (h₀, h₁) Ξ₁) (omz (h₀, 1) Φ') ((B.o.resT J.W₀).symm (0, v))) =
        fun v => omb (h₀, h₁) Ξ₁ 0 * omz (h₀, 1) Φ' v := by
      funext v
      simp only [OrthDec.boxT, AddEquiv.apply_symm_apply]
    simp only [contractT, e, thPair]
    rw [← integral_const_mul]
    congr 1; funext w
    have ew := congrFun e w
    rw [ew]; ring
  simp only [handP, hpt, Pi.smul_apply, smul_eq_mul, liftT_apply]
  rw [← integral_const_mul]
  congr 1; funext h₀; ring

end GlobalTheory.HandProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardHeckeCosetsEqCardSubmodulesSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeCosetCount

theorem card_eq_latCount : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
      Rc.card = Nat.card (GlobalTheory.HeckeCount.LatCount (T.Q.Dw ((i : ℕ) + 1)) p (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal T.Q.H P.asIdeal)
        (Ideal.absNorm P.asIdeal ^ k)) := by
  intro D hHP hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hL hG hF hM hTh hTie i σ hσ hV hFP P p k α Rc hs
  obtain ⟨hso, hp, hpP, -, hk, hα, hdc⟩ := hs
  rw [_root_.GlobalTheory.SplitCosetCount.card_cosets D R hL hF i P k α Rc hso hk hα hdc]
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hr := (hTie.laws.unf _ hj T.σ₀ T.good_σ₀).1
  have hrk : Module.finrank (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La = D.R.r := by
    rw [(T.Q.Dw ((i : ℕ) + 1)).rank]; omega
  set J := GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal T.Q.H P.asIdeal with hJdef
  have hJm : J.IsMaximal := by
    rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal]
    haveI : P.asIdeal.IsMaximal := P.isMaximal
    exact Ideal.map_isMaximal_of_equiv T.Q.H.bar
  have hpJ : ((p : ℕ) : 𝓞 D.host.E) ∈ J := by
    rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal]
    have := Ideal.mem_map_of_mem (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hpP
    rwa [map_natCast] at this
  have hN : Ideal.absNorm J = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv P.asIdeal J T.Q.H.bar (by rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal])).toEquiv.symm
  rw [← hN, _root_.GlobalTheory.LatCountGauss.card_latCount _ p J hp.pos hJm hpJ k, hrk]

end GlobalTheory.HeckeCosetCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiSRfl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

variable {D : D7}

def chiS (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : EAf D) : ℂ :=
  X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g
    (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h).symm c))

theorem chiS_rfl (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : EAf D) :
    chiS X h c = X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g
      (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h).symm c)) := rfl

end GlobalTheory.SeeConjChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DivisibilityTypeProductReadLevelPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

open scoped Pointwise

namespace GlobalTheory.SeeConjZMod

theorem dvd_of_mem_primes {A : Type} [CommRing A] [IsDedekindDomain A] {x b : A} (hx : x ≠ 0)
    (h : ∀ P : HeightOneSpectrum A, x ∈ P.asIdeal → x ∉ P.asIdeal ^ 2 ∧ b ∈ P.asIdeal) : x ∣ b := by
  have hI : Ideal.span {x} ≠ ⊥ := by simpa using hx
  have hsq : Squarefree (Ideal.span {x}) := by
    rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI]
    intro p hp hd
    have hpr : Prime p := hp.prime
    let P : HeightOneSpectrum A := ⟨p, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩
    have h2 : x ∈ p ^ 2 := by
      rw [sq, ← Ideal.dvd_span_singleton]; exact hd
    exact (h P (Ideal.pow_le_self two_ne_zero h2)).1 h2
  have hrad : (Ideal.span {x}).IsRadical := by
    intro y ⟨n, hn⟩
    rw [← Ideal.dvd_span_singleton] at hn ⊢
    rw [← Ideal.span_singleton_pow] at hn
    exact hsq.isRadical n _ hn
  rw [← Ideal.mem_span_singleton]
  apply hrad
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro J ⟨hJ, hp⟩
  exact (h ⟨J, hp, fun h0 => hI (le_bot_iff.1 (h0 ▸ hJ))⟩ (hJ (Ideal.mem_span_singleton_self x))).2

theorem conj_of_isConj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.L2.DIV.IsConjPl P P') :
    GlobalTheory.Mem.Chr.ConjPl D.host.conj.toRingEquiv P P' := by
  have hle : D.host.conj • P.asIdeal ≤ P'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    exact (hc _ y ((GlobalTheory.TypePlaces.star_eq_conj D _).trans (D.host.conj.apply_symm_apply (y : D.host.E))).symm).1 hy
  have hmax : (D.host.conj • P.asIdeal).IsMaximal := by
    have := P.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => P.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  exact (GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj P P').2 (hmax.eq_of_le P'.isPrime.ne_top hle)

theorem g_coprime (D : D7) :
    IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
  Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)

theorem g_not_mem_sq (D : D7) (P : Pl D.host.E) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  intro h
  rw [Nat.cast_mul] at h
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 :=
    fun k hk => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P hk).2.1
  have hno : ¬ (((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) := by
    rintro ⟨h0, h1⟩
    obtain ⟨a, b, hab⟩ := g_coprime D
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)
  have hP := P.isPrime
  rcases P.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero h) with h0 | h1
  · rcases Ideal.IsPrime.mul_mem_pow P.asIdeal (mul_comm (_ : 𝓞 D.host.E) _ ▸ h) with h' | h'
    · exact hno ⟨h0, h'⟩
    · exact key 0 h0 h'
  · rcases Ideal.IsPrime.mul_mem_pow P.asIdeal h with h' | h'
    · exact hno ⟨h', h1⟩
    · exact key 1 h1 h'

theorem exists_eq_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (hm : m ≠ 0) (hsq : ∀ P : Pl E, ((m : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (s : Formalism.L2.Herm.intAf F E)
    (h : ∀ P : Pl E, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal → resS F P s = 0) :
    ∃ t : Formalism.L2.Herm.intAf F E, s = (m : ℕ) * t := by
  have hm0 : ((m : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hm
  obtain ⟨q, hq⟩ := cmpS_surj (F := F) (Ideal.span {((m : ℕ) : 𝓞 E)}) (by simpa using hm0)
    (Ideal.Quotient.mk _ s)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hb : oToS F E b - s ∈ idS F (Ideal.span {((m : ℕ) : 𝓞 E)}) :=
    Ideal.Quotient.eq.1 hq
  rw [idS, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at hb
  obtain ⟨u, hu⟩ := hb
  have hd : ((m : ℕ) : 𝓞 E) ∣ b := by
    refine dvd_of_mem_primes hm0 fun P hP => ⟨hsq P, ?_⟩
    have e := congrArg (resS F P) hu
    rw [map_sub, h P hP, sub_zero, resS_oToS, map_mul, map_natCast] at e
    have e0 : ((m : ℕ) : kP P) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hP
    rw [e0, zero_mul] at e
    exact Ideal.Quotient.eq_zero_iff_mem.1 e
  obtain ⟨w, rfl⟩ := hd
  refine ⟨oToS F E w - u, ?_⟩
  rw [map_mul, map_natCast] at hu
  linear_combination -hu

theorem div_or_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (P : Pl D.host.E)
    (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ k, Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P) := by
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P) := by
    intro k hk
    have h := ((GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P
      hk).2.2.2 (Pb.pb k) (Pb.pb_over k) _ (conj_of_isConj (Formalism.L2.DIV.isConjPl_conjPl P))).2
    by_contra hn
    rw [not_or] at hn
    exact hn.1 (h.2 hn.2)
  rw [Nat.cast_mul] at hP
  exact (P.isPrime.mem_or_mem hP).elim (fun h => ⟨0, key 0 h⟩) (fun h => ⟨1, key 1 h⟩)

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ (c : EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc' : sigA (II D) c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ R.Pg, resS D.host.F PP ⟨c, hc⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) c, hc'⟩ = 0) → ZMod' (II D) (D.host.g 0 * D.host.g 1) c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs _
  have hPg : ∀ PP, PP ∈ R.Pg ↔ ∃ k, R.C.P.Div k PP := hIs.Pg
  refine ⟨fun PP hPP => ?_, fun c hc hc' h => ?_⟩
  · obtain ⟨k, hk⟩ := (hPg PP).1 hPP
    have ho : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := R.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ ho
    · exact Ideal.mul_mem_left _ _ ho
  · obtain ⟨t, ht⟩ := exists_eq_mul (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
      (g_not_mem_sq D) ⟨c, hc⟩ fun P hP => by
        obtain ⟨k, hk | hk⟩ := div_or_conj R.C.P P hP
        · exact (h P ((hPg P).2 ⟨k, hk⟩)).1
        · exact (resS_sigS_eq_zero_iff (II D).cm (Formalism.L2.DIV.isConjPl_conjPl P) ⟨c, hc⟩).1
            (h _ ((hPg _).2 ⟨k, hk⟩)).2
    refine ⟨t.1, t.2, ?_⟩
    have e := congrArg Subtype.val ht
    rw [Subring.coe_mul, Subring.coe_natCast] at e
    exact e

end GlobalTheory.SeeConjZMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceHermitianStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_unipotent_at_split_place : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  first | exact @GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | exact GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | (intros; apply GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAuxiliaryHyperbolicVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StandardGramVectors

open GlobalTheory.FrameComplement GlobalTheory.DetNorm

def stdGram (K : Type) [Field K] (ρ ε : ℕ) (t : K) :
    Matrix ((Fin ρ ⊕ Fin ρ) ⊕ Fin ε) ((Fin ρ ⊕ Fin ρ) ⊕ Fin ε) K :=
  fromBlocks (fromBlocks 0 1 1 0) 0 0 ((-t) • 1)

theorem hasSignature_submatrix {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {J : Matrix n n ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature J p q) (e : m ≃ n) :
    Formalism.UG.HasSignature (J.submatrix e e) p q := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ h
  refine hasSignature_of_frame (by rw [Fintype.card_congr e, c]) (Q.submatrix e id) ?_
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id, hQ]

theorem hasSignature_stdGram (ρ ε : ℕ) {T : ℕ} (hT : 0 < T) :
    Formalism.UG.HasSignature (stdGram ℂ ρ ε (T : ℂ)) (ρ + 0) (ρ + ε) := by
  refine hasSignature_fromBlocks ?_ ?_
  · refine hasSignature_of_frame (by simp) (fromBlocks 1 1 ((1 / 2 : ℂ) • 1) ((-1 / 2 : ℂ) • 1)) ?_
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply, Formalism.UG.Jpq, conjTranspose_smul, conjTranspose_one]
    ext (r | r) (s | s) <;> by_cases h : r = s <;> simp [h] <;> norm_num
  · have h1 : ((√(T : ℝ) : ℝ) : ℂ) * ((√(T : ℝ) : ℝ) : ℂ) = T := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg T)]; simp
    have h2 : ((√(T : ℝ) : ℝ) : ℂ) ≠ 0 := fun h => by
      rw [h, mul_zero] at h1
      exact hT.ne' (by exact_mod_cast h1.symm)
    refine hasSignature_of_frame (by simp) (fromCols 0 ((((√(T : ℝ) : ℝ) : ℂ))⁻¹ • 1)) ?_
    ext (r | r) (s | s)
    · exact r.elim0
    · exact r.elim0
    · exact s.elim0
    · rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]
      by_cases h : r = s
      · simp [h, Formalism.UG.Jpq]
        rw [← h1]; field_simp
      · simp [h, Formalism.UG.Jpq]

theorem det_stdGram (K : Type) [Field K] (ρ ε : ℕ) (t : K) :
    ∃ s : K, s * s = 1 ∧ (stdGram K ρ ε t).det = s * (-t) ^ ε := by
  refine ⟨(fromBlocks 0 1 1 0 : Matrix (Fin ρ ⊕ Fin ρ) (Fin ρ ⊕ Fin ρ) K).det, ?_, ?_⟩
  · rw [← Matrix.det_mul, Matrix.fromBlocks_multiply]
    simp
  · rw [stdGram, det_fromBlocks_zero₂₁, det_smul, det_one, mul_one, Fintype.card_fin]

theorem gram_comb {E : Type} [Field E] [NumberField E] [StarRing E] (Y : HSpace E) {c : ℕ} (b : Fin c → Y.V)
    (P : Matrix (Fin c) (Fin c) E) (k l : Fin c) :
    Y.hT (∑ i, P i k • b i) (∑ i, P i l • b i) = (Pᴴ * (Matrix.of fun i l => Y.hT (b i) (b l)) * P) k l := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul,
    LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem isN_pow {D : D7} {x : D.host.E} (h : IsN D x) (n : ℕ) : IsN D (x ^ n) := by
  induction n with
  | zero => simpa using isN_star (D := D) 1
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem exists_std (D : D7) (j : ℕ) (hj : j < D.R.m) :
    ∃ w : (Fin ((D.R.m - 1 - j) / 2) ⊕ Fin ((D.R.m - 1 - j) / 2)) ⊕ Fin ((D.R.m - 1 - j) % 2) → (D.sp.Y j).V,
      (∀ k x, (D.sp.Y j).hT (D.sp.iXY j x) (w k) = 0) ∧
      ∀ k l, (D.sp.Y j).hT (w k) (w l) = stdGram D.host.E _ _ (D.sp.T : D.host.E) k l := by
  obtain ⟨b, hb, hd, hs, a, ha, hdet⟩ := exists_complement_XY D j hj
  generalize D.R.m - 1 - j = c at *
  have hT : 0 < D.sp.T := D.sp.T_prime.pos
  obtain ⟨e⟩ : Nonempty (Fin c ≃ (Fin (c / 2) ⊕ Fin (c / 2)) ⊕ Fin (c % 2)) :=
    Fintype.card_eq.1 (by simp; omega)
  obtain ⟨s, hs1, hs2⟩ := det_stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)
  have hsN : IsN D s ∧ star s = s := by
    rcases mul_self_eq_one_iff.1 hs1 with h | h
    · rw [h]; exact ⟨by simpa using isN_star (D := D) 1, star_one _⟩
    · rw [h]; exact ⟨isN_neg_one, by simp⟩
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs1
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have hX := GlobalTheory.FrameComplement.gram_det_ne (D.sp.X j)
  obtain ⟨P, -, hP⟩ := GlobalTheory.HermAdelicNorm.congr_of_signature_of_adelic_norm D.host.F D.host.E D.sp.cm c
    (Matrix.of fun i l => (D.sp.Y j).hT (b i) (b l))
    ((stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)).submatrix e e)
    (Matrix.ext fun i l => (D.sp.Y j).herm.eq _ _)
    (by simp [stdGram, conjTranspose_submatrix, fromBlocks_conjTranspose]) hd
    (by rw [det_submatrix_equiv_self, hs2]; exact mul_ne_zero hs0 (pow_ne_zero _ (neg_ne_zero.2 hT0)))
    (fun τ => ⟨_, _, hs τ, by
      have h1 : ((stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)).submatrix e e).map τ =
          (stdGram ℂ (c / 2) (c % 2) (D.sp.T : ℂ)).submatrix e e := by
        ext r t
        simp only [map_apply, submatrix_apply]
        rcases e r with (r | r) | r <;> rcases e t with (t | t) | t <;>
          simp [stdGram, Matrix.one_apply, apply_ite τ]
      rw [h1]
      convert hasSignature_submatrix (hasSignature_stdGram (c / 2) (c % 2) hT) e using 1 <;> omega⟩)
    (by
      have h1 : IsN D (-(D.sp.T : D.host.E)) := by simpa using (isN_neg_one (D := D)).mul isNormFromTensorFiniteAdele_levelNormT
      have h2 := (((isN_det (D.sp.Y j)).mul ((isN_det (D.sp.X j)).inv (star_det _))).mul (isN_star a⁻¹)).mul
        ((hsN.1.mul (isN_pow h1 (c % 2))).inv (by simp [hsN.2]))
      have ha' : star a ≠ 0 := star_ne_zero.2 ha
      have h3 : ∀ x g u : D.host.E, x ≠ 0 → star a * a * x * g * x⁻¹ * (star a⁻¹ * a⁻¹) * u⁻¹ = g / u :=
        fun x g u hx => by rw [star_inv₀, div_eq_mul_inv]; field_simp
      rw [hdet, h3 _ _ _ hX] at h2
      rw [det_submatrix_equiv_self, hs2]
      exact h2)
  refine ⟨fun k => ∑ i, P i (e.symm k) • b i, fun k x => ?_, fun k l => ?_⟩
  · simp [hb]
  · rw [gram_comb, hP, submatrix_apply, e.apply_symm_apply, e.apply_symm_apply]

theorem exists_auxiliaryHyperbolicVectors : ∀ (D : D7) (j : ℕ), j < D.R.m → ∃ (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V), GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter D j E Ev z := by
  intro D j hj
  obtain ⟨w, h0, hw⟩ := exists_std D j hj
  refine ⟨fun i => if h : i < (D.R.m - 1 - j) / 2 then w (.inl (.inl ⟨i, h⟩)) else 0,
    fun i => if h : i < (D.R.m - 1 - j) / 2 then w (.inl (.inr ⟨i, h⟩)) else 0,
    if h : 0 < (D.R.m - 1 - j) % 2 then w (.inr ⟨0, h⟩) else 0, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.nAux HSpace.hD
  refine ⟨fun i hi l hl => ?_, fun i hi x => ?_, fun he => ?_⟩
  · simp only [dif_pos hi, dif_pos hl, hw]
    simp [stdGram, Matrix.one_apply, Fin.ext_iff, eq_comm]
  · simp only [dif_pos hi, h0, and_self]
  · have h : 0 < (D.R.m - 1 - j) % 2 := by
      obtain ⟨a, ha⟩ := D.R.m_even
      obtain ⟨b, hb⟩ := he
      omega
    refine ⟨?_, fun x => ?_, fun i hi => ?_⟩
    · simp only [dif_pos h, hw]; simp [stdGram]
    · simp only [dif_pos h, h0]
    · simp only [dif_pos h, dif_pos hi, hw]; simp [stdGram]

end GlobalTheory.StandardGramVectors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsAdelicGlueVectorOfGlueBaseDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAdelicGlueVector_of_glueBaseData : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (X : HSp D) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D), IsBasePair X u π L₀ f₀ → ∃ f, IsGlueVec X u L₀ f ∧ ∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f = f₀ w := by
  first | exact @GlobalTheory.AdIsom.BaseVec.exists_isGlueVec | exact GlobalTheory.AdIsom.BaseVec.exists_isGlueVec | (intros; apply GlobalTheory.AdIsom.BaseVec.exists_isGlueVec <;> assumption)
end

