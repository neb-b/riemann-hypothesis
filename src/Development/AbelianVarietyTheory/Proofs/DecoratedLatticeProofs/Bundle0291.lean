module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LatIndHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  rw [← map_one p.pr, p.sec_pr, mul_one]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b :=
  calc p.sec (a * b) = p.sec (p.pr (p.sec a * p.sec b)) := by rw [map_mul p.pr, p.pr_sec, p.pr_sec]
    _ = p.e * (p.sec a * p.sec b) := p.sec_pr _
    _ = p.sec a * p.sec b := by rw [← mul_assoc, e_mul_sec]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  obtain ⟨α, rfl, -, h0⟩ := hε
  have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
    rw [show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]
    unfold idAt
    rw [Submodule.mem_inf, RingHom.mem_ker, Submodule.mem_iInf]
    refine ⟨?_, fun w => RingHom.mem_ker.2 ?_⟩
    · change fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · change evalV D.host.F w.1 α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  rw [← heε]
  exact Ideal.mul_mem_right _ _ hmem

theorem mul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => w * y i) ∈ latV S L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun y i => w * y i) fun a b => funext fun i => mul_add w (a i) (b i)
  have main : latV S L P ≤ (latV S L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) :=
      AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (1 * x i))))
        fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add (f := _)]; rfl
    have hle : intAE D ≤ (latV S L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨γ, hγ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v),
        fun v hv => by rw [map_mul, hβ v hv, mul_zero], 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      change GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (1 * x i))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
        show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]
      congr 1
      ring
    have e : Ψ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w β _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact main hy

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem mulVec_sec (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) (x : n' → k) :
    t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) = fun i => p.sec ((β.b *ᵥ (rd α β t *ᵥ x)) i) := by
  have hM : (β.b * rd α β t * α.b') *ᵥ (α.b *ᵥ x) = β.b *ᵥ (rd α β t *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (β.b * rd α β t), α.b'b, Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [← hM]
  funext i
  conv_lhs => rw [← GlobalTheory.FinPl.HalfInd.wr_rd α β ht]
  simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.HalfInd.wr_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (sec_mul p _ _).symm

theorem mem_latO_iff_rd (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) (hU : p.UnitAA) {ΛS : Submodule 𝒪[k] (n' → k)} {ΛT : Submodule 𝒪[k] (n → k)}
    (hα : α.IsLat LS ΛS) (hβ : β.IsLat LT ΛT) {t : WO S T} (ht : IsHalf p.e t) :
    t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ x ∈ ΛS, rd α β t *ᵥ x ∈ ΛT := by
  have hmem := GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = p.v) t
  rw [hU.2 T LT] at hmem
  constructor
  · intro h x hx
    have h1 : t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) ∈ latV T LT (· = p.v) := (hmem.1 h).2 _ ((hα x).1 hx)
    rw [mulVec_sec α β ht] at h1
    exact (hβ _).2 h1
  · intro h
    refine hmem.2 ⟨fun i j => ?_, fun y hy => ?_⟩
    · rw [← ht i j]
      exact Ideal.mul_mem_right _ _ (e_mem_idAt p)
    · have hy' : t *ᵥ y = t *ᵥ (fun j => p.e * y j) := by
        funext i
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, mul_comm (t i j) p.e, ht i j]
      have hey : (fun j => p.e * y j) = fun j => p.sec ((α.b *ᵥ (α.b' *ᵥ fun j => p.pr (y j))) j) := by
        funext j
        rw [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec, p.sec_pr]
      have hint : finPart D p.e ∈ intAE D := by
        rw [← sec_one p]
        exact (p.int_iff 1).1 (one_mem _)
      have hx : α.b' *ᵥ (fun j => p.pr (y j)) ∈ ΛS := (hα _).2 (hey ▸ mul_mem_latV hint hy)
      show t *ᵥ y ∈ latV T LT (· = p.v)
      rw [hy', hey, mulVec_sec α β ht]
      exact (hβ _).1 (h _ hx)

end GlobalTheory.FinPl.LatIndHalf

theorem GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT hU ΛS ΛT hα hβ
  funext t
  unfold extFun halfInd
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    unfold latInd
    have key := GlobalTheory.FinPl.LatIndHalf.mem_latO_iff_rd α β hS hT hU hα hβ ht
    by_cases h : t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v)
    · rw [if_pos (key.1 h), if_pos ⟨h, ht⟩]
    · rw [if_neg fun h' => h (key.2 h'), if_neg fun h' => h h'.1]
  · rw [if_neg ht, if_neg fun h => ht h.2]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_iff_of_carries (y k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsFullLattice E N) (h1 : Formalism.L2.Herm.Carries (y * k) (Formalism.L2.Col.stdLat E n) N)
    (h2 : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (x : Fin n → E) :
    x ∈ N ↔ ∀ i, (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) i ∈ Formalism.L2.Herm.intAf F E := by
  have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) hN.span_eq_top
  have e0 : x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N := by
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  rw [e0, h1, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← h2]
  exact Formalism.L2.Col.mem_latS_std _

theorem finM_mul' {D : D7} (V : HSp D) {m : ℕ} (hn : V.rank = m) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [← Matrix.map_mul]
  congr 1

theorem finM_one' {D : D7} (V : HSp D) {m : ℕ} (hn : V.rank = m) : finM V hn 1 = 1 := by
  subst hn
  change (Formalism.L2.Theta.mt V 1).map (toEAf D) = 1
  have e : Formalism.L2.Theta.mt V 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one]
    rfl
  rw [e, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RepLattice

namespace GlobalTheory.RepLattice
open GlobalTheory.AdForm

end GlobalTheory.RepLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSqThetaLocalDatumAtTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
noncomputable section

namespace GlobalTheory.ThetaNormTwist

theorem normSq_thetaLocalDatum_at_twistPlace_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) → ∀ r : ℕ, r ≤ S.rank → r ≤ T.rank → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (onHalf φ S T (frCo φ βS) (frCo φ βT) e (phiQ v r mu)) x → nrm2 m X x = zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hcov hfS hfT PP v φ e he hP hA r hrS hrT ξ mu hmu x hx
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  obtain ⟨⟨Tm, hTm⟩, hxall⟩ := hx
  have hxT := hxall Tm hTm
  have hco := (GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he (frCo φ βS) (frCo φ βT)).1
  let ν : Measure (Fv D.host.F v) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨hv0, hvT, hiso⟩ := GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ m X hB hcov v e he.1
    T.rank S.rank (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.mapCo φ S T (frCo φ βS) (frCo φ βT)) hco Tm hTm ν hν
  obtain ⟨hip, hSB⟩ := GlobalTheory.T.split_weil_phi_inner_product D PP v φ hP S.rank T.rank r hrS hrT ξ mu hmu ν hν

  obtain ⟨⟨a0, ha0, -, hmax, himg⟩, -⟩ :=
    GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hB.2.2.1 hB.2.2.2.1 hfS hfT v φ e he
  have hval : Valued.v (rdQ φ a0) = 1 := by
    obtain ⟨⟨a1, ha1, h1⟩, hle⟩ := hA
    exact le_antisymm (hle a0 ha0) (h1 ▸ hmax a1 ha1)
  rw [hval] at himg
  have key := hiso _ hSB _ hSB
  rw [himg, hip] at key
  rw [← GlobalTheory.PlaceTensor.onHalf_eq_pull] at key
  rw [← hxT] at key
  have hne : ((GlobalTheory.SplitWeil.volM ν (Fin T.rank) (Fin S.rank) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal : ℂ) ≠ 0 := by
    rw [← himg]
    exact_mod_cast ENNReal.toReal_ne_zero.mpr ⟨hv0, hvT⟩
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO m X x x = ((nrm2 m X x : ℝ) : ℂ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO nrm2
    rw [← integral_complex_ofReal]
    congr 1
    funext w
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [e2] at key
  push_cast at key
  have key2 := mul_left_cancel₀ hne key
  apply Complex.ofReal_injective
  rw [key2]
  push_cast
  ring

end GlobalTheory.ThetaNormTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOOnb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJRealOnb

variable {D : D7}

theorem det_ne_zero_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (hG : IsCartanInv G 1)
    (hB : ∃ p, IsONBasis G 1 B p) : G.det ≠ 0 ∧ B.det ≠ 0 := by
  have hP : G.PosDef := by simpa using hG.2.2
  have hGd : G.det ≠ 0 := hP.det_pos.ne'
  refine ⟨hGd, fun h0 => ?_⟩
  obtain ⟨p, ε, hε, h1, -⟩ := hB
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h2
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h2.symm
  rcases hε a with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem det_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (τ : D.what₂.Tau) (hB : (B τ).det ≠ 0) : (inB θ V B g τ).det = (compAt θ τ (mt V g)).det := by
  unfold inB
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.det_one, one_mul]

theorem comp_eq_mul_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (hB : ∀ τ, (B τ).det ≠ 0) : (fun τ => compAt θ τ (mt V g) * B τ) = fun τ => B τ * inB θ V B g τ := by
  funext τ
  unfold inB
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit (hB τ)), Matrix.one_mul]

end GlobalTheory.KJRealOnb

namespace GlobalTheory.KJReal


open GlobalTheory.KJRealOnb in
theorem om_pureTensorO_onb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (x : DefSp S) (y : DefSp T) (μ : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → x.Is → y.Is → x.s = (fun _ => 1) → y.s = (fun _ => 1) → Even S.rank → Even T.rank → IsWeilDatumO ψ S T μ μ om → ∀ e : D.what₂.Tau → ℤ, (∀ τ, HasInfExp D μ τ (e τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ k ∈ GinfC S, ∀ k' ∈ GinfC T, ∀ P, om (k, k') (pureTensorO ψ θ S T x.s y.s x.B y.B f P) = (∏ τ, (inB θ S x.B k τ).det ^ (-e τ - T.rank / 2 : ℤ) * (inB θ T y.B k' τ).det ^ (e τ + S.rank / 2 : ℤ)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (mvZ (fun τ => (inB θ S x.B k τ)⁻¹) (inB θ T y.B k') P) := by
  intro D ψ θ S T x y μ om hθ hx hy hxs hys eS eT hom e he f hf hv k hk k' hk' P
  obtain ⟨mS, hmS⟩ := eS
  obtain ⟨mT, hmT⟩ := eT
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by have h := hx.cart τ; rw [hxs] at h; exact h
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => by have h := hy.cart τ; rw [hys] at h; exact h
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (x.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cS τ) (by have h := hx.onb τ; rw [hxs] at h; exact h)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (y.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cT τ) (by have h := hy.onb τ; rw [hys] at h; exact h)
  obtain ⟨xr, hxr, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) k hk
  obtain ⟨yr, hyr, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) k' hk'
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ μ μ om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT k hk k' hk' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) xr yr hxr hyr f hf hv
  have expT : ∀ τ, HasInfExp D (μ * (η ^ T.rank)⁻¹) τ ((e τ - mT : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    rw [hmT]; push_cast; ring
  have expS : ∀ τ, HasInfExp D (μ * (η ^ S.rank)⁻¹) τ ((e τ - mS : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    rw [hmS]; push_cast; ring
  have vx := hxv _ (fun τ => e τ - mT) expT
  have vy := hyv _ (fun τ => e τ - mS) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T μ μ om hom hθ (fun _ => 1) (fun _ => 1) x.B
    (fun τ => compAt θ τ (mt S k) * x.B τ) (fun _ => 1) (fun _ => 1) y.B
    (fun τ => compAt θ τ (mt T k') * y.B τ) k k' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  rw [hxs, hys, hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, comp_eq_mul_inB θ S x.B k (fun τ => (dS τ).2),
    comp_eq_mul_inB θ T y.B k' (fun τ => (dT τ).2),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ x.B (inB θ S x.B k) y.B (inB θ T y.B k') f hf P]
  congr 1
  · rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k)
    rw [Matrix.det_mul, Matrix.det_one] at inv
    have g0 := left_ne_zero_of_mul_eq_one inv
    have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k')
    rw [Matrix.det_mul, Matrix.det_one] at inv'
    have g0' := left_ne_zero_of_mul_eq_one inv'
    rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv, det_inB θ S x.B k τ (dS τ).2,
      det_inB θ T y.B k' τ (dT τ).2]
    have a1 : -e τ - (T.rank : ℤ) / 2 = -e τ - mT := by omega
    have a2 : e τ + (S.rank : ℤ) / 2 = e τ + mS := by omega
    rw [a1, a2]
    exact GlobalTheory.KJReal.exp_identity _ _ g0 g0' (e τ) mS mT S.rank T.rank (by rw [hmS]; push_cast; ring)
      (by rw [hmT]; push_cast; ring)

end GlobalTheory.KJReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem eq_of_parts {m n : ℕ} {u u' : Formalism.IndefR.Datum.Mx D m n} (h1 : u.map (infPart D) = u'.map (infPart D))
    (h2 : u.map (finPart D) = u'.map (finPart D)) : u = u' := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j

theorem finTens_mem_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finTens 1 M ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  refine ⟨fun h => ?_, finTens_mem_latO (one_mem_intAf _)⟩
  refine (_root_.GlobalTheory.LatVac.latRat_selfDual D S T ΛS ΛT hS hT (_root_.GlobalTheory.LatVacDual.dualFamily D S ΛS hS) _).2 fun ℓ hℓ => ?_
  have h1 := char_sympl_eq_one hψ hS hT h (finTens_mem_latO (one_mem_intAf _) hℓ)
  rw [symplO_finTens, one_mul, one_mul] at h1
  exact (char_rat hψ _).1 h1

theorem genMap_mulVec (S T : HSp D) (a : D.host.E) (s y : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    genMap S T a s t *ᵥ y = a • (∑ i, ∑ j, star (s i) * S.gram i j * y j) • t := by
  funext i
  simp only [genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_latRat_iff_perO {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔
      Matrix.toLin' M ∈ perO (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      refine Submodule.subset_span ⟨a, ha, Matrix.toLin' (genMap S T 1 s t), fun y hy => ?_, ?_⟩
      · obtain ⟨b, hb⟩ := (hS.2 y).1 hy s hs
        rw [Matrix.toLin'_apply, genMap_mulVec, one_smul, ← hb]
        exact ΛT.smul_mem b ht
      · refine LinearMap.ext fun y => ?_
        rw [LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, genMap_mulVec, genMap_mulVec, one_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro h
    obtain ⟨n, s, s', hs, hd⟩ := _root_.GlobalTheory.LatVacDual.dualFamily D S ΛS hS
    have key : ∀ z ∈ perO (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT,
        LinearMap.toMatrix' z ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨r, hr, x, hx, rfl⟩ := hw
        have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
          refine Matrix.ext fun i j => ?_
          have e1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
            funext c
            rw [Finset.sum_apply, Pi.single_apply, ← hd c j]
            exact Finset.sum_congr rfl fun k _ => mul_comm (s k c) _
          have e2 : LinearMap.toMatrix' (r • x) i j = r * x (Pi.single j 1) i := by
            rw [LinearMap.toMatrix'_apply]
            first
              | rfl
              | (congr 3; funext c; simp [Pi.single_apply])
          set_option synthInstance.maxHeartbeats 100000 in
            rw [e2, e1, map_sum, Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [LinearMap.map_smul]
          change r * ((∑ l, star (s' k l) * S.gram l j) * x (s k) i) = r * x (s k) i * ∑ l, star (s' k l) * S.gram l j
          ring
        refine e ▸ AddSubgroup.sum_mem _ fun k _ => ?_
        exact AddSubgroup.subset_closure ⟨r, hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul c x _ hx =>
        have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
          rw [← map_smul]; rfl
        rw [e]
        exact smul_mem_latRat c hx
    have := key _ h
    rwa [LinearMap.toMatrix'_toLin'] at this

theorem AA_eq (h : D.host.ccK = ⊤) : D.host.AA = D.host.AA0 := by
  rw [Host.AA, Host.ccE, h, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

theorem finOf_mem_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) N N', (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) ↔ toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP ΛS ΛT N N' h1 h2 hΛS hΛT γ v hv
  subst hS hT
  have e1 : N = ΛS := (SetLike.coe_injective h1).symm
  have e2 : N' = ΛT := (SetLike.coe_injective h2).symm
  have : v = finTens 1 γ :=
    eq_of_parts (hv.1.trans (Matrix.ext fun i j => (infPart_pair _ _).symm)) (hv.2.trans rfl)
  rw [← h1, ← h2, this, finTens_mem_iff hP.std hΛS hΛT, mem_latRat_iff_perO ΛT hΛS, AA_eq hP.cc, e1, e2]
  rfl

end GlobalTheory.AdForm.RatLat

end
end

