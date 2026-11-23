module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartitionOfUnitySupport
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinCharCut

open GlobalTheory.FinTrig

theorem exists_lev_subset {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (K : Set (κ → Af F)) (hK : K ∈ nhds (0 : κ → Af F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ u : κ → Af F, Lev d u → u ∈ K := by
  rw [nhds_pi, Filter.mem_pi] at hK
  obtain ⟨I, -, t, ht, hIt⟩ := hK
  have hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => hIt fun i _ => ?_⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

theorem fin_char_cut : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := by
  intro F _ _ κ _ ψ hψ C K hC hK h0 y
  classical
  obtain ⟨d, -, hdK⟩ := exists_lev_subset K (hK.mem_nhds h0)
  set yf : κ → FiniteAdeleRing (𝓞 F) F := fun i => (y i).2 with hyf
  set C' := C ∩ {z | Lev d (z - yf)}ᶜ with hC'def
  have hC' : IsCompact C' := hC.inter_right (isOpen_lev d yf).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC'.elim_nhds_subcover (fun a => {z | Lev d (z - a)})
    (fun a _ => (isOpen_lev d a).mem_nhds (by simp only [Set.mem_setOf_eq, sub_self]; exact lev_zero d))
  have hsep : ∀ a ∈ C', ∃ q ∈ (Q0 : Set (κ → AF F)), ψ (vecFin (a - yf) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, Lev d u → ψ (vecFin u ⬝ᵥ q) = 1 := fun a ha => exists_sep ψ hψ d (a - yf) ha.2
  choose! q hq0 hq1 hq2 using hsep
  set c : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun a => ψ (vecFin (a - yf) ⬝ᵥ q a) with hc
  set φ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(y ⬝ᵥ q a)) • chi ψ (q a) - c a • 1) with hφ
  have hφx : ∀ a ∈ C', ∀ x, φ a x = (1 - c a)⁻¹ * (ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) - c a) := by
    intro a ha x
    have e1 : ψ (-(y ⬝ᵥ q a)) * ψ (x ⬝ᵥ q a) = ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, neg_add_eq_sub, ← sub_dotProduct, dot_eq_vecFin (hq0 a ha)]
      rfl
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TP ψ := fun a ha =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem ψ (hq0 a (htC a ha))))
      (Submodule.smul_mem _ _ (one_mem_TP ψ)))
  obtain ⟨s, cc, hs, hP⟩ := exists_of_mem_TP ψ (prod_mem_TP ψ t φ hφmem)
  refine ⟨s, cc, fun b hb i => fst_eq_zero (hs b hb i), ?_, fun x hxC hxK => ?_⟩
  · rw [← hP y, Finset.prod_apply]
    refine Finset.prod_eq_one fun a ha => ?_
    rw [hφx a (htC a ha)]
    have e0 : (fun i => (y i).2) - yf = 0 := sub_self _
    have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
    rw [e0, vecFin_zero, zero_dotProduct, AddChar.map_zero_eq_one, inv_mul_cancel₀ hne]
  · rw [← hP x, Finset.prod_apply]
    have hL : ¬ Lev d ((fun i => (x i).2) - yf) := by
      intro hL
      refine hxK _ (hdK _ hL) ?_
      funext i
      simp [yf]
    have hxC' : (fun i => (x i).2) ∈ C' := ⟨hxC, hL⟩
    obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC')
    rw [Finset.prod_eq_zero hat]
    rw [hφx a (htC a hat)]
    have e : (fun i => (x i).2) - yf = ((fun i => (x i).2) - a) + (a - yf) := (sub_add_sub_cancel _ _ _).symm
    rw [e, vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul, sub_self,
      mul_zero]

end GlobalTheory.FinCharCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationFifth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.IoExtConj

open GlobalTheory.AdTh.IoExtPf
open scoped Classical

theorem deltaConj_ne {D : D7} (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : deltaConj (D := D) i σ ≠ 0 := by
  refine delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))
  show ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 ≤ _
  rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]
  have := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem exists_unit_of_isIoW {D : D7} {V W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (hs : LowSm M)
    (hl : ExtLine M) (c : CoefA V) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)) (Δ : PolF D W.rank V.rank) (hΔ : pt Δ ≠ 0)
    (hwt : ∀ (τ : D.what₂.Tau) (a : Fin W.rank → ℝ), ω (1, atTau θ W τ ((M.fr τ)⁻¹ *
      Matrix.diagonal (fun j => Complex.exp ((a j : ℂ) * Complex.I)) * M.fr τ)) (pt Δ) =
        Complex.exp (((∑ j, extWt M τ j * a j : ℝ) : ℂ) * Complex.I) • pt Δ)
    (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank) (h : IsIoW θ M c ω pt Δ io)
    (v' : ∀ ρ, lowT M ρ) (hv' : IsExtVec M (fun ρ => v' ρ)) :
    ∃ w : c.W, ‖w‖ = 1 ∧ io (PiTensorProduct.tprod ℂ v') w = Δ := by
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := h
  let f : LowT M →ₗ[ℂ] (WO V W → ℂ) := pt ∘ₗ io.flip w
  have hf : ∀ x, f x = pt (io x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact hΔ
  have hv : IsExtVec M (fun ρ => v ρ) := by
    refine fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩
    have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
    let u : lowT M τ := ⟨⟨_, hs τ hm⟩, hm⟩
    have h1 := hK τ _ ha v u rfl w
    rw [hio, hwt τ a, ← hio, ← hf, ← hf] at h1
    have h2 := inj_factor M hs hl τ f (fun k => ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)))
      (fun k hk v u hu => hK τ k hk v u hu w) v hv0
      (u - Complex.exp (((∑ j, extWt M τ j * a j : ℝ) : ℂ) * Complex.I) • v τ) (by
        rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1,
          RingHom.id_apply, sub_self])
    exact congrArg (fun y : lowT M τ => ((y : M.sm τ) : M.H τ)) (sub_eq_zero.1 h2)
  choose a ha1 ha using hl _ _ hv hv'
  have e : v' = fun ρ => a ρ • v ρ := funext fun ρ => Subtype.ext (ha ρ)
  have hn : ‖∏ ρ, a ρ‖ = 1 := by simp [norm_prod, ha1]
  have h0 : ∏ ρ, a ρ ≠ 0 := fun h => by simp [h] at hn
  refine ⟨(∏ ρ, a ρ)⁻¹ • w, by rw [norm_smul, norm_inv, hn, hw1]; simp, ?_⟩
  rw [e, MultilinearMap.map_smul_univ, map_smul, map_smul, LinearMap.smul_apply, smul_smul]
  simp only [RingHom.id_apply, inv_mul_cancel₀ h0, one_smul, hio]

end GlobalTheory.GalOne.IoExtConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

open GlobalTheory.VecInv Formalism.IndefR.Lev

theorem mu_detAt_eq_levChi {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) (t : T0)
    (hQ : L.Q t = ∅) {P : Finset (Pl D.host.E)} {e : AE D} (hee : e * e = e)
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) {κ : GA D (Vc D i)}
    (hκ : IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 κ) :
    ((L.mu t ((i : ℕ) + 1) (detAt e hee _ κ) : Circle) : ℂ) = levChi _ (L.βV i) (flagL (L.datVt i t)) κ := by
  have sV : finE (Vc D i) κ ∈ St (L.βV i) := parLev_St hκ.2.1
  have tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
    parLev_g hκ.2.1 h
  have one : ∀ PP ∈ L.Pg, upperLeftBlock (r_le_V i) (redFn (L.βV i) PP (finE (Vc D i) κ)) = 1 := fun PP h =>
    congrFun hκ.2.2 ⟨PP, h⟩
  obtain ⟨aV, haV, hrV⟩ := exists_det_int sV
  have mV := (mu_val hL t i hP he (detAt e hee _ κ) _ aV _ (isDetAt_detAt e hee _ κ) haV fun PP _ => hrV PP).1
  rw [levChi_flag_V i t tg, mV, hQ, Finset.prod_empty, Finset.prod_empty, one_mul]
  refine congrArg (fun z : ℂˣ => ((z * 1 : ℂˣ) : ℂ)) (Finset.prod_congr rfl fun PP h => ?_)
  rw [(_root_.GlobalTheory.VecInv.TwoBlockDet.det_blocks _ _ _ 0 (r_le_V i) _).1 (blockTri_blkOf_le _ _ (tg PP h)), one PP h, map_one, one_mul]

theorem smul_of_splitFac {D : D7} {X ι : Type} {u v : X → ℂ} {c : ι → ℂ} {μ η : (AE D)ˣ →* Circle} {x y : (AE D)ˣ} {z : ℂ}
    (h : (∏ i ∈ (∅ : Finset ι), c i) • u = ((splitFacO μ (μ * η⁻¹) x y : Circle) : ℂ) • v) (hy : y = 1) (hη : η x = 1)
    (hz : ((μ x : Circle) : ℂ) = z) : u = z⁻¹ • v := by
  rwa [Finset.prod_empty, one_smul, splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, hη, inv_one, mul_one, hy, map_one,
    mul_one, Circle.coe_inv, hz] at h

end GlobalTheory.GalOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationSixth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Rebase

open GlobalTheory.ConjLiftUnique

theorem rebase_gen {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}
    (hω : IsWeilDatumO ψ V W χV χW ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) 1) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f)
    {BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {p : D.what₂.Tau → ℕ} (hB : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B τ) (p τ))
    (hO : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (onb M τ) (p τ))
    (hinj : Function.Injective (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f)) {Δ : PolF D W.rank V.rank}
    {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank}
    (hio : IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f) Δ io) :
    ∃ io' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f) Δ io' ∧
      ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) =
        pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io' x w) := by
  classical
  have hk : ∀ τ, ∃ k ∈ Formalism.REAL.Kset (M.ε τ), B τ = onb M τ * k := fun τ => by
    obtain ⟨k, hk, -, k2, -⟩ := exists_kset (M.fr_unit τ) (M.fr_gram τ) (hO τ) (hB τ)
    refine ⟨k, hk, k2.trans ?_⟩
    unfold onb
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), Matrix.mul_one]
  choose k hk hBk using hk
  obtain ⟨s, hs⟩ : ∃ s : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ P,
      pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f P =
        pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (s P) := by
    obtain rfl : B = fun τ => onb M τ * k τ := funext hBk
    have h := GlobalTheory.FockSubst.pureTensorO_subst D ψ θ V W S M BV f k
      (fun τ b a => if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) hω.std hθ hV hf hk fun _ _ _ => rfl
    generalize MvPolynomial.aeval (R := ℂ) (S₁ := MvPolynomial (FVar D W.rank V.rank) ℂ) _ = s at h
    exact ⟨s.toLinearMap, h⟩
  have e0 : ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io.compr₂ s x w) =
      pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun x w => (hs _).symm
  refine ⟨io.compr₂ s, ⟨fun u hu x w => by rw [e0, e0, hio.1 u hu],
    fun τ k hk v u hu w => by rw [e0, e0, hio.2.1 τ k hk v u hu], ?_⟩, fun x w => (e0 x w).symm⟩
  have t1 := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M) B hf
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W :=
    io.compr₂ ((pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f).codRestrict (thetaSub ψ V W) t1)
  have f1 : ∀ x w, (F x w).1 = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun _ _ => rfl
  clear_value F
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₁, l, n3, hl, e1⟩ := exists_move hω hθ kV kW hV h1 h2 hF hf hv hB hO Δ n1 ((f1 _ w₀).trans (congrArg _ e))
  have l0 : l ≠ 0 := fun h => by simp [h] at hl
  refine ⟨v₁, l⁻¹ • w₀, n3, by rw [norm_smul, norm_inv, hl, n2, inv_one, one_mul], hinj ?_⟩
  rw [map_smul, map_smul, e0, ← f1, e1, smul_smul, inv_mul_cancel₀ l0, one_smul]

end GlobalTheory.GalOne.Rebase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParameters
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.BottomRallis.TrivParFun

variable {D : D7}

theorem isParamFun_one_trivPar : ∀ {D : D7} (A : HSp D) (LA : Lat A) (Sf : Finset (FinPl D)), IsSelfDualC A LA →
    (∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) →
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) (fun _ : GA D A => (1 : ℂ))
      (GlobalTheory.BottomRallis.trivPar A.rank) := by
  intro D V L Sf hLd _ v _ w h
  have hH := GlobalTheory.Doubling.isHermND_gram V
  have hL := hLd.1
  classical
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  haveI : Submodule.IsFullLattice D.host.E L := hfull V L hLd
  have hd := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hLd v
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    have := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h0 : (fun _ : GA D V => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w', hw'⟩
  · obtain ⟨e, he, -, -⟩ := LFun.SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg Submodule.IsFullLattice.span_eq_top h hs hd
    exact Or.inl ⟨hs, e, he, ((LFun.Model.hasSatGL_trivial w V.rank).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl)
      one_ne_zero).map (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0⟩
  · obtain rfl := (GlobalTheory.LFun.InertChart.under_eq_iff hw' w).1 h
    obtain ⟨-, ⟨τ, hτ, -⟩, -, -, hconj⟩ := (LFun.exists_isInertChart _ (isCMExt_host D) v).2 w h hw'
    obtain ⟨⟨ϖ, hϖ⟩, hch⟩ := hconj τ hτ
    obtain ⟨e, he, -, -⟩ := hch V.rank V.gram L hH hL.fg Submodule.IsFullLattice.span_eq_top hd
    refine Or.inr ⟨hw', τ, ϖ, e, _, hϖ, he, ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero v) V.rank).2 1
      (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0, ?_⟩
    rw [GlobalTheory.Core.Rk.Exh.Model.bcParam_rho]
    exact GlobalTheory.Core.Rk.Exh.Model.seg_eq_str (LFun.qV_ne_zero v) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _

end GlobalTheory.BottomRallis.TrivParFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspPhMemChiLat
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LevDesc

theorem cuspPh_mem_chiLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E) (hG : Even G.2) (hW : Even W.2) (hK : KeepsCusp U (G + W)) (hKW : KeepsCusp U W), (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U (G + W)), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U (G + W) → g ∈ latW U (G + W)) → (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U W), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U W → g ∈ latW U W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), u ∈ latW U W → ∀ f : cuspW Xo c U G, f ∈ latW U G → ∀ h : S, GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h ∈ GlobalTheory.LevDesc.chiLat S U (G + W) χ := by
  intro E _ _ _ H Dw l Xo c r U S hpq hA G W hG hW hK hKW hGW hWW χ u hu f hf h
  rw [GlobalTheory.LevDesc.mem_chiLat]
  refine ⟨?_, fun g => ?_⟩
  · have hint : ∀ g : S, IsIntegral ℤ ((((χ g)⁻¹ : (c.F)ˣ) : c.F)) := fun g => by
      refine IsIntegral.of_pow (Fintype.card_pos (α := S)) ?_
      rw [← Units.val_pow_eq_pow_val, ← map_inv, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
      exact isIntegral_one
    have hmem : ∀ g : S, pull Xo c g ((f : Rul Xo c) * pull Xo c h u) ∈ cuspW Xo c U (G + W) := fun g =>
      hK _ _ (GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW _ _ u.2))
    have hlat : ∀ g : S, (⟨_, hmem g⟩ : cuspW Xo c U (G + W)) ∈ latW U (G + W) := fun g => by
      have hu' : (⟨pull Xo c h u, hKW _ _ u.2⟩ : cuspW Xo c U W) ∈ latW U W := hWW h u _ rfl hu
      have hm : (f : Rul Xo c) * pull Xo c h u ∈ cuspW Xo c U (G + W) := GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW _ _ u.2)
      exact hGW g ⟨_, hm⟩ _ rfl (GlobalTheory.AllWt.mul_mem_supLat hf hu' hm)
    have he : GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h =
        ∑ g : S, (⟨_, hint g⟩ : 𝓞 c.F) • (⟨_, hmem g⟩ : cuspW Xo c U (G + W)) := by
      apply Subtype.ext
      rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply, GlobalTheory.LevDesc.levTr_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Submodule.coe_smul_of_tower, ← algebraMap_smul (c.F)]
      rfl
    rw [he]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hlat g)
  · rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply]
    exact (GlobalTheory.LevDesc.mem_levEigen.1 (GlobalTheory.LevDesc.levTr_mem_levEigen hpq hA χ _)) g

end GlobalTheory.LevDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (φ φ₁ φ₂ : (κ → Fv F v) → ℂ), φ ∈ GlobalTheory.WeilM.SB _ →
    (∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ₁ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ₂ r) →
    φ₁ = φ₂ := by
  first | exact @GlobalTheory.TensUniq.eq_of_tens_eq | exact GlobalTheory.TensUniq.eq_of_tens_eq | (intros; apply GlobalTheory.TensUniq.eq_of_tens_eq <;> assumption)
end

