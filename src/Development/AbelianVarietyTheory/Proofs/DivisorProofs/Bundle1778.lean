module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightShiftEqDetMul
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactor
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SumExpAt

theorem mem_locP {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem locIncl_of_equiv {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (e : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (N D : Submodule (𝓞 K) V) (N' D' : Submodule (𝓞 K) V')
    (hN : N.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = N')
    (hD : D.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = D')
    (h : ∀ x ∈ N', a • x ∈ Formalism.HermitianLatticesTheory.localization₂ p D') : ∀ v ∈ N, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p D := by
  intro v hv
  set f : V →ₗ[𝓞 K] V' := (e : V →ₗ[K] V').restrictScalars (𝓞 K) with hf
  have hx : f v ∈ N' := hN ▸ Submodule.mem_map_of_mem hv
  obtain ⟨s, hs, hsD⟩ := (mem_locP p D' _).1 (h _ hx)
  refine (mem_locP p D _).2 ⟨s, hs, ?_⟩
  rw [← hD] at hsD
  obtain ⟨y, hy, hye⟩ := hsD
  have hinj : Function.Injective f := e.injective
  have : y = s • a • v := hinj (by rw [hye, map_smul, map_smul])
  rw [← this]
  exact hy

theorem cutLat_locIncl {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.DIV.CSD K) {d : ℕ}
    (E : Matrix (Fin S.dim) (Fin d) K) (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (h : ∀ c, ∀ v ∈ S.Nab c, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p (S.Del c)) :
    ∀ z ∈ Formalism.DivisionValues.cutLat E S.nabLat, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ p (Formalism.DivisionValues.cutLat E S.delLat) := by
  classical
  intro z hz
  have hz' : ∀ c, S.I (E.mulVec z) c ∈ S.Nab c := fun c => hz c (Set.mem_univ c)
  have hlin : ∀ (r : 𝓞 K) (y : Fin d → K), S.I (E.mulVec (r • y)) = r • S.I (E.mulVec y) := fun r y => by
    have h1 := ((Matrix.mulVecLin E).restrictScalars (𝓞 K)).map_smul r y
    have h2 := (S.I.restrictScalars (𝓞 K)).map_smul r (E.mulVec y)
    simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at h1 h2
    rw [h1, h2]
  choose s hs hsD using fun c => (mem_locP p (S.Del c) _).1 (h c _ (hz' c))
  refine (mem_locP p _ _).2 ⟨∏ c, s c, prod_mem fun c _ => hs c, ?_⟩
  intro c _
  show S.I (E.mulVec ((∏ c, s c) • a • z)) c ∈ S.Del c
  rw [hlin, hlin, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ c), Pi.smul_apply, Pi.smul_apply, mul_comm,
    mul_smul]
  exact Submodule.smul_mem _ _ (hsD c)

end GlobalTheory.SumExpAt

namespace GlobalTheory.SumExpAt


open Formalism.CohomologicalDescent.LD in
theorem exZ_res_eq_natW (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) (f : ℕ → ℕ) (c : ℤ)
    (hc : ∀ a : Fin n, (f a : ℤ) = lam.w a + c) (l : ℕ) (hl : l.Prime) :
    Formalism.CohomologicalDescent.LA.exZ n n le_rfl (res n f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl lam.natW l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · congr 1
    funext a
    exact a.elim0
  · let m : Fin n := ⟨n - 1, by omega⟩
    have hds : lam.detShift = lam.w m := by
      simp only [Formalism.BasicNotions.DomWeight.detShift, dif_pos hn]
      rfl
    have hres : res n f = fun a => lam.natW a + f m := by
      funext a
      have h1 := hc a
      have h2 := hc m
      have h3 : lam.w m ≤ lam.w a := lam.anti (Fin.le_def.2 (by simp only [m]; omega))
      have h4 : ((lam.w a - lam.w m).toNat : ℤ) = lam.w a - lam.w m := Int.toNat_of_nonneg (by omega)
      change f a.val = (lam.w a - lam.detShift).toNat + f m
      rw [hds]
      omega
    have hanti : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      exact Int.toNat_le_toNat (by omega)
    rw [hres]
    exact Formalism.CohomologicalDescent.LA.exact_z_twist_by_det n lam.natW (f m) l hanti hl

theorem exZ_res_congr {N n : ℕ} (h : N = n) (f : ℕ → ℕ) (l : ℕ) :
    Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Formalism.CohomologicalDescent.LD.res N f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl (Formalism.CohomologicalDescent.LD.res n f) l := by
  subst h
  rfl

end GlobalTheory.SumExpAt

namespace GlobalTheory.ExpTie

open GlobalTheory.SumExpAt
open Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem lIncl_sumExp (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (hD : Dict L j P W) (t : p.P.T)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := p.charW.base.fam.tie
  obtain ⟨e, -, -, -, hNab, hDel⟩ := hT.coefL j t
  have hJ : W.JA P (Formalism.EigenvalueLevelCeiling.plc w) = ∑ τ, Formalism.CohomologicalDescent.LA.exZ (Vc D j).rank (Vc D j).rank le_rfl
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).natW (Formalism.EigenvalueLevelCeiling.plc w) := by
    unfold Wts.JA Wts.ex
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [exZ_res_congr hD.Nr]
    obtain ⟨c, hc⟩ := hD.lam τ
    exact exZ_res_eq_natW _ _ _ c hc _ (Formalism.EigenvalueLevelCeiling.plc_prime w)
  intro z hz
  rw [hJ]
  refine cutLat_locIncl (blk p j t).S _ w.asIdeal _ (fun c => ?_) z hz
  refine locIncl_of_equiv e w.asIdeal _ _ _ _ _ (hNab c) (hDel c) ?_
  have hLat (g : Bridge.Gf (Vc D j)) : Submodule.IsFullLattice D.host.E (Bridge.hLat (Vc D j) g) := by
    obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D j)
    obtain ⟨Λ, hΛ, h1, h2, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E (Vc D j).rank (GlobalTheory.Member.latC (Vc D j)) g.1 hfg hsp
    rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat (Vc D j) g).trans hΛ.symm)]
    exact { toIsLattice := Submodule.IsLattice.of_fg D.host.E h1, span_eq_top := h2 }
  exact GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr _ _ _ _ _ _ _ (hLat _) w

end Point

end GlobalTheory.ExpTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestriction
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

noncomputable section
namespace GlobalTheory.VacFactor

theorem pure_update_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (w : Pl (F := F)) (r : ℂ) (h : (κ → Fv F w) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) :
    pure f (Function.update φ w (r • h)) = pure (r • f) (Function.update φ w h) := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  rw [GlobalTheory.PureFactor.finprod_update φ w (r • h) hφ x, GlobalTheory.PureFactor.finprod_update φ w h hφ x]
  simp only [SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (c : ℂ) (g : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) : tens ev (c • g) r = c • tens ev g r := by
  funext x
  simp [tens, mul_assoc]

theorem std_of_off {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (hvac : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1)
    (U : Finset (Pl (F := F))) (h : ∀ v, v ∉ U → φ v = vac v) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hvac, U.finite_toSet.compl_mem_cofinite] with v h1 h2
  rw [h v h2, h1]

theorem factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')),
    (∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ → G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∃ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ i w, w ∉ S → φ' i w = G.M'.vac w) ∧
      Ψ = ∑ i, pure (f' i) (φ' i) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S f φ hφSB hφvac Ψ hΨ hyp
  have hvstd := hT.geo.hM'.std
  have hvSB : ∀ v, G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := fun v => (hT.geo.hM'.vac v).1
  have hyp' : ∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) → G.M'.co.rho B.ψ γ Ψ = c • Ψ := by
    intro w hw γ hγ c hc
    have hstd := std_of_off G.M'.vac φ hvstd S hφvac
    obtain ⟨r, hr1, hr2⟩ := GlobalTheory.PureFactor.exists_rest_factor w f φ hstd
    have e : pure f φ = tens (evFin F w) (G.M'.vac w) r := by
      rw [hr2, ← hφvac w hw, Function.update_eq_self]
    refine hyp w hw γ hγ c ?_
    have hR : Rest (evFin F w) (G.M'.vac w) r := ⟨hr1, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hφSB hstd⟩
    rw [e, hc r hR, tens_smul]
  obtain ⟨T, m, f₀, φ₀, hSB₀, hstd₀, hsum₀⟩ := GlobalTheory.T.adelic_schwartz_finite_pure_tensors F _ Ψ hΨ
  have hfin : {v | ¬ G.M'.vac v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1}.Finite :=
    Filter.eventually_cofinite.1 hvstd
  have key : ∀ U : Finset (Pl (F := F)), ∀ (f : Fin m → SInf F (Fin a' × Fin (a + a')))
      (φ : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ i v, v ∉ S → v ∉ U → φ i v = G.M'.vac v) →
      Ψ = ∑ i, pure (f i) (φ i) →
      ∃ (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ i v, φ' i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ i v, v ∉ S → φ' i v = G.M'.vac v) ∧
        Ψ = ∑ i, pure (f' i) (φ' i) := by
    intro U
    induction U using Finset.induction_on with
    | empty => exact fun f φ h1 h2 h3 => ⟨f, φ, h1, fun i v hv => h2 i v hv (Finset.notMem_empty v), h3⟩
    | insert w U hwU ih =>
      intro f φ h1 h2 h3
      by_cases hwS : w ∈ S
      · refine ih f φ h1 (fun i v hv hvU => h2 i v hv ?_) h3
        rw [Finset.mem_insert]
        rintro (rfl | h)
        exacts [hv hwS, hvU h]
      · have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
            φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := fun i =>
          std_of_off G.M'.vac (φ i) hvstd (S ∪ insert w U) fun v hv =>
            h2 i v (fun h => hv (Finset.mem_union_left _ h)) (fun h => hv (Finset.mem_union_right _ h))
        obtain ⟨g, hgSB, hgE, hgsum⟩ := GlobalTheory.T.triple_lattice_invariant_schwartz_global hP F E σ B a a' G X om om' hT w Ψ hΨ (hyp' w hwS) m f φ h1 hstd h3
        choose r hr using fun i => GlobalTheory.T.triple_lattice_invariant_schwartz_local hP F E σ B a a' G X om om' hT w (g i) (hgSB i) (hgE i)
        refine ih (fun i => r i • f i) (fun i => Function.update (φ i) w (G.M'.vac w)) (fun i v => ?_)
          (fun i v hv hvU => ?_) ?_
        · by_cases hvw : v = w
          · subst hvw
            rw [Function.update_self]
            exact hvSB _
          · rw [Function.update_of_ne hvw]
            exact h1 i v
        · by_cases hvw : v = w
          · subst hvw
            rw [Function.update_self]
          · rw [Function.update_of_ne hvw]
            refine h2 i v hv ?_
            rw [Finset.mem_insert]
            rintro (h | h)
            exacts [hvw h, hvU h]
        · rw [hgsum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hr i, pure_update_smul _ _ _ _ _ (hstd i)]
  obtain ⟨f', φ', h1, h2, h3⟩ := key (T ∪ hfin.toFinset) f₀ φ₀ hSB₀ (fun i v _ hv => by
    rw [hstd₀ i v (fun h => hv (Finset.mem_union_left _ h))]
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 fun h => hne h.symm))) hsum₀
  exact ⟨m, f', φ', h1, h2, h3⟩

end GlobalTheory.VacFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal)

theorem stepFac_ratio_core {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (W : G.Weil) (S : GridChoice W Set.univ) (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ)
    (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (h0 : stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0) :
    GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
      (stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  classical
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨hc1, -, hcmul, hcinv, -⟩ := GlobalTheory.Square.isAwayUnit_closure D.what₂.LL (Qn G t) hQn
  have hone : GlobalTheory.Square.IsAwayUnit (Qn G t) (1 : D.what₂.LL) := GlobalTheory.Square.IsAwayUnit.one _
  have hzpow : ∀ (x : D.what₂.LL) (n : ℕ), 0 < n → x ^ n = 1 → ∀ e : ℤ, GlobalTheory.Square.IsAwayUnit (Qn G t) (x ^ e) := by
    intro x n hn hx e
    refine hc1 _ n hn ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hprod : ∀ (s : Finset Bs.P) (f : Bs.P → D.what₂.LL), (∀ v ∈ s, GlobalTheory.Square.IsAwayUnit (Qn G t) (f v)) →
      GlobalTheory.Square.IsAwayUnit (Qn G t) (∏ v ∈ s, f v) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact hcmul _ _ (hf a (Finset.mem_insert_self _ _)) (ih fun v hv => hf v (Finset.mem_insert_of_mem hv))
  set σ := D.what₂.embLL with hσ
  set X₀ := GlobalTheory.SqStep.chs G i j μ₀ with hX₀
  set X := GlobalTheory.SqStep.chs G i j t with hX
  set Sz := G.pl.S0 with hS0
  set f : Chars D.host.F D.host.E → Bs.P → ℂ := fun Y v =>
    (chrW Y.ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW Y.ν (Bs.τ v)) z with hf
  have hS0T : Sz ⊆ X.T := Finset.subset_union_left
  have hT0 : X₀.T = Sz := GlobalTheory.SqStepArith.chs_T_base G hL i j
  have hst : ∀ Y : Chars D.host.F D.host.E, stepFac Bs Y e₁ e₂ s 𝔟 𝔠 z =
      ((idealVal Y.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) * ((idealVal Y.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Y.T), f Y v := by
    intro Y
    simp only [stepFac, Units.val_mul, Units.val_zpow_eq_zpow_val, hf]

  have hsplit : ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T), f X v =
      (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T)) (fun v : Bs.P => v.1 ∈ Sz),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    · ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hS0T h, h⟩⟩
  have hne : ∀ v : Bs.P, v.1 ∈ Sz → f X v ≠ 0 := by
    intro v hv
    rw [hst, hsplit] at h0
    have h1 := left_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using hv)
  have hS := fun (v : Bs.P) (hv : v.1 ∈ Sz) => _root_.GlobalTheory.SqStepArith.base_place_factor_zero G hL W S hN i j t Bs hB v hv s z (hne v hv)
  choose bS gS gS' hbS hgS hgS' heS using hS
  have hneT : ∀ v : Bs.P, v.1 ∈ X.T → v.1 ∉ Sz → f X v ≠ 0 := by
    intro v hv hv'
    rw [hst, hsplit] at h0
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using And.intro hv hv')
  have hTw := fun (v : Bs.P) (hv : v.1 ∈ X.T) (hv' : v.1 ∉ Sz) => _root_.GlobalTheory.SqTwist.twist_factor G hL W S hN i j t Bs hB v hv hv' s z (hneT v hv hv')
  choose bT hbT heT using hTw
  obtain ⟨b1, ⟨n1, hn1, hb1⟩, e1⟩ := _root_.GlobalTheory.SqStepIdeal.idealVal_chs_base G hL W S hN i j t 𝔟
  obtain ⟨b2, ⟨n2, hn2, hb2⟩, e2⟩ := _root_.GlobalTheory.SqStepIdeal.idealVal_chs_base G hL W S hN i j t 𝔠
  let bS₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ Sz then bS v h else 1
  let bT₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ X.T ∧ v.1 ∉ Sz then bT v h.1 h.2 else 1
  let g : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS ⟨v, h.1⟩ h.2 else 1
  let g' : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS' ⟨v, h.1⟩ h.2 else 1
  have hSP : ∀ v ∈ Sz, v ∈ Bs.P := fun v hv => hB.2.1 (hS0T hv)

  have hmap : ∀ F' : HeightOneSpectrum (𝓞 D.host.F) → D.what₂.LL,
      ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1 = ∏ v ∈ Sz, F' v := by
    intro F'
    rw [show (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1) =
        ∏ v ∈ (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)).map (Function.Embedding.subtype _), F' v from
      (Finset.prod_map (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)) (Function.Embedding.subtype _) F').symm]
    congr 1
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    exact ⟨fun ⟨w, hw, e⟩ => e ▸ hw, fun hv => ⟨⟨v, hSP v hv⟩, hv, rfl⟩⟩
  refine ⟨b1 ^ (e₁ : ℤ) * b2 ^ (e₂ : ℤ) * (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
    (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v), g, g', ?_, ?_, ?_⟩
  · refine hcmul _ _ (hcmul _ _ (hcmul _ _ (hzpow b1 n1 hn1 hb1 _) (hzpow b2 n2 hn2 hb2 _)) ?_) ?_
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ Sz := by simpa using hv
      simp only [bS₁, dif_pos hv']
      exact hbS v hv'
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      exact hbT v hv'.1 hv'.2
  · intro v hv
    have h : v ∈ Bs.P ∧ v ∈ Sz := ⟨hSP v hv, hv⟩
    simp only [g, g', dif_pos h]
    exact ⟨hgS _ h.2, hgS' _ h.2⟩
  · have hA : ∀ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz),
        f X₀ v = σ (bS₁ v * ((g v.1 : D.what₂.LL) / (g' v.1 : D.what₂.LL))) * f X v := by
      intro v hv
      have hv' : v.1 ∈ Sz := by simpa using hv
      have h2 : v.1 ∈ Bs.P ∧ v.1 ∈ Sz := ⟨v.2, hv'⟩
      simp only [bS₁, g, g', dif_pos hv', dif_pos h2]
      exact heS v hv'
    have hTw : (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v) *
        σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v) = 1 := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      rw [mul_comm]
      exact heT v hv'.1 hv'.2
    rw [hst X₀, hst X, hsplit, hT0, Finset.prod_congr rfl hA, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_mul_distrib, hmap (fun v => (g v : D.what₂.LL) / (g' v : D.what₂.LL)), e1, e2, mul_zpow, mul_zpow]
    simp only [map_mul, map_zpow₀]
    linear_combination (-((σ b1) ^ (e₁ : ℤ) * (σ b2) ^ (e₂ : ℤ) *
      σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
      σ (∏ v ∈ Sz, (g v : D.what₂.LL) / (g' v : D.what₂.LL)) * ((idealVal X.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) *
      ((idealVal X.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) * ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v)) * hTw

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

theorem stepFac_ratio : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S _ hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0
  exact stepFac_ratio_core G hL W S hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0

end GlobalTheory.SqStepArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLattices
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperStab

theorem upper_isUStab (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (c : C) :
    ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  rintro β ⟨u, hu, γ, hγ, rfl⟩
  have hs := (M.comp c).Γ_stab γ hγ
  have hh : ∀ x y, herm (M.comp c).Gm (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x)
      (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) y) = herm (M.comp c).Gm x y := by
    intro x y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm c, M.tr_herm]
  refine ⟨⟨hh, fun v => ?_⟩, ⟨hh, fun v => ?_⟩⟩
  · have h1 := M.tr_L' u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact M.Γ_L' c γ hγ _
  · have h1 := M.tr_Λ u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact hs.2 _

end GlobalTheory.UpperStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijectiveStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_element_operator_bijective : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChangeBij.HasOpB ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  first | exact @GlobalTheory.WeylBij.weyl_hasOpB | exact GlobalTheory.WeylBij.weyl_hasOpB | (intros; apply GlobalTheory.WeylBij.weyl_hasOpB <;> assumption)
end

