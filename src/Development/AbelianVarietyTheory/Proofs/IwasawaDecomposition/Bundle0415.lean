module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSelfDualLatticeCoordsIffIntegralPosSpace
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VvCastBVVRepr
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.RowStd

section Cast

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

def castSp (h : n = n') : (Fin n → E) ≃ₗ[E] (Fin n' → E) :=
  LinearEquiv.funCongrLeft E E (finCongr h).symm

def SameWt (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') : Prop :=
  ∀ τ i, (lam' τ).w i = (lam τ).w (Fin.cast h.symm i)

theorem sameWt_eq (lam lam' : ι → DomWeight n) (hl : SameWt rfl lam lam') : lam' = lam := by
  funext τ
  cases h1 : lam' τ with
  | mk w a =>
    cases h2 : lam τ with
    | mk w' a' =>
      have : w = w' := funext fun i => by
        have := hl τ i
        rw [h1, h2] at this
        simpa using this
      subst this
      rfl

def vvCast (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') (hl : SameWt h lam lam') :
    VV K lam ≃ₗ[K] VV K lam' := by
  subst h
  exact LinearEquiv.ofEq _ _ (by rw [sameWt_eq lam lam' hl])

end Cast

section CastLemmas

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem vvCast_self (lam : ι → DomWeight n) (hl : SameWt rfl lam lam) :
    vvCast (K := K) rfl lam lam hl = LinearEquiv.refl K (VV K lam) := by
  ext x
  rfl

theorem vvCast_rhoV (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (g : GL (Fin n) E) (g' : GL (Fin n') E) (hg : MatEq g' g) (v : VV K lam) :
    vvCast h lam lam' hl (rhoV emb lam g v) = rhoV emb lam' g' (vvCast h lam lam' hl v) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  have hg' : g' = g := Units.ext (Matrix.ext fun i j => hg.2 i j i j rfl rfl)
  subst hg'
  rw [vvCast_self]
  rfl

end CastLemmas

section CastLemmas2

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem castSp_self : castSp (E := E) (rfl : n = n) = LinearEquiv.refl E (Fin n → E) := by
  ext x i
  rfl

theorem vvCast_pairV [StarRing K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E)
    (hJ : ∀ i j, J' i j = J (Fin.cast h.symm i) (Fin.cast h.symm j)) (x y : VV K lam) :
    pairV emb lam' J' (vvCast h lam lam' hl x) (vvCast h lam lam' hl y) = pairV emb lam J x y := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  have hJ' : J' = J := Matrix.ext fun i j => hJ i j
  subst hJ'
  rw [vvCast_self]
  rfl

theorem vvCast_bVV_repr [StarRing K] (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (i : VVIdx lam) (j : VVIdx lam') :
    (bVV K lam').repr (vvCast h lam lam' hl (bVV K lam i)) j ∈ Formalism.DivisionValues.cmMax K := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, LinearEquiv.refl_apply, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst hij
    rw [Finsupp.single_eq_same]
    exact (Formalism.DivisionValues.cmMax K).one_mem
  · rw [Finsupp.single_eq_of_ne (Ne.symm hij)]
    exact (Formalism.DivisionValues.cmMax K).zero_mem

theorem vvCast_nabAt [NumberField K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n)
    (lam' : ι → DomWeight n') (hl : SameWt h lam lam') (N : Submodule (𝓞 E) (Fin n → E)) :
    (nabAt emb lam N).map (((vvCast (K := K) h lam lam' hl).toLinearMap).restrictScalars (𝓞 K)) =
      nabAt emb lam' (N.map (((castSp (E := E) h).toLinearMap).restrictScalars (𝓞 E))) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, castSp_self]
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.restrictScalars_id, Submodule.map_id]

theorem vvCast_delAt [NumberField K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n)
    (lam' : ι → DomWeight n') (hl : SameWt h lam lam') (N : Submodule (𝓞 E) (Fin n → E)) :
    (delAt emb lam N).map (((vvCast (K := K) h lam lam' hl).toLinearMap).restrictScalars (𝓞 K)) =
      delAt emb lam' (N.map (((castSp (E := E) h).toLinearMap).restrictScalars (𝓞 E))) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, castSp_self]
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.restrictScalars_id, Submodule.map_id]

end CastLemmas2

section CastLemmas3

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem vvCast_bVV (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') (hl : SameWt h lam lam') :
    ∃ f : VVIdx lam ≃ VVIdx lam', ∀ i, vvCast (K := K) h lam lam' hl (bVV K lam i) = bVV K lam' (f i) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  exact ⟨Equiv.refl _, fun i => by rw [vvCast_self]; rfl⟩

theorem one_cast (h : n = n') (i j : Fin n') :
    (1 : Matrix (Fin n') (Fin n') E) i j = (1 : Matrix (Fin n) (Fin n) E) (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  simp only [Matrix.one_apply, Fin.cast_inj]

end CastLemmas3

section Gram

open GlobalTheory.Mem GlobalTheory.Mem.Col2

theorem gram_X'_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (h : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := h.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

end Gram

end GlobalTheory.Mem.R3.RowStd

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowStd

theorem sameWt_true (X : Stages) :
    SameWt (RowAd.rank_X' X).symm X.B.wts.sgTrue (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
  RowWeight.lamRdef_eq_sgTrue X

def wtCast (X : Stages) :
    VV X.toD7.what₂.LL X.B.wts.sgTrue ≃ₗ[X.toD7.what₂.LL] VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
  vvCast (RowAd.rank_X' X).symm _ _ (sameWt_true X)


set_option maxHeartbeats 4000000 in
theorem exists_coef : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∃ c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W,
      (∀ v, c v = c0R (wtCast X v)) ∧
      (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
        Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) ∧
      LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) ∧
      Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ ∧
      (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) ∧
      ∀ t (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ),
        (∀ x, P.coef x = c x) →
        (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') →
        Bridge.CoefTie X.toD7.sp.X' cX.coef P (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
          (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L hI cX gramR c0R hc hgr hM hin
  have hw := sameWt_true X
  let e0 : VV X.toD7.what₂.LL X.B.wts.sgTrue ≃ₗ[X.toD7.what₂.LL] VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
    vvCast (RowAd.rank_X' X).symm _ _ hw
  let c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W := (by with_unfolding_all exact (c0R.comp e0.toLinearMap :))
  have hgram := gram_X'_eq_one X I hI
  have hpair : ∀ x y, pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) gramR (e0 x) (e0 y) =
      pairV X.B.fields.emb X.B.wts.sgTrue 1 x y := by
    intro x y
    rw [GlobalTheory.RowsSign.pairV_gramR_eq X px I hI cX gramR c0R hc hgr hM hin, hgram]
    exact vvCast_pairV (labLL X.toD7) _ _ _ hw 1 1 (one_cast (RowAd.rank_X' X).symm) x y
  have hInter : ∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
      Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v) := by
    intro γ γE g hγ hm v
    have key := vvCast_rhoV (labLL X.toD7) _ _ _ hw g γE hm v
    exact (congrArg c0R key).trans (hM.1 γ γE hγ _)
  obtain ⟨f, hf⟩ := vvCast_bVV (K := X.toD7.what₂.LL) (RowAd.rank_X' X).symm _ _ hw
  have hcf : (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) =
      (fun j => c0R (bVV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) j)) ∘ f := by
    funext i
    exact congrArg c0R (hf i)
  have hli : LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) := by
    rw [hcf]
    exact hM.2.1.comp f f.injective
  have hsp : Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ := by
    have h2 := f.surjective.range_comp (fun j => c0R (bVV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) j))
    rw [hcf]
    refine Eq.trans ?_ hM.2.2
    exact congrArg (Submodule.span ℂ) h2
  have hinn : ∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y) := by
    intro x y
    exact (hin _ _).trans (congrArg X.toD7.what₂.embLL (hpair x y))
  refine ⟨c, fun v => rfl, hInter, hli, hsp, hinn, fun t P hPc hPy => ⟨e0, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j
    exact vvCast_bVV_repr _ _ _ hw i j
  · intro x
    exact hPc x
  · intro x x'
    exact hpair x x'
  · intro c'
    rw [RowLat.hLat_eq_decoAd_N X px I hX hI U t (P.y c'), hPy c']
    exact vvCast_nabAt (labLL X.toD7) _ _ _ hw _
  · intro c'
    rw [RowLat.hLat_eq_decoAd_N X px I hX hI U t (P.y c'), hPy c']
    exact vvCast_delAt (labLL X.toD7) _ _ _ hw _

end GlobalTheory.Mem.R3.RowStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationRulesHold
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilRule

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem isAdmissibleSplittingCharPair_symm {V W : HSp D} {χ χ' : IdC D} (ha : admitted V W χ χ') : admitted W V χ' χ :=
  ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩

theorem resEta_one (D : D7) : ResEta D 1 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ _ => by simp⟩

theorem isAdmissibleSplittingCharPair_mul_twist {V W : HSp D} {χ χ' ν ν' : IdC D} (ha : admitted V W χ χ') (h1 : IsHC D ν) (h2 : IsHC D ν')
    (r1 : ResEta D ν 0) (r2 : ResEta D ν' 0) : admitted V W (χ * ν) (χ' * ν') := by
  obtain ⟨C, hC⟩ := (GlobalTheory.Mem.HeckeExp.hecke_exp_laws D).1
  exact ⟨ha.1, (hC _).1 (C.mul_mem ((hC _).2 ha.2.1) ((hC _).2 h1)), (hC _).1 (C.mul_mem ((hC _).2 ha.2.2.1) ((hC _).2 h2)),
    resEta_mul ha.2.2.2.1 r1, resEta_mul ha.2.2.2.2 r2⟩

theorem twist_small (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank)
    (h1 : IsHC D ν) (h2 : IsHC D ν') (r1 : ResEta D ν 0) (r2 : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om)
    (H' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g h x y} (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = ((((ν' x)⁻¹ * ν y : Circle) : ℂ)) • om (g, h) := by
  obtain ⟨o, ho, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ V W χ χ' om ha hr H
  obtain ⟨o', ho', e'⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ V W _ _ om' (isAdmissibleSplittingCharPair_mul_twist ha h1 h2 r1 r2) hr H'
  obtain ⟨o'', ho'', e''⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ V W χ χ' ν ν' o ho h1.1 h2.1 r1 r2
  obtain ⟨c, -, -, hc, -, -, -, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  refine LinearMap.ext fun Φ => Subtype.ext (funext fun w => ?_)
  obtain ⟨u, rfl⟩ := c.surjective w
  have hf : IsThetaFunO ψ V W fun x => Φ.1 (toTWsmall V W x) := by
    simpa only [hc] using (hth ψ Φ.1).2 (mem_ThS.1 Φ.2)
  have k := congrFun (_root_.GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ V W _ _ o' o'' ho' ho'' (g, h) _ hf) u
  rw [e', e'' g h x y hx hy, LinearMap.smul_apply, e] at k
  rw [hc]
  exact k

theorem exists_swap (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' : IdC D} (hne : V.rank ≠ W.rank)
    {om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om) :
    ∃ om' : GA D W × GA D V →* Module.End ℂ (ThS ψ W V), IsWeilOn ψ W V χ' χ om' ∧
      ∀ g h Φ, om' (h, g) (WeilSwap.trEquiv ψ hne Φ) = WeilSwap.trEquiv ψ hne (om (g, h) Φ) := by
  obtain ⟨om', H', e⟩ := WeilSwap.exists_isWeilOn_swap D ψ hψ V W χ χ' om hne H
  exact ⟨om', H', fun g h Φ => Subtype.ext (funext fun y => e g h Φ _ (fun _ => rfl) y.transpose)⟩

theorem twist (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D} (ha : admitted V W χ χ')
    (h1 : IsHC D ν) (h2 : IsHC D ν') (r1 : ResEta D ν 0) (r2 : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om)
    (H' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g h x y} (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = (((if V.rank < W.rank then (ν' x)⁻¹ * ν y else (ν y)⁻¹ * ν' x : Circle) : ℂ)) • om (g, h) := by
  rcases ha.1.lt_or_gt with hr | hr
  · rw [if_pos hr]; exact twist_small hψ ha hr h1 h2 r1 r2 H H' hx hy
  · rw [if_neg hr.not_gt]
    obtain ⟨o, ho, e⟩ := exists_swap hψ ha.1 H
    obtain ⟨o', ho', e'⟩ := exists_swap hψ ha.1 H'
    refine LinearMap.ext fun Φ => (WeilSwap.trEquiv ψ ha.1).injective ?_
    rw [← e', twist_small hψ (isAdmissibleSplittingCharPair_symm ha) hr h2 h1 r2 r1 ho ho' hy hx, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, e]

theorem unique (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' : IdC D} (ha : admitted V W χ χ')
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om)
    (H' : IsWeilOn ψ V W χ χ' om') : om' = om := by
  refine MonoidHom.ext fun ⟨g, h⟩ => ?_
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D V g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D W h
  have := twist hψ ha (isHC_one D) (isHC_one D) (resEta_one D) (resEta_one D) H (by simpa only [mul_one] using H') hx hy
  simpa using this

theorem map_eq_one_of_supp {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {a x : R} (ha : φ a = 0)
    (hx : a * (x - 1) = x - 1) : φ x = 1 := by
  have := congrArg φ hx
  rw [map_mul, ha, zero_mul, map_sub, map_one] at this
  exact sub_eq_zero.1 this.symm

theorem unramAt_of_outside {χ : IdC D} {Z : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : UnramOutside D χ Z)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ Z) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : UnramAt ε χ := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  intro x hx i1 i2
  refine h x (map_eq_one_of_supp (infPart D) (TensorProduct.zero_tmul _ _) hx) i1 i2 fun w hw => ?_
  refine map_eq_one_of_supp
    ((Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)).toRingHom.comp (finPart D)) ?_ hx
  change evalV D.host.F w β ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  rw [h0 w fun e => hv (e ▸ hw), TensorProduct.zero_tmul]

theorem fixes_local {S T : HSp D} {χS χT : IdC D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (uS : UnramAt ε χS) (uT : UnramAt ε χT) {g : GA D S} {h : GA D T} (hg : g ∈ KsphC S ∅) (hh : h ∈ KsphC T ∅)
    (sg : SuppPl ε S g) (sh : SuppPl ε T h) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hv : ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w = v), heisO ψ S T u f = f) : om (g, h) f = f := by
  obtain ⟨KS, hKS, -⟩ := GlobalTheory.Mem.Ksph.exists_subgroup_ksph D S ∅
  obtain ⟨KT, hKT, -⟩ := GlobalTheory.Mem.Ksph.exists_subgroup_ksph D T ∅
  have hg' : g⁻¹ ∈ KsphC S ∅ := by rw [← hKS] at hg ⊢; exact KS.inv_mem hg
  have hh' : h⁻¹ ∈ KsphC T ∅ := by rw [← hKT] at hh ⊢; exact KT.inv_mem hh
  by_cases hs : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e, he, heq⟩ := hs
    obtain ⟨x, hx, hx1⟩ := GlobalTheory.Mem.DetUnit.exists_isDetAt_unram D S ε e he heq g hg
    obtain ⟨y, hy, hy1⟩ := GlobalTheory.Mem.DetUnit.exists_isDetAt_unram D T ε e he heq h hh
    have he' : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]
    have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he.1 + he.2.1
    have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + he.2.1
    refine GlobalTheory.SplitHecke.om_eq_self_of_lattice_stable D ψ S T χS χT om H e he g h (fun i j => by rw [heq]; exact sg i j)
      (fun i j => by rw [heq]; exact sh i j) x y hx hy (by rw [splitFacO, hx1 _ uT, hy1 _ uS, inv_one, mul_one])
      (GlobalTheory.LatStabAct.actO_mem_latO_of_stab D S T _ hg' _ hh' _) f hf fun u hu hh => hv u ?_
    rcases hh with hh | hh
    · have := (GlobalTheory.PlaceModel.idem_smul_mem hε he.1 heε hu).1
      rwa [show e • u = u from Matrix.ext hh] at this
    · have := (GlobalTheory.PlaceModel.idem_smul_mem hε he' heε' hu).1
      rwa [show cA D e • u = u from Matrix.ext hh] at this
  · obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
    have k := _root_.GlobalTheory.VacInert.fixesVacAt_of_unram D ψ H.std S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
      χS χT om ⟨η, e1, e4, e3, e2⟩ H v ε ⟨hε, hs⟩ uS uT g h sg sh
    rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at k
    refine k (fun u => ⟨GlobalTheory.LatStabAct.actO_mem_latO_of_stab D S T _ hg _ hh _ u, fun hu => ?_⟩) f hf hv
    have := GlobalTheory.LatStabAct.actO_mem_latO_of_stab D S T _ hg' _ hh' _ _ hu
    have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
    rw [inv_inv, inv_inv] at e
    rwa [e] at this

theorem latO_mono {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P Q : HeightOneSpectrum (𝓞 D.host.F) → Prop} (h : ∀ w, P w → Q w) : latO S T LS LT P ≤ latO S T LS LT Q :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, h0, k⟩ => ⟨α, hα, fun w hw => h0 w fun e => hw (h w e), k⟩

theorem fixes_oriented {S T : HSp D} {χS χT : IdC D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) {Z : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (uS : UnramOutside D χS Z) (uT : UnramOutside D χT Z) {g : GA D S} {h : GA D T} (hg : g ∈ KsphC S Z) (hh : h ∈ KsphC T Z)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hv : ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w ∉ Z), heisO ψ S T u f = f) : om (g, h) f = f := by
  let K : Subgroup (GA D S × GA D T) :=
    { carrier := {p | om p f = f}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change om (a * b) f = f
        rw [map_mul, Module.End.mul_apply, show om b f = f from hb, show om a f = f from ha]
      inv_mem' := fun {a} ha => by
        change om a⁻¹ f = f
        conv_lhs => rw [← show om a f = f from ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hK : IsClosed (K : Set (GA D S × GA D T)) :=
    isClosed_eq (continuous_pi fun w => H.om_cont f hf w) continuous_const
  have hl : ∀ v, v ∉ Z → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w = v), heisO ψ S T u f = f := fun v hvZ u hu =>
    hv u (latO_mono (fun w (e : w = v) => e ▸ hvZ) hu)
  have one : ∀ V : HSp D, (1 : GA D V) ∈ KsphC V ∅ := fun V => by
    obtain ⟨KV, hKV, -⟩ := GlobalTheory.Mem.Ksph.exists_subgroup_ksph D V ∅
    rw [← hKV]; exact KV.one_mem
  have sone : ∀ (V : HSp D) ε, SuppPl ε V 1 := fun V ε i j => by simp [Formalism.L2.Theta.mt]
  have k1 : g ∈ K.comap (MonoidHom.inl _ _) :=
    GlobalTheory.LevelClosure.ksph_le_of_isClosed D S Z _ (hK.preimage (continuous_id.prodMk continuous_const))
      (fun v hvZ ε hε g hg sg => fixes_local H hε (unramAt_of_outside uS hvZ hε) (unramAt_of_outside uT hvZ hε) hg (one T) sg
        (sone T ε) hf (hl v hvZ)) g hg
  have k2 : h ∈ K.comap (MonoidHom.inr _ _) :=
    GlobalTheory.LevelClosure.ksph_le_of_isClosed D T Z _ (hK.preimage (continuous_const.prodMk continuous_id))
      (fun v hvZ ε hε h hh sh => fixes_local H hε (unramAt_of_outside uS hvZ hε) (unramAt_of_outside uT hvZ hε) (one S) hh
        (sone S ε) sh hf (hl v hvZ)) h hh
  have : (g, h) ∈ K := by simpa using K.mul_mem k1 k2
  exact this

theorem fixes_small (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank)
    {om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om)
    {Z : Finset (HeightOneSpectrum (𝓞 D.host.F))} (u1 : UnramOutside D χ Z) (u2 : UnramOutside D χ' Z)
    {g : GA D V} {h : GA D W} (hg : g ∈ KsphC V Z) (hh : h ∈ KsphC W Z) (Φ : ThS ψ V W)
    (hv : ∀ u ∈ latVWS V W Z, Heisenberg₂ ψ V W u Φ.1 = Φ.1) : om (g, h) Φ = Φ := by
  obtain ⟨o, ho, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ V W χ χ' om ha hr H
  obtain ⟨c, -, -, hc, -, -, hhe, hth, hl⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  have k := fixes_oriented ho u1 u2 hg hh ((hth ψ Φ.1).2 (mem_ThS.1 Φ.2)) fun u hu => by
    rw [hhe, hv _ (hl Z u hu)]
  simp only [hc] at k
  rw [e] at k
  refine Subtype.ext (funext fun w => ?_)
  obtain ⟨u, rfl⟩ := c.surjective w
  rw [hc]
  exact congrFun k u

theorem transpose_mem_latVWS {V W : HSp D} (hne : V.rank ≠ W.rank) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    {u : WA V W} (hu : u ∈ latVWS V W Z) : u.transpose ∈ latVWS W V Z := by
  have : latVWS V W Z ≤ (latVWS W V Z).comap (Matrix.transposeAddEquiv _ _ _).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, h0, a, ha, x, hx, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, y, hy, x, hx, Matrix.ext fun i j => ?_⟩
    change _ ⊗ₜ _ = _ ⊗ₜ _
    congr 1
    rcases hne.lt_or_gt with hr | hr
    · rw [if_pos hr.le, if_neg hr.not_ge]; ring
    · rw [if_neg hr.not_ge, if_pos hr.le]; ring
  exact this hu

theorem weilRules : ∀ D : D7, WeilRules D := by
  intro D ψ hψ Wc
  refine ⟨fun V W χ χ' ν ha h1 r1 g h x hx => ?_, fun V W χ χ' ν ha h1 r1 g h y hy => ?_,
    fun V W χ χ' ha g h Φ Φ' e x => ?_, fun V W χ χ' ha Z u1 u2 g hg h hh Φ hv => ?_⟩
  · obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D W h
    have := twist hψ ha (isHC_one D) h1 (resEta_one D) r1 (Wc.weil V W χ χ' ha)
      (Wc.weil V W _ _ (isAdmissibleSplittingCharPair_mul_twist ha (isHC_one D) h1 (resEta_one D) r1)) hx hy
    simpa only [mul_one, MonoidHom.one_apply, inv_one, one_mul] using this
  · obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D V g
    have := twist hψ ha h1 (isHC_one D) r1 (resEta_one D) (Wc.weil V W χ χ' ha)
      (Wc.weil V W _ _ (isAdmissibleSplittingCharPair_mul_twist ha h1 (isHC_one D) r1 (resEta_one D))) hx hy
    simpa only [mul_one, MonoidHom.one_apply, inv_one, one_mul] using this
  · obtain ⟨o, ho, k⟩ := WeilSwap.exists_isWeilOn_swap D ψ hψ V W χ χ' _ ha.1 (Wc.weil V W χ χ' ha)
    rw [unique hψ (isAdmissibleSplittingCharPair_symm ha) ho (Wc.weil W V χ' χ (isAdmissibleSplittingCharPair_symm ha))]
    exact k g h Φ Φ' e x
  · rcases ha.1.lt_or_gt with hr | hr
    · exact fixes_small hψ ha hr (Wc.weil V W χ χ' ha) u1 u2 hg hh Φ hv
    · obtain ⟨o, ho, k⟩ := exists_swap hψ ha.1 (Wc.weil V W χ χ' ha)
      refine (WeilSwap.trEquiv ψ ha.1).injective ?_
      rw [← k]
      refine fixes_small hψ (isAdmissibleSplittingCharPair_symm ha) hr ho u2 u1 hh hg _ fun u hu => ?_
      refine (WeilSwap.heis_transpose ψ ha.1.symm u Φ.1).symm.trans ?_
      rw [hv _ (transpose_mem_latVWS ha.1.symm Z hu)]
      rfl

end GlobalTheory.Mem.WeilRule

end
end

