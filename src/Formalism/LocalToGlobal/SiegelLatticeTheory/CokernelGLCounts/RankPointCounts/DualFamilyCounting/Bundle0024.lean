module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0020
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValDiffProd
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

section General

variable (F : Type) [Field F] [NumberField F]

abbrev mDiff (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors

lemma differentIdeal_ne_zero' : differentIdeal ℤ (𝓞 F) ≠ 0 := by
  exact differentIdeal_ne_bot

variable {F}

lemma pow_mDiff_dvd (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal ^ mDiff F v ∣ differentIdeal ℤ (𝓞 F) := by
  have hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0 := Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  rw [← Associates.mk_dvd_mk, Associates.mk_pow]
  exact (Associates.prime_pow_dvd_iff_le hD hirr).mpr le_rfl

lemma not_pow_succ_mDiff_dvd (v : HeightOneSpectrum (𝓞 F)) :
    ¬ v.asIdeal ^ (mDiff F v + 1) ∣ differentIdeal ℤ (𝓞 F) := by
  have hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0 := Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  intro h
  rw [← Associates.mk_dvd_mk, Associates.mk_pow] at h
  have := (Associates.prime_pow_dvd_iff_le hD hirr).mp h
  exact Nat.lt_irrefl _ (Nat.lt_of_succ_le this)

lemma intValuation_le_of_mem_different (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F}
    (hx : x ∈ differentIdeal ℤ (𝓞 F)) : v.intValuation x ≤ exp (-(mDiff F v : ℤ)) := by
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd]
  exact dvd_trans (pow_mDiff_dvd v) (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx))

lemma exists_mem_different_intValuation_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x ∈ differentIdeal ℤ (𝓞 F), v.intValuation x = exp (-(mDiff F v : ℤ)) := by
  have hnot := not_pow_succ_mDiff_dvd v
  rw [Ideal.dvd_iff_le, IsConcreteLE.not_le_iff_exists] at hnot
  obtain ⟨x, hxD, hxv⟩ := hnot
  refine ⟨x, hxD, le_antisymm (intValuation_le_of_mem_different v hxD) ?_⟩
  have h1 : ¬ v.intValuation x ≤ WithZero.exp (-((mDiff F v + 1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem]
    exact hxv
  have hx0 : v.intValuation x ≠ 0 := by
    intro h0
    apply h1
    rw [h0]
    exact zero_le
  rw [← WithZero.exp_log hx0] at h1 ⊢
  rw [WithZero.exp_le_exp] at h1 ⊢
  push_cast at h1
  omega

lemma valued_algebraMap_coe (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)

lemma valued_dV (v : HeightOneSpectrum (𝓞 F)) : Valued.v (dV v) = exp (-(mDiff F v : ℤ)) := by
  obtain ⟨x, hxD, hxv⟩ := exists_mem_different_intValuation_eq v
  have hex : ∃ d, IsDiffVal v d := by
    refine ⟨algebraMap F (Fv F v) (x : F), ?_, ?_, x, hxD, rfl⟩
    · intro h0
      have := valued_algebraMap_coe v x
      rw [h0, map_zero, hxv] at this
      exact WithZero.exp_ne_zero this.symm
    · intro y hy
      rw [valued_algebraMap_coe, valued_algebraMap_coe, hxv]
      exact intValuation_le_of_mem_different v hy
  have hd : IsDiffVal v (dV v) := by
    unfold dV
    rw [dite_eq_left hex]
    exact hex.choose_spec
  obtain ⟨-, hle, y, hyD, hyv⟩ := hd
  apply le_antisymm
  · rw [← hyv, valued_algebraMap_coe]
    exact intValuation_le_of_mem_different v hyD
  · have := hle x hxD
    rwa [valued_algebraMap_coe, hxv] at this

lemma absV_of_valued_eq (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) (n : ℤ) (h : Valued.v x = exp n) :
    absV v x = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n := by
  have hx : Valued.v x ≠ 0 := by
    rw [h]
    exact WithZero.exp_ne_zero
  unfold absV
  rw [dite_eq_right hx]
  congr 1
  have hu : WithZero.unzero hx = Multiplicative.ofAdd n := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [hu, toAdd_ofAdd]

lemma absV_dV (v : HeightOneSpectrum (𝓞 F)) :
    absV v (dV v) = ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 F))) : ℕ) : ℝ)⁻¹ := by
  rw [absV_of_valued_eq v _ _ (valued_dV v), IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow,
    zpow_neg, zpow_natCast, Nat.cast_pow]


variable (F) in
theorem hasProd_absV_dV :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (|(discr F : ℝ)|⁻¹) := by
  have hD := differentIdeal_ne_zero' F
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing (differentIdeal ℤ (𝓞 F))).Finite := Ideal.hasFiniteMulSupport hD
  have hfac : ∏ v ∈ hfin.toFinset, v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = differentIdeal ℤ (𝓞 F) := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hfin.mem_toFinset.mpr hv)]
    exact Ideal.finprod_heightOneSpectrum_factorization hD
  have hone : ∀ v ∉ hfin.toFinset, absV v (dV v) = 1 := by
    intro v hv
    rw [absV_dV]
    have h1 : v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = 1 := by
      by_contra hc
      exact hv (hfin.mem_toFinset.mpr hc)
    rw [h1, map_one]
    simp
  have hval : ∏ v ∈ hfin.toFinset, absV v (dV v) = |(discr F : ℝ)|⁻¹ := by
    rw [Finset.prod_congr rfl (fun v _ => absV_dV v), Finset.prod_inv_distrib, ← Nat.cast_prod, ← map_prod, hfac,
      NumberField.absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs]
  have key : HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (∏ v ∈ hfin.toFinset, absV v (dV v)) :=
    hasProd_prod_of_ne_finset_one hone
  rw [hval] at key
  exact key

end General

section Loc

variable {D : D7} (X : HidaSetting D)

theorem diffProd_holds : DiffProd X := by
  exact hasProd_absV_dV _

end Loc

end Formalism.L2.SG.Pf.NcVal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def scl (v : PlX X) : Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v :=
  Fin.append (alp v D.R.rS) (fun b : Fin D.R.rS => (alp v D.R.rS b.castSucc)⁻¹)

def yTup (v : PlX X) : TupV (E := X.B.I.E) v X.B.I.n (D.R.rS + 1 + D.R.rS) :=
  fun i => sc (E := X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i

def localGramMatrixFrame (v : PlX X) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v))

abbrev abelian₂ : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def OmVStd : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → StdHyp X.B.I.cm.sig X.B.I.J ψ

def OmVLat : Prop :=
  ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E), Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = abelian₂ X

def OmVSD : Prop := ∀ v : PlX X, IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X)

def OmVUnram : Prop := ∀ v : PlX X, UnramAt (E := X.B.I.E) v

def OmVPrim : Prop := ∀ v : PlX X, IsPrim v (abelian₂ X) (yTup X u' v)

def OmVGram : Prop := ∀ v : PlX X, gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) = localGramMatrixFrame X u' v

def OmVDet : Prop :=
  ∀ v : PlX X, ¬ (((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) →
    ∃ w ∈ OEv (E := X.B.I.E) v, (localGramMatrixFrame X u' v).det ∈ OEv (E := X.B.I.E) v ∧ (localGramMatrixFrame X u' v).det * w = 1

def OmVScale : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} =
      omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v}

def OmVBadT : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X) → UnramAt (E := X.B.I.E) v → IsPrim v (abelian₂ X) (yTup X u' v) →
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      ENNReal.ofReal (absV v (dV v) ^ ((X.B.I.n : ℝ) * (D.R.rS + 1 + D.R.rS : ℕ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) *
        ∏ j ∈ Finset.Icc (X.B.I.n - (D.R.rS + 1 + D.R.rS)) X.B.I.n,
          (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))))

def OmVLocU : Prop :=
  ∀ (v : PlX X) (a : ℕ) (Y : TupV (E := X.B.I.E) v X.B.I.n a),
    Formalism.L2.SG.Pf.NcLoc.OmLocU X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFixPushIff
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

def stabEquivW (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) (N : Submodule (𝓞 K) ↥(orthK h U)) :
    stabFix h U (push (orthK h U) N) ≃ Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N where
  toFun g := ⟨restr g.2.1, restr_mem g.2.1, push_injective _ (by rw [← gmap_push g.2.1]; exact g.2.2)⟩
  invFun g := ⟨extId hc g.1, extId_mem hs hc g.2.1, by rw [gmap_extId_push hs hc g.2.1, g.2.2]⟩
  left_inv g := Subtype.ext (extId_restr hc g.2.1)
  right_inv g := Subtype.ext (restr_extId hs hc g.2.1)

theorem card_stab_push (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) (N : Submodule (𝓞 K) ↥(orthK h U)) :
    Nat.card (stabFix h U (push (orthK h U) N)) = Nat.card (Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N) :=
  Nat.card_congr (stabEquivW hs hc N)

theorem sameGenusFix_push_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hc : IsCompl U (orthK h U)) (A B : Submodule (𝓞 K) ↥(orthK h U)) :
    SameGenusFix (F := F) h U (push (orthK h U) A) (push (orthK h U) B) ↔
      Formalism.HermitianLatticesTheory.SameGenus (formOn h (orthK h U)) A B := by
  rw [GoodGenusOrbits.sameGenus_iff (F := F) hK hF A B]
  constructor
  · intro H 𝔭
    obtain ⟨g, hg, e⟩ := H 𝔭.1 𝔭.2
    refine ⟨restr hg, restr_mem hg, push_injective _ ?_⟩
    rw [← gmap_push hg, push_locF _ 𝔭.2.isPrime, push_locF _ 𝔭.2.isPrime]
    exact e
  · intro H 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := H ⟨𝔭, h𝔭⟩
    refine ⟨extId hc g, extId_mem hs hc hg, ?_⟩
    rw [← push_locF _ h𝔭.isPrime, ← push_locF _ h𝔭.isPrime, gmap_extId_push hs hc hg]
    exact congrArg _ e

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SdBasisBot
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem sd_basis_bot {W : Submodule K V} {M : AddSubgroup V} (hM : IsSD S h W M) (hW : W = ⊥) :
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun v => ?_, ?_⟩
  · rw [spanS_empty]
    constructor
    · rintro rfl
      exact M.zero_mem
    · intro hv
      have := hM.le v hv
      rwa [hW, Submodule.mem_bot] at this
  · rw [hW, Set.range_eq_empty, Submodule.span_empty]

theorem sup_cutW {W : Submodule K V} {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    K ∙ x ⊔ cutW h W x = W := by
  apply le_antisymm
  · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) inf_le_left
  · intro w hw
    have e : w = (h x w * (h x x)⁻¹) • x + (w - (h x w * (h x x)⁻¹) • x) := by abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) ?_
    refine mem_cutW.mpr ⟨W.sub_mem hw (W.smul_mem _ hx), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hxx, mul_one, sub_self]

theorem sd_basis (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) : ∀ (n : ℕ) (W : Submodule K V) (M : AddSubgroup V),
    finrank K W ≤ n → IsSD S h W M →
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  intro n
  induction n with
  | zero =>
    intro W M hn hM
    exact sd_basis_bot hM (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn))
  | succ n ih =>
    intro W M hn hM
    by_cases hbot : W = ⊥
    · exact sd_basis_bot hM hbot
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    have hxW := hM.le x hx
    obtain ⟨k, f, hfo, hfu, hfM, hfW⟩ := ih _ _
      (by have := finrank_cutW_lt (h := h) hxW hu.1; omega) (hM.cut hx hu)
    have hfc : ∀ i, f i ∈ cutW h W x := fun i => by
      rw [← hfW]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hfm : ∀ i, f i ∈ M := fun i =>
      (mem_cutM.mp ((hfM (f i)).mp (mem_spanS_self f i))).1
    refine ⟨k + 1, Fin.cons x f, ?_, ?_, fun v => ?_, ?_⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_cutW.mp (hfc j)).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa using symm_zero hs (mem_cutW.mp (hfc i)).2
        | succ j =>
          simpa using hfo i j (fun h' => hij (by rw [h']))
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hfu i
    · constructor
      · rintro ⟨c, hc, rfl⟩
        refine M.sum_mem fun i _ => hM.smul_mem _ (hc i) _ ?_
        cases i using Fin.cases with
        | zero => simpa using hx
        | succ i => simpa using hfm i
      · intro hv
        obtain ⟨d, hd', hdv⟩ := (hfM _).mpr (proj_mem hM.toIsLatIn hx hu hv)
        refine ⟨Fin.cons (h x v * (h x x)⁻¹) d, fun i => ?_, ?_⟩
        · cases i using Fin.cases with
          | zero => simpa using S.mul_mem (hM.int _ hx _ hv) hu.2.2
          | succ i => simpa using hd' i
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hdv]
          abel
    · rw [Fin.range_cons, Submodule.span_insert, hfW]
      exact sup_cutW hxW hu.1

end

end Formalism.L2.SG.Pf.G3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SummandLocalization
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.LocalSpans

theorem summand_localization : SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 h𝔭 Λ ⟨L, hL, rfl⟩
  let W := Submodule.span K (L : Set V)
  let i := W.subtype.restrictScalars (𝓞 K)
  let L' := L.comap i
  have hmap : L'.map i = L := by
    apply Submodule.map_comap_eq_self
    change L ≤ LinearMap.range (W.restrictScalars (𝓞 K)).subtype
    rw [Submodule.range_subtype]
    exact fun _ hx => Submodule.subset_span hx
  have hfull : Submodule.IsFullLattice K L' := by
    have hfg : L'.FG := Submodule.fg_of_fg_map_injective i Subtype.val_injective
      (hmap.symm ▸ hL.fg)
    letI : Submodule.IsLattice K L' := Submodule.IsLattice.of_fg K hfg
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
    have himage : W.subtype '' (L' : Set W) = (L : Set V) := by
      rw [← hmap, Submodule.map_coe]
      rfl
    rw [Submodule.map_span, himage, Submodule.map_top, Submodule.range_subtype]
  let X' := X.comap W.subtype
  let Lloc := UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 L'
  obtain ⟨p, hpX, hpId, hpL⟩ :=
    UpperTheory.Reformulated.B.SummandLocalization.summand_localization
      K F W X' 𝔭 h𝔭 Lloc ⟨L', hfull, rfl⟩
  let N := (LinearMap.ker p).map W.subtype
  have hNX : Disjoint N X := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨w, hw, rfl⟩ hx
    have hzero : p w = 0 := hw
    rw [hpId w hx] at hzero
    exact congrArg Subtype.val hzero
  obtain ⟨Y, hNY, hYX⟩ := hNX.exists_isCompl
  let π := X.projection Y hYX.symm
  have hπ (w : W) : π w = (p w : V) := by
    have hdiff : (w : V) - (p w : V) ∈ Y := hNY ⟨w - p w, by
      change p (w - p w) = 0
      rw [map_sub, hpId _ (hpX w), sub_self], rfl⟩
    have he := Submodule.projection_apply_of_mem_right hYX.symm hdiff
    change π ((w : V) - (p w : V)) = 0 at he
    have hp : (p w : V) ∈ X := hpX w
    have hproj : π (p w : V) = (p w : V) :=
      Submodule.projection_apply_of_mem_left hYX.symm hp
    rwa [map_sub, hproj, sub_eq_zero] at he
  refine ⟨π, Submodule.projection_apply_mem hYX.symm,
    fun _ hx => Submodule.projection_apply_of_mem_left hYX.symm hx, ?_⟩
  letI := h𝔭.isPrime
  intro y hy
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  have ht0 : t ≠ 0 := fun ht0 => ht (ht0 ▸ 𝔭.zero_mem)
  let a := algebraMap (𝓞 F) (𝓞 K) t
  have ha : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h
    apply ht0
    apply RingOfIntegers.algebraMap.injective F K
    apply (RingOfIntegers.coe_injective)
    simpa [a] using h
  have hyW : y ∈ W := by
    have hs : algebraMap (𝓞 K) K a • y ∈ W := by
      rw [algebraMap_smul]
      exact Submodule.subset_span hty
    have h := W.smul_mem (algebraMap (𝓞 K) K a)⁻¹ hs
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h
  let w : W := ⟨y, hyW⟩
  have hwL : w ∈ Lloc := (LocalSpans.mem_locF 𝔭 L' w).2 ⟨t, ht, hty⟩
  rw [show y = (w : V) from rfl, hπ w]
  obtain ⟨u, hu, hpu⟩ := (LocalSpans.mem_locF 𝔭 L' (p w)).1 (hpL w hwL)
  exact (LocalSpans.mem_locF 𝔭 L (p w : V)).2 ⟨u, hu, hpu⟩

end Formalism.L2.SG.Pf.G6
end
end

