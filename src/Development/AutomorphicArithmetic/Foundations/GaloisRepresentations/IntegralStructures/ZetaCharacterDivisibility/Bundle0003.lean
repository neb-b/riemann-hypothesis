module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0221
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PWDFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSepPin
section
open Polynomial

namespace UpperTheory.Gal.Int.Div

theorem sepPin_of : SepPin := by
  intro k _ a M Q hQm hQd hQ hsep
  have key : M.charpoly ∣ Q := by
    rw [← Polynomial.map_dvd_map (algebraMap k (AlgebraicClosure k))
      (algebraMap k (AlgebraicClosure k)).injective M.charpoly_monic]
    rw [← M.charpoly_map]
    have hQ' : aeval (M.map (algebraMap k (AlgebraicClosure k))) Q = 0 := by
      have e : M.map (algebraMap k (AlgebraicClosure k)) =
          (Algebra.ofId k (AlgebraicClosure k)).mapMatrix M := rfl
      rw [e, Polynomial.aeval_algHom_apply, hQ, map_zero]
    have hf : aeval (Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k)))) Q = 0 := by
      have e : Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k))) =
          Matrix.toLinAlgEquiv' (M.map (algebraMap k (AlgebraicClosure k))) := rfl
      rw [e, ← Polynomial.aeval_map_algebraMap (AlgebraicClosure k), Polynomial.aeval_algHom_apply,
        Polynomial.aeval_map_algebraMap, hQ', map_zero]
    have hmon := (M.map (algebraMap k (AlgebraicClosure k))).charpoly_monic
    refine dvd_trans ?_ (prod_multiset_X_sub_C_dvd (Q.map (algebraMap k (AlgebraicClosure k))))
    rw [(IsAlgClosed.splits (M.map (algebraMap k (AlgebraicClosure k))).charpoly).eq_prod_roots_of_monic hmon]
    apply Multiset.prod_dvd_prod_of_le
    apply Multiset.map_le_map
    have hnd : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.roots.Nodup := by
      rw [M.charpoly_map]
      exact nodup_roots hsep.map
    rw [Multiset.le_iff_subset hnd]
    intro μ hμ
    have hroot : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.IsRoot μ :=
      (mem_roots hmon.ne_zero).mp hμ
    rw [← Matrix.charpoly_toLin'] at hroot
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hv' := Module.End.aeval_apply_of_hasEigenvector (p := Q.map (algebraMap k (AlgebraicClosure k))) hv
    rw [Polynomial.aeval_map_algebraMap, hf, LinearMap.zero_apply] at hv'
    have h0 : (Q.map (algebraMap k (AlgebraicClosure k))).eval μ = 0 :=
      (smul_eq_zero.mp hv'.symm).resolve_right hv.2
    rw [mem_roots (Polynomial.map_monic_ne_zero hQm)]
    exact h0
  exact (eq_of_monic_of_dvd_of_natDegree_le M.charpoly_monic hQm key
    (by rw [hQd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])).symm

end UpperTheory.Gal.Int.Div
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSubLoc
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.subLoc_of :
    SubSplit → InFacts → LocConj → LocSum → JumpCard → SubLoc := by
  intro hS hI hC hL _ E Ω _ _ _ _ _ l _ a d r ρ hss hin ι w P AI hT A h O _ _ _ Bw hj
  obtain ⟨had, -, -⟩ := hI _ _ a d r ρ hin
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  obtain ⟨s, g, hg⟩ := hS _ _ a b r ρ hss hin
  have e : (sumRep r s).comp (Dec (F := E) A).subtype =
      sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype) := by
    ext; rfl
  have hiso : RepIso (ρ.comp (Dec (F := E) A).subtype)
      (sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)) := by
    refine ⟨g, fun x => ?_⟩
    rw [← e]
    exact hg x
  have hconj := (hC l P AI hT E Ω A O Bw (a + b) (ρ.comp (Dec (F := E) A).subtype) _).2 hiso
  have hsum := hL l P AI hT E Ω A O Bw a b (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)
  refine ⟨fun hc => ?_, fun τ J J' h1 h2 => hsum.2 τ J J' (hconj.2.2.1 τ J h1) h2⟩
  have hcS := hconj.1 hc
  obtain ⟨cr, cs⟩ := hsum.1 hcS
  refine ⟨cr, fun x => ?_⟩
  have pr := ((hC l P AI hT E Ω A O Bw a _ (r.comp (Dec (F := E) A).subtype)).1 cr).2
  have ps := ((hC l P AI hT E Ω A O Bw b _ (s.comp (Dec (F := E) A).subtype)).1 cs).2
  have pT := ((hC l P AI hT E Ω A O Bw (a + b) _ (ρ.comp (Dec (F := E) A).subtype)).1 hcS).2
  have hw := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l P AI hT ι E Ω A w O Bw h hj a b _ _ pr ps pT
  rw [← hconj.2.2.2 ι w h hj hc, hw, (UpperTheory.Gal.TP.Sub.wDFacts_holds E Ω A w h _ _).2.1 x]
  exact Dvd.intro _ rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSubSplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

noncomputable section

namespace UpperTheory.Gal.Int.Div

section SubSplitAux

variable {Γ k : Type} [Group Γ] [Field k] {n a b : ℕ}

private lemma sumRep_val (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep r s g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      (Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0
        (s g : Matrix (Fin b) (Fin b) k)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl

private def resHom (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') : Γ →* Module.End k W' where
  toFun g := (Matrix.mulVecLin (ρ g : Matrix (Fin n) (Fin n) k)).restrict (hinv g)
  map_one' := by ext x; simp
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (ρ (g * h) : Matrix (Fin n) (Fin n) k).mulVec (x : Fin n → k) =
      (ρ g : Matrix (Fin n) (Fin n) k).mulVec
        ((ρ h : Matrix (Fin n) (Fin n) k).mulVec (x : Fin n → k))
    simp [Matrix.mulVec_mulVec]

private def subRep (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') : Γ →* GL (Fin b) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix c c (resHom ρ hinv g)
      map_one' := by simp [LinearMap.toMatrix_one]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp c c c] }

private lemma subRep_val (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') (g : Γ) :
    ((subRep ρ hinv c g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) =
      LinearMap.toMatrix c c (resHom ρ hinv g) := rfl

private def colM (A : Matrix (Fin n) (Fin a) k) {W' : Submodule k (Fin n → k)}
    (c : Module.Basis (Fin b) k W') : Matrix (Fin n) (Fin a ⊕ Fin b) k :=
  Matrix.of fun i => Sum.elim (fun j => A i j) (fun j => (c j : Fin n → k) i)

private lemma intertw (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') (A : Matrix (Fin n) (Fin a) k)
    (R : Matrix (Fin a) (Fin a) k) (g : Γ)
    (hA : (ρ g : Matrix (Fin n) (Fin n) k) * A = A * R) :
    (ρ g : Matrix (Fin n) (Fin n) k) * colM A c =
      colM A c * Matrix.fromBlocks R 0 0 (subRep ρ hinv c g : Matrix (Fin b) (Fin b) k) := by
  ext i (j | j)
  · have h := congrFun (congrFun hA i) j
    simpa [colM, Matrix.mul_apply, Fintype.sum_sum_type] using h
  · have hs := congrArg (fun v : W' => (v : Fin n → k) i) (c.sum_repr (resHom ρ hinv g (c j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hs
    simp only [colM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, subRep_val, LinearMap.toMatrix_apply]
    refine Eq.trans ?_ (hs.symm.trans ?_)
    · rfl
    · exact Finset.sum_congr rfl fun x _ => mul_comm _ _

private lemma col_indep (A : Matrix (Fin n) (Fin a) k) (hA : A.rank = a)
    {W' : Submodule k (Fin n → k)} (c : Module.Basis (Fin b) k W')
    (hc : IsCompl (LinearMap.range A.mulVecLin) W') :
    LinearIndependent k (Sum.elim A.col (fun j => (c j : Fin n → k))) := by
  apply LinearIndependent.sum_type
  · rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    calc a = A.rank := hA.symm
      _ = _ := by
        rw [Matrix.rank_eq_finrank_span_cols]
        rfl
  · exact c.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  · refine hc.disjoint.mono ?_ ?_
    · rw [Matrix.range_mulVecLin]
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (c j).2

end SubSplitAux

theorem subSplit_of : SubSplit := by
  intro Γ k _ _ a b r ρ hss ⟨A, hA, hAg⟩
  have hinvW : IsInv ρ (LinearMap.range A.mulVecLin) := by
    rintro g _ ⟨u, rfl⟩
    refine ⟨(r g : Matrix (Fin a) (Fin a) k).mulVec u, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAg g]
  obtain ⟨W', hinv, hc⟩ := hss _ hinvW
  have hdim : Module.finrank k W' = b := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    have h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a := hA
    rw [Module.finrank_fin_fun] at h1
    omega
  let c : Module.Basis (Fin b) k W' := Module.finBasisOfFinrankEq k W' hdim
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  let P : Matrix (Fin (a + b)) (Fin (a + b)) k := (colM A c).submatrix id e.symm
  have hP : IsUnit P := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have h := (col_indep A hA c hc).comp e.symm e.symm.injective
    convert h using 1
    ext j i
    rcases h' : e.symm j with j' | j' <;> simp [P, colM, Matrix.col, h'] <;> rfl
  have hinvP : ((hP.unit⁻¹ : GL (Fin (a + b)) k) : Matrix _ _ k) * P = 1 := by
    have h := hP.unit.inv_mul
    rwa [hP.unit_spec] at h
  refine ⟨subRep ρ hinv c, hP.unit⁻¹, fun x => ?_⟩
  have hx : (ρ x : Matrix _ _ k) * P = P * (Matrix.fromBlocks (r x : Matrix (Fin a) (Fin a) k) 0 0
      (subRep ρ hinv c x : Matrix (Fin b) (Fin b) k)).submatrix e.symm e.symm := by
    rw [Matrix.submatrix_mul_equiv, ← intertw ρ hinv c A (r x) x (hAg x)]
    ext i j
    simp [P, Matrix.mul_apply]
  rw [inv_inv]
  apply Units.ext
  rw [sumRep_val, Units.val_mul, Units.val_mul, hP.unit_spec, mul_assoc, hx, ← mul_assoc, hinvP,
    one_mul]

end UpperTheory.Gal.Int.Div

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Div

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cpl (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) := conjSrc (GlobalTheory.SplitPts.conjE E) w


omit [NumberField E] [IsCMField E] in
def SameK (x : E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → (y ∈ w.asIdeal ↔ y ∈ w'.asIdeal)

def CplMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (y y' : 𝓞 E),
    (y' : E) = IsCMField.complexConj E (y : E) → (y ∈ (cpl w).asIdeal ↔ y' ∈ w.asIdeal)

def SameOr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l d : ℕ), l.Prime → 0 < d → ∀ x : E, x ^ 2 = -(d : E) →
    ∀ w w' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ((l : ℕ) : 𝓞 E) ∈ w'.asIdeal → SameK x w w' ∨ SameK x (cpl w) w'

def LocIso : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
    locU (E := E) a (cpl w) = locU a w ∧
    ∃ β : GL (Fin a) ((cpl w).adicCompletion E) ≃ₜ* GL (Fin a) (w.adicCompletion E),
      (∀ x : UA E a, β (cLoc (cpl w) x) = cLoc w x) ∧ (∀ g, g ∈ GlobalTheory.LFun.KGL (cpl w) (n := a) → β g ∈ GlobalTheory.LFun.KGL w (n := a)) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V),
        GlobalTheory.SmGL.IsCuspidal σ → GlobalTheory.SmGL.IsCuspidal (σ.comp β.toMulEquiv.toMonoidHom)

def SatConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w →
      (∃ B, UpperTheory.Gal.TP.Sub.SatU U w B) → ∃ B, UpperTheory.Gal.TP.Sub.SatU U (cpl w) B

def TyConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ) (U : Submodule ℂ (UA E a → ℂ))
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → GlobalTheory.CongW.TyEll E l a w U → GlobalTheory.CongW.TyEll E l a (cpl w) U

def LacConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (U : Submodule ℂ (UA E a → ℂ)) (v : HeightOneSpectrum (𝓞 E)), LacWtAt ι v U → LacWtAt ι (cpl v) U

def GapLac : Prop := ∀ (a : ℕ) (J : Finset ℤ), J.card = a → GapJ a J.val → Lacunary J

end UpperTheory.Gal.Int.Div

end
end

