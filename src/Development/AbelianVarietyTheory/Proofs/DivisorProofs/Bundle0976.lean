module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HeckeP

theorem mem_range_map_subtype {B : Type} [CommRing B] (R : Subring B) {n : ℕ} (g : GL (Fin n) B) :
    g ∈ (GeneralLinearGroup.map R.subtype).range ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) B) i j ∈ R) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((h : Matrix (Fin n) (Fin n) R) i j).2
    · rw [← map_inv]; exact ((h⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) R => X.map R.subtype) :=
      fun X Y e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
    have hM : M.map R.subtype = (g : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
    have hM' : M'.map R.subtype = ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
    have e1 : M * M' = 1 := hinj (by
      show (M * M').map R.subtype = (1 : Matrix (Fin n) (Fin n) R).map R.subtype
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have e2 : M' * M = 1 := hinj (by
      show (M' * M).map R.subtype = (1 : Matrix (Fin n) (Fin n) R).map R.subtype
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    exact ⟨⟨M, M', e1, e2⟩, Units.ext hM⟩

variable (p : ℕ) [Fact p.Prime]

theorem inclK_mem_intKQ_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (a : K) :
    inclK p K r a ∈ intKQ p K r ↔ a ∈ GlobalTheory.LKLoc.intK p K := by
  constructor
  · intro h
    have h1 := GlobalTheory.LKRes.Model.mulMap_intKQ p K r _ h
    have h2 : GlobalTheory.LKRes.Model.mulMap p K r (inclK p K r a) = (a : PadicAlgCl p) := by
      show (a : PadicAlgCl p) * 1 = _
      rw [mul_one]
    rw [h2] at h1
    exact (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 h1
  · intro h
    exact Subring.subset_closure (Or.inl ⟨⟨a, h⟩, rfl⟩)

theorem map_inclK_mem_Kres_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (g : GL (Fin n) K) :
    GeneralLinearGroup.map (inclK p K r).toRingHom g ∈ Kres p K n r ↔ g ∈ GlobalTheory.LKLoc.KintK p K n := by
  unfold Kres GlobalTheory.LKLoc.KintK
  rw [mem_range_map_subtype, mem_range_map_subtype, ← map_inv]
  simp only [GeneralLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, RingHom.mapMatrix_apply]
  simp [Matrix.map_apply, inclK_mem_intKQ_iff]

theorem scalar_mem_Kint_iff (r : ℕ) (s : ℚ_[p]ˣ) :
    (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom s) ∈
        GlobalTheory.LKLoc.Kint p (Q0 p) 1 r ↔ ‖(s : ℚ_[p])‖ ≤ 1 ∧ ‖((s⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := by
  unfold GlobalTheory.LKLoc.Kint
  rw [mem_range_map_subtype, ← map_inv, ← map_inv]
  have key : ∀ t : ℚ_[p], algebraMap ℚ_[p] (Qr p r) t ∈ GlobalTheory.LKLoc.intR p (Q0 p) r ↔ ‖t‖ ≤ 1 := by
    intro t
    rw [GlobalTheory.LKLoc.intR, Subring.mem_comap, ValuationSubring.mem_toSubring, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff,
      ← IsScalarTower.algebraMap_apply, PadicAlgCl.norm_extends]
  have key' : ∀ t : ℚ_[p], (algebraMap ℚ_[p] (Qr p r) t)⁻¹ ∈ GlobalTheory.LKLoc.intR p (Q0 p) r ↔ ‖t‖⁻¹ ≤ 1 := by
    intro t; rw [← map_inv₀, key, norm_inv]
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, key, key']

theorem inclG_mem_KHT_iff (G : HTGroup p) (r : ℕ) (x : Gp G) :
    inclG G r x ∈ KHT p G.m G.n r G.Fw ↔
      (‖(x.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((x.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ∧
        ∀ w, x.2 w ∈ GlobalTheory.LKLoc.KintK p (G.Fw w) G.n := by
  unfold KHT
  rw [Subgroup.mem_prod, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]
  have h1 : (inclG G r x).1 =
      (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom x.1) := rfl
  have h2 : ∀ w, (inclG G r x).2 w = GeneralLinearGroup.map (inclK p (G.Fw w) r).toRingHom (x.2 w) :=
    fun w => rfl
  rw [h1, scalar_mem_Kint_iff]
  simp only [h2, map_inclK_mem_Kres_iff]

theorem gl_one_map_conj {R : Type} [CommRing R] (H : Subgroup (GL (Fin 1) R)) (g : GL (Fin 1) R) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  have hc : ∀ a b : GL (Fin 1) R, a * b = b * a := fun a b => by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have : (MulAut.conj g).toMonoidHom = MonoidHom.id _ := MonoidHom.ext fun x => by
    show g * x * g⁻¹ = x
    rw [hc g x, mul_inv_cancel_right]
  rw [this, Subgroup.map_id]

theorem Kres_commensurable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    Subgroup.Commensurable ((Kres p K n r).map (MulAut.conj g).toMonoidHom) (Kres p K n r) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  have mono : ∀ (x : KQ p K r) (k l : ℕ), k ≤ l → (p : KQ p K r) ^ k * x ∈ intKQ p K r →
      (p : KQ p K r) ^ l * x ∈ intKQ p K r := by
    intro x k l hkl h
    rw [← Nat.add_sub_cancel' hkl, pow_add, mul_comm ((p : KQ p K r) ^ k), mul_assoc]
    exact mul_mem (pow_mem (natCast_mem _ p) _) h
  choose f hf using GlobalTheory.T.exists_padic_pow_mul_mem_tensorUnramifiedIntegers p K r
  let k : ℕ := (Finset.univ.sup fun ij : Fin n × Fin n => f ((g : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) ⊔
    Finset.univ.sup fun ij : Fin n × Fin n => f (((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)
  have hk1 : ∀ i j, (p : KQ p K r) ^ k * (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r :=
    fun i j => mono _ _ _ (le_sup_left.trans' (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      f ((g : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) (Finset.mem_univ (i, j)))) (hf _)
  have hk2 : ∀ i j, (p : KQ p K r) ^ k *
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r :=
    fun i j => mono _ _ _ (le_sup_right.trans' (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      f (((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) (Finset.mem_univ (i, j)))) (hf _)
  let c : intKQ p K r := (p : intKQ p K r) ^ k
  have hc : (c : KQ p K r) = (p : KQ p K r) ^ k := by simp [c]
  have hfin : Finite (intKQ p K r ⧸ Ideal.span {c * c}) := by
    have h := GlobalTheory.T.finite_padicTensorUnramifiedIntegers_quot_primePow p K r (2 * k) (GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim p K (2 * k)) (GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim p (Qr p r) (2 * k))
    have e : c * c = (p : intKQ p K r) ^ (2 * k) := by simp only [c]; ring
    rw [e]; exact h
  exact GlobalTheory.T.commensurable_conj_range_gl_map_subtype (intKQ p K r) n c hfin g (fun i j => by rw [hc]; exact hk1 i j)
    (fun i j => by rw [hc]; exact hk2 i j)

end GlobalTheory.HeckeP


open GlobalTheory.HeckeP in
theorem GlobalTheory.heckeOperator_integral :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
      (∀ g : Gr G r, Subgroup.Commensurable ((KHT p G.m G.n r G.Fw).map (MulAut.conj g).toMonoidHom)
        (KHT p G.m G.n r G.Fw)) ∧
      (KHT p G.m G.n r G.Fw).comap (inclG G r) = Kp0 G ∧
      (KHT p G.m G.n r G.Fw).map (sigG G r) ≤ KHT p G.m G.n r G.Fw := by
  intro p _ G r hr
  refine ⟨fun g => ?_, ?_, ?_⟩
  · unfold KHT
    exact GlobalTheory.T.commensurable_map_conj_prod_pi' _ _ g (by rw [gl_one_map_conj])
      (fun i => Kres_commensurable p (G.Fw i) G.n r hr (g.2 i))
  · ext x
    rw [Subgroup.mem_comap, Kp0, Subgroup.mem_comap, inclG_mem_KHT_iff, inclG_mem_KHT_iff]
  · rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.LKRes.Model.sigHT_KHT p _ _ _ _ x hx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem conj_rel_alg' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β e e' : G.Cˣ) (a' : G.C) (r r' : ℚˣ) :
    algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) =
      algebraMap ℚ G.C ((r : ℚ) / r') * (((e * e'⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (r' : ℚ) *
        ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))) *
        ((β : G.C) * sh G ((e * e'⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  have hsh : sh G ((e * e'⁻¹ : G.Cˣ) : G.C) = sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C) := by
    simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
  have h1 : sh G (e' : G.C) * sh G ((e'⁻¹ : G.Cˣ) : G.C) = 1 := by
    simp only [sh]
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hrr : (r' : ℚ) * ((r : ℚ) / r') = r := by field_simp
  have key2 : ((e : G.C) * ((e'⁻¹ : G.Cˣ) : G.C)) * ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) *
      ((β : G.C) * (sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C)) * ((β⁻¹ : G.Cˣ) : G.C)) =
      (e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    simp only [mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul_cancel_left, ← mul_assoc (sh G (e' : G.C)), h1, one_mul]
  rw [hsh, Units.val_mul]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, hrr]
  rw [key2]

theorem commute_of_commute_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (y₀ : G.C)
    (hsep : (minpoly G.F y₀).Separable) (hdeg : (minpoly G.F y₀).natDegree = G.n) (a b : G.C)
    (ha : Commute a y₀) (hb : Commute b y₀) : Commute a b := by
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hamem : a ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact ha.eq.symm
  have hbmem : b ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hb.eq.symm
  rw [hc] at hamem
  have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({y₀} : Set G.C) hamem
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 b hbmem).symm

theorem units_conj_of_minpoly_eq_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ)
    (hab : minpoly G.F (a : G.C) = minpoly G.F (b : G.C)) (hsep : (minpoly G.F (b : G.C)).Separable)
    (hdeg : (minpoly G.F (b : G.C)).natDegree = G.n) : ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  haveI : Infinite G.F := Infinite.of_injective (Nat.cast : ℕ → G.F) Nat.cast_injective
  obtain ⟨g, hg⟩ := GlobalTheory.LKInv.exists_unit_conj_of_minpoly_eq G.F G.C G.n G.rankC (b : G.C) (a : G.C) hsep hdeg hab
  refine ⟨g, ?_⟩
  rw [hg, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.LKCx.ClsReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
section
noncomputable section

namespace GlobalTheory.ChrWUnif

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

theorem valued_unifAt (v : Pl F) : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have hu : valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπv : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    e.lt_one_iff_lt_one.1 (hu ▸ uniformizer_lt_one)
  have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
  have hle1 : valuation (Fv F v) ((π : F) : Fv F v) ≤ valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) := by
    rw [hu, le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) := hπv ▸ (e _ _).1 hle1
  rw [← WithZero.exp_log h0] at hlt hge ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hge
  congr 1
  omega

theorem chrW_unifAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E)
    (v : Pl F) (t : E →ₐ[F] Fv F v) (h : UnrAt χ (splitPrime t)) : chrW χ t (unifAt v) = val χ (splitPrime t) := by
  refine h.locChar_eq_val ?_
  show Valued.v (complMap (splitPrime_under t) ((unifAt v : (Fv F v)ˣ) : Fv F v)) = WithZero.exp (-1 : ℤ)
  rw [GlobalTheory.LFun.SplitTie.valued_complMap t (splitPrime_under t), valued_unifAt]

end GlobalTheory.ChrWUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqHolomorphicLowestKTypeSubRootLt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.VoganRoot

open Finset Formalism.REAL

theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  have h1 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      = n - 1 - a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h2 : (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have ha := a.2
  have h3 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      + a + 1 = n := by omega
  have h3' := congrArg (Nat.cast : ℕ → ℝ) h3
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  push_cast at h3' h2'
  unfold Formalism.REAL.rhoN Formalism.REAL.rhoC
  linarith

theorem nsq_sub_root {n : ℕ} (u : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    Formalism.REAL.nsq (u - Formalism.REAL.root a b) = Formalism.REAL.nsq u - 2 * (u a - u b) + 2 := by
  have : ∀ i, (u - Formalism.REAL.root a b) i * (u - Formalism.REAL.root a b) i =
      u i * u i - 2 * ((if i = a then u i else 0) - (if i = b then u i else 0)) +
        ((if i = a then 1 else 0) + (if i = b then 1 else 0)) := by
    intro i
    simp only [Formalism.REAL.root, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [h1, h2, hab, hab.symm]
    all_goals ring
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  norm_num

theorem vNormSq_lowK_sub_root_lt {n : ℕ} (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : StrictAnti μ)
    {a b : Fin n} (hab : a < b) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b) < Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ) := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [show Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b + (2 : ℝ) • Formalism.REAL.rhoC ε
      = (Formalism.QuantumDeterminants.lowK ε μ + (2 : ℝ) • Formalism.REAL.rhoC ε) - Formalism.REAL.root a b by abel,
    nsq_sub_root _ hab.ne]
  have h1 := hμ hab
  have h2 := rhoN_add_rhoC ε a
  have h3 := rhoN_add_rhoC ε b
  have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

end GlobalTheory.HolDict.VoganRoot

theorem GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → ∀ a c : Fin n, ε a = true → ε c = false → vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam - Formalism.REAL.root a c) < vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  intro n p ε lam hl hε a c ha hc
  rw [hε] at ha hc
  have hac : a < c := by
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ha hc
    exact Fin.lt_def.mpr (by omega)
  exact GlobalTheory.HolDict.VoganRoot.vNormSq_lowK_sub_root_lt ε hl.1 hac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WatIffType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WatType

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_lift (R : RealDat D A Ks) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (hinj : Function.Injective (R.HW i σ).e) {x : (R.HW i σ).H} (hx : x ≠ 0) (g : G) :
    ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : R.gW i σ g x = 0 := by
    apply hinj
    rw [hg i σ g x, map_zero]
    ext v h
    show actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dite_eq_right hk]
    rfl
  have : R.gW i σ g⁻¹ (R.gW i σ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h0, map_zero]

theorem mem_wat_iff (R : RealDat D A Ks) (F : Face D A) (hg : R.models_gW) (hW : R.models_HW) (b : Bool) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e x ∈ R.Wat i σ (R.levL F b σ) ↔
      (∀ p : (F.lvl b).P, postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG p)) ((R.HW i σ).e x) =
        σ ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • (R.HW i σ).e x) ∧
      ∑ g, σ ((idemOf A.X).coeff g) • postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x) =
        (R.HW i σ).e x := by
  have hx : (R.HW i σ).e x ∈ R.Wall i σ := (hW i σ).2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.Wall at hx
  unfold RealDat.Wat
  rw [mem_goodPart]
  rw [GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  refine and_congr ?_ ?_
  · constructor
    · intro h1 g
      by_cases h0 : x = 0
      · simp [h0]
      ext v h
      have hmem : R.eG g ∈ (R.levL F b σ).H := by
        show R.eG.symm (R.eG g) ∈ (F.lvl b).P
        rw [MulEquiv.symm_apply_apply]; exact g.2
      have h2 := GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) (P := R.levL F b σ)
        (F := (R.HW i σ).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift R hg i σ (hW i σ).1 h0 g)
      have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
        Subtype.ext (R.eG.symm_apply_apply g)
      refine (congrFun h2 h).trans ?_
      show σ (((F.lvl b).ψ⁻¹ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
      rw [h3]
      rfl
    · intro h
      refine ⟨hx.aut, hx.cusp, fun v => ?_, hx.equiv, hx.cont⟩
      have hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F b σ) ((R.HW i σ).e x v) := by
        refine ⟨fun κ hκ y => hx.lev v κ hκ y, fun p => ?_⟩
        have h1 := congrArg (fun z : MMap (R.MW i σ) => z v) (h ⟨R.eG.symm p.1, p.2⟩)
        have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
        simp only [h2] at h1
        exact h1
      exact fun κ hκ y => hP.hasType κ hκ y
  · have h3 : ∀ v, R.eWf i σ ((R.HW i σ).e x v) = (∑ g, σ ((idemOf A.X).coeff g) •
        postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x)) v := by
      intro v
      simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
        MultilinearMap.smul_apply, postOn_apply]
      rfl
    simp only [h3]
    exact ⟨fun h => MultilinearMap.ext h, fun h v => by rw [h]⟩

theorem wat_iff_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ (b : Bool) i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ↔ (eH R i x = x ∧ ∀ p : (F.lvl b).P, R.gW i (sg0 D A) p x = sg0 D A ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ hC b i x
  have hW := hC.models.HW
  have hg := hC.models.gW
  have hinj := (hW i (sg0 D A)).1
  rw [mem_wat_iff R F hg hW, and_comm]
  refine and_congr ?_ (forall_congr' fun p => ?_)
  · rw [← hinj.eq_iff]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [eH, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hg i _ _ x]
  · rw [← hinj.eq_iff, hg, map_smul]

end GlobalTheory.WatType

end
end

