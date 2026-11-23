module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterTrivialAtWildOfCoprimePow
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.WildChar

theorem val_natCast_not_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l p : ℕ}
    (hcop : Nat.Coprime l p) (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (l : Ω) < 1 := by
  intro hl
  have e : ((l : ℤ) * l.gcdA p + (p : ℤ) * l.gcdB p : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab l p
    rw [hcop.gcd_eq_one] at this
    push_cast at this
    exact this.symm
  have e' : (l : Ω) * (l.gcdA p : Ω) + (p : Ω) * (l.gcdB p : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) e
    push_cast at this
    exact this
  have ha : A.valuation (l.gcdA p : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have hb : A.valuation (l.gcdB p : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have h1 : A.valuation ((l : Ω) * (l.gcdA p : Ω) + (p : Ω) * (l.gcdB p : Ω)) < 1 := by
    refine lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact (mul_le_of_le_one_right' ha).trans_lt hl
    · rw [map_mul]; exact (mul_le_of_le_one_right' hb).trans_lt hp
  rw [e', map_one] at h1
  exact lt_irrefl _ h1

theorem sub_lt_of_wild {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (τ : Gal(Ω/F)) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) (y : Ω) (hy : y ≠ 0) :
    A.valuation (τ y - y) < A.valuation y := by
  have hv : A.valuation y ≠ 0 := by simpa using hy
  have h := hτ y hy
  have e : τ y / y - 1 = (τ y - y) / y := by field_simp
  rw [e, map_div₀] at h
  have hpos : 0 < A.valuation y := zero_lt_iff.mpr hv
  calc A.valuation (τ y - y) = A.valuation (τ y - y) / A.valuation y * A.valuation y := by
        rw [div_mul_cancel₀ _ hv]
    _ < 1 * A.valuation y := by
        exact mul_lt_mul_of_pos_right h hpos
    _ = A.valuation y := one_mul _

theorem pow_sub_lt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (τ : Gal(Ω/F)) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) (y : Ω) (hy : y ≠ 0) :
    ∀ i : ℕ, A.valuation ((τ ^ i) y - y) < A.valuation y := by
  have hv : A.valuation y ≠ 0 := by simpa using hy
  intro i
  induction i with
  | zero => simpa using zero_lt_iff.mpr hv
  | succ i ih =>
    have hne : (τ ^ i) y ≠ 0 := fun h0 => hy ((τ ^ i).injective (h0.trans (map_zero _).symm))
    have heq : A.valuation ((τ ^ i) y) = A.valuation y := Valuation.map_eq_of_sub_lt _ ih
    have h1 := sub_lt_of_wild A τ hτ _ hne
    rw [heq] at h1
    have e : (τ ^ (i + 1)) y - y = (τ ((τ ^ i) y) - (τ ^ i) y) + ((τ ^ i) y - y) := by
      rw [pow_succ', AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt h1 ih)

theorem fix_of_pow_fix {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (p : ℕ)
    (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1)
    (τ : Gal(Ω/F)) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1)
    (n : ℕ) (hn : Nat.Coprime n p) (y : Ω) (hy : (τ ^ n) y = y) : τ y = y := by
  by_contra hne
  set e := τ y - y with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr hne
  have hsum : ∑ i ∈ Finset.range n, (τ ^ i) e = 0 := by
    have : ∀ i, (τ ^ i) e = (τ ^ (i + 1)) y - (τ ^ i) y := by
      intro i; rw [he, map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (τ ^ i) y) n, hy]; simp
  have hsplit : ∑ i ∈ Finset.range n, (τ ^ i) e =
      (n : Ω) * e + ∑ i ∈ Finset.range n, ((τ ^ i) e - e) := by
    rw [Finset.sum_sub_distrib]; simp
  have hlt : A.valuation (∑ i ∈ Finset.range n, ((τ ^ i) e - e)) < A.valuation e :=
    Valuation.map_sum_lt _ (by simpa using he0) (fun i _ => pow_sub_lt A τ hτ e he0 i)
  have hn1 : A.valuation (n : Ω) = 1 := by
    have hle : A.valuation (n : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A _)
    exact le_antisymm hle (not_lt.mp (val_natCast_not_lt A hn hp))
  have key : (n : Ω) * e = - ∑ i ∈ Finset.range n, ((τ ^ i) e - e) := by
    rw [hsplit] at hsum; linear_combination hsum
  have := congrArg A.valuation key
  rw [map_mul, hn1, one_mul, Valuation.map_neg] at this
  rw [this] at hlt
  exact lt_irrefl _ hlt

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∀ (R : Type) [CommRing R] (χ : G F Ω →* Rˣ), IsOpen (χ.ker : Set (G F Ω)) →
    ∀ σ : G F Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) →
    ∀ m : ℕ, 0 < m → Nat.Coprime m p → χ σ ^ m = 1 → χ σ = 1 := by
  intro F Ω _ _ _ _ _ p hpr A hp R _ χ hK σ hσ m _ hmp hχm
  have : Normal F Ω := IsAlgClosure.normal F Ω
  obtain ⟨E, hfin, hnorm, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F Ω _).mp (hK.mem_nhds χ.ker.one_mem)
  set k := orderOf (AlgEquiv.restrictNormalHom E σ) with hk
  have hk0 : k ≠ 0 := (orderOf_pos _).ne'
  have hfixE : ∀ τ : Gal(Ω/F), AlgEquiv.restrictNormalHom E τ = 1 → ∀ a ∈ E, τ a = a := by
    intro τ h1 a ha
    have := AlgEquiv.restrictNormal_commutes τ E ⟨a, ha⟩
    have h2 : (AlgEquiv.restrictNormal τ E) ⟨a, ha⟩ = ⟨a, ha⟩ := by
      have h3 : AlgEquiv.restrictNormalHom E τ = AlgEquiv.restrictNormal τ E := rfl
      rw [← h3, h1]; rfl
    rw [h2] at this
    exact this.symm
  have hσk : ∀ a ∈ E, (σ ^ k) a = a := by
    apply hfixE
    rw [map_pow, hk, pow_orderOf_eq_one]
  set a := k.factorization p
  set n := k / p ^ a
  have hkan : p ^ a * n = k := Nat.ordProj_mul_ordCompl_eq_self k p
  have hnp : Nat.Coprime n p := (Nat.coprime_ordCompl hpr.out hk0).symm
  set τ := σ ^ (p ^ a)
  have hτw : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
    intro y hy
    have hv : A.valuation y ≠ 0 := by simpa using hy
    have h := pow_sub_lt A σ hσ y hy (p ^ a)
    have e : τ y / y - 1 = (τ y - y) / y := by field_simp
    rw [e, map_div₀]
    exact (div_lt_one₀ (zero_lt_iff.mpr hv)).mpr h
  have hτE : τ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro b hb
    apply fix_of_pow_fix p A hp τ hτw n hnp b
    rw [← pow_mul, hkan]
    exact hσk b hb
  have h1 : χ σ ^ (p ^ a) = 1 := by rw [← map_pow]; exact MonoidHom.mem_ker.mp (hE hτE)
  have hcop : Nat.Coprime m (p ^ a) := Nat.Coprime.pow_right _ hmp
  have h3 : χ σ ^ Nat.gcd m (p ^ a) = 1 := pow_gcd_eq_one.mpr ⟨hχm, h1⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

end GlobalTheory.WildChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyEqRankPartMul
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.CharpolyFrobDense

def CoeffCont {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K] (F : Γ → K[X]) : Prop :=
  ∀ k, Continuous fun g => (F g).coeff k

theorem CoeffCont.mul {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {F F' : Γ → K[X]} (h : CoeffCont F) (h' : CoeffCont F') :
    CoeffCont (F * F') := by
  intro k
  simp only [Pi.mul_apply, coeff_mul]
  exact continuous_finsetSum _ fun x _ => (h x.1).mul (h' x.2)

theorem coeffCont_one {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K] :
    CoeffCont (1 : Γ → K[X]) := fun _ => continuous_const

theorem coeffCont_X_sub_C {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {a : Γ → K} (ha : Continuous a) :
    CoeffCont fun g => (X - C (a g)) := by
  intro k
  rcases k with _ | _ | k
  · simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
    exact ha.neg
  · simpa using continuous_const
  · simp only [coeff_sub, coeff_X, coeff_C]
    simpa using continuous_const

theorem coeffCont_prod {Γ K ι : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (s : Finset ι) (F : ι → Γ → K[X]) (h : ∀ c ∈ s, CoeffCont (F c)) :
    CoeffCont fun g => ∏ c ∈ s, F c g := by
  have : (fun g => ∏ c ∈ s, F c g) = ∏ c ∈ s, F c := by
    funext g; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (fun G => CoeffCont G) (fun _ _ ha hb => ha.mul hb) coeffCont_one h

end GlobalTheory.CharpolyFrobDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefActionReprMemSubfield
section
open Formalism.L2.DIV Formalism.BasicNotions NumberField

namespace GlobalTheory

open NumberField in
private lemma blockAct_map_mem_range_map_of_entries_mem {K : Type} [Field K] (K₀ : Subfield K) {ι : Type} [Fintype ι] {n : ℕ}
    (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ K₀)
    (P : MvPolynomial (ι × Fin n × Fin n) K₀) :
    _root_.Formalism.GradedWeylDivisibility.blockAct K U (MvPolynomial.map K₀.subtype P) ∈ (MvPolynomial.map K₀.subtype).range := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C a, ?_⟩
    rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul, map_mul, MvPolynomial.map_X, _root_.Formalism.L2.DIV.blockAct_X]
    refine mul_mem hp (sum_mem fun b _ => mul_mem ?_ ?_)
    · exact ⟨MvPolynomial.C ⟨U v.1 v.2.1 b, hU _ _ _⟩, by simp⟩
    · exact ⟨MvPolynomial.X (v.1, b, v.2.2), by simp⟩

open NumberField in
private lemma actP_mem_range_map_of_entries_mem {K : Type} [Field K] (K₀ : Subfield K) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (g : ι → GL (Fin n) K)
    (hg : ∀ τ a b, (g τ : Matrix (Fin n) (Fin n) K) a b ∈ K₀)
    {F : _root_.Formalism.L2.DIV.Pol K ι n} (hF : F ∈ (MvPolynomial.map K₀.subtype).range) :
    _root_.Formalism.L2.DIV.actP lam g F ∈ (MvPolynomial.map K₀.subtype).range := by
  obtain ⟨P, rfl⟩ := hF
  have hdet : ∀ τ, (g τ : Matrix (Fin n) (Fin n) K).det ∈ K₀ := by
    intro τ
    have hM : (g τ : Matrix (Fin n) (Fin n) K) =
        (Matrix.of fun a b => (⟨(g τ : Matrix _ _ K) a b, hg τ a b⟩ : K₀)).map K₀.subtype := by
      ext a b; rfl
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact SetLike.coe_mem _
  have hd : _root_.Formalism.L2.DIV.detTwK lam g ∈ K₀ := by
    rw [_root_.Formalism.L2.DIV.detTw_eq]
    exact prod_mem fun τ _ => by
      first | exact pow_mem (hdet τ) _ | exact zpow_mem (hdet τ) _
  unfold _root_.Formalism.L2.DIV.actP _root_.Formalism.L2.DIV.trAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul]
  refine mul_mem ⟨MvPolynomial.C ⟨_, hd⟩, by simp⟩ (blockAct_map_mem_range_map_of_entries_mem K₀ _ ?_ P)
  intro τ a b
  exact hg τ b a


open NumberField in
theorem _root_.GlobalTheory.coefAction_repr_mem_subfield : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (K₀ : Subfield K) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n), (∀ τ x, emb τ x ∈ K₀) → ∀ (g : GL (Fin n) E) i j, (_root_.Formalism.L2.DIV.bVV K lam).repr (_root_.Formalism.L2.DIV.rhoV emb lam g (_root_.Formalism.L2.DIV.bVV K lam j)) i ∈ K₀ ∧ (_root_.Formalism.L2.DIV.bVV K lam).repr (_root_.Formalism.L2.DIV.rhoVr emb lam g (_root_.Formalism.L2.DIV.bVV K lam j)) i ∈ K₀ := by
  intro E K ι _ _ _ _ _ n emb K₀ lam hemb γ i j
  classical
  have hbase : ∀ l, _root_.Formalism.L2.DIV.bVVfun K lam l ∈ (MvPolynomial.map K₀.subtype).range := by
    intro l
    obtain ⟨P, hP⟩ := _root_.Formalism.L2.DIV.bVVfun_int K lam l
    rw [hP]
    exact _root_.Formalism.L2.DIV.fk_int_mem K₀ P
  have key : ∀ x : _root_.Formalism.L2.DIV.VV K lam, (x : _root_.Formalism.L2.DIV.Pol K ι n) ∈ (MvPolynomial.map K₀.subtype).range →
      (_root_.Formalism.L2.DIV.bVV K lam).repr x i ∈ K₀ := by
    intro x hx
    refine _root_.Formalism.L2.DIV.fk_descent K₀ (_root_.Formalism.L2.DIV.bVVfun K lam) (_root_.Formalism.L2.DIV.bVVfun_spec K lam).1 hbase (fun l => (_root_.Formalism.L2.DIV.bVV K lam).repr x l) ?_ i
    have hs := congrArg Subtype.val ((_root_.Formalism.L2.DIV.bVV K lam).sum_repr x)
    rw [Submodule.coe_sum] at hs
    simp only [Submodule.coe_smul, _root_.Formalism.L2.DIV.bVV_coe] at hs
    rw [hs]
    exact hx
  have hj : ((_root_.Formalism.L2.DIV.bVV K lam j : _root_.Formalism.L2.DIV.VV K lam) : _root_.Formalism.L2.DIV.Pol K ι n) ∈
      (MvPolynomial.map K₀.subtype).range := by
    rw [_root_.Formalism.L2.DIV.bVV_coe]; exact hbase j
  constructor
  · apply key
    unfold _root_.Formalism.L2.DIV.rhoV
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.rhoK_coe]
    refine actP_mem_range_map_of_entries_mem K₀ lam _ ?_ hj
    intro τ a b
    rw [_root_.Formalism.L2.DIV.embGL_coe]
    exact hemb τ _
  · apply key
    unfold _root_.Formalism.L2.DIV.rhoVr
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.rhoK_coe]
    refine actP_mem_range_map_of_entries_mem K₀ lam _ ?_ hj
    intro τ a b
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.invTrK_coe, _root_.Formalism.L2.DIV.embGL_inv, _root_.Formalism.L2.DIV.embGL_coe]
    exact hemb τ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

namespace GlobalTheory.Pst.DmapNonzero

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem tensV_eq_rTensor {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.Pst.DmapNonzero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompEq
section
namespace GlobalTheory.AbsolutelyIrreduciblePullback

open Formalism.MainNotions.N

def pullSub {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (W : Submodule L (Fin n → L)) : Submodule K (Fin n → K) where
  carrier := {v | f ∘ v ∈ W}
  add_mem' := by
    intro a b ha hb
    have : f ∘ (a + b) = f ∘ a + f ∘ b := by
      funext i; simp
    show f ∘ (a + b) ∈ W
    rw [this]
    exact W.add_mem ha hb
  zero_mem' := by
    have : f ∘ (0 : Fin n → K) = 0 := by
      funext i; simp
    show f ∘ (0 : Fin n → K) ∈ W
    rw [this]
    exact W.zero_mem
  smul_mem' := by
    intro c v hv
    have : f ∘ (c • v) = f c • (f ∘ v) := by
      funext i; simp
    show f ∘ (c • v) ∈ W
    rw [this]
    exact W.smul_mem _ hv

theorem mem_pullSub {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (W : Submodule L (Fin n → L)) (v : Fin n → K) : v ∈ pullSub f W ↔ f ∘ v ∈ W := by
  exact Iff.rfl

theorem exists_comp_eq {K L : Type} [Field K] [Field L] (f : K →+* L) (hf : Function.Surjective f)
    {n : ℕ} (w : Fin n → L) : ∃ v : Fin n → K, f ∘ v = w := by
  choose v hv using fun i => hf (w i)
  exact ⟨v, funext hv⟩

theorem isInv_pullSub {Γ : Type} [Group Γ] {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (ρ : Γ →* GL (Fin n) K) (W : Submodule L (Fin n → L)) (hW : IsInv (mapRep f ρ) W) :
    IsInv ρ (pullSub f W) := by
  intro g v hv
  rw [mem_pullSub] at hv ⊢
  have heq : f ∘ ((ρ g : Matrix (Fin n) (Fin n) K).mulVec v) =
      ((mapRep f ρ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec (f ∘ v) := by
    funext i
    exact RingHom.map_mulVec f _ v i
  rw [heq]
  exact hW g (f ∘ v) hv

theorem absIrrSub_top {Γ : Type} [Group Γ] {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (hn : 1 ≤ n) (ρ : Γ →* GL (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), IsInv ρ W → W = ⊥ ∨ W = ⊤) : AbsIrrSub ρ ⊤ := by
  have hsurj : Function.Surjective (algebraMap K (AlgebraicClosure K)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := AlgebraicClosure K)).2
  have hspan : Submodule.span (AlgebraicClosure K)
      ((fun v => (algebraMap K (AlgebraicClosure K)) ∘ v) '' ((⊤ : Submodule K (Fin n → K)) : Set (Fin n → K))) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
    exact Submodule.subset_span ⟨v, Submodule.mem_top, rfl⟩
  unfold AbsIrrSub IsIrrSub
  rw [hspan]
  refine ⟨?_, fun _ _ _ => trivial, ?_⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact top_ne_bot
  · intro W' _ hW'
    rcases h _ (isInv_pullSub (algebraMap K (AlgebraicClosure K)) ρ W' hW') with h0 | h1
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
      have hv : v ∈ pullSub (algebraMap K (AlgebraicClosure K)) W' := (mem_pullSub _ _ _).mpr hw
      rw [h0, Submodule.mem_bot] at hv
      subst hv
      rw [Submodule.mem_bot]
      funext i
      simp
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
      have hv : v ∈ pullSub (algebraMap K (AlgebraicClosure K)) W' := by
        rw [h1]
        trivial
      exact (mem_pullSub _ _ _).mp hv

end GlobalTheory.AbsolutelyIrreduciblePullback
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWild
section
noncomputable section

namespace GlobalTheory.TameRel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem wild_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {s u : G E Ω} (hs : s ∈ Dec (F := E) A)
    (hu : ∀ y : Ω, y ≠ 0 → A.valuation (u y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A.valuation ((s * u * s⁻¹) y / y - 1) < 1 := by
  intro y hy
  set z := (s⁻¹ : G E Ω) y with hz
  have hsz : s z = y := mul_inv_apply y
  have hz0 : z ≠ 0 := by
    intro h; apply hy; rw [← hsz, h, map_zero]
  have e : (s * u * s⁻¹) y / y - 1 = s (u z / z - 1) := by
    rw [map_sub, map_div₀, map_one, hsz]
    rfl
  rw [e, GlobalTheory.TameLabels.valuation_apply_of_mem_Dec hs]
  exact hu z hz0

end GlobalTheory.TameRel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.TameRel.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (k : Fin 2) (v : N.PlG k), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), ∃ φ : G H.E N.Om, φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)) ∧ φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ wildSet N (N.plOm.1 (A.plGw k v)) := by
  intro R H what₂ N A k v γ hγ
  obtain ⟨φ, hφ⟩ := exists_isFrob (N.plOm.2 (A.plGw k v))
  rw [GlobalTheory.TameLabels.normV_eq_of_split (H.g_prime k) (N.g_split k) (A.plGw_over k v)] at hφ
  refine ⟨φ, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (conj_mem_Ine hφ.1 hγ) (Subgroup.inv_mem _ (Subgroup.pow_mem _ hγ _))
  · have hu := GlobalTheory.TameLabels.wild_of_frob hγ hφ
    have hs : γ ^ H.g k ∈ Dec (F := H.E) (N.plOm.1 (A.plGw k v)) :=
      (Dec (F := H.E) _).pow_mem (Ine_le_Dec _ hγ) _
    have h := GlobalTheory.TameRel.wild_conj hs hu
    have e : γ ^ H.g k * ((γ ^ H.g k)⁻¹ * (φ * γ * φ⁻¹)) * (γ ^ H.g k)⁻¹ = φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ := by
      group
    rw [e] at h
    exact h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacter
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.MuCharProof

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) :
    M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

theorem mem_list_sum {α β : Type} (L : List α) (f : α → Multiset β) {a : α} (ha : a ∈ L) {b : β}
    (hb : b ∈ f a) : b ∈ (L.map f).sum :=
  Multiset.mem_of_le (List.le_sum_of_mem (List.mem_map_of_mem ha)) hb

end GlobalTheory.MuCharProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.StringRepresentationDecomposition

theorem rbEx_of_jointCond_rho : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  intro D hrho i hHG
  obtain ⟨x, hx⟩ := hHG
  have hx' := hx
  obtain ⟨-, Sig, hSig, hgood⟩ := hx'
  obtain ⟨ρ₀, ξ, -, -, hρx⟩ := hrho i x hx Sig hSig hgood
  exact ⟨_, isRhoBar_of_isRhoOf D i x _ hρx⟩

end GlobalTheory.StringRepresentationDecomposition
end

