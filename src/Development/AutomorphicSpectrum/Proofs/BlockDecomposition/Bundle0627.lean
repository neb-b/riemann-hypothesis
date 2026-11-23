module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiltration
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibOrd.ChainFilt

section generic
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

def subMap (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v)) (S : Subrepresentation ρ) :
    Subrepresentation σ :=
  ⟨S.toSubmodule.map f, by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, hf g v⟩⟩

theorem subMap_mono (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v))
    {S T : Subrepresentation ρ} (h : S ≤ T) : subMap f hf S ≤ subMap f hf T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem subMap_bot (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v)) :
    subMap f hf (⊥ : Subrepresentation ρ) = ⊥ :=
  Subrepresentation.toSubmodule_injective (Submodule.map_bot f)

theorem subQuot_subMap_equiv (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v))
    (hi : Function.Injective f) (S T : Subrepresentation ρ) :
    Nonempty ((subQuot S T).Equiv (subQuot (subMap f hf S) (subMap f hf T))) := by
  let e : S.toSubmodule ≃ₗ[ℂ] (subMap f hf S).toSubmodule :=
    Submodule.equivMapOfInjective f hi S.toSubmodule
  have he : (T.toSubmodule.comap S.toSubmodule.subtype).map e.toLinearMap =
      (subMap f hf T).toSubmodule.comap (subMap f hf S).toSubmodule.subtype := by
    ext ⟨w, hw⟩
    constructor
    · rintro ⟨⟨v, hvS⟩, hvT, hv⟩
      have hv' : f v = w := congrArg Subtype.val hv
      exact ⟨v, hvT, hv'⟩
    · rintro ⟨v, hvT, hv⟩
      obtain ⟨u, hu, rfl⟩ := hw
      have huv : v = u := hi hv
      subst huv
      exact ⟨⟨v, hu⟩, hvT, Subtype.ext rfl⟩
  let q := Submodule.Quotient.equiv _ _ e he
  refine ⟨Representation.Equiv.mk q fun g => ?_⟩
  refine Submodule.linearMap_qext _ ?_
  ext v
  show Submodule.Quotient.mk (e ⟨ρ g v.1, S.apply_mem_toSubmodule g v.2⟩) =
    Submodule.Quotient.mk (⟨σ g (f v.1), (subMap f hf S).apply_mem_toSubmodule g ⟨v.1, v.2, rfl⟩⟩ : _)
  congr 1
  exact Subtype.ext (hf g v.1)

end generic

section chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {R : ℕ → GRep k n → Prop} {Z : ℕ → Prop}

theorem chain_le {a b : ℕ} {X : GRep k n} (h : Chain R Z a b X) : a ≤ b := by
  induction h <;> omega

theorem filt_extend {a b : ℕ} {X Y : GRep k n} (f : Y.V →ₗ[ℂ] X.V)
    (hf : ∀ x v, f (Y.ρ x v) = X.ρ x (f v)) (hi : Function.Injective f) (hab : a < b)
    (F' : ℕ → Subrepresentation Y.ρ) (hanti : Antitone F') (htop : F' (a + 1) = ⊤) (hbot : F' b = ⊥)
    (hst : ∀ i, a + 1 ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F' i) (F' (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F' i = F' (i + 1)))
    (h0 : (∃ A, R a A ∧ Nonempty ((subQuot ⊤ (subMap f hf ⊤)).Equiv A.ρ)) ∨
      (Z a ∧ (⊤ : Subrepresentation X.ρ) = subMap f hf ⊤)) :
    ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧ F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  classical
  obtain ⟨F, hF1, hF2⟩ : ∃ F : ℕ → Subrepresentation X.ρ, (∀ i, i ≤ a → F i = ⊤) ∧
      (∀ i, a < i → F i = subMap f hf (F' i)) :=
    ⟨fun i => if i ≤ a then ⊤ else subMap f hf (F' i), fun i h => if_pos h,
      fun i h => if_neg (by omega)⟩
  refine ⟨F, ?_, hF1 a le_rfl, ?_, ?_⟩
  · intro i j hij
    by_cases h2 : i ≤ a
    · rw [hF1 i h2]; exact le_top
    · rw [hF2 i (by omega), hF2 j (by omega)]; exact subMap_mono f hf (hanti hij)
  · rw [hF2 b hab, hbot, subMap_bot]
  · intro i hai hib
    rcases hai.eq_or_lt with rfl | hlt
    · rw [hF1 a le_rfl, hF2 (a + 1) (by omega), htop]
      exact h0
    · rw [hF2 i hlt, hF2 (i + 1) (by omega)]
      rcases hst i hlt hib with ⟨A, hR, ⟨e⟩⟩ | ⟨hZ, he⟩
      · obtain ⟨e'⟩ := subQuot_subMap_equiv f hf hi (F' i) (F' (i + 1))
        exact Or.inl ⟨A, hR, ⟨e'.symm.trans e⟩⟩
      · exact Or.inr ⟨hZ, by rw [he]⟩

theorem exists_filtration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) (a b : ℕ)
    (X : GRep k n), Chain R Z a b X → ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧
      F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
        (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  intro k _ _ _ _ n R Z a b X h
  induction h with
  | nil a X hs =>
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, ?_, rfl, fun i h1 h2 => by omega⟩
    refine Subrepresentation.toSubmodule_injective ?_
    ext v
    have : v = 0 := Subsingleton.elim _ _
    subst this
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  | @step a b X Y A hR hs hc ih =>
    obtain ⟨f, g, hf, hg, hi, hsur, he⟩ := hs
    obtain ⟨F', h1, h2, h3, h4⟩ := ih
    have hab := chain_le hc
    refine filt_extend f hf hi (by omega) F' h1 h2 h3 h4 (Or.inl ⟨A, hR, ?_⟩)
    obtain ⟨S, hS, e⟩ := GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv X.ρ A.ρ
      ⟨g, fun x => LinearMap.ext (hg x)⟩ hsur
    have hS' : S = subMap f hf ⊤ := by
      refine Subrepresentation.toSubmodule_injective ?_
      refine hS.trans ?_
      show LinearMap.ker g = Submodule.map f ⊤
      rw [Submodule.map_top, he]
    exact hS' ▸ e
  | @skip a b X Y hZ he hc ih =>
    obtain ⟨e⟩ := he
    obtain ⟨F', h1, h2, h3, h4⟩ := ih
    have hab := chain_le hc
    refine filt_extend e.toLinearEquiv.toLinearMap (eint e) e.toLinearEquiv.injective (by omega)
      F' h1 h2 h3 h4 (Or.inr ⟨hZ, ?_⟩)
    refine Subrepresentation.toSubmodule_injective ?_
    show ⊤ = Submodule.map e.toLinearEquiv.toLinearMap ⊤
    rw [Submodule.map_top, LinearEquiv.range]

end chain

end GlobalTheory.CompanionTheory.LeibOrd.ChainFilt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIndicatorFormula
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.TjChar

open GlobalTheory.WeylGL (tor tor_val tor_add tor_const_comm IntM intM_tor intM_doset)

theorem sum_ite_lt (n m : ℕ) : ∑ j : Fin n, (if (j : ℕ) < m then (1 : ℤ) else 0) = min (n : ℤ) m := by
  rw [Finset.sum_boole, Fin.card_filter_val_lt]
  push_cast
  rfl

theorem antitone_eq {n k : ℕ} {a : Fin n → ℤ} (ha : Antitone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1)
    (hs : ∑ i, a i = (k : ℤ)) (i : Fin n) : a i = if (i : ℕ) < k then 1 else 0 := by
  have hi := i.2
  have hc : a i = 0 ∨ a i = 1 := by
    have := h0 i
    have := h1 i
    omega
  rcases hc with hc | hc
  · have hle : ∑ j, a j ≤ ∑ j : Fin n, (if (j : ℕ) < (i : ℕ) then (1 : ℤ) else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj
      · exact h1 j
      · have : a j ≤ a i := ha (Fin.le_def.2 (by omega))
        omega
    rw [hs, sum_ite_lt] at hle
    have : k ≤ (i : ℕ) := by omega
    rw [hc, if_neg (by omega)]
  · have hle : ∑ j : Fin n, (if (j : ℕ) < (i : ℕ) + 1 then (1 : ℤ) else 0) ≤ ∑ j, a j := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj
      · have : a i ≤ a j := ha (Fin.le_def.2 (by omega))
        omega
      · exact h0 j
    rw [hs, sum_ite_lt] at hle
    have : (i : ℕ) < k := by
      push_cast at hle
      omega
    rw [hc, if_pos this]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {ϖ : w.adicCompletion E}

theorem ordL_eq_of_v {x : w.adicCompletion E} {m : ℤ} (h : Valued.v x = WithZero.exp (-m)) : ordL x = m := by
  have hx : Valued.v x ≠ 0 := by
    rw [h]
    exact WithZero.exp_ne_zero
  have e : WithZero.unzero hx = Multiplicative.ofAdd (-m) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  unfold ordL
  rw [dite_eq_right hx, e]
  simp

theorem v_zpow_eq (hu : IsUnifV E w ϖ) (m : ℤ) : Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hu]
  have : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := rfl
  rw [this, ← WithZero.exp_zsmul]
  simp

theorem v_prod_zpow (hu : IsUnifV E w ϖ) (a : Fin n → ℤ) (s : Finset (Fin n)) :
    Valued.v (∏ i ∈ s, ϖ ^ a i) = WithZero.exp (-∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, map_mul, ih, v_zpow_eq hu, ← WithZero.exp_add]
    congr 1
    ring

theorem ordL_det (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    ordL (c * tor h0 a * d : GL (Fin n) (w.adicCompletion E)).val.det = ∑ i, a i := by
  apply ordL_eq_of_v
  have h1 : Valued.v c.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hc
  have h2 : Valued.v d.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hd
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, h1, h2, tor_val,
    Matrix.det_diagonal, v_prod_zpow hu]
  simp

theorem tor_inv (h0 : ϖ ≠ 0) (a : Fin n → ℤ) : (tor h0 a)⁻¹ = tor h0 (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← tor_add]
  ext1
  simp [tor_val]

theorem tor_one_val (h0 : ϖ ≠ 0) (x : GL (Fin n) (w.adicCompletion E)) :
    (tor h0 (fun _ => 1) * x : GL (Fin n) (w.adicCompletion E)).val = ϖ • x.val := by
  ext i j
  simp [tor_val, Matrix.diagonal_mul]

theorem intM_iff {c d x y : GL (Fin n) (w.adicCompletion E)} (hc : c ∈ GLint (Fin n) (Ov E w))
    (hd : d ∈ GLint (Fin n) (Ov E w)) (e : x = c * y * d) : IntM x ↔ IntM y :=
  ⟨fun h => intM_doset h ⟨c⁻¹, Subgroup.inv_mem _ hc, d⁻¹, Subgroup.inv_mem _ hd, by rw [e]; group⟩,
    fun h => intM_doset h ⟨c, hc, d, hd, e⟩⟩

theorem isInt_iff (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    IsInt w (c * tor h0 a * d : GL (Fin n) (w.adicCompletion E)).val ↔ ∀ i, 0 ≤ a i :=
  (intM_iff hc hd rfl).trans (intM_tor h0 hu a)

theorem isInt_dual_iff (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    IsInt w (ϖ • ((c * tor h0 a * d : GL (Fin n) (w.adicCompletion E))⁻¹).val) ↔ ∀ i, a i ≤ 1 := by
  rw [← tor_one_val h0]
  have e : tor h0 (fun _ => 1) * (c * tor h0 a * d)⁻¹ = d⁻¹ * tor h0 ((fun _ => 1) + -a) * c⁻¹ := by
    rw [tor_add, _root_.mul_inv_rev, _root_.mul_inv_rev, tor_inv, ← mul_assoc (tor h0 fun _ => 1) d⁻¹, tor_const_comm]
    group
  have h := (intM_iff (Subgroup.inv_mem _ hd) (Subgroup.inv_mem _ hc) e).trans (intM_tor h0 hu _)
  refine h.trans (forall_congr' fun i => ?_)
  simp

end GlobalTheory.CompanionTheory.CtS.TjChar

namespace GlobalTheory.CompanionTheory.CtS


open GlobalTheory.CompanionTheory.CtS.TjChar in
theorem Tj_eq_ite : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n k : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → k ≤ n → ∀ g : GL (Fin n) (w.adicCompletion E), Tj ℂ n (Ov E w) ϖ k g = if IsInt w g.val ∧ IsInt w (ϖ • (g⁻¹).val) ∧ ordL g.val.det = (k : ℤ) then 1 else 0 := by
  intro E _ _ w n k ϖ hu hk g
  have h0 : ϖ ≠ 0 := fun h => by simp [IsUnifV, h] at hu
  rw [GlobalTheory.WeylGL.Tj_eq h0 k]
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨a, ha, c, hc, d, hd, rfl⟩ := GlobalTheory.WeylGL.cartan h0 hu g
    have ha0 := (isInt_iff h0 hu hc hd a).1 h1
    have ha1 := (isInt_dual_iff h0 hu hc hd a).1 h2
    rw [ordL_det h0 hu hc hd] at h3
    have e : a = fun i : Fin n => if (i : ℕ) < k then 1 else 0 :=
      funext (antitone_eq ha ha0 ha1 h3)
    subst e
    exact GlobalTheory.WeylGL.dosetInd_of_mem ⟨c, hc, d, hd, rfl⟩
  · refine GlobalTheory.WeylGL.dosetInd_of_not ?_
    rintro ⟨c, hc, d, hd, rfl⟩
    refine h ⟨(isInt_iff h0 hu hc hd _).2 fun i => ?_, (isInt_dual_iff h0 hu hc hd _).2 fun i => ?_, ?_⟩
    · split_ifs <;> omega
    · split_ifs <;> omega
    · rw [ordL_det h0 hu hc hd, sum_ite_lt, min_eq_right (by exact_mod_cast hk)]

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeVectorLinearCombination
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.HeckeSum

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem heckeVec_finset_sum {ι : Type} (ρ : Representation ℂ G V) (K : Subgroup G) (s : Finset ι) (f : ι → ℂ)
    (h : ι → G → ℂ) (x : V) (hf : ∀ p ∈ s, {c : G ⧸ K | h p c.out ≠ 0}.Finite) :
    heckeVec ρ K (fun g => ∑ p ∈ s, f p * h p g) x = ∑ p ∈ s, f p • heckeVec ρ K (h p) x := by
  have e : ∀ c : G ⧸ K, (∑ p ∈ s, f p * h p c.out) • ρ c.out x =
      ∑ p ∈ s, f p • (h p c.out • ρ c.out x) := fun c => by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun p _ => mul_smul _ _ _
  unfold heckeVec
  rw [finsum_congr e, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_finsum]
  · intro p hp
    exact (hf p hp).subset fun c hc h0 => hc (by simp [h0])

theorem biInv_out {K : Subgroup G} {h : G → ℂ} (hh : IsBiInv K h) (g : G) :
    h ((g : G ⧸ K).out) = h g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  have e := hh 1 k g
  simp only [OneMemClass.coe_one, one_mul] at e
  rw [hk, e]

variable {A B : Type} [Group A] [Group B]

theorem finite_pair {KA : Subgroup A} {KB : Subgroup B} {fA : A → ℂ} {fB : B → ℂ}
    (hA : IsBiInv KA fA) (hB : IsBiInv KB fB) (fa : {c : A ⧸ KA | fA c.out ≠ 0}.Finite)
    (fb : {c : B ⧸ KB | fB c.out ≠ 0}.Finite) :
    {c : (A × B) ⧸ KA.prod KB | fA c.out.1 * fB c.out.2 ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image
    (f := fun c : (A × B) ⧸ KA.prod KB => (((c.out.1 : A ⧸ KA)), ((c.out.2 : B ⧸ KB))))
    ((fa.prod fb).subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : fA c.out.1 * fB c.out.2 ≠ 0 := hc
    refine ⟨?_, ?_⟩
    · change fA ((c.out.1 : A ⧸ KA).out) ≠ 0
      rw [biInv_out hA]
      exact left_ne_zero_of_mul hc'
    · change fB ((c.out.2 : B ⧸ KB).out) ≠ 0
      rw [biInv_out hB]
      exact right_ne_zero_of_mul hc'
  · intro c _ d _ e
    have e1 := QuotientGroup.eq.1 (congrArg Prod.fst e)
    have e2 := QuotientGroup.eq.1 (congrArg Prod.snd e)
    rw [← c.out_eq', ← d.out_eq']
    exact QuotientGroup.eq.2 (Subgroup.mem_prod.2 ⟨by simpa using e1, by simpa using e2⟩)

end Abstract

theorem heckeVec_Tj_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℂ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V),
    heckeVec ρ (K2 a b w) (fun g => ∑ p ∈ s, f p * (Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2)) x =
      ∑ p ∈ s, f p • heckeVec ρ (K2 a b w) (fun g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x := by
  intro E _ _ _ a b w ϖ hϖ s f V _ _ ρ x
  refine heckeVec_finset_sum ρ (K2 a b w) s f
    (fun p g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x fun p _ => ?_
  have ha := Tj_mem_hecke (n := a) hϖ p.1
  have hb := Tj_mem_hecke (n := b) hϖ p.2
  exact finite_pair ha.1 hb.1 (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w a) ha.2)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w b) hb.2)

end GlobalTheory.CompanionTheory.CtS.HeckeSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmooth
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem smooth_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → Geo.IsSmoothHerm A := by
  rintro m n M A ⟨u, -, -, hA⟩ z₀ hz₀
  choose c hc using hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  let T : Set ((Σ k, Bk n k) → ℂ) := {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
  have hT : IsOpen T := by
    have : T = ⋂ k, {z : (Σ k, Bk n k) → ℂ | z ⟨k, c k⟩ ≠ 0} := by ext; simp [T]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
  have hz : z₀ ∈ T := hc
  let s := multiprojectivePoint (m := m) (n := n) c
  obtain ⟨haff, hgen⟩ := _root_.GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo m n c
  have hmem : ∀ z ∈ T, s z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := fun z h => (GlobalTheory.T.multiprojective_point_of_nonvanishing_coords m n c z h).2
  obtain ⟨hcont, hholo⟩ := holo_of_affine haff hT hmem hgen
  obtain ⟨i, hi⟩ := exists_mem_ptsIn M.isLB.cover (s z₀)
  have hV : s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hi, hmem z₀ hz⟩

  let F : CxPts (mpStr ℤ m n) σ₀ → ℝ := fun y =>
    ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
      Real.exp ((M.φ σ₀).φ i y / 2)
  have hF : CInfAt F (s z₀) := by
    have h1 : CInfAt (fun y => ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)
        (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖) (s z₀) := by
      refine ⟨M.B.U i ⊓ mchart c, Unit, inferInstance, fun _ => (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)),
        fun v => ‖v ()‖, {v | v () ≠ 0}, hV, isOpen_ne_fun (continuous_apply _) continuous_const,
        ev_ne_zero hV (u i c).isUnit, ?_, Filter.EventuallyEq.rfl⟩
      intro v hv
      exact ((contDiffAt_norm ℝ hv).comp v ((contDiff_apply ℝ (fun _ => ℂ) ()).contDiffAt)).contDiffWithinAt
    have h2 := (M.cInf σ₀) i (s z₀) hi
    exact h1.comp₂ h2 (G := fun x => x.1 * Real.exp (x.2 / 2))
      (contDiff_fst.mul (Real.contDiff_exp.comp (contDiff_snd.div_const 2)))
  have hFs := _root_.GlobalTheory.CompanionTheory.CxSmooth.contDiffAt_comp_of_cInfAt hT hcont hholo hz hF
  have hP : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) z₀ := by
    refine contDiffAt_prod fun k _ => ?_
    have hn : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ‖z ⟨k, c k⟩‖) z₀ :=
      (contDiffAt_norm ℝ (hc k)).comp z₀ ((contDiff_apply ℝ (fun _ => ℂ) (⟨k, c k⟩ : Σ k, Bk n k)).contDiffAt)
    have hx : ‖z₀ ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hc k)
    cases h : A.a k with
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast]
      exact hn.pow j
    | negSucc j =>
      simp only [zpow_negSucc]
      exact (hn.pow (j + 1)).inv (pow_ne_zero _ hx)
  refine (hP.mul hFs).congr_of_eventuallyEq ?_
  have hnb : ∀ᶠ z in nhds z₀, z ∈ T ∧ s z ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) :=
    Filter.Eventually.and (hT.mem_nhds hz) ((hcont.continuousAt (hT.mem_nhds hz)).preimage_mem_nhds ((isOpen_ptsIn _).mem_nhds hV))
  filter_upwards [hnb] with z hz'
  rw [hA i c (s z) z (GlobalTheory.T.multiprojective_point_of_nonvanishing_coords m n c z hz'.1).1 hz'.2]
  simp only [F, Function.comp_apply]
  ring

end GlobalTheory.CompanionTheory.MPSmooth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegmentsStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_langlands_subquotient_segments : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL (k := k)), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  first | exact @GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | (intros; apply GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeftStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_product_rank_zero_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | exact GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | (intros; apply GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' <;> assumption)
end

