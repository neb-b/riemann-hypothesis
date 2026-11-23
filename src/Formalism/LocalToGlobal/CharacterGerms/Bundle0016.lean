module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Rename

theorem prod_X_rename {σ τ : Type} (φ : σ → τ) (e : σ →₀ ℕ) :
    (e.prod fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) =
      MvPowerSeries.monomial (e.mapDomain φ) 1 := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg,
      Finsupp.mapDomain_add, MvPowerSeries.monomial_mul_monomial, one_mul]
  · intro a b
    rw [Finsupp.prod_single_index (h := fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) (pow_zero _),
      Finsupp.mapDomain_single]
    simp only [MvPowerSeries.X_pow_eq]

theorem coeff_subst_rename_inj {σ τ : Type} [Finite σ] (φ : σ → τ) (hφ : Function.Injective φ)
    (F : MvPowerSeries σ C) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e.mapDomain φ)
      (MvPowerSeries.subst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) F) = MvPowerSeries.coeff e F := by
  have hA : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp)
  rw [MvPowerSeries.coeff_subst hA, finsum_eq_single _ e]
  · rw [prod_X_rename, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    rw [prod_X_rename, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
    intro h
    exact hd (Finsupp.mapDomain_injective hφ h).symm

variable {dd : ℕ}

theorem snd_injective_fin_one : Function.Injective (fun p : Fin 1 × Fin dd => p.2) := fun p q h => Prod.ext (Subsingleton.elim _ _) h

theorem hasSubst_snd : MvPowerSeries.HasSubst
    (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp)

theorem uncurry_eq_subst (f : PS C 1 dd) :
    un1 f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) f := by
  ext μ
  have h := coeff_subst_rename_inj (C := C) (fun p : Fin 1 × Fin dd => p.2) snd_injective_fin_one f
    (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  have e1 : (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)).mapDomain (fun p : Fin 1 × Fin dd => p.2) = μ := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  rw [e1] at h
  exact h.symm

theorem subst_singlePointUncurry {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hasSubst_snd hA]
  congr 1
  funext p
  show MvPowerSeries.subst a (MvPowerSeries.X p.2) = a p.2
  rw [MvPowerSeries.subst_X hA]

theorem subst_oneVariableUncurry_eq_subst {σ : Type} [Finite σ] {b : σ → PS C 1 dd} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    un1 (MvPowerSeries.subst b f) = MvPowerSeries.subst (fun s => un1 (b s)) f := by
  have hB : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hB hasSubst_snd]
  congr 1
  funext s
  rw [uncurry_eq_subst]

theorem uncurry_X (i : Fin dd) : un1 (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd) = MvPowerSeries.X i := by
  rw [uncurry_eq_subst, MvPowerSeries.subst_X hasSubst_snd]

theorem eval_single_eq_subst {n : ℕ} (a : Pt C n dd) (f : PS C 1 dd) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  simp only [ev]
  congr 1
  funext p
  rw [Subsingleton.elim p.1 0]
  rfl

theorem uncurry_comp {φ a : Pt C 1 dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (a j)) (un1 (φ i)) = un1 (comp1 φ a i) := by
  have hu : ∀ j, MvPowerSeries.constantCoeff (un1 (a j)) = 0 := by
    intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (a j) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha j
  rw [subst_singlePointUncurry hu]
  show _ = un1 (ev ![a] (φ i))
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => a p.2) (fun s => ha s.2)]

end Rename

section Inst

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem FBChart.lg_const (i : Fin dd) : MvPowerSeries.constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_X] at h
  exact h

end Inst

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieChar
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def FBChart.IsChar (Y : FBChart C V O dd) (χ : PS C 1 dd) : Prop :=
  IntS V χ ∧ MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] χ = ev (n := 2) ![pt C dd 0] χ * ev (n := 2) ![pt C dd 1] χ

def dlogC (χ : PS C 1 dd) (i : Fin dd) : C := MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) χ

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePDescJet
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.DescP

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Jet

variable {k : Type} [CommRing k] {n d : ℕ}

def HiOrd (K : ℕ) (g : PS k n d) : Prop :=
  ∀ μ : Fin n × Fin d →₀ ℕ, μ.degree < K → coeff μ g = 0

theorem HiOrd.mono {K K' : ℕ} {g : PS k n d} (h : HiOrd K' g) (hK : K ≤ K') : HiOrd K g := fun μ hμ => h μ (lt_of_lt_of_le hμ hK)

theorem HiOrd.mul_left {K : ℕ} {g : PS k n d} (h : HiOrd K g) (a : PS k n d) : HiOrd K (a * g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have h2 : Finsupp.degree pq.2 < K :=
    lt_of_le_of_lt (by rw [← hpq', map_add (f := _)]; exact Nat.le_add_left _ _) hμ
  rw [h _ h2, mul_zero]

theorem HiOrd.sum {K : ℕ} {α : Type} (s : Finset α) (g : α → PS k n d) (h : ∀ i ∈ s, HiOrd K (g i)) :
    HiOrd K (∑ i ∈ s, g i) := by
  intro μ hμ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi μ hμ

theorem HiOrd.deriv {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (i : Fin n × Fin d) :
    HiOrd K (MvPowerSeries.pderiv (R := k) i g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_pderiv, h _ (by rw [map_add (f := _), Finsupp.degree_single]; omega), zero_mul]

theorem HiOrd.dofN {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (F : Fin d → PS k 2 d) (b : Fin n)
    (u : Fin d → k) : HiOrd K (DofN F b u g) := by
  unfold DofN
  exact HiOrd.sum _ _ fun j _ => (h.deriv _).mul_left _

theorem HiOrd.iter (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) :
    ∀ (j K : ℕ) (g : PS k n d), HiOrd (K + j) g → HiOrd K ((DofN F b u)^[j] g)
  | 0, K, g, h => h
  | j + 1, K, g, h => by
    rw [Function.iterate_succ_apply]
    exact HiOrd.iter F b u j K _ (HiOrd.dofN (K := K + j) (by rw [add_assoc]; exact h) F b u)

theorem HiOrd.foldr (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (K : ℕ) (g : PS k n d), HiOrd (K + (L.map m).sum) g →
      HiOrd K (L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g)
  | [], K, g, h => by simpa using h
  | l :: L, K, g, h => by
    rw [List.foldr_cons]
    refine HiOrd.iter F (cp l) (u l) (m l) K _ (HiOrd.foldr F cp u m L (K + m l) g ?_)
    rw [List.map_cons, List.sum_cons] at h
    rw [add_assoc]
    exact h

theorem HiOrd.dmonN (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (m : ι →₀ ℕ) {K : ℕ} {g : PS k n d} (h : HiOrd (K + m.degree) g) : HiOrd K (DmonN F cp u m g) := by
  unfold DmonN
  refine HiOrd.foldr F cp u m _ K g ?_
  rw [Finset.sum_map_toList, ← Finsupp.degree_eq_sum]
  exact h

theorem const_dpolyN_eq_zero (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) {g : PS k n d} (h : HiOrd (P.totalDegree + 1) g) :
    constantCoeff (DpolyN F cp u P g) = 0 := by
  unfold DpolyN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hd : Finsupp.degree m ≤ P.totalDegree := by
    have h1 := MvPolynomial.le_totalDegree hm
    rw [Finsupp.degree_apply]
    exact h1
  have h1 : HiOrd 1 (DmonN F cp u m g) := HiOrd.dmonN F cp u m (h.mono (by omega))
  rw [map_mul, ← coeff_zero_eq_constantCoeff_apply (DmonN F cp u m g), h1 0 (by simp), mul_zero]

theorem dofN_add (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f g : PS k n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (c : k) (f : PS k n d) :
    DofN F b u (c • f) = c • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, Finset.smul_sum, mul_smul_comm]

theorem iter_add (A : PS k n d → PS k n d) (hA : ∀ f g, A (f + g) = A f + A g) :
    ∀ (j : ℕ) (f g : PS k n d), A^[j] (f + g) = A^[j] f + A^[j] g
  | 0, f, g => rfl
  | j + 1, f, g => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, hA,
      iter_add A hA j]

theorem iter_smul (A : PS k n d → PS k n d) (hA : ∀ (c : k) f, A (c • f) = c • A f) :
    ∀ (j : ℕ) (c : k) (f : PS k n d), A^[j] (c • f) = c • A^[j] f
  | 0, c, f => rfl
  | j + 1, c, f => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hA, iter_smul A hA j]

theorem foldr_add (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (f g : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (f + g) =
        L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f + L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g
  | [], f, g => rfl
  | l :: L, f, g => by
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, foldr_add F cp u m L f g,
      iter_add _ (dofN_add F (cp l) (u l))]

theorem foldr_smul (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (c : k) (f : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (c • f) =
        c • L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f
  | [], c, f => rfl
  | l :: L, c, f => by
    rw [List.foldr_cons, List.foldr_cons, foldr_smul F cp u m L c f,
      iter_smul _ (dofN_smul F (cp l) (u l))]

theorem dpolyN_add (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f g : PS k n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, DmonN, foldr_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (c : k) (f : PS k n d) :
    DpolyN F cp u P (c • f) = c • DpolyN F cp u P f := by
  simp only [DpolyN, DmonN, foldr_smul, mul_smul_comm, Finset.smul_sum]

def nabL (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) : PS k n d →ₗ[k] k where
  toFun f := constantCoeff (DpolyN F cp u P (f * G))
  map_add' f g := by
    rw [add_mul, dpolyN_add, map_add (f := _)]
  map_smul' c f := by
    rw [smul_mul_assoc, dpolyN_smul, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      map_smul]
    rfl

def cst (D : ℕ) : Fin n × Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => D

theorem hiOrd_sub_trunc (f : PS k n d) (D : ℕ) :
    HiOrd (D + 1) (f - ((trunc' k (cst D) f : MvPolynomial _ k) : PS k n d)) := by
  intro μ hμ
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos, sub_self]
  intro i
  have h1 : μ i ≤ Finsupp.degree μ := Finsupp.le_degree i μ
  simp [cst]
  omega

theorem coe_eq_sum (p : MvPolynomial (Fin n × Fin d) k) :
    (p : PS k n d) = ∑ μ ∈ p.support, AddMonoidAlgebra.coeff p μ • monomial μ (1 : k) := by
  ext ν
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.coeff_coe, map_sum]
  simp only [map_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simpa using h

theorem nabL_trunc (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) (f : PS k n d) :
    nabL F cp u P G f = ∑ μ ∈ (trunc' k (cst P.totalDegree) f).support,
      AddMonoidAlgebra.coeff (trunc' k (cst P.totalDegree) f) μ * nabL F cp u P G (monomial μ (1 : k)) := by
  set T : PS k n d := ((trunc' k (cst P.totalDegree) f : MvPolynomial _ k) : PS k n d) with hTdef
  have h0 : nabL F cp u P G (f - T) = 0 := by
    show constantCoeff (DpolyN F cp u P ((f - T) * G)) = 0
    rw [mul_comm]
    exact const_dpolyN_eq_zero F cp u P ((hiOrd_sub_trunc f P.totalDegree).mul_left G)
  have hsplit : nabL F cp u P G f = nabL F cp u P G (f - T) + nabL F cp u P G T := by
    rw [← map_add (f := _), sub_add_cancel]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsplit, h0, zero_add, hTdef, coe_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem dpolyN_sub (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ m ∈ S, MvPowerSeries.C (P.coeff m) * DmonN F cp u m g := by
  unfold DpolyN
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]

theorem const_dpolyN_lin (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    {α : Type} (s : Finset α) (c : α → k) (Q : α → MvPolynomial ι k) (g : PS k n d) :
    constantCoeff (DpolyN F cp u (∑ i ∈ s, c i • Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) := by
  set S := (∑ i ∈ s, c i • Q i).support ∪ s.biUnion (fun i => (Q i).support) with hS
  rw [dpolyN_sub F cp u _ g S Finset.subset_union_left]
  have hQ : ∀ i ∈ s, DpolyN F cp u (Q i) g = ∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g :=
    fun i hi => dpolyN_sub F cp u _ g S
      (fun m hm => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hm⟩))
  have hR : ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g) :=
    Finset.sum_congr rfl fun i hi => by rw [hQ i hi]
  rw [hR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

end Jet

theorem exists_fin_sum {α M : Type} [AddCommMonoid M] (s : Finset α) (g : α → M) :
    ∃ (N : ℕ) (e : Fin N → α), (∀ j, e j ∈ s) ∧ ∑ x ∈ s, g x = ∑ j, g (e j) := ⟨s.card, fun j => (s.equivFin.symm j : α), fun j => (s.equivFin.symm j).2, by
    rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]⟩

end Formalism.L2.FormalSeriesBounds.DescP
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

theorem vV_algebraMap_nonneg (T : CDVR) (t : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr t) := by
  have hle := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) t
  unfold vV valV
  generalize (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
    (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr t) = y at hle ⊢
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hy
    have ha : a ≤ 1 := WithZero.coe_le_one.1 hle
    have hlog : WithZero.log (a : WithZero (Multiplicative ℤ)) = Multiplicative.toAdd a := rfl
    rw [hlog, neg_nonneg]
    exact ha

theorem embIntSt_holds : EmbIntSt := by
  unfold EmbIntSt
  intro T C _ V ι h t
  by_cases ht : t = 0
  · subst ht
    rw [map_zero, map_zero]
    exact VF.Ge.zero 0
  · have hx : algebraMap T.V T.Fr t ≠ 0 :=
      fun h0 => ht ((IsFractionRing.injective T.V T.Fr) (by rw [h0, map_zero]))
    have hl : ((V.l : ℕ) : T.Fr) = algebraMap T.V T.Fr ((V.l : ℕ) : T.V) := (map_natCast _ _).symm
    have h1 := vV_algebraMap_nonneg T t
    have h2 := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rw [← hl] at h2
    unfold VF.Ge
    rw [h (algebraMap T.V T.Fr t) hx]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2))

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLogExSt
section
set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogEx

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

def LinN {C : Type} [CommRing C] {dd : ℕ} (f : Pt C 1 dd) : Prop :=
  ∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (f i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)

section Gen

variable {C : Type} [CommRing C] {dd : ℕ}

theorem linN_const {f : Pt C 1 dd} (hf : LinN f) (i : Fin dd) : constantCoeff (f i) = 0 := by
  have h := hf i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h, MvPowerSeries.coeff_zero_X]

end Gen

end LogEx

end Formalism.L2.FormalSeriesBounds
end
end

