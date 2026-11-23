module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PNameOf
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem natCard_of_finrank {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) : Nat.card K = g ^ m := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]

private theorem frob_top {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (x : K) : x ^ g ^ m = x := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_of_finrank hm hK
  rw [← hc]
  exact FiniteField.pow_card x

private theorem aeval_pow_prime_pow_eq_pow {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (Y : (ZMod g)[X]) (x : K) (j : ℕ) : aeval (x ^ g ^ j) Y = (aeval x Y) ^ g ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, pow_mul, ← ih, ← Polynomial.expand_aeval, ZMod.expand_card, map_pow]

private theorem conj_ne {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = m)
    (a : ℕ) (ha : 0 < a) (ham : a < m) : (z : K) ^ g ^ a ≠ z := by
  intro h
  classical
  have hg : g.Prime := Fact.out
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  set F := IntermediateField.adjoin (ZMod g) {(z : K)} with hFdef
  have hF : Module.finrank (ZMod g) F = m := by
    rw [IntermediateField.adjoin.finrank hint, hz]
  have hfix : ∀ y ∈ F, y ^ g ^ a = y := by
    intro y hy
    have hy' : y ∈ Algebra.adjoin (ZMod g) {(z : K)} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      exact hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show (aeval (z : K) p) ^ g ^ a = aeval (z : K) p
    rw [← aeval_pow_prime_pow_eq_pow, h]
  have hq : 1 < g ^ a := Nat.one_lt_pow ha.ne' hg.one_lt
  have hP0 : (X ^ (g ^ a) - X : K[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hle := Polynomial.card_le_degree_of_subset_roots (p := (X ^ (g ^ a) - X : K[X]))
    (Z := Finset.univ.map (Function.Embedding.subtype (· ∈ F))) (by
      intro y hy
      rw [Finset.map_val, Multiset.mem_map] at hy
      obtain ⟨⟨y, hyF⟩, -, rfl⟩ := hy
      rw [Polynomial.mem_roots hP0, IsRoot, eval_sub, eval_pow, eval_X]
      simp only [Function.Embedding.coe_subtype]
      rw [hfix y hyF, sub_self])
  rw [Polynomial.natDegree_X_pow_sub_X (R := K) hq, Finset.card_map, Finset.card_univ,
    Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hF] at hle
  have := Nat.pow_lt_pow_right hg.one_lt ham
  omega

private theorem conj_inj {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = m)
    (i j : ℕ) (hij : i < j) (hj : j < m) : (z : K) ^ g ^ i ≠ (z : K) ^ g ^ j := by
  intro h
  have key : ∀ x : K, (x ^ g ^ i) ^ g ^ (m - i) = x := by
    intro x
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (by omega)]
    exact frob_top hm hK x
  apply conj_ne hm hK z hz (j - i) (by omega) (by omega)
  have hs : (z : K) ^ g ^ j = ((z : K) ^ g ^ (j - i)) ^ g ^ i := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  rw [hs] at h
  have h2 := congrArg (fun y => y ^ g ^ (m - i)) h
  simp only [key] at h2
  exact h2.symm

private theorem aeval_conj {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (Y : (ZMod g)[X]) (x : K) (hx : aeval x Y = 0) (j : ℕ) : aeval (x ^ g ^ j) Y = 0 := by
  rw [aeval_pow_prime_pow_eq_pow, hx, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]

private theorem roots_conj {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (Y : (ZMod g)[X]) (hY : Irreducible Y) (hYm : Y.Monic)
    (hYd : Y.natDegree = m) (z : Kˣ) (hz : aeval (z : K) Y = 0) {L : Type} [Field L] (ι : K →+* L) :
    ((Y.map (algebraMap (ZMod g) K)).map ι).roots = (Multiset.range m).map fun j => ι ((z : K) ^ g ^ j) := by
  have hzm : (minpoly (ZMod g) (z : K)).natDegree = m := by
    rw [← minpoly.eq_of_irreducible_of_monic hY hz hYm, hYd]
  have hnd : ((Multiset.range m).map fun j => ι ((z : K) ^ g ^ j)).Nodup := by
    rw [Multiset.nodup_map_iff_inj_on (Multiset.nodup_range m)]
    intro i hi j hj hij
    simp only [Multiset.mem_range] at hi hj
    have h' : (z : K) ^ g ^ i = (z : K) ^ g ^ j := ι.injective hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd h' (conj_inj hm hK z hzm i j h hj)
    · exact h
    · exact absurd h'.symm (conj_inj hm hK z hzm j i h hi)
  have hP0 : ((Y.map (algebraMap (ZMod g) K)).map ι) ≠ 0 := ((hYm.map _).map _).ne_zero
  have hle : ((Multiset.range m).map fun j => ι ((z : K) ^ g ^ j)) ≤
      ((Y.map (algebraMap (ZMod g) K)).map ι).roots := by
    rw [Multiset.le_iff_subset hnd]
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy
    rw [mem_roots hP0, IsRoot, eval_map, eval₂_map, ← Polynomial.hom_eval₂, ← aeval_def,
      aeval_conj Y _ hz j, map_zero]
  have hdeg : ((Y.map (algebraMap (ZMod g) K)).map ι).natDegree = m := by
    rw [natDegree_map, natDegree_map, hYd]
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [Multiset.card_map, Multiset.card_range, ← hdeg]
  exact card_roots' _

private theorem false_of_reg_of_mul_pow_modEq {g m c i j : ℕ} (hg : 0 < g) (hc : Reg g m c) (hij : i < j) (hj : j < m)
    (h : c * g ^ i ≡ c * g ^ j [MOD g ^ m - 1]) : False := by
  have hone : g ^ m ≡ 1 [MOD g ^ m - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hg)
  have h2 := h.mul_right (g ^ (m - i))
  have e1 : c * g ^ i * g ^ (m - i) = c * g ^ m := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have e2 : c * g ^ j * g ^ (m - i) = c * g ^ (j - i) * g ^ m := by
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e1, e2] at h2
  have h3 : c * g ^ m ≡ c [MOD g ^ m - 1] := by simpa using hone.mul_left c
  have h4 : c * g ^ (j - i) * g ^ m ≡ c * g ^ (j - i) [MOD g ^ m - 1] := by
    simpa using hone.mul_left (c * g ^ (j - i))
  exact hc (j - i) (by omega) (by omega) (h4.symm.trans (h2.symm.trans h3))

private theorem regular_character_of_pow {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K 𝔨 : Type} [Field K] [Algebra (ZMod g) K] [Field 𝔨]
    (hK : Module.finrank (ZMod g) K = m) (ι : K →+* 𝔨) (Θ : 𝔨 →* ℂ) (hΘ : Inj Θ) (c : ℕ) (hc : Reg g m c) :
    GlobalTheory.Published.IsRegularChar g m ((Units.map (Θ.comp ι.toMonoidHom)) ^ c : Kˣ →* ℂˣ) := by
  intro i j hi hj hij
  have hg : g.Prime := Fact.out
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = g ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, natCard_of_finrank hm hK]
  have hv := DFunLike.congr_fun hij ζ
  simp only [MonoidHom.pow_apply, ← pow_mul] at hv
  rw [← map_pow, ← map_pow] at hv
  have hv' : Θ (ι ((ζ ^ (c * g ^ i) : Kˣ) : K)) = Θ (ι ((ζ ^ (c * g ^ j) : Kˣ) : K)) :=
    congrArg (fun u : ℂˣ => (u : ℂ)) hv
  have h1 := hΘ _ _ (by simp) (by simp) hv'
  have h2 : ζ ^ (c * g ^ i) = ζ ^ (c * g ^ j) := Units.ext (ι.injective h1)
  rw [pow_eq_pow_iff_modEq, hord] at h2
  rcases lt_trichotomy i j with h | h | h
  · exact (false_of_reg_of_mul_pow_modEq hg.pos hc h hj h2).elim
  · exact h
  · exact (false_of_reg_of_mul_pow_modEq hg.pos hc h hi h2.symm).elim

theorem UpperTheory.Gal.InertialTypesAlt.nameOf :
    NameOf := by
  intro g _ m hm F K 𝔨 _ _ _ _ _ hK r e ι Θ hΘ c hc
  refine ⟨(Units.map (Θ.comp ι.toMonoidHom)) ^ c, ?_, regular_character_of_pow hm hK ι Θ hΘ c hc, ?_⟩
  · intro u
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  · intro τ hτ y hy z hz
    set Y : (ZMod g)[X] := (y : Matrix (Fin m) (Fin m) (ZMod g)).charpoly with hYdef
    have hYm : Y.Monic := Matrix.charpoly_monic _
    have hYd : Y.natDegree = m := by
      rw [hYdef, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    let γ : GL (Fin m) F := Matrix.GeneralLinearGroup.map r.symm.toRingHom y
    have hyγ : Matrix.GeneralLinearGroup.map r.toRingHom γ = y := by
      ext i j
      simp [γ]
    have hγc : (γ : Matrix (Fin m) (Fin m) F).charpoly = Y.map r.symm.toRingHom := by
      rw [show (γ : Matrix (Fin m) (Fin m) F) = (y : Matrix (Fin m) (Fin m) (ZMod g)).map r.symm.toRingHom
        from rfl, Matrix.charpoly_map]
    have hirr : Irreducible (LinearMap.charpoly (Matrix.toLin' (γ : Matrix (Fin m) (Fin m) F))) := by
      rw [Matrix.charpoly_toLin', hγc]
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv r.symm)).mpr hy
    rw [← hyγ, hτ γ]
    delta cusp psiG
    congr 1
    refine (_root_.GlobalTheory.CuspGL.psi_of_irreducible_charpoly F (Fin m → F) _ (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F (Θ.comp e) c).1 _ hirr).trans ?_
    rw [Matrix.charpoly_toLin', hγc]
    delta GlobalTheory.CuspGL.rootSum
    rw [Polynomial.map_map]
    have hP : (Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).Splits :=
      IsAlgClosed.splits _
    have hroots : (Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map e =
        ((Y.map (algebraMap (ZMod g) K)).map ι).roots := by
      rw [← hP.roots_map e, Polynomial.map_map, Polynomial.map_map]
      congr 2
      exact Subsingleton.elim _ _
    have hre : ((Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map
        fun α => (Θ.comp e) α ^ c) =
        (((Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map e).map
        fun β => Θ β ^ c) := by
      rw [Multiset.map_map]
      rfl
    rw [hre, hroots, roots_conj hm hK Y hy hYm hYd z hz ι, Multiset.map_map,
      Finset.sum_eq_multiset_sum, Finset.range_val]
    apply congrArg
    apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp_apply]
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_pow_eq_pow_val]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PParCons
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section ParConsAux

variable {F : Type} [Field F]

private theorem tl_entry {a n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin a) (I J : Fin n)
    (hI : (I : ℕ) = i) (hJ : (J : ℕ) = j) : GlobalTheory.Shin.tl a M i j = M I J := by
  unfold GlobalTheory.Shin.tl GlobalTheory.Shin.ent
  rw [dite_eq_left ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem br_entry {a b n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin b) (I J : Fin n)
    (hI : (I : ℕ) = a + i) (hJ : (J : ℕ) = a + j) : GlobalTheory.Shin.br a b M i j = M I J := by
  unfold GlobalTheory.Shin.br GlobalTheory.Shin.ent
  rw [dite_eq_left ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem units_of {a b n : ℕ} (hn : n = a + b) (p : GL (Fin n) F) (h : GlobalTheory.Shin.InPar a p) :
    IsUnit (GlobalTheory.Shin.tl a (p : Matrix (Fin n) (Fin n) F)) ∧
      IsUnit (GlobalTheory.Shin.br a b (p : Matrix (Fin n) (Fin n) F)) := by
  subst hn
  have hM : (p : Matrix (Fin (a + b)) (Fin (a + b)) F).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (GlobalTheory.Shin.tl a (p : Matrix (Fin (a + b)) (Fin (a + b)) F))
        (Matrix.of fun i j => (p : Matrix (Fin (a + b)) (Fin (a + b)) F) (Fin.castAdd b i) (Fin.natAdd a j)) 0
        (GlobalTheory.Shin.br a b (p : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
      exact (tl_entry _ i j _ _ (by simp) (by simp)).symm
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.of_apply]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.zero_apply]
      exact h _ _ (by simp) (by simp)
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
      exact (br_entry _ i j _ _ (by simp) (by simp)).symm
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hM, Matrix.det_fromBlocks_zero₂₁,
    IsUnit.mul_iff] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 hu.1, (Matrix.isUnit_iff_isUnit_det _).2 hu.2⟩

private theorem toG_coe {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((GlobalTheory.Shin.toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold GlobalTheory.Shin.toG
  rw [dite_eq_left h]
  rfl

private theorem sv0 {s n : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n) (i : Fin (d 0)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩ : Fin n) : ℕ) = i := by
  rw [GlobalTheory.SmGL.stdBlocks_val]
  simp

private theorem svS {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (c : Fin s) (i : Fin (d c.succ)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩ : Fin n) : ℕ) =
      d 0 + ((GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩ : Fin b) : ℕ) := by
  rw [GlobalTheory.SmGL.stdBlocks_val, GlobalTheory.SmGL.stdBlocks_val]
  erw [Fin.sum_univ_succ]
  rw [add_assoc]
  congr 2

private theorem inPar_of {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (p : GL (Fin n) F)
    (hp : p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd)) : GlobalTheory.Shin.InPar (d 0) p := by
  intro i j hj hi
  obtain ⟨⟨α, i'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective i
  obtain ⟨⟨β, j'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.mem_parab_iff] at hp
  cases β using Fin.cases with
  | zero =>
    cases α using Fin.cases with
    | zero =>
      rw [sv0] at hi
      exact absurd i'.isLt (by omega)
    | succ c => exact hp _ _ _ _ (Fin.succ_pos c)
  | succ c =>
    rw [svS d hd hb] at hj
    omega

private theorem brG_entry {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (hn : n = d 0 + b) (p : GL (Fin n) F)
    (h : GlobalTheory.Shin.InPar (d 0) p) (c c' : Fin s) (i : Fin (d c.succ)) (j : Fin (d c'.succ)) :
    ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c', j⟩) =
      (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c'.succ, j⟩) := by
  unfold GlobalTheory.Shin.brG
  rw [toG_coe (units_of hn p h).2]
  exact br_entry _ _ _ _ _ (svS d hd hb c i) (svS d hd hb c' j)

end ParConsAux

theorem UpperTheory.Gal.InertialTypesAlt.parCons :
    ParCons := by
  intro F _ s n d hd b hb p
  have hn : n = d 0 + b := by rw [← hd, ← hb, Fin.sum_univ_succ]
  refine ⟨⟨fun hp => ⟨inPar_of d hd hb p hp, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩, fun hp hp' => ⟨?_, fun c => ?_⟩⟩
  · have h1 := inPar_of d hd hb p hp
    rw [GlobalTheory.SmGL.mem_parab_iff] at hp ⊢
    intro c c' i j hc
    rw [brG_entry d hd hb hn p h1]
    exact hp _ _ _ _ (Fin.succ_lt_succ_iff.2 hc)
  · rw [GlobalTheory.SmGL.mem_parab_iff] at h2 ⊢
    intro α β i j hαβ
    cases α using Fin.cases with
    | zero => exact absurd hαβ (Fin.not_lt_zero _)
    | succ c =>
      cases β using Fin.cases with
      | zero =>
        apply h1
        · rw [sv0]; exact j.isLt
        · rw [svS d hd hb]; omega
      | succ c' =>
        rw [← brG_entry d hd hb hn p h1]
        exact h2 _ _ _ _ (Fin.succ_lt_succ_iff.1 hαβ)
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩)
      (GlobalTheory.SmGL.stdBlocks d hd ⟨0, j⟩) = _
    unfold GlobalTheory.Shin.tlG
    rw [toG_coe (units_of hn p h1).1]
    exact (tl_entry _ _ _ _ _ (sv0 d hd i) (sv0 d hd j)).symm
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, j⟩) =
      ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, j⟩)
    rw [brG_entry d hd hb hn p h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPolTop
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem polTop_sum (q : ℕ) (hq : 2 ≤ q) (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, p.1 = 1) :
    (L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (q - 1)))).sum =
      ((L.map fun p => (p.1, ((p.2 : ℕ) : ZMod (q - 1))) : List _) : Multiset _) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have h1 : p.1 = 1 := hL p (by simp)
    have hpos : 0 < q - 1 := by omega
    rw [List.map_cons, List.sum_cons, ih (fun r hr => hL r (List.mem_cons_of_mem _ hr)), List.map_cons,
      h1]
    simp [Nat.div_self hpos]

theorem UpperTheory.Gal.InertialTypesAlt.polTop :
    PolTop := by
  intro b x hq hL hx
  have hpos : 0 < b.q - 1 := by omega
  have hb : b.blocks b.q = ((b.D ++ b.L).map fun p => (p.1, ((p.2 : ℕ) : ZMod (b.q - 1))) : List _) := by
    unfold Lbl.blocks
    rw [polTop_sum b.q hq b.L hL, List.map_append, ← Multiset.coe_add]
    simp [Nat.div_self hpos]
  refine ⟨hb, ?_⟩
  unfold Lbl.pol
  rw [hb, Multiset.map_coe, Multiset.prod_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  rw [ZMod.val_natCast, ← pow_eq_pow_mod p.2 hx]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PStepInert
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem card_eq_pow_finrank {F F' : Type} [Field F] [Field F'] [Finite F'] (m : Module F F') :
    Nat.card F' = Nat.card F ^ @Module.finrank F F' _ _ m := by
  letI := m
  exact Module.natCard_eq_pow_finrank

private theorem finrank_module_unique {F F' : Type} [Field F] [Field F'] [Finite F] [Finite F'] (m₁ m₂ : Module F F') :
    @Module.finrank F F' _ _ m₁ = @Module.finrank F F' _ _ m₂ :=
  Nat.pow_right_injective (Finite.one_lt_card (α := F))
    ((card_eq_pow_finrank m₁).symm.trans (card_eq_pow_finrank m₂))

theorem UpperTheory.Gal.InertialTypesAlt.stepInert :
    FinTrace → StableOf → ResEmbCompat → ResDeg → LiftOk → JDEq → ∀ P₀, KillsOn P₀ → StepAt P₀ Not := by
  intro hFT hSt hRE hRD hLO hJD P₀ hK K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hl n hn π P hW A Θ hΘ v w hs hu e e' he he'
    τ τ' hτ hτ' a hPa hL
  obtain ⟨hOk, hq, hna, hMeets⟩ := hL
  obtain ⟨r, j, hr, hj, hje⟩ := hRE K M Ω A v w e e' he he'
  letI := r.toAlgebra
  obtain ⟨hfr, s, hsf⟩ := hRD K M hl v w hs hu
  have hfr' : @Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule = Module.finrank K M :=
    (finrank_module_unique _ _).trans hfr
  have hl' : (@Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule).Prime := by
    rw [hfr']
    exact hl
  let ι : AlgebraicClosure 𝓀[v.adicCompletion K] →ₐ[𝓀[v.adicCompletion K]] AlgebraicClosure 𝓀[w.1.adicCompletion M] :=
    { j.toRingHom with
      commutes' := fun x => by
        show j (algebraMap _ _ x) = _
        rw [hj x, IsScalarTower.algebraMap_apply 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M]
          (AlgebraicClosure 𝓀[w.1.adicCompletion M]) x]
        rfl }
  let θ' : AlgebraicClosure 𝓀[w.1.adicCompletion M] →* ℂ := Θ.comp e'.toMonoidHom
  have hθ' : Inj θ' := fun x y hx hy h =>
    e'.injective (hΘ _ _ (fun h0 => hx (e'.injective (by simpa using h0)))
      (fun h0 => hy (e'.injective (by simpa using h0))) h)
  have hpull : pullθ ι θ' = Θ.comp e.toMonoidHom := by
    ext x
    show Θ (e' (j x)) = Θ (e x)
    rw [hje]
  rw [← hpull] at hMeets
  subst hna
  have hlift := hLO a _ hl' hOk
  refine ⟨a.lift (@Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule),
    Relation.ReflTransGen.single ⟨_, hl', rfl⟩, hlift.1, ?_, hlift.2.symm, ?_⟩
  · show a.q ^ _ = _
    rw [hq]
    exact (card_eq_pow_finrank _).symm
  · intro hz
    have hf : IsCl fun g => star (JD (pullθ ι θ') a.D a.L a.rk g) := fun x y => by
      show star _ = star _
      rw [(hJD _ (pullθ ι θ')).2.2 a.D a.L a.rk x y]
    have hTr := hFT K M hl a.rk hn π P (hSt K M hl a.rk hn π P hW).1 hW v w hs hu τ τ' hτ hτ' hr s hsf _ hf hMeets
    have hstar : ∀ δ, shLift s (fun g => star (JD (pullθ ι θ') a.D a.L a.rk g)) δ =
        star (shLift s (JD (pullθ ι θ') a.D a.L a.rk) δ) := fun δ => by
      unfold shLift
      split_ifs <;> simp
    haveI : FiniteDimensional ℂ (fixed τ'.ρ (KOne (w.1.adicCompletion M) (Fin a.rk))) :=
      (UpperTheory.Zero.LLC.Pr.adm _ _ _ _ τ'.smooth τ'.irred).2 _ GlobalTheory.StepData.isOpen_KOne
        (levelPre_bot (k := w.1.adicCompletion M) (n := Fin a.rk) ▸ isCompact_levelPre ⊥)
    refine hTr ?_
    simp only [hstar]
    exact hK _ _ s hl' hsf ι θ' hθ' a hPa hOk hq _ (levelZero τ'.ρ) hz
end

