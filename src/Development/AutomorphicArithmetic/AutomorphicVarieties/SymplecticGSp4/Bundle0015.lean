module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.DiagonalCharacters

private def dchar {H K : Type} [Group H] [Field K] (r : H →* M4 K) (h : DiagType r) (i : Fin 4) : H →* Kˣ :=
  MonoidHom.toHomUnits
    { toFun g := r g i i
      map_one' := by simp
      map_mul' a b := by
        rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single i]
        · intro k _ hk
          by_contra h0
          exact h i k hk.symm ⟨a, left_ne_zero_of_mul h0⟩ ⟨b, right_ne_zero_of_mul h0⟩
        · simp }

private theorem dual_prod {H K : Type} [Group H] [Field K] (r : H →* M4 K) (h : DiagType r)
    (hrev : ∀ i j, Ge r i j → Ge r j.rev i.rev) (ν : K) (g : H) (hg : IsGSp ν (r g)) (i : Fin 4) :
    r g i i * r g i.rev i.rev = ν := by
  have h1 := congrFun (congrFun hg i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · have hs : sgn i * sgn i = 1 := by fin_cases i <;> rfl
    rw [adj_apply, hs, one_smul, mul_comm] at h1
    simpa using h1
  · intro k _ hk
    by_contra h0
    have h2 : r g k.rev i.rev ≠ 0 := fun e => by
      rw [adj_apply, e, smul_zero, zero_mul] at h0
      exact h0 rfl
    exact h _ _ (fun e => hk (Fin.rev_injective e)) ⟨g, h2⟩ (hrev k i ⟨g, right_ne_zero_of_mul h0⟩)
  · simp

private theorem match_chars {H K : Type} [Group H] [Field K] (a b : Fin 4 → H →* K) (hb : Function.Injective b)
    (h : ∀ g, ∑ i, a i g = ∑ j, b j g) : ∃ m : Fin 4 → Fin 4, Function.Injective m ∧ ∀ i, a i = b (m i) := by
  classical
  have key : ∀ j, ∃ i, a i = b j := by
    intro j
    by_contra hn
    push Not at hn
    have li := linearIndependent_monoidHom H K
    rw [linearIndependent_iff_injective_finsuppLinearCombination] at li
    have h1 : (∑ i, Finsupp.single (a i) (1 : K)) = ∑ j, Finsupp.single (b j) (1 : K) := by
      apply li
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finsupp.linearCombination_single, one_smul]
      funext g
      simpa using h g
    have h2 := congrArg (fun f => f (b j)) h1
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, hn, hb.eq_iff] at h2
    simp at h2
  choose n hn using key
  have hinj : Function.Injective n := fun x y e => hb (by rw [← hn x, ← hn y, e])
  let e := Equiv.ofBijective n (Finite.injective_iff_bijective.1 hinj)
  refine ⟨e.symm, e.symm.injective, fun i => ?_⟩
  rw [← hn]
  exact congrArg a (e.apply_symm_apply i).symm

private theorem perm_cases (m : Fin 4 → Fin 4) (h1 : Function.Injective m) (h2 : ∀ i, lamW i = lamW (m i))
    (h3 : ∀ i, m i.rev = (m i).rev) : m = id ∨ m = ![2, 3, 0, 1] := by
  have key : ∀ a b c d : Fin 4, a ≠ c → lamW 0 = lamW a → lamW 2 = lamW c → d = a.rev → b = c.rev →
      (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 0 ∧ d = 1) := by decide
  rcases key (m 0) (m 1) (m 2) (m 3) (h1.ne (by decide)) (h2 0) (h2 2) (h3 0) (h3 2) with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · left; funext i; fin_cases i <;> assumption
  · right; funext i; fin_cases i <;> assumption

private theorem open_ker {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [TopologicalSpace K] [T2Space K]
    [ContinuousMul K] (δ : G ℚ Ω →* Kˣ) (hc : Continuous fun g => (δ g : K)) (N : ℕ) (hN : N ≠ 0)
    (h : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) A, δ g ^ N = 1) : IsOpen (δ.ker : Set (G ℚ Ω)) := by
  have hcl : IsClosed ((δ ^ N).ker : Set (G ℚ Ω)) := by
    have : ((δ ^ N).ker : Set (G ℚ Ω)) = {g | (δ g : K) ^ N = 1} := by
      ext g
      simp [MonoidHom.mem_ker, Units.ext_iff]
    rw [this]
    exact isClosed_eq (hc.pow N) continuous_const
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨(δ ^ N).ker, hcl⟩
  have htop : ∀ g, δ g ^ N = 1 := by
    intro g
    have : g ∈ (δ ^ N).ker := by
      have key' : (δ ^ N).ker = _ := key
      rw [key', Subgroup.mem_sInf]
      rintro U ⟨hU, hle⟩
      have hle' : (δ ^ N).ker ≤ U := hle
      have hn : U.Normal := Subgroup.Normal.of_commutator_le _ ((Abelianization.commutator_subset_ker _).trans hle')
      rw [B3.minkowski Ω U hn hU fun B x hx => hle' (h B x hx)]
      trivial
    exact this
  have hfin : Finite δ.range := by
    haveI : NeZero N := ⟨hN⟩
    have hle : δ.range ≤ rootsOfUnity N K := by
      rintro _ ⟨g, rfl⟩
      exact htop g
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  haveI : δ.ker.FiniteIndex := Subgroup.finiteIndex_ker δ
  refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
  have : (δ.ker : Set (G ℚ Ω)) = {g | (δ g : K) = 1} := by
    ext g
    simp [MonoidHom.mem_ker]
  rw [this]
  exact isClosed_eq hc continuous_const

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem residue_eq {l : ℕ} [Fact l.Prime] (c : Coef l) (a b : c.O) (h : ‖(a : PadicAlgCl l) - b‖ < 1) :
    residue c.O a = residue c.O b := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h3 : ‖((u⁻¹ : c.Oˣ) : c.O).1‖ ≤ 1 :=
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) _).map c.O.val)
  have h2 : ‖((u : c.O) : PadicAlgCl l)‖ < 1 := by rw [hu]; exact h
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem perm (D : Raw Ω c) (hD : D.Good) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r) (hd : DiagType r) :
    ∃ m : Fin 4 → Fin 4, (m = id ∨ m = ![2, 3, 0, 1]) ∧
      ∀ i, ∀ s ∈ D.Ip l, r s i i = ((D.ps (m i) s : c.O) : PadicAlgCl l) := by
  obtain ⟨-, f2, -, -, -, f6, f7, -⟩ := facts D hD
  obtain ⟨p1, -, -, -, -, p6, -⟩ := ptIn D hD _ r hr
  obtain ⟨-, -, -, g4, -⟩ := geAlg _ r _ p1 p6
  obtain ⟨-, e2, -⟩ := eptInt D hD r hr
  have hon : Loc.PtOn D D.condL (r.comp (D.Gp l).subtype) := by
    obtain ⟨R, i1, i2, i3, ρ, y, hρ, rfl⟩ := hr
    exact ⟨R, i1, i2, i3, D.loc ρ l, y, hρ.atL, rfl⟩
  obtain ⟨u, κ, k1, k2, k3, -⟩ := Loc.spPtL D hD _ hon
  have hs0 : (D.s0 : G ℚ Ω) ∈ D.Ip l := hD.decompSigma_mem.1.1
  have f7' : Function.Injective fun i => ((D.ps i D.s0 : c.O) : PadicAlgCl l) := Subtype.val_injective.comp f7
  obtain ⟨m, m1, m2⟩ := match_chars
    (fun i => (Units.coeHom _).comp ((dchar r hd i).comp (D.Gp l).subtype)) (fun j => (Units.coeHom _).comp (κ j))
    (fun i j e => f7' (by
      have := DFunLike.congr_fun e D.s0
      exact (k2 i _ hs0).symm.trans (this.trans (k2 j _ hs0))))
    (fun g => by
      have h1 : ((u⁻¹ : (M4 (PadicAlgCl l))ˣ) * r g * u : M4 (PadicAlgCl l)).trace = (r g).trace := by
        rw [Matrix.trace_mul_cycle, Units.mul_inv, one_mul]
      exact h1.symm.trans (Finset.sum_congr rfl fun j _ => (k1 g).2 j))
  have m3 : ∀ i (g : D.Gp l), r g i i = κ (m i) g := fun i g => DFunLike.congr_fun (m2 i) g
  have m4 : ∀ i, ∀ s ∈ D.Ip l, r s i i = ((D.ps (m i) s : c.O) : PadicAlgCl l) := fun i s hs =>
    (m3 i ⟨s, Ine_le_Dec _ hs⟩).trans (k2 _ _ hs)
  refine ⟨m, perm_cases m m1 (fun i => ?_) (fun i => f7' ?_), m4⟩
  · obtain ⟨a1, -, a3⟩ := f2 l (Finset.mem_insert_self _ _)
    by_contra hne
    refine a3 _ _ hne (residue_eq c _ _ ?_)
    have b1 : ‖r (D.sg l) i i - ((D.ps i (D.sg l) : c.O) : PadicAlgCl l)‖ < 1 := by
      have := e2 (D.sg l) i i
      rwa [Raw.r0E, mapRep_apply, Raw.r0, show diagRep D.ps (D.sg l) i i = D.ps i (D.sg l) from Matrix.diagonal_apply_eq _ i] at this
    have b2 : ‖r (D.sg l) i i - ((D.ps (m i) (D.sg l) : c.O) : PadicAlgCl l)‖ < 1 := by
      rw [m3 i ⟨_, a1⟩]; exact k3 _ _
    rw [norm_sub_rev] at b1
    rw [← sub_add_sub_cancel _ (r (D.sg l) i i)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt b1 b2)
  · have h1 := dual_prod r hd g4 _ _ (p1 D.s0) i
    rw [m4 _ _ hs0, m4 _ _ hs0, ← f6 (m i)] at h1
    have h0 : ((D.ps (m i) D.s0 : c.O) : PadicAlgCl l) ≠ 0 :=
      ((D.ps (m i) D.s0).isUnit.map (algebraMap c.O (PadicAlgCl l))).ne_zero
    exact mul_left_cancel₀ h0 h1

end UpperTheory.V.GradeZeroInterpolatingElement.DiagonalCharacters

open UpperTheory.V.GradeZeroInterpolatingElement.DiagonalCharacters in
theorem UpperTheory.V.GradeZeroInterpolatingElement.diagChar :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → DiagType r → ∃ (κ : Fin 4 → G ℚ Ω →* (PadicAlgCl l)ˣ) (m : Fin 4 → Fin 4), (∀ i g, (κ i g : PadicAlgCl l) = r g i i) ∧ (m = id ∨ m = ![2, 3, 0, 1]) ∧ (∀ i, ∀ s ∈ D.Ip l, r s i i = ((D.ps (m i) s : c.O) : PadicAlgCl l)) ∧ ∀ i, ∃ δ : G ℚ Ω →* (PadicAlgCl l)ˣ, IsOpen (δ.ker : Set (G ℚ Ω)) ∧ ∀ g, r g i i = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ D.wts4 (m i) * δ g := by
  intro Ω _ _ _ l hl c D hD r hr hd
  obtain ⟨m, m1, m2⟩ := perm D hD r hr hd
  refine ⟨dchar r hd, m, fun _ _ => rfl, m1, m2, fun i => ?_⟩
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨f1, -, -, f4, -, -, -, -, -, -, -, f12, f13, -⟩ := facts D hD
  obtain ⟨-, p2, -, -, p5, -⟩ := ptIn D hD _ r hr
  obtain ⟨e1, -⟩ := eptInt D hD r hr
  set δ : G ℚ Ω →* (PadicAlgCl l)ˣ := (chiO ℚ Ω l (PadicAlgCl l) ^ D.wts4 (m i))⁻¹ * dchar r hd i with hδ
  have hne : ∀ g, algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ D.wts4 (m i) ≠ 0 := fun g =>
    pow_ne_zero _ ((cycZ ℚ Ω l g).isUnit.map _).ne_zero
  have hval : ∀ g, (δ g : PadicAlgCl l) =
      (algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ D.wts4 (m i))⁻¹ * r g i i := fun g => by
    rw [hδ, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val]
    rfl
  refine ⟨δ, ?_, fun g => by rw [hval, mul_inv_cancel_left₀ (hne g)]⟩
  have hf : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)) := by
    refine ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val).congr fun x => ?_
    exact (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x).symm
  have hc : Continuous fun g => (δ g : PadicAlgCl l) := by
    simp only [hval]
    exact (((hf.comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))).pow _).inv₀ hne).mul (e1.matrix_elem i i)
  let U : Subgroup (G ℚ Ω) := D.rbar.ker ⊓ (D.ψ.ker ⊓ D.om.ker)
  have hU : IsOpen (U : Set (G ℚ Ω)) := f12.inter (hD.psi_open.inter f13)
  haveI : Finite (G ℚ Ω ⧸ U) := U.quotient_finite_of_isOpen hU
  have hI : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, r g = 1 → δ g = 1 :=
    fun A hA g hg h1 => Units.ext (by
      rw [hval, MonoidHom.mem_ker.1 ((places ℚ Ω l A).2.2.2 hA hg), h1]
      simp)
  have hT : ∀ p ∈ D.T, p.Prime ∧ ∀ g ∈ D.Ip p, g ∈ U → δ g = 1 := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · refine ⟨hl.out, fun g hg hu => Units.ext ?_⟩
      rw [hval, m2 i g hg, f4 (m i) g ⟨⟨hg, hu.2.1⟩, hu.2.2⟩, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
      exact inv_mul_cancel₀ (hne g)
    · obtain ⟨q1, q2, -⟩ := f1 p hp
      refine ⟨q1, fun g hg hu => hunr (D.pl p) (fun hv => ?_) g hg ((p5 p hp).2 ⟨g, Ine_le_Dec _ hg⟩ ⟨hg, hu.2.1⟩)⟩
      have hv' := hD.pl_over p q1
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes q1 hl.out).2 q2)
      have h1 : (a : Ω) * p + (b : Ω) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
      have h2 : ∀ (z : ℤ) (y : Ω), (D.pl p).valuation y < 1 → (D.pl p).valuation (z * y) < 1 := fun z y hy => by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (((D.pl p).valuation_le_one_iff _).2 (intCast_mem _ z))) hy
      have h3 := (D.pl p).valuation.map_add_lt (h2 a _ hv') (h2 b _ hv)
      rw [h1, map_one] at h3
      exact lt_irrefl _ h3
  refine open_ker δ hc U.index hI fun A g hg => ?_
  by_cases hA : Raw.Away D.T A
  · rw [← map_pow]
    exact hunr A (hA l (Finset.mem_insert_self _ _)) _ (pow_mem hg _) (p2 A hA _ (pow_mem hg _) (U.pow_index_mem g).1)
  · simp only [Raw.Away, not_forall, not_not] at hA
    obtain ⟨p, hp, hv⟩ := hA
    obtain ⟨t, ht⟩ := (B3.placesQ Ω).2.2 p (D.pl p) A (hT p hp).1 (hD.pl_over p (hT p hp).1) hv
    have h1 := (hT p hp).2 _ (pow_mem (ht g hg) _) (U.pow_index_mem _)
    rw [map_pow, map_mul, map_mul, map_inv, inv_mul_cancel_comm] at h1
    exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LevBasis
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem lev_basis {ι k : Type} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (X : ι → Matrix (Fin n) (Fin n) k)
    (hc : ∀ a b, Commute (X a) (X b)) (hf : ∀ a, IsOfFinOrder (X a)) :
    ∃ (P : GL (Fin n) k) (d : ι → Fin n → k), ∀ a, X a * P = P * Matrix.diagonal (d a) := by
  classical
  let f : ι → Module.End k (Fin n → k) := fun a => Matrix.toLinAlgEquiv' (X a)
  have hss : ∀ a, (f a).IsFinitelySemisimple := fun a => by
    obtain ⟨m, hm, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 (hf a)
    refine (Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (1 : k) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero).squarefree ?_).isFinitelySemisimple
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, f]
    rw [← map_pow, h1, map_one, sub_self]
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun a b _ => (hc a b).map _) fun a => Module.End.iSup_maxGenEigenspace_eq_top _
  simp only [fun a => (hss a).maxGenEigenspace_eq_eigenspace] at htop
  let S : Set (Fin n → k) := {v | ∃ d : ι → k, ∀ a, (X a).mulVec v = d a • v}
  have hS : Submodule.span k S = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun d v hv => Submodule.subset_span ⟨d, fun a => ?_⟩
    exact Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent k S
  let b₀ : Module.Basis t k (Fin n → k) := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hS])
  let b := b₀.reindex (b₀.indexEquiv (Pi.basisFun k (Fin n)))
  have hb : ∀ i, b i ∈ S := fun i => by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact ht (Subtype.coe_prop _)
  choose d hd using hb
  haveI := (Pi.basisFun k (Fin n)).invertibleToMatrix b
  refine ⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix b), fun a i => d i a, fun a => ?_⟩
  ext i j
  have := congrFun (hd j a) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mul_diagonal]
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, this, mul_comm]

private theorem lev_diag {Γ A k : Type} [Group Γ] [CommGroup A] [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (φ : Γ →* A) (hφ : ∀ s, IsOfFinOrder (φ s))
    (hr : ∀ s ∈ H, φ s = 1 → r s = 1) :
    ∃ χ : Fin n → Γ →* kˣ, (∀ i s, φ s = 1 → χ i s = 1) ∧ Af.IsDiagOn r H χ := by
  obtain ⟨P, d, hP⟩ := lev_basis (fun s : H => (r s : Matrix (Fin n) (Fin n) k)) (fun a b => by
      have h := hr ((a : Γ) * b * ((b : Γ) * a)⁻¹) (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) (by
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (φ a), mul_inv_cancel])
      rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h
      exact congrArg Units.val h) fun a => by
    obtain ⟨m, hm, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 (hφ a)
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hr _ (pow_mem a.2 m) (by rw [map_pow, h1]), Units.val_one]
  have hd : ∀ s : H, ((P⁻¹ * r s * P : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (d s) := fun s => by
    rw [Units.val_mul, Units.val_mul, mul_assoc, hP, Units.inv_mul_cancel_left]
  let κ : Fin n → H →* kˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun s => d s i
      map_one' := by simpa using (congrFun (congrFun (hd 1) i) i).symm
      map_mul' := fun s t => by
        have h : (P⁻¹ * r (s * t : H) * P : GL (Fin n) k) = (P⁻¹ * r s * P) * (P⁻¹ * r t * P) := by
          rw [Subgroup.coe_mul, map_mul]
          group
        have h1 := hd (s * t)
        rw [h, Units.val_mul, hd, hd, Matrix.diagonal_mul_diagonal] at h1
        simpa using (congrFun (congrFun h1 i) i).symm }
  have hsurj := (φ.comp H.subtype).rangeRestrict_surjective
  have hker : ∀ i, (φ.comp H.subtype).rangeRestrict.ker ≤ (κ i).ker := fun i s hs => by
    have h1 := hd s
    rw [hr s s.2 (congrArg Subtype.val hs), mul_one, inv_mul_cancel] at h1
    apply Units.ext
    show d s i = 1
    simpa using (congrFun (congrFun h1 i) i).symm
  choose χ hχ using fun i => GlobalTheory.PrimaryCharacter.exists_extend_of_injective (φ.comp H.subtype).range.subtype
    (Subgroup.subtype_injective _) ((φ.comp H.subtype).rangeRestrict.liftOfSurjective hsurj ⟨κ i, hker i⟩)
  refine ⟨fun i => (χ i).comp φ, fun i s hs => by rw [MonoidHom.comp_apply, hs, map_one], P⁻¹, fun s hs => ?_⟩
  rw [inv_inv, hd ⟨s, hs⟩]
  congr 1
  funext i
  have h := hχ i ((φ.comp H.subtype).rangeRestrict ⟨s, hs⟩)
  rw [MonoidHom.liftOfRightInverse_comp_apply] at h
  exact (congrArg Units.val h).symm

private theorem lev_place {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨p1, p2, p3, -⟩ := places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

open Matrix in
private theorem lev_dual {k : Type} [Field k] : ∃ P : GL (Fin 4) k, ∀ (ν : k) (X : M4 k), IsGSp ν X →
    Xᵀ * (P : M4 k) * X = ν • (P : M4 k) := by
  let J : M4 k := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  have hJ : J * -J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_four]
  refine ⟨⟨J, -J, hJ, by rw [neg_mul, ← mul_neg, hJ]⟩, fun ν X h => ?_⟩
  have h1 : Xᵀ * J = J * adj X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]
  show Xᵀ * J * X = ν • J
  rw [h1, mul_assoc, h, Matrix.mul_smul, mul_one]

theorem UpperTheory.V.GradeZeroInterpolatingElement.level :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ r, D.EPt r → Af.Level l N ![(D.e : ℤ) + 1, D.e, 1, 0] r.toHomUnits ∧ ∃ θ, Af.IsCycWt l ((D.e : ℤ) + 1) θ ∧ Af.DualTw r.toHomUnits θ ∧ ∀ g, (θ g : PadicAlgCl l) = ((D.th g : c.O) : PadicAlgCl l) := by
  intro Ω _ _ _ l hl c D hD N hN hψ hξ hom r hr
  obtain ⟨hmult, hunr, -, -, hP, -⟩ := ptIn D hD _ r hr
  have hcont := (eptInt D hD r hr).1
  let m : c.Oˣ →* (PadicAlgCl l)ˣ := Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom
  have hcyc : ∀ s : G ℚ Ω, GlobalTheory.GalOfCusp.cycBar ℚ Ω l s = m (chiO ℚ Ω l c.O s) := fun s => Units.ext rfl
  let χ₀ : Fin 4 → G ℚ Ω →* c.Oˣ := ![D.om⁻¹ * D.ξ * D.ψ, D.ψ, D.om⁻¹ * D.ξ, 1]
  have hχ₀ : ∀ i s, D.ψ s = 1 → D.ξ s = 1 → D.om s = 1 → χ₀ i s = 1 := fun i s h1 h2 h3 => by
    fin_cases i <;> simp [χ₀, h1, h2, h3]
  have hps : ∀ i s, D.ps i s = chiO ℚ Ω l c.O s ^ (![(D.e : ℤ) + 1, D.e, 1, 0] i) * χ₀ i s := fun i s => by
    fin_cases i <;> simp [χ₀, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, zpow_add_one, mul_comm, mul_left_comm, mul_assoc]
  have hK : ∀ i, Af.KillsMu N (m.comp (χ₀ i)) := fun i s hs => by
    rw [MonoidHom.comp_apply, hχ₀ i s (hψ s hs) (hξ s hs) (hom s hs), map_one]
  refine ⟨⟨?_, fun w hw => ?_, fun w hw => ?_⟩, m.comp D.th, ⟨N, m.comp (χ₀ 0), hN, hK 0, ?_⟩, ?_, fun _ => rfl⟩
  · exact Units.continuous_iff.2 ⟨hcont, hcont.comp continuous_inv⟩
  · let φ := D.ψ.prod (D.ξ.prod D.om)
    have hφ : ∀ s, IsOfFinOrder (φ s) := fun s => by
      haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.psi_open
      haveI : Finite (G ℚ Ω ⧸ D.ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.xi_open
      refine IsOfFinOrder.prod_mk ?_ (IsOfFinOrder.prod_mk ?_ ?_)
      · exact (QuotientGroup.kerLift D.ψ).isOfFinOrder (isOfFinOrder_of_finite (s : G ℚ Ω ⧸ D.ψ.ker))
      · exact (QuotientGroup.kerLift D.ξ).isOfFinOrder (isOfFinOrder_of_finite (s : G ℚ Ω ⧸ D.ξ.ker))
      · exact isOfFinOrder_iff_pow_eq_one.2 ⟨l - 1, Nat.sub_pos_of_lt hl.out.one_lt, DFunLike.congr_fun hD.om_pow s⟩
    obtain ⟨A, hA, h⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∀ s ∈ Ine (F := ℚ) A, φ s = 1 → r s = 1 := by
      obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
      by_cases hT : Raw.Away D.T B
      · refine ⟨B, hB, fun s hs h1 => hunr B hT s hs ?_⟩
        have h2 : cycZ ℚ Ω l s = 1 := (places ℚ Ω l B).2.2.2 (hT l (Finset.mem_insert_self _ _)) hs
        have h3 : ∀ i, D.ps i s = 1 := fun i => by
          rw [hps, hχ₀ i s (congrArg Prod.fst h1) (congrArg (·.2.1) h1) (congrArg (·.2.2) h1), chiO, MonoidHom.comp_apply, h2,
            map_one, one_zpow, mul_one]
        have h4 : D.r0 s = 1 := by
          show Matrix.diagonal (fun i => (D.ps i s : c.O)) = 1
          simp only [h3, Units.val_one, Matrix.diagonal_one]
        show (residue c.O).mapMatrix (D.r0 s) = 1
        rw [h4, map_one]
      · obtain ⟨p, hp, hB'⟩ : ∃ p ∈ D.T, B.valuation (p : Ω) < 1 := by simpa [Raw.Away] using hT
        have hpw : (p : 𝓞 ℚ) ∈ w.asIdeal := (hB _).1 (by simpa using hB')
        have hpb : p ∈ D.Sb := (Finset.mem_insert.1 hp).resolve_left fun e => hw (e ▸ hpw)
        have hpp := ((facts D hD).1 p hpb).1
        exact ⟨D.pl p, lev_place hpp (hD.pl_over p hpp) hpw, fun s hs h1 =>
          (hP p hpb).2 ⟨s, hs.1⟩ ⟨hs, congrArg Prod.fst h1⟩⟩
    obtain ⟨χ, h1, h2⟩ := lev_diag r.toHomUnits (Ine (F := ℚ) A) φ hφ fun s hs e => Units.ext (h s hs e)
    exact ⟨A, hA, χ, fun i s hs => h1 i s (Prod.ext (hψ s hs) (Prod.ext (hξ s hs) (hom s hs))), h2⟩
  · obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
    obtain ⟨h, κ, hF, h1, -, -, -, h2⟩ := UpperTheory.V.Loc.spPtL D hD
      ((mapRep (y : R →+* PadicAlgCl l) ρ.hom).comp (D.Gp l).subtype)
      ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩
    refine ⟨D.pl l, lev_place hl.out (hD.pl_over l hl.out) hw, fun i => m.comp (χ₀ i), κ, hK, ⟨h⁻¹, fun s => ?_⟩,
      fun i s hs => ?_, Or.inl fun i j hij => ?_⟩
    · rw [inv_inv]
      exact hF s
    · have e : κ i s = m (D.ps i s) := Units.ext (h1 i s hs)
      rw [e, hps, map_mul, map_zpow, hcyc]
      rfl
    · by_cases e : i = j
      · subst e
        have h3 := DFunLike.congr_fun hij D.s0
        rw [MonoidHom.mul_apply, left_eq_mul] at h3
        have h4 : cycZ ℚ Ω l D.s0 = 1 := by
          refine Units.ext (Subtype.val_injective ((algebraMap ℚ_[l] (PadicAlgCl l)).injective ?_))
          exact (congrArg Units.val h3).trans (map_one _).symm
        exact hD.decompSigma_ord (h4 ▸ IsOfFinOrder.one)
      · obtain ⟨g, -, hg⟩ := h2 i j e ⊤ isOpen_univ
          ⟨⟨D.sg l, ((facts D hD).2.1 l (Finset.mem_insert_self _ _)).1⟩, trivial, rfl⟩
        exact hg (congrArg Units.val (DFunLike.congr_fun hij g))
  · ext s : 1
    have e : D.th s = _ := hps 0 s
    rw [MonoidHom.comp_apply, e, map_mul, map_zpow, ← hcyc]
    rfl
  · obtain ⟨P, hP⟩ := lev_dual (k := PadicAlgCl l)
    exact ⟨P, fun s => hP _ _ (hmult s)⟩
end

