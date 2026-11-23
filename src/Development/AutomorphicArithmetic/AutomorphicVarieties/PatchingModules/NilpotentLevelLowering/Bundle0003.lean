module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.OpTransport
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ot_inv {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') (hi : Function.Injective e.p) :
    ∃ k : G'.Hom G, ∀ g, k.p (e.p g) = g := by
  let eq : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hi, e.surj⟩
  have hk : ∀ x, e.p (eq.symm x) = x := fun x => eq.apply_symm_apply x
  have hcont : Continuous (eq.symm : G'.Γ → G.Γ) :=
    (Continuous.homeoOfEquivCompactToT2 (f := eq.toEquiv) e.cont).symm.continuous
  refine ⟨Glob.Hom.mk eq.symm.toMonoidHom hcont eq.symm.surjective (fun g => ?_) ?_ (fun g => ?_)
    (fun v g => ?_) (fun v g => ?_), fun g => eq.symm_apply_apply g⟩
  · show G.η (eq.symm g) = G'.η g
    rw [← e.η, hk]
  · show eq.symm G'.c = G.c
    apply hi
    rw [hk, e.c]
  · show G.ε (eq.symm g) = G'.ε g
    rw [← e.ε, hk]
  · show eq.symm _ = _
    apply hi
    rw [hk, e.φ]
  · show eq.symm _ = _
    apply hi
    rw [hk, e.φu]

private theorem ot_tr_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (y : MonoidAlgebra A H) : (D.comap φ).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A φ y) := by
  have key : ∀ z : MonoidAlgebra A H, MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.mapRingHom H Polynomial.C z) =
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom A φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | single m r => simp [MonoidAlgebra.mapRingHom_single]
  show (-1) ^ 1 * ((D.D (Polynomial A)) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C y))).coeff (n - 1) =
    (-1) ^ 1 * ((D.D (Polynomial A)) (MonoidAlgebra.single 1 Polynomial.X -
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom A φ y))).coeff (n - 1)
  rw [map_sub, key]
  simp

private theorem ot_comap_comap {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [Group K] (D : GDet n A G)
    (φ : H →* G) (ψ : K →* H) : (D.comap φ).comap ψ = D.comap (φ.comp ψ) := by
  apply GDet.ext
  intro B _ _ x
  show (D.D B) (MonoidAlgebra.mapDomainRingHom B φ (MonoidAlgebra.mapDomainRingHom B ψ x)) =
    (D.D B) (MonoidAlgebra.mapDomainRingHom B (φ.comp ψ) x)
  rw [MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

private theorem ot_single {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (a : A) :
    MonoidAlgebra.mapDomainRingHom A φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) a := by simp

private theorem mapDomain_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (u : Fin n → A) :
    MonoidAlgebra.mapDomainRingHom A φ (q1El g u) = q1El (φ g) u := by
  simp only [q1El, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, ot_single, map_one]

private theorem mapDomain_partial_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g t : H) (u : Fin n → A)
    (i : Fin n) (y : A) : MonoidAlgebra.mapDomainRingHom A φ (q2El g t u i y) = q2El (φ g) (φ t) u i y := by
  simp only [q2El, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, ot_single, apply_ite,
    map_one]

private theorem ot_pair {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (k : G'.Hom G) {O : Type} [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid G.frame O n} {r' : Resid G'.frame O n} (hc : Glob.Compat k r' r)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) :
    ∃ p' : Pair r' R, p'.D = p.D.comap k.p₀ ∧ p'.ψ = p.ψ := by
  let fh : FHom G'.frame G.frame :=
    { π := k.p, π_cont := k.cont, hη := k.η, hc := k.c, hε := k.ε, vl := id,
      gv := fun _ => MonoidHom.id _, gv_cont := fun _ => continuous_id,
      hφ := fun v g => (k.φ v g).symm, hI := fun _ _ hg => hg }
  have hπ : fh.π₀ = k.p₀ := rfl
  obtain ⟨h1, h2, h3⟩ := hc
  have hfc : fh.Compat r' r := by
    refine ⟨fun i => by rw [hπ]; exact h1 i, fun v i => ?_, fun v i g hg => ?_, fun u g hg => ?_⟩
    · rw [h2]
      rfl
    · rw [h3]
      rfl
    · right
      refine ⟨u, ?_⟩
      obtain ⟨hgI, hgk⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hgI
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        exact Subtype.ext (k.φu u x).symm
      · rw [Subgroup.mem_iInf] at hgk ⊢
        intro i
        have := hgk i
        rw [MonoidHom.mem_ker, h1 i] at this
        rw [MonoidHom.mem_ker, hπ]
        exact this
  obtain ⟨p', hD, hψ⟩ := exists_determinantPair_pullback l G'.frame G.frame fh O n r' r hfc
    (fun h0 => (p.isEmpty_of_zero h0).1) R p
  exact ⟨p', hD, funext fun v => funext fun i => by rw [hψ]; rfl⟩

theorem UpperTheory.V.Pa.Lev.opTransport :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (G G' : Glob l L) (e : G.Hom G') (h : G.Hom G0) (h' : G'.Hom G0) (q N : ℕ) (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ), Function.Injective e.p → (∀ g, h'.p (e.p g) = h.p g) → OpRel A Nq ph ta ex → ∃ A' : OpMod b h' q N, OpRel A' Nq (fun j => e.p₀ (ph j)) (fun j => e.p₀ (ta j)) ex := by
  intro l _ L G0 O _ _ _ _ _ n r B _ _ _ u J D b G G' e h h' q N A Nq ph ta ex hi hh hR
  obtain ⟨k, hk⟩ := ot_inv e hi
  have hek : ∀ x, e.p (k.p x) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surj x
    rw [hk]
  have hcomp : h.p₀.comp k.p₀ = h'.p₀ := MonoidHom.ext fun g => Subtype.ext (by
    show h.p (k.p (g : G'.Γ)) = h'.p (g : G'.Γ)
    rw [← hh, hek])
  have hpe : ∀ x, h'.p₀ (e.p₀ x) = h.p₀ x := fun x => Subtype.ext (hh (x : G.Γ))
  have hke : ∀ x, k.p₀ (e.p₀ x) = x := fun x => Subtype.ext (hk (x : G.Γ))
  obtain ⟨rN', hc'⟩ := Core.resPull l L G' G0 h' n O r
  have hck : Glob.Compat k rN' A.rN := by
    obtain ⟨h1, h2, h3⟩ := hc'
    obtain ⟨a1, a2, a3⟩ := A.compat
    refine ⟨fun i => ?_, h2.trans a2.symm, h3.trans a3.symm⟩
    rw [h1 i, a1 i, MonoidHom.comp_assoc, hcomp]
  obtain ⟨p', hpD, hpψ⟩ := ot_pair k hck A.p
  have hmc : ∀ {S : Type} [CommRing S] (f : A.R →+* S), (A.p.D.comap k.p₀).map f = (A.p.D.map f).comap k.p₀ :=
    fun _ => rfl
  have hlam : ∀ j : Fin D, (algebraMap (abelian₂ O Empty D) A.R) (MvPowerSeries.X (Sum.inr j)) =
      (algebraMap O A.R) (b.wt.c j) * ↑((p'.ψ (b.wt.v j) (b.wt.i j)) (b.wt.γ j)) - 1 := by
    intro j
    rw [hpψ]
    exact A.segmentWeightExponent j
  have hβ : p'.Maps A.β.toRingHom (u.D.comap h'.p₀) u.ψ := by
    refine ⟨?_, fun v i => ?_⟩
    · rw [hpD, hmc, A.β_pair.1, ot_comap_comap, hcomp]
    · rw [hpψ]
      exact A.β_pair.2 v i
  refine ⟨{ A with
              rN := rN'
              compat := hc'
              p := p'
              segmentWeightExponent := hlam
              β_pair := hβ }, ?_⟩
  refine ⟨?_, fun j g => ?_, fun j i g => ?_⟩
  · dsimp only
    simp only [hpe]
    exact hR.two
  · dsimp only
    rw [hpD, hmc, ot_tr_comap, map_mul, ot_single, mapDomain_charpoly_element]
    simp only [hke]
    exact hR.rel1 j (k.p₀ g)
  · dsimp only
    rw [hpD, hmc, ot_tr_comap, map_mul, ot_single, mapDomain_partial_charpoly_element]
    simp only [hke]
    exact hR.rel2 j i (k.p₀ g)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PairRel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_conj {K : Type} [Field K] {n : ℕ} (V : Matrix (Fin n) (Fin n) K) :
    ∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) K) (d : Fin m → Fin n → K),
      (∀ k, F k * V = V * Matrix.diagonal (d k)) →
      (List.ofFn F).prod * V = V * Matrix.diagonal (fun j => ∏ k, d k j) := by
  intro m
  induction m with
  | zero => intro F d _; simp
  | succ m ih =>
    intro F d h
    rw [List.ofFn_succ, List.prod_cons, mul_assoc, ih (fun k => F k.succ) (fun k => d k.succ) (fun k => h _),
      ← mul_assoc, h 0, mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [Fin.prod_univ_succ]

private theorem exists_diag {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K) (α : Fin n → K)
    (hα : Function.Injective α)
    (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) :
    ∃ V : Matrix (Fin n) (Fin n) K, IsUnit V ∧ P * V = V * Matrix.diagonal α :=
  _root_.UpperTheory.Reformulated.B.ExistsDiagonalization.exists_diag P α hα hP

theorem UpperTheory.V.Pa.Lev.pairRel :
    ∀ (K : Type) [Field K] (n : ℕ) (P T : Matrix (Fin n) (Fin n) K) (α β : Fin n → K), Function.Injective α → P * T = T * P → P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i)) → (∀ a : ℕ, (P ^ a * T).trace = ∑ i, α i ^ a * β i) → ∀ i, (List.ofFn fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) K)).prod * (T - β i • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
  intro K _ n P T α β hα hc hP htr i
  obtain ⟨V, hV, hPV⟩ := exists_diag P α hα hP
  obtain ⟨V', h1, h2⟩ := isUnit_iff_exists.1 hV
  obtain ⟨S, hS⟩ : ∃ S, S = V' * T * V := ⟨_, rfl⟩
  have hTV : T * V = V * S := by
    rw [hS, ← mul_assoc, ← mul_assoc, h1, one_mul]
  have hSD : Matrix.diagonal α * S = S * Matrix.diagonal α := by
    refine hV.mul_left_cancel ?_
    rw [← mul_assoc, ← hPV, mul_assoc, ← hTV, ← mul_assoc, hc, mul_assoc, hPV, ← mul_assoc, hTV,
      mul_assoc]
  have hSd : S = Matrix.diagonal (fun j => S j j) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      have := congrFun (congrFun hSD a) b
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at this
      by_contra h0
      exact hab (hα (mul_left_cancel₀ h0 this))
  have hpow : ∀ a : ℕ, P ^ a * V = V * Matrix.diagonal α ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ, mul_assoc, hPV, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have htr' : ∀ a : ℕ, ∑ j, α j ^ a * S j j = ∑ j, α j ^ a * β j := by
    intro a
    rw [← htr a]
    have e : P ^ a * T = V * (Matrix.diagonal α ^ a * S) * V' := by
      rw [← mul_assoc, ← hpow, mul_assoc (P ^ a), ← hTV, mul_assoc, mul_assoc, h1, mul_one]
    rw [e, Matrix.trace_mul_cycle, h2, one_mul, Matrix.diagonal_pow]
    simp [Matrix.trace, Matrix.diagonal_mul]
  have hβ : (fun j => S j j - β j) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hα (fun a => ?_)
    simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using htr' a
  have hSβ : S = Matrix.diagonal β := by
    rw [hSd]
    congr 1
    ext j
    exact sub_eq_zero.1 (congrFun hβ j)
  have hE := prod_conj V n
    (fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) K))
    (fun k j => if k = i then 1 else α j - α k) (by
      intro k
      by_cases hk : k = i
      · simp [hk]
      · simp only [if_neg hk]
        rw [sub_mul, hPV, smul_mul_assoc, one_mul]
        ext a b
        simp [Matrix.mul_diagonal, mul_sub, mul_comm])
  have hT : (T - β i • (1 : Matrix (Fin n) (Fin n) K)) * V = V * Matrix.diagonal (fun j => β j - β i) := by
    rw [sub_mul, hTV, hSβ, smul_mul_assoc, one_mul]
    ext a b
    simp [Matrix.mul_diagonal, mul_sub, mul_comm]
  refine hV.mul_right_cancel ?_
  rw [mul_assoc, hT, ← mul_assoc, hE, mul_assoc, Matrix.diagonal_mul_diagonal, zero_mul]
  have : (fun j => (∏ k, if k = i then 1 else α j - α k) * (β j - β i)) = fun _ => (0 : K) := by
    ext j
    by_cases hj : j = i
    · simp [hj]
    · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), zero_mul]
  rw [this, Matrix.diagonal_zero, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ProjNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem coeffSum (Λ G : Type) [CommRing Λ] [Group G] [Fintype G] (x : MonoidAlgebra Λ G) :
    ∑ g : G, (MonoidAlgebra.single g (1:Λ)) * MonoidAlgebra.single (1:G) (((MonoidAlgebra.single g⁻¹ (1:Λ)) * x).coeff 1) = x := by
  classical
  ext h
  simp [MonoidAlgebra.single_mul_single, Finsupp.single_apply]

private theorem higman (Λ G N : Type) [CommRing Λ] [Group G] [Fintype G] [AddCommGroup N]
    [Module (MonoidAlgebra Λ G) N] (h : Module.Projective (MonoidAlgebra Λ G) N) :
    ∃ φ : N →+ N, ∀ m, ∑ g : G, MonoidAlgebra.single g (1:Λ) • φ (MonoidAlgebra.single g⁻¹ (1:Λ) • m) = m := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def.1 h
  let e : MonoidAlgebra Λ G →+ MonoidAlgebra Λ G :=
    { toFun := fun x => MonoidAlgebra.single (1:G) (x.coeff 1)
      map_zero' := by simp
      map_add' := by intro x y; simp [MonoidAlgebra.single_add] }
  refine ⟨(Finsupp.linearCombination (MonoidAlgebra Λ G) (id : N → N)).toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom e).comp s.toAddMonoidHom), fun m => ?_⟩
  conv_rhs => rw [← hs m]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ← map_smul, ← map_sum]
  congr 1
  ext1 n
  rw [Finsupp.finsetSum_apply]
  simp only [map_smul, Finsupp.smul_apply, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact coeffSum Λ G (s m n)

theorem UpperTheory.V.Pa.Lev.projNorm :
    ∀ (Λ G M : Type) [CommRing Λ] [Group G] [Fintype G] [AddCommGroup M] [Module Λ M] (ρ : Representation Λ G M), Module.Projective (MonoidAlgebra Λ G) ρ.asModule → (∀ m, (∀ g, ρ g m = m) → ∃ m', ∑ g, ρ g m' = m) ∧ ∀ S : Set G, Subgroup.closure S = ⊤ → ∀ m, ∑ g, ρ g m = 0 → m ∈ ⨆ g ∈ S, LinearMap.range (ρ g - 1) := by
  intro Λ G M _ _ _ _ _ ρ hP
  obtain ⟨φ₀, hφ₀⟩ := higman Λ G ρ.asModule hP
  obtain ⟨φ, hφ⟩ : ∃ φ : M →+ M, ∀ m, ∑ g : G, ρ g (φ (ρ g⁻¹ m)) = m := by
    refine ⟨ρ.asModuleEquiv.toLinearMap.toAddMonoidHom.comp (φ₀.comp ρ.asModuleEquiv.symm.toLinearMap.toAddMonoidHom), fun m => ?_⟩
    have := congrArg ρ.asModuleEquiv (hφ₀ (ρ.asModuleEquiv.symm m))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearEquiv.apply_symm_apply] at this
    rw [← this]
    conv_lhs => rw [this]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_symm_map_rho]
    rfl
  refine ⟨fun m hm => ⟨φ m, ?_⟩, fun S hS m hm => ?_⟩
  · simpa only [hm] using hφ m
  · set I : Submodule Λ M := ⨆ g ∈ S, LinearMap.range (ρ g - 1) with hI
    have key : ∀ g : G, ∀ x, ρ g x - x ∈ I := by
      intro g
      have hg : g ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top g
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        intro x
        exact Submodule.mem_iSup_of_mem g (Submodule.mem_iSup_of_mem hg ⟨x, rfl⟩)
      | one => intro x; simp
      | mul a b _ _ ha hb =>
        intro x
        have := I.add_mem (ha (ρ b x)) (hb x)
        simpa using this
      | inv a _ ha =>
        intro x
        have := I.neg_mem (ha (ρ a⁻¹ x))
        simpa using this
    have h0 : ∑ g : G, φ (ρ g⁻¹ m) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← map_zero φ, ← hm]
      congr 1
      exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
    have : m = ∑ g : G, (ρ g (φ (ρ g⁻¹ m)) - φ (ρ g⁻¹ m)) := by
      rw [Finset.sum_sub_distrib, hφ, h0, sub_zero]
    rw [this]
    exact I.sum_mem fun g _ => key g _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PsLinSmall
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem psLin_span {A κ : Type} [CommRing A] (d : ℕ) (s : Finset κ) :
    ∀ f : MvPowerSeries κ A, (∀ e : κ →₀ ℕ, (∀ i ∈ s, e i < d) → MvPowerSeries.coeff e f = 0) →
      f ∈ Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro f hf
    have h0 : f = 0 := by
      ext e
      simpa using hf e (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  · intro a s _ ih f hf
    let g : MvPowerSeries κ A := fun e => MvPowerSeries.coeff (e + Finsupp.single a d) f
    let r : MvPowerSeries κ A := fun e => if e a < d then MvPowerSeries.coeff e f else 0
    have hfr : f = (MvPowerSeries.X a) ^ d * g + r := by
      ext e
      rw [map_add (f := _), MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]
      by_cases h : e a < d
      · have h' : ¬ (Finsupp.single a d ≤ e) := by
          rw [Finsupp.single_le_iff]
          omega
        rw [if_neg h']
        show _ = 0 + (if e a < d then MvPowerSeries.coeff e f else 0)
        rw [if_pos h, zero_add]
      · have h' : Finsupp.single a d ≤ e := by
          rw [Finsupp.single_le_iff]
          omega
        rw [if_pos h']
        show _ = 1 * MvPowerSeries.coeff (e - Finsupp.single a d + Finsupp.single a d) f +
          (if e a < d then MvPowerSeries.coeff e f else 0)
        rw [if_neg h, tsub_add_cancel_of_le h', one_mul, add_zero]
    rw [hfr]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)) (ih r ?_)
    intro e he
    show (if e a < d then MvPowerSeries.coeff e f else 0) = 0
    split_ifs with h
    · exact hf e (fun i hi => by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h
        · exact he i hi)
    · rfl

private theorem psLin_small {Λ A M κ : Type} [CommRing Λ] [CommRing A] [AddCommGroup M] [Module Λ M]
    (act : MvPowerSeries κ A →+* Module.End Λ M) (I : Ideal Λ) (d : ℕ) (m : M)
    (h : ∀ i, (act (MvPowerSeries.X i) ^ d) m ∈ (I • ⊤ : Submodule Λ M)) (f : MvPowerSeries κ A)
    (hf : f ∈ Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d)) :
    act f m ∈ (I • ⊤ : Submodule Λ M) := by
  have hT : ∀ (T : Module.End Λ M) (y : M), y ∈ (I • ⊤ : Submodule Λ M) →
      T y ∈ (I • ⊤ : Submodule Λ M) :=
    fun T y hy => Submodule.smul_top_le_comap_smul_top I T hy
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [map_pow]
    exact h i
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, map_mul, Module.End.mul_apply]
    exact hT _ _ hx

theorem UpperTheory.V.Pa.Lev.psLin :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (A M M' κ : Type) [CommRing A] [AddCommGroup M] [Module Λ M] [AddCommGroup M'] [Module Λ M'] [Module.Finite Λ M] [Module.Finite Λ M'] [Fintype κ] (act : MvPowerSeries κ A →+* Module.End Λ M) (act' : MvPowerSeries κ A →+* Module.End Λ M') (φ : M →ₗ[Λ] M'), topNil (maximalIdeal Λ) (fun i => act (MvPowerSeries.X i)) = ⊤ → topNil (maximalIdeal Λ) (fun i => act' (MvPowerSeries.X i)) = ⊤ → (∀ a m, φ (act (MvPowerSeries.C a) m) = act' (MvPowerSeries.C a) (φ m)) → (∀ i m, φ (act (MvPowerSeries.X i) m) = act' (MvPowerSeries.X i) (φ m)) → ∀ f m, φ (act f m) = act' f (φ m) := by
  intro Λ _ _ _ _ A M M' κ _ _ _ _ _ _ _ _ act act' φ hN hN' hC hX f m
  classical
  have hpoly : ∀ P : MvPolynomial κ A, ∀ y,
      φ (act (P : MvPowerSeries κ A) y) = act' (P : MvPowerSeries κ A) (φ y) := by
    intro P
    refine MvPolynomial.induction_on
      (motive := fun P => ∀ y, φ (act (P : MvPowerSeries κ A) y) = act' (P : MvPowerSeries κ A) (φ y))
      P ?_ ?_ ?_
    · intro a y
      rw [MvPolynomial.coe_C]
      exact hC a y
    · intro p q hp hq y
      rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _),
        hp, hq]
    · intro p i hp y
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, hp, hX]
  rw [← sub_eq_zero]
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M') (maximalIdeal Λ)
    (IsLocalRing.maximalIdeal.isMaximal Λ).ne_top
  have hmem : φ (act f m) - act' f (φ m) ∈ ⨅ k, (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M') := by
    rw [Submodule.mem_iInf]
    intro k
    have ev1 : ∀ᶠ r in Filter.atTop, ∀ i,
        (act (MvPowerSeries.X i) ^ r) m ∈ (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M) :=
      Filter.eventually_all.mpr fun i =>
        (mem_topNil (I := maximalIdeal Λ) (T := fun i => act (MvPowerSeries.X i)) (m := m)).mp
          (by rw [hN]; exact Submodule.mem_top) i k
    have ev2 : ∀ᶠ r in Filter.atTop, ∀ i,
        (act' (MvPowerSeries.X i) ^ r) (φ m) ∈ (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M') :=
      Filter.eventually_all.mpr fun i =>
        (mem_topNil (I := maximalIdeal Λ) (T := fun i => act' (MvPowerSeries.X i)) (m := φ m)).mp
          (by rw [hN']; exact Submodule.mem_top) i k
    obtain ⟨d, hd1, hd2, hd0⟩ := (ev1.and (ev2.and (Filter.eventually_ge_atTop 1))).exists
    let n0 : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => d - 1
    let P := MvPowerSeries.trunc' A n0 f
    have hr : f - (P : MvPowerSeries κ A) ∈
        Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d) := by
      apply psLin_span d Finset.univ
      intro e he
      have hle : e ≤ n0 := Finsupp.le_def.mpr fun i => by
        have := he i (Finset.mem_univ i)
        show e i ≤ d - 1
        omega
      rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]
    have h1 := psLin_small act ((maximalIdeal Λ) ^ k) d m hd1 _ hr
    have h2 := psLin_small act' ((maximalIdeal Λ) ^ k) d (φ m) hd2 _ hr
    have h3 := Submodule.smul_top_le_comap_smul_top ((maximalIdeal Λ) ^ k) φ h1
    have hsplit : φ (act f m) - act' f (φ m) =
        φ (act (f - ↑P) m) - act' (f - ↑P) (φ m) := by
      simp only [map_sub, LinearMap.sub_apply, hpoly P m, sub_sub_sub_cancel_right]
    rw [hsplit]
    exact Submodule.sub_mem _ h3 h2
  rw [hbot] at hmem
  exact (Submodule.mem_bot Λ).mp hmem
end

