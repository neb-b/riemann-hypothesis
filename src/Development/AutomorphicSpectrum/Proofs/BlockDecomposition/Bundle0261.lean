module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0243
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentative
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0252
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpEpsilonRootIdempotentSum
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Frob

variable {l : ℕ} {R : Type} [CommRing R] (φ : R →+* R)

theorem mem_span_of_frob_mem (hb : Function.Bijective φ) {y p : R}
    (h : φ y ∈ Ideal.span {φ p}) : y ∈ Ideal.span {p} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨c', rfl⟩ := hb.2 c
  exact Ideal.mem_span_singleton'.2 ⟨c', hb.1 (by rw [map_mul, hc])⟩

theorem mem_span_of_pow_mem (hφ : ∀ x, φ x = x ^ l) (hb : Function.Bijective φ) {x p : R}
    (N : ℕ) (h : x ^ l ^ N ∈ Ideal.span {p ^ l ^ N}) : x ∈ Ideal.span {p} := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih (mem_span_of_frob_mem φ hb ?_)
    rw [hφ, hφ, ← pow_mul, ← pow_mul, ← pow_succ]
    exact h

theorem sub_pow_of_frob (hφ : ∀ x, φ x = x ^ l) (a b : R) (N : ℕ) :
    (a - b) ^ l ^ N = a ^ l ^ N - b ^ l ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, ← hφ, map_sub, hφ, hφ]

end Frob

theorem root_pow {l : ℕ} {T : Type} [Monoid T] {x : ℕ → T} (hx : ∀ m, x (m + 1) ^ l = x m) (m k : ℕ) :
    x (m + k) ^ l ^ k = x m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' l k, pow_mul, ← add_assoc, hx, ih]

variable {l : ℕ} [Fact l.Prime]

def powSum (A : PAlg l) (u : (A.cont ℤ_[l]).A) (N : ℕ) : (A.cont ℤ_[l]).A :=
  ∑ c : ZMod (l ^ N), ind A N c * u ^ c.val

theorem ev_powSum (A : PAlg l) (u : (A.cont ℤ_[l]).A) (N : ℕ) (z : ℤ_[l]) :
    Hom.f (A.evCont z) (powSum A u N) = Hom.f (A.evCont z) u ^ (PadicInt.toZModPow N z).val := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [powSum, map_sum]
  simp only [map_mul, map_pow, ev_ind, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem sub_powSum_mem (A : PAlg l) {u ρ : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (hρ : ∀ n, ρ (n + 1) ^ l = ρ n)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) (ρ 0) -
      Hom.f (A.evCont z) (u 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {A.pi ^ (l ^ m)})
    (N : ℕ) : ρ N - powSum A (u N) N ∈ Ideal.span {(A.cont ℤ_[l]).pi} := by
  have hf : ∀ x : (A.cont ℤ_[l]).A, (A.cont ℤ_[l]).frob x = x ^ l := fun _ => rfl
  refine mem_span_of_pow_mem (l := l) (A.cont ℤ_[l]).frob hf (A.cont ℤ_[l]).frob_bijective N ?_
  have h1 : ρ N ^ l ^ N = ρ 0 := by simpa using root_pow hρ 0 N
  have h2 : u N ^ l ^ N = u 0 := by simpa using root_pow hu 0 N
  rw [sub_pow_of_frob (l := l) _ hf, h1, mem_span_pi_pow]
  intro z
  rw [map_sub, map_pow, ev_powSum, ← pow_mul, mul_comm, pow_mul, ← map_pow, h2]
  exact h0 N z

theorem sharp_powSum (A : PAlg l) {u : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (m k : ℕ) (hv : (A.cont ℤ_[l]).sharp (u m) ^ l ^ m = 1) :
    (A.cont ℤ_[l]).sharp (powSum A (u (m + k)) (m + k) ^ l ^ k) =
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val := by
  set B := powSum A (u (m + k)) (m + k) ^ l ^ k with hB
  set v := (A.cont ℤ_[l]).sharp (u m) with hvdef
  set T := ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * v ^ c.val with hT
  have hle : m ≤ m + k := Nat.le_add_right m k
  have h1 : ∀ c' : ZMod (l ^ (m + k)), ind A (m + k) c' * B = ind A (m + k) c' * u m ^ c'.val := by
    intro c'
    refine cont_ext fun z => ?_
    rw [map_mul, map_mul, ev_ind]
    split_ifs with h
    · have hr : Hom.f (A.evCont z) (u (m + k)) ^ l ^ k = Hom.f (A.evCont z) (u m) := by
        rw [← map_pow, root_pow hu]
      rw [hB, map_pow, ev_powSum, map_pow, h, ← pow_mul, mul_comm c'.val, pow_mul, hr]
    · simp
  have h2 : ∀ (c' : ZMod (l ^ (m + k))) (c : ZMod (l ^ m)), ZMod.cast c' ≠ c →
      ind A (m + k) c' * ind A m c = 0 := by
    intro c' c hc
    refine cont_ext fun z => ?_
    rw [map_mul, ev_ind, ev_ind, map_zero]
    split_ifs with h h'
    · exact absurd (by rw [← h', ← h, PadicInt.cast_toZModPow m (m + k) hle]) hc
    all_goals simp
  have h3 : ∀ c' : ZMod (l ^ (m + k)),
      ind A (m + k) c' * ind A m (ZMod.cast c') = ind A (m + k) c' := by
    intro c'
    refine cont_ext fun z => ?_
    rw [map_mul, ev_ind, ev_ind]
    split_ifs with h h'
    · simp
    · exact absurd (by rw [← h, PadicInt.cast_toZModPow m (m + k) hle]) h'
    all_goals simp
  have h4 : ∀ c' : ZMod (l ^ (m + k)), v ^ (ZMod.cast c' : ZMod (l ^ m)).val = v ^ c'.val := by
    intro c'
    rw [pow_eq_pow_mod c'.val hv, ← ZMod.natCast_val, ZMod.val_natCast]
  have key : ∀ c' : ZMod (l ^ (m + k)), (A.cont ℤ_[l]).sharp (ind A (m + k) c') * (A.cont ℤ_[l]).sharp B =
      (A.cont ℤ_[l]).sharp (ind A (m + k) c') * T := by
    intro c'
    rw [← map_mul, h1, map_mul, map_pow, hT, Finset.mul_sum, Finset.sum_eq_single (ZMod.cast c')]
    · rw [← mul_assoc, ← map_mul, h3, h4]
    · intro c _ hc
      rw [← mul_assoc, ← map_mul, h2 c' c (Ne.symm hc), sharp_zero, zero_mul]
    · simp
  have hsum := sum_sharp_eq_one (A.cont ℤ_[l]) (coi_ind A (m + k))
  calc (A.cont ℤ_[l]).sharp B = (∑ c', (A.cont ℤ_[l]).sharp (ind A (m + k) c')) * (A.cont ℤ_[l]).sharp B := by
        rw [hsum, one_mul]
    _ = (∑ c', (A.cont ℤ_[l]).sharp (ind A (m + k) c')) * T := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c' _ => key c'
    _ = T := by rw [hsum, one_mul]

theorem sharp_roots_core (A : PAlg l) {u ρ : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (hs : (A.cont ℤ_[l]).sharp (u 0) = 1) (hρ : ∀ n, ρ (n + 1) ^ l = ρ n)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) (ρ 0) -
      Hom.f (A.evCont z) (u 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {A.pi ^ (l ^ m)})
    (m : ℕ) : (A.cont ℤ_[l]).sharp (ρ m) =
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val := by
  have hv : (A.cont ℤ_[l]).sharp (u m) ^ l ^ m = 1 := by
    rw [← map_pow, (by simpa using root_pow hu 0 m : u m ^ l ^ m = u 0), hs]
  have hk : ∀ k, (A.cont ℤ_[l]).sharp (ρ m) -
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val ∈
      Ideal.span {(l : (A.cont ℤ_[l]).U) ^ (k + 1)} := by
    intro k
    have h := (RL.sharp_cong (A.cont ℤ_[l])).1 _ _ k (sub_powSum_mem A hu hρ h0 (m + k))
    rwa [root_pow hρ, sharp_powSum A hu m k hv] at h
  refine sub_eq_zero.1 (IsHausdorff.haus
    (inferInstance : IsHausdorff (Ideal.span {(l : (A.cont ℤ_[l]).U)}) (A.cont ℤ_[l]).U) _ fun k => ?_)
  refine smodEq_iff.2 ?_
  rw [sub_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hk k)
  exact Ideal.mem_span_singleton'.2 ⟨c * l, by rw [← hc, pow_succ]; ring⟩

theorem sharp_roots_universal {l : ℕ} [Fact l.Prime] (ε : Eps l) (ρ : ℕ → ((base l).cont ℤ_[l]).A)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) (ρ 0) -
      (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)})
    (hρ : ∀ m, ρ (m + 1) ^ l = ρ m) (m : ℕ) : ((base l).cont ℤ_[l]).sharp (ρ m) =
    ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (GlobalTheory.CompanionTheory.ContUniv.ind (base l) m c) *
      ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val := by
  have hev : ∀ (n : ℕ) (z : ℤ_[l]),
      Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e n)) = (base l).s (ε.e n) :=
    fun n z => RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  refine sharp_roots_core (base l) (u := fun n => ((base l).cont ℤ_[l]).s (ε.e n)) (fun n => ?_)
    (ε.sharp_e _) hρ (fun k z => ?_) m
  · show ((base l).cont ℤ_[l]).s (ε.e (n + 1)) ^ l = ((base l).cont ℤ_[l]).s (ε.e n)
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]
  · show Hom.f ((base l).evCont z) (ρ 0) -
      Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) ^ _ ∈ _
    rw [hev]
    exact h0 k z

end GlobalTheory.CompanionTheory.ContUniv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

theorem hom_eq_zero_of_basicOpen_cover {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type} (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i (f : Γ(X, V i)) (s : Γ(M, X.basicOpen f)), φ.app (X.basicOpen f) s = 0) :
    φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  have hcov' : W ≤ ⨆ p : {p : Σ i, Γ(X, V i) // X.basicOpen p.2 ≤ W}, X.basicOpen p.1.2 := by
    intro x hx
    have hx' : x ∈ iSup V := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    obtain ⟨f, hfW, hxf⟩ := (hV i).exists_basicOpen_le ⟨x, hx⟩ hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨i, f⟩, hfW⟩, hxf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun p : {p : Σ i, Γ(X, V i) // X.basicOpen p.2 ≤ W} ↦ X.basicOpen p.1.2) W
    (fun p ↦ homOfLE p.2) hcov' _ _ fun p ↦ ?_
  have nat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE p.2).op) s
  have e1 : (ConcreteCategory.hom (N.presheaf.map (homOfLE p.2).op)) (φ.app W s) = 0 :=
    nat.symm.trans (h p.1.1 p.1.2 _)
  refine e1.trans ?_
  rw [Scheme.Modules.Hom.zero_app]
  simp

theorem app_basicOpen_eq_zero {X : Scheme.{0}} {M N : X.Modules} [M.IsQuasicoherent] (φ : M ⟶ N)
    {U : X.Opens} (hU : IsAffineOpen U) (h0 : ∀ t : Γ(M, U), φ.app U t = 0) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) : φ.app (X.basicOpen f) s = 0 := by
  obtain ⟨n, t, ht⟩ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff M f).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen M hU f)).1 s
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n) :=
    (GlobalTheory.QCoh.isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).pow n
  have nat := ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) t
  have key : X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • φ.app (X.basicOpen f) s = 0 := by
    rw [← Scheme.Modules.Hom.app_smul, ht]
    refine nat.trans ?_
    change (ConcreteCategory.hom (N.presheaf.map (homOfLE (X.basicOpen_le f)).op)) (φ.app U t) = 0
    rw [h0 t]
    simp
  exact (hu.smul_eq_zero).1 key

theorem le_of_secs_subset_cover {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent]
    (S T : Subobject E) (hS : (S : X.Modules).IsQuasicoherent)
    (_hT : (T : X.Modules).IsQuasicoherent) {ι : Type} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i, secs S (V i) ⊆ secs T (V i)) : S ≤ T := by
  have h0 : S.arrow ≫ cokernel.π T.arrow = 0 := by
    refine hom_eq_zero_of_basicOpen_cover _ V hV hcov fun i f s ↦ ?_
    refine app_basicOpen_eq_zero _ (hV i) (fun t ↦ ?_) f s
    obtain ⟨y, hy⟩ := h i ⟨t, rfl⟩
    have hz : (T.arrow ≫ cokernel.π T.arrow).app (V i) y = 0 := by
      rw [cokernel.condition]; rfl
    change (cokernel.π T.arrow).app (V i) (S.arrow.app (V i) t) = 0
    rw [← hy]
    exact hz
  exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow h0) (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentativeStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_differential_representative : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D), Taylor Fil E p → ∀ (n : ℕ) (f : CH.Cn (CH.modF Φ.A) n) (y : Idx n d → Φ.A.obj E.D) (c : CH.H (gr Fil (n : ℤ)) n)
      (x : CH.H (gr Fil ((n : ℤ) + 1)) (n + 1)),
      CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => f u) c →
      CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => ∑ I : Idx n d, E.form σ I.1 (y I) u) c →
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n f u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1))
        (fun u => ∑ a : Idx n d × Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) a.1.1 a.2) ((-1) ^ n * p a.2 (y a.1)) u) x := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.connecting_form | exact GlobalTheory.CompanionTheory.ConeLocal.connecting_form | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.connecting_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrameStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_of_local_frame : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.taylor_loc | exact GlobalTheory.CompanionTheory.ConeLocal.taylor_loc | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.taylor_loc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TchNeMulOfPowEq
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exists_monic_eval₂_of_span {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (S : Subring B)
    (T : Finset B) (hW : ∀ a, f a ∈ S) (hT : ∀ t ∈ T, t ∈ S)
    (hS : ∀ s ∈ S, ∃ a : B → A, s = ∑ t ∈ T, t * f (a t)) (e : B) (he : e ∈ S) :
    ∃ P : Polynomial A, P.Monic ∧ P.eval₂ f e = 0 := by
  letI : Algebra A B := f.toAlgebra
  let C : Subalgebra A B := { S with algebraMap_mem' := hW }
  have hfg : (Subalgebra.toSubmodule C).FG := by
    refine ⟨T, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 fun t ht => hT t ht
    · intro s hs
      obtain ⟨a, rfl⟩ := hS s hs
      refine Submodule.sum_mem _ fun t ht => ?_
      have : t * f (a t) = a t • t := by
        rw [Algebra.smul_def, mul_comm]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ht)
  exact IsIntegral.of_mem_of_fg C hfg e he

theorem pow_natDegree_eq_zero_of_eval₂ {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    (f : A →+* B) (hf : Function.Injective f) (c : A →+* R) (P : Polynomial A) (hP : P.Monic)
    (e : B) (he : P.eval₂ f e = 0) (n v : A) (hn : c n = 0) (hv : f n * e = f v) :
    c v ^ P.natDegree = 0 := by
  have h1 : (P.scaleRoots n).eval₂ f (f v) = 0 := by
    rw [← hv, Polynomial.scaleRoots_eval₂_mul, he, mul_zero]
  have h2 : (P.scaleRoots n).eval v = 0 := by
    apply hf
    rw [← Polynomial.eval₂_at_apply, h1, map_zero]
  have h3 : (P.scaleRoots n).eval₂ c (c v) = 0 := by
    rw [Polynomial.eval₂_at_apply, h2, map_zero]
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.natDegree_scaleRoots,
    Finset.sum_eq_single P.natDegree] at h3
  · rw [Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree,
      hP.leadingCoeff, map_one, one_mul] at h3
    exact h3
  · intro i hi hne
    have hlt : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hne
    rw [Polynomial.coeff_scaleRoots, map_mul, map_pow, hn, zero_pow (Nat.sub_ne_zero_of_lt hlt)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

theorem tch_ne_mul_of_pow_eq {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (T : Finset (Formalism.Per6.BdRp l)) :
    (∀ a, wB l a ∈ S) → (∀ t ∈ T, t ∈ S) →
    (∀ s ∈ S, ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t)) →
    ∀ (ϖ y : Formalism.Per6.BdRp l) (N : ℕ), y ∈ S → ϖ ^ N = (l : Formalism.Per6.BdRp l) * y →
    ∀ u : Tl l, u ≠ 0 → ∀ s ∈ S, tch l u ≠ ϖ * s := by
  intro hW hT hS ϖ y N hy hN u hu s hs h
  haveI := GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l
  obtain ⟨P, hP, hev⟩ := exists_monic_eval₂_of_span (wB l) S T hW hT hS (y * s ^ N)
    (S.mul_mem hy (S.pow_mem hs N))
  have hinj : Function.Injective (wB l) := PositivityTheory.LocInh.wittTo_injective
  have hv : wB l (l : Wl l) * (y * s ^ N) = wB l (WittVector.teichmuller l (u ^ N)) := by
    have h1 : wB l (WittVector.teichmuller l (u ^ N)) = tch l u ^ N := by
      rw [map_pow, map_pow]; rfl
    rw [h1, h, mul_pow, hN, map_natCast, mul_assoc]
  have hc : (WittVector.constantCoeff : Wl l →+* Tl l) (l : Wl l) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ _
  have h0 := pow_natDegree_eq_zero_of_eval₂ (wB l) hinj WittVector.constantCoeff P hP _ hev
    (l : Wl l) _ hc hv
  have h2 : (WittVector.constantCoeff : Wl l →+* Tl l) (WittVector.teichmuller l (u ^ N)) = u ^ N :=
    WittVector.teichmuller_coeff_zero l _
  rw [h2] at h0
  exact hu (eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero h0))

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorNoetherianAffineOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

theorem krull_noeth_chart : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens), IsAffineOpen V → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R], IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := by
  intro X J Z ψ hψ V hV U hU h
  have hft : ((ψ ≫ J.subschemeι).appLE V U h).hom.FiniteType := by
    haveI : LocallyOfFiniteType ψ := inferInstance
    haveI : LocallyOfFiniteType (ψ ≫ J.subschemeι) := inferInstance
    exact LocallyOfFiniteType.finiteType_appLE (ψ ≫ J.subschemeι) hV hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra
  intro R _ _ _
  haveI : Algebra.FiniteType Γ(X, V) Γ(Z, U) := by
    exact hft
  haveI : Algebra.FiniteType R (R ⊗[Γ(X, V)] Γ(Z, U)) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing R _

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZeroStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_induced_agree : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ),
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) → (∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1) →
      ∀ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) →
      (∀ σ : ↥(Dec (F := E) A), (σ : G E Ω) ∈ V → (σ : G E Ω) ∈ Ine (F := E) A → ψ σ = 1) →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ 0 := by
  first | exact @GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | exact GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | (intros; apply GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphism
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrisDP

theorem wn_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ),
    IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  intro l _ K r n
  let F₀ : WittVector l r.k →+* (base l).Acr0 :=
    (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))
  refine RL.pd_mor (Ideal.Quotient.mk _) ((base l).mkAcr n) (Ideal.span {(l : WittVector l r.k)}) (base l).PFil0
    (Wc.pd l r.k n) (B.DD true (base l) n) F₀ (Mid.wn r n) Ideal.Quotient.mk_surjective
    (pdI_l l (witt_unit l r.k)) (Wc.isPd l r.k n) ((base l).isPd_pdPFil n) ?_ ?_
  · intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  · intro a
    rw [Mid.wn_mk]
    exact (base l).cris_algebraMap n (WittVector.map r.s a)

end GlobalTheory.CompanionTheory.CrisDP
end
end

