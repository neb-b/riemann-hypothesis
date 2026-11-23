module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem taylor_alg {K A B : Type} [CommRing K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] {d : ℕ}
    (t : Fin d → A)
    (hf : (MvPolynomial.eval₂Hom (algebraMap K A) t : MvPolynomial (Fin d) K →+* A).FormallyUnramified)
    (D : Fin d → Derivation K A A) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0)
    (N P : Ideal B) (hNP : N * N ≤ P) (a b : A →ₐ[K] B) (hab : ∀ x, a x - b x ∈ N) (x : A) :
    a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) ∈ P := by
  classical
  let f : MvPolynomial (Fin d) K →+* A := MvPolynomial.eval₂Hom (algebraMap K A) t
  let π : B →+* B ⧸ P := Ideal.Quotient.mk P
  let e : Fin d → B := fun k => a (t k) - b (t k)
  have he : ∀ k, e k ∈ N := fun k => hab _
  let S : A → B := fun x => ∑ k, e k * b (D k x)
  have hS : ∀ x, S x ∈ N := fun x => Ideal.sum_mem _ fun k _ => N.mul_mem_right _ (he k)
  have hSadd : ∀ x y, S (x + y) = S x + S y := fun x y => by
    simp only [S, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hSmul : ∀ x y, S (x * y) = b x * S y + b y * S x := fun x y => by
    simp only [S, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hSone : S 1 = 0 := by simp [S]
  have hSzero : S 0 = 0 := by simp [S]
  let c : A →+* B ⧸ P :=
    { toFun := fun x => π (b x + S x)
      map_one' := by simp [hSone]
      map_zero' := by simp [hSzero]
      map_add' := fun x y => by
        rw [hSadd, map_add b, ← map_add π]
        congr 1
        ring
      map_mul' := fun x y => by
        rw [← map_mul π]
        refine Ideal.Quotient.eq.2 ?_
        have h := hNP (Ideal.mul_mem_mul (hS x) (hS y))
        have e2 : b (x * y) + S (x * y) - (b x + S x) * (b y + S y) = -(S x * S y) := by
          rw [hSmul, map_mul]
          ring
        rw [e2]
        exact P.neg_mem h }
  have hc : ∀ x, c x = π (b x + S x) := fun _ => rfl
  have hcf : c.comp f = π.comp ((a : A →+* B).comp f) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_C, hc]
      have : S (algebraMap K A r) = 0 := by simp [S]
      simp [this]
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_X', hc]
      have : S (t i) = e i := by simp [S, hD, e]
      rw [this]
      simp [e]
  letI algA : Algebra (MvPolynomial (Fin d) K) A := f.toAlgebra
  letI algC : Algebra (MvPolynomial (Fin d) K) (B ⧸ P) := (π.comp ((a : A →+* B).comp f)).toAlgebra
  haveI : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) A := hf
  let g₁ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := π.comp (a : A →+* B), commutes' := fun _ => rfl }
  let g₂ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := c, commutes' := fun p => RingHom.congr_fun hcf p }
  have hnil : IsNilpotent (N.map π) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot]
    refine le_bot_iff.1 ((Ideal.map_mono hNP).trans ?_)
    rw [Ideal.map_quotient_self]
  have hg : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext (N.map π) hnil fun y => ?_
    refine Ideal.Quotient.eq.2 ?_
    have : g₁ y - g₂ y = π (a y - (b y + S y)) := by
      rw [map_sub]
      rfl
    rw [this]
    refine Ideal.mem_map_of_mem π ?_
    have e3 : a y - (b y + S y) = (a y - b y) - S y := by ring
    rw [e3]
    exact N.sub_mem (hab y) (hS y)
  have h1 : π (a x) = π (b x + S x) := DFunLike.congr_fun hg x
  have h2 := Ideal.Quotient.eq.1 h1
  have e4 : a x - (b x + S x) = a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) := by
    simp only [S, e]
    ring
  rwa [e4] at h2

theorem taylor_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  intro K _ _ X q W d c s E ε h
  letI := (strV q W).toAlgebra
  intro D hD
  obtain ⟨-, -, h3, h4, h5⟩ := h
  intro T u v x
  obtain ⟨y, rfl⟩ := ε.surjective x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have hcomm : ∀ (w : E.D ⟶ T) (r : K), ((sP (KS q s {W})).A.map w).hom (ε (algebraMap K Γ(X, W) r)) =
      algebraMap K ((sP (KS q s {W})).A.obj T) r := fun w r => by
    have e : ε (algebraMap K Γ(X, W) r) = algebraMap K _ r := h3 r
    rw [e]
    exact AlgHom.commutes _ r
  let ev' : (E.D ⟶ T) → (Γ(X, W) →ₐ[K] (sP (KS q s {W})).A.obj T) := fun w =>
    { toRingHom := RingHom.comp (AlgHom.toRingHom ((sP (KS q s {W})).A.map w).hom) ε.toRingHom
      commutes' := hcomm w }
  have hNP : (sFil (KS q s {W}) 1).S T * (sFil (KS q s {W}) 1).S T ≤ (sFil (KS q s {W}) 2).S T :=
    Ideal.mul_le.2 fun a ha b hb => hF.mul 1 1 T ha hb
  have hab : ∀ g, ev' u g - ev' v g ∈ (sFil (KS q s {W}) 1).S T := fun g => by
    rw [hF.one T]
    have e := (h4 T u g).symm.trans (h4 T v g)
    exact Ideal.Quotient.eq.1 e
  have hf : (MvPolynomial.eval₂Hom (algebraMap K Γ(X, W)) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).FormallyUnramified :=
    by
      have he := c.etale
      letI := (MvPolynomial.eval₂Hom (strV q W) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).toAlgebra
      haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, W) := he
      exact (inferInstance : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) Γ(X, W))
  have key := taylor_alg c.t hf D hD _ _ hNP (ev' u) (ev' v) hab y
  have e : ∀ k, E.τ k v u = ev' u (c.t k) - ev' v (c.t k) := fun k => h5 k v u
  simp only [ε.symm_apply_apply, e]
  exact key

end GlobalTheory.CompanionTheory.ConeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExists
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.TopNil

theorem exists_thB_wB {l : ℕ} [Fact l.Prime] (y : ℂ_[l]) (hy : ‖y‖ ≤ 1) :
    ∃ a, thB l (wB l a) = y := by
  obtain ⟨a, ha⟩ := GroundTheory.PAdicHodge.IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l
    ⟨y, GroundTheory.PAdicHodge.mem_normInteger.2 hy⟩
  refine ⟨a, ?_⟩
  have h := GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus
    (K := ℂ_[l]) l a
  rw [ha] at h
  exact h

theorem near_tch_pow {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (hS : ∀ a, wB l a ∈ S)
    (ϖ : Formalism.Per6.BdRp l) (hϖ : thB l ϖ ≠ 0) (x : Tl l) (hx : ‖thB l (tch l x)‖ < 1) :
    ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) := by
  set c : ℂ_[l] := thB l (tch l x) with hc
  have hpos : 0 < ‖thB l ϖ‖ := norm_pos_iff.2 hϖ
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hx
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  have hle : ‖c‖ ^ (N + 1) ≤ ‖thB l ϖ‖ := by
    rw [pow_succ]
    calc ‖c‖ ^ N * ‖c‖ ≤ ‖c‖ ^ N * 1 :=
          mul_le_mul_of_nonneg_left hx.le (pow_nonneg (norm_nonneg _) _)
      _ = ‖c‖ ^ N := mul_one _
      _ ≤ ‖thB l ϖ‖ := hN.le
  have hy : ‖c ^ (N + 1) / thB l ϖ‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one hpos]
    exact hle
  obtain ⟨a, ha⟩ := exists_thB_wB _ hy
  refine ⟨wB l a, hS a, ?_⟩
  rw [pow_one, FB, pow_one, RingHom.mem_ker, map_sub, map_pow, map_mul, ha, ← hc]
  field_simp
  simp

theorem main : ∀ {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)), (∀ a, wB l a ∈ S) →
    ∀ (ϖ : Formalism.Per6.BdRp l), thB l ϖ ≠ 0 → ∀ x : Tl l, ‖thB l (tch l x)‖ < 1 →
      ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) :=
  fun S hS ϖ hϖ x hx => near_tch_pow S hS ϖ hϖ x hx

end GlobalTheory.CompanionTheory.LTPer.TopNil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransportSymm
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GlobBc

universe w w'

theorem tens_transport {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f) : Tens R f₁ := by
  obtain ⟨g, hg⟩ := hT
  let c : (∀ i, N i ⊗[R] M₁ i) ≃+ (∀ i, N i ⊗[R] M i) :=
    AddEquiv.piCongrRight fun i => (TensorProduct.congr (LinearEquiv.refl R (N i)) (e i).symm).toAddEquiv
  refine ⟨c.trans (g.trans e'), fun i n x => ?_⟩
  have hc : c (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ (e i).symm x) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [c]
    · simp [c, Pi.single_eq_of_ne hk]
  simp only [AddEquiv.trans_apply]
  rw [hc, hg, h, LinearEquiv.apply_symm_apply]

theorem tens_transport_symm {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f₁) : Tens R f :=
  tens_transport (fun i => (e i).symm) e'.symm
    (fun i n x => by rw [AddEquiv.symm_apply_eq, h, LinearEquiv.apply_symm_apply]) hT

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

def thM : SMor (thP (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))) (thP (nlFun γ 0 X q (κA O I)))
    (algebraMap O A) where
  G := ((nmO γ q).mor 0).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

theorem leC {c : A} {i : ℕ} (hc : c ∈ pdP γ i) (r : ℤ) :
    (thM γ q).LeC c (thFil _ (r - i)) (thFil _ r) := by
  intro T x hx
  have h1 : T.i c ∈ pdP T.δ i := dividedPowerFiltration_map T.compat i hc
  have h2 : x ∈ pdP T.δ (r - i).toNat := hx
  have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ _ _ (Ideal.mul_mem_mul h1 h2)
  exact T.pdPow_anti (by omega) h3

end

abbrev rq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    CH.Mor (sq (sFil Q r) (sFil Q r')) (sq (sFil Q' r) (sFil Q' r')) (RingHom.id _) :=
  (incl h).sq (incl_fil h r) (incl_fil h r')

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) {m : ℕ} (S : GrSplit O γ m)

theorem leS (𝒱 : Set X.Opens) (i : Fin m) (n : S.N i) (r : ℤ) :
    (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
  fun T x hx => leC γ q (S.mem i n) r T.obj x hx

abbrev mC (𝒱 : Set X.Opens) (r r' : ℤ) (i : Fin m) (n : S.N i) :=
  (smO γ q l s 𝒱).sqC (S.ν i n) (leS γ q l s S 𝒱 i n r) (leS γ q l s S 𝒱 i n r')

def BcAt (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) : Prop :=
  Tens O (N := S.N) (M := fun i => HQ (TO q l s 𝒱) (r - i) (r' - i) j) (M' := HQ (TS γ q l s 𝒱) r r' j)
    fun i n x => (mC γ q l s S 𝒱 r r' i n).pull j x

variable {γ q l s}

theorem st_top {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {p : ℕ} {κ : O →+* R ⧸ J}
    (Q : ObjectProperty (Thick (nlFun δ p X q κ))) (𝒱 : Set X.Opens) : St Q 𝒱 ≤ St Q {⊤} := by
  rintro T ⟨h, V, -, -⟩
  exact ⟨h, ⊤, rfl, fun _ _ => trivial⟩

theorem comm_top (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) (i : Fin m) (n : S.N i) (x) :
    (rq (st_top (TF l s) 𝒱) r r').pull j ((mC γ q l s S {⊤} r r' i n).pull j x) =
    (mC γ q l s S 𝒱 r r' i n).pull j ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j x) := by
  refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (mC γ q l s S {⊤} r r' i n) (rq (st_top (TF l s) 𝒱) r r') j x).1).symm.trans
    (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (rq (st_top (TF l s) 𝒱) (r - i) (r' - i)) (mC γ q l s S 𝒱 r r' i n) j x).1))
  refine CrystallineSemistableComparison.P.prism (σ := algebraMap O A) ((mC γ q l s S {⊤} r r' i n).comp (rq (st_top (TF l s) 𝒱) r r'))
    ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).comp (mC γ q l s S 𝒱 r r' i n)) (𝟙 _) (fun T y => ?_) j x
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  first
    | rfl
    | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)

theorem used_TF {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} (l s : ℕ) :
    Used (TF l s : ObjectProperty (Thick (nlFun δ 0 X q κ))) :=
  Or.inl ⟨rfl, l, s, rfl⟩

theorem bcAt_iff (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (j : ℕ) :
    BcAt γ q l s S {⊤} r r' j ↔ BcAt γ q l s S 𝒱 r r' j := by
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup 𝒱 := fun W hW => by rw [h𝒱]; exact le_top
  have bO := (_root_.GlobalTheory.CompanionTheory.NlZar.zariski_descent (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk (⊥ : Ideal O)) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  have bA := (_root_.GlobalTheory.CompanionTheory.NlZar.zariski_descent (γ := γ) (p := 0) (q := q) (κ := κA O I) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  let eO : ∀ i : Fin m, HQ (TO q l s {⊤}) (r - i) (r' - i) j ≃ₗ[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j := fun i =>
    LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j) (bO _ _)
  let eA : HQ (TS γ q l s {⊤}) r r' j ≃+ HQ (TS γ q l s 𝒱) r r' j :=
    (LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) r r').pull j) (bA _ _)).toAddEquiv
  have hcomm : ∀ i n x, eA ((mC γ q l s S {⊤} r r' i n).pull j x) = (mC γ q l s S 𝒱 r r' i n).pull j (eO i x) :=
    fun i n x => comm_top S 𝒱 r r' j i n x
  exact ⟨tens_transport eO eA hcomm, tens_transport_symm eO eA hcomm⟩

end

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {m : ℕ} (S : GrSplit O γ m)

abbrev thO (q : X ⟶ Spec (CommRingCat.of O)) (r r' : ℤ) :
    Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) ⥤ ModuleCat.{0} O :=
  sq (thFil _ r) (thFil _ r')

abbrev thS (r r' : ℤ) : Thick (nlFun γ 0 X q (κA O I)) ⥤ ModuleCat.{0} A :=
  sq (thFil _ r) (thFil _ r')

abbrev tM (r r' : ℤ) (i : Fin m) (n : S.N i) : CH.Mor (thO q (r - i) (r' - i)) (thS γ q r r') (algebraMap O A) :=
  (thM γ q).sqC (S.ν i n) (leC γ q (S.mem i n) r) (leC γ q (S.mem i n) r')

theorem tM_add (r r' : ℤ) (i : Fin m) (n n' : S.N i) (T) (x) :
    (tM γ q S r r' i (n + n')).τ T x = (tM γ q S r r' i n).τ T x + (tM γ q S r r' i n').τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (n + n')) * z' = algebraMap A B (S.ν i n) * z' + algebraMap A B (S.ν i n') * z' := by
    rw [map_add (f := _), map_add (f := _), add_mul]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

theorem tM_smul (r r' : ℤ) (i : Fin m) (c : O) (n : S.N i) (T) (x) :
    (tM γ q S r r' i (c • n)).τ T x = algebraMap O A c • (tM γ q S r r' i n).τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (c • n)) * z' = algebraMap O A c • (algebraMap A B (S.ν i n) * z') := by
    rw [map_smul, Algebra.smul_def c, map_mul, mul_assoc, Algebra.smul_def (algebraMap O A c)]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

end

theorem main : KH.GlobBcSt → BcOn True → BcOn False := by
  intro hG hT O A _ _ _ I γ l s m hO hA S X q 𝒱 hc r r' hrr hr's ha hb j
  obtain ⟨U, h𝒱⟩ : Nonempty (Cov q) ∧ sSup 𝒱 = ⊤ := by
    rcases hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h.elim
    · exact h
  obtain ⟨U⟩ := U
  have hU : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  have hmem : ∀ (𝒲 : Set X.Opens) (T), St (TF l s) 𝒲 T → St (TF l s) 𝒲 ((((nmO γ q).mor 0).functor).obj T) :=
    fun 𝒲 T h => nmO_mem γ q l s 𝒲 T h
  have key : ∀ j, BcAt γ q l s S (Set.range U.U) r r' j := fun j =>
    hG (O := O) (R := O) (I := ⊥) (γ := dividedPowersBot O) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥)
      (O' := O) (R' := A) (I' := I) (γ' := γ) (p' := 0) (X' := X) (q' := q) (κ' := κA O I)
      (Λ := O) (Λ' := A) (σ := algebraMap O A) ((nmO γ q).mor 0).functor S.N
      (fun i => thO q (r - i) (r' - i)) (thS γ q r r')
      (fun i n T => (tM γ q S r r' i n).τ T) (fun i n {T T'} φ x => (tM γ q S r r' i n).nat φ x)
      (fun i n n' T x => tM_add γ q S r r' i n n' T x) (fun i c n T x => tM_smul γ q S r r' i c n T x)
      (TF l s) (TF l s) U.U U.U (fun α T h => hmem _ T h) (fun S' T h => hmem _ T h) (fun T h => hmem _ T h)
      (fun S' hS' j => by
        obtain ⟨α, hα⟩ := hS'
        obtain ⟨c', -⟩ := _root_.GlobalTheory.CompanionTheory.CoordRes.main (U.c α) (iInf₂_le α hα : (⨅ α ∈ S', U.U α) ≤ U.U α) (U.inter S' ⟨α, hα⟩)
        exact hT γ l s m hO hA S q {⨅ α ∈ S', U.U α} (Or.inl ⟨trivial, _, _, rfl, ⟨c'⟩⟩) r r' hrr hr's
          (fun i n => leS γ q l s S _ i n r) (fun i n => leS γ q l s S _ i n r') j) j
  exact (bcAt_iff S 𝒱 h𝒱 r r' j).1 ((bcAt_iff S (Set.range U.U) hU r r' j).2 (key j))

end GlobalTheory.CompanionTheory.GlobBc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotent
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.Dichotomy

section Core

variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

end Core

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  by_contra hc
  push Not at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hc x] at this
    exact this.symm)
  have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal

theorem exists_theta {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E), θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
  obtain ⟨y, hy⟩ := exists_moved h
  have hE2 : (2 : E) ≠ 0 := two_ne_zero
  have hσθ : σ (y - σ y) = -(y - σ y) := by
    rw [map_sub, sigma_sigma h]
    ring
  have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  generalize y - σ y = θ at hσθ hθ
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, mul_one] at hst
    have h1 := congrArg σ hst
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ, map_zero] at h1
    have hs : (2 : E) * algebraMap F E s = 0 := by
      linear_combination hst + h1
    have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
      linear_combination hst - h1
    have hs0 : s = 0 := by
      have := (mul_eq_zero.1 hs).resolve_left hE2
      exact (map_eq_zero _).1 this
    have ht0 : t = 0 := by
      have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
      exact (map_eq_zero _).1 this
    exact ⟨hs0, ht0⟩
  let B : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = θ := by simp [B]
  have hsum := B.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hB0, hB1] at hsum
  generalize B.repr (θ * θ) 0 = a at hsum
  generalize B.repr (θ * θ) 1 = b at hsum
  have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
    simpa only [Algebra.smul_def, mul_one] using hsum
  have hconj := congrArg σ hsum'
  simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ] at hconj
  have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
    linear_combination hsum' - hconj
  have hb0 : algebraMap F E b = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
  have hsq : θ * θ = algebraMap F E a := by
    rw [← hsum', hb0, zero_mul, add_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact hθ (mul_self_eq_zero.1 hsq)
  exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩

end CM

end GlobalTheory.CompanionTheory.SaGen.Dichotomy
end
end

