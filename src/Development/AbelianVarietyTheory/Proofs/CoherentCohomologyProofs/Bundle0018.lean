module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
section
open CategoryTheory CategoryTheory.Limits TensorProduct Function

namespace GlobalTheory

theorem exists_smul_mem_range_of_exact_fibre {R : Type*} [CommRing R] {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [Module.Finite R B] [Module.Projective R B] [Module.Finite R C] [Module.Projective R C]
    (K : Type*) [Field K] [Algebra R K] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : Exact (f.lTensor K) (g.lTensor K)) (b : B) (hb : g b = 0) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧ r • b ∈ LinearMap.range f := by
  let P : Ideal R := RingHom.ker (algebraMap R K)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  let O := Localization.AtPrime P
  have h1 := (exact_lTensor_iff_residueField P K rfl f g).1 h
  have h2 : Exact (AlgebraTensorModule.lTensor O P.ResidueField f)
      (AlgebraTensorModule.lTensor O P.ResidueField g) ↔
      Exact ((f.baseChange O).lTensor P.ResidueField) ((g.baseChange O).lTensor P.ResidueField) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField C)
      (by ext; simp) (by ext; simp)
  have h3 := h2.1 h1
  have hfg' : g.baseChange O ∘ₗ f.baseChange O = 0 := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_zero]
  obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField hfg'
    (fun m _ => forall_exact_residueField_of_isLocalRing h3 m)
  have h4 := exact_of_homotopy hfg' hst
  obtain ⟨x, hx⟩ := (h4 ((1 : O) ⊗ₜ[R] b)).1 (by simp [hb])
  obtain ⟨⟨a, u⟩, ha⟩ := IsLocalizedModule.surj P.primeCompl (TensorProduct.mk R O A 1) x
  have h5 : TensorProduct.mk R O B 1 ((u : R) • b) = TensorProduct.mk R O B 1 (f a) := by
    have := congrArg (f.lTensor O) ha
    rw [Submonoid.smul_def, map_smul] at this
    have hx' : f.lTensor O x = (1 : O) ⊗ₜ[R] b := hx
    rw [hx'] at this
    simpa using this
  obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) h5
  refine ⟨(v * u : P.primeCompl), (v * u).2, (v : R) • a, ?_⟩
  rw [map_smul, Submonoid.coe_mul, mul_smul]
  exact hv.symm


set_option backward.isDefEq.respectTransparency false in
theorem exists_smul_homology_eq_zero_of_acyclic_fibre (R : Type) [CommRing R] [IsNoetherianRing R]
    (K : Type) [Field K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p))
    (hac : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic)
    (p : ℕ) : ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0 := by
  letI : Algebra R K := χ.toAlgebra
  obtain ⟨L, φ, -, h2, -, h4, h5, -, h7⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} C n hn hflat hfin
  have h8 : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) := h7 K
  have h9 : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj L).ExactAt p :=
    (exactAt_iff_of_quasiIsoAt
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) p).2 (hac p)
  have h10 : Exact ((L.sc p).f.hom.lTensor K) ((L.sc p).g.hom.lTensor K) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h9
  have hpt : ∀ z : L.homology p, ∃ r : R, χ r ≠ 0 ∧ r • z = 0 := by
    intro z
    let e := (L.sc p).moduleCatHomologyIso.toLinearEquiv
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (e z)
    haveI : Module.Finite R (L.sc p).X₂ := h2 _
    haveI : Module.Finite R (L.sc p).X₃ := h2 _
    haveI : Module.Projective R (L.sc p).X₂ := h4 _
    haveI : Module.Projective R (L.sc p).X₃ := h4 _
    obtain ⟨r, hr, a, ha⟩ := exists_smul_mem_range_of_exact_fibre K
      (congrArg ModuleCat.Hom.hom (L.sc p).zero) h10 b.1 b.2
    refine ⟨r, hr, e.injective ?_⟩
    rw [map_smul, map_zero, ← hb]
    exact (Submodule.Quotient.mk_eq_zero _).2 (show r • b ∈ _ from ⟨a, Subtype.ext ha⟩)
  let e := (isoOfQuasiIsoAt φ p).toLinearEquiv
  let P : PrimeSpectrum R := ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩
  have hP : P ∉ Module.support R (C.homology p) := by
    rw [Module.notMem_support_iff']
    intro z
    obtain ⟨r, hr, hz⟩ := hpt (e.symm z)
    refine ⟨r, hr, ?_⟩
    rw [← e.apply_symm_apply z, ← map_smul, hz, map_zero]
  haveI := hfin p
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hP
  obtain ⟨r, hr, hr'⟩ := hP
  exact ⟨r, hr', Module.mem_annihilator.1 hr⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulOfTwCoord
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem GrSum.apply_eq_eval₂Hom_mul {ι R B : Type*} [CommRing R] [CommRing B]
    {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) (c : R →+* B) (b : ι → B)
    (φ : ∀ n, A n → B) (hadd : ∀ n a a', φ n (a + a') = φ n a + φ n a')
    (hsmul : ∀ n (r : R) a, φ n (r • a) = c r * φ n a)
    (hop : ∀ i n a, φ (n + 1) (x i n a) = b i * φ n a)
    (F : MvPolynomial ι R) {t t' : ℤ} {a : A t} {a' : A t'}
    (h : F • GrSum.of hx t a = GrSum.of hx t' a') :
    φ t' a' = MvPolynomial.eval₂Hom c b F * φ t a := by
  letI : Algebra R B := c.toAlgebra
  letI : Algebra (MvPolynomial ι R) B := (MvPolynomial.eval₂Hom c b).toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) B :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C c b r).symm
  let ψ : ∀ n, A n →ₗ[R] B := fun n => ⟨⟨φ n, hadd n⟩, hsmul n⟩
  have hψ : ∀ i n a, ψ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R) • ψ n a :=
    fun i n a => (hop i n a).trans
      (congrArg (· * φ n a) (MvPolynomial.eval₂Hom_X' c b i).symm)
  have e := congrArg (GrSum.lift hx ψ hψ) h
  rw [map_smul, GrSum.lift_of, GrSum.lift_of] at e
  exact e.symm

theorem AbLaw.exists_smul_of_twCoord :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (V : Y.Opens) (F : MvPolynomial (Fin (m + 1)) R) (d t t' : ℤ) (y : SecOn (tw M H t) V), F ∈ polyGrading (Fin (m + 1)) R d → t' = t + d → ∃ y' : SecOn (tw M H t') V, F • GrSum.of (hx V) t (SecOnR.of f _ V y) = GrSum.of (hx V) t' (SecOnR.of f _ V y') ∧ ∀ (p : M.ι) (l : H.ι), SecOn.twCoord y' p l = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (MvPolynomial.eval₂Hom (cst f (H.U l)) (fun j => (s j).f l) F) * SecOn.twCoord y p l := by
  intro R _ Y f H m s M hx V F d t t' y hF ht
  subst ht
  obtain ⟨a, ha⟩ := (GrSum.mem_grading (hx V)).1
    (grSMul_mem (GrSum.grading (hx V)) hF (GrSum.of_mem_grading (hx V) t (SecOnR.of f _ V y)))
  refine ⟨(SecOnR.of f _ V).symm a, ha.symm, fun p l => ?_⟩
  have h₀ : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l := inf_le_right.trans inf_le_right
  have e := GrSum.apply_eq_eval₂Hom_mul (hx V) (cst f (V ⊓ (M.U p ⊓ H.U l)))
    (fun j => rs Y h₀ ((s j).f l))
    (fun n z => SecOn.twCoord ((SecOnR.of f _ V).symm z) p l) (fun _ _ _ => rfl)
    (fun n r z => SecOnR.coord_base_smul r z (p, l)) (fun _ _ _ => rfl) F ha.symm
  refine e.trans (congrArg (· * SecOn.twCoord y p l) ?_)
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  exact RingHom.ext fun r => (rs_cst f h₀ r).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsTwExtendPowMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw.TwExtend

variable {Y : Scheme.{0}}

theorem basicOpen_rs_eq {L : LB Y} (s : LB.Sec L) (k : L.ι) {W : Y.Opens} (h : W ≤ L.U k) :
    Y.basicOpen (rs Y h (s.f k)) = nonzeroLocus s ⊓ W := by
  apply le_antisymm
  · have hb : Y.basicOpen (rs Y h (s.f k)) = W ⊓ Y.basicOpen (s.f k) := Y.basicOpen_res _ _
    rw [hb]
    exact le_inf (inf_le_right.trans (le_iSup (fun k => Y.basicOpen (s.f k)) k)) inf_le_left
  · have hu := SecOn.isUnit_rs_of_le_nonzeroLocus s k
      (inf_le_right.trans h : nonzeroLocus s ⊓ W ≤ L.U k) inf_le_left
    rw [← rs_rs h inf_le_right] at hu
    have hb : Y.basicOpen (rs Y (inf_le_right : nonzeroLocus s ⊓ W ≤ W) (rs Y h (s.f k))) =
      (nonzeroLocus s ⊓ W) ⊓ Y.basicOpen (rs Y h (s.f k)) := Y.basicOpen_res _ _
    rw [Y.basicOpen_of_isUnit hu] at hb
    exact hb.le.trans inf_le_right

theorem fun_extend {W O : Y.Opens} (hW : IsAffineOpen W) (f : Γ(Y, W)) (hO : Y.basicOpen f = O)
    (h : O ≤ W) (z : Γ(Y, O)) : ∃ (n : ℕ) (x : Γ(Y, W)), rs Y h x = rs Y h f ^ n * z := by
  subst hO
  exact exists_eq_pow_mul_of_isAffineOpen Y W hW f z

theorem fun_kill {W O : Y.Opens} (hW : IsCompact (W : Set Y)) (f x : Γ(Y, W))
    (hO : Y.basicOpen f = O) (h : O ≤ W) (hx : rs Y h x = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  subst hO
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Y hW x f hx

theorem exists_fin_cover [CompactSpace Y] {M H : LB Y} (hM : M.IsLB) (hH : H.IsLB) :
    ∃ (κ : Type) (_ : Fintype κ) (W : κ → Y.Opens) (p : κ → M.ι) (l : κ → H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (p a) ⊓ H.U (l a)) ∧ ⊤ ≤ ⨆ a, W a := by
  have h : ∀ x : Y, ∃ (W : Y.Opens) (p : M.ι) (l : H.ι),
      IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U p ⊓ H.U l := by
    intro x
    obtain ⟨p, hp⟩ := LB.mem_of_cover hM x
    obtain ⟨l, hl⟩ := LB.mem_of_cover hH x
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ M.U p ⊓ H.U l from ⟨hp, hl⟩)
        (M.U p ⊓ H.U l).isOpen
    exact ⟨W, p, l, hW, hx, hle⟩
  choose W p l hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set Y))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => p a, fun a => l a, fun a => hW a,
    fun a => hle a, ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem unit_shift {R : Type} [CommRing R] (A B : Rˣ) (t d : ℤ) (k : ℕ) {u v : R}
    (h : u = (B ^ d).val * v) :
    (A * B ^ (t + k * d)).val * v ^ k = u ^ k * (A * B ^ t).val := by
  rw [h, zpow_add, mul_comm (k : ℤ) d, zpow_mul, zpow_natCast]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
  ring

theorem pw_rel {H : LB Y} {d : ℤ} (σ : LB.Sec (pw H d)) (u : ∀ l, Γ(Y, H.U l))
    (hu : ∀ l, u l = σ.f l) (l m : H.ι) {O : Y.Opens}
    (hl : O ≤ H.U l) (hm : O ≤ H.U m) (h : O ≤ H.U l ⊓ H.U m) :
    rs Y hl (u l) = (res h (H.g l m) ^ d).val * rs Y hm (u m) := by
  rw [← map_zpow, hu, hu]
  exact GlobalTheory.LB.sec_rel σ l m hl hm h

end GlobalTheory.AbLaw.TwExtend

namespace GlobalTheory.AbLaw

open TwExtend

theorem exists_tw_extend_pow_mul : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → QuasiSeparatedSpace Y → ∀ y : SecOn (tw M H t) V, ∃ (k : ℕ) (a : SecOn (tw M H (t + k * d)) ⊤), ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_inf_right _ le_top : V ⊓ (M.U p ⊓ H.U l) ≤ ⊤ ⊓ (M.U p ⊓ H.U l)) (SecOn.twCoord a p l) = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord y p l := by
  intro Y H M d σ V t hH hM hV _ _ y
  obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, H.U l), ∀ l, u l = σ.f l := ⟨σ.f, fun _ => rfl⟩
  have hb : ∀ l {W : Y.Opens} (h : W ≤ H.U l), Y.basicOpen (rs Y h (u l)) = V ⊓ W := by
    intro l W h
    rw [hu, hV]
    exact basicOpen_rs_eq σ l h
  have hrel := pw_rel σ u hu
  suffices key : ∃ (k : ℕ) (a : SecOn (tw M H (t + k * d)) ⊤), ∀ (p : M.ι) (l : H.ι),
      rs Y (inf_le_inf_right _ le_top : V ⊓ (M.U p ⊓ H.U l) ≤ ⊤ ⊓ (M.U p ⊓ H.U l))
        (SecOn.twCoord a p l) =
      rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (u l) ^ k *
        SecOn.twCoord y p l by
    simp only [hu] at key
    exact key
  clear hu hV σ
  obtain ⟨κ, _, W, p, l, hW, hWc, hc⟩ := exists_fin_cover hM hH
  have hWl : ∀ a, W a ≤ H.U (l a) := fun a => (hWc a).trans inf_le_right
  have hWp : ∀ a, W a ≤ M.U (p a) := fun a => (hWc a).trans inf_le_left
  choose n x hx using fun a => fun_extend (hW a) (rs Y (hWl a) (u (l a))) (hb _ _) inf_le_right
    (rs Y (inf_le_inf_left V (hWc a)) (SecOn.twCoord y (p a) (l a)))
  obtain ⟨N, hN⟩ : ∃ N, ∀ a, n a ≤ N :=
    ⟨Finset.univ.sup n, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ∀ a, Γ(Y, W a), ∀ a {O : Y.Opens} (hO : O ≤ W a) (hO' : O ≤ V),
      rs Y hO (x' a) = rs Y (hO.trans (hWl a)) (u (l a)) ^ N *
        rs Y (le_inf hO' (hO.trans (hWc a))) (SecOn.twCoord y (p a) (l a)) := by
    refine ⟨fun a => rs Y (hWl a) (u (l a)) ^ (N - n a) * x a, fun a O hO hO' => ?_⟩
    have := congrArg (rs Y (le_inf hO' hO)) (hx a)
    simp only [map_mul, map_pow, rs_rs] at this ⊢
    rw [this, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (hN a)]
  have hk : ∀ q : κ × κ, ∃ K : ℕ, rs Y (inf_le_left.trans (hWl q.1)) (u (l q.1)) ^ K *
      (rs Y (inf_le_left : W q.1 ⊓ W q.2 ≤ _) (x' q.1) -
        (res (inf_le_inf (hWp q.1) (hWp q.2)) (M.g (p q.1) (p q.2)) *
          res (inf_le_inf (hWl q.1) (hWl q.2)) (H.g (l q.1) (l q.2)) ^ (t + N * d)).val *
        rs Y inf_le_right (x' q.2)) = 0 := by
    rintro ⟨a, b⟩
    refine fun_kill (QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hW a).isCompact
      (W b).isOpen (hW b).isCompact) _ _ (hb _ _) inf_le_right ?_
    have hM' : V ⊓ (W a ⊓ W b) ≤ M.U (p a) ⊓ M.U (p b) :=
      inf_le_right.trans (inf_le_inf (hWp a) (hWp b))
    have hH' : V ⊓ (W a ⊓ W b) ≤ H.U (l a) ⊓ H.U (l b) :=
      inf_le_right.trans (inf_le_inf (hWl a) (hWl b))
    have e : rs Y (inf_le_right : V ⊓ (W a ⊓ W b) ≤ W a ⊓ W b)
        (res (inf_le_inf (hWp a) (hWp b)) (M.g (p a) (p b)) *
          res (inf_le_inf (hWl a) (hWl b)) (H.g (l a) (l b)) ^ (t + N * d)).val =
        (res hM' (M.g (p a) (p b)) * res hH' (H.g (l a) (l b)) ^ (t + N * d)).val := by
      refine (GlobalTheory.LB.val_res _ _).symm.trans (congrArg Units.val ?_)
      rw [map_mul, map_zpow, LB.res_res, LB.res_res]
    rw [map_sub, map_mul, e, rs_rs, rs_rs, hx' a _ inf_le_left, hx' b _ inf_le_left,
      SecOn.twCoord_compat y (p a) (p b) (l a) (l b) _
        (inf_le_inf_left V (inf_le_right.trans (hWc b))) hM' hH', ← _root_.mul_assoc,
      ← _root_.mul_assoc, unit_shift _ _ t d N (hrel (l a) (l b) (hH'.trans inf_le_left) _ hH'),
      sub_self]
  choose k hk using hk
  obtain ⟨K, hK⟩ : ∃ K, ∀ q, k q ≤ K :=
    ⟨Finset.univ.sup k, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  have hNK : t + ((N + K : ℕ) : ℤ) * d = t + N * d + K * d := by push_cast; ring
  obtain ⟨s, hs, -⟩ := SecOn.existsUnique_of_local (isLB_tw hM hH (t + ((N + K : ℕ) : ℤ) * d))
    (V := ⊤) W (fun _ => le_top) hc (fun a => (p a, l a)) hWc
    (fun a => rs Y (hWl a) (u (l a)) ^ K * x' a) (fun a b => by
      have e := congrArg Units.val (SecOn.res_tw_g (M := M) (H := H)
        (t + ((N + K : ℕ) : ℤ) * d) (p a) (p b) (l a) (l b) (inf_le_inf (hWc a) (hWc b))
        (inf_le_inf (hWp a) (hWp b)) (inf_le_inf (hWl a) (hWl b)))
      refine Eq.trans ?_ (congrArg (· * rs Y (inf_le_right : W a ⊓ W b ≤ W b)
        (rs Y (hWl b) (u (l b)) ^ K * x' b)) e.symm)
      have h0 := hk (a, b)
      have h1 := unit_shift (res (inf_le_inf (hWp a) (hWp b)) (M.g (p a) (p b))) _ (t + N * d) d K
        (hrel (l a) (l b) (inf_le_left.trans (hWl a)) (inf_le_right.trans (hWl b))
          (inf_le_inf (hWl a) (hWl b)))
      simp only [map_mul, map_pow, rs_rs]
      rw [hNK, ← _root_.mul_assoc, h1, ← Nat.sub_add_cancel (hK (a, b)), pow_add]
      linear_combination
        rs Y (inf_le_left.trans (hWl a) : W a ⊓ W b ≤ _) (u (l a)) ^ (K - k (a, b)) * h0)
  refine ⟨N + K, s, fun q m => ?_⟩
  refine GlobalTheory.LB.fun_ext_of_cover (fun a => V ⊓ (M.U q ⊓ H.U m) ⊓ W a) (fun _ => inf_le_left)
    (GlobalTheory.LB.le_iSup_inf (top_unique hc) _) fun a => ?_
  change rs Y _ _ = rs Y _ _
  have hM' : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ M.U q ⊓ M.U (p a) :=
    inf_le_inf (inf_le_right.trans inf_le_left) (hWp a)
  have hH' : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ H.U m ⊓ H.U (l a) :=
    inf_le_inf (inf_le_right.trans inf_le_right) (hWl a)
  have hs' : rs Y (le_inf le_top (hWc a)) (SecOn.twCoord s (p a) (l a)) =
    rs Y (hWl a) (u (l a)) ^ K * x' a := hs a
  have e := congrArg (rs Y (inf_le_right : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ W a)) hs'
  rw [map_mul, map_pow, rs_rs, rs_rs, hx' a _ (inf_le_left.trans inf_le_left),
    ← _root_.mul_assoc, ← pow_add, add_comm K N] at e
  rw [map_mul, map_pow, rs_rs, rs_rs,
    SecOn.twCoord_compat s q (p a) m (l a) _ (le_inf le_top (inf_le_right.trans (hWc a))) hM' hH',
    SecOn.twCoord_compat y q (p a) m (l a) _
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans (hWc a))) hM' hH',
    e, ← _root_.mul_assoc, ← _root_.mul_assoc,
    unit_shift _ _ t d (N + K) (hrel m (l a) (hH'.trans inf_le_left) _ hH')]

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteQuotSMulTopXSubOneOfChart
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
open Pointwise in
theorem _root_.GlobalTheory.finite_quotSMulTop_X_sub_one_of_chart : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [_root_.GlobalTheory.PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (i : ι) (B : Type) (_ : CommRing B) (_ : Algebra R B)
    (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
    (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
    (Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
      ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) →
    (Module.Finite B P → Module.Finite (MvPolynomial ι R)
      (QuotSMulTop ((MvPolynomial.X i : MvPolynomial ι R) - 1) G)) ∧
    (Algebra.FinitePresentation R B → Module.FinitePresentation B P →
      Module.FinitePresentation (MvPolynomial ι R)
        (QuotSMulTop ((MvPolynomial.X i : MvPolynomial ι R) - 1) G)) := by
  open scoped Pointwise in
  intro ι _ _ R _ G _ _ _ _ 𝒢 _ _ i B _ _ π P _ _ ε ⟨hπs, hπX, hεs, hker⟩
  letI : Algebra (MvPolynomial ι R) B := (π : MvPolynomial ι R →+* B).toAlgebra
  letI : Module (MvPolynomial ι R) P := Module.compHom P (π : MvPolynomial ι R →+* B)
  haveI : IsScalarTower (MvPolynomial ι R) B P :=
    ⟨fun a b p => by
      change (π a * b) • p = π a • b • p
      exact mul_smul _ _ _⟩
  have hkerε : ∀ y, ε y = 0 ↔ ∃ w : G, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w :=
    _root_.GlobalTheory.dehomogenising_eq_zero_iff ι R G 𝒢 i B (π : MvPolynomial ι R →+* B) P ε hπX hker
  let ε' : G →ₗ[MvPolynomial ι R] P :=
    { toFun := ε
      map_add' := ε.map_add
      map_smul' := fun a g => ε.map_smulₛₗ a g }
  have hle : ((MvPolynomial.X i : MvPolynomial ι R) - 1) • (⊤ : Submodule (MvPolynomial ι R) G) ≤
      LinearMap.ker ε' := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact (hkerε _).2 ⟨y, rfl⟩
  let φ := Submodule.liftQ _ ε' hle
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.ker_liftQ_eq_bot
    intro x hx
    obtain ⟨w, rfl⟩ := (hkerε x).1 hx
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨w, trivial, rfl⟩
  have hsurj : Function.Surjective φ := by
    intro p
    obtain ⟨g, rfl⟩ := hεs p
    exact ⟨Submodule.Quotient.mk g, rfl⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  haveI : Module.Finite (MvPolynomial ι R) B :=
    Module.Finite.of_surjective (Algebra.linearMap (MvPolynomial ι R) B) hπs
  refine ⟨fun hP => ?_, fun hB hPfp => ?_⟩
  · haveI : Module.Finite (MvPolynomial ι R) P := Module.Finite.trans B P
    exact Module.Finite.equiv e.symm
  · haveI : IsScalarTower R (MvPolynomial ι R) B :=
      IsScalarTower.of_algebraMap_eq (fun r => (π.commutes r).symm)
    haveI : Algebra.FinitePresentation (MvPolynomial ι R) B :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) B
    haveI : Module.FinitePresentation (MvPolynomial ι R) B :=
      Module.FinitePresentation.of_finite_of_finitePresentation _ _
    haveI : Module.FinitePresentation (MvPolynomial ι R) P :=
      Module.FinitePresentation.trans (MvPolynomial ι R) P B
    exact Module.finitePresentation_of_surjective e.symm.toLinearMap e.symm.surjective
      (by rw [LinearEquiv.ker]; exact Submodule.fg_bot)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularLocalRingAndRingKrullDimEqOfPolAV
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem isRegularLocalRing_and_ringKrullDim_eq_of_polAV :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t₀ : Spec (CommRingCat.of R) ⟶ P.A.left) (m : Ideal R) [m.IsMaximal] (O : Type) [CommRing O] [Algebra R O] [IsLocalization.AtPrime O m], IsOpenImmersion t₀ → IsRegularLocalRing O ∧ ringKrullDim O = P.g := by
  intro K _ _ P R _ t₀ m hm O _ _ _ ht
  have hab := P.isAb
  have hd := P.smoothDim
  have hsm : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  have hgi : GeometricallyIntegral P.A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsm hab.geomConnected
  have hint : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have hnt : Nontrivial R := ⟨⟨0, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).2 (h ▸ m.zero_mem))⟩⟩
  let φ : CommRingCat.of K ⟶ CommRingCat.of R := Spec.preimage (t₀ ≫ P.A.hom)
  have hφ : t₀ ≫ P.A.hom = Spec.map φ := (Spec.map_preimage _).symm
  let _ : Algebra K R := φ.hom.toAlgebra
  have hφ' : t₀ ≫ P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)) := hφ
  have htr : Algebra.trdeg K R = P.g :=
    trdeg_eq_of_smoothOfRelativeDimension K P.A.left P.A.hom P.g hd R t₀ ht hφ'
  have : IsIntegral (Spec (CommRingCat.of R)) := isIntegral_of_isOpenImmersion t₀
  have : IsDomain R := (affine_isIntegral_iff (CommRingCat.of R)).1 inferInstance
  have hs : Smooth (Spec.map φ) := hφ ▸ inferInstance
  have hs' : Algebra.Smooth K R := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  have hreg : IsRegularRing R := isRegularRing_of_smooth K R
  have hh := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field P.g htr m
  refine ⟨?_, ?_⟩
  · have := isRegularRing_iff.mp hreg m
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv m.primeCompl
      (Localization.AtPrime m) O).toRingEquiv
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height m O, hh]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnBasicOpenLocalization
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem secOn_basicOpen_localization :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V W : Y.Opens) (a : Γ(Y, V)) (h : W ≤ V), M.IsLB → IsCompact (V : Set Y) → IsQuasiSeparated (V : Set Y) → W = Y.basicOpen a → (∀ x : SecOn M V, SecOn.restrict M h x = 0 → ∃ k : ℕ, a ^ k • x = 0) ∧ ∀ y : SecOn M W, ∃ (k : ℕ) (x : SecOn M V), SecOn.restrict M h x = rs Y h a ^ k • y := by
  intro Y M V W a h hM hV hV' hW
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hM
  refine ⟨fun x hx => GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact (GlobalTheory.LB.toMod M) hV a h hW x hx,
    fun y => ?_⟩
  obtain ⟨k, x, e⟩ := GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod M) hV hV' a h hW y
  exact ⟨k, x, e.symm⟩

end GlobalTheory.AbLaw
end

