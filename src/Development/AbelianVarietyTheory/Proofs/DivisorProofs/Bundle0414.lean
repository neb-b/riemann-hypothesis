module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0376
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexPairingTensorUniversalProperty
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.TensFam

variable {R : Type} [CommRing R]

theorem tensRes_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  simp [Tens.res, DirectSum.lmap_lof]

theorem tensRes_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = (Tens.res f w).comp (Tens.res g w) := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  simp [Tens.res, DirectSum.lmap_lof]

theorem lift_resL {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    (τ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (τ.lift U w) := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  have := τ.nat g p.1.1 p.1.2 w p.2 a b
  simp [Tens.res, Pair.lift, DirectSum.lmap_lof] at this ⊢
  exact this.symm

def tensP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} where
  obj U := AddCommGrpCat.of (Tens I J U.unop w)
  map g := AddCommGrpCat.ofHom (Tens.res g.unop w).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.ext; intro x
    change Tens.res (I := I) (J := J) (𝟙 U.unop) w x = x
    rw [tensRes_id]; rfl
  map_comp f g := by
    apply AddCommGrpCat.ext; intro x
    change Tens.res (I := I) (J := J) (g.unop ≫ f.unop) w x = Tens.res g.unop w (Tens.res f.unop w x)
    rw [tensRes_comp]; rfl

def secP (F : Shv R) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} := F.obj ⋙ forget₂ _ AddCommGrpCat

def liftP {I J K : Cx R} (τ : Pair I J K) (w : ℤ) : tensP I J w ⟶ secP (K.X w) where
  app U := AddCommGrpCat.ofHom (τ.lift U.unop w).toAddMonoidHom
  naturality V U g := by
    apply AddCommGrpCat.ext; intro x
    exact LinearMap.congr_fun (lift_resL τ g.unop w) x

end GlobalTheory.EtC.TensFam


open GlobalTheory.EtC.TensFam in
theorem GlobalTheory.EtC.tens_fam : ∀ (R S : Type) [CommRing R] [CommRing S] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) → ∃ φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧ ∀ U x, φ U (τ.lift U w x) = b U x := by
  intro R S _ _ I J K τ hτ w M b hb
  exact GlobalTheory.T.etaleSheaf_descend_along_locallyBijective S (tensP I J w) (secP (K.X w)) (liftP τ w)
    (fun U y => hτ.1 U w y) (fun U x hx => hτ.2 U w x hx) M b hb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
section
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

namespace GlobalTheory.Sandwich.HodgeTateBound

section General

variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}

end General

open Matrix in
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] in
private lemma mul_eq_smul_one_of_mul_eq_smul_one [IsDomain R] {A B : Matrix n n R} {c : R}
    (hc : c ≠ 0) (hBA : B * A = c • (1 : Matrix n n R)) : A * B = c • (1 : Matrix n n R) := by
  have hdet : A.det ≠ 0 := by
    intro h0
    have hprod : B.det * A.det = c ^ Fintype.card n := by
      rw [← det_mul, hBA, det_smul, det_one, mul_one]
    rw [h0, mul_zero] at hprod
    exact pow_ne_zero _ hc hprod.symm
  have key : A.det • (A * B) = A.det • (c • (1 : Matrix n n R)) := by
    calc A.det • (A * B) = (A * B) * (A * adjugate A) := by
          rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = A * (B * A) * adjugate A := by simp only [Matrix.mul_assoc]
      _ = A.det • (c • (1 : Matrix n n R)) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, mul_adjugate, smul_smul,
            smul_smul, mul_comm]
  ext i j
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact mul_left_cancel₀ hdet hij

open Matrix in
variable {A O : Type*} [CommRing A] [CommRing O] {h : ℕ} in
private lemma smul_mem_range_of_mem_ker_of_mul_eq (θ : A →+* O) (hθ : Function.Surjective θ)
    {ξ ν : A} (hker : RingHom.ker θ = Ideal.span {ξ}) (hξ : ∀ y : A, y * ξ = 0 → y = 0)
    {P Q : Matrix (Fin h) (Fin h) A} (hQP : Q * P = (ξ * ν) • (1 : Matrix (Fin h) (Fin h) A))
    (t : Fin h → O) (ht : t ∈ LinearMap.ker (toLin' (P.map θ))) :
    θ ν • t ∈ LinearMap.range (toLin' (Q.map θ)) := by
  choose s hs using fun i => hθ (t i)
  have hst : (θ ∘ s) = t := funext hs
  rw [LinearMap.mem_ker, toLin'_apply] at ht
  have hmem : ∀ i, (P *ᵥ s) i ∈ Ideal.span {ξ} := by
    intro i
    rw [← hker, RingHom.mem_ker, RingHom.map_mulVec, hst]
    exact congrFun ht i
  choose g hg using fun i => Ideal.mem_span_singleton'.mp (hmem i)
  have hQg : Q *ᵥ g = ν • s := by
    funext i
    apply sub_eq_zero.mp
    apply hξ
    have h1 : Q *ᵥ (P *ᵥ s) = (ξ * ν) • s := by
      rw [mulVec_mulVec, hQP, Matrix.smul_mulVec, one_mulVec]
    have h2 : P *ᵥ s = fun j => g j * ξ := funext fun j => (hg j).symm
    have h3 := congrFun h1 i
    rw [h2] at h3
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h3 ⊢
    have h4 : ∑ j, Q i j * (g j * ξ) = (∑ j, Q i j * g j) * ξ := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    rw [h4] at h3
    linear_combination h3
  refine ⟨θ ∘ g, ?_⟩
  rw [toLin'_apply]
  funext i
  rw [← RingHom.map_mulVec, hQg]
  simp [← hs]

open Matrix in
variable {O : Type*} [CommRing O] {h : ℕ} in
private lemma map_iInf_eigenspace_le_of_intertwine {ι : Type*} {X Y : ι → Matrix (Fin h) (Fin h) O}
    {Z : Matrix (Fin h) (Fin h) O} (c : ι → O) (hZ : ∀ a, Y a * Z = Z * X a) :
    (⨅ a, Module.End.eigenspace (toLin' (X a)) (c a)).map (toLin' Z) ≤
      ⨅ a, Module.End.eigenspace (toLin' (Y a)) (c a) := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hx
  rw [Submodule.mem_iInf]
  intro a
  have hxa := hx a
  rw [Module.End.mem_eigenspace_iff, toLin'_apply] at hxa ⊢
  rw [toLin'_apply, mulVec_mulVec, hZ, ← mulVec_mulVec, hxa, mulVec_smul]


open Matrix in
theorem _root_.GlobalTheory.Sandwich.HodgeTateBound.bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ ε : PreTilt O p, IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ], ∀ (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ),
    D.F * D.G =
        _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧
      LinearMap.range D.al ≤ D.Fil ∧
      D.Lie ≤ LinearMap.ker D.al ∧
      (∀ f ∈ D.Fil, WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • f ∈
        LinearMap.range D.al) ∧
      (∀ t ∈ LinearMap.ker D.al,
        WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • t ∈ D.Lie) ∧
      (∀ τ : Λ →+* O, (D.Tsub τ).map D.al ≤
          D.Fil ⊓ D.Hsub τ ∧
        (D.Hsub τ).map D.bb ≤
          D.Lie ⊓ D.Tsub τ ∧
        D.Lie ⊓ D.Tsub τ ≤
          D.W τ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  have hker := _root_.GlobalTheory.AinfXi.ker_theta hv ε hε
  have hξ := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε
  have hsurj : Function.Surjective (WittVector.fontaineTheta O p) := _root_.ReciprocityTheory.PGsh.Ainf.theta_surj p O hv
  have hμ := _root_.GlobalTheory.Sandwich.xi_mul_nu ε
  have hθξ : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  have hθμ : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.mu ε) = 0 := by
    rw [← hμ, map_mul, hθξ, zero_mul]
  have hξ0 : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    exact one_ne_zero (hξ 1 (by rw [h0, mul_zero]))
  have hν0 : _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by
    intro h0
    have h1 : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) =
        PreTilt.untilt (_root_.GlobalTheory.Sandwich.root ε) - 1 := by
      simp [_root_.GlobalTheory.Sandwich.nu, WittVector.fontaineTheta_teichmuller]
    rw [h0, map_zero] at h1
    exact hε.ne_one (Fact.out : p.Prime).one_lt (sub_eq_zero.mp h1.symm)
  have hμ0 : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
    rw [← hμ]
    exact mul_ne_zero hξ0 hν0
  have hGF := D.G_mul_F
  have hFG := mul_eq_smul_one_of_mul_eq_smul_one hμ0 hGF
  have hA : D.G.map (WittVector.fontaineTheta O p) *
      D.F.map (WittVector.fontaineTheta O p) = 0 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [hθμ]
  have hB : D.F.map (WittVector.fontaineTheta O p) *
      D.G.map (WittVector.fontaineTheta O p) = 0 := by
    rw [← Matrix.map_mul, hFG]
    ext i j
    simp [hθμ]
  have hpad : ∀ M : Matrix (Fin h) (Fin h) ℤ_[p],
      (M.map (_root_.GlobalTheory.Sandwich.ofPadic p O)).map (WittVector.fontaineTheta O p) = M.map (_root_.GlobalTheory.Sandwich.padicToO p O) := by
    intro M
    ext i j
    simp [_root_.GlobalTheory.Sandwich.padicToO]
  have hact := D.F_act
  have hGact : ∀ a, (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G =
      D.G * D.ρM a := by
    intro a
    have e : _root_.GlobalTheory.Sandwich.mu ε •
        ((D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G) =
        _root_.GlobalTheory.Sandwich.mu ε • (D.G * D.ρM a) := by
      calc _ = D.G * D.F *
              (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G := by
            rw [hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
        _ = D.G * (D.F *
              (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O)) * D.G := by
            simp only [Matrix.mul_assoc]
        _ = D.G * (D.ρM a * D.F) *
              D.G := by rw [hact a]
        _ = D.G * D.ρM a *
              (D.F * D.G) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hFG, Matrix.mul_smul, Matrix.mul_one]
    refine Matrix.ext fun i j => ?_
    have hij := congrFun (congrFun e i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    exact mul_left_cancel₀ hμ0 hij
  simp only [_root_.GlobalTheory.Sandwich.Datum.al, _root_.GlobalTheory.Sandwich.Datum.bb,
    _root_.GlobalTheory.Sandwich.Datum.Fil, _root_.GlobalTheory.Sandwich.Datum.Lie,
    _root_.GlobalTheory.Sandwich.Datum.Tsub, _root_.GlobalTheory.Sandwich.Datum.Hsub,
    _root_.GlobalTheory.Sandwich.Datum.W]
  have hrange : LinearMap.range (toLin' (D.F.map (WittVector.fontaineTheta O p))) ≤
      LinearMap.ker (toLin' (D.G.map (WittVector.fontaineTheta O p))) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, hA, zero_mulVec]
  have hlie : LinearMap.range (toLin' (D.G.map (WittVector.fontaineTheta O p))) ≤
      LinearMap.ker (toLin' (D.F.map (WittVector.fontaineTheta O p))) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, hB, zero_mulVec]
  refine ⟨hFG, hrange, hlie, ?_, ?_, ?_⟩
  · exact smul_mem_range_of_mem_ker_of_mul_eq _ hsurj hker hξ (by rw [hFG, hμ])
  · exact smul_mem_range_of_mem_ker_of_mul_eq _ hsurj hker hξ (by rw [hGF, hμ])
  · intro τ
    refine ⟨le_inf (LinearMap.map_le_range.trans hrange) ?_,
      le_inf LinearMap.map_le_range ?_, fun x hx => ⟨hx.2, hlie hx.1⟩⟩
    · refine map_iInf_eigenspace_le_of_intertwine τ fun a => ?_
      rw [← Matrix.map_mul, ← hact a, Matrix.map_mul, hpad]
    · refine map_iInf_eigenspace_le_of_intertwine τ fun a => ?_
      rw [← hpad, ← Matrix.map_mul, hGact a, Matrix.map_mul]

end GlobalTheory.Sandwich.HodgeTateBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRegularFormsFiniteProjectiveSmooth
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem projective_exteriorPower_of_projective (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Projective R V] (n : ℕ) : Module.Projective R (⋀[R]^n V) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R V)
  haveI : Module.Free R (⋀[R]^n (V →₀ R)) := exteriorPower.instFree R n
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

theorem span_omB_comap_finite_projective : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Module.Finite B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) ∧ Module.Projective B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) := by
  intro k K _ _ _ B _ _ p W _ _ _ _ e he hr
  obtain ⟨e', he', hre', -⟩ := GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower k K B p
  have hom := fun a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B p p).2.1 a ha)
  let S : Submodule k W := (omB k K B p).comap (e.restrictScalars k)
  let T : Submodule B W :=
    { carrier := (S : Set W)
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun c w hw => by
        change e ((c : K) • w) ∈ omB k K B p
        rw [map_smul]
        exact (hom _ hw).2.2.2 c c.2 }
  have hST : Submodule.span B (S : Set W) = T := Submodule.span_eq T
  change Module.Finite B (Submodule.span B (S : Set W)) ∧ Module.Projective B (Submodule.span B (S : Set W))
  rw [hST]
  let g : T →ₗ[B] DR k K :=
    { toFun := fun w => e w
      map_add' := fun w w' => by simp
      map_smul' := fun c w => by
        change e ((c : K) • (w : W)) = (c : K) • e w
        exact e.map_smul (c : K) w }
  have hg : Function.Injective g := fun w w' h => Subtype.ext (he h)
  have hrg : LinearMap.range g = LinearMap.range e' := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := (hre' _).1 w.2
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      have hy : e' z ∈ omB k K B p := (hre' _).2 ⟨z, rfl⟩
      have hy' : e' z ∈ LinearMap.range e := by rw [hr]; exact (hom _ hy).2.2.1
      obtain ⟨w, hw⟩ := hy'
      have hwT : w ∈ T := by
        change e w ∈ omB k K B p
        rw [hw]; exact hy
      exact ⟨⟨w, hwT⟩, hw⟩
  let E : T ≃ₗ[B] ⋀[B]^p Ω[B⁄k] :=
    (LinearEquiv.ofInjective g hg).trans ((LinearEquiv.ofEq _ _ hrg).trans (LinearEquiv.ofInjective e' he').symm)
  haveI : Module.Projective B (⋀[B]^p Ω[B⁄k]) := projective_exteriorPower_of_projective B _ p
  exact ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm⟩

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i}, ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  first | (exact @GlobalTheory.PD.rA_single_polyEquiv) | (exact GlobalTheory.PD.rA_single_polyEquiv) | (intros; apply GlobalTheory.PD.rA_single_polyEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SxProdIsoHomSnd
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

def sxProdIso (A B : Spc) (p : ℕ) :
    (A ⨯ B).obj (op (SimplexCategory.mk p)) ≅ FunctorToTypes.prod (A.obj (op (SimplexCategory.mk p))) (B.obj (op (SimplexCategory.mk p))) :=
  PreservesLimitPair.iso ((evaluation _ _).obj (op (SimplexCategory.mk p))) A B ≪≫ FunctorToTypes.binaryProductIso _ _

theorem sxProdIso_hom_fst (A B : Spc) (p : ℕ) :
    (sxProdIso A B p).hom ≫ FunctorToTypes.prod.fst = (prod.fst : A ⨯ B ⟶ A).app (op (SimplexCategory.mk p)) := by
  rw [sxProdIso, Iso.trans_hom, Category.assoc]
  erw [FunctorToTypes.binaryProductIso_hom_comp_fst]
  rw [PreservesLimitPair.iso_hom]
  erw [prodComparison_fst]
  rfl

theorem sxProdIso_hom_snd (A B : Spc) (p : ℕ) :
    (sxProdIso A B p).hom ≫ FunctorToTypes.prod.snd = (prod.snd : A ⨯ B ⟶ B).app (op (SimplexCategory.mk p)) := by
  rw [sxProdIso, Iso.trans_hom, Category.assoc]
  erw [FunctorToTypes.binaryProductIso_hom_comp_snd]
  rw [PreservesLimitPair.iso_hom]
  erw [prodComparison_snd]
  rfl

theorem sxProdIso_inv_fst (A B : Spc) (p : ℕ) :
    (sxProdIso A B p).inv ≫ (prod.fst : A ⨯ B ⟶ A).app (op (SimplexCategory.mk p)) = FunctorToTypes.prod.fst := by
  rw [Iso.inv_comp_eq, sxProdIso_hom_fst]

theorem sxProdIso_inv_snd (A B : Spc) (p : ℕ) :
    (sxProdIso A B p).inv ≫ (prod.snd : A ⨯ B ⟶ B).app (op (SimplexCategory.mk p)) = FunctorToTypes.prod.snd := by
  rw [Iso.inv_comp_eq, sxProdIso_hom_snd]

def sxPair {A B : Spc} {p : ℕ} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx (A ⨯ B) p V :=
  ((sxProdIso A B p).inv.app (op V)) (show (FunctorToTypes.prod (A.obj (op (SimplexCategory.mk p))) (B.obj (op (SimplexCategory.mk p)))).obj (op V) from (a, b))

@[simp] theorem sxPair_fst {A B : Spc} {p : ℕ} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) :
    (sxPair a b).map prod.fst = a := by
  exact ConcreteCategory.congr_hom (congr_app (sxProdIso_inv_fst A B p) (op V)) (((a, b) : Sx A p V × Sx B p V) : (FunctorToTypes.prod (A.obj (op (SimplexCategory.mk p))) (B.obj (op (SimplexCategory.mk p)))).obj (op V))

@[simp] theorem sxPair_snd {A B : Spc} {p : ℕ} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) :
    (sxPair a b).map prod.snd = b := by
  exact ConcreteCategory.congr_hom (congr_app (sxProdIso_inv_snd A B p) (op V)) (((a, b) : Sx A p V × Sx B p V) : (FunctorToTypes.prod (A.obj (op (SimplexCategory.mk p))) (B.obj (op (SimplexCategory.mk p)))).obj (op V))

theorem sxPair_eta {A B : Spc} {p : ℕ} {V : Scheme.{0}} (y : Sx (A ⨯ B) p V) :
    sxPair (y.map prod.fst) (y.map prod.snd) = y := by
  have h1 := ConcreteCategory.congr_hom (congr_app (sxProdIso_hom_fst A B p) (op V)) y
  have h2 := ConcreteCategory.congr_hom (congr_app (sxProdIso_hom_snd A B p) (op V)) y
  have : ((sxProdIso A B p).hom.app (op V)) y = (y.map prod.fst, y.map prod.snd) := Prod.ext h1 h2
  rw [sxPair, ← this]
  exact ConcreteCategory.congr_hom (congr_app (sxProdIso A B p).hom_inv_id (op V)) y

theorem sx_prod_ext {A B : Spc} {p : ℕ} {V : Scheme.{0}} {y y' : Sx (A ⨯ B) p V}
    (h1 : y.map prod.fst = y'.map prod.fst) (h2 : y.map prod.snd = y'.map prod.snd) : y = y' := by
  rw [← sxPair_eta y, ← sxPair_eta y', h1, h2]

theorem sxMap_res {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    (x.res g).map f = (x.map f).res g :=
  ConcreteCategory.congr_hom ((f.app (op (SimplexCategory.mk p))).naturality g.op) x

theorem sxMap_comp {E E' E'' : Spc} (f : E ⟶ E') (f' : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    x.map (f ≫ f') = (x.map f).map f' := rfl

theorem sxPair_res {A B : Spc} {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (a : Sx A p U) (b : Sx B p U) :
    (sxPair a b).res g = sxPair (a.res g) (b.res g) :=
  sx_prod_ext (by rw [sxMap_res, sxPair_fst, sxPair_fst]) (by rw [sxMap_res, sxPair_snd, sxPair_snd])

theorem sxPair_map {A B A' B' : Spc} (f : A ⟶ A') (f' : B ⟶ B') {p : ℕ} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) :
    (sxPair a b).map (prod.map f f') = sxPair (a.map f) (b.map f') :=
  sx_prod_ext (by rw [← sxMap_comp, prod.map_fst, sxMap_comp, sxPair_fst, sxPair_fst])
    (by rw [← sxMap_comp, prod.map_snd, sxMap_comp, sxPair_snd, sxPair_snd])

variable {R : Type} [CommRing R]

theorem secRes_res {F : Shv R} {U V W : Scheme.{0}} (g : V ⟶ U) (g' : W ⟶ V) (b : Sec F U) :
    Sec.res g' (Sec.res g b) = Sec.res (g' ≫ g) b := by
  rw [Sec.res, Sec.res, Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem ev_smulU {E : Spc} {I : Cx R} {n : ℤ} (r : ULift.{1} R) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    _root_.GlobalTheory.EtC.ev (R := R) (r • α) p s h U x =
      r • _root_.GlobalTheory.EtC.ev (R := R) α p s h U x := by
  unfold _root_.GlobalTheory.EtC.ev
  rw [Cochain.smul_v, Linear.comp_smul]
  rfl

def schSx {V W : Scheme.{0}} (v : W ⟶ V) (p : ℕ) : Sx (sch.obj V) p W := v

theorem schSx_map {V V' W : Scheme.{0}} (v : W ⟶ V) (u : V ⟶ V') (p : ℕ) :
    (schSx v p).map (sch.map u) = schSx (v ≫ u) p := rfl

def evLin (I : Cx R) (E : Spc) (n : ℤ) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →ₗ[ULift.{1} R] Sec (I.X s) U where
  toFun α := _root_.GlobalTheory.EtC.ev (R := R) α p s h U x
  map_add' α β := by
    simp [_root_.GlobalTheory.EtC.ev, Cochain.add_v]
  map_smul' r α := ev_smulU r α p s h U x

theorem cotPre_ev (q N : ℕ) (I : Cx R) (n : ℤ) {U V : Scheme.{0}} (v : V ⟶ U)
    (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0})
    (y : Sx (sch.obj V ⨯ fibQ q N) p W) :
    _root_.GlobalTheory.EtC.ev (R := R) (I := I) (E := sch.obj V ⨯ fibQ q N)
        (((cotPre R q N I n).map v.op).hom c) p s h W y =
      _root_.GlobalTheory.EtC.ev (R := R) c p s h W (y.map (prod.map (sch.map v) (𝟙 _))) := by
  let f : sch.obj V ⨯ fibQ q N ⟶ sch.obj U ⨯ fibQ q N := prod.map (sch.map v) (𝟙 _)
  change _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp c (zero_add n))
    p s h W y = _root_.GlobalTheory.EtC.ev (R := R) c p s h W (y.map f)
  unfold _root_.GlobalTheory.EtC.ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc,
    _root_.GlobalTheory.EtC.CupSpec.chains_map, Category.assoc]
  change Sec.map ((chainsXIso R (sch.obj U ⨯ fibQ q N) p).inv ≫ c.v _ _ h)
    (Sec.map ((free R).map (f.app (op (SimplexCategory.mk p)))) (freeGen R _ W y)) = _
  rw [_root_.GlobalTheory.EtC.CupSpec.freeGen_map]
  rfl

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummandStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistModule_free_and_generator_summand : ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [Nontrivial A], Module.Free (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ∧ ∀ ζ : Prim q A, ∃ f : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), f (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  first | (exact @GlobalTheory.TwFree.twist_free) | (exact GlobalTheory.TwFree.twist_free) | (intros; apply GlobalTheory.TwFree.twist_free  <;> assumption)
end

