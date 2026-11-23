module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0009
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0006
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
section
noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison.Br

def LocFacts : Prop := ∀ (A : Type) [CommRing A] (a t : A), (∃ r : ℕ, a ∣ t ^ r) →
  (∀ x : Formalism.Per6.Loc2 a t, ∃ (r : ℕ) (y : A), Formalism.Per6.Loc2.mk₀ a t t ^ r * x = Formalism.Per6.Loc2.mk₀ a t y) ∧
    ∀ y : A, Formalism.Per6.Loc2.mk₀ a t y = 0 → ∃ r : ℕ, t ^ r * y = 0

def ActEq : Prop := ∀ (l : ℕ) [Fact l.Prime], (∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (x : Acris l),
    galA g x = GroundTheory.PAdicHodge.ACris.galCris (Formalism.Per6.toBot g.1) x) ∧ ∀ z : ℤ_[l], Formalism.Per6.zB l z = Formalism.Per6.cB l (zA l z)

def PBTied : Prop := ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ K : FinExt l,
  ∃ (B : PB l K.1) (e : P.R.B ≃ₐ[ℚ_[l]] B.C), (∀ (g : ↥(GK K)) b, e (P.actQ (g : GQ l) b) = B.σ g (e b)) ∧ (∀ b, e (P.φB b) = B.φ (e b)) ∧
    Function.Injective B.φ

def AnnDrop : Prop := ∀ (F G B C : Type) [Field F] [Group G] [CommRing B] [Algebra F B] [CommRing C] [Algebra F C] (σ : G → End F B)
  (φ : B →ₐ[F] B) (s : G → (C →ₐ[F] C)) (ψ : C →ₐ[F] C) (e : B ≃ₐ[F] C), (∀ g b, e (σ g b) = s g (e b)) → (∀ b, e (φ b) = ψ (e b)) →
  Function.Injective ψ → ∀ (V : Type 1) [AddCommGroup V] [Module F V] (V₀ : Type) [AddCommGroup V₀] [Module F V₀] (i : V ≃ₗ[F] V₀)
    (act : G → End F V) (ρ : Representation F G V₀), (∀ g v, ρ g (i v) = i (act g v)) → ∀ (f q n N : ℕ) (A : Fin (n + 1) → End F V)
    (T : ℕ → End F V₀), (∀ (j : Fin (n + 1)) v, T j (i v) = i (A j v)) →
    (∀ x : V ⊗[F] C, (∀ g, TensorProduct.map (act g) (s g).toLinearMap x = x) →
      ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) • TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j + N))) x = 0) →
    AnnD σ (φ.toLinearMap ^ f) q n ρ T

def FinAll : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  [IsDomain (OK l K)] [IsDiscreteValuationRing (OK l K)] (f : ℕ), 0 < f → Nat.card (IsLocalRing.ResidueField (OK l K)) = l ^ f →
  ∀ (ϖ : OK l K), Irreducible ϖ → ∀ (M : Model l K), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) → ∀ B₀ : PB l K, ∃ N : ℕ, ∀ x, IsInv B₀ M j x →
    ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)) •
      TensorProduct.map (A i) (B₀.φ.toLinearMap ^ (f * (n - i + N))) x = 0

def AnnModel : Prop := FinAll → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (K : FinExt l)
  [IsDomain (OK l K.1)] [IsDiscreteValuationRing (OK l K.1)] (f : ℕ), 0 < f → Nat.card (IsLocalRing.ResidueField (OK l K.1)) = l ^ f →
  ∀ (ϖ : OK l K.1), Irreducible ϖ → ∀ (M : Model l K.1), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) →
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module ℚ_[l] V₀] (i : M.V j ≃ₗ[ℚ_[l]] V₀) (ρ : Representation ℚ_[l] ↥(GK K) V₀),
    (∀ g v, ρ g (i v) = i (M.act j g v)) → ∀ T₀ : ℕ → End ℚ_[l] V₀, (∀ (a : Fin (n + 1)) v, T₀ a (i v) = i (A a v)) →
    AnnD (σCr P K) (ψCr P f) (l ^ f) n ρ T₀

end UpperTheory.Gal.crystallineComparison.Br
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAffFin
section
open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.affFin_of :
    AffFinProj := by
  intro R _ Y f hf s
  haveI : GlobalTheory.FiniteSubsetsInAffineOpens Y := GlobalTheory.FiniteSubsetsInAffineOpens.of_isProjOver hf
  obtain ⟨U, hU, hsub⟩ :=
    GlobalTheory.FiniteSubsetsInAffineOpens.exists_isAffineOpen (X := Y) (s : Set Y) s.finite_toSet
  exact ⟨U, hU, fun x hx => hsub (Finset.mem_coe.mpr hx)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetBasis
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detBasis_of :
    BasisIn := by
  intro C W X _ _ _ _ a mk hspan hfin
  obtain ⟨t, hts, hst, hli⟩ := exists_linearIndependent C (Set.range mk)
  have htop : ⊤ ≤ Submodule.span C (Set.range ((↑) : t → W)) := by
    rw [Subtype.range_coe, hst, hspan]
  let b₀ : Basis t C W := Basis.mk hli htop
  haveI : Finite t := Module.Finite.finite_basis b₀
  haveI : Fintype t := Fintype.ofFinite t
  have hcard : Fintype.card t = a := by
    rw [← hfin, Module.finrank_eq_card_basis b₀]
  let e : t ≃ Fin a := Fintype.equivFinOfCardEq hcard
  have hx : ∀ k : Fin a, ∃ x : X, mk x = ((e.symm k : t) : W) := fun k => hts (e.symm k).2
  choose x hx using hx
  refine ⟨x, b₀.reindex e, fun k => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply, hx k]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCo_of :
    CoFacts := by
  intro F L B _ _ _ _ _ a
  refine ⟨fun x y => ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    simp [co, map_add (f := _)]
  · intro c x
    funext i
    show AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id (c • x) =
      (c ⊗ₜ[F] (1 : B)) * AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id x
    rw [map_smul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  · intro b x
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp [co]
    | tmul m n => simp [co, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp_all [co, mul_add]
  · intro T A hT s x
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp [co, Matrix.mulVec, dotProduct]
    | tmul m n =>
      simp [co, onR, hT, Matrix.mulVec, dotProduct, TensorProduct.sum_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply] at hx hy ⊢
      simp_all [co, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  · convert (AlgebraTensorModule.congr (LinearEquiv.funUnique (Fin 1) L L)
      (LinearEquiv.refl F B)).bijective using 1
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp [co]
    | tmul m n => simp [co]
    | add x y hx hy => simp_all [co]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCoLift
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

set_option maxHeartbeats 1600000 in
theorem UpperTheory.Gal.crystallineComparison.detCoLift_of :
    CoFacts → WdLift → CoLift := by
  intro hco hwd l _ P ι K LL a ρ S _ _ π h1 h2
  obtain ⟨f1, f2, f3, -, -⟩ := hco ℚ_[l] ↥LL.1 (Bst P) a
  refine Exists.elim (hwd l P ι K LL (Fin a → ↥LL.1) ρ (Fin a → S)
    (fun x i => π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) ?_ ?_ ?_)
    fun j hj => ⟨j, fun x i => by rw [hj]⟩
  · intro x y
    funext i
    rw [Submodule.coe_add, f1, Pi.add_apply, Pi.add_apply, map_add (f := _)]
  · intro c x
    funext i
    change π (co (c • (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) i) = _
    rw [f2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, h1,
      Algebra.smul_def]
  · intro c x
    funext i
    have e : co (mulV P ↥LL.1 (Fin a → ↥LL.1) c (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) = _ :=
      f3 (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)
    show π (co (mulV P ↥LL.1 (Fin a → ↥LL.1) c (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) i) =
      ι (c : Om l) • π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)
    rw [e, Pi.smul_apply, smul_eq_mul, RingHom.map_mul π, h2, Algebra.smul_def]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCore
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCore_of :
    UnitOfSpan → BasisIn → DetCore := by
  intro hU hB C R S W W' X X' _ _ _ _ _ _ _ _ _ _ _ a π mk mk' c c' j j' M M' w w' A s ha h1
    hspanC hj hj' hMw hM'w hcw hc'w hex hspanS
  obtain ⟨x, b, hb⟩ := hB C W X a mk hspanC ha
  set P0 : Matrix (Fin a) (Fin a) R := Matrix.of fun i k => c (x k) i with hP0
  let v : Fin a → Fin a → S := fun k i => π (c (x k) i)
  have hspan : Submodule.span S (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspanS, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have e1 : (fun i => π (c y i)) = j (mk y) := funext fun i => (hj y i).symm
    have e2 := congrArg j (b.sum_repr (mk y))
    show (fun i => π (c y i)) ∈ Submodule.span S (Set.range v)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, ← e2, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul, hb k, ← algebraMap_smul S (b.repr (mk y) k)]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, ?_⟩)
    funext i
    exact (hj (x k) i).symm
  have hunit : IsUnit (π P0.det) := by
    rw [RingHom.map_det]
    exact hU S a v hspan
  set mb := LinearMap.toMatrix b b M with hmb
  have hM : ∀ k, M (b k) = ∑ l, mb l k • b l := by
    intro k
    simp only [hmb, LinearMap.toMatrix_apply]
    exact (b.sum_repr _).symm
  have hmat : A.map π * (P0.map s).map π = P0.map π * mb.map (algebraMap C S) := by
    ext i k
    have e1 : (A.map π * (P0.map s).map π) i k = π (c (w (x k)) i) := by
      rw [hcw (x k)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, hP0]
    have e2 : π (c (w (x k)) i) = (P0.map π * mb.map (algebraMap C S)) i k := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hj, ← hMw, ← hb k, hM k, map_sum, Finset.sum_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, Pi.smul_apply, Algebra.smul_def, hb l, hj, mul_comm (algebraMap C S _)]
      simp [hP0]
    rw [e1, e2]
  have hdet : π A.det * π (s P0.det) = π P0.det * algebraMap C S mb.det := by
    have e := congrArg Matrix.det hmat
    simp only [Matrix.det_mul] at e
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using e
  obtain ⟨x', hx'⟩ := hex x
  obtain ⟨d, hd, -⟩ := M'.existsUnique_eq_smul_id_of_finrank_eq_one h1
  have hdM' : LinearMap.det M' = d := by
    rw [hd, LinearMap.det_smul, LinearMap.det_id, h1, pow_one, mul_one]
  have e3 : j' (M' (mk' x')) = algebraMap C S d * π P0.det := by
    rw [hd, LinearMap.smul_apply, LinearMap.id_apply, map_smul, Algebra.smul_def, hj', hx']
  have e4 : j' (M' (mk' x')) = π A.det * π (s P0.det) := by
    rw [hM'w, hj', hc'w, hx', map_mul]
  have e5 : algebraMap C S d = algebraMap C S mb.det := by
    have e6 : algebraMap C S d * π P0.det = algebraMap C S mb.det * π P0.det := by
      rw [← e3, e4, hdet, mul_comm]
    exact hunit.mul_left_injective e6
  rw [hdM', ← LinearMap.det_toMatrix b M]
  exact (algebraMap C S).injective e5.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem step_fix (hco : CoFacts) {F L B : Type} [Field F] [Field L] [Algebra F L] [CommRing B] [Algebra F B] {a : ℕ}
    (x : Fin a → (Fin a → L) ⊗[F] B) (y : (Fin 1 → L) ⊗[F] B)
    (hy : co y 0 = Matrix.det (Matrix.of fun i k => co (x k) i))
    (T : End L (Fin a → L)) (A : Matrix (Fin a) (Fin a) L) (hT : ∀ v, T v = A.mulVec v)
    (T' : End L (Fin 1 → L)) (A' : Matrix (Fin 1) (Fin 1) L) (hT' : ∀ v, T' v = A'.mulVec v)
    (hdet : A'.det = A.det) (s : B →ₐ[F] B)
    (hfix : ∀ k, AlgebraTensorModule.map T s.toLinearMap (x k) = x k) :
    AlgebraTensorModule.map T' s.toLinearMap y = y := by
  obtain ⟨-, -, -, hmap, -⟩ := hco F L B a
  obtain ⟨-, -, -, hmap', hbij⟩ := hco F L B 1
  set D : Matrix (Fin a) (Fin a) (L ⊗[F] B) := Matrix.of fun i k => co (x k) i with hD
  have hM : D = A.map (algebraMap L (L ⊗[F] B)) * D.map (onR L s) := by
    ext i k
    have h1 := congrFun (hmap T A hT s (x k)) i
    rw [hfix k] at h1
    simpa [D, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1
  have key : D.det = algebraMap L (L ⊗[F] B) A.det * onR L s D.det := by
    conv_lhs => rw [hM]
    rw [Matrix.det_mul, RingHom.map_det, RingHom.map_det]
    rfl
  apply hbij.1
  have h1 := congrFun (hmap' T' A' hT' s y) 0
  have h3 : A' 0 0 = A.det := by rw [← hdet, Matrix.det_fin_one]
  show co _ 0 = co y 0
  rw [h1, hy]
  conv_rhs => rw [key]
  simp [Matrix.mulVec, dotProduct, h3, hy]

private theorem one_ext {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) {a : ℕ} (x : Fin a → ↥(Dpst P ρ)) :
    ∃ K' : FinExt l, ∀ k, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → stRep P ρ g (x k : V ⊗[ℚ_[l]] Bst P) = x k := by
  have hs : ∀ s : Finset (Fin a), ∃ K' : FinExt l, ∀ k ∈ s, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
      stRep P ρ g (x k : V ⊗[ℚ_[l]] Bst P) = x k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨K, by simp⟩
    | insert k s hk ih =>
      obtain ⟨K₁, h₁⟩ := ih
      obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρ).mp (x k).2
      refine ⟨supExt K₁ K₂, fun k' hk' g hg => ?_⟩
      rcases Finset.mem_insert.mp hk' with rfl | hk'
      · exact h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
      · exact h₁ k' hk' g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)
  obtain ⟨K', h⟩ := hs Finset.univ
  exact ⟨K', fun k => h k (Finset.mem_univ k)⟩

theorem UpperTheory.Gal.crystallineComparison.detMem_of :
    CoFacts → DetMem := by
  intro hco l _ P K LL a ρ ρ' A A' hA hA' hdet x
  obtain ⟨K', hK'⟩ := one_ext P ρ x
  obtain ⟨y, hy⟩ := (hco ℚ_[l] ↥LL.1 (Bst P) 1).2.2.2.2.2
    (Matrix.det (Matrix.of fun i k => co (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
  exact ⟨⟨y, (mem_Dpst P ρ').mpr ⟨K', fun g hg =>
    step_fix hco (fun k => (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) y hy (ρ g) (A g) (hA g) (ρ' g) (A' g) (hA' g)
      (hdet g) (actSt P (g : GQ l)) fun k => hK' k g hg⟩⟩, hy⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}

private theorem fa (a : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1)) (hr : IsPst P ρ) :
    finrank ℂ (WDSpace P ι ρ) = a := by
  rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι K LL _ ρ hr]
  simp

set_option maxHeartbeats 1600000 in
private theorem ringS' (hRing : RingS) (LL : FinExt l) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra ℂ S) (π : ↥LL.1 ⊗[ℚ_[l]] Bst P →+* S), Nontrivial S ∧
      (∀ x : ↥LL.1, π (x ⊗ₜ[ℚ_[l]] (1 : Bst P)) = algebraMap ℂ S (ι (x : Om l))) ∧
      ∀ c : ↥(MaximalUnramifiedExtension l), π ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) =
        algebraMap ℂ S (ι (c : Om l)) := by
  haveI : Nontrivial P.R.B := nontrivial_B P
  haveI : Nontrivial (Bst P) := inferInstanceAs (Nontrivial (Polynomial P.R.B))
  have hz : ∀ z : ℚ_[l], (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (algebraMap ℚ_[l] ↥LL.1 z) =
      (urC ι) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) z) := by
    intro z
    simp only [urC, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact hRing ℚ_[l] ↥LL.1 ↥(MaximalUnramifiedExtension l) (Bst P) ℂ
    (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (urC ι) hz

set_option maxHeartbeats 1600000 in
private theorem core (hCo : CoFacts) (hCore : DetCore) (a : ℕ)
    (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1)) (ρ' : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1))
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (S : Type) [CommRing S] [Algebra ℂ S] [Nontrivial S] (π : ↥LL.1 ⊗[ℚ_[l]] Bst P →+* S)
    (hfa : finrank ℂ (WDSpace P ι ρ) = a) (hf1 : finrank ℂ (WDSpace P ι ρ') = 1)
    (j : WDSpace P ι ρ →ₗ[ℂ] (Fin a → S)) (j1 : WDSpace P ι ρ' →ₗ[ℂ] (Fin 1 → S))
    (hj : ∀ x i, j (wdMk P ι ρ x) i = π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
    (hj1 : ∀ x i, j1 (wdMk P ι ρ' x) i = π (co (x : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
    (M : End ℂ (WDSpace P ι ρ)) (M' : End ℂ (WDSpace P ι ρ'))
    (w : ↥(Dpst P ρ) → ↥(Dpst P ρ)) (w' : ↥(Dpst P ρ') → ↥(Dpst P ρ'))
    (hM : ∀ x, M (wdMk P ι ρ x) = wdMk P ι ρ (w x)) (hM' : ∀ x, M' (wdMk P ι ρ' x) = wdMk P ι ρ' (w' x))
    (T : End ↥LL.1 (Fin a → ↥LL.1)) (T' : End ↥LL.1 (Fin 1 → ↥LL.1))
    (B : Matrix (Fin a) (Fin a) ↥LL.1) (B' : Matrix (Fin 1) (Fin 1) ↥LL.1)
    (hT : ∀ v, T v = B.mulVec v) (hT' : ∀ v, T' v = B'.mulVec v) (hB : B'.det = B.det)
    (σ : Bst P →ₐ[ℚ_[l]] Bst P)
    (hw : ∀ x, (w x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) =
      AlgebraTensorModule.map T σ.toLinearMap (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P))
    (hw' : ∀ x, (w' x : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) =
      AlgebraTensorModule.map T' σ.toLinearMap (x : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P))
    (hmem : ∀ x : Fin a → ↥(Dpst P ρ), ∃ x' : ↥(Dpst P ρ'),
      co (x' : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) 0 =
        Matrix.det (Matrix.of fun i k => co (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
    (hspan : Submodule.span S (Set.range fun (x : ↥(Dpst P ρ)) i =>
      π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) = ⊤) :
    LinearMap.det M = LinearMap.det M' := by
  have hc4 := (hCo ℚ_[l] ↥LL.1 (Bst P) a).2.2.2.1
  have hc4' := (hCo ℚ_[l] ↥LL.1 (Bst P) 1).2.2.2.1
  refine hCore ℂ (↥LL.1 ⊗[ℚ_[l]] Bst P) S (WDSpace P ι ρ) (WDSpace P ι ρ') ↥(Dpst P ρ) ↥(Dpst P ρ') a π
    (wdMk P ι ρ) (wdMk P ι ρ') (fun x => co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P))
    (fun x => co (x : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) 0) j ((LinearMap.proj 0).comp j1) M M' w w'
    (B.map (algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] Bst P))) (onR ↥LL.1 σ) hfa hf1 (span_wdMk P ι ρ) hj
    (fun x => hj1 x 0) hM hM' ?_ ?_ hmem hspan
  · intro x
    rw [hw x]
    exact hc4 T B hT σ _
  · intro x
    rw [hw' x, hc4' T' B' hT' σ _]
    have e : (B.map (algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] Bst P))).det =
        algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] Bst P) (B' 0 0) := by
      have e1 := RingHom.map_det (algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] Bst P)) B
      rw [RingHom.mapMatrix_apply] at e1
      rw [← e1, ← hB, Matrix.det_fin_one]
    rw [e]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
end

set_option maxHeartbeats 1600000 in
theorem UpperTheory.Gal.crystallineComparison.detOne_of :
    CoFacts → RingS → DetCore → DetMem → WeilCo → SpanS → CoLift → DetE := by
  intro hCo hRing hCore hMem hWeil hSpan hLift l _ P AI hAI ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a LL r c
    hdet hsst hr hc g hg
  haveI := hr.finite
  haveI := hc.finite
  obtain ⟨S, _, _, π, hS, hπL, hπU⟩ := ringS' P ι hRing LL
  refine (hLift l P ι Bw.Kw LL a (Bw.repE LL r) S π hπL hπU).elim ?_
  intro j hj1
  refine (hLift l P ι Bw.Kw LL 1 (Bw.repE LL c) S π hπL hπU).elim ?_
  intro j1 hj2
  have hdv : ∀ x, ((c x : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1).det =
      ((r x : GL (Fin a) ↥LL.1) : Matrix (Fin a) (Fin a) ↥LL.1).det := fun x => by
    have e := congrArg Units.val (hdet x)
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply] at e
  exact core P ι hCo hCore a (Bw.repE LL r) (Bw.repE LL c) S π (fa P ι a _ hr) (fa P ι 1 _ hc) j j1 hj1 hj2
    (wdRho P ι Bw h hj (Bw.repE LL r) g) (wdRho P ι Bw h hj (Bw.repE LL c) g)
    (weilD Bw h P (Bw.repE LL r) g) (weilD Bw h P (Bw.repE LL c) g) (fun x => rfl) (fun x => rfl)
    (Bw.repE LL r (weilToGK Bw h g)) (Bw.repE LL c (weilToGK Bw h g))
    ((r (Bw.e.symm (weilToGK Bw h g)) : GL (Fin a) ↥LL.1) : Matrix (Fin a) (Fin a) ↥LL.1)
    ((c (Bw.e.symm (weilToGK Bw h g)) : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1)
    (fun v => GlobalTheory.ConjLocal.repE_apply Bw LL r _ v) (fun v => GlobalTheory.ConjLocal.repE_apply Bw LL c _ v) (hdv _)
    ((actSt P (weilToGK Bw h g : GQ l)).comp (phiSt P ^ resDeg l w))
    (fun x => hWeil l P E Ω A w h O Bw LL _ (Bw.repE LL r) g hg x)
    (fun x => hWeil l P E Ω A w h O Bw LL _ (Bw.repE LL c) g hg x)
    (hMem l P Bw.Kw LL a (Bw.repE LL r) (Bw.repE LL c)
      (fun y => ((r (Bw.e.symm y) : GL (Fin a) ↥LL.1) : Matrix (Fin a) (Fin a) ↥LL.1))
      (fun y => ((c (Bw.e.symm y) : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1))
      (fun y v => GlobalTheory.ConjLocal.repE_apply Bw LL r y v) (fun y v => GlobalTheory.ConjLocal.repE_apply Bw LL c y v)
      (fun y => hdv _))
    (hSpan l P AI hAI Bw.Kw LL a (Bw.repE LL r) hsst S π)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetRingS
section
noncomputable section

open TensorProduct

namespace UpperTheory.Gal.crystallineComparison

theorem detRingS_of :
    RingS := by
  intro F L U B C _ _ _ _ _ _ _ _ _ _ _ τL τU h
  letI : Algebra U C := τU.toAlgebra
  let S := TensorProduct U C B
  have hS : Nontrivial S :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right U C B τU.injective
  let ψ : B →+* S := (Algebra.TensorProduct.includeRight : B →ₐ[U] S).toRingHom
  have key : ∀ c : U, algebraMap C S (τU c) = (1 : C) ⊗ₜ[U] algebraMap U B c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have e : τU c = c • (1 : C) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [e, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  letI : Algebra F S := (ψ.comp (algebraMap F B)).toAlgebra
  let φ : L →ₐ[F] S :=
    { (algebraMap C S).comp τL with
      commutes' := by
        intro z
        change algebraMap C S (τL (algebraMap F L z)) = ψ (algebraMap F B z)
        rw [h z, key, IsScalarTower.algebraMap_apply F U B z]
        rfl }
  let ψ' : B →ₐ[F] S := { ψ with commutes' := fun _ => rfl }
  let π : L ⊗[F] B →+* S :=
    (Algebra.TensorProduct.lift φ ψ' (fun _ _ => Commute.all _ _)).toRingHom
  refine ⟨S, inferInstance, inferInstance, π, hS, ?_, ?_⟩
  · intro x
    change φ x * ψ' 1 = _
    rw [map_one, mul_one]
    rfl
  · intro c
    change φ 1 * ψ' (algebraMap U B c) = _
    rw [map_one, one_mul, key]
    rfl

end UpperTheory.Gal.crystallineComparison
end
end

