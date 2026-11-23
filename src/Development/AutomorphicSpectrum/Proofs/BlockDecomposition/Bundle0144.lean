module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningFiltrationIsFil
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

theorem isFil_thFil : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := by
  intro b L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.pdPow_zero
  · intro T
    change T.pdPow (1 : ℤ).toNat = T.J
    exact le_antisymm (dividedPowerFiltration_one_le T.δ) T.J_le_pdPow_one
  · intro r r' h T
    exact T.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.B from x) ∈ pdP T.δ r := by
      have : (show T.B from x) ∈ T.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.B from y) ∈ pdP T.δ r' := by
      have : (show T.B from y) ∈ T.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := dividedPowerFiltration_mul_le T.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.δ k hx

end GlobalTheory.CompanionTheory.DPFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitUniversalEqPullbackBoxEvaluation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem con_evF_eq_evL [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (T : C)
    (u : ∀ a : Fin (0 + 1) ⥤ C, F.obj (a.obj (Fin.last 0)) ⊗[R] F.obj T) :
    con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T) (evF F T₀ ε) u =
      evL F T₀ T ε (u ((Functor.const (Fin (0 + 1))).obj T₀)) := by
  refine pure_induction (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T)
    (P := fun u ↦ con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T) (evF F T₀ ε) u =
      evL F T₀ T ε (u ((Functor.const (Fin (0 + 1))).obj T₀))) ?_ ?_ ?_ u
  · rw [map_zero]
    exact (map_zero (evL F T₀ T ε)).symm
  · intro f m
    rw [con_pure]
    show evF F T₀ ε f • m = evL F T₀ T ε (f ((Functor.const (Fin (0 + 1))).obj T₀) ⊗ₜ m)
    simp only [evL, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply,
      Algebra.smul_def]
    rfl
  · intro u v hu hv
    rw [map_add (f := _), hu, hv]
    exact (map_add (evL F T₀ T ε) _ _).symm

theorem tmap_mp_id {T T' : C} (t : F.obj T ⊗[R] F.obj T') :
    Algebra.TensorProduct.map (mp F (𝟙 T)) (mp F (𝟙 T')) t = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul x y => simp only [Algebra.TensorProduct.map_tmul, mp_id]
  | add x y hx hy => rw [map_add (f := _), hx, hy]

theorem UU_evF [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (w : Cn (box F) n) :
    UU F (evF F T₀ ε) n w = pulln (boxE F T₀ ε) n w := by
  funext b
  have h1 : UU F (evF F T₀ ε) n w b = con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0)))
      (F.obj (b.obj (Fin.last n))) (evF F T₀ ε) (fun a ↦ S0 F n w a b) := rfl
  have hb : b.map (homOfLE (Fin.le_last (Fin.last n))) = 𝟙 _ := by
    rw [show homOfLE (Fin.le_last (Fin.last n)) = 𝟙 _ from Subsingleton.elim _ _, b.map_id]
  have h2 : S0 F n w ((Functor.const (Fin (0 + 1))).obj T₀) b = w (b ⋙ CategoryTheory.Prod.sectR T₀ C) := by
    show Algebra.TensorProduct.map (mp F (𝟙 T₀)) (mp F (b.map (homOfLE (Fin.le_last (Fin.last n)))))
      (w (b ⋙ CategoryTheory.Prod.sectR T₀ C)) = _
    rw [hb]
    exact tmap_mp_id F _
  rw [h1, con_evF_eq_evL, pulln_apply, h2]
  rfl

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfSymmetricTensorZero
section
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace GlobalTheory.CompanionTheory.WedgeOf

section SymmWedge

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem wedgeT_tmul_self (a : V) : wedgeT (R := R) V (a ⊗ₜ[R] a) = 0 := by
  rw [wedgeT_tmul]
  exact (exteriorPower.ιMulti R (M := V) 2).map_eq_zero_of_eq ![a, a]
    (i := 0) (j := 1) rfl (by decide)

theorem wedgeT_tmul_add_swap (a b : V) :
    wedgeT (R := R) V (a ⊗ₜ[R] b) + wedgeT (R := R) V (b ⊗ₜ[R] a) = 0 := by
  have h := wedgeT_tmul_self (R := R) (a + b)
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add (f := _), map_add (f := _),
    map_add, wedgeT_tmul_self, wedgeT_tmul_self, zero_add, add_zero] at h
  exact h

theorem sum_sum_eq_zero_of_antisymm {ι M : Type} [DecidableEq ι] [AddCommGroup M]
    (f : ι → ι → M) (hd : ∀ i, f i i = 0) (ha : ∀ i j, f i j + f j i = 0) (s : Finset ι) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    simp only [Finset.sum_insert has, Finset.sum_add_distrib, ih, hd, zero_add, add_zero]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ ha a i

theorem wedgeT_eq_zero_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)
    (t : V ⊗[R] V) (ht : TensorProduct.comm R V V t = t) : wedgeT (R := R) V t = 0 := by
  set B := b.tensorProduct b with hB
  have hsym : ∀ i j, B.repr t (i, j) = B.repr t (j, i) := by
    have key : ∀ (i j : ι) (s : V ⊗[R] V),
        B.repr (TensorProduct.comm R V V s) (i, j) = B.repr s (j, i) := by
      intro i j s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [hB, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]
      | add x y hx hy => simp [map_add (f := _), hx, hy]
    intro i j
    rw [← key i j t, ht]
  have hexp : t = ∑ i, ∑ j, B.repr t (i, j) • (b i ⊗ₜ[R] b j) := by
    conv_lhs => rw [← B.sum_repr t]
    rw [Fintype.sum_prod_type]
    simp [hB, Module.Basis.tensorProduct_apply]
  rw [hexp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  refine sum_sum_eq_zero_of_antisymm
    (fun i j ↦ B.repr t (i, j) • wedgeT (R := R) V (b i ⊗ₜ[R] b j)) ?_ ?_ Finset.univ
  · intro i
    simp [wedgeT_tmul_self]
  · intro i j
    show B.repr t (i, j) • _ + B.repr t (j, i) • _ = 0
    rw [hsym j i, ← smul_add, wedgeT_tmul_add_swap, smul_zero]

theorem map_wedgeT {W : Type} [AddCommGroup W] [Module R W] (r : W →ₗ[R] V) (s : W ⊗[R] W) :
    exteriorPower.map 2 r (wedgeT (R := R) W s) = wedgeT (R := R) V (TensorProduct.map r r s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [TensorProduct.map_tmul, wedgeT_tmul, wedgeT_tmul, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem wedgeT_eq_zero_of_symm (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Projective R V] (t : V ⊗[R] V)
    (ht : t - TensorProduct.comm R V V t = 0) : wedgeT (R := R) V t = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' R V
  obtain ⟨i, hi⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hri : ∀ v, r (i v) = v := fun v ↦ LinearMap.congr_fun hi v
  have hcomm : TensorProduct.comm R V V t = t := (sub_eq_zero.1 ht).symm
  have hmap : ∀ s : V ⊗[R] V, TensorProduct.comm R (Fin n → R) (Fin n → R) (TensorProduct.map i i s)
      = TensorProduct.map i i (TensorProduct.comm R V V s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hback : ∀ s : V ⊗[R] V, TensorProduct.map r r (TensorProduct.map i i s) = s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hri]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hW : wedgeT (R := R) (Fin n → R) (TensorProduct.map i i t) = 0 :=
    wedgeT_eq_zero_of_basis (Pi.basisFun R (Fin n)) _ (by rw [hmap, hcomm])
  have := map_wedgeT r (TensorProduct.map i i t)
  rw [hW, map_zero, hback] at this
  exact this.symm

end SymmWedge

end GlobalTheory.CompanionTheory.WedgeOf
end
end

