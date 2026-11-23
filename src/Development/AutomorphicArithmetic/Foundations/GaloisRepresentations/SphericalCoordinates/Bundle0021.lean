module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem add_expand {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A) (w : V) :
    f w = ∑ i, ((b.repr w i : ℚ) : ℝ) • f (b i) := by
  conv_lhs => rw [← b.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := map_ratCast_smul f ℚ ℝ (b.repr w i) (b i)
  simpa using h

private theorem span_basis {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A)
    (hs : Submodule.span ℝ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun i => f (b i))) := by
  rw [← hs]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  rw [add_expand b f w]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem equiv_of_spans {V A B : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A] [AddCommGroup B] [Module ℝ B]
    [FiniteDimensional ℝ B] (th : V →+ A) (Q : V →+ B)
    (hA : Submodule.span ℝ (Set.range th) = ⊤) (hB : Submodule.span ℝ (Set.range Q) = ⊤)
    (dA : Module.finrank ℝ A = Module.finrank ℚ V) (dB : Module.finrank ℝ B = Module.finrank ℚ V) :
    ∃ R : A ≃ₗ[ℝ] B, ∀ w, Q w = R (th w) := by
  let b := Module.finBasis ℚ V
  let bA : Module.Basis (Fin (Module.finrank ℚ V)) ℝ A :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => th (b i)) (span_basis b th hA) (by simp [dA])
  let bB : Module.Basis (Fin (Module.finrank ℚ V)) ℝ B :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => Q (b i)) (span_basis b Q hB) (by simp [dB])
  refine ⟨bA.equiv bB (Equiv.refl _), fun w => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_expand b th w, add_expand b Q w, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 1
  have h1 : bA i = th (b i) := by simp [bA]
  have h2 : bB i = Q (b i) := by simp [bB]
  rw [← h1, ← h2, Module.Basis.equiv_apply]
  rfl

theorem UpperTheory.Gal.W2.perExt_of :
    UpperTheory.Gal.W2.PerExt := by
  intro p _ D G L A β ρ Q hQ
  haveI : Module.Finite ℤ D.La := D.finLa
  haveI : Module.Finite ℚ (VQ D) := Module.Finite.base_change ℤ ℚ D.La
  refine equiv_of_spans A.th Q A.span hQ.2.1 A.dim ?_
  rw [← A.dim, A.dimg]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowSm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powSm_of :
    UpperTheory.Gal.W2.PowSm := by
  intro X s d g hs hqc hsep A _ _ hA hg k
  have hP : IsProper (KS.pow A k).hom := KS.Leray.isProper_pow_hom A hA.proper k
  have hsm := FibPow.smoothOfRelativeDimension_fibrePower ℂ X s d g hs A hA hg k
  refine ⟨hsm, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · haveI : Smooth ((KS.pow A k).hom ≫ s) := hsm.smooth
    infer_instance
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPwOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i' => ?_) i hf
    · intro hf0
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hf0 _ (Fin.succ_ne_zero j)
    · intro hfs
      rw [hfs 0 (Fin.succ_ne_zero i').symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i' (fun j hj => hfs _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  unfold GlobalTheory.KS.matEnd GlobalTheory.KS.pr
  rw [Pi.lift_comp_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp
  · intro j hj
    simp [Matrix.diagonal_apply_ne' d hj, GlobalTheory.KS.Model.act_zero, Hom.one_def]

theorem UpperTheory.Gal.W2.pwOver_of :
    UpperTheory.Gal.W2.PwOver := by
  intro p _ D G L gb N N' h X X' c k
  have hpw : c.pw k ≫ (KS.pow X.univ.A k).hom = (KS.pow X'.univ.A k).hom ≫ c.q := by
    delta Leg.pw
    exact KS.Model.powMap_over _ _ _ k
  have hpr : ∀ i : Fin k,
      c.pw k ≫ Over.Hom.left (KS.pr X.univ.A i) = Over.Hom.left (KS.pr X'.univ.A i) ≫ c.tot := by
    intro i
    delta Leg.pw
    exact KS.Model.powMap_pr _ _ _ k i
  refine ⟨hpw, hpr, ?_, fun α => ⟨?_, fun i => ?_⟩⟩
  · intro b
    delta Leg.tot
    have h1 := congrArg Over.Hom.left (c.tr.2.1 b)
    simp only [Over.comp_left] at h1
    rw [← Category.assoc, h1, Category.assoc, c.φ.act b, Category.assoc]
  · delta Leg.tw
    rw [Category.assoc, Over.w, hpw]
  · have hm := congrArg Over.Hom.left
      (matEnd_diagonal_pr X.univ.act (fun s => (algebraMap (𝓞 D.F) D.O (α s) : D.toG.O)) i)
    rw [Over.comp_left, Over.comp_left] at hm
    delta Leg.tw
    refine (Category.assoc _ _ _).trans ((congrArg (c.pw k ≫ ·) hm).trans ?_)
    rw [← Category.assoc, hpr, Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTateWit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

theorem tateWit_of : TateWit := by
  intro p _ D gb N S s o hX hL ρ D' t P x e hN hNp hU I hI
  classical
  obtain ⟨-, hper, hexp, hker, hact, hweil, heta⟩ := hU
  have hadd : ∀ z w, e (z + w) = e z * e w := hexp.1
  have hsurj : Function.Surjective e := hexp.2.1
  have hlin : ∀ (c : D.O) u, P (c • u) = ρ c *ᵥ P u := hper.1
  have hinj : Function.Injective P := hper.2.1
  haveI : Module.Free ℤ D.toG.La := D.freeLa
  have hlift : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ φ : D.La →+ D'.La, ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (φ a)) :=
    fun n hn hnp => unifCls_lift e P hadd hsurj hker (I.ev n) (I.add n) hn
      (fun y => (I.onto n hn _).2 ⟨y, rfl⟩)
  have hroot : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ v : ℤ, IsCoprime v n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (v : ℂ) / n) :=
    fun n hn hnp => unifCls_root hn _ (I.ζ_prim n hn)
  let f : ℕ → D.La →+ D'.La := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hlift n hn.1 hn.2) else 0
  let nu : ℕ → ℤ := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hroot n hn.1 hn.2) else 0
  have hf : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a)) := by
    intro n hn hnp a
    simp only [f, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hlift n hn hnp) a
  have hnu : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p), IsCoprime (nu n) n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) := by
    intro n hn hnp
    simp only [nu, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hroot n hn hnp)
  have heq : ∀ {n : ℕ}, 0 < n → ∀ v v' : D'.La,
      e ((n : ℂ)⁻¹ • P v) = e ((n : ℂ)⁻¹ • P v') ↔ ∃ w, v = v' + n • w :=
    fun hn v v' => unifCls_eq_iff e P hadd hker hinj hn v v'
  refine ⟨f, nu, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n m hn hm hnm
    have hnp : n.Coprime p := (Nat.coprime_mul_iff_left.1 hnm).1
    refine ⟨?_, fun a => ?_⟩
    · have hz := I.ζ_pow n m hn hm
      have hz' := congrArg (fun u : ℂˣ => (u : ℂ)) hz
      simp only [Units.val_pow_eq_pow_val] at hz'
      rw [(hnu _ (Nat.mul_pos hn hm) hnm).2, (hnu n hn hnp).2, ← Complex.exp_nat_mul] at hz'
      have : (m : ℂ) * (-(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / ((n * m : ℕ) : ℂ)) =
          -(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / n := by
        have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        push_cast; field_simp
      rw [this] at hz'
      exact (unifCls_exp_eq_iff hn _ _).1 hz'
    · have ht := I.tower n m hn hm a
      have e1 := hf _ (Nat.mul_pos hn hm) hnm a
      have e2 := hf n hn hnp a
      rw [e1, e2] at ht
      erw [unifCls_tower e P hadd hn hm] at ht
      exact (heq hn _ _).1 ht
  · intro n hn hnp
    refine ⟨(hnu n hn hnp).1, fun c a => ?_, fun a => ?_, fun a' => ?_, fun a a' => ?_⟩
    · have hl := I.lin n c a
      erw [hf n hn hnp (c • a), hf n hn hnp a] at hl
      have h3 := hact c ((n : ℂ)⁻¹ • P (f n a))
      rw [Matrix.mulVec_smul] at h3
      have h4 := hlin c (f n a)
      have h5 : e ((n : ℂ)⁻¹ • P (c • f n a)) = e ((n : ℂ)⁻¹ • P (f n a)) ≫ o.act.act c := by
        rw [h4]; exact h3
      exact (heq hn _ _).1 (hl.trans h5.symm)
    · have h1 := I.ker n hn a
      erw [hf n hn hnp a, unifCls_unit_iff e P hker hinj hn] at h1
      exact h1
    · obtain ⟨y, hy⟩ := (I.onto n hn (e ((n : ℂ)⁻¹ • P a'))).1 (unifCls_pow e P hadd hker hn a')
      rw [hf n hn hnp y] at hy
      obtain ⟨w, hw⟩ := (heq hn _ _).1 hy.symm
      exact ⟨y, w, hw⟩
    · have hiso := I.isom n hn a a'
      rw [hf n hn hnp a, hf n hn hnp a'] at hiso
      have hw := hweil n (f n a) (f n a')
        (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF (f n a) (f n a') : ℂ) / n)) (Complex.exp_ne_zero _))
        hn rfl
      have hu := _root_.GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex S o.A D.g o.ab hX _ hL x n _ _ _ _ hiso hw
      have hu' := congrArg (fun u : ℂˣ => (u : ℂ)) hu
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hu'
      rw [(hnu n hn hnp).2, ← Complex.exp_int_mul] at hu'
      have : ((2 * D.toG.EF a a' : ℤ) : ℂ) * (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) =
          -(2 * Real.pi * Complex.I) * ((nu n * (2 * D.toG.EF a a') : ℤ) : ℂ) / n := by
        push_cast; ring
      rw [this] at hu'
      exact (unifCls_exp_eq_iff hn _ _).1 hu'.symm
  · intro a
    have h3 : I.ev N a = e ((N : ℂ)⁻¹ • P (t a)) := (hI a).symm.trans (heta a)
    rw [hf N hN hNp a] at h3
    obtain ⟨w, hw⟩ := (heq hN _ _).1 h3
    exact ⟨w, hw⟩
  · intro n hn hnp a
    exact hf n hn hnp a

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.SNOf
section
open scoped Matrix

namespace UpperTheory.Gal.W2

theorem sN_of : SN := by
  intro F K _ _ n τ ψ hψ
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by simp, fun M => Subsingleton.elim _ _⟩
  have i0 : Fin n := ⟨0, hn⟩
  haveI : Nonempty (Fin n) := ⟨i0⟩
  have hsc : ∀ {R : Type} [Field R] (i k : Fin n) (x : R),
      Matrix.single i k x = Matrix.scalar (Fin n) x * Matrix.single i k 1 := by
    intro R _ i k x
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hsum1 : ∀ {R : Type} [Field R], (∑ k : Fin n, Matrix.single k k (1 : R)) = 1 := by
    intro R _
    ext r s
    rw [Matrix.sum_apply, Finset.sum_eq_single r]
    · by_cases h : r = s
      · subst h
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, Matrix.one_apply, h]
    · intro k _ hk
      simp [Matrix.single_apply, hk]
    · simp
  have hEE : ∀ i j j' k, ψ (Matrix.single i j 1) * ψ (Matrix.single j' k 1) =
      if j = j' then ψ (Matrix.single i k 1) else 0 := by
    intro i j j' k
    rw [← map_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, map_zero]
  have hP : ψ (Matrix.single i0 i0 1) ≠ 0 := by
    intro h0
    have hk : ∀ k, ψ (Matrix.single k k 1) = 0 := by
      intro k
      have e1 : ψ (Matrix.single k k 1) = ψ (Matrix.single k i0 1) * ψ (Matrix.single i0 i0 1) *
          ψ (Matrix.single i0 k 1) := by
        rw [hEE k i0 i0 i0, if_pos rfl, hEE k i0 i0 k, if_pos rfl]
      rw [e1, h0, mul_zero, zero_mul]
    have h1 : ψ 1 = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsum1 (R := F), map_sum]
      exact Finset.sum_eq_zero fun k _ => hk k
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨a, b, hab⟩ : ∃ a b, ψ (Matrix.single i0 i0 1) a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (Matrix.ext h)
  have hL : ∀ i k, ψ (Matrix.single i k 1) * (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) =
      ψ (Matrix.single i i0 1) * Matrix.single b k 1 := by
    intro i k
    rw [Finset.mul_sum]
    have l1 : ∀ j, ψ (Matrix.single i k 1) * (ψ (Matrix.single j i0 1) * Matrix.single b j 1) =
        if k = j then ψ (Matrix.single i i0 1) * Matrix.single b k 1 else 0 := by
      intro j
      rw [← mul_assoc, hEE]
      split_ifs with h
      · subst h
        rfl
      · rw [zero_mul]
    simp only [l1, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hR : ∀ i k, (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) * Matrix.single i k 1 =
      ψ (Matrix.single i i0 1) * Matrix.single b k 1 := by
    intro i k
    rw [Finset.sum_mul]
    have l2 : ∀ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1 * Matrix.single i k 1 =
        if j = i then ψ (Matrix.single i i0 1) * Matrix.single b k 1 else 0 := by
      intro j
      rw [mul_assoc]
      split_ifs with h
      · subst h
        rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, mul_zero]
    simp only [l2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1, ?_, ?_⟩
  · have hTS : (∑ k, Matrix.single k a (ψ (Matrix.single i0 i0 1) a b)⁻¹ * ψ (Matrix.single i0 k 1)) *
        (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) = 1 := by
      rw [Finset.sum_mul, ← hsum1 (R := K)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, hL, ← mul_assoc, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    have hd := congrArg Matrix.det hTS
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact right_ne_zero_of_mul_eq_one hd
  · intro M
    have hM : M = ∑ i, ∑ k, Matrix.scalar (Fin n) (M i k) * Matrix.single i k 1 := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single M]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsc i k (M i k)
    have hMt : M.map τ = ∑ i, ∑ k, Matrix.scalar (Fin n) (τ (M i k)) * Matrix.single i k 1 := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single (M.map τ)]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsc i k _
    rw [hMt]
    conv_lhs => rw [hM]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hψ, mul_assoc, hL, ← hR, ← mul_assoc, ← mul_assoc,
      (Matrix.scalar_commute (τ (M i k)) (fun r' => Commute.all _ r') _).eq]

end UpperTheory.Gal.W2
end

