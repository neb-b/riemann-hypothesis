module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0281

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfTermwiseBiject
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.LevelCx

open GlobalTheory.ColFilt

theorem zcomp_coe {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) : (zcomp a b h).1 = a.1.comp b.1 h := rfl

theorem ofHom_coe {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (Cocycle.ofHom f).1 = Cochain.ofHom f := rfl

theorem main : ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) →
    ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
    (∀ p n, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) →
    ∀ n, Function.Bijective (cpull g I n) := by
  intro R _ I _ _ K L _ _ g hg
  have hb1 : ∀ p n' m (h : 0 + n' = m), Function.Bijective
      (cpre (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p))) I n' m h) := by
    intro p n' m h
    obtain rfl : n' = m := by omega
    exact hg p n'
  let Φ : ∀ n, (∀ _ : Unit, Cochain L I (n - 0)) →+ Cochain K I n := fun n =>
    AddMonoidHom.mk' (fun α => (Cochain.ofHom g).comp (α ()) (by omega))
      (fun α β => Cochain.comp_add _ _ _ _)
  have hΦ0 : ∀ n (α : ∀ _ : Unit, Cochain L I (n - 0)), Φ n α = (Cochain.ofHom g).comp (α ()) (by omega) := fun _ _ => rfl
  have hΦ : ∀ n (α : ∀ _ : Unit, Cochain L I (n - 0)) (t q : ℤ) (hq : t + n = q),
      (Φ n α).v t q hq = g.f t ≫ (α ()).v t q (by omega) := by
    intro n α t q hq
    rw [hΦ0, Cochain.comp_v _ _ _ t t q (add_zero t) (by omega), Cochain.ofHom_v]
  have key : ∀ n' n (h : 0 + n' = n), Function.Bijective (cpre (Cocycle.ofHom g) I n' n h) := by
    intro n' n h
    obtain rfl : n' = n - 0 := by omega
    have := bijective_of_columns (isColumns_terms L) (isColumns_terms K) (fun _ : Unit => I) I (fun _ => 0) Φ
      (fun n m hnm α => by
        rw [hΦ0, hΦ0, δ_comp (Cochain.ofHom g) (α ()) _ 1 (m - 0) m hnm (zero_add 1) (by omega),
          δ_ofHom, Cochain.zero_comp, smul_zero, add_zero])
      (fun p n α hα => by
        show ∀ (c k t : ℤ) (h : c + k = t) (q : ℤ) (hq : t + n = q), p < c → ιTerm K c k t h ≫ (Φ n α).v t q hq = 0
        intro c k t h q hq hc
        by_cases hk : k = 0
        · subst hk
          obtain rfl : c = t := by omega
          have h0 := eq_zero_of_ιTerm (hα () c 0 c h q (by omega) hc)
          rw [hΦ, h0, comp_zero, comp_zero]
        · rw [ιTerm_ne _ _ _ _ _ hk, zero_comp])
      (fun p _ => ⟨fun m x => cpre (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p))) I (m - 0) m
          (by omega) (x ()),
        fun m => (hb1 p (m - 0) m (by omega)).comp (Equiv.funUnique Unit _).bijective,
        fun n m h α _ a b ha hb => by
          refine congrArg CohomologyClass.mk (Cocycle.ext (Cochain.ext _ _ fun k q hq => ?_))
          rw [zcomp_coe, ofHom_coe, Cochain.comp_v _ _ _ k k q (add_zero k) (by omega), Cochain.ofHom_v, ha (), hb]
          by_cases hk : k = 0
          · subst hk
            rw [restr_v _ _ p _ _ _ _ 0 p q (add_zero p) _ (by omega), restr_v _ _ p _ _ _ _ 0 p q (add_zero p) _ (by omega),
              hΦ, ιTerm_zero, ιTerm_zero,
              show ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)).f 0 =
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).hom ≫ g.f p ≫
                  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.X p)).inv from
                HomologicalComplex.single_map_f_self _ _ _]
            exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))))
          · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) k hk).eq_of_src _ _⟩)
      n (fun x => cpre (Cocycle.ofHom g) I (n - 0) n h (x ()))
      (fun a b hb => congrArg CohomologyClass.mk (Cocycle.ext (by rw [zcomp_coe, hb]; rfl)))
    exact this.comp (Equiv.funUnique Unit _).symm.bijective
  intro n
  exact key n n (zero_add n)

end GlobalTheory.LevelCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.BiprodCls

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull {K L M : _root_.GlobalTheory.EtC.Cx R} (f : K ⟶ L)
    (g : L ⟶ M) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    _root_.GlobalTheory.EtC.cpull f I n (_root_.GlobalTheory.EtC.cpull g I n x) =
      _root_.GlobalTheory.EtC.cpull (f ≫ g) I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_add {K L : _root_.GlobalTheory.EtC.Cx R} (f g : K ⟶ L)
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (f + g) I n x =
      _root_.GlobalTheory.EtC.cpull f I n x + _root_.GlobalTheory.EtC.cpull g I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.add_comp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_zero {K L : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_zero]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_id {K : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    _root_.GlobalTheory.EtC.cpull (𝟙 K) I n x = x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

end GlobalTheory.EtC.BiprodCls

namespace GlobalTheory.EtC
open BiprodCls

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cpull_biprod_bijective : ∀ (R : Type) [CommRing R]
    (K L I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ),
    Function.Bijective fun x : CohomologyClass (K ⊞ L) I n =>
      (_root_.GlobalTheory.EtC.cpull (biprod.inl : K ⟶ K ⊞ L) I n x,
        _root_.GlobalTheory.EtC.cpull (biprod.inr : L ⟶ K ⊞ L) I n x) := by
  intro R _ K L I n
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y => _root_.GlobalTheory.EtC.cpull (biprod.fst : K ⊞ L ⟶ K) I n y.1 +
    _root_.GlobalTheory.EtC.cpull (biprod.snd : K ⊞ L ⟶ L) I n y.2, fun x => ?_, fun y => ?_⟩
  · simp only [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, ← _root_.GlobalTheory.EtC.BiprodCls.cpull_add,
      biprod.total, _root_.GlobalTheory.EtC.BiprodCls.cpull_id]
  · obtain ⟨a, b⟩ := y
    simp only [map_add (f := _), _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_fst, biprod.inl_snd,
      biprod.inr_fst, biprod.inr_snd, _root_.GlobalTheory.EtC.BiprodCls.cpull_id,
      _root_.GlobalTheory.EtC.BiprodCls.cpull_zero, add_zero, zero_add]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesCuspidalCharacterGLFin
section
noncomputable section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.FreeCusp

theorem charpoly_one {F : Type} [Field F] (M : Matrix (Fin 1) (Fin 1) F) : M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

theorem rootSum_X_sub_C {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (a : F) :
    rootSum θ k (X - C a) = θ (algebraMap F (AlgebraicClosure F) a) ^ k := by
  unfold rootSum
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.roots_X_sub_C]
  simp

theorem cusp_one {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (x : GL (Fin 1) F) :
    cusp θ 1 k x = θ (algebraMap F (AlgebraicClosure F) ((x : Matrix (Fin 1) (Fin 1) F) 0 0)) ^ k := by
  have hs := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  unfold cusp psiG
  rw [psi_eq]
  have hz : ∑ᶠ W : {W : Submodule F (Fin 1 → F) // W ≠ ⊤ ∧ ∀ v ∈ W,
      Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F) v ∈ W},
      psi (rootSum θ k) W.1 ((Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F)).restrict W.2.2) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    have h1 := Submodule.finrank_lt W.2.1
    rw [Module.finrank_fin_fun] at h1
    haveI : Subsingleton W.1 := (Module.finrank_zero_iff (R := F)).mp (by omega)
    exact PsiPrimitive.psi_trivial _ hs _ _
  rw [hz, sub_zero, Matrix.charpoly_toLin', charpoly_one, rootSum_X_sub_C]
  simp

theorem hfree_one {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (k : ℕ)
    (hk : ¬ k ≡ 0 [MOD Nat.card F - 1]) : HFree (cusp θ 1 k) := by
  intro _
  have hset : {x : GL (Fin 1) F | ∀ i j : Fin 1, (j : ℕ) + 1 < 1 →
      (x : Matrix (Fin 1) (Fin 1) F) i j = (1 : Matrix (Fin 1) (Fin 1) F) i j} = Set.univ :=
    Set.eq_univ_of_forall fun x i j h => absurd h (by omega)
  rw [hset, finsum_mem_univ]
  letI := Fintype.ofFinite (GL (Fin 1) F)
  rw [finsum_eq_sum_of_fintype]
  let f : GL (Fin 1) F →* ℂ := (powMonoidHom k).comp (θ.comp
    ((algebraMap F (AlgebraicClosure F) : F →* AlgebraicClosure F).comp
      ((Units.coeHom F).comp Matrix.GeneralLinearGroup.det)))
  have hf : ∀ x, f x = cusp θ 1 k x := by
    intro x
    rw [cusp_one]
    simp [f, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rw [← Finset.sum_congr rfl fun x _ => hf x]
  refine sum_hom_units_eq_zero f ?_
  intro h1
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  let x : GL (Fin 1) F := Matrix.GeneralLinearGroup.mk'' (Matrix.of fun _ _ => (u : F))
    (by rw [Matrix.det_fin_one]; exact u.isUnit)
  have hx : f x = 1 := by rw [h1]; rfl
  have hx' : f x = θ (algebraMap F (AlgebraicClosure F) ((u : F) ^ k)) := by
    simp [f, x, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, map_pow]
  rw [hx', ← map_one θ] at hx
  have hne : algebraMap F (AlgebraicClosure F) ((u : F) ^ k) ≠ 0 := by
    rw [_root_.map_ne_zero]; exact pow_ne_zero _ u.ne_zero
  have h2 := hθ _ _ hne one_ne_zero hx
  rw [← map_one (algebraMap F (AlgebraicClosure F))] at h2
  have h3 : (u : F) ^ k = 1 := (algebraMap F (AlgebraicClosure F)).injective h2
  have h4 : u ^ k = 1 := Units.ext (by simpa using h3)
  have h5 := orderOf_dvd_iff_pow_eq_one.mpr h4
  rw [hu, Nat.card_units] at h5
  exact hk (Nat.modEq_zero_iff_dvd.mpr h5)

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin.FreeCusp

variable {F : Type} [Field F]

def hyp {m : ℕ} (l : Fin m) : Submodule F (Fin m → F) := LinearMap.ker (LinearMap.proj l)

theorem mem_hyp {m : ℕ} (l : Fin m) (v : Fin m → F) : v ∈ hyp l ↔ v l = 0 := by
  simp [hyp]

def dg {m : ℕ} (l : Fin m) (d : F) : Matrix (Fin m) (Fin m) F := Matrix.diagonal fun i => if i = l then d else 1

theorem dg_off {m : ℕ} (l : Fin m) (d : F) (i j : Fin m) (hj : j ≠ l) :
    dg l d i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
  by_cases h : i = j
  · subst h; simp [dg, hj]
  · simp [dg, Matrix.one_apply, h]

theorem mem_nilRad_of {m : ℕ} (l : Fin m) (M : Matrix (Fin m) (Fin m) F)
    (h1 : ∀ i j, j ≠ l → M i j = 0) (h2 : M l l = 0) : Matrix.toLin' M ∈ nilRad (hyp l) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [mem_hyp, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = l
    · subst hj; rw [h2, zero_mul]
    · rw [h1 l j hj, zero_mul]
  · rw [mem_hyp] at hv
    funext i
    rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = l
    · subst hj; rw [hv, mul_zero]
    · rw [h1 i j hj, zero_mul]

theorem of_mem_nilRad {m : ℕ} (l : Fin m) (h : Module.End F (Fin m → F)) (hh : h ∈ nilRad (hyp l)) :
    (∀ i j, j ≠ l → LinearMap.toMatrix' h i j = 0) ∧ LinearMap.toMatrix' h l l = 0 := by
  refine ⟨fun i j hj => ?_, ?_⟩
  · rw [LinearMap.toMatrix'_apply, hh.2 _ ((mem_hyp l _).2 (Pi.single_eq_of_ne (Ne.symm hj) _))]
    rfl
  · rw [LinearMap.toMatrix'_apply]
    exact (mem_hyp l _).1 (hh.1 _)

theorem det_of_cols {m : ℕ} (l : Fin m) (hl : (l : ℕ) + 1 = m) (M : Matrix (Fin m) (Fin m) F)
    (h : ∀ i j, j ≠ l → M i j = (1 : Matrix (Fin m) (Fin m) F) i j) : M.det = M l l := by
  have hlt : ∀ j : Fin m, j ≠ l → j < l := fun j hj => by
    rw [Fin.lt_iff_val_lt_val]; have := j.2; have : (j : ℕ) ≠ l := fun e => hj (Fin.ext e); omega
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_single l (fun i _ hi => ?_) (fun h' => absurd (Finset.mem_univ l) h')
    rw [h i i hi, Matrix.one_apply_eq]
  · intro i j hij
    have hj : j ≠ l := fun e => by subst e; exact absurd (hlt i (ne_of_gt hij)) (not_lt.2 (le_of_lt hij))
    rw [h i j hj]; exact Matrix.one_apply_ne (ne_of_gt hij)

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin.FreeCusp

theorem hfree_two_le {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (k m : ℕ) (hm : 2 ≤ m) :
    HFree (cusp θ m k) := by
  intro _
  letI := Fintype.ofFinite F
  let l : Fin m := ⟨m - 1, by omega⟩
  have hl1 : (l : ℕ) + 1 = m := by simp only [l]; omega
  have hjl : ∀ j : Fin m, (j : ℕ) + 1 < m ↔ j ≠ l := fun j => by
    constructor
    · intro h e; rw [e] at h; omega
    · intro h; have := j.2; have : (j : ℕ) ≠ m - 1 := fun e => h (Fin.ext e); omega
  have hs : IsAdditive (rootSum θ k) := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  haveI : Finite (Module.End F (Fin m → F)) := Finite.of_injective _ DFunLike.coe_injective
  have hN : (nilRad (hyp l) : Set (Module.End F (Fin m → F))).Finite := Set.toFinite _
  have hSf : {x : GL (Fin m) F | ∀ i j : Fin m, (j : ℕ) + 1 < m →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j}.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf]
  unfold cusp
  rw [← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  unfold psiG
  have hNcols : ∀ (d : F) (h : Module.End F (Fin m → F)), h ∈ nilRad (hyp l) → ∀ i j, j ≠ l →
      LinearMap.toMatrix' (Matrix.toLin' (dg l d) + h) i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
    intro d h hh i j hj
    rw [map_add (f := _), LinearMap.toMatrix'_toLin', Matrix.add_apply, (of_mem_nilRad l h hh).1 i j hj, add_zero,
      dg_off l d i j hj]
  have hNll : ∀ (d : F) (h : Module.End F (Fin m → F)), h ∈ nilRad (hyp l) →
      LinearMap.toMatrix' (Matrix.toLin' (dg l d) + h) l l = d := by
    intro d h hh
    rw [map_add (f := _), LinearMap.toMatrix'_toLin', Matrix.add_apply, (of_mem_nilRad l h hh).2, add_zero]
    simp [dg]
  have hxcols : ∀ x ∈ hSf.toFinset, ∀ i j, j ≠ l →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
    intro x hx i j hj
    exact (hSf.mem_toFinset.1 hx) i j ((hjl j).2 hj)
  have key : ∑ x ∈ hSf.toFinset, psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))
      = ∑ p ∈ (Finset.univ.filter (fun d : F => d ≠ 0)) ×ˢ hN.toFinset,
        psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (dg l p.1) + p.2) := by
    refine Finset.sum_bij'
      (fun x _ => ((x : Matrix (Fin m) (Fin m) F) l l,
        Matrix.toLin' ((x : Matrix (Fin m) (Fin m) F) - dg l ((x : Matrix (Fin m) (Fin m) F) l l))))
      (fun p hp => Matrix.GeneralLinearGroup.mk'' (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2))
        (by
          have hp' := Finset.mem_product.1 hp
          have h1 := (Finset.mem_filter.1 hp'.1).2
          have h2 := hN.mem_toFinset.1 hp'.2
          rw [det_of_cols l hl1 _ (hNcols _ _ h2), hNll _ _ h2]
          exact h1.isUnit)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hd : (x : Matrix (Fin m) (Fin m) F) l l ≠ 0 := by
        have := (Matrix.GeneralLinearGroup.det x).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply, det_of_cols l hl1 _ (hxcols x hx)] at this
      refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, hN.mem_toFinset.2 ?_⟩
      refine mem_nilRad_of l _ (fun i j hj => ?_) ?_
      · rw [Matrix.sub_apply, hxcols x hx i j hj, dg_off l _ i j hj, sub_self]
      · rw [Matrix.sub_apply]; simp [dg]
    · intro p hp
      have hp' := Finset.mem_product.1 hp
      have h2 := hN.mem_toFinset.1 hp'.2
      refine hSf.mem_toFinset.2 fun i j hj => ?_
      exact hNcols _ _ h2 i j ((hjl j).1 hj)
    · intro x hx
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      change LinearMap.toMatrix' _ i j = _
      rw [← map_add (f := _), add_sub_cancel, LinearMap.toMatrix'_toLin']
    · intro p hp
      have hp' := Finset.mem_product.1 hp
      have h2 := hN.mem_toFinset.1 hp'.2
      change (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2) l l,
        Matrix.toLin' (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2)
          - dg l (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2) l l))) = p
      rw [hNll _ _ h2, map_sub, Matrix.toLin'_toMatrix', add_sub_cancel_left]
    · intro x hx
      congr 1
      rw [map_sub, add_sub_cancel]
  rw [key, Finset.sum_product]
  have hA0 : hyp (F := F) l ≠ ⊥ := by
    intro e
    have h0 : Pi.single (⟨0, by omega⟩ : Fin m) (1 : F) ∈ hyp l :=
      (mem_hyp l _).2 (Pi.single_eq_of_ne (fun e' => by have := congrArg Fin.val e'; simp [l] at this; omega) _)
    rw [e, Submodule.mem_bot] at h0
    have := congr_fun h0 ⟨0, by omega⟩
    simp at this
  have hA1 : hyp (F := F) l ≠ ⊤ := by
    intro e
    have h0 : Pi.single l (1 : F) ∈ hyp l := e ▸ Submodule.mem_top
    rw [mem_hyp] at h0
    simp at h0
  refine Finset.sum_eq_zero fun d _ => ?_
  dsimp only
  rw [← finsum_mem_eq_finite_toFinset_sum]
  refine isPrimitive_psi F _ _ hs (hyp l) hA0 hA1 _ fun v hv => ?_
  rw [mem_hyp] at hv ⊢
  rw [Matrix.toLin'_apply, dg, Matrix.mulVec_diagonal, hv, mul_zero]

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin

theorem hFree_cusp : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k : ℕ, (2 ≤ m ∨ ¬ k ≡ 0 [MOD Nat.card F - 1]) → HFree (cusp θ m k) := by
  intro F _ _ θ hθ m k h
  rcases h with hm | hk
  · exact FreeCusp.hfree_two_le θ k m hm
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · intro h0; exact absurd h0 (lt_irrefl 0)
      · exact FreeCusp.hfree_one θ hθ k hk
    · exact FreeCusp.hfree_two_le θ k m hm

end GlobalTheory.Shin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem haar_UJ_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro n ε μ _
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by
    rw [Measure.map_smul, hR.map_mul_right_eq_self]
    exact (measurable_mul_const g).aemeasurable⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryLieAlgebraMemIffEntries
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem pcLieEntry : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z ↔ ∀ a b, (starRingEnd ℂ) (Z a b) = -((if ε a then (1 : ℂ) else -1) * (if ε b then (1 : ℂ) else -1) * Z b a) := by
  intro n ε Z
  have key : ∀ a b, (Zᴴ * Jm ε + Jm ε * Z) a b = (starRingEnd ℂ) (Z b a) * (if ε b then (1 : ℂ) else -1) + (if ε a then (1 : ℂ) else -1) * Z a b := by
    intro a b
    simp [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  unfold inG
  constructor
  · intro h a b
    have hb := congrFun (congrFun h b) a
    rw [key] at hb
    simp only [Matrix.zero_apply] at hb
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb
  · intro h
    ext a b
    rw [key]
    simp only [Matrix.zero_apply]
    have hb := h b a
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAllPreservesDegreeAndRegularity
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_all_preserves_degree_and_regularity : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) → deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  first | (exact @GlobalTheory.liftAll_deg_reg) | (exact GlobalTheory.liftAll_deg_reg) | (intros; apply GlobalTheory.liftAll_deg_reg <;> assumption)
end

