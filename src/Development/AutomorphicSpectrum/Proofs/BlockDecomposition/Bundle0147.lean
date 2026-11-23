module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0125
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0144
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def mulSq (a b : IdF A) (T : C) (y : A.obj T) : sqM a b T →ₗ[R] sqM a b T where
  toFun x := ⟨Ideal.Quotient.mk _ y * x.1, Ideal.mul_mem_left ((a.S T).map (Ideal.Quotient.mk (b.S T))) _ x.2⟩
  map_add' x x' := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)

def mulMor (a b c : IdF A) (y : ∀ T : C, A.obj T)
    (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (A.map φ).hom (y T) ∈ c.S T')
    (hc : ∀ (T : C) {v w : A.obj T}, v ∈ c.S T → w ∈ a.S T → v * w ∈ b.S T) :
    CH.Mor (sq a b) (sq a b) (RingHom.id R) where
  G := 𝟭 C
  τ T := mulSq a b T (y T)
  nat {T T'} φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have key : ∀ w : A.obj T, w ∈ a.S T → Ideal.Quotient.mk (b.S T') (y T') * Ideal.Quotient.mk (b.S T') ((A.map φ).hom w) =
        Ideal.Quotient.mk (b.S T') ((A.map φ).hom (y T * w)) := by
      intro w hw
      rw [← map_mul, map_mul (A.map φ).hom, Ideal.Quotient.eq, ← sub_mul]
      exact hc _ (hy φ) (a.map_mem φ hw)
    exact Subtype.ext (key w hw)

end Abstract

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem sub_mem_of_lift {W : X.Opens} {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') (f : Γ(X, W))
    (v : T.B) (v' : T'.B) (hv : Ideal.Quotient.mk T.J v = ev T h f) (hv' : Ideal.Quotient.mk T'.J v' = ev T' h' f) :
    v' - φ.φ v ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [hv', ev_nat φ h h', ← hv]
  rfl

theorem lft_mul_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T f * lft W T g - lft W T (f * g) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, lft_spec T h, lft_spec T h, lft_spec T h, map_mul]

theorem J_mul_sFil (P : ObjectProperty (Thick (LL q))) (r : ℕ) (T : P.FullSubcategory) {v w : (sP P).A.obj T}
    (hv : v ∈ (sP P).J.S T) (hw : w ∈ (sFil P r).S T) : v * w ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have h1 : v ∈ (sFil P 1).S T := by
    have e := hF.one T
    rw [e]
    exact hv
  have := hF.mul 1 r T (x := v) (y := w) h1 hw
  have e : (((1 + r : ℕ)) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  rwa [e] at this

def mulZ {W : X.Opens} (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (z : Γ(X, W)) :
    CH.Mor (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (RingHom.id O) :=
  mulMor (sFil P r) (sFil P ((r : ℤ) + 1)) (sP P).J (fun T => lft W T.obj z)
    (fun {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) z _ _
      (lft_spec _ (hP _ T.property) z) (lft_spec _ (hP _ T'.property) z))
    (fun T _ _ hv hw => J_mul_sFil P r T hv hw)

theorem units_mul_relation_rearrange_commRing {S : Type} [CommRing S] (y w l l' : S) : y * (w * l) - w * l' = (y * l - l') * w := by ring

theorem stAct : StAct := by
  intro O _ X q W P hP r z
  refine ⟨((mulZ P hP r z).pull r).toAddMonoidHom, ?_⟩
  intro d t u hu x c hc
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulZ P hP r z).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj z) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have hd := lft_mul_sub _ (hP _ (s.obj (Fin.last r)).property) z (x I)
    have := J_mul_sFil P r _ hd hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (lft W (s.obj (Fin.last r)).obj z) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem rep_add {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' z'' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : ∀ s, z'' s - (z s + z' s) ∈ b.S _) (hc : Rep a b z c) (hc' : Rep a b z' c') :
    Rep a b z'' (c + c') := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  obtain ⟨f', hf', rfl, e'⟩ := hc'
  refine ⟨f + f', by rw [map_add (f := _), hf, hf', add_zero], rfl, fun s => ?_⟩
  change (show sqM a b _ from f s).1 + (show sqM a b _ from f' s).1 = _
  rw [e s, e' s, ← map_add (f := _)]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem rep_neg {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z' s - (-z s) ∈ b.S _) (hc : Rep a b z c) : Rep a b z' (-c) := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  refine ⟨-f, by rw [map_neg, hf, neg_zero], rfl, fun s => ?_⟩
  change -(show sqM a b _ from f s).1 = _
  rw [e s, ← map_neg]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem sum_wz_sub {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    {ι : Type} [Fintype ι] (I : ι → Fin j → Fin d) (s : ComposableArrows C j)
    (y y' : ι → Φ.A.obj (s.obj (Fin.last j))) (h : ∀ i, y i - y' i ∈ Φ.J.S _) :
    ∑ i, wz u (I i) s * y i - ∑ i, wz u (I i) s * y' i ∈ (Fil ((j : ℤ) + 1)).S _ := by
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← mul_sub]
  have h1 : y i - y' i ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact h i
  have := hF.mul j 1 _ (wz_mem hF u hu (I i) s) h1
  rwa [Nat.cast_add, Nat.cast_one] at this

end Abstract

section Forms
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_add_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T (f + g) - (lft W T f + lft W T g) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), lft_spec T h, lft_spec T h, lft_spec T h, map_add (f := _), sub_self]

theorem lft_neg_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f : Γ(X, W)) :
    lft W T (-f) - (-lft W T f) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, lft_spec T h, lft_spec T h, map_neg, sub_self]

theorem lift_cocycle {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (i : Fin d)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' := by
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hu i _ (hP _ T'.property), ev_nat φ.hom (hP _ T.property) (hP _ T'.property),
    ← hu i _ (hP _ T.property)]
  exact sub_eq_zero.2 rfl

end Forms

theorem stAdd : StAdd := by
  intro O _ X q W d t u hu P hP r x x' c c' hc hc'
  have hF : IsFil (sP P) (sFil P) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hcoc := fun i {T T' : P.FullSubcategory} (φ : T ⟶ T') => lift_cocycle hu P hP i φ
  constructor
  · refine rep_add (fun s => ?_) hc hc'
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((x + x') I)))
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) +
        (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x' I)))
      (fun I => lft_add_sub _ (hP _ (s.obj (Fin.last r)).property) _ _)
    simpa only [mul_add, Finset.sum_add_distrib] using this
  · refine rep_neg (fun s => ?_) hc
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((-x) I)))
      (fun I => -(show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)))
      (fun I => lft_neg_sub _ (hP _ (s.obj (Fin.last r)).property) _)
    simpa only [mul_neg, Finset.sum_neg_distrib] using this

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CocProd (tele sa_val)
open GlobalTheory.CompanionTheory.TowerEnd (Q dQ val Vals cl d_cl dQ_apply)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.Coc

theorem alt_sum {B : Type*} [CommRing B] {j : ℕ} (w : Fin j → Fin (j + 2) → B) :
    ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) *
      ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) = 0 := by
  classical
  set u : Fin j → B := fun k => w k k.succ.castSucc - w k k.castSucc.castSucc with hu
  set v : Fin j → B := fun k => w k k.succ.succ - w k k.succ.castSucc with hv
  set P : ℕ → B := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → B := fun i =>
    ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) with hT
  have cg : ∀ (k : Fin j) {p q p' q' : Fin (j + 2)}, (p : ℕ) = p' → (q : ℕ) = q' →
      w k p - w k q = w k p' - w k q' := by
    intro k p q p' q' h h'
    rw [Fin.ext h, Fin.ext h']
  have hT0 : T (Fin.castSucc 0) = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => w k (i.succ.castSucc.succAbove k.succ) -
        w k (i.succ.castSucc.succAbove k.castSucc)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · have e : u i + v i = w i i.succ.succ - w i i.castSucc.castSucc := by
          rw [hu, hv]; ring
        rw [e]
        refine cg i ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
        · refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  change ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) * T i = 0
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hint : ∑ i : Fin j, (-1 : B) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * T i.succ.castSucc =
      ∑ m ∈ Finset.range j, (-1 : B) ^ (m + 1) * (P (m + 1) + P m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (-1 : B) ^ (m + 1) * (P (m + 1) + P m)) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hTi]
    simp only [Fin.val_castSucc, Fin.val_succ]
  rw [hint, hT0, hTl]
  simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
  linear_combination tele P j

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def vt (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last p)))).hom (c (s.obj p))

theorem vt_last (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1))
    (hp : p = Fin.last n) : vt c s p = c (s.obj (Fin.last n)) := by
  subst hp
  have : (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ := Subsingleton.elim _ _
  unfold vt
  rw [this, s.map_id]
  simp

theorem face_vt (c : ∀ T : C, Φ.A.obj T) {j : ℕ} (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (c ((face i s).obj (Fin.last j))) = vt c s (i.succAbove (Fin.last j)) := rfl

theorem face_wz {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T) (I : Fin j → Fin d)
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (wz u I (face i s)) =
      ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) := by
  have map_map {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (y : Φ.A.obj X) :
      (Φ.A.map f).hom ((Φ.A.map g).hom y) = (Φ.A.map (g ≫ f)).hom y := by
    simp
  unfold wz
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [map_sub]
  rw [map_map]
  have e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e, map_map, e, map_map]
  have e2 : (face i s).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le) ≫
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) =
      s.map (homOfLE (Fin.le_last (i.succAbove k.castSucc))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e2]
  rfl

theorem d_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (y : ∀ T : C, Φ.A.obj T) (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (Φ.A.map φ).hom (y T) ∈ Φ.J.S T')
    (I : Fin j → Fin d) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) ∈ (Fil ((j : ℤ) + 1)).S _ := by
  set Y := y (s.obj (Fin.last (j + 1))) with hY
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) with hT
  set V : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    vt y s (i.succAbove (Fin.last j)) with hV
  have hVY : ∀ i : Fin (j + 1), V i.castSucc = Y := by
    intro i
    refine vt_last y s _ (Fin.ext ?_)
    have := i.2
    rw [sa_val]
    simp only [Fin.val_last, Fin.val_castSucc]
    split_ifs <;> omega
  have hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) =
      (-1) ^ j * (T (Fin.last (j + 1)) * (Y - V (Fin.last (j + 1)))) := by
    have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
        (wz u I (face i s) * y ((face i s).obj (Fin.last j))) = (-1) ^ (i : ℕ) * (T i * V i) := by
      intro i
      rw [map_mul, face_wz, face_vt, zsmul_eq_mul]
      push_cast
      rfl
    have h0 := alt_sum (B := Φ.A.obj (s.obj (Fin.last (j + 1)))) (j := j) (fun k p => vt (u (I k)) s p)
    change ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) * T i = 0 at h0
    rw [Fin.sum_univ_castSucc] at h0
    rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc]
    have h1 : ∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * (T i.castSucc * V i.castSucc) =
        (∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * T i.castSucc) * Y := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hVY]
      ring
    rw [h1]
    simp only [Fin.val_last] at h0 ⊢
    linear_combination Y * h0
  rw [hsum]
  refine Ideal.mul_mem_left _ _ ?_
  have hA : T (Fin.last (j + 1)) ∈ (Fil (j : ℤ)).S _ := by
    have := (Fil (j : ℤ)).map_mem (toLast (Fin.last (j + 1)) s) (wz_mem hF u hu I (face (Fin.last (j + 1)) s))
    rwa [face_wz] at this
  have hB : Y - V (Fin.last (j + 1)) ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    have e : (((1 : ℕ) : ℤ)) = 1 := rfl
    rw [e, hF.one]
    have h := hy (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))
    have e2 : V (Fin.last (j + 1)) = (Φ.A.map (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))).hom
        (y (s.obj (Fin.last j).castSucc)) := by
      have : (Fin.last (j + 1)).succAbove (Fin.last j) = (Fin.last j).castSucc := Fin.succAbove_last_apply _
      simp only [hV, vt]
      rw [this]
    rw [e2]
    exact h
  have h := hF.mul j 1 _ hA hB
  have e : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  rwa [e] at h

end GlobalTheory.CompanionTheory.GrForm.Coc


open GlobalTheory.CompanionTheory.GrForm.Coc in
theorem GlobalTheory.CompanionTheory.GrForm.stCocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  intro R _ C _ Φ Fil hF d j u hu y hy I
  let z : Q Φ.A j := fun s => (wz u I s * y (s.obj (Fin.last j)) : Φ.A.obj (s.obj (Fin.last j)))
  have hz : Vals (Fil j) z := fun s => Ideal.mul_mem_right _ _ (wz_mem hF u hu I s)
  refine ⟨cl (Fil j) (Fil ((j : ℤ) + 1)) z hz, ?_, fun s => rfl⟩
  rw [d_cl]
  funext s
  apply Subtype.ext
  change Ideal.Quotient.mk _ (val (dQ Φ.A j z) s) = 0
  rw [dQ_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (d_mem hF u hu y hy I s)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrForm.AffCover

theorem iInf_basicOpen {X : Scheme.{0}} {V : X.Opens} : ∀ (n : ℕ) (g : Fin (n + 1) → Γ(X, V)),
    (⨅ a, X.basicOpen (g a)) = X.basicOpen (∏ k, g k) := by
  intro n
  induction n with
  | zero =>
    intro g
    simp
  | succ n ih =>
    intro g
    rw [Fin.prod_univ_succ, Scheme.basicOpen_mul, ← ih (fun k => g k.succ)]
    exact le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a => iInf_le _ a.succ))
      (le_iInf fun a => Fin.cases inf_le_left (fun b => inf_le_right.trans (iInf_le _ b)) a)

theorem stCover : GlobalTheory.CompanionTheory.GrForm.StCover := by
  intro O _ X q _ V hV
  classical
  have loc : ∀ x : V, ∃ (f : Γ(X, V)) (d : ℕ), x.1 ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d) := by
    intro x
    have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V le_top).hom :=
      RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
    obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth
      RingHom.isStandardSmooth_respectsIso q hV h x.2
    obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨f, n, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩
  choose f d hx hc using loc
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2) (fun x hxV => Set.mem_iUnion.2 ⟨⟨x, hxV⟩, hx _⟩)
  refine ⟨t, inferInstance, fun a => X.basicOpen (f a.1), fun a => d a.1, fun a => (hc a.1).some, ?_, ?_⟩
  · refine le_antisymm (iSup_le fun a => X.basicOpen_le _) fun x hxV => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht hxV)
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  · intro n i
    have e : capO (fun a : t => X.basicOpen (f a.1)) i = X.basicOpen (∏ k, f (i k).1) :=
      iInf_basicOpen n (fun k => f (i k).1)
    rw [e]
    exact hV.basicOpen _

end GlobalTheory.CompanionTheory.GrForm.AffCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsInertiaStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_equiv_transports_inertia : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ inv : InvFam F Ω l r, ∃ inv' : InvFam F' Ω' l r, ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (Function.Bijective (inv A) → Function.Bijective (inv' A')) ∧ (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → inv' A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.InvTransport.exists_invFam | exact GlobalTheory.CompanionTheory.PTIso.InvTransport.exists_invFam | (intros; apply GlobalTheory.CompanionTheory.PTIso.InvTransport.exists_invFam <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsResidueStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_equiv_transports_residue : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) → (∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)) → ∀ (ζ : Ω) (v : HeightOneSpectrum (𝓞 F)) (iA : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (iA' : H2 (muLoc F' l r A') →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → iA' (Submodule.Quotient.mk z') = iA (Submodule.Quotient.mk z)) → IsNormalised ζ A v iA → IsNormalised (E ζ) A' (eV v) iA' := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer | exact GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer | (intros; apply GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitUniversalEqPullbackBoxEvaluationStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitUniversal_eq_pullback_box_evaluation : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (w : Cn (box F) n), UU F (evF F T₀ ε) n w = pulln (boxE F T₀ ε) n w := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.UU_evF | exact GlobalTheory.CompanionTheory.HopfC.UU_evF | (intros; apply GlobalTheory.CompanionTheory.HopfC.UU_evF <;> assumption)
end

