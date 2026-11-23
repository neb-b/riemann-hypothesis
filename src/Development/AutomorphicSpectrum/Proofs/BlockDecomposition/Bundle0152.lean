module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0150
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatCocycleTensorRepresentationStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_cocycle_tensor_representation : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (f : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] N),
    (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f T T'' (φ ≫ ψ) = (mp F ψ).toLinearMap.rTensor N (f T T' φ) + f T' T'' ψ) →
    ∃ t : Z1 F ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = f T T' φ := by
  first | exact @GlobalTheory.CompanionTheory.Axis.cocycle_of_flat | exact GlobalTheory.CompanionTheory.Axis.cocycle_of_flat | (intros; apply GlobalTheory.CompanionTheory.Axis.cocycle_of_flat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormCoboundaryRelation
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrDelta
open GlobalTheory.CompanionTheory.CocProd

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem sqMap_val {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {T T' : C} (φ : T ⟶ T') (z : sqM a b T)
    (u : A.obj T) (h : z.1 = Ideal.Quotient.mk _ u) :
    (sqMap a b φ z).1 = Ideal.Quotient.mk _ ((A.map φ).hom u) := by
  obtain ⟨x, hx⟩ := z
  obtain rfl : x = _ := h
  rfl

variable {d : ℕ} (Q : Poly Φ) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)

theorem Pmap_j_apply {T T' : C} (φ : T ⟶ T') (u : Φ.A.obj T) :
    (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom ((Φ.A.map (Q.j T)).hom u) =
      (Φ.A.map (Q.j T')).hom ((Φ.A.map φ).hom u) := by
  exact (Cut.mapA_comp _ _ u).symm.trans
    ((congrArg (fun f => (Φ.A.map f).hom u) (Cut.Pmap_j Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).trans
      (Cut.mapA_comp _ _ u))

theorem Pmap_shift {T₀ T T' : C} (ψ : T₀ ⟶ T) (φ : T ⟶ T') :
    (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom
      (Q.X T + (Φ.A.map (Q.j T)).hom (E.a σ 0 ψ)) =
      Q.X T' + (Φ.A.map (Q.j T')).hom (E.a σ 0 (ψ ≫ φ)) := by
  have h : (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom (Q.X T) =
      Q.X T' + (Φ.A.map (Q.j T')).hom (E.a σ 0 φ) :=
    Cut.Pmap_X Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ
  rw [map_add (f := _), Pmap_j_apply, a_comp, map_add (f := _), h]
  abel

def Bv {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) : Φ.A.obj (Q.P (s.obj (Fin.last n))) :=
  Q.X _ + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.le_last p))))

theorem Bv_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Bv Q E σ s p ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
  have h : Bv Q E σ s p ∈ Φ.J.S _ := Ideal.add_mem _ (Q.X_mem _) (Φ.J.map_mem _ (E.mem 0 _ _))
  rw [Nat.cast_one, hF.one]
  exact h

theorem term_val {Fil : ℤ → IdF Φ.A} {j : ℕ} {r : ℤ} (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j)
    (hy : ∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s)))
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (show sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1)))) from
      ((Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r).map (toLast i s)).hom (y (face i s))).1 =
      Ideal.Quotient.mk _ (Bv Q E σ s (i.succAbove 0) *
        (Φ.A.map (Q.j _)).hom ((Φ.A.map (toLast i s)).hom (E.form σ (Fin.succ ∘ I) x (face i s)))) := by
  refine (sqMap_val (Fil r) (Fil (r + 1)) (Cut.Pmap Q (X := (Pt.Sσ σ).obj _) (Y := (Pt.Sσ σ).obj _) (toLast i s))
    (y (face i s)) _ (hy (face i s))).trans ?_
  have e : (face i s).map (homOfLE (Fin.zero_le (Fin.last j))) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove 0))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  have h1 := Pmap_shift Q E σ ((face i s).map (homOfLE (Fin.zero_le (Fin.last j)))) (toLast i s)
  have h2 := Pmap_j_apply Q E σ (toLast i s) (E.form σ (Fin.succ ∘ I) x (face i s))
  rw [e] at h1
  exact congrArg (Ideal.Quotient.mk _) ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 h2))

theorem Bv_zero {n : ℕ} (s : ComposableArrows C (n + 1)) :
    Bv Q E σ s 0 = Bv Q E σ s 1 + (Φ.A.map (Q.j _)).hom (ga E σ 0 s 0 1 (Fin.zero_le _)) := by
  have e : s.map (homOfLE (Fin.le_last (0 : Fin (n + 2)))) =
      s.map (homOfLE (Fin.zero_le (1 : Fin (n + 2)))) ≫ s.map (homOfLE (Fin.le_last (1 : Fin (n + 2)))) := by
    rw [← s.map_comp]; rfl
  unfold Bv ga
  rw [e, a_comp, map_add (f := _)]
  abel

theorem form_cons {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) :
    E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s =
      ga E σ 0 s 0 1 (Fin.zero_le _) * (Φ.A.map (toLast 0 s)).hom (E.form σ (Fin.succ ∘ I) x (face 0 s)) := by
  rw [face_form]
  have hl : (0 : Fin (j + 2)).succAbove (Fin.last j) = Fin.last (j + 1) := by simp
  have hW : (Φ.A.map (toLast 0 s)).hom ((Φ.A.map (σ _)).hom x) = (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x := by
    rw [map_map, show σ _ ≫ toLast 0 s = σ (s.obj (Fin.last (j + 1))) from sec_last E σ s _ hl]
  rw [hW]
  unfold Frame.form
  rw [Fin.prod_univ_succ, mul_assoc]
  congr 2

theorem alt_sum {S S' F : Type*} [CommRing S] [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (J : F) (n : ℕ)
    (t : Fin (n + 1) → S) (b : Fin (n + 1) → S') (B : S') (g : S) (h0 : B = b 0 + J g)
    (hs : ∀ k : Fin n, b k.succ = B) :
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (b i * J (t i)) =
      B * J (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • t i) - J (g * t 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i : Fin (n + 1) => B * J ((-1 : ℤ) ^ (i : ℕ) • t i))]
  have h : ∀ k : Fin n, (-1 : ℤ) ^ (k.succ : ℕ) • (b k.succ * J (t k.succ)) = B * J ((-1 : ℤ) ^ (k.succ : ℕ) • t k.succ) := by
    intro k
    rw [hs, map_zsmul, mul_smul_comm]
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp only [Fin.val_zero, pow_zero, one_smul, map_mul, h0]
  ring

theorem gr_delta {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ)
    (hr : r = j + 1 + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j) (w : CH.Cn (gr Fil r) (j + 1))
    (hy : ∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s)))
    (hw : ∀ s, (show sqM _ _ _ from w s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) :
    CH.d _ j y = -(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w := by
  funext s
  apply Subtype.ext
  have hL : Subtype.val (CH.d _ j y s : sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) =
      Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Bv Q E σ s (i.succAbove 0) *
        (Φ.A.map (Q.j _)).hom ((Φ.A.map (toLast i s)).hom (E.form σ (Fin.succ ∘ I) x (face i s))))) := by
    change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r).map (toLast i s)).hom (y (face i s)) :
      sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    refine Eq.trans ?_ (congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z) (term_val Q E σ I x y hy s i))
    rfl
  have hR : Subtype.val ((-(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w) s :
      sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) =
      -Ideal.Quotient.mk _ ((Φ.A.map (Q.j _)).hom (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) :=
    congrArg Neg.neg (sqMap_val (Fil r) (Fil (r + 1)) (Q.j (s.obj (Fin.last (j + 1)))) (w s) _ (hw s))
  refine hL.trans (Eq.trans ?_ hR.symm)
  change Ideal.Quotient.mk ((Fil (r + 1)).S (Q.P (s.obj (Fin.last (j + 1))))) _ =
    -Ideal.Quotient.mk ((Fil (r + 1)).S (Q.P (s.obj (Fin.last (j + 1))))) _
  rw [alt_sum (Φ.A.map (Q.j _)).hom (j + 1) _ (fun i => Bv Q E σ s (i.succAbove 0)) (Bv Q E σ s 0)
    (ga E σ 0 s 0 1 (Fin.zero_le _))
    (by simpa using Bv_zero Q E σ s) (fun k => by simp), ← map_neg, Ideal.Quotient.eq, form_cons]
  have hD := d_form_mem E σ hF hc j q (Fin.succ ∘ I) x hx s
  have hJ := (Fil (((j : ℤ) + q) + 1)).map_mem (Q.j (s.obj (Fin.last (j + 1)))) hD
  have e1 : (((j + q + 1 : ℕ) : ℤ)) = ((j : ℤ) + q) + 1 := by push_cast; ring
  rw [← e1] at hJ
  have hm := hF.mul 1 (j + q + 1) _ (Bv_mem Q E σ hF s 0) hJ
  have e2 : (((1 + (j + q + 1) : ℕ) : ℤ)) = r + 1 := by rw [hr]; push_cast; ring
  rw [e2] at hm
  convert hm using 1
  ring

end GlobalTheory.CompanionTheory.GrDelta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltration
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FormMem

theorem prod_fil_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (T : C) : ∀ (n : ℕ) (f : Fin n → Φ.A.obj T), (∀ k, f k ∈ (Fil 1).S T) →
      ∏ k, f k ∈ (Fil (n : ℤ)).S T := by
  intro n
  induction n with
  | zero =>
    intro f _
    rw [hF.top ((0 : ℕ) : ℤ) (by simp) T]
    exact Submodule.mem_top
  | succ n ih =>
    intro f h
    rw [Fin.prod_univ_succ]
    simpa only [Nat.add_comm 1 n] using
      hF.mul 1 n T (h 0) (ih (fun k => f k.succ) fun k => h k.succ)

theorem form_mem : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  refine hF.mul j q _ (prod_fil_mem hF _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _

end GlobalTheory.CompanionTheory.FormMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRestrictionCocycle
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrPull
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem prod_mem_fil {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (T : C) :
    ∀ (n : ℕ) (g : Fin n → Φ.A.obj T), (∀ k, g k ∈ Φ.J.S T) → ∏ k, g k ∈ (Fil n).S T
  | 0, g, _ => by
    have h := hF.top 0 le_rfl T
    simp only [Nat.cast_zero, h]
    exact Submodule.mem_top
  | n + 1, g, h => by
    rw [Fin.prod_univ_castSucc]
    have h1 : g (Fin.last n) ∈ (Fil ((1 : ℕ) : ℤ)).S T := by
      rw [Nat.cast_one, hF.one]; exact h _
    exact hF.mul n 1 T (prod_mem_fil hF T n _ fun k => h _) h1

variable {d : ℕ} {E : Frame Φ (d + 1)} (Q : Poly Φ) (σ : ∀ T : C, E.D ⟶ T)

theorem tau_sec_Pmap (i : Fin d) {T T' : C} (φ : T ⟶ T') :
    E.τ i.succ (Cut.sec Q ⟨T, σ T⟩ ≫ Cut.Pmap Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ) (Cut.sec Q ⟨T', σ T'⟩) =
      (Φ.A.map (Q.j T')).hom (E.τ i.succ (σ T ≫ φ) (σ T')) := by
  rw [Cut.τ_sec, if_neg (Fin.succ_ne_zero i), neg_zero, zero_add]
  have e : σ T ≫ Q.j T ≫ Cut.Pmap Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ = (σ T ≫ φ) ≫ Q.j T' := by
    have := Cut.Pmap_j Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ
    simp only at this
    rw [this, Category.assoc]
  simp only
  rw [e, E.add i.succ _ (σ T' ≫ Q.j T') _, E.nat]
  have h := Cut.sec_spec Q (E := E) ⟨T', σ T'⟩ i.succ
  simp only at h
  rw [h, if_neg (Fin.succ_ne_zero i), add_zero]

theorem factor {T₀ T₁ T₂ : C} (i : Fin d) (b : T₀ ⟶ T₁) (a : T₁ ⟶ T₂) :
    (Φ.A.map (Cut.Pmap Q (X := ⟨T₁, σ T₁⟩) (Y := ⟨T₂, σ T₂⟩) a)).hom
      (E.τ i.succ (Cut.sec Q ⟨T₀, σ T₀⟩ ≫ Cut.Pmap Q (X := ⟨T₀, σ T₀⟩) (Y := ⟨T₁, σ T₁⟩) b) (Cut.sec Q ⟨T₁, σ T₁⟩)) =
      (Φ.A.map (Q.j T₂)).hom ((Φ.A.map a).hom (E.τ i.succ (σ T₀ ≫ b) (σ T₁))) := by
  rw [tau_sec_Pmap, ← Cut.mapA_comp, ← Cut.mapA_comp]
  have := Cut.Pmap_j Q (X := ⟨T₁, σ T₁⟩) (Y := ⟨T₂, σ T₂⟩) a
  simp only at this
  rw [this]

variable {Fil : ℤ → IdF Φ.A}

theorem form_sub_mem (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (s : ComposableArrows C j) :
    (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from (Cut.E1 E).form Cut.can I x (s ⋙ Cut.Pσ Q σ)) -
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (E.form σ (Fin.succ ∘ I) x s) ∈
        (Fil (r + 1)).S (Q.P (s.obj (Fin.last j))) := by
  have e1 : ∀ k : Fin j, ((Cut.Φ1 E).A.map ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.le_last k.succ)))).hom
      ((Cut.E1 E).a Cut.can (I k) ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom ((Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
        (E.a σ ((Fin.succ ∘ I) k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))) :=
    fun k => factor Q σ (I k) _ _
  let P₀ : Φ.A.obj (s.obj (Fin.last j)) := ∏ k : Fin j, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (E.a σ ((Fin.succ ∘ I) k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))
  have hP : P₀ ∈ (Fil j).S (s.obj (Fin.last j)) :=
    prod_mem_fil hF _ j _ fun k => Φ.J.map_mem _ (E.mem _ _ _)
  let u : E.D ⟶ Q.P (s.obj (Fin.last j)) := Cut.sec Q ⟨s.obj (Fin.last j), σ _⟩
  let v : E.D ⟶ Q.P (s.obj (Fin.last j)) := σ (s.obj (Fin.last j)) ≫ Q.j _
  have f1 : (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from (Cut.E1 E).form Cut.can I x (s ⋙ Cut.Pσ Q σ)) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ * (Φ.A.map u).hom x := by
    have h : (∏ k : Fin j, (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from
        ((Cut.Φ1 E).A.map ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.le_last k.succ)))).hom
          ((Cut.E1 E).a Cut.can (I k) ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))))) =
        (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ :=
      (Finset.prod_congr rfl fun k _ => e1 k).trans (map_prod (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom _ _).symm
    exact congrArg (· * (Φ.A.map u).hom x) h
  have f2 : (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (E.form σ (Fin.succ ∘ I) x s) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ * (Φ.A.map v).hom x := by
    change (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (P₀ * (Φ.A.map (σ _)).hom x) = _
    rw [map_mul, ← Cut.mapA_comp]
  rw [f1, f2, ← mul_sub]
  have hcast : r + 1 = ((j + (q + 1) : ℕ) : ℤ) := by rw [hr]; push_cast; ring
  rw [hcast]
  refine hF.mul j (q + 1) _ ((Fil j).map_mem _ hP) ?_
  have := hc q u v hx
  have e : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
  rw [e]
  exact this

theorem gr_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (f : CH.Cn (Cut.U E ⋙ gr Fil r) j) (g : CH.Cn (gr Fil r) j)
    (hf : ∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ ((Cut.E1 E).form Cut.can I x s))
    (hg : ∀ s, (show sqM _ _ _ from g s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.succ ∘ I) x s)) :
    (CH.Mor.restrict (Cut.U E ⋙ gr Fil r) (Cut.Pσ Q σ)).pullC j f =
      (CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC j g := by
  funext s
  refine Subtype.ext ?_
  have h1 := hf (s ⋙ Cut.Pσ Q σ)
  have h2 := hg s
  change (show sqM _ _ _ from f (s ⋙ Cut.Pσ Q σ)).1 =
    Ideal.quotientMapₐ _ (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (fun _ hx => (Fil (r + 1)).map_mem _ hx)
      (show sqM _ _ _ from g s).1
  rw [h1, h2]
  exact Ideal.Quotient.eq.2 (form_sub_mem Q σ hF hc j q r hr I x hx s)

end
end GlobalTheory.CompanionTheory.GrPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrame
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LocGr

theorem H_succ_subsingleton {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {T₀ : C}
    (h : Limits.IsInitial T₀) (n : ℕ) : Subsingleton (CH.H F (n + 1)) := by
  have key : ∀ c : CH.H F (n + 1), c = 0 := by
    intro c
    obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨g, hg⟩ := (CrystallineSemistableComparison.P.initial F T₀ h).2.2.2 n f hf
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change f ∈ (CH.cx F).B (n + 1)
    exact ⟨g, hg.trans (one_smul R f)⟩
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem H_zero_subsingleton {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {r : ℤ} (hr : r < 0) : Subsingleton (CH.H (gr Fil r) 0) := by
  have hT : ∀ T, Subsingleton ((gr Fil r).obj T) := fun T => by
    have h1 : (Fil (r + 1)).S T = ⊤ := hF.top _ (by omega) T
    have h2 : Subsingleton (Φ.A.obj T ⧸ (Fil (r + 1)).S T) := Ideal.Quotient.subsingleton_iff.2 h1
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim (α := Φ.A.obj T ⧸ (Fil (r + 1)).S T) _ _)⟩
  have hC : Subsingleton (CH.Cn (gr Fil r) 0) := ⟨fun a b => funext fun s => (hT _).elim _ _⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have e : f = g := hC.elim f g
  subst e
  rfl

theorem gr_zero : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (E : Frame Φ 0) (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D := by
  intro R _ C _ Φ Fil hF E σ r j
  have hI : Limits.IsInitial E.D := E.initial
  refine ⟨fun hr => ?_, fun q hq => ?_⟩
  · cases j with
    | zero => exact H_zero_subsingleton hF (by simpa using hr)
    | succ n => exact H_succ_subsingleton _ hI n
  · cases j with
    | succ n =>
      have hs := H_succ_subsingleton (gr Fil r) hI n
      haveI : IsEmpty (Idx (n + 1) 0) := ⟨fun I => (I.1 0).elim0⟩
      refine ⟨fun c => ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, ?_⟩, fun x _ _ I => isEmptyElim I⟩
      unfold CrystallineSemistableComparison.Pb.Rep
      refine ⟨0, map_zero _, Subsingleton.elim _ _, fun s => ?_⟩
      have e := Fintype.sum_empty (fun I : Idx (n + 1) 0 => E.form σ I.1 (isEmptyElim I) s)
      refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) e).symm
      exact (map_zero _).symm
    | zero =>
      have hq' : r = q := by simpa using hq
      subst hq'
      haveI : Unique (Idx 0 0) := ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun I => Subtype.ext (funext fun a => a.elim0)⟩
      have hform : ∀ (x : Idx 0 0 → Φ.A.obj E.D) (s : ComposableArrows C 0),
          ∑ I : Idx 0 0, E.form σ I.1 (x I) s = (Φ.A.map (σ _)).hom (x default) := by
        intro x s
        rw [Fintype.sum_unique]
        simp [Frame.form]
      refine ⟨fun c => ?_, fun x hx hrep I => ?_⟩
      · obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨m, hm⟩ := (CrystallineSemistableComparison.P.initial (gr Fil (q : ℤ)) E.D hI).2.2.1 f hf
        obtain ⟨m', hm'⟩ := m
        obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hm'
        refine ⟨fun _ => y, fun _ => hy, ?_⟩
        unfold CrystallineSemistableComparison.Pb.Rep
        refine ⟨f, hf, rfl, fun s => ?_⟩
        refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) (hform (fun _ => y) s)).symm
        have h1 := congrFun (hm.trans (one_smul R f)) s
        have h2 := congrArg Subtype.val h1
        rw [show σ (s.obj (Fin.last 0)) = hI.to _ from hI.hom_ext _ _]
        exact h2.symm
      · unfold CrystallineSemistableComparison.Pb.Rep at hrep
        obtain ⟨f, hf, h0, hs⟩ := hrep
        have hf0 : f = 0 := by
          have h3 : (⟨f, hf⟩ : (CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) ∈
              ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).B 0).submoduleOf ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) :=
            (Submodule.Quotient.mk_eq_zero _).1 h0.symm
          exact (Submodule.mem_bot R).1 h3
        subst hf0
        have h1 := (hs (ComposableArrows.mk₀ E.D)).trans (congrArg (Ideal.Quotient.mk _) (hform x _))
        have hσ : σ ((ComposableArrows.mk₀ E.D).obj (Fin.last 0)) = 𝟙 E.D := hI.hom_ext _ _
        rw [hσ] at h1
        have h4 : (Φ.A.map (𝟙 E.D)).hom (x default) = x default := by
          rw [Φ.A.map_id]; rfl
        have h5 : Ideal.Quotient.mk ((Fil ((q : ℤ) + 1)).S E.D) (x default) = 0 := by
          rw [← h4]
          exact h1.symm
        rw [Subsingleton.elim I default]
        exact Ideal.Quotient.eq_zero_iff_mem.1 h5

end GlobalTheory.CompanionTheory.LocGr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverField
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrSplitField

theorem exists_step {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B}
    (γ : DividedPowers I) (i : ℕ) :
    ∃ C : Submodule K B, (∀ n ∈ C, n ∈ pdP γ i) ∧ (∀ n ∈ C, n ∈ pdP γ (i + 1) → n = 0) ∧
      ∀ x ∈ pdP γ i, ∃ n ∈ C, x - n ∈ pdP γ (i + 1) := by
  have hQ : (pdP γ (i + 1)).restrictScalars K ≤ (pdP γ i).restrictScalars K :=
    fun x hx => (Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, (Nat.le_succ i).trans hr, hz⟩ :
      pdP γ (i + 1) ≤ pdP γ i) hx
  obtain ⟨c, hc⟩ := exists_isCompl
    (⟨(pdP γ (i + 1)).restrictScalars K, hQ⟩ : Set.Iic ((pdP γ i).restrictScalars K))
  have hinf : (pdP γ (i + 1)).restrictScalars K ⊓ c.1 = ⊥ := congrArg Subtype.val hc.inf_eq_bot
  have hsup : (pdP γ (i + 1)).restrictScalars K ⊔ c.1 = (pdP γ i).restrictScalars K :=
    congrArg Subtype.val hc.sup_eq_top
  refine ⟨c.1, fun n hn => c.2 hn, fun n hn hn' => ?_, fun x hx => ?_⟩
  · have : n ∈ (pdP γ (i + 1)).restrictScalars K ⊓ c.1 := ⟨hn', hn⟩
    rw [hinf] at this
    simpa using this
  · have hx' : x ∈ (pdP γ (i + 1)).restrictScalars K ⊔ c.1 := by
      rw [hsup]
      exact hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    exact ⟨z, hz, by simpa using hy⟩

theorem nonempty_grSplit : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  intro K B _ _ _ I γ m hm
  choose C hC₁ hC₂ hC₃ using fun i : ℕ => exists_step (K := K) γ i
  exact ⟨{
    N := fun i => C i
    ν := fun i => (C i).subtype
    mem := fun i n => hC₁ i n n.2
    inj := fun i n h => Subtype.ext (hC₂ i n n.2 h)
    surj := fun i x hx => by
      obtain ⟨n, hn, h⟩ := hC₃ i x hx
      exact ⟨⟨n, hn⟩, h⟩
    nil := hm }⟩

end GlobalTheory.CompanionTheory.GrSplitField
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicativeStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_log_multiplicative : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ), pdP δ s = ⊥ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ {x y : B}, x ∈ J → y ∈ J → plogK δ s ((1 + x) * (1 + y) - 1) = plogK δ s x + plogK δ s y := by
  first | exact @GlobalTheory.CompanionTheory.PlogMul.plogK_mul | exact GlobalTheory.CompanionTheory.PlogMul.plogK_mul | (intros; apply GlobalTheory.CompanionTheory.PlogMul.plogK_mul <;> assumption)
end

