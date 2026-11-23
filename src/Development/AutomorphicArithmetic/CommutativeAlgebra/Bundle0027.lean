module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0021
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0024
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleLocalPrimitiveRootAndRootsOfUnity
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCupProductLevelwiseCompat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem units_map_smul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (η : ℤˣ) (x : A) :
    f (η • x) = η • f x := by
  simp [Units.smul_def]

private theorem colEx_transfer {C C' D D' : DC} (Φ : C.Hom C') (Ψ : D.Hom D') (p : ℕ) (η : ℤˣ)
    (e : ∀ s, C.A p s ≃+ D.A 0 s) (e' : ∀ s, C'.A p s ≃+ D'.A 0 s)
    (hd : ∀ s t x, e t (C.d p s t x) = D.d 0 s t (e s x))
    (hd' : ∀ s t x, e' t (C'.d p s t x) = D'.d 0 s t (e' s x))
    (hΦ : ∀ s x, e' s (Φ p s x) = η • Ψ 0 s (e s x)) (h : Ψ.ColEx 0) : Φ.ColEx p := by
  have hηη : ∀ {A : Type 1} [AddCommGroup A] (x : A), η • η • x = x := fun x => by
    rw [smul_smul, Int.units_mul_self, one_smul]
  intro s a y ha hy
  have hΨ : ∀ s x, Ψ 0 s (e s x) = η • e' s (Φ p s x) := fun s x => by rw [hΦ, hηη]
  obtain ⟨a', y', h1, h2⟩ := h s (e _ a) (η • e' s y)
    (by rw [← hd, ha, map_zero])
    (by rw [hΨ, hy, hd', units_map_smul])
  refine ⟨(e s).symm a', η • (e' _).symm y', ?_, ?_⟩
  · apply (e _).injective
    rw [hd, AddEquiv.apply_symm_apply, h1]
  · apply (e' _).injective
    have h3 : e' s y = η • (Ψ 0 s a' + D'.d 0 (s - 1) s y') := by rw [← h2, hηη]
    have h4 : e' (s - 1) (η • (e' (s - 1)).symm y') = η • y' := by
      have := units_map_smul (e' (s - 1)).toAddMonoidHom η ((e' (s - 1)).symm y')
      simpa using this
    rw [h3, map_add (f := _), hΦ, hd', AddEquiv.apply_symm_apply, h4, units_map_smul, smul_add]

private def lvl {R : Type} [CommRing R] {E : Spc} {p : ℕ} (Z : Sub E)
    (Z' : Sub (disc.obj (E.obj (op (SimplexCategory.mk p)))))
    (h : ∀ (W : Scheme.{0}) (z : Sx E p W), Z'.mem 0 W z ↔ Z.mem p W z) (M : Shv R) :
    Fam Z p M ≃+ Fam Z' 0 M where
  toFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).1 hx)⟩
  invFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).2 hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem disc_δ {R : Type} [CommRing R] {F : PSh} (Z : Sub (disc.obj F)) (L : Cx R) (m s : ℤ)
    (x : (famDC Z L m).A 0 s) : (famDC Z L m).δ 0 s x = 0 := by
  apply Subtype.ext
  funext U z
  have hf : ∀ i, Sx.face (E := disc.obj F) z i = z := fun _ => rfl
  change m.negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (show Fam Z 0 (L.X (s + m)) from x).1 U (Sx.face (E := disc.obj F) z i) = 0
  simp [Fin.sum_univ_two, hf]

private theorem fam_smul {R : Type} [CommRing R] {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) (η : ℤˣ) (a : Fam Z p M)
    (W : Scheme.{0}) (z : Sx E p W) : (η • a).1 W z = η • a.1 W z := by
  rcases Int.units_eq_one_or η with rfl | rfl <;> simp

theorem UpperTheory.relativeCupProduct_levelwise_compat :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X) (p : ℕ)
    (Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m))
    (Ψ : (famDC (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))) I 0).Hom (famDC (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))) K m)),
    IsProd μ π β Φ → IsProd μ (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) β Ψ → Ψ.TotEx → Φ.ColEx p := by
  intro R _ I J K μ X U E π m β p Φ Ψ hΦ hΨ hT
  have h0 : Ψ.ColEx 0 := UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero _ _ Ψ (disc_δ _ _ _) (disc_δ _ _ _) hT
  have hbot : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))).mem 0 W z ↔ (Sub.bot E).mem p W z :=
    fun _ _ => Iff.rfl
  have himg : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))).mem 0 W z ↔
        (Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z := fun W z =>
    ((UpperTheory.mem_pullbackImage_iff_factors_through_open U (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) 0 W z).1).trans
      ((UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1).symm
  refine colEx_transfer Φ Ψ p (m * (p : ℤ)).negOnePow (fun s => lvl _ _ hbot _) (fun s => lvl _ _ himg _)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) ?_ h0
  intro s x
  apply Subtype.ext
  funext W z
  have h1 := hΦ p s x W z
  have h2 := hΨ 0 s (lvl _ _ hbot _ x) W z
  refine Eq.trans h1 (Eq.trans ?_ (fam_smul _ _ _ (m * (p : ℤ)).negOnePow (Ψ 0 s (lvl _ _ hbot _ x)) W z).symm)
  refine congrArg _ (Eq.trans ?_ h2.symm)
  have h0' : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
  rw [h0', one_smul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCupProductRealizesProductOfRepresentativ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem inl_fold' (P : Arrow Spc) : dbl.inl P ≫ dbl.fold P = 𝟙 _ := pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _

private theorem inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

private theorem aw_last {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m) {W : Scheme.{0}} {p : ℕ}
    (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (r k : ℕ) (hr : r = p) (hk : k = 0) (s t w : ℤ) (h : s + t = w)
    (hs : -(r : ℤ) + n = s) (ht : -(k : ℤ) + m = t) (h0 : 0 + r ≤ p) (h1 : r + k ≤ p)
    (s' : ℤ) (hs' : -(p : ℤ) + n = s') (h' : s' + m = w) :
    μ.mul W s t w h (ev α r s hs W (x.sub 0 r h0)) (ev β k t ht W (x.sub r k h1)) =
      μ.mul W s' m w h' (ev α p s' hs' W x) b := by
  subst hr hk
  have ht' : m = t := by simpa using ht
  subst ht'
  subst hs
  subst hs'
  rw [(GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.1, hb]

private theorem aw_eval {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m)
    (γ : Cochain ((chains R).obj D) K (n + m)) (hγ : μ.IsAW rfl α β γ)
    (hβ : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx D k W), ev β k s h W y = 0)
    {W : Scheme.{0}} {p : ℕ} (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (w : ℤ) (h : -(p : ℤ) + (n + m) = w)
    (s : ℤ) (hs : -(p : ℤ) + n = s) (h' : s + m = w) :
    ev γ p w h W x = (m * (p : ℕ)).negOnePow • μ.mul W s m w h' (ev α p s hs W x) b := by
  rw [hγ p w h W x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · exact congrArg _ (aw_last μ α β x b hp hb _ _ rfl (Nat.sub_self p) _ _ _ _ _ _ _ _ s hs h')
  · intro r _
    have hk : 0 < p - ((Fin.castSucc r : Fin (p + 1)) : ℕ) := by
      have := r.2
      simp only [Fin.val_castSucc]
      omega
    rw [hβ _ hk, map_zero, smul_zero]

private theorem last_vertex {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {p : ℕ} {W : Scheme.{0}}
    (z : Sx E p W) (h : p + 0 ≤ p) (ι' : E ⟶ dbl (abv U π)) (ι : sch.obj X ⟶ dbl (opn U))
    (hι : ι' ≫ dbl.map (abvMap U π) = π ≫ ι) :
    ((z.map ι').sub p 0 h).map (dbl.map (abvMap U π)) = Sx.map (E := sch.obj X) (p := 0) ι (under π z) := by
  rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.1 ι']
  have h1 : ((z.sub p 0 h).map ι').map (dbl.map (abvMap U π)) = (z.sub p 0 h).map (ι' ≫ dbl.map (abvMap U π)) := rfl
  rw [h1, hι]
  have h2 : (z.sub p 0 h).map (π ≫ ι) = Sx.map (E := sch.obj X) (p := 0) ι (under π (z.sub p 0 h)) := rfl
  rw [h2, ((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.2, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.2 0 _]

theorem UpperTheory.relativeCupProduct_realizes_product_of_representative :
    LeafAW → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m j i n : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X), IsRep U β c.1 →
    ∀ Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m), IsProd (twPair q i j) π β Φ →
    ∀ (x : (famDC (Sub.bot E) (res _ (tw q i)) 0).Tot) (a : Ht q E n i), HRel x a → SRel (P := abv U π) (N := n + m) (Φ.tot x) (Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)).1 := by
  intro hAW q _ X U E π m j i n c β hrep Φ hΦ x a hx
  obtain ⟨-, -, γ₀, hγ₀, h0l, h0r, h0p⟩ := hrep
  obtain ⟨α, hα, hαx⟩ := hx
  let α' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q i)) n :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.fold (abv U π)))) α (zero_add n)
  let β' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q j)) m :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.map (abvMap U π)))) γ₀ (zero_add m)
  obtain ⟨γ, hγ, hcup⟩ := (hAW q i j).2 (dbl (abv U π)) n m α' β'
  have evα : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev α'.1 p s h W y = ev α.1 p s h W (y.map (dbl.fold (abv U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.fold (abv U π)) α.1 p s h W y
  have evβ : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev β'.1 p s h W y = ev γ₀.1 p s h W (y.map (dbl.map (abvMap U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.map (abvMap U π)) γ₀.1 p s h W y
  have hvan : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) k W), ev β'.1 k s h W y = 0 := by
    intro k hk s h W y
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [evβ]
    exact h0p k s _ W _
  have hinr : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (z : Sx (abv U π).right p W),
      ev γ.1 p s h W (z.map (dbl.inr (abv U π))) = 0 := by
    intro p s h W z
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inr (abv U π))).sub p 0 (by omega)) = 0 := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inr (abv U π)) (dbl.inr (opn U)) (dbl.inr_map (abvMap U π)))).trans ?_
      exact h0r W _
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ 0 (by omega) hb s h (-(p : ℤ) + n) rfl (by omega), map_zero, smul_zero]
  refine ⟨γ, ?_, ?_, hinr⟩
  · have hC : cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 = CohomologyClass.mk γ := by
      rw [← hcup, ← hα]
      change cup q _ (pull _ (dbl.map (abvMap U π)) _ m c.1) = _
      rw [← hγ₀]
      rfl
    have hz : pull _ (dbl.inr (abv U π)) (tw q (i + j)) (n + m) (CohomologyClass.mk γ) = 0 := by
      have h0 : zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m)) = 0 := by
        have hc : (zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m))).1 = 0 := by
          refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.1 _ _ fun p s h W z => ?_
          rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).1 0 0 p s h W z).2.2.1]
          exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.inr (abv U π)) γ.1 p s h W z).trans (hinr p s h W z)
        exact Cocycle.ext hc
      exact (congrArg CohomologyClass.mk h0).trans (CohomologyClass.mk_zero _ _ _)
    change CohomologyClass.mk γ = cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 -
      pull _ (dbl.fold (abv U π)) _ _ (pull _ (dbl.inr (abv U π)) _ _
        (cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1))
    rw [hC, hz, map_zero, sub_zero]
  · intro p s h W z
    have hs : -(p : ℤ) + n = s + 0 := by omega
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inl (abv U π))).sub p 0 (by omega)) = Sec.res (under π z) β := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inl (abv U π)) (dbl.inl (opn U)) (inl_map' (abvMap U π)))).trans ?_
      exact h0l W _
    have e := hΦ p s (x p s) W z
    rw [hαx p s hs W z] at e
    refine e.trans ?_
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ _ (by omega) hb (s + m) h (s + 0) hs (by omega), evα]
    have hf : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (𝟙 E) := by
      have h1 : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (dbl.inl (abv U π) ≫ dbl.fold (abv U π)) := rfl
      rw [h1, inl_fold']
      rfl
    rw [hf]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexBotTotalModel
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ConstantCochains

variable {R : Type} [CommRing R] {E : Spc} {K : Cx R}

private theorem map_id' {p : ℕ} {U : Scheme.{0}} (z : Sx E p U) : Sx.map (𝟙 E) z = z := rfl

private def cst {U : Scheme.{0}} {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) : Sec (K.X b) U := e ▸ v

private theorem res_cst {V U : Scheme.{0}} (g : V ⟶ U) {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) :
    Sec.res g (cst e v) = cst e (Sec.res g v) := by
  subst e; rfl

private theorem cst_fam (x : (famDC (Sub.bot E) K 0).Tot) (p : ℕ) (U : Scheme.{0}) (z : Sx E p U)
    {s t : ℤ} (e : t = s) (e' : t + 0 = s + 0) :
    (show Fam (Sub.bot E) p (K.X (s + 0)) from x p s).1 U z =
      cst e' ((show Fam (Sub.bot E) p (K.X (t + 0)) from x p t).1 U z) := by
  subst e; rfl

private theorem exists_cochain (n : ℤ) (x : (famDC (Sub.bot E) K 0).Tot) :
    ∃ γ : Cochain ((chains R).obj E) K n, Comp (𝟙 E) γ x := by
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (K.X s) U :=
    fun p s _ U z => cst (add_zero s) ((x p s).1 U z)
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (z : Sx E p U),
      Sec.res g (a p s h U z) = a p s h V (z.res g) := by
    intro p s h V U g z
    exact (res_cst g _ _).trans (congrArg (cst (add_zero s)) ((x p s).2.1 V U g z))
  have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ K.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U z,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ U z) = a p j (hp ▸ hij) U z := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U z => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U z
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  let γ : Cochain ((chains R).obj E) K n := Cochain.mk φ
  have hγ : ∀ p s h U z, ev γ p s h U z = a p s h U z := by
    intro p s h U z
    have he := hφ _ _ h p rfl U z
    rw [eqToHom_refl, Category.id_comp] at he
    exact he
  refine ⟨γ, ?_⟩
  intro p s h U z
  rw [map_id', hγ]
  exact cst_fam x p U z (add_zero s) (add_zero (s + 0))

private theorem eq_zero_of_comp {N : ℤ} (γ : Cochain ((chains R).obj E) K N)
    (h : Comp (𝟙 E) γ (0 : (famDC (Sub.bot E) K 0).Tot)) : γ = 0 := by
  have hext : ∀ α β : Cochain ((chains R).obj E) K N,
      (∀ p s h U z, ev α p s h U z = ev β p s h U z) → α = β := by
    intro α β H
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact CupSpec.free_ext _ _ (fun U z => H k s hs U z)
    · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
  apply hext
  intro p s hs U z
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 0 := ⟨s, (add_zero s).symm⟩
  have h1 := h p t hs U z
  rw [map_id'] at h1
  rw [← h1]
  simp [ev]
  rfl

private theorem eq_of_comp {N : ℤ} (γ γ' : Cochain ((chains R).obj E) K N)
    (x : (famDC (Sub.bot E) K 0).Tot) (h : Comp (𝟙 E) γ x) (h' : Comp (𝟙 E) γ' x) : γ = γ' := by
  have h2 := (UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 N N (add_zero N)).2.2.2.1 γ γ' x x h h'
  rw [sub_self] at h2
  exact sub_eq_zero.1 (eq_zero_of_comp _ h2)

end UpperTheory.ConstantCochains

open UpperTheory.ConstantCochains in
theorem UpperTheory.supportDoubleComplex_bot_totalModel :
    ∀ (R : Type) [CommRing R] (E : Spc) (K : Cx R) (n : ℤ), TModel (famDC (Sub.bot E) K 0) n (HRel (E := E) (K := K) (n := n)) := by
  intro R _ E K n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have Ik := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 k k (add_zero k)
  have I1 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1) (k + 1) (add_zero _)
  have I2 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1 + 1) (k + 1 + 1) (add_zero _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ⟩ := exists_cochain (k + 1) x
    have h1 := I1.2.2.1 γ x hγ
    rw [hD] at h1
    have h0 := eq_zero_of_comp _ h1
    exact ⟨CohomologyClass.mk (Cocycle.mk γ _ rfl h0), Cocycle.mk γ _ rfl h0, rfl, hγ⟩
  · intro c
    obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
    obtain ⟨x, hx, hc⟩ := I1.1 γ (fun _ _ _ _ _ hm => False.elim hm)
    refine ⟨x, hx, ?_, γ, rfl, hc⟩
    have h1 := I1.2.2.1 γ x hc
    rw [Cocycle.δ_eq_zero] at h1
    have c00 : Comp (𝟙 E) (0 : Cochain ((chains R).obj E) K (k + 1 + 1))
        (0 : (famDC (Sub.bot E) K 0).Tot) := by
      intro p s h U z
      simp [ev]
      rfl
    exact I2.2.1 0 _ 0 (I1.2.2.2.2 x hx) (fun _ _ _ => rfl) h1 c00
  · rintro x c x' c' ⟨γ, rfl, hγ⟩ ⟨γ', rfl, hγ'⟩
    exact ⟨γ - γ', CohomologyClass.mk_sub _ _, I1.2.2.2.1 _ _ _ _ hγ hγ'⟩
  · rintro x c hx ⟨γ, rfl, hγ⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ k rfl, add_sub_cancel_right]
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨y, hy, hyβ⟩ := Ik.1 β (fun _ _ _ _ _ hm => False.elim hm)
      refine ⟨y, hy, ?_⟩
      have h1 := Ik.2.2.1 β y hyβ
      rw [hβ] at h1
      exact I1.2.1 _ _ _ (Ik.2.2.2.2 y hy) hx h1 hγ
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ⟩ := exists_cochain k y
      exact ⟨β, eq_of_comp _ _ _ (Ik.2.2.1 β y hβ) hγ⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistGeneratorOfPrimitiveRootAndRootsEtaleLo
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

theorem UpperTheory.tateTwist_generator_of_primitiveRoot_and_roots_etaleLocal :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}), (∀ ζ : GlobalTheory.EtC.Prim q Γ(U, ⊤), Gen Scheme.etaleTopology q (GlobalTheory.EtC.tw q i).obj (GlobalTheory.EtC.twGen i ζ)) ∧ (UpperTheory.Et.Inv q U → LocT Scheme.etaleTopology U fun V _ => Nonempty (GlobalTheory.EtC.Prim q Γ(V, ⊤))) := by
  intro q _ i U
  obtain ⟨-, h2, h3, h4, -⟩ := UpperTheory.Cb.tateTwist_sections_locally_generated q i
  refine ⟨fun ζ => ⟨?_, ?_, ?_⟩, fun hq => (UpperTheory.Cb.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq⟩
  · have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext (ZMod.natCast_self q)
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q, h0, zero_smul]
  · intro V k c hV hc
    haveI := hV
    refine h3 V (ζ.map k.appTop.hom) c ?_
    rw [← h4 V U k ζ]
    exact hc
  · intro V k y
    obtain ⟨S, hS, h⟩ := h2 V (ζ.map k.appTop.hom) y
    refine ⟨S, hS, fun W g hg => ?_⟩
    obtain ⟨c, hc⟩ := h W g hg
    refine ⟨c, hc.trans ?_⟩
    have e : GlobalTheory.EtC.twGen i ((ζ.map k.appTop.hom).map g.appTop.hom) =
        GlobalTheory.EtC.Sec.res (g ≫ k) (GlobalTheory.EtC.twGen i ζ) := by
      rw [← h4 W V g, ← h4 V U k]
      simp [GlobalTheory.EtC.Sec.res]
    rw [e]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedSectionEqNsmulGeneratorOfConnected
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem tw_q_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) : q • a = 0 := by
  have h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]

private theorem tw_nsmul_mod {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) (n : ℕ) :
    n • a = (n % q) • a := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm, mul_nsmul, tw_q_nsmul, add_zero]

private theorem mod_eq_of_nsmul_eq {q : ℕ} [NeZero q] {i : ℤ} {U : Scheme.{0}} [Nonempty U]
    (ζ : Prim q Γ(U, ⊤)) {c c' : ℕ} (h : c • twGen i ζ = c' • twGen i ζ) : c % q = c' % q := by
  have hq : 1 ≤ q := NeZero.pos q
  have h1 : (q - 1) * c' + c' = q * c' := by
    have : (q - 1) * c' + c' = ((q - 1) + 1) * c' := by ring
    rw [this, Nat.sub_add_cancel hq]
  have h0 : (c + (q - 1) * c') • twGen i ζ = 0 := by
    rw [add_nsmul, h, ← add_nsmul, add_comm, h1, mul_comm, mul_nsmul, tw_q_nsmul]
  obtain ⟨k, hk⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have h2 : c + q * c' = c' + q * k := by
    rw [← hk, ← h1]
    ring
  calc c % q = (c + q * c') % q := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (c' + q * k) % q := by rw [h2]
    _ = c' % q := Nat.add_mul_mod_self_left _ _ _

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

private theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem res_gen {q : ℕ} [NeZero q] {i : ℤ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (ζ : Prim q Γ(U, ⊤)) :
    Sec.res k (twGen i (ζ.map g.appTop.hom)) = twGen i (ζ.map (k ≫ g).appTop.hom) := by
  rw [(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1]
  congr 1

theorem UpperTheory.twisted_section_eq_nsmul_generator_of_connected :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) [ConnectedSpace X] (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X), ∃ c : ℕ, y = c • twGen i ζ := by
  intro q _ i X _ ζ y
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y
  have hpts := (loc_iff_etale_affine_points X (fun V g => S.arrows g)
    (fun V W g k h => S.downward_closed h k)).1 ⟨S, hS, fun _ _ h => h⟩
  choose V g hA hE hx hS' using hpts
  choose c hc using fun x => hP (V x) (g x) (hS' x)
  have hlc : IsLocallyConstant (fun x => c x % q) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    haveI := hE x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, ?_⟩
    rintro x' ⟨v, hv⟩
    obtain ⟨v', hv'⟩ := hx x'
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g x) (g := g x') v v' (hv.trans hv'.symm)
    haveI : Nonempty ↥(pullback (g x) (g x')) := ⟨z⟩
    have e1 := congrArg (Sec.res (pullback.fst (g x) (g x'))) (hc x)
    have e2 := congrArg (Sec.res (pullback.snd (g x) (g x'))) (hc x')
    rw [← res_comp, res_nsmul, res_gen] at e1 e2
    rw [pullback.condition] at e1
    exact (mod_eq_of_nsmul_eq _ (e1.symm.trans e2)).symm
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  have hconst : ∀ x, c x % q = c x0 % q := fun x => hlc.apply_eq_of_preconnectedSpace x x0
  refine ⟨c x0, (_root_.GlobalTheory.EtC.sec_ext_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X _ ?_).2 fun x => ⟨V x, g x, hA x, hE x, hx x, ?_⟩
  · intro V W g k h
    rw [res_comp, res_comp, h]
  · rw [hc, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1, tw_nsmul_mod, hconst x, ← tw_nsmul_mod]
end

