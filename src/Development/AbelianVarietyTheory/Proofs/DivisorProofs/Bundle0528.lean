module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCurvatureClosednessRelationsAdd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AbCoh.rel_add : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), (∀ (x x' : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x' y' w' → DRel F (x + x') (Fin.append y y') (Fin.append w w')) ∧ (∀ (x x' : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ObRel F x u v → ObRel F x' u' v' → ObRel F (x + x') (Fin.append u u') (Fin.append v v')) ∧ ∀ (w w' : Glob1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ClRel F w u v → ClRel F w' u' v' → ClRel F (w + w') (Fin.append u u') (Fin.append v v') := by
  intro R _ C _ F
  have hw : ∀ {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) (T : C),
      wsum F (Fin.append u u') (Fin.append v v') T = wsum F u v T + wsum F u' v' T := by
    intro n n' u v u' v' T
    simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  refine ⟨?_, ?_, ?_⟩
  · rintro x x' n n' y w y' w' ⟨f, g, ω, hf, hg, he⟩ ⟨f', g', ω', hf', hg', he'⟩
    refine ⟨f + f', Fin.append g g', ω + ω', by rw [map_add (f := _), hf, hf'], ?_, ?_⟩
    · intro k
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) k
      · simp only [Fin.append_left]; exact hg i
      · simp only [Fin.append_right]; exact hg' i
    · intro T T' φ
      have e1 := he φ
      have e2 := he' φ
      simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Submodule.coe_add, Pi.add_apply, map_add (f := _)]
      rw [e1, e2]; abel
  · rintro x x' n n' u v u' v' ⟨f, ω, hf, hc, hd⟩ ⟨f', ω', hf', hc', hd'⟩
    refine ⟨f + f', ω + ω', by rw [map_add (f := _), hf, hf'], ?_, ?_⟩
    · intro T T' φ
      simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
      rw [hc φ, hc' φ]; abel
    · intro T
      simp only [Pi.add_apply, map_add (f := _), hw, hd T, hd' T]
  · intro w w' n n' u v u' v' h h' T
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), hw, h T, h' T]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

def rsub {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
  aeval fun v => ∑ w, C (M w v) * X w

theorem rsub_X {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) (v : σ) :
    rsub M (X v) = ∑ w, C (M w v) * X w := aeval_X _ _

variable {ι : Type}

open Classical in
def frameMat {d a : ℕ} (x₀ : Var ι d a → ℂ) : Matrix (ι × Fin a × Fin a) (Var ι d a) ℂ :=
  by
    classical
    exact fun w v => if w.1 = v.1 ∧ w.2.2 = v.2.2 then x₀ (v.1, v.2.1, w.2.1) else 0

def detG [Fintype ι] (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_detG [Fintype ι] (a : ℕ) (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (detG a n) = detChar n g := by
  unfold detG detChar
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem detG_ne_zero [Fintype ι] (a : ℕ) (n : ι → ℕ) : detG (ι := ι) a n ≠ 0 := by
  intro h
  have := eval_detG (ι := ι) a n (fun _ => 1)
  rw [h, map_zero] at this
  simp [detChar] at this

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameFunctionCompare
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFg

theorem ev_finset_sum {R : Type} [CommRing R] {S : Spc} {I : Cx R} {n : ℤ} {ι : Type} [DecidableEq ι] (s : Finset ι)
    (c : ι → Cochain ((chains R).obj S) I n) (p : ℕ) (t : ℤ) (h : -(p : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S p U) :
    ev (∑ j ∈ s, c j) p t h U x = ∑ j ∈ s, ev (c j) p t h U x := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ev_add, ih]

theorem col_identity (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (a : ℕ) (n m : ℤ) (hnm : n + -(a : ℤ) = m)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (c : ∀ j : Fin N, Cochain (sgl (((chains (ZMod q)).obj E).X (-(a : ℤ)))) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (m - 2 * ((j : ℕ) : ℤ)))
    (ha : ∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X (-(a : ℤ))) ≫ (c j).v 0 r hr = (α j).v (-(a : ℤ)) r hr')
    (β : Cochain ((biChains (ZMod q) (twX E V)).X (-(a : ℤ))) (res _ (tw q i)) m)
    (hb : ∀ (k t : ℤ) (h : -(a : ℤ) + k = t) r hr hr', β.v k r hr =
      (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) k t h ≫ (phi q V ℓ i z n α).v t r hr')
    (γ : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a)))) (res _ (tw q i)) m)
    (hγ : ∀ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).IsAW (sub_add_cancel m _)
      ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
        ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _))
      ((Cochain.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))).comp (z j) (zero_add _)) (γ j)) :
    (Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j) (zero_add m) = β := by
  ext k r hkr : 1
  by_cases hk : k ≤ 0
  · obtain ⟨b', rfl⟩ : ∃ b' : ℕ, k = -(b' : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [← cancel_epi (biChainsXIso (ZMod q) (twX E V) a b').inv]
    refine free_ext _ _ fun U y => ?_
    have e1 : Sec.map ((biChainsXIso (ZMod q) (twX E V) a b').inv ≫
        ((Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j) (zero_add m)).v (-(b' : ℤ)) r hkr)
        (freeGen (ZMod q) _ U y) = ev (∑ j, γ j) b' r hkr U y := by
      rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% colCx_f]
      rfl
    have e2 : Sec.map ((biChainsXIso (ZMod q) (twX E V) a b').inv ≫ β.v (-(b' : ℤ)) r hkr) (freeGen (ZMod q) _ U y) =
        evT (phi q V ℓ i z n α) a b' r (by push_cast; omega) U y := by
      rw [hb (-(b' : ℤ)) (-((a + b' : ℕ) : ℤ)) (by push_cast; ring) r hkr (by push_cast; omega)]
      rfl
    rw [e1, e2, ev_finset_sum, GlobalTheory.T.projectiveBundleCochain_apply_bisimplex]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hA : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + (m - 2 * ((j : ℕ) : ℤ)) = t) (U' : Scheme.{0})
        (x : Sx ((twX E V).obj (op (SimplexCategory.mk a))) s U'), 0 < s →
        ev ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
          ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _)) s t h U' x = 0 := by
      intro s t h U' x hs
      erw [ev_pull]
      exact ev_prE_pos _ E a (c j) s t h U' _ hs
    rw [GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel m _) _ _ (γ j) (hγ j) hA b' r hkr U y]
    have hAv : ∀ (h0 : -((0 : ℕ) : ℤ) + (m - 2 * ((j : ℕ) : ℤ)) = m - 2 * ((j : ℕ) : ℤ)) (h00 : 0 + 0 ≤ b'),
        EtC.ev ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
          ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _)) 0 (m - 2 * ((j : ℕ) : ℤ)) h0 U
          (Sx.sub (E := (twX E V).obj (op (SimplexCategory.mk a))) y 0 0 h00) =
        Sec.map ((chainsXIso (ZMod q) E a).inv ≫ sglι _ ≫ (c j).v 0 (m - 2 * ((j : ℕ) : ℤ)) (by simpa using h0))
          (freeGen (ZMod q) _ U (baseS V y)) := fun h0 h00 =>
      (ev_pull (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N))
        ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) 0 _ h0 U
        (Sx.sub (E := (twX E V).obj (op (SimplexCategory.mk a))) y 0 0 h00)).trans
        (ev_prE_zero _ E a (c j) _ h0 U _)
    have hZv : ∀ (h2 : -(b' : ℤ) + 2 * ((j : ℕ) : ℤ) = -(b' : ℤ) + 2 * ((j : ℕ) : ℤ)),
        EtC.ev ((Cochain.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))).comp (z j) (zero_add _)) b'
          (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) h2 U y = EtC.ev (z j) b' _ rfl U (vertS V ℓ y) := fun h2 =>
      ev_pull (ℓ.app (op (SimplexCategory.mk a))) (z j) b' _ h2 U y
    refine (congrArg₂ (fun u v => (twPairI q i ((j : ℕ) : ℤ)).mul U (m - 2 * ((j : ℕ) : ℤ))
      (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r (by omega) u v) (hAv _ _) (hZv _)).trans ?_
    have key : ∀ (s : ℤ) (hs : -(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ)) = s) (h0 : 0 + (m - 2 * ((j : ℕ) : ℤ)) = s)
        (h1 : s + (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) = r),
        (twPairI q i ((j : ℕ) : ℤ)).mul U s (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r h1
          (Sec.map ((chainsXIso (ZMod q) E a).inv ≫ sglι _ ≫ (c j).v 0 s h0) (freeGen (ZMod q) _ U (baseS V y)))
          (ev (z j) b' _ rfl U (vertS V ℓ y)) =
        (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r
          (by omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b' _ rfl U (vertS V ℓ y)) := by
      intro s hs
      subst hs
      intro h0 h1
      rw [ha j _ h0 (by omega)]
      rfl
    exact key _ (by omega) _ _
  · exact (biChains_isZero (twX E V) (-(a : ℤ)) k (Or.inr (by omega))).eq_of_src _ _

theorem graded_bijective : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  intro q _ E N V hE B ℓ i z hz hD p hp
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a : ℤ) := ⟨(-p).toNat, by omega⟩
  set P : PSh := E.obj (op (SimplexCategory.mk a)) with hPdef
  have hP : Inv q (disc.obj P) := fun U ⟨x⟩ =>
    hE U ⟨(E.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk a) 0).op).app (op U) x⟩
  have hpbf := hD P (trivV N (disc.obj P)) hP
  have hpi : ∀ m, Function.Bijective (fun (x : ∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X (-(a : ℤ))))
      (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (j : Fin N) => cpull (prE _ E a) _ _ (x j)) := by
    intro m
    have hb := fun (j : Fin N) => LevelCmp.cpull_bij_of_heq (prEquiv (ZMod q) E a) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (m - 2 * ((j : ℕ) : ℤ))
    refine ⟨fun x y hxy => funext fun j => (hb j).1 (congrFun hxy j), fun y => ?_⟩
    exact ⟨fun j => ((hb j).2 (y j)).choose, funext fun j => ((hb j).2 (y j)).choose_spec⟩
  refine ⟨fun m x => cpull (colCx _ (twX E V) a).hom _ m (pull _ (colIso P (trivV N (disc.obj P))).hom _ m
    (pbfMap q (trivV N (disc.obj P)) m i (fun j => cpull (prE _ E a) _ _ (x j)))), fun m => ?_, ?_⟩
  · exact (LevelCmp.cpull_bij_of_heq (HomotopyEquiv.ofIso (colCx _ (twX E V) a)) _ m).comp
      ((LevelCmp.cpull_bij_of_heq (HomotopyEquiv.ofIso ((chains (ZMod q)).mapIso (colIso P (trivV N (disc.obj P))))) _ m).comp
        ((hpbf m i).comp (hpi m)))
  · intro n m hnm α hα ac b ha hb
    let A : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a))))
        (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ)) := fun j =>
      zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ptimes.fst P (Fib N))))
        (zcomp (Cocycle.ofHom (prE _ E a)) (ac j) (zero_add _)) (zero_add _)
    let Z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a))))
        (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)) := fun j =>
      zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)
    choose γ hγ using fun j : Fin N => Pair.aw_exists (twPairI q i ((j : ℕ) : ℤ)) ((twX E V).obj (op (SimplexCategory.mk a)))
      (sub_add_cancel m (2 * ((j : ℕ) : ℤ))) (A j) (Z j)
    have hterm : ∀ j : Fin N, ((cup q (pull _ (ptimes.fst P (Fib N)) _ _
        (cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j))))
        (cpow q (c1 q (ptimes.snd P (Fib N) ≫ Fib.line N)) j)).cast (by ring) (by ring) : Ht q (ptimes P (Fib N)) m i) =
        CohomologyClass.mk (γ j) := by
      intro j
      rw [← hz a j]
      exact GlobalTheory.T.cupProduct_cast_mk_of_isAlexanderWhitney q i j m (A j) (Z j) (γ j) (hγ j)
    change cpull _ _ m (pull _ _ _ m (pbfMap q (trivV N (disc.obj P)) m i
      (fun j => cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j))))) = _
    have h1 := pull_colIso_pbfMap q P (trivV N (disc.obj P)) hP m i
      (fun j => cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j)))
    erw [h1]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    erw [mk_sum_cocycle]
    change CohomologyClass.mk (zcomp _ _ _) = _
    congr 1
    apply Cocycle.ext
    change (Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j).1 (zero_add m) = b.1
    have hsum : ∀ s : Finset (Fin N), (∑ j ∈ s, γ j).1 = ∑ j ∈ s, (γ j).1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | @insert j s hj ih => simp only [Finset.sum_insert hj, Cocycle.coe_add, ih]
    rw [hsum]
    exact col_identity q V ℓ i (fun j => (z j).1) a n m hnm α (fun j => (ac j).1) ha b.1 hb (fun j => (γ j).1) hγ

end GlobalTheory.PBFg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvariance
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem SemiMap.sub_op {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ ρ' : SemiMap I J)
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (ρ.sub ρ').op.app E n x = ρ.op.app E n x - ρ'.op.app E n x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ').1 E n α
  have hsub : (ρ.sub ρ').IsImage α.1 (β - β').1 := by
    intro p s h U x
    rw [show (β - β').1 = β.1 - β'.1 from rfl, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 β.1 β'.1 p s h U x).2.1, hβ p s h U x,
      hβ' p s h U x]
    rfl
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R _).2 E n α _ hsub, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ,
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ').2 E n α β' hβ', CohomologyClass.mk_sub]

theorem a8 : A8 := by
  intro R S _ _ φ E F n
  obtain ⟨ρ₀, h₀, hb⟩ := GlobalTheory.T.restrictScalars_resolution_comparison R S φ F
  have hz := GlobalTheory.T.semilinearResolutionMap_cohomology_eq_zero_of_kill S R F ((restr φ).obj F) ((restrMap φ F).sub ρ₀) (fun U a => by
    change (restrMap φ F).app U 0 _ - ρ₀.app U 0 _ = 0
    rw [GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec R S φ F U a, h₀ U a, sub_self])
  have he : restrH φ E F n = ρ₀.op.app E n := by
    ext x
    have := hz E n x
    rw [SemiMap.sub_op] at this
    exact sub_eq_zero.mp this
  rw [he]
  exact hb E n

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhd
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem Hens.of_injective_of_nbhd (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    Function.Injective (Hens.of i) := by
  have : IsDirected (EtNbhd R) (· ≤ ·) := _root_.GlobalTheory.Henselisation.etNbhd_isDirected R
  have : DirectedSystem (fun j : EtNbhd R => j.B) (fun _ _ h => ⇑(EtNbhd.trans h)) :=
    ⟨fun j x => (_root_.GlobalTheory.Henselisation.trans_system R).1 j x,
      fun k j l hlj hjk x => (_root_.GlobalTheory.Henselisation.trans_system R).2 l j k hlj hjk x⟩
  exact Ring.DirectLimit.of_injective (G := fun j : EtNbhd R => j.B) (fun _ _ h => EtNbhd.trans h)
    (fun _ _ h => (_root_.GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective R _ _ h).2) i

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSurjectiveSectionOfSH
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_surjective_section_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f →
      ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  intro A _ hA Y f hf hs
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  obtain ⟨y, hy⟩ := f.surjective (IsLocalRing.closedPoint A)
  let 𝒰 := Y.affineOpenCover
  let i := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  let g : Spec (𝒰.X i) ⟶ Spec (CommRingCat.of A) := 𝒰.f i ≫ f
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  haveI : Etale g := inferInstance
  let φ : CommRingCat.of A ⟶ 𝒰.X i := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hEt : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  letI : Algebra A (𝒰.X i) := φ.hom.toAlgebra
  haveI : Algebra.Etale A (𝒰.X i) := hEt
  have hq : z.asIdeal.comap (algebraMap A (𝒰.X i)) = IsLocalRing.maximalIdeal A := by
    have h1 : (Spec.map φ).base z = IsLocalRing.closedPoint A := by
      rw [hφ]; show f.base ((𝒰.f i).base z) = _; rw [hz, hy]
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    exact h2
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨hH, hsep⟩ (𝒰.X i) z.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ 𝒰.f i, ?_⟩
  rw [Category.assoc]
  change Spec.map (CommRingCat.ofHom s.toRingHom) ≫ g = _
  rw [← hφ, ← Spec.map_comp]
  have : φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _ := by
    ext a
    exact s.commutes a
  exact (congrArg Spec.map this).trans (Spec.map_id _)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalBasePtTopMinors
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RowIrr

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def basePt (ι : Type) (d a : ℕ) : Var ι d a → ℂ := fun y => if (y.2.1 : ℕ) = (y.2.2 : ℕ) then 1 else 0

def lowScal (d a : ℕ) (t : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else t

def topRows {a d : ℕ} (h : a ≤ d) : {s : Fin a → Fin d // StrictMono s} :=
  ⟨Fin.castLE h, Fin.strictMono_castLE h⟩

def topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : Pol ι d a :=
  prodMinors (ι := ι) (n := n) (fun _ _ => topRows h)

theorem eval_rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (rowSub κ P) = eval (fun y => ∑ i' : Fin d, κ y.1 i' y.2.1 * z (y.1, i', y.2.2)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rowSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp => simp [rowSub, hp] at *

theorem eval_colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (colSub g P) = eval (fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * z (y.1, y.2.1, j')) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp => simp [colSub, hp] at *

theorem rowSub_rowSub {d a : ℕ} (κ κ' : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rowSub κ (rowSub κ' P) = rowSub (fun τ => κ τ * κ' τ) P := by
  have : (rowSub κ).comp (rowSub κ') = (rowSub (fun τ => κ τ * κ' τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) := by
    apply MvPolynomial.algHom_ext
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rowSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul, C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_one {d a : ℕ} (P : Pol ι d a) : rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) P = P := by
  have : (rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [rowSub, aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single y.2.1]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem eval_basePt_topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : eval (basePt ι d a) (topMinors h n) = 1 := by
  simp only [topMinors, prodMinors, minorAt, map_prod, RingHom.map_det]
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => ?_
  have : (RingHom.mapMatrix (eval (basePt ι d a)))
      (Matrix.of fun i i' : Fin a => (X (τ, (topRows h).1 i, i') : Pol ι d a)) = 1 := by
    ext i i'
    simp [basePt, topRows, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]

theorem topMinors_ne_zero {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : topMinors (ι := ι) h n ≠ 0 := by
  intro h0
  have := eval_basePt_topMinors (ι := ι) h n
  rw [h0, map_zero] at this
  exact zero_ne_one this

end GlobalTheory.MinorFrame.RowIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCohomologyDerivativeRelationOfFrame
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem dRel_of_frame_exists (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    HasFrame F → ∀ x : GlobalTheory.CatCoh.H1 F, ∃ (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w := by
  rintro ⟨n, ⟨fr⟩⟩ x
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F x
  let g : Fin n → Z1 F := fun i ↦ ⟨fun T T' φ ↦ fr.δ i T' (D R (F.obj T') (f.1 T T' φ)), by
    intro T T' T'' φ ψ
    simp only
    rw [Z1.comp f φ ψ, map_add (f := _), map_add (f := _), ← p1_D, fr.nat]⟩
  refine ⟨n, fun i ↦ GlobalTheory.CatCoh.H1.mk F (g i), fr.w, f, g, 0, rfl, fun _ ↦ rfl, ?_⟩
  intro T T' φ
  simp only [Pi.zero_apply, map_zero, sub_zero, add_zero]
  exact fr.sum T' _

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubGoodIdempotentEqBadTupleSumsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_goodIdempotent_eq_badTupleSums : ∀ (D : D7), ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ 1 - D.ntypes.e0 = badElt D 0 (S 0) + badElt D 1 (S 1) - badElt D 0 (S 0) * badElt D 1 (S 1) := by
  first | exact @GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums | exact GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums | (intros; apply GlobalTheory.BadCount.one_sub_goodTypeIdempotent_eq_badTupleSums <;> assumption)
end

