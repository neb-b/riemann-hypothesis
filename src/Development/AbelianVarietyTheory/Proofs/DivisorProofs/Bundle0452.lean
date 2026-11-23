module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimplicialCochainRepresentingClassAcyclicL
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.LeraySurj

variable {R : Type} [CommRing R]

theorem chains_d_eq (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
  rw [← h2]
  exact HomologicalComplex.extend_d_eq _ _ rfl rfl

theorem cobd_eq (E : Spc) {F : Shv R} (n : ℕ) (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    cobd s = (chainsXIso R E (n + 1)).inv ≫ ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ s := by
  rw [chains_d_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Preadditive.sum_comp, Preadditive.zsmul_comp]
  rfl

theorem step (E : Spc) (F : Shv R) {n : ℤ} (z : Cocycle ((chains R).obj E) (res R F) n) (k : ℕ)
    (hv : ∀ p q (hpq : p + n = q), -(k : ℤ) < p → z.1.v p q hpq = 0)
    (hex : ∀ t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X (n - k), t ≫ (res R F).d (n - k) (n - k + 1) = 0 →
      ∃ y : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X (n - k - 1), t = y ≫ (res R F).d (n - k - 1) (n - k)) :
    ∃ z' : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z' = CohomologyClass.mk z ∧
      ∀ p q (hpq : p + n = q), -((k + 1 : ℕ) : ℤ) < p → z'.1.v p q hpq = 0 := by
  have hcl : z.1.v (-(k : ℤ)) (n - k) (by omega) ≫ (res R F).d (n - k) (n - k + 1) = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) (-(k : ℤ)) (n - k + 1) (by omega)
    rw [δ_v n (n + 1) rfl _ _ _ _ (n - k) (-(k : ℤ) + 1) (by omega) rfl,
      hv (-(k : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨y, hy⟩ := hex ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) (by omega))
    (by rw [Category.assoc, hcl, Limits.comp_zero])
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.single (p := -(k : ℤ)) (q := n - k - 1) ((chainsXIso R E k).hom ≫ y) (n - 1)
  let c : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p q hpq hp
    have hβ1 : β.v (p + 1) q (by omega) = 0 := Cochain.single_v_eq_zero _ _ _ _ _ (by omega)
    have hc : c.1.v p q hpq = β.v p (q - 1) (by omega) ≫ (res R F).d (q - 1) q := by
      change (δ (n - 1) n β).v p q hpq = _
      rw [δ_v (n - 1) n (by omega) _ _ _ _ (q - 1) (p + 1) rfl rfl, hβ1]
      simp
    rw [Cocycle.coe_sub, Cochain.sub_v, hc]
    rcases lt_or_eq_of_le (show -(k : ℤ) ≤ p by omega) with h | h
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = n - k := by omega
      rw [Cochain.single_v]
      have hz : z.1.v (-(k : ℤ)) (n - k) hpq = (chainsXIso R E k).hom ≫ ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) hpq) := by
        rw [Iso.hom_inv_id_assoc]
      rw [hz, hy]
      simp

theorem exact_of_vanish (F : Shv R) (P : PSh) (m : ℤ) (h0 : ∀ y : H R (disc.obj P) F m, y = 0)
    (t : (free R).obj P ⟶ (res R F).X m) (ht : t ≫ (res R F).d m (m + 1) = 0) :
    ∃ y : (free R).obj P ⟶ (res R F).X (m - 1), t = y ≫ (res R F).d (m - 1) m := by
  obtain ⟨cl, -, hinj, hzero, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  have h : cl P m t ht = cl P m 0 Limits.zero_comp := by rw [hzero]; exact h0 _
  obtain ⟨y, hy⟩ := (hinj P m t ht 0 Limits.zero_comp).1 h
  exact ⟨y, by rw [hy, zero_add]⟩

theorem reduce (F : Shv R) (E : Spc) (n : ℕ)
    (hyp : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (x : H R E F n) (j : ℕ) (hj : j ≤ n) :
    ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(j : ℤ) < p → z.1.v p q hpq = 0 := by
  induction j with
  | zero =>
    obtain ⟨z, rfl⟩ := x.mk_surjective
    refine ⟨z, rfl, fun p q hpq hp => ?_⟩
    exact ((_root_.GlobalTheory.EtC.res_basic R F).2.2.2.2.2 E p (by omega)).eq_of_src _ _
  | succ j ih =>
    obtain ⟨z, hz, hv⟩ := ih (by omega)
    obtain ⟨z', hz', hv'⟩ := step E F z j hv (fun t ht => by
      have hm : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
      have h0 := hyp j (n - j) (by omega) (by omega)
      rw [hm] at h0
      have := exact_of_vanish F _ ((n : ℤ) - j) h0 t ht
      exact this)
    exact ⟨z', hz'.trans hz, hv'⟩

theorem main (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ)
    (hyp : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (x : H R E F n) : ∃ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 ∧ IsCls s x := by
  obtain ⟨z, rfl, hv⟩ := reduce F E n hyp x n le_rfl
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, -⟩ := _root_.GlobalTheory.EtC.res_basic R F
  have hcl : z.1.v (-(n : ℤ)) 0 (by omega) ≫ (res R F).d 0 1 = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-(n : ℤ)) 1 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ 0 (-(n : ℤ) + 1) (by omega) rfl,
      hv (-(n : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨u, hu⟩ := hex.lift' ((chainsXIso R E n).inv ≫ z.1.v (-(n : ℤ)) 0 (by omega))
    (by change _ ≫ (res R F).d 0 1 = 0; rw [Category.assoc, hcl, Limits.comp_zero])
  change u ≫ resι R F = _ at hu
  have hz : z.1.v (-(n : ℤ)) 0 (by omega) = (chainsXIso R E n).hom ≫ u ≫ resι R F := by
    rw [hu, Iso.hom_inv_id_assoc]
  refine ⟨u, ?_, z, rfl, ?_⟩
  · rw [cobd_eq]
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (-1) (-(n : ℤ)) (by omega) (by omega), hz,
      (hneg (-1) (by omega)).eq_of_tgt (z.1.v _ (-1) _) 0] at h
    simp only [Limits.zero_comp, zero_add, Cochain.zero_v] at h
    have h' := (smul_eq_zero_iff_eq _).1 h
    have h'' : (((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ u) ≫ resι R F =
        0 ≫ resι R F := by
      simpa [Category.assoc] using h'
    rw [cancel_mono] at h''
    rw [h'', Limits.comp_zero]
  · refine Cochain.ext _ _ (fun p q hpq => ?_)
    rcases lt_trichotomy p (-(n : ℤ)) with h | h | h
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · subst h
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hz]
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]

end GlobalTheory.EtC.LeraySurj

theorem GlobalTheory.EtC.leray_surj : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) → ∀ x : H R E F n, ∃ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 ∧ IsCls s x :=
  fun R _ F E n hyp x => GlobalTheory.EtC.LeraySurj.main R F E n hyp x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFiniteEtaleGaloisCoverLadic
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TrGal

open GlobalTheory.EtC.Tr GlobalTheory.EtC.TrDeg

variable (R : Type) [CommRing R]

theorem splitBy_of_equiv {Y X V : Scheme.{0}} (f : Y ⟶ X) (y : V ⟶ X) {G : Type} {m : ℕ} (e : Fin m ≃ G)
    (a : G → (V ⟶ Y)) (ha : ∀ g, a g ≫ f = y)
    (h : IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 V) (by rw [ha g, Category.id_comp])) :
      ∐ (fun _ : G => V) ⟶ pullback f y)) : SplitBy f y (fun j => a (e j)) := by
  refine ⟨fun j => ha _, ?_⟩
  let w : ∐ (fun _ : Fin m => V) ≅ ∐ (fun _ : G => V) := Sigma.reindex e (fun _ : G => V)
  have hw : ∀ j, Sigma.ι (fun _ : Fin m => V) j ≫ w.hom = Sigma.ι (fun _ : G => V) (e j) := fun j =>
    Sigma.ι_reindex_hom e (fun _ : G => V) j
  convert (inferInstance : IsIso (w.hom ≫ (Sigma.desc (fun g => pullback.lift (a g) (𝟙 V) (by rw [ha g, Category.id_comp])) :
      ∐ (fun _ : G => V) ⟶ pullback f y)))
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_desc, reassoc_of% (hw j), Sigma.ι_desc]

theorem along_sum {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) {ι : Type} (s : Finset ι) (t : ι → (freeSch R X ⟶ freeSch R Y))
    (x : H R (sch.obj Y) F n) : along R F n (∑ j ∈ s, t j) x = ∑ j ∈ s, along R F n (t j) x :=
  map_sum (AddMonoidHom.mk' (fun u : freeSch R X ⟶ freeSch R Y => along R F n u x) (fun u v => along_add R F n u v x)) t s

theorem pull_trH {Y X V : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Y)} (hs : SplitBy f y s) (F : Shv R) (n : ℤ) (x : H R (sch.obj Y) F n) :
    pull R (sch.map y) F n (trH R f F n x) = ∑ j, pull R (sch.map (s j)) F n x := by
  rw [trH, ← along_free, ← along_comp,
    (transfer_spec R (existsUnique_isTransfer R f).exists).apply_of_splitBy R hs, along_sum]
  simp only [along_free]

theorem exists_trace_galois : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, ∃ tr : Hl l (sch.obj Y) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i,
  (∀ x, tr (pullHl l (sch.map f) n i x) = Fintype.card G • x) ∧ ∀ y, pullHl l (sch.map f) n i (tr y) = ∑ g, pullHl l (sch.map (a g)) n i y := by
  intro l _ Y X f _ _ _ G _ a ha hiso n i
  have hs := splitBy_of_equiv f f (Fintype.equivFin G).symm a ha hiso
  have h := trHl_spec l (redCompat_of_finite_etale l f (fun R _ => existsUnique_isTransfer R f) n i)
  refine ⟨trHl l f n i, fun x => Subtype.ext (funext fun k => ?_), fun y => Subtype.ext (funext fun k => ?_)⟩
  · exact (h _ k).trans (trH_pull (ZMod (l ^ k)) f hs (tw (l ^ k) i) n (x.1 k))
  · rw [← Equiv.sum_comp (Fintype.equivFin G).symm, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    exact (congrArg (pull (ZMod (l ^ k)) (sch.map f) (tw (l ^ k) i) n) (h y k)).trans
      (pull_trH (ZMod (l ^ k)) f hs (tw (l ^ k) i) n (y.1 k))

end GlobalTheory.EtC.TrGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLieBasis
section
open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem suLie_finrank_ge : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, (e i).trace = 0 ∧ ∀ x y, herm G (e i *ᵥ x) y + herm G x (e i *ᵥ y) = 0) ∧
      LinearIndependent (maximalRealSubfield E) e := by
  intro E _ _ _ r G hG hdet
  let F := maximalRealSubfield E
  have cc_mul : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => map_mul (IsCMField.complexConj E) x y
  have cc_add : ∀ x y : E, cc (x + y) = cc x + cc y := fun x y => map_add (IsCMField.complexConj E) x y
  have cc_cc : ∀ x : E, cc (cc x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have cc_F : ∀ (c : F) (x : E), cc (c • x) = c • cc x := by
    intro c x
    have hc : cc (c : E) = c := (IsCMField.complexConj_eq_self_iff E _).mpr c.2
    show cc ((c : E) * x) = (c : E) * cc x
    rw [cc_mul, hc]
  have hs : ∀ (f : Fin r → E), cc (∑ i, f i) = ∑ i, cc (f i) := fun f => map_sum (IsCMField.complexConj E) f _
  haveI : FiniteDimensional F E :=
    Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)
  have hV : Module.finrank F (Matrix (Fin r) (Fin r) E) = r * r * 2 := by
    rw [Module.finrank_matrix, Algebra.IsQuadraticExtension.finrank_eq_two F E]; simp

  let conjL : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun X => X.map cc
      map_add' := fun X Y => by ext a b; simp [cc_add]
      map_smul' := fun c X => by ext a b; simp [cc_F] }
  let φ : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun X => Xᵀ * G + G * conjL X
      map_add' := fun X Y => by simp only [map_add (f := _), transpose_add, Matrix.add_mul, Matrix.mul_add]; abel
      map_smul' := fun c X => by
        simp only [map_smul, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply, smul_add] }

  let H : Submodule F (Matrix (Fin r) (Fin r) E) :=
    { carrier := {M | ∀ a b, cc (M a b) = M b a}
      add_mem' := fun {M N} hM hN a b => by simp [cc_add, hM a b, hN a b]
      zero_mem' := fun a b => by simp [cc]
      smul_mem' := fun c M hM a b => by simp [cc_F, hM a b] }
  have hφH : LinearMap.range φ ≤ H := by
    rintro _ ⟨X, rfl⟩ a b
    have hφX : φ X = Xᵀ * G + G * X.map cc := rfl
    show cc ((φ X) a b) = (φ X) b a
    rw [hφX]
    simp only [Matrix.add_apply, Matrix.mul_apply, transpose_apply, map_apply, cc_add]
    rw [hs, hs, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp only [cc_mul, cc_cc, hG] <;> ring

  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  have hy' : cc y ≠ y := hy
  set δ : E := y - cc y with hδdef
  have hδ : cc δ = -δ := by rw [hδdef, show cc (y - cc y) = cc y - cc (cc y) from map_sub _ _ _, cc_cc]; ring
  have hδ0 : δ ≠ 0 := fun h => hy' (sub_eq_zero.mp h).symm
  let Dm : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun M => δ • M
      map_add' := fun M N => smul_add δ M N
      map_smul' := fun c M => smul_comm δ c M }
  have hDm : Function.Injective Dm := fun M N h => smul_right_injective _ hδ0 h
  have hinf : H ⊓ H.map Dm = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro M ⟨hM, N, hN, rfl⟩
    have hN0 : ∀ a b, N a b = 0 := by
      intro a b
      have h := hM b a
      change cc (δ * N b a) = δ * N a b at h
      rw [cc_mul, hδ, hN b a] at h
      have : δ * N a b = 0 := by linear_combination (-1/2 : E) * h
      exact (mul_eq_zero.mp this).resolve_left hδ0
    ext a b
    show δ * N a b = 0
    rw [hN0, mul_zero]
  have hHmap : Module.finrank F (H.map Dm) = Module.finrank F H :=
    (Submodule.equivMapOfInjective Dm hDm H).finrank_eq.symm
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := Submodule.finrank_mono hφH
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq H (H.map Dm)
  have h4 := Submodule.finrank_le (H ⊔ H.map Dm)
  rw [hinf, finrank_bot] at h3
  have hK : r * r ≤ Module.finrank F (LinearMap.ker φ) := by omega

  let t : Matrix (Fin r) (Fin r) E →ₗ[F] E := Matrix.traceLinearMap (Fin r) F E
  let f := t.domRestrict (LinearMap.ker φ)
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hf : LinearMap.range f ≤ Submodule.span F {δ} := by
    rintro _ ⟨⟨X, hX⟩, rfl⟩
    have hX' : Xᵀ * G + G * X.map cc = 0 := hX
    have hbar : X.map cc = -(G⁻¹ * (Xᵀ * G)) := by
      have : G * X.map cc = -(Xᵀ * G) := eq_neg_of_add_eq_zero_right hX'
      calc X.map cc = G⁻¹ * (G * X.map cc) := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hu, Matrix.one_mul]
        _ = -(G⁻¹ * (Xᵀ * G)) := by rw [this, Matrix.mul_neg]
    have htr : cc X.trace = -X.trace := by
      have e1 : (X.map cc).trace = cc X.trace := by
        simp only [Matrix.trace, Matrix.diag, map_apply]; exact (hs _).symm
      rw [← e1, hbar, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv G hu, Matrix.mul_one, Matrix.trace_transpose]
    have hz : cc (X.trace / δ) = X.trace / δ := by
      rw [show cc (X.trace / δ) = cc X.trace / cc δ from map_div₀ (IsCMField.complexConj E) _ _, htr, hδ,
        neg_div_neg_eq]
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨X.trace / δ, (IsCMField.complexConj_eq_self_iff E _).mp hz⟩, ?_⟩
    show X.trace / δ * δ = X.trace
    exact div_mul_cancel₀ _ hδ0

  have hv : ∀ u v : Fin r → E, herm G u v = u ⬝ᵥ (G *ᵥ fun b => cc (v b)) := by
    intro u v
    simp only [herm, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hcv : ∀ (X : Matrix (Fin r) (Fin r) E) (y : Fin r → E),
      (fun b => cc ((X *ᵥ y) b)) = X.map cc *ᵥ fun b => cc (y b) := by
    intro X y; ext b
    simp only [mulVec, dotProduct, map_apply]
    exact (hs _).trans (Finset.sum_congr rfl fun c _ => cc_mul _ _)
  have skew : ∀ X : Matrix (Fin r) (Fin r) E, Xᵀ * G + G * X.map cc = 0 →
      ∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0 := by
    intro X hX x y
    rw [hv, hv, hcv, ← vecMul_transpose X x, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
      ← dotProduct_add, ← add_mulVec, hX, zero_mulVec, dotProduct_zero]

  have h5 := LinearMap.finrank_range_add_finrank_ker f
  have h6 := (Submodule.finrank_mono hf).trans (finrank_span_singleton hδ0).le
  have hle : r ^ 2 - 1 ≤ Module.finrank F (LinearMap.ker f) := by rw [sq]; omega
  let b := Module.finBasis F (LinearMap.ker f)
  let g : LinearMap.ker f →ₗ[F] Matrix (Fin r) (Fin r) E :=
    (LinearMap.ker φ).subtype ∘ₗ (LinearMap.ker f).subtype
  have hg : LinearMap.ker g = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Subtype.val_injective.comp Subtype.val_injective)
  refine ⟨fun i => g (b (Fin.castLE hle i)), fun i => ?_,
    (b.linearIndependent.comp _ (Fin.castLE_injective hle)).map' g hg⟩
  have hx1 : f (b (Fin.castLE hle i)).1 = 0 := (b (Fin.castLE hle i)).2
  have hx2 : φ (b (Fin.castLE hle i)).1.1 = 0 := (b (Fin.castLE hle i)).1.2
  exact ⟨hx1, skew _ hx2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimit
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem faithfullyFlat_of_split : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Projective R D →
    (∃ τ : D →ₗ[R] R, τ 1 = 1) → Module.FaithfullyFlat R D := by
  intro R D _ _ _ hP ⟨τ, hτ⟩
  haveI : Module.Flat R D := inferInstance
  refine ⟨fun m hm h => ?_⟩
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by rw [h]; exact Submodule.mem_top
  have h2 : ∀ x ∈ m • (⊤ : Submodule R D), τ x ∈ m := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr d _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, smul_eq_mul]; exact m.mul_mem_right _ hr
    · rw [map_add (f := _)]; exact m.add_mem hx hy
  have := h2 1 h1
  rw [hτ] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)

theorem isZModTorsor_of_algEquiv : ∀ (R D D' : Type) [CommRing R] [CommRing D] [CommRing D'] [Algebra R D] [Algebra R D'] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[R] D)) (act' : Multiplicative (ZMod q) →* (D' ≃ₐ[R] D'))
    (e : D ≃ₐ[R] D'), (∀ (g : Multiplicative (ZMod q)) (x : D), e (act g x) = act' g (e x)) →
    GlobalTheory.LocAcyc.IsZModTorsor R D q act → GlobalTheory.LocAcyc.IsZModTorsor R D' q act' := by
  intro R D D' _ _ _ _ _ q act act' e he hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  have el : D ≃ₗ[R] D' := e.toLinearEquiv
  refine ⟨Module.Finite.equiv el, Module.Projective.of_equiv el, ?_, ?_⟩
  · exact Module.FaithfullyFlat.of_linearEquiv R D el.symm
  · let eT : D ⊗[R] D ≃ₐ[R] D' ⊗[R] D' := Algebra.TensorProduct.congr e e
    let eP : (Multiplicative (ZMod q) → D) ≃ₐ[R] (Multiplicative (ZMod q) → D') :=
      AlgEquiv.piCongrRight (fun _ => e)
    have key : ∀ x, GlobalTheory.TorsorColim.prodMapOf R D' q act' (eT x) = eP (GlobalTheory.TorsorColim.prodMapOf R D q act x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        funext g
        simp [eT, eP, he]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    have hb : Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D q act) := h4
    have : ⇑(GlobalTheory.TorsorColim.prodMapOf R D' q act') = eP ∘ (GlobalTheory.TorsorColim.prodMapOf R D q act) ∘ eT.symm := by
      funext y
      simp only [Function.comp_apply]
      rw [← key, AlgEquiv.apply_symm_apply]
    change Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D' q act')
    rw [this]
    exact eP.bijective.comp (hb.comp eT.symm.bijective)

theorem exists_torsor_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc q hq D _ _ act hD
  haveI : Module.Finite c.pt D := hD.1
  haveI : Module.Projective c.pt D := hD.2.1
  haveI : Module.FinitePresentation c.pt D := Module.finitePresentation_of_projective c.pt D
  obtain ⟨j, A, _, _, _, he0⟩ := GlobalTheory.T.exists_finitePresentation_descent_of_isColimit J F c hc D inferInstance
  obtain ⟨k, B, _, _, _, actB, e, he⟩ := GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered J F c hc q hq j A D act he0
  letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra
  have hT : GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj k] B) q
      (GlobalTheory.TorsorColim.bcAct c.pt actB) := by
    refine GlobalTheory.TorsorColim.isZModTorsor_of_algEquiv c.pt D _ q act _ e.symm (fun g y => ?_) hD
    apply e.injective
    rw [he, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have h1 := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc k B hT.1
  have h2 := GlobalTheory.T.projective_eventually_filteredColimit_algebra J F c hc k B ⟨hT.1, hT.2.1⟩
  have h3 := GlobalTheory.T.exists_late_split_of_filteredColimit J F c hc k B ⟨hT.1, GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat _ _ hT.1 hT.2.1 hT.2.2.1⟩
  have h4 := GlobalTheory.T.eventually_zmodTorsorGaloisProductMap_bijective_colimit J F c hc q hq k B actB hT
  have h34 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; ∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h3 h4
  have h234 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h2 h34
  obtain ⟨m, f₀, hm⟩ := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Finite (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B) ∧ (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h1 h234
  obtain ⟨i1, i2, ⟨τ, hτ⟩, i4⟩ := hm m (𝟙 m)
  refine ⟨m, ?_⟩
  letI : Algebra (F.obj k) (F.obj m) := (F.map (f₀ ≫ 𝟙 m)).hom.toAlgebra
  letI : Algebra (F.obj m) c.pt := (c.ι.app m).hom.toAlgebra
  haveI : IsScalarTower (F.obj k) (F.obj m) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app k).hom x = (c.ι.app m).hom ((F.map (f₀ ≫ 𝟙 m)).hom x)
    rw [← c.w (f₀ ≫ 𝟙 m)]
    rfl)
  exact ⟨F.obj m ⊗[F.obj k] B, inferInstance, inferInstance, GlobalTheory.TorsorColim.bcAct (F.obj m) actB,
    ⟨i1, i2, GlobalTheory.TorsorColim.faithfullyFlat_of_split _ _ i2 ⟨τ, hτ⟩, i4⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange (F.obj k) (F.obj m) c.pt c.pt B).trans e⟩⟩

end GlobalTheory.TorsorColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsTateTwistResolutionHomExtAugmentatiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q)) (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) = Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) → extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  first | (exact @GlobalTheory.EtC.extAug_comp_ext) | (exact GlobalTheory.EtC.extAug_comp_ext) | (intros; apply GlobalTheory.EtC.extAug_comp_ext  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cover_chart_smooth_normal : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → Module.Finite (rA k x I) (integralClosure (rA k x I) K) ∧ IsFractionRing (rB k K x I) K ∧ Algebra.Smooth k (rB k K x I) := by
  first | (exact @GlobalTheory.PD.rB_finite_frac_smooth) | (exact GlobalTheory.PD.rB_finite_frac_smooth) | (intros; apply GlobalTheory.PD.rB_finite_frac_smooth  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocalisationAtElementsTrivSqZeroExtFormsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ), Desc.HasLoc F → Desc.HasLoc (FormExtJ.omjExt F j) := by
  first | exact @GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt | exact GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt | (intros; apply GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ (q : ℕ) (y : DR k K), y ∈ omB k K (rB k K x I) q ↔ ∃ N : ℕ, (algebraMap F K (∏ j ∈ I, x j / x i) ^ N) • y ∈ omB k K (rB k K x {i}) q := by
  first | (exact @GlobalTheory.omB_iff_pow_smul) | (exact GlobalTheory.omB_iff_pow_smul) | (intros; apply GlobalTheory.omB_iff_pow_smul <;> assumption)
end

