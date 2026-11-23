module

public import Development.EtaleCohomology.TateTwists.Bundle0015
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.TateTwists.Bundle0011
public import Development.EtaleCohomology.TateTwists.Bundle0017
public import Development.EtaleCohomology.TateTwists.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0020
public import Development.EtaleCohomology.TateTwists.Bundle0022
public import Development.EtaleCohomology.TateTwists.Bundle0009
public import Development.EtaleCohomology.TateTwists.Bundle0019
public import Development.EtaleCohomology.TateTwists.Bundle0016
public import Development.EtaleCohomology.TateTwists.Bundle0008
public import Development.EtaleCohomology.TateTwists.Bundle0021

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.CcAwFlipPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.cupflip_ev_ext_pf : LateralTheory.EtaleFoundations.cupflip_ev_ext := by
  intro R _ E I n α β hab
  refine Cochain.ext _ _ fun p q hpq => ?_
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    have key : (chainsXIso R E N).inv ≫ α.v _ q hpq = (chainsXIso R E N).inv ≫ β.v _ q hpq := by
      refine (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R _ _).2.1 _ _ fun U x => ?_
      exact hab N q hpq U x
    simpa using congrArg (fun f => (chainsXIso R E N).hom ≫ f) key
  · have := (LateralTheory.Fin.EtaleSimplicialChainsFreeDescription.intersectionNumber_baseChange R).1 E
    have hz : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    exact hz.eq_of_src _ _

namespace LateralTheory.EtaleFoundations

theorem ev_res' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have h3 := (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R (E.obj (op (SimplexCategory.mk p))) (I.X s)).2.2.1 V U g x
  unfold ev
  rw [show Sx.res g x = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← h3]
  have := congrArg (fun f => (ModuleCat.Hom.hom f) (freeGen R (E.obj (op (SimplexCategory.mk p))) U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)
  simpa using this.symm

theorem along_res' {E : Spc} {p N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.along θ).res g = (x.res g).along θ := by
  unfold Sx.along Sx.res
  exact (NatTrans.naturality_apply (E.map θ.op) g.op x).symm

theorem cupflip_eta_mk_pf : cupflip_eta_mk := by
  intro h _ R _ I J K μ E n m k hk α β
  obtain ⟨η, hη⟩ := LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation.intersectionNumber_baseChange R (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ hk α β x s (h N)) (by
      intro N s hs V U g x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [phi, Finsupp.sum, Sec.res, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      unfold phiT
      split_ifs with hw
      · rw [map_zsmul]
        have := μ.nat g _ _ _ (by omega : -(z.1 : ℤ) + n + (-(z.2.1 : ℤ) + m) = s)
          (ev α z.1 _ rfl U (x.along z.2.2.1)) (ev β z.2.1 _ rfl U (x.along z.2.2.2))
        simp only [Sec.res] at this
        have ea := ev_res' α _ _ rfl g (x.along z.2.2.1)
        have eb := ev_res' β _ _ rfl g (x.along z.2.2.2)
        rw [along_res'] at ea eb
        simp only [Sec.res] at ea eb
        rw [this, ea, eb]
      · simp)
  exact ⟨η, fun N s hs U x => hη N s hs U x⟩

end LateralTheory.EtaleFoundations

theorem LateralTheory.EtaleFoundations.cc_aw_flip_of (hst : LateralTheory.EtaleFoundations.cupflip_steen) (hdl : LateralTheory.EtaleFoundations.cupflip_eta_delta) :
    LateralTheory.EtaleFoundations.cc_aw_flip :=
  LateralTheory.EtaleFoundations.cupflip_aw_flip_of hst (LateralTheory.EtaleFoundations.cupflip_homotopy_of LateralTheory.EtaleFoundations.cupflip_ev_ext_pf
    LateralTheory.EtaleFoundations.cupflip_eta_mk_pf hdl)
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipEtaDeltaPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib

namespace LateralTheory.EtaleFoundations.EtaDelta
variable {R : Type} [CommRing R]

theorem along_face {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E M U)
    (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk M) (i : Fin (p + 2)) :
    (x.along a).face i = x.along (SimplexCategory.δ i ≫ a) :=
  along_comp x a (SimplexCategory.δ i)

theorem face_along {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E (M + 1) U) (i : Fin (M + 2))
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk M) :
    (x.face i).along a = x.along (a ≫ SimplexCategory.δ i) :=
  along_comp x (SimplexCategory.δ i) a

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem phi_eq {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) :
    phi μ hk α β x w c = Finsupp.linearCombination ℤ (phiT μ hk α β x w) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem phiT_face {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (i : Fin (M + 2)) (w : ℤ) (z : Pr M) :
    phiT μ hk α β (x.face i) w z =
      phiT μ hk α β x w ⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ i, z.2.2.2 ≫ SimplexCategory.δ i⟩ := by
  simp only [phiT, face_along]

theorem phi_bd {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (w : ℤ) (c : Pr M →₀ ℤ) :
    ∑ i : Fin (M + 2), (-1 : ℤ) ^ (i : ℕ) • phi μ hk α β (x.face i) w c = phi μ hk α β x w (Pr.bd c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [phi_eq, Pr.bd, map_sum, map_zsmul, Pr.push, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact congrArg _ (funext fun z => phiT_face μ hk α β x i w z)

theorem phiT_Fm {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phiT μ hk α β x w ⟨p, r, a, b⟩ = ((m * (p : ℤ)).negOnePow : ℤ) • Fm μ α β U w p r (x.along a) (x.along b) := by
  dsimp only [phiT, Fm]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rw [smul_zero]

end

theorem ev_zero' {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have := ev_sub' (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rwa [sub_self, sub_self] at this

theorem d_ev {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (hst : s + 1 = t) (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s t) (ev α.1 p s hs U y) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q z => if hh : -(q : ℤ) + n = t then ev α.1 q t hh U z else 0) p y := by
  have h := ev_delta_bd (n := n) (m := n + 1) rfl α.1 p s t hs (by omega) U y
  rw [Cocycle.δ_eq_zero, ev_zero', Int.negOnePow_succ, Units.smul_def, Units.val_neg, neg_smul] at h
  exact add_neg_eq_zero.mp h.symm

theorem bd_zero' {E : Spc} {U : Scheme.{0}} {G : Type*} [AddCommGroup G] (p : ℕ) (y : Sx E p U) :
    bd (E := E) (U := U) (fun _ _ => (0 : G)) p y = 0 := by
  cases p <;> simp [bd]

theorem mul_zsmul_left {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h (c • a) b = c • μ.mul U s t w h a b := by
  rw [map_zsmul]; rfl

theorem mul_zsmul_right {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h a (c • b) = c • μ.mul U s t w h a b :=
  map_zsmul _ c b

theorem d_Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cocycle ((chains R).obj E) I n)
    (β : Cocycle ((chains R).obj E) J m) (U : Scheme.{0}) (s t : ℤ) (hst : s + 1 = t) (p r : ℕ)
    (y : Sx E p U) (z : Sx E r U) :
    Sec.map (K.d s t) (Fm μ α.1 β.1 U s p r y z) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q y' => Fm μ α.1 β.1 U t q r y' z) p y +
      ((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) • bd (fun q z' => Fm μ α.1 β.1 U t p q y z') r z := by
  by_cases h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = s
  · have e : Fm μ α.1 β.1 U s p r y z = μ.mul U _ _ s h (ev α.1 p _ rfl U y) (ev β.1 r _ rfl U z) := by
      unfold Fm; rw [dite_eq_left h]
    rw [e, leib' μ U _ _ s (-(p : ℤ) + n + 1) (-(r : ℤ) + m + 1) t h rfl rfl hst,
      d_ev α p _ _ rfl rfl, d_ev β r _ _ rfl rfl, mul_zsmul_left, mul_zsmul_right, mul_bd_left, mul_bd_right,
      Units.smul_def, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    · refine bd_congr (fun q y' hq => ?_) y
      unfold Fm
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · refine bd_congr (fun q z' hq => ?_) z
      unfold Fm
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · have e : Fm μ α.1 β.1 U s p r y z = 0 := by unfold Fm; rw [dite_eq_right h]
    have h0 := secmap_zsmul (K.d s t) (0 : ℤ) (0 : Sec (K.X s) U)
    rw [zero_smul, zero_smul] at h0
    rw [e, h0]
    rw [bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q y' hq => by unfold Fm; rw [dite_eq_right (by omega)]) y,
      bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q z' hq => by unfold Fm; rw [dite_eq_right (by omega)]) z,
      bd_zero', bd_zero', smul_zero, smul_zero, add_zero]

theorem secmap_add' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add ((φ.hom.app (op U)).hom) a b

theorem secmap_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero ((φ.hom.app (op U)).hom)

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)

theorem part1 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((n.negOnePow : ℤˣ) : ℤ) •
      bd (fun q y' => Fm μ α.1 β.1 U t q r y' (x.along b)) p (x.along a)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t) (Pr.d₁ (⟨p, r, a, b⟩ : Pr N)) := by
  cases p with
  | zero => simp [bd, Pr.d₁]
  | succ p =>
    show _ = _ • Finsupp.linearCombination ℤ _
      (∑ i : Fin (p + 2), Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) ((-1 : ℤ) ^ (i : ℕ)))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by push_cast; ring⟩

theorem part2 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) •
      bd (fun q z' => Fm μ α.1 β.1 U t p q (x.along a) z') r (x.along b)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
      ((-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N)) := by
  cases r with
  | zero => simp [bd, Pr.d₂]
  | succ r =>
    show _ = _ • Finsupp.linearCombination ℤ _ ((-1 : ℤ) ^ p •
      ∑ j : Fin (r + 2), Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) ((-1 : ℤ) ^ (j : ℕ)))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, map_zsmul, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum,
      smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-(p : ℤ), by push_cast; ring⟩

theorem d_phiT {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (z : Pr N) :
    Sec.map (K.d s t) (phiT μ hk α.1 β.1 x s z) =
      ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
        (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [phiT_Fm, secmap_zsmul, d_Fm μ α β U s t hst, smul_add, map_add (f := _), smul_add, part1 μ hk α β, part2 μ hk α β]

theorem d_phi {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (c : Pr N →₀ ℤ) :
    Sec.map (K.d s t) (phi μ hk α.1 β.1 x s c) = ((k.negOnePow : ℤˣ) : ℤ) • phi μ hk α.1 β.1 x t (Pr.d N c) := by
  rw [phi_eq, phi_eq]
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp only [map_zero, secmap_zero', smul_zero]
  · intro f g hf hg
    rw [map_add (f := _), map_add (f := _), map_add (f := _), secmap_add', hf, hg, smul_add]
  · intro z a
    rw [Finsupp.linearCombination_single, secmap_zsmul, d_phiT μ hk α β x s t hst]
    unfold Pr.d
    rw [Finsupp.linearCombination_single, map_zsmul, smul_comm]

theorem phi_add {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c + d) = phi μ hk α.1 β.1 x w c + phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_add (f := _)]

theorem phi_sub {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c - d) = phi μ hk α.1 β.1 x w c - phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_sub]

end

end LateralTheory.EtaleFoundations.EtaDelta


open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.EtaDelta in
theorem LateralTheory.EtaleFoundations.cupflip_eta_delta_of : LateralTheory.EtaleFoundations.cupflip_eta_delta := by
  intro h hs R _ I J K μ E n m k hk α β η hη N t ht U x
  cases N with
  | zero =>
    rw [ev_delta_zero (n := k - 1) (by omega) η (-((0 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη 0 _ _ U x,
      d_phi μ hk α β x _ t (by omega), hs.2.1, phi_sub]
  | succ M =>
    rw [ev_delta_succ (n := k - 1) (by omega) η M (-((M + 1 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη (M + 1) _ _ U x]
    simp only [hη]
    rw [Units.smul_def, phi_bd, d_phi μ hk α β x _ t (by omega), ← smul_add, ← phi_add, hs.2.2 M, phi_sub]
end
end

-- bundled from Development.EtaleCohomology.TateTwists.Delta
section
namespace LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass

theorem delta : LateralTheory.EtaleFoundations.EtaleSimplicialCochainEvaluationDifferentialFormula := LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds

theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSchemeGlobalSectionCohomologyClass :=
  LateralTheory.EtaleFoundations.etaleSimplicialCochain_scheme_class_of_evaluation_properties LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections delta
    LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components
    (LateralTheory.EtaleFoundations.etaleSimplicialScheme_cocycle_vanishing_at_id_isCoboundary_of_evaluati LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections delta
      LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components)

end LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awex_sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact ((E.map (SimplexCategory.subinterval j l h).op).naturality_apply g.op x)

theorem awex_freeGen_res {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen
  have e := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)) (ModuleCat.freeMk (ULift.up x))
  refine e.symm.trans ?_
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom y)
    (ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (P.map g.op)) (ULift.up x))

theorem awex_ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  unfold ev Sec.res
  have e := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)) (freeGen R _ U x)
  refine e.symm.trans ?_
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op V)).hom y)
    (awex_freeGen_res (R := R) _ g x)

theorem awex_lift_single {S : Type*} [Semiring S] {X M : Type*} [AddCommMonoid M] [Module S M]
    (f : X → M) (x : X) : Finsupp.lift M S X f (Finsupp.single x 1) = f x := by
  simp

noncomputable def awexNat {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : (freeP R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ (I.X s).obj where
  app U := ModuleCat.ofHom (Finsupp.lift _ (ULift.{1} R) _
        (fun y : ULift.{1} (Sx E p (unop U)) => a p s h (unop U) y.down))
  naturality := by
        intro U V g
        refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_)
        have e := ModuleCat.free_map_apply (R := ULift.{1} R)
          (uliftFunctor.{1}.map ((E.obj (op (SimplexCategory.mk p))).map g)) y
        change (Finsupp.lift _ (ULift.{1} R) _ _) (((freeP R).obj _).map g |>.hom (Finsupp.single y 1)) =
          ((I.X s).obj.map g).hom ((Finsupp.lift _ (ULift.{1} R) _ _) (Finsupp.single y 1))
        erw [e]
        refine (awex_lift_single (S := ULift.{1} R) _ _).trans ?_
        refine Eq.trans ?_ (congrArg ((I.X s).obj.map g).hom (awex_lift_single (S := ULift.{1} R) _ _).symm)
        exact (ha p s h (unop V) (unop U) g.unop y.down).symm

noncomputable def awexPhi {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ (I.X s)).symm (awexNat a ha p s h)

theorem awexPhi_freeGen {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ((awexPhi a ha p s h).hom.app (op U)).hom (freeGen R _ U x) = a p s h U x := by
  have e := toSheafify_sheafifyLift Scheme.etaleTopology (awexNat a ha p s h) (I.X s).property
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (congrArg (fun φ => φ.app (op U)) e))
    (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))
  refine e2.trans ?_
  exact awex_lift_single (S := ULift.{1} R) (fun y : ULift.{1} (Sx E p U) => a p s h U y.down) (ULift.up x)

def EtaleSimplicialCochainFromNaturalEvaluationsExists : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

theorem etale_alexander_whitney_cup_exists_of_cochain_from_evaluations (hmk : EtaleSimplicialCochainFromNaturalEvaluationsExists) : EtaleAlexanderWhitneyCupCochainExistsForPairing := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hmk R (E := E) (I := K) (n := k)
    (fun N w h U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n)
      (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega))))
    (by
      intro N w h V U g x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Sec.res, map_sum, Units.smul_def, map_zsmul]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [awex_sub_res, awex_sub_res, ← awex_ev_res, ← awex_ev_res]
      exact μ.nat g _ _ _ _ _ _)
  exact ⟨γ, fun N w h U x => hγ N w h U x⟩

noncomputable def awexCochain {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    Cochain ((chains R).obj E) I n :=
  Cochain.mk fun x y hxy => if hx : x ≤ 0 then
    (((chains R).obj E).XIsoOfEq (show x = -(((-x).toNat : ℕ) : ℤ) by omega)).hom ≫
      (chainsXIso R E (-x).toNat).hom ≫ awexPhi a ha (-x).toNat y (by omega)
  else 0

theorem awex_key {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (q p : ℕ) (e : q = p) (he : -(p : ℤ) = -(q : ℤ)) (s : ℤ) (h : -(p : ℤ) + n = s) (hq : -(q : ℤ) + n = s) :
    (chainsXIso R E p).inv ≫ (((chains R).obj E).XIsoOfEq he).hom ≫ (chainsXIso R E q).hom ≫ awexPhi a ha q s hq =
      awexPhi a ha p s h := by
  subst e
  simp

theorem awex_ev {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (awexCochain a ha) p s h U x = a p s h U x := by
  unfold ev
  rw [awexCochain, Cochain.mk_v, dite_eq_left (by omega), awex_key a ha _ p (by omega)]
  exact awexPhi_freeGen a ha p s h U x

theorem etale_simplicial_cochain_from_natural_evaluations_exists_holds : EtaleSimplicialCochainFromNaturalEvaluationsExists := by
  intro R _ E I n a ha
  exact ⟨awexCochain a ha, awex_ev a ha⟩

theorem etale_alexander_whitney_cup_cochain_exists_holds : EtaleAlexanderWhitneyCupCochainExistsForPairing :=
  etale_alexander_whitney_cup_exists_of_cochain_from_evaluations etale_simplicial_cochain_from_natural_evaluations_exists_holds

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCohomologyEvaluationConnectingHom
section
namespace LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
theorem etale_evaluation_map_basic_of_components : LateralTheory.EtaleFoundations.pp_ev_basic := by
  apply LateralTheory.EtaleFoundations.pp_ev_basic_of
theorem etale_cohomology_evaluation_mk : LateralTheory.EtaleFoundations.pp_ev_mk := by
  apply LateralTheory.EtaleFoundations.pp_ev_mk_of
theorem etale_cohomology_evaluation_connecting_hom : LateralTheory.EtaleFoundations.pp_ev_delta := by
  apply LateralTheory.EtaleFoundations.pp_ev_delta_of
theorem etale_torsion_cohomology_operation_spec : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := etale_torsion_cohomology_operation_spec
end LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyUniquenessHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_uniqueness_holds : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupCochainUnique := by
  intro R _ I J K μ E n m k hk α β γ γ' h h'
  exact LateralTheory.EtaleFoundations.AwExPf.ev_ext _ _ fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleMayerVietorisShortExactSequenceFreeOfCompon
section
namespace LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
theorem etale_mayer_vietoris_short_exact_sequence_free_of_components : LateralTheory.EtaleFoundations.EtaleFreePresheafMayerVietorisShortExact := by
  apply LateralTheory.EtaleFoundations.etale_free_presheaf_mayer_vietoris_short_exact_holds
theorem etale_mayer_vietoris_short_exact_sequence_of_components : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := by
  apply LateralTheory.EtaleFoundations.etale_chains_mayer_vietoris_short_exact_of_free <;> first | exact etale_mayer_vietoris_short_exact_sequence_free_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := etale_mayer_vietoris_short_exact_sequence_of_components
end LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit
section
open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney (hA : leaf_acyc) (hAW : leaf_aw) (hWA : leaf_wa) :
    LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy :=
  LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations hA steenrod_prism_chain_differential_squared_eq_zero_of_etale prism_boundary_map_square_zero_holds hAW hWA
end

