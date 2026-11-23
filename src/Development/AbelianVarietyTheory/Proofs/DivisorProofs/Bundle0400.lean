module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupGradedCommOfIsFlip
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec

variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}

def phi (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) (w : ℤ) {N : ℕ} (x : Sx E N U) :
    (Pr N →₀ ℤ) →ₗ[ℤ] Sec (K.X w) U :=
  Finsupp.linearCombination ℤ fun z => sg (m * z.1) • pv μ a b w z.1 z.2.1 (x.along z.2.2.1) (x.along z.2.2.2)

variable (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)

theorem phi_single (w : ℤ) {N : ℕ} (x : Sx E N U) (z : Pr N) (t : ℤ) :
    phi μ a b w x (Finsupp.single z t) = t • sg (m * z.1) • pv μ a b w z.1 z.2.1 (x.along z.2.2.1) (x.along z.2.2.2) :=
  Finsupp.linearCombination_single _ _ _

theorem face_eq {p : ℕ} (x : Sx E (p + 1) U) (i : Fin (p + 2)) : x.face i = x.along (SimplexCategory.δ i) := rfl

theorem along_res {N p : ℕ} {V : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    (x.res g).along θ = (x.along θ).res g :=
  ConcreteCategory.congr_hom ((E.map θ.op).naturality g.op) x

theorem pv_res (w : ℤ) (p r : ℕ) {V : Scheme.{0}} (g : V ⟶ U) (y : Sx E p U) (z : Sx E r U) :
    Sec.res g (pv μ a b w p r y z) = pv μ a b w p r (y.res g) (z.res g) := by
  unfold pv
  split_ifs with h
  · rw [μ.nat, ev_res, ev_res]
  · exact map_zero _

theorem phi_res (w : ℤ) {N : ℕ} {V : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (c : Pr N →₀ ℤ) :
    Sec.res g (phi μ a b w x c) = phi μ a b w (x.res g) c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; exact map_zero _
  | add f f' hf hf' => rw [map_add (f := _), map_add (f := _), ← hf, ← hf']; exact map_add _ _ _
  | single z t =>
    rw [phi_single, phi_single, along_res, along_res, ← pv_res]
    simp only [Sec.res, map_zsmul]

theorem phi_along (w : ℤ) {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (x : Sx E M U) (c : Pr N →₀ ℤ) :
    phi μ a b w (x.along θ) c = phi μ a b w x (Pr.push θ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f f' hf hf' => rw [map_add (f := _), map_add (f := _), map_add (f := _), hf, hf']
  | single z t =>
    rw [Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, phi_single, phi_single, along_along, along_along]

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec
variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}
variable (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)

theorem phi_d₁ (w : ℤ) {N : ℕ} (x : Sx E N U) (p r : ℕ) (a' : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b' : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phi μ a b w x (Pr.d₁ ⟨p, r, a', b'⟩) = sg (m * p + m) • bdL (pv μ a b w) p r (x.along a') (x.along b') := by
  cases p with
  | zero =>
    change phi μ a b w x 0 = _
    simp [bdL]
  | succ p =>
    change phi μ a b w x (∑ i : Fin (p + 2), Finsupp.single ⟨p, r, SimplexCategory.δ i ≫ a', b'⟩ ((-1) ^ (i : ℕ))) = _
    have e : sg (m * ((p + 1 : ℕ) : ℤ) + m) = sg (m * p) := by
      rw [show m * ((p + 1 : ℕ) : ℤ) + m = m * p + (m + m) by push_cast; ring, sg_add, sg_add, sg_sq, mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, bdL, e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phi_single, face_eq, along_along, smul_comm]

theorem phi_d₂ (w : ℤ) {N : ℕ} (x : Sx E N U) (p r : ℕ) (a' : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b' : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phi μ a b w x (Pr.d₂ ⟨p, r, a', b'⟩) = sg (m * p) • bdR (pv μ a b w) p r (x.along a') (x.along b') := by
  cases r with
  | zero =>
    change phi μ a b w x 0 = _
    simp [bdR]
  | succ r =>
    change phi μ a b w x (∑ j : Fin (r + 2), Finsupp.single ⟨p, r, a', SimplexCategory.δ j ≫ b'⟩ ((-1) ^ (j : ℕ))) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, bdR, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [phi_single, face_eq, along_along, smul_comm]

theorem pv_zero_left (w : ℤ) (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    pv μ (0 : Cochain ((chains R).obj E) I n) b w p r y z = 0 := by
  unfold pv
  split_ifs
  · rw [ev_zero, map_zero, LinearMap.zero_apply]
  · rfl

theorem pv_zero_right (w : ℤ) (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    pv μ a (0 : Cochain ((chains R).obj E) J m) w p r y z = 0 := by
  unfold pv
  split_ifs
  · rw [ev_zero, map_zero]
  · rfl

theorem d_pv_cyc (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (w w' : ℤ) (hw : w + 1 = w')
    (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    Sec.map (K.d w w') (pv μ α.1 β.1 w p r y z) =
      -(sg (n + 1) • bdL (pv μ α.1 β.1 w') p r y z) - sg (-(p : ℤ) + n) • sg (m + 1) • bdR (pv μ α.1 β.1 w') p r y z := by
  by_cases h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w
  · rw [d_pv μ rfl rfl α.1 β.1 w w' hw p r y z h, Cocycle.δ_eq_zero, Cocycle.δ_eq_zero, pv_zero_left, pv_zero_right,
      zero_sub, zero_sub, smul_neg, ← sub_eq_add_neg]
  · have h0 : pv μ α.1 β.1 w p r y z = 0 := dif_neg h
    have hL : bdL (pv μ α.1 β.1 w') p r y z = 0 := by
      cases p with
      | zero => rfl
      | succ p =>
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [pv, dif_neg (by push_cast at h ⊢; omega), smul_zero]
    have hR : bdR (pv μ α.1 β.1 w') p r y z = 0 := by
      cases r with
      | zero => simp [bdR]
      | succ r =>
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [pv, dif_neg (by push_cast at h ⊢; omega), smul_zero]
    rw [h0, hL, hR]
    simp

theorem phi_d (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (w w' : ℤ) (hw : w + 1 = w')
    {N : ℕ} (x : Sx E N U) (c : Pr N →₀ ℤ) :
    Sec.map (K.d w w') (phi μ α.1 β.1 w x c) = sg (n + m) • phi μ α.1 β.1 w' x (Pr.d N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => rw [map_add (f := _), map_add (f := _), map_add (f := _), smul_add, ← hf, ← hf']; exact map_add _ _ _
  | single z t =>
    obtain ⟨p, r, a', b'⟩ := z
    have e1 : Sec.map (K.d w w') (phi μ α.1 β.1 w x (Finsupp.single ⟨p, r, a', b'⟩ t)) =
        t • sg (m * p) • Sec.map (K.d w w') (pv μ α.1 β.1 w p r (x.along a') (x.along b')) := by
      rw [phi_single]; simp only [Sec.map, map_zsmul]
    rw [e1, d_pv_cyc μ α β w w' hw, Pr.d, Finsupp.linearCombination_single, map_zsmul, map_add (f := _), map_zsmul, phi_d₁, phi_d₂]
    dsimp only
    have hm2 := sg_sq m
    simp only [sg_add, sg_neg, sg_one, sg_nat]
    match_scalars <;> first | ring1 | linear_combination (t * sg (m * p) * sg n) * hm2 | linear_combination (-(t * sg (m * p) * sg n)) * hm2

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec
variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}

theorem sg_eq_of_even (c d : ℤ) (h : Even (c - d)) : sg c = sg d := by
  obtain ⟨e, he⟩ := h
  calc sg c = sg (d + (e + e)) := by rw [show d + (e + e) = c by omega]
    _ = sg d := by rw [sg_add, sg_add, sg_sq, mul_one]

theorem phi_aw {k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c : Cochain ((chains R).obj E) K k} (hc : μ.IsAW hk a b c) (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (x : Sx E N U) :
    phi μ a b w x (Pr.aw N) = ev c N w h U x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc N w h U x, Pr.aw, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [phi_single, one_smul]
  dsimp only
  rw [pv_eq μ a b w (p : ℕ) (N - p) _ _ _ _ rfl rfl (by omega), sg_smul]
  rfl

theorem phi_wa {ν : Pair J I K} (hf : μ.IsFlip ν) {k : ℤ} (h' : m + n = k) {a : Cochain ((chains R).obj E) I n}
    {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k} (hc : ν.IsAW h' b a c) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + k = w) (x : Sx E N U) :
    phi μ a b w x (Pr.wa N) = sg (n * m) • ev c N w h U x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc N w h U x, Pr.wa, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [phi_single]
  dsimp only
  rw [pv_eq μ a b w (N - p) (p : ℕ) _ _ _ _ rfl rfl (by have := p.isLt; omega), hf, sg_smul, sg_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [sg_nat, ← sg_add, ← sg_add, ← sg_add]
  refine sg_eq_of_even _ _ ⟨m * ((N - p : ℕ) : ℤ) - n * m, ?_⟩
  push_cast
  ring
  all_goals (have := p.isLt; omega)

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x :=
  map_sub (evHom I n p s h U x) a b

end GlobalTheory.EtC.CupFlip


open GlobalTheory.EtC.CupSpec GlobalTheory.EtC.CupFlip in
theorem GlobalTheory.EtC.Pair.cup_flip : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (h : n + m = k) (h' : m + n = k) a b,
      μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a := by
  intro R _ I J K μ ν hf E n m k h h' a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := μ.aw_exists E h α β
  obtain ⟨γ', hγ'⟩ := ν.aw_exists E h' β α
  rw [μ.cup_spec E h α β γ hγ, ν.cup_spec E h' β α γ' hγ']
  obtain ⟨hh, -, hd0, hds⟩ := _root_.GlobalTheory.EtC.pr_aw_wa_homotopy
  obtain ⟨θ, hθ⟩ := ev_exists (R := R) (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ α.1 β.1 s x (hh N)) (fun N s _ V U g x => phi_res μ α.1 β.1 s g x (hh N))
  have key : δ (k - 1) k θ = sg k • (γ.1 - sg (n * m) • γ'.1) := by
    refine ev_ext _ _ fun N t ht U x => ?_
    rw [ev_zsmul, ev_sub', ev_zsmul]
    cases N with
    | zero =>
      rw [ev_δ_zero (by omega) θ U (t - 1) t (by omega) ht x, hθ, phi_d μ α β (t - 1) t (by omega), hd0, map_sub,
        phi_aw μ h hγ 0 t ht x, phi_wa μ hf h' hγ' 0 t ht x, h]
    | succ N =>
      have hb : phi μ α.1 β.1 t x (Pr.bd (hh N)) =
          ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • ev θ N t (by omega) U (x.face i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Pr.bd, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, hθ, face_eq, phi_along]
      rw [ev_δ_succ (by omega) θ U N (t - 1) t (by omega) ht x, hθ, phi_d μ α β (t - 1) t (by omega), ← hb, h, sg_smul,
        ← smul_add, ← map_add, hds, map_sub, phi_aw μ h hγ (N + 1) t ht x, phi_wa μ hf h' hγ' (N + 1) t ht x]
  have hmk : ∀ (c : ℤ) (z : Cocycle ((chains R).obj E) K k), CohomologyClass.mk (c • z) = c • CohomologyClass.mk z :=
    fun c z => map_zsmul (AddMonoidHom.mk' CohomologyClass.mk CohomologyClass.mk_add) c z
  rw [Units.smul_def, show (((n * m).negOnePow : ℤˣ) : ℤ) = sg (n * m) from rfl, ← hmk, ← sub_eq_zero,
    ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨k - 1, by omega, sg k • θ, ?_⟩
  rw [δ_smul, key, smul_smul, sg_sq, one_smul]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductCastMkOfIsAlexanderWhitney
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem cup_cast_mk_of_isAW_rec (q : ℕ) {S : Spc} (a b k n m N : ℤ) (e : a + b = k) (hN : n + m = N)
    (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q a)) n)
    (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q b)) m)
    (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q k)) N)
    (h : (Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q a)) (res (ZMod q) (tw q b)) (res (ZMod q) (tw q k)))
      (twPair q a b) e).IsAW hN α.1 β.1 γ.1) :
    ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast hN e : Ht q S N k) = CohomologyClass.mk γ := by
  subst e
  subst hN
  exact Pair.cup_spec (twPair q a b) S rfl α β γ h

theorem cup_cast_mk_of_isAW : ∀ (q : ℕ) {S : Spc} (i : ℤ) (j : ℕ) (m : ℤ) (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (i - (j : ℤ)))) (m - 2 * (j : ℤ))) (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (j : ℤ))) (2 * (j : ℤ))) (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q i)) m), (twPairI q i (j : ℤ)).IsAW (sub_add_cancel m _) α.1 β.1 γ.1 → ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast (by ring) (by ring) : Ht q S m i) = CohomologyClass.mk γ := by
  intro q S i j m α β γ h
  exact cup_cast_mk_of_isAW_rec q (i - (j : ℤ)) (j : ℤ) i (m - 2 * (j : ℤ)) (2 * (j : ℤ)) m
    (sub_add_cancel i _) (sub_add_cancel m _) α β γ h

end GlobalTheory.PBFc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductDiscreteSpaceFibreEqPairing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.DiscCup

theorem sub_zero_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i; simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem map_fst_sub {F : PSh} {E' : Spc} {N : ℕ} {U : Scheme.{0}} (w : Sx (disc.obj F ⨯ E') N U) (l : ℕ) (h : 0 + l ≤ N) :
    (show F.obj (op U) from Sx.map (prod.fst : disc.obj F ⨯ E' ⟶ _) (w.sub 0 l h)) =
      (show F.obj (op U) from Sx.map (prod.fst : disc.obj F ⨯ E' ⟶ _) w) := by
  unfold Sx.map Sx.sub
  have h1 := (prod.fst : disc.obj F ⨯ E' ⟶ _).naturality (SimplexCategory.subinterval 0 l h).op
  have h2 := congrArg (fun φ => φ.app (op U)) h1
  simp only [NatTrans.comp_app] at h2
  exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) w)

theorem ev_vanish {E : Spc} {R : Type} [CommRing R] {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (hv : α.v (-(p : ℤ)) s h = 0) (U : Scheme.{0}) (x : Sx E p U) : _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = 0 := by
  rw [_root_.GlobalTheory.EtC.ev, hv, comp_zero]
  rfl

end GlobalTheory.EtC.DiscCup

namespace GlobalTheory.EtC.DiscCup

theorem term_zero {q : ℕ} {E₁ E₂ : Spc} {i₁ i₂ n m s : ℤ} (k : ℕ)
    (a : Cochain ((chains (ZMod q)).obj E₁) (res (ZMod q) (tw q i₁)) n)
    (b : Cochain ((chains (ZMod q)).obj E₂) (res (ZMod q) (tw q i₂)) m) (V : Scheme.{0})
    (p : ℕ) (hp : p = 0) (s₁ t₁ : ℤ) (hs₁ : -(p : ℤ) + n = s₁) (ht₁ : -((k - p : ℕ) : ℤ) + m = t₁) (hw : s₁ + t₁ = s)
    (x0 : Sx E₁ p V) (x1 : Sx E₂ (k - p) V) (y0 : Sx E₁ 0 V) (y1 : Sx E₂ k V)
    (h0 : ∀ e : p = 0, e ▸ x0 = y0) (h1 : ∀ e : k - p = k, e ▸ x1 = y1) (hs' : n + (-(k : ℤ) + m) = s) :
    (twPair q i₁ i₂).mul V s₁ t₁ s hw (_root_.GlobalTheory.EtC.ev (R := ZMod q) a p s₁ hs₁ V x0) (_root_.GlobalTheory.EtC.ev (R := ZMod q) b (k - p) t₁ ht₁ V x1) =
      (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s hs' (_root_.GlobalTheory.EtC.ev (R := ZMod q) a 0 n (by simp) V y0) (_root_.GlobalTheory.EtC.ev (R := ZMod q) b k (-(k : ℤ) + m) rfl V y1) := by
  subst hp
  have e0 := h0 rfl
  have e1 := h1 rfl
  subst e0 e1
  obtain rfl : s₁ = n := by omega
  subst ht₁
  rfl

end GlobalTheory.EtC.DiscCup

open GlobalTheory.EtC.DiscCup in
theorem GlobalTheory.EtC.disc_cup_fibre : ∀ (q N : ℕ) (F : PSh) {n m i₁ i₂ : ℤ} (α : Cocycle ((chains (ZMod q)).obj (disc.obj F)) (res (ZMod q) (tw q i₁)) n) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) m), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0) → ∃ γ : Cocycle ((chains (ZMod q)).obj (disc.obj F ⨯ fibQ q N)) (res (ZMod q) (tw q (i₁ + i₂))) (n + m), CohomologyClass.mk γ = cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk α)) (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk z)) ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + (n + m) = s) (V : Scheme.{0}) (w : Sx (disc.obj F ⨯ fibQ q N) k V), _root_.GlobalTheory.EtC.ev (R := ZMod q) γ.1 k s hs V w = (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s (by omega) (_root_.GlobalTheory.EtC.ev (R := ZMod q) α.1 0 n (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) w)) (_root_.GlobalTheory.EtC.ev (R := ZMod q) z.1 k (-(k : ℤ) + m) rfl V (Sx.map prod.snd w)) := by
  intro q N F n m i₁ i₂ α z hα
  let α' := zcomp (Cocycle.ofHom ((chains (ZMod q)).map (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _))) α (zero_add n)
  let z' := zcomp (Cocycle.ofHom ((chains (ZMod q)).map (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _))) z (zero_add m)
  obtain ⟨γ, hγ⟩ := (twPair q i₁ i₂).aw_exists (disc.obj F ⨯ fibQ q N) rfl α' z'
  refine ⟨γ, ((twPair q i₁ i₂).cup_spec _ rfl α' z' γ hγ).symm, ?_⟩
  intro k s hs V w
  rw [hγ k s hs V w, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · have e1 : ((m * (((0 : Fin (k + 1)) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul]
    change (twPair q i₁ i₂).mul V _ _ s _ (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp α.1 (zero_add n)) _ _ rfl V _)
      (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp z.1 (zero_add m)) _ _ rfl V _) = _
    rw [CupSpec.ev_pull, CupSpec.ev_pull]
    apply term_zero k α.1 z.1 V _ (by simp)
    · intro e
      exact map_fst_sub w _ _
    · intro e
      exact congrArg (Sx.map prod.snd) (sub_zero_full w _)
  · intro i _
    change _ • (twPair q i₁ i₂).mul V _ _ s _ (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp α.1 (zero_add n)) _ _ rfl V _) _ = 0
    rw [CupSpec.ev_pull, ev_vanish α.1 (i.succ : ℕ) _ _ (hα _ (by simp) _ _), map_zero, LinearMap.zero_apply, smul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEqStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] → cusp θ m k' = cusp θ m k := by
  first | (exact @GlobalTheory.Shin.cusp_eq_of_modEq) | (exact GlobalTheory.Shin.cusp_eq_of_modEq) | (intros; apply GlobalTheory.Shin.cusp_eq_of_modEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F), cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  first | (exact @GlobalTheory.Shin.cusp_gal) | (exact GlobalTheory.Shin.cusp_gal) | (intros; apply GlobalTheory.Shin.cusp_gal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinatesStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_integral_coordinates : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ MvIsInt v (Ψ a) ∧ constantCoeff (Ψ a) = 0) → (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) → ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) → (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) → detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C // MvIsInt v f}, toE (v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f.1))) := by
  first | exact @GlobalTheory.FGDepth.Coord.depth_in_coords | exact GlobalTheory.FGDepth.Coord.depth_in_coords | (intros; apply GlobalTheory.FGDepth.Coord.depth_in_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthLeDividedPowerContentStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d n : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (u : ∀ b, Fin (n b) → Fin (d b) → C) (P : MvPolynomial (Σ b, Fin (n b)) C) (D : ℕ), P.IsHomogeneous D → (∀ b, IsSatFrame v (u b)) → depth G (ι := fun b => Fin (n b)) u P ≤ content v P := by
  first | exact @GlobalTheory.FGDepth.DepthLeContent.depth_le_content | exact GlobalTheory.FGDepth.DepthLeContent.depth_le_content | (intros; apply GlobalTheory.FGDepth.DepthLeContent.depth_le_content <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteGlBundleEqTrivialGLBundleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle : ∀ (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), V = trivV N (disc.obj F) := by
  first | (exact @GlobalTheory.EtC.disc_eq_trivV) | (exact GlobalTheory.EtC.disc_eq_trivV) | (intros; apply GlobalTheory.EtC.disc_eq_trivV  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticSystemDerivativeContinuousFunctional
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SolFunc

variable {d : ℕ}

def extLin {U : Set (E d)} (S : Submodule ℂ (U →ᵇ ℂ)) : S →ₗ[ℂ] (E d → ℂ) where
  toFun u := ext0 U ((u : U →ᵇ ℂ) : U → ℂ)
  map_add' u v := by funext x; exact GlobalTheory.HCA.SolSub.matrixExtendByZero_add (u : U →ᵇ ℂ) v x
  map_smul' c u := by funext x; exact GlobalTheory.HCA.SolSub.extendByZeroOffSubset_smul_apply c (u : U →ᵇ ℂ) x

theorem continuous_extLin_apply {U : Set (E d)} (S : Submodule ℂ (U →ᵇ ℂ)) (x : E d) :
    Continuous fun u : S => extLin S u x := by
  by_cases hx : x ∈ U
  · have : (fun u : S => extLin S u x) = fun u : S => (u : U →ᵇ ℂ) ⟨x, hx⟩ := by
      funext u; simp [extLin, ext0, hx]
    rw [this]
    exact (BoundedContinuousFunction.evalCLM ℂ (⟨x, hx⟩ : U)).continuous.comp continuous_subtype_val
  · have : (fun u : S => extLin S u x) = fun _ => 0 := by
      funext u; simp [extLin, ext0, hx]
    rw [this]; exact continuous_const

theorem continuousOn_extendByZeroOffSubset {U : Set (E d)} (u : U →ᵇ ℂ) : ContinuousOn (ext0 U u) U := by
  rw [continuousOn_iff_continuous_restrict]
  have : U.domRestrict (ext0 U u) = u := by funext x; exact dif_pos x.2
  rw [this]; exact u.continuous

end GlobalTheory.HCA.SolFunc


open GlobalTheory.HCA.SolFunc in
theorem GlobalTheory.HCA.dw_solSet_continuous_functional : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : S →L[ℂ] ℂ, ∀ u : S, l u = dw w (ext0 U (u : U →ᵇ ℂ)) x := by
  intro d ι _ P U hU ha hell S hS w x hx
  have hcl : IsClosed (S : Set (U →ᵇ ℂ)) := by
    rw [hS]; exact (GlobalTheory.HCA.solSet_closed_submodule d ι P U hU ha).1
  haveI : CompleteSpace S := hcl.completeSpace_coe
  have hsm : ∀ u : S, ContDiffOn ℝ ∞ (extLin S u) U := by
    intro u
    have hu : (u : U →ᵇ ℂ) ∈ solSet P U := by rw [← hS]; exact u.2
    exact ZetaZeros.D.EllReg.elliptic_regularity_of_parts d ι P U _ ⟨hU, ha, hell, continuousOn_extendByZeroOffSubset _, hu⟩
  obtain ⟨l, hl⟩ := _root_.GlobalTheory.HCA.dw_continuousFunctional d U hU S (extLin S) (fun y _ => continuous_extLin_apply S y) hsm w x hx
  exact ⟨l, fun u => hl u⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective : ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ), Function.Bijective (fun x : Ht q (sp (A × B)) n i => (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
  first | (exact @GlobalTheory.EtC.ProdCoh.ht_prod_bijective) | (exact GlobalTheory.EtC.ProdCoh.ht_prod_bijective) | (intros; apply GlobalTheory.EtC.ProdCoh.ht_prod_bijective  <;> assumption)
end

