module

public import Formalism.LocalToGlobal.Columns.Bundle0036
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.Columns.XiTopTilRefHolds
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.ChainTwPsi

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ChainTwFrA
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def tfaExt {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact extE f

theorem tfa_std_iff {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (x : Sp E (n + 1)) :
    x ∈ stdAt E (n + 1) Q ↔ initL E n x ∈ stdAt E n Q ∧ IntAt Q (x (Fin.last n)) := by
  rw [ciMem_stdAt, ciMem_stdAt]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases h2 (fun j => ?_) i
    exact h1 j

def tfaD {n : ℕ} (z : E) (hz : z ≠ 0) : Sp E (n + 1) ≃ₗ[E] Sp E (n + 1) :=
  LinearEquiv.piCongrRight fun i : Fin (n + 1) => if i = Fin.last n then LinearEquiv.smulOfNeZero E E z hz else LinearEquiv.refl E E

theorem tfaD_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    tfaD z hz x i = if i = Fin.last n then z * x i else x i := by
  unfold tfaD
  rw [LinearEquiv.piCongrRight_apply]
  split_ifs with h
  · simp [LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  · rfl

theorem tfaD_symm_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    (tfaD z hz).symm x i = if i = Fin.last n then z⁻¹ * x i else x i := by
  have key : tfaD z hz (fun j => if j = Fin.last n then z⁻¹ * x j else x j) = x := by
    funext j
    rw [tfaD_apply]
    by_cases h : j = Fin.last n
    · subst h
      simp [hz]
    · simp only [h, if_false]
  conv_lhs => rw [← key]
  rw [LinearEquiv.symm_apply_apply]

def tfaExtZ {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (z : E) (hz : z ≠ 0) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact (tfaD z hz).trans (extE f)

theorem tfaZ_spec {SG : Finset (HeightOneSpectrum (𝓞 E))} {ST : Finset (HeightOneSpectrum (𝓞 E))} {N n : ℕ} (hN : N = n + 1) (pi : 𝓞 E)
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) (hOk : (d.1.til (ST := ST) pi).Ok) (w : SG) (hw : pi ∉ w.1.asIdeal) (hz : (algebraMap (𝓞 E) E pi) ≠ 0)
    (x : Sp E N) :
    tfaExtZ hN (d.1.liftFr w) (algebraMap (𝓞 E) E pi) hz x ∈ localization₂ w.1.asIdeal (DecoSet.tilH (ST := ST) hN pi d).1.N ↔
      x ∈ stdAt E N w.1 := by
  subst hN
  have hl := Deco.liftFr_spec (d.2.hasLift w)
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N ↔ _
  unfold DecoSet.til
  rw [dif_pos hOk]
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (tilN d.1.N) ↔ _
  have hinit : initL E n (tfaD (algebraMap (𝓞 E) E pi) hz x) = initL E n x := by
    funext i
    show tfaD _ hz x (Fin.castSucc i) = x (Fin.castSucc i)
    rw [tfaD_apply, if_neg (Fin.castSucc_ne_last i)]
  have hlast : tfaD (algebraMap (𝓞 E) E pi) hz x (Fin.last n) = algebraMap (𝓞 E) E pi * x (Fin.last n) := by
    rw [tfaD_apply, if_pos rfl]
  rw [mem_localization_tilN, initL_extE, extE_last, hinit, hlast, tfa_std_iff]
  refine and_congr (hl.1 _) ⟨fun h => ?_, fun h => (IntAt.coe w.1 pi).mul h⟩
  have h2 := (xtIntAt_piInv hw).mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hz, one_mul] at h2

end Gen

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (u : Pr.Word)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')


variable (sel mu) in
open Classical in
def topFrA (hQS : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∈ SG') : TopFr (R := R) sel mu u hSG where
  fr P d := if h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal then
      tfaExtZ (N_m_succ R) (d.1.liftFr ⟨P.1, hQS P.1 P.2⟩) (algebraMap (𝓞 X.E) X.E (Pr.piT u))
        (fun h0 => h.2 (by rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 X.E) X.E)] at h0; rw [h0]; exact zero_mem _))
    else frameOfY u P.1 (tilR hSG u d)
  spec P d x := by
    by_cases h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal
    · rw [dif_pos h]
      exact tfaZ_spec (N_m_succ R) (Pr.piT u) d h.1 ⟨P.1, hQS P.1 P.2⟩ h.2 _ x
    · rw [dite_eq_right h]
      exact frameOfY_spec u P.1 (tilR hSG u d) x


end Top

end Formalism.L2.Col.Sc.Fr
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainTwTopQ
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwTopQ

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem twTQ_HQ_entry {κ : Type} [CommRing κ] {n r b : ℕ} {M : GL (Fin n) κ} (hM : M ∈ HQ κ n r b) {a l : Fin n} (ha : a.1 < r)
    (hl : r ≤ l.1) : (M : Matrix (Fin n) (Fin n) κ) l a = 0 := by
  apply hM
  show coarse r [b] a.1 < coarse r [b] l.1
  unfold coarse
  simp only [blkIdx, if_pos ha, if_neg (not_lt.2 hl)]
  omega

def twInit {n : ℕ} (x : Sp E n) : Sp E (n - 1) := fun i => x ⟨i.1, by have := i.2; omega⟩

def twSnoc {n : ℕ} (x' : Sp E (n - 1)) (t : E) : Sp E n := fun l => if h : l.1 < n - 1 then x' ⟨l.1, h⟩ else t

theorem twInit_snoc {n : ℕ} (x' : Sp E (n - 1)) (t : E) : twInit (twSnoc (n := n) x' t) = x' := by
  funext i
  simp [twInit, twSnoc, i.2]

variable (P : HeightOneSpectrum (𝓞 E))

def twLastI {n : ℕ} (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

theorem twPar_block {n r : ℕ} (hr : r < n) (H : Sp E n ≃ₗ[E] Sp E n) (h' : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1))
    (hH : ∀ x (l : Fin n), H x l = if h : l.1 < n - 1 then h' (twInit x) ⟨l.1, h⟩ else x l)
    (hint : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (h' x' i))
    (hD : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (h' (Pi.single a 1) l / (qOf P : E)))
    (x : Sp E n) (hx : x ∈ LocE.parL P (qOf P) r n 0) : H x ∈ LocE.parL P (qOf P) r n 0 := by
  have hq0 : (qOf P : E) ≠ 0 := by exact_mod_cast (Formalism.L2.Ker.qOf_pos P).ne'
  rw [twParL_mem] at hx ⊢
  have hxI : ∀ l, IntAt P (x l) := fun l => by
    have := hx l
    by_cases hl : r ≤ l.1 ∧ l.1 < n
    · rw [if_pos hl, zpow_one] at this
      have e : x l = (qOf P : E) * ((qOf P : E)⁻¹ * x l) := by field_simp
      rw [e]; exact (ciIntAt_q (P := P) (q := qOf P)).mul this
    · rw [if_neg hl] at this; simpa using this
  have hxD : ∀ l : Fin n, r ≤ l.1 → IntAt P ((qOf P : E)⁻¹ * x l) := fun l hl => by
    have := hx l
    rw [if_pos ⟨hl, l.2⟩, zpow_one] at this
    exact this
  intro l
  rw [hH]
  by_cases hl : l.1 < n - 1
  · rw [dite_eq_left hl]
    by_cases hDl : r ≤ l.1
    · rw [if_pos ⟨hDl, l.2⟩, zpow_one]
      rw [twApply_coordE h' (twInit x) ⟨l.1, hl⟩, Finset.mul_sum]
      apply twIntAt_sum
      intro a
      have ea : (twE a : Sp E (n - 1)) = Pi.single a 1 := by
        funext j; unfold twE; simp [Pi.single_apply, eq_comm]
      rw [ea]
      by_cases ha : a.1 < r
      · have e : ((qOf P : E))⁻¹ * (twInit x a * h' (Pi.single a 1) ⟨l.1, hl⟩) =
            twInit x a * (h' (Pi.single a 1) ⟨l.1, hl⟩ / (qOf P : E)) := by field_simp
        rw [e]
        exact (hxI _).mul (hD a ⟨l.1, hl⟩ ha hDl)
      · have hxa := hxD ⟨a.1, by have := a.2; omega⟩ (by show r ≤ a.1; omega)
        have e : ((qOf P : E))⁻¹ * (twInit x a * h' (Pi.single a 1) ⟨l.1, hl⟩) =
            ((qOf P : E))⁻¹ * x ⟨a.1, by have := a.2; omega⟩ * h' (Pi.single a 1) ⟨l.1, hl⟩ := by
          unfold twInit; ring
        rw [e]
        refine hxa.mul (hint _ (fun j => ?_) _)
        by_cases hj : j = a
        · subst hj; simp only [Pi.single_eq_same]; exact ⟨1, 1, one_notMem P, by simp⟩
        · rw [Pi.single_eq_of_ne hj]; exact ⟨0, 1, one_notMem P, by simp⟩
    · rw [if_neg (fun h => hDl h.1), zpow_zero, inv_one, one_mul]
      exact hint (twInit x) (fun i => hxI _) ⟨l.1, hl⟩
  · rw [dite_eq_right hl]
    exact hx l

theorem mem_kOne_of_block {n r c : ℕ} (hr : r < n) (G : ↥(GLint E n P)) (g' : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1))
    (hblk : ∀ x (l : Fin n), (G : Sp E n ≃ₗ[E] Sp E n) x l = if h : l.1 < n - 1 then g' (twInit x) ⟨l.1, h⟩ else x l)
    (hDA : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (g' (Pi.single a 1) l / (qOf P : E)))
    (hDA' : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (g'.symm (Pi.single a 1) l / (qOf P : E))) :
    G ∈ twK1H P n r c := by
  have hn : 0 < n := by omega
  set Gm : Sp E n ≃ₗ[E] Sp E n := (G : Sp E n ≃ₗ[E] Sp E n) with hGm
  have hinitG : ∀ x, twInit (Gm x) = g' (twInit x) := fun x => by
    funext i
    show Gm x ⟨i.1, by have := i.2; omega⟩ = g' (twInit x) i
    rw [hblk, dite_eq_left i.2]
  have hlastG : ∀ x, Gm x (twLastI hn) = x (twLastI hn) := fun x => by
    rw [hblk, dite_eq_right (by unfold twLastI; simp)]
  have hinv : ∀ x (l : Fin n), Gm.symm x l = if h : l.1 < n - 1 then g'.symm (twInit x) ⟨l.1, h⟩ else x l := by
    intro x l
    have hx : Gm (Gm.symm x) = x := Gm.apply_symm_apply x
    by_cases h : l.1 < n - 1
    · rw [dite_eq_left h]
      have e1 : twInit (Gm.symm x) = g'.symm (twInit x) := by
        have h2 := hinitG (Gm.symm x)
        rw [hx] at h2
        rw [h2, LinearEquiv.symm_apply_apply]
      have := congrFun e1 ⟨l.1, h⟩
      unfold twInit at this
      exact this
    · rw [dite_eq_right h]
      have := congrFun hx l
      rw [hblk, dite_eq_right h] at this
      exact this
  have hinitG' : ∀ x, twInit (Gm.symm x) = g'.symm (twInit x) := fun x => by
    funext i
    show Gm.symm x ⟨i.1, by have := i.2; omega⟩ = g'.symm (twInit x) i
    rw [hinv, dite_eq_left i.2]
  have hlastG' : ∀ x, Gm.symm x (twLastI hn) = x (twLastI hn) := fun x => by
    rw [hinv, dite_eq_right (by unfold twLastI; simp)]

  have hstd : ∀ v : Sp E n, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (Gm v l) := fun v hv =>
    (twStd_mem _).1 ((G.2 v).2 ((twStd_mem _).2 hv))
  have hstd' : ∀ v : Sp E n, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (Gm.symm v l) := fun v hv =>
    (twStd_mem _).1 (((G⁻¹).2 v).2 ((twStd_mem _).2 hv))
  have hsnoc : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ l, IntAt P (twSnoc (n := n) x' 0 l) := fun x' hx l => by
    unfold twSnoc; split_ifs
    · exact hx _
    · exact ⟨0, 1, one_notMem P, by simp⟩
  have hg1 : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (g' x' i) := fun x' hx i => by
    have h1 := hstd _ (hsnoc x' hx) ⟨i.1, by have := i.2; omega⟩
    rw [hblk, dite_eq_left i.2, twInit_snoc] at h1
    exact h1
  have hg2 : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (g'.symm x' i) := fun x' hx i => by
    have h1 := hstd' _ (hsnoc x' hx) ⟨i.1, by have := i.2; omega⟩
    rw [hinv, dite_eq_left i.2, twInit_snoc] at h1
    exact h1
  have hsc : ∀ (f : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1)), (∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (f x' i)) →
      ∀ x' : Sp E (n - 1), (∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * x' i)) → ∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * f x' i) :=
    fun f hf x' hx i => by
      have h1 := hf (((qOf P : E) ^ (c : ℤ))⁻¹ • x') (fun j => by simpa [Pi.smul_apply, smul_eq_mul] using hx j) i
      rw [map_smul] at h1
      simpa [Pi.smul_apply, smul_eq_mul] using h1
  have hJ : Gm ∈ LocE.JQ P (qOf P) r n 0 := by
    refine ⟨G.2, fun x => ⟨fun h => ?_, twPar_block P hr Gm g' hblk hg1 hDA x⟩⟩
    have := twPar_block P hr Gm.symm g'.symm hinv hg2 hDA' _ h
    rwa [LinearEquiv.symm_apply_apply] at this

  have hL : ∀ (x : Sp E n), x ∈ LocE.sclLat P (qOf P) n (kOneLastExponents n c) ↔ (∀ i, IntAt P (twInit x i)) ∧
      IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * x (twLastI hn)) := by
    intro x
    rw [ciMem_sclLat]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h ⟨i.1, by have := i.2; omega⟩
        unfold kOneLastExponents at this
        rw [if_neg (show ¬ (i.1 + 1 = n) by have := i.2; omega)] at this
        simpa [twInit] using this
      · have := h (twLastI hn)
        have e : kOneLastExponents n c (twLastI hn).1 = (c : ℤ) := by unfold kOneLastExponents twLastI; rw [if_pos (by simp; omega)]
        rw [e] at this
        exact this
    · rintro ⟨h1, h2⟩ l
      unfold kOneLastExponents
      by_cases hl : l.1 + 1 = n
      · rw [if_pos hl]
        have e : l = twLastI hn := Fin.ext (by unfold twLastI; simp; omega)
        rw [e]; exact h2
      · rw [if_neg hl]
        simpa [twInit] using h1 ⟨l.1, by have := l.2; omega⟩
  have hX : ∀ (x : Sp E n), x ∈ LocE.sclLat P (qOf P) n (twistedLevelExponent n c) ↔
      (∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * twInit x i)) ∧ IntAt P (x (twLastI hn)) := by
    intro x
    rw [ciMem_sclLat]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h ⟨i.1, by have := i.2; omega⟩
        unfold twistedLevelExponent at this
        rw [if_neg (show ¬ (i.1 + 1 = n) by have := i.2; omega)] at this
        simpa [twInit] using this
      · have := h (twLastI hn)
        have e : twistedLevelExponent n c (twLastI hn).1 = 0 := by unfold twistedLevelExponent twLastI; rw [if_pos (by simp; omega)]
        rw [e, zpow_zero, inv_one, one_mul] at this
        exact this
    · rintro ⟨h1, h2⟩ l
      unfold twistedLevelExponent
      by_cases hl : l.1 + 1 = n
      · rw [if_pos hl]
        have e : l = twLastI hn := Fin.ext (by unfold twLastI; simp; omega)
        rw [e]; simpa using h2
      · rw [if_neg hl]
        simpa [twInit] using h1 ⟨l.1, by have := l.2; omega⟩
  refine ⟨hJ, fun x => ?_, fun x => ?_, fun w hw => ?_⟩
  · show Gm x ∈ _ ↔ x ∈ _
    rw [hL, hL, hinitG, hlastG]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, h2⟩
      have := hg2 _ h1 i
      rwa [LinearEquiv.symm_apply_apply] at this
    · rintro ⟨h1, h2⟩
      exact ⟨hg1 _ h1, h2⟩
  · show Gm x ∈ _ ↔ x ∈ _
    rw [hX, hX, hinitG, hlastG]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, h2⟩
      have := hsc g'.symm hg2 _ h1 i
      rwa [LinearEquiv.symm_apply_apply] at this
    · rintro ⟨h1, h2⟩
      exact ⟨hsc g' hg1 _ h1, h2⟩
  · rw [hX] at hw
    rw [ciMem_sclLat]
    intro l
    show IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * (Gm w l - w l))
    rw [hblk]
    by_cases hl : l.1 < n - 1
    · rw [dite_eq_left hl, mul_sub]
      have a1 := hsc g' hg1 _ hw.1 ⟨l.1, hl⟩
      have a2 := hw.1 ⟨l.1, hl⟩
      unfold twInit at a2
      exact ciIntAt_sub a1 a2
    · rw [dite_eq_right hl, sub_self, mul_zero]; exact ⟨0, 1, one_notMem P, by simp⟩

end TwTopQ

end Formalism.L2.Col
end
end

