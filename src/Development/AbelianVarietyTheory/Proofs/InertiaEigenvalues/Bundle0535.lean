module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0517
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDROfLinks
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.DRLim

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

private theorem hom_frobenius_pt {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
    (f : WittVector p R →+* WittVector p R) (x : WittVector p R) :
    f (WittVector.frobenius x) = WittVector.frobenius (f x) := by
  have h1 : ∀ z : WittVector p R, (p : WittVector p R) ∣ WittVector.frobenius z - z ^ p := by
    intro z
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have : WittVector.constantCoeff (WittVector.frobenius z - z ^ p) = 0 := by
      rw [map_sub, map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP, sub_self]
    exact this
  have h2 : ∀ y : R, WittVector.frobenius (WittVector.teichmuller p y) = WittVector.teichmuller p y ^ p := by
    intro y
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have h3 : ∀ n : ℕ, f (WittVector.frobenius x) - WittVector.frobenius (f x) ∈
      Ideal.span {(p : WittVector p R) ^ n} := by
    intro n
    have hnil : IsNilpotent ((p : ℕ) : WittVector p R ⧸ Ideal.span {(p : WittVector p R) ^ n}) := by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have := WittVector.eq_of_apply_teichmuller_eq
      ((Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})).comp (f.comp WittVector.frobenius))
      ((Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})).comp (WittVector.frobenius.comp f)) hnil (by
        intro y
        obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv R p n).surjective y
        simp only [RingHom.comp_apply]
        rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton, h2, iterateFrobeniusEquiv_def]
        simp only [map_pow]
        rw [pow_right_comm]
        exact (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub (h1 _) n))
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun this x)
  rw [← sub_eq_zero]
  refine WittVector.ext fun n => ?_
  rw [WittVector.zero_coeff]
  exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).1 (h3 _) n (Nat.lt_succ_self n)

theorem σA_frob (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) :=
  hom_frobenius_pt (Per.σA g) x

theorem map_mk_eq_zero {R : Type} [CommRing R] {m n : Type} (I : Ideal R) (M : Matrix m n R) :
    M.map (Ideal.Quotient.mk I) = 0 ↔ ∀ i j, M i j ∈ I := by
  rw [← Matrix.ext_iff]
  simp only [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]

theorem msub {R B : Type} [CommRing R] [CommRing B] {m n : Type} (f : R →+* B) (M M' : Matrix m n R) :
    (M - M').map f = M.map f - M'.map f := Matrix.map_sub _ (map_sub f) _ _

theorem map_smul_one {R B : Type} [CommRing R] [CommRing B] {n : Type} [DecidableEq n] (f : R →+* B) (a : R) :
    (a • (1 : Matrix n n R)).map f = f a • (1 : Matrix n n B) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, h]

theorem exists_of_mem_sup {R : Type} [CommRing R] {a b x : R} (h : x ∈ Ideal.span {a} ⊔ Ideal.span {b}) :
    ∃ u v, x = b * u + a * v := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  exact ⟨z, y, by ring⟩

theorem σA_mem (bk : BK K) (g : GQ l) (n M : ℕ) (a : Ainf l)
    (ha : a ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M}) :
    Per.σA g a ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M} := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hE : bk.ev bk.E ∣ Per.σA g (bk.ev bk.E) := by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  obtain ⟨w, hw⟩ := hE
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, hw, mul_pow]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)) (Ideal.mem_sup_right ?_)
  exact Ideal.mem_span_singleton.2 ⟨Per.σA g z * w ^ M, by ring⟩

theorem ev_mem (bk : BK K) (n M : ℕ) (s : bk.S) (hs : s ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ M}) :
    bk.ev s ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M} := by
  have := Ideal.mem_map_of_mem bk.ev hs
  rwa [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow, map_pow,
    map_natCast] at this

end GlobalTheory.BKLim.DRLim


open GlobalTheory.BKLim.DRLim in
theorem GlobalTheory.BKLim.isDR_of_links : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsDR) → F₀.IsDR := by
  intro l _ K bk d N ρ tw F F₀ r hlink hDR M
  obtain ⟨c, hc⟩ := GlobalTheory.T.breuilKisin_beta_bounded_denominators l K bk (M + 1)
  obtain ⟨k₀, hk₀⟩ := _root_.GlobalTheory.BSP.BK.exists_inv_lift l K bk (M + 1)
  choose γf hγ1 hγ2 using hk₀
  have htf1 := _root_.GlobalTheory.AinfEPow.ePow_facts l K bk 1
  have htfM := _root_.GlobalTheory.AinfEPow.ePow_facts l K bk (M + 1)
  let Xm : (Fin d × Fin d → bk.S) → Matrix (Fin d) (Fin d) bk.S := fun x => Matrix.of fun i j => x (i, j)
  let I₁ : ℕ → Ideal bk.S := fun n => Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ 1}
  let J : ℕ → Ideal (Ainf l) := fun n => Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ (M + 1)}
  let Φ : ↥(GK K) → Matrix (Fin d) (Fin d) bk.S → Matrix (Fin d) (Fin d) (Ainf l) := fun g β =>
    (F₀.ε g).map WittVector.frobenius * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev
  let Q : ℕ → (Fin d × Fin d → bk.S) → Prop := fun n x =>
    (∀ i j, (Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j ∈ I₁ n) ∧
      ∀ g i j, Φ g (Xm x) i j ∈ J n
  have hmono : ∀ n x, Q (n + 1) x → Q n x := by
    intro n x ⟨h1, h2⟩
    have hl : ∀ {R : Type} [CommRing R] (y : R), Ideal.span {(l : R) ^ (n + 1)} ≤ Ideal.span {(l : R) ^ n} :=
      fun _ => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n))
    exact ⟨fun i j => sup_le_sup_right (hl (0 : bk.S)) _ (h1 i j),
      fun g i j => sup_le_sup_right (hl (0 : Ainf l)) _ (h2 g i j)⟩
  have hpert : ∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)}) →
      Q n y := by
    intro n x y ⟨h1, h2⟩ hd
    have hle : Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)} ≤ I₁ n :=
      sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega))) _
    have hD : ∀ i j, (Xm x - Xm y) i j ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)} :=
      fun i j => hd (i, j)
    refine ⟨fun i j => ?_, fun g i j => ?_⟩
    · have e : (Xm y - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j =
          (Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j - (Xm x - Xm y) i j := by
        simp only [Matrix.sub_apply]; ring
      rw [e]
      exact sub_mem (h1 i j) (hle (hD i j))
    · have e : Φ g (Xm y) = Φ g (Xm x) - ((F₀.ε g).map WittVector.frobenius *
          ((Xm x - Xm y).map bk.ev).map (Per.σA (g : GQ l)) - (Xm x - Xm y).map bk.ev) := by
        simp only [Φ, msub, Matrix.mul_sub]; abel
      rw [e, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply]
      refine sub_mem (h2 g i j) (sub_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) ?_)
      · exact σA_mem bk _ n (M + 1) _ (ev_mem bk n (M + 1) _ (hD k j))
      · exact ev_mem bk n (M + 1) _ (hD i j)
  have hex : ∀ n, ∃ x, Q n x := by
    intro n
    obtain ⟨m, hnm, R, G, hRT, hRG⟩ := hlink n
    obtain ⟨k', β'', hβ''⟩ := hDR m (M + 1)
    obtain ⟨β', hβ'⟩ := hc N (tw.d' m) _ (F m) k' β'' hβ''
    have hrel := _root_.GlobalTheory.BKLim.LinkCocycle.main l K bk N N d (tw.d' m) n (fun g => (ρ g).val) (fun g => (tw.ρ' m g).val) F₀ (F m)
      (tw.Pi m) R (fun g i j => (pow_dvd_pow _ hnm).trans ((tw.onto m).equi g i j)) hRT
    let φS := frobS l bk.a
    let γ : Matrix (Fin (tw.d' m)) (Fin d) bk.S := Matrix.of fun i j => γf (φS (G i j))
    let Mx : Matrix (Fin d) (Fin d) bk.S := R.map φS * β' * γ
    refine ⟨fun ij => Mx ij.1 ij.2, ?_, ?_⟩
    ·
      let q := Ideal.Quotient.mk (I₁ n)
      have hE : ∀ s : bk.S, bk.E ∣ s → q s = 0 := fun s hs =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (by simpa using hs)))
      have hL : ∀ s : bk.S, (l : bk.S) ^ n ∣ s → q s = 0 := fun s hs =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 hs))
      have hq1 : β'.map q = q ((l : bk.S) ^ c) • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) _) := by
        have : (β' - (l : bk.S) ^ c • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) bk.S)).map q = 0 := by
          ext i j; exact hE _ (hβ'.1 i j)
        rwa [msub, map_smul_one, sub_eq_zero] at this
      have hq2 : γ.map q = q ((l : bk.S) ^ k₀) • (G.map φS).map q := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, γ, smul_eq_mul, ← map_mul]
        exact (Ideal.Quotient.eq.2 (Ideal.Quotient.eq_zero_iff_mem.1 (hE _ (hγ1 _))))
      have hq3 : (R.map φS).map q * (G.map φS).map q = q ((l : bk.S) ^ r) • (1 : Matrix (Fin d) (Fin d) _) := by
        have : (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)).map (q.comp φS) = 0 := by
          ext i j
          refine hL _ ?_
          have := map_dvd φS (hRG i j)
          simpa [φS, map_pow, map_natCast] using this
        rw [msub, Matrix.map_mul, map_smul_one, sub_eq_zero, RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_map,
          Function.comp_apply, map_pow, map_natCast] at this
        rw [this, map_pow, map_natCast]
      refine (map_mk_eq_zero (I₁ n) _).1 ?_
      show (Mx - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)).map q = 0
      rw [msub, map_smul_one, Matrix.map_mul, Matrix.map_mul, hq1, hq2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
      rw [hq3, smul_smul, sub_eq_zero]
      congr 1
      simp only [← map_mul, ← pow_add]
      ring_nf
    · intro g
      refine (map_mk_eq_zero (J n) _).1 ?_
      let p := Ideal.Quotient.mk (J n)
      show (Φ g Mx).map p = 0
      have hp1 : ((F₀.ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * (((R.map bk.ev).map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p =
          ((R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * (((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p := by
        have h : (((F₀.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * (F m).ε g)).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p = 0 := by
          ext i j
          simp only [Matrix.map_apply, Matrix.zero_apply]
          refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 ?_))
          simpa [map_pow, map_natCast] using map_dvd (WittVector.frobenius : Ainf l →+* Ainf l) (hrel g i j)
        simpa only [msub, Matrix.map_mul, sub_eq_zero] using h
      have hp2 : (((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * ((β'.map bk.ev).map (Per.σA (g : GQ l))).map p = (β'.map bk.ev).map p := by
        have h : ((((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l) * (β'.map bk.ev).map (Per.σA (g : GQ l)) - β'.map bk.ev)).map p = 0 := by
          ext i j
          simp only [Matrix.map_apply, Matrix.zero_apply]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (hβ'.2 g i j)))
        simpa only [msub, Matrix.map_mul, sub_eq_zero] using h
      have hp3 : ((γ.map bk.ev).map (Per.σA (g : GQ l))).map p = (γ.map bk.ev).map p := by
        ext i j
        simp only [Matrix.map_apply, Matrix.of_apply, γ]
        exact Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (hγ2 _ g)))
      have hRev : (R.map φS).map bk.ev = (R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l) := by
        exact Matrix.ext fun i j => bk.ev_frob _
      have hRσ : ((R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l)).map (Per.σA (g : GQ l)) = ((R.map bk.ev).map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) := by
        exact Matrix.ext fun i j => σA_frob _ _
      simp only [Φ, Mx, msub, Matrix.map_mul]
      rw [hRev, hRσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hp1, Matrix.mul_assoc _ ((((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p), hp2, hp3, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.T.breuilKisin_quotient_eisenstein_compactness l K bk (Fin d × Fin d) (M + 1) Q hmono hpert hex
  refine ⟨c + k₀ + r, Xm x, fun i j => ?_, fun g i j => ?_⟩
  · have h4 := htf1.2.2.2 (bk.ev ((Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j))
      (fun n => exists_of_mem_sup (ev_mem bk n 1 _ ((hx n).1 i j)))
    simpa using htf1.2.1 _ h4
  · have h4 := htfM.2.2.2 (Φ g (Xm x) i j) (fun n => exists_of_mem_sup ((hx n).2 g i j))
    exact (pow_dvd_pow _ (Nat.le_succ M)).trans h4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfLocalizationAway
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_away {A C A' C' : Type} [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
    (h : A →+* C) (k : A →+* A') (k' : C →+* C') (h' : A' →+* C') (e : k'.comp h = h'.comp k) (x : A)
    (H : letI := h.toAlgebra; IsLocalization.Away x C)
    (H' : letI := h'.toAlgebra; IsLocalization.Away (k x) C') :
    CategoryTheory.IsPushout (CommRingCat.ofHom h) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  letI : Algebra A C := h.toAlgebra
  letI : Algebra A A' := k.toAlgebra
  letI : Algebra C C' := k'.toAlgebra
  letI : Algebra A' C' := h'.toAlgebra
  letI : Algebra A C' := (h'.comp k).toAlgebra
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun e a).symm
  haveI : IsLocalization (Submonoid.powers x) C := H
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers x)) C' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact H'
  haveI : Algebra.IsPushout A A' C C' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers x) C A' C'
  exact (CommRingCat.isPushout_iff_isPushout (R := A) (R' := C) (S := A') (S' := C')).2
    (Algebra.IsPushout.symm inferInstance)

theorem IsLoc.isUnit_of_complete {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} {s : B.A} {h : Hom B C}
    (H : IsLoc s h) : IsUnit (h.f s) := by
  have hu : IsUnit (qmap h 1 (Ideal.Quotient.mk (adI B ^ 1) s)) := by
    letI := (qmap h 1).toAlgebra
    haveI := H.away 1
    exact IsLocalization.Away.algebraMap_isUnit _
  rw [qmap_mk] at hu
  haveI := C.complete
  have hj : adI C ^ 1 ≤ (⊥ : Ideal C.A).jacobson := by
    rw [pow_one]
    exact IsAdicComplete.le_jacobson_bot _
  haveI := isLocalHom_of_le_jacobson_bot _ hj
  exact IsUnit.of_map (Ideal.Quotient.mk _) _ hu

theorem stable_of_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C),
    (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  rintro l _ R _ B C s h ⟨t, ht, hst⟩ H
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · letI := (qmap h m).toAlgebra
    haveI := H.away m
    exact IsLocalization.flat _ (Submonoid.powers (Ideal.Quotient.mk (adI B ^ m) s))
  ·
    have hgen : GenAway B' (k.f s) (k.f t) := by
      refine ⟨k.f_I t ht, fun x hx => ?_⟩
      rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R B B' k] at hx
      have hx' : x ∈ Ideal.span (k.f '' B.I) := hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ n : ℕ, k.f s ^ n * x ∈ Ideal.span {k.f t}) ?_ ?_ ?_ ?_ hx'
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨n, hn⟩ := hst y hy
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
        refine ⟨n, Ideal.mem_span_singleton'.2 ⟨k.f c, ?_⟩⟩
        simpa only [map_mul, map_pow] using congrArg k.f hc
      · exact ⟨0, by simp⟩
      · rintro a b _ _ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
        refine ⟨n₁ + n₂, ?_⟩
        have hab : k.f s ^ (n₁ + n₂) * (a + b) =
            k.f s ^ n₂ * (k.f s ^ n₁ * a) + k.f s ^ n₁ * (k.f s ^ n₂ * b) := by ring
        rw [hab]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
      · rintro a b _ ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hn
    obtain ⟨C', h', hloc', -⟩ := _root_.GlobalTheory.BSP.exists_isLoc l R B' (k.f s) (k.f t) hgen
    obtain ⟨k', hk'⟩ := H.univ C' (h'.comp k)
      (show IsUnit (h'.f (k.f s)) from IsLoc.isUnit_of_complete hloc')
    refine ⟨C', k', h', hk', fun m => ?_⟩
    refine isPushout_of_away (qmap h m) (qmap k m) (qmap k' m) (qmap h' m) ?_
      (Ideal.Quotient.mk _ s) (H.away m) ?_
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, qmap_mk]
      exact congrArg (fun g : Hom B C' => Ideal.Quotient.mk (adI C' ^ m) (g.f a)) hk'
    · rw [qmap_mk]
      exact hloc'.away m

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JBSingleMemFilT
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiPole

section Rings

variable {l : ℕ} [Fact l.Prime]

theorem ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) :=
  GlobalTheory.MemLoc.ULaws.iota_aB C w

private theorem aB_alg (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) w) = Per.aB l w :=
  GlobalTheory.MemLoc.ULaws.iota_injective C (by rw [C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris, ι_aB])

private theorem toB_tmul (C : GlobalTheory.MemLoc.Core l) {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O)
    (w : Per.Ainf l) : toB l O (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] Per.aB l w :=
  congrArg (fun y : Per.Bcris l => (o ⊗ₜ[ℤ_[l]] y : OB l O)) (aB_alg C w)

end Rings

section Tensor

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem smul_TWincl_mem_filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) {n : ℤ} {d : Per.Bcris l}
    (hd : C.ι d ∈ Per.FilD l n) (z : TW (OA l O) T) :
    ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z ∈ filT C T n := by
  unfold filT
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | tmul c x =>
    change ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • (toB l O c ⊗ₜ[O] x) ∈ _
    rw [smul_tmul', smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, zero_tmul]; exact zero_mem _
    | tmul o w =>
      have e : ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) * toB l O (o ⊗ₜ w) =
          o • ((1 : O) ⊗ₜ[ℤ_[l]] (d * Per.aB l w) : OB l O) := by
        rw [toB_tmul C o w, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, ← smul_tmul']
      refine Submodule.smul_mem _ o (Submodule.subset_span ⟨d * Per.aB l w, x, ?_, rfl⟩)
      rw [map_mul, ι_aB, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hd
    | add c c' hc hc' => rw [map_add (f := _), mul_add, add_tmul]; exact add_mem hc hc'
  | add z z' hz hz' => rw [map_add (f := _), smul_add]; exact add_mem hz hz'

end Tensor

end GlobalTheory.BKGal.XiPole


open GlobalTheory.BKGal.XiPole in
theorem GlobalTheory.BKGal.XiPole.jB_single_mem_filT : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R C i

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩

  obtain ⟨-, -, -, hK4⟩ := _root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε _ hEps hδl
  obtain ⟨z, hz⟩ := hK4 (inclL t ϖ D.toPhiMod (Pi.single i 1)) ⟨Pi.single i 1, rfl⟩
  rw [← inclL_smul_coord] at hz
  have hB := R.cmp _ z hz
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η) with hm
  have e1 : (fun j => toB l O (m * (Pi.single i (1 : OA l O) : ι → OA l O) j)) = toB l O m • (Pi.single i (1 : OB l O)) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [e1, map_smul] at hB
  have htm : toB l O m = (1 : O) ⊗ₜ[ℤ_[l]] Per.aB l (muOf ε ^ η) := toB_tmul C _ _

  have hμu : IsUnit (Per.aB l (muOf ε)) := by
    rw [← aB_alg C]
    exact GlobalTheory.MemLoc.TFil.isUnit_mu hE
  set d : Per.Bcris l := ((hμu.unit⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) ^ η with hd
  have hdm : d * Per.aB l (muOf ε ^ η) = 1 := by
    rw [hd, map_pow, ← mul_pow, IsUnit.val_inv_mul, one_pow]
  clear_value d
  have hjB : R.jB (Pi.single i 1) = ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z := by
    rw [← hB, smul_smul, htm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hdm,
      ← Algebra.TensorProduct.one_def, one_smul]

  have hν : IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (GlobalTheory.MemLoc.TiedUnif.theta_piOne hE)
  obtain ⟨v', hv'⟩ := hν.exists_right_inv
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hUval : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hιμ : C.ι (Per.aB l (muOf ε)) = (U : Per.BdR l) *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) := by
    rw [ι_aB, hUval, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg _ (GlobalTheory.MemLoc.TiedUnif.mu_eq ε))
  have h1 : C.ι d * (C.ι (Per.aB l (muOf ε))) ^ η = 1 := by
    rw [← map_pow, ← map_mul, ← map_pow, hdm, map_one]
  rw [hιμ] at h1
  have hpq : ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η = 1 := by
    rw [show ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) =
      ((U : Per.BdR l) * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε) * v') by
      rw [map_mul]; ring, Units.mul_inv, hv', map_one, one_mul, one_pow]
  have hU : ((U ^ (-(η : ℤ)) : (Per.BdR l)ˣ) : Per.BdR l) = ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ η := by
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  have hdF : C.ι d ∈ Per.FilD l (-(η : ℤ)) := by
    refine (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE _ _).2 ⟨v' ^ η, ?_⟩
    rw [← hUdef, hU, map_pow]
    calc C.ι d = C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η := by
          rw [hpq, mul_one]
      _ = (C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε))) ^ η) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v') ^ η := by
          rw [mul_pow _ _ η, mul_assoc]
      _ = _ := by rw [h1, one_mul, mul_pow]
  rw [hjB]
  exact smul_TWincl_mem_filT C T hdF z
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturatedStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wachN_of_map_mem_saturated : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀ := by
  first | exact @GlobalTheory.NL.KerSat.mem_N_of_map_mem | exact GlobalTheory.NL.KerSat.mem_N_of_map_mem | (intros; apply GlobalTheory.NL.KerSat.mem_N_of_map_mem <;> assumption)
end

