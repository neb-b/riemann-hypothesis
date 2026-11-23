module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRestrictScalarsTraceFormStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_restrictScalars_traceForm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')),
    (∀ v, v ∈ LZ.T ↔ v ∈ L.T) → (∀ v, v ∈ LZ'.T ↔ v ∈ L'.T) →
    ∀ (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x y, PQ x y = lam (Pr x y)) → IsDualLat1 (P.PD K) L L' Pr →
    IsDualLat1 (P.PD K) LZ LZ' PQ := by
  first | exact @GlobalTheory.DualLatDescent.dualLat_resQ | exact GlobalTheory.DualLatDescent.dualLat_resQ | (intros; apply GlobalTheory.DualLatDescent.dualLat_resQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageAddEllPiAdicClosed
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem powerSeries_exists_sum {O : Type} [CommRing O] (a : ℕ → PowerSeries O) :
    ∃ s : PowerSeries O, ∀ m, ∃ b,
      s = ∑ i ∈ Finset.range m, PowerSeries.X ^ i * a i + PowerSeries.X ^ m * b := by
  set s : PowerSeries O := PowerSeries.mk fun n =>
    PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1), PowerSeries.X ^ i * a i) with hs
  refine ⟨s, fun m => ?_⟩
  have hdvd : PowerSeries.X ^ m ∣ s - ∑ i ∈ Finset.range m, PowerSeries.X ^ i * a i := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, hs, PowerSeries.coeff_mk, sub_eq_zero]

    have key : ∀ d, PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1 + d), PowerSeries.X ^ i * a i)
        = PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1), PowerSeries.X ^ i * a i) := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [show n + 1 + (d + 1) = n + 1 + d + 1 by omega, Finset.sum_range_succ, map_add (f := _), ih,
          PowerSeries.coeff_X_pow_mul', if_neg (by omega), add_zero]
    have := key (m - (n + 1))
    rw [show n + 1 + (m - (n + 1)) = m by omega] at this
    exact this.symm
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨b, by rw [← hb]; ring⟩

theorem letA_exists_sum {O : Type} [CommRing O] {n : ℕ} (a : ℕ → LetA O n) :
    ∃ s : LetA O n, ∀ m, ∃ b, s = ∑ i ∈ Finset.range m, letπ ^ i * a i + letπ ^ m * b := by
  choose s hs using fun k : ZMod n => powerSeries_exists_sum (fun i => a i k)
  refine ⟨s, fun m => ?_⟩
  choose b hb using fun k => hs k m
  refine ⟨b, ?_⟩
  funext k
  rw [hb k]
  unfold letπ
  simp [Finset.sum_apply, Pi.pow_apply, Pi.mul_apply]

theorem near_closed_abstract {A E S R : Type} [CommRing A] [CommRing E] [CommRing S] [CommRing R]
    (j : A →+* E) (io : A →+* S) (ι : S →+* R) (f : E →+* R) (p : ℕ) (π : A) (t : R)
    (hext : ∀ a, f (j a) = ι (io a)) (ht : ι (io π) = t)
    (hsum : ∀ a : ℕ → A, ∃ s, ∀ m, ∃ b, s = ∑ i ∈ Finset.range m, π ^ i * a i + π ^ m * b)
    (hsep : ∀ x : R, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
    (hE : ∀ m e, Near ι p t m (f e) → ∃ a e', e = j (π ^ m * a) + (p : E) * e')
    (x : R) (hx : ∀ m, ∃ e, Near ι p t m (x - f e)) : ∃ e r, x - f e = (p : R) * r := by
  unfold Near at hsep hE hx
  choose e he using hx

  have hD : ∀ i, ∃ a r, f (e (i + 1) - e i) = t ^ i * ι a + (p : R) * r := by
    intro i
    obtain ⟨a0, r0, h0⟩ := he i
    obtain ⟨a1, r1, h1⟩ := he (i + 1)
    refine ⟨a0 - io π * a1, r0 - r1, ?_⟩
    have hsplit : f (e (i + 1) - e i) = (x - f (e i)) - (x - f (e (i + 1))) := by
      rw [map_sub]; ring
    rw [hsplit, h0, h1, map_sub, map_mul, ht]
    ring
  choose a e' hae using fun i => hE i _ (hD i)
  obtain ⟨s, hs⟩ := hsum a
  have hsumD : ∀ m, e m = e 0 + j (∑ i ∈ Finset.range m, π ^ i * a i) +
      (p : E) * ∑ i ∈ Finset.range m, e' i := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, map_add (f := _)]
      linear_combination hae k + ih
  refine ⟨e 0 + j s, hsep _ fun m => ?_⟩
  obtain ⟨b, hb⟩ := hs m
  obtain ⟨a0, r0, h0⟩ := he m
  refine ⟨a0 - io b, r0 + f (∑ i ∈ Finset.range m, e' i), ?_⟩
  have key : f (e 0 + j s) = f (e m) - (p : R) * f (∑ i ∈ Finset.range m, e' i) + t ^ m * ι (io b) := by
    rw [hsumD m, hb]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, hext, ht]
    ring
  rw [key, map_sub]
  linear_combination h0

set_option maxHeartbeats 1000000 in
private theorem ioE_closed_lemma (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL)
    (hx : ∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) : ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  obtain ⟨hsep, -⟩ := _root_.GlobalTheory.Decompl.nearPi_sep_complete l P AI LL s
  obtain ⟨hE, -⟩ := _root_.GlobalTheory.Decompl.near_ioE l P AI K s LL h W E
  have hext : ∀ a, E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE a) =
      inclR LL (E.tie.io a) := by
    intro a
    exact E.tie.ioE_ext a
  have ht : inclR LL (E.tie.io letπ) = piR AI LL s := by
    rw [E.tie.io_π]
    rfl

  have hN : ∀ m y, NearPi AI LL s m y ↔ Near (inclR LL : RA LL →+* RW LL) l (piR AI LL s) m y :=
    fun _ _ => Iff.rfl
  simp only [hN] at hsep hE hx
  exact near_closed_abstract (algebraMap _ W.EE) (E.tie.io : _ →+* RA LL) (inclR LL : RA LL →+* RW LL)
    (E.tie.ioE : W.EE →+* RW LL) l letπ (piR AI LL s) hext ht letA_exists_sum hsep hE x hx

theorem ioE_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL), (∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) → ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  intro l _ P AI K s LL h W E x hx
  exact ioE_closed_lemma l P AI K s LL h W E x hx

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageSaturatedAdicClosed
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.Sat

theorem pow_dvd_of_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (p : ℕ)
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hd : ∀ (e : A) (r : R), f e = (p : R) * r → ∃ e' : A, e = (p : A) * e') (k : ℕ) :
    ∀ (e : A) (r : R), f e = (p : R) ^ k * r → ∃ e' : A, e = (p : A) ^ k * e' := by
  induction k with
  | zero => exact fun e _ _ => ⟨e, by simp⟩
  | succ k ih =>
    intro e r h
    obtain ⟨e₁, rfl⟩ := hd e ((p : R) ^ k * r) (by rw [h]; ring)
    have h1 : f e₁ = (p : R) ^ k * r := by
      rw [← sub_eq_zero]
      apply htf
      rw [map_mul, map_natCast] at h
      linear_combination h
    obtain ⟨e₂, rfl⟩ := ih e₁ r h1
    exact ⟨e₂, by ring⟩

theorem sat_closed {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (p : ℕ)
    (hA : IsPrecomplete (Ideal.span {(p : A)}) A)
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (hd : ∀ (e : A) (r : R), f e = (p : R) * r → ∃ e' : A, e = (p : A) * e') :
    (∀ (x : R) (e : A), (p : R) * x = f e → ∃ e', x = f e') ∧
      ∀ x : R, (∀ k : ℕ, ∃ e r, x - f e = (p : R) ^ k * r) → ∃ e, x = f e := by
  refine ⟨fun x e h => ?_, fun x h => ?_⟩
  · obtain ⟨e', rfl⟩ := hd e x h.symm
    refine ⟨e', ?_⟩
    rw [← sub_eq_zero]
    apply htf
    rw [map_mul, map_natCast] at h
    linear_combination h
  · choose e r her using h
    have key : ∀ (n : ℕ) (a b : A),
        a ≡ b [SMOD (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A)] ↔ (p : A) ^ n ∣ a - b := by
      intro n a b
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
    obtain ⟨L, hL⟩ := hA.prec (f := e) (by
      intro m n hmn
      rw [key]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine pow_dvd_of_map f p htf hd m _ ((p : R) ^ k * r (m + k) - r m) ?_
      rw [map_sub]
      linear_combination her (m + k) - her m)
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    refine hsep _ fun k => ?_
    obtain ⟨c, hc⟩ := (key _ _ _).1 (hL k)
    have h1 := congrArg f hc
    rw [map_sub, map_mul, map_pow, map_natCast] at h1
    exact ⟨r k + f c, by linear_combination her k + h1⟩

theorem ioE_saturated_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (x : RW LL) (e : W.EE), (l : RW LL) * x = E.tie.ioE e → ∃ e', x = E.tie.ioE e') ∧ ∀ x : RW LL, (∀ k : ℕ, ∃ e r, x - E.tie.ioE e = (l : RW LL) ^ k * r) → ∃ e, x = E.tie.ioE e := by
  intro l _ P AI K s LL h W E
  have hc : IsAdicComplete (Ideal.span {(l : W.EE)}) W.EE := by
    have := W.EE_complete
    rwa [P.PD_p K] at this
  exact sat_closed (E.tie.ioE : W.EE →+* RW LL) l hc.toIsPrecomplete
    (LAdic.ladic_RW l LL).1 (LAdic.ladic_RW l LL).2.1 (_root_.GlobalTheory.Decompl.near_ioE l P AI K s LL h W E).2

end GlobalTheory.Decompl.Sat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisPhiPowEigenvectorDoubleSeries
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem exists_acris_Lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  intro l _ h y hh hy
  choose w hw hθ using fun k => _root_.GlobalTheory.PSer.series_acris l h (y k) hh (hy k)
  haveI : IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := (GlobalTheory.MemLoc.acris_basic l).1
  obtain ⟨W, hW, hsum⟩ := _root_.GlobalTheory.abssum_eigen_lim l (Acris l) (GlobalTheory.MemLoc.phiA l) h w hw
  refine ⟨W, hW, fun Θ hΘ htm j => ?_⟩
  set φ := GlobalTheory.MemLoc.phiA l
  have hS := hsum (Θ.comp (φ ^ j)) (fun a => hΘ _)
  simp only [RingHom.coe_comp, RingHom.coe_pow, Function.comp_apply] at hS
  unfold abelian₂
  rw [← hS.tsum_eq]
  congr 1
  funext k
  rw [hθ k Θ hΘ htm j]

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfSpanOfStrict
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.TopBasisCons

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type} {b : ι → A}


variable (s I b) in
def Approx (x : A) (f : ι → S) : Prop :=
  ∀ n : ℕ, ∃ F : Finset ι, (∀ i, i ∉ F → f i ∈ I ^ n) ∧ x - ∑ i ∈ F, s (f i) * b i ∈ (I ^ n).map s

theorem smodEq_iff (x y : S) (n : ℕ) : x ≡ y [SMOD (I ^ n • ⊤ : Submodule S S)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem sum_sub_sum_mem {f : ι → S} {n : ℕ} {F G : Finset ι} (hF : ∀ i, i ∉ F → f i ∈ I ^ n)
    (hG : ∀ i, i ∉ G → f i ∈ I ^ n) :
    ∑ i ∈ F, s (f i) * b i - ∑ i ∈ G, s (f i) * b i ∈ (I ^ n).map s := by
  classical
  rw [← Finset.sum_sdiff (Finset.inter_subset_left : F ∩ G ⊆ F),
    ← Finset.sum_sdiff (Finset.inter_subset_right : F ∩ G ⊆ G), add_sub_add_right_eq_sub]
  refine sub_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hG i fun h => ?_)))
    (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i fun h => ?_)))
  · exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 hi).1, h⟩)
  · exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_inter.2 ⟨h, (Finset.mem_sdiff.1 hi).1⟩)

theorem Approx.approx {x : A} {f : ι → S} (h : Approx s I b x f) (n : ℕ) (F : Finset ι)
    (hF : ∀ i, i ∉ F → f i ∈ I ^ n) : x - ∑ i ∈ F, s (f i) * b i ∈ (I ^ n).map s := by
  obtain ⟨G, hG, hx⟩ := h n
  have := sub_mem hx (sum_sub_sum_mem (s := s) (b := b) hF hG)
  rwa [sub_sub_sub_cancel_right] at this

theorem Approx.finite {x : A} {f : ι → S} (h : Approx s I b x f) (n : ℕ) : {i | f i ∉ I ^ n}.Finite := by
  obtain ⟨F, hF, -⟩ := h n
  exact F.finite_toSet.subset fun i hi => by_contra fun h' => hi (hF i h')

theorem Approx.add {x y : A} {f g : ι → S} (hx : Approx s I b x f) (hy : Approx s I b y g) :
    Approx s I b (x + y) (f + g) := by
  classical
  intro n
  obtain ⟨F, hF, -⟩ := hx n
  obtain ⟨G, hG, -⟩ := hy n
  refine ⟨F ∪ G, fun i hi => ?_, ?_⟩
  · simp only [Finset.mem_union, not_or] at hi
    exact add_mem (hF i hi.1) (hG i hi.2)
  · have h1 := hx.approx n (F ∪ G) fun i hi => hF i fun h => hi (Finset.mem_union_left _ h)
    have h2 := hy.approx n (F ∪ G) fun i hi => hG i fun h => hi (Finset.mem_union_right _ h)
    convert add_mem h1 h2 using 1
    simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
    ring

theorem Approx.mul {x : A} {f : ι → S} (hx : Approx s I b x f) (a : S) :
    Approx s I b (s a * x) (fun i => a * f i) := by
  intro n
  obtain ⟨F, hF, h⟩ := hx n
  refine ⟨F, fun i hi => Ideal.mul_mem_left _ _ (hF i hi), ?_⟩
  convert Ideal.mul_mem_left _ (s a) h using 1
  simp only [map_mul, mul_sub, Finset.mul_sum, mul_assoc]

theorem approx_single [DecidableEq ι] (i : ι) : Approx s I b (b i) (Pi.single i 1) := by
  intro n
  refine ⟨{i}, fun j hj => ?_, by simp⟩
  rw [Pi.single_eq_of_ne (by simpa using hj)]
  exact zero_mem _

theorem Approx.eq_zero (hH : IsHausdorff I S)
    (hst : ∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n)
    {h : ι → S} (hh : Approx s I b 0 h) : h = 0 := by
  classical
  funext i
  refine hH.haus (h i) fun n => ?_
  rw [smodEq_iff, sub_zero]
  obtain ⟨m, hm⟩ := hst n
  obtain ⟨F, hF, hs⟩ := hh (max n m)
  by_cases hi : i ∈ F
  · have key := hm (Finsupp.onFinset F (fun j => if j ∈ F then h j else 0)
      (fun j hj => by by_contra hj'; simp [hj'] at hj)) ?_ i
    · simpa [hi] using key
    · rw [Finsupp.onFinset_sum _ (fun j => by simp)]
      have e : ∑ j ∈ F, s (if j ∈ F then h j else 0) * b j = -(0 - ∑ j ∈ F, s (h j) * b j) := by
        rw [zero_sub, neg_neg]
        exact Finset.sum_congr rfl fun j hj => by rw [if_pos hj]
      rw [e]
      exact neg_mem (Ideal.map_mono (Ideal.pow_le_pow_right (le_max_right n m)) hs)
  · exact Ideal.pow_le_pow_right (le_max_left n m) (hF i hi)

end GlobalTheory.BSP.TopBasisCons

namespace GlobalTheory.BSP.TopBasisCons

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type} {b : ι → A}

theorem exists_step (hsp : ∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) (n : ℕ) (y : A)
    (hy : y ∈ (I ^ n).map s) : ∃ a : ι →₀ S, (∀ i, a i ∈ I ^ n) ∧
      y - a.sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s := by
  classical
  let T : A → Prop := fun y => ∃ a : ι →₀ S, (∀ i, a i ∈ I ^ n) ∧
      y - a.sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s
  have T0 : T 0 := ⟨0, fun _ => zero_mem _, by simp⟩
  have Tadd : ∀ y y', T y → T y' → T (y + y') := by
    rintro y y' ⟨a, ha, hy⟩ ⟨a', ha', hy'⟩
    refine ⟨a + a', fun i => add_mem (ha i) (ha' i), ?_⟩
    rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add (f := _), add_mul])]
    convert add_mem hy hy' using 1
    ring
  have T1 : ∀ t ∈ I ^ n, ∀ w : A, T (s t * w) := by
    intro t ht w
    obtain ⟨a, ha⟩ := hsp w
    refine ⟨t • a, fun i => by rw [Finsupp.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ ht, ?_⟩
    rw [Finsupp.sum_smul_index (fun _ => by simp)]
    have e : s t * w - a.sum (fun i c => s (t * c) * b i) = s t * (w - a.sum (fun i c => s c * b i)) := by
      rw [mul_sub, Finsupp.mul_sum]
      simp only [map_mul, mul_assoc]
    rw [e, Ideal.map_pow, pow_succ]
    exact Ideal.mul_mem_mul (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem s ht) ha
  have key : ∀ y' ∈ Submodule.span A (s '' ((I ^ n : Ideal S) : Set S)), ∀ z, T (z * y') := by
    intro y' hy'
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact fun z => by rw [mul_comm]; exact T1 t ht z
    | zero => exact fun z => by rw [mul_zero]; exact T0
    | add x x' _ _ hx hx' => exact fun z => by rw [mul_add]; exact Tadd _ _ (hx z) (hx' z)
    | smul a x _ hx => exact fun z => by rw [smul_eq_mul, ← mul_assoc]; exact hx (z * a)
  simpa using key y hy 1

theorem exists_approx (hS : IsPrecomplete I S) (g : ℕ → A → ι →₀ S)
    (hg1 : ∀ n y, y ∈ (I ^ n).map s → ∀ i, g n y i ∈ I ^ n)
    (hg2 : ∀ n y, y ∈ (I ^ n).map s → y - (g n y).sum (fun i c => s c * b i) ∈ (I ^ (n + 1)).map s) (x : A) :
    ∃ f, Approx s I b x f := by
  classical
  let r : ℕ → A := fun n => Nat.rec x (fun k rk => rk - (g k rk).sum (fun i c => s c * b i)) n
  have hrs : ∀ k, r (k + 1) = r k - (g k (r k)).sum (fun i c => s c * b i) := fun k => rfl
  have hrm : ∀ k, r k ∈ (I ^ k).map s := by
    intro k
    induction k with
    | zero => simp [r, Ideal.map_top]
    | succ k ih => rw [hrs]; exact hg2 k _ ih
  let a : ℕ → ι →₀ S := fun k => g k (r k)
  have ha : ∀ k i, a k i ∈ I ^ k := fun k => hg1 k _ (hrm k)
  have hrx : ∀ N, r N = x - ∑ k ∈ Finset.range N, (a k).sum (fun i c => s c * b i) := by
    intro N
    induction N with
    | zero => simp [r]
    | succ N ih => rw [hrs, Finset.sum_range_succ, ← sub_sub, ← ih]
  let P : ℕ → ι → S := fun N i => ∑ k ∈ Finset.range N, a k i
  have hP : ∀ i m n, m ≤ n → P n i - P m i ∈ I ^ m := by
    intro i m n hmn
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    exact Ideal.sum_mem _ fun k hk => Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (ha k i)
  have hlim : ∀ i, ∃ L, ∀ N, P N i - L ∈ I ^ N := by
    intro i
    obtain ⟨L, hL⟩ := hS.prec (f := fun N => P N i) fun {m n} hmn => by
      rw [smodEq_iff, ← neg_sub]; exact neg_mem (hP i m n hmn)
    exact ⟨L, fun N => (smodEq_iff _ _ _).1 (hL N)⟩
  choose f hf using hlim
  refine ⟨f, fun n => ?_⟩
  let F : Finset ι := (Finset.range n).biUnion fun k => (a k).support
  have hPF : ∀ i, i ∉ F → P n i = 0 := fun i hi => Finset.sum_eq_zero fun k hk => by
    by_contra h
    exact hi (Finset.mem_biUnion.2 ⟨k, hk, Finsupp.mem_support_iff.2 h⟩)
  refine ⟨F, fun i hi => ?_, ?_⟩
  · have := neg_mem (hf i n)
    rwa [hPF i hi, zero_sub, neg_neg] at this
  · have hsum : ∑ k ∈ Finset.range n, (a k).sum (fun i c => s c * b i) = ∑ i ∈ F, s (P n i) * b i := by
      rw [Finset.sum_congr rfl fun k hk => Finsupp.sum_of_support_subset (a k) (s := F)
        (fun i hi => Finset.mem_biUnion.2 ⟨k, hk, hi⟩) (fun i c => s c * b i) (fun _ _ => by simp),
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, map_sum, Finset.sum_mul]
    have e : x - ∑ i ∈ F, s (f i) * b i = r n + ∑ i ∈ F, s (P n i - f i) * b i := by
      rw [hrx, hsum]
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    exact add_mem (hrm n) (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hf i n)))

end GlobalTheory.BSP.TopBasisCons


open GlobalTheory.BSP.TopBasisCons in
theorem GlobalTheory.BSP.exists_topBasis_of_span_of_strict : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A)
    (I : Ideal S) (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 → I.FG → IsAdicComplete I S →
    IsAdicComplete (I.map s) A → (∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) →
    (∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n) →
    ∃ TB : TopBasis s I ι, TB.b = b := by
  intro S A _ _ s I ι b i₀ hb0 _ hS hA hsp hst
  classical
  choose! g hg1 hg2 using exists_step (s := s) (I := I) (b := b) hsp
  have hex : ∀ x, ∃ f, Approx s I b x f := exists_approx hS.toIsPrecomplete g hg1 hg2
  choose coef hcoef using hex
  have huniq : ∀ {x : A} {f g : ι → S}, Approx s I b x f → Approx s I b x g → f = g := by
    intro x f g hf hg
    have h := hf.add (hg.mul (-1))
    have e : x + s (-1) * x = 0 := by simp
    rw [e] at h
    have := h.eq_zero hS.toIsHausdorff hst
    funext i
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.zero_apply, neg_one_mul] at hi
    exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact hi)
  let c : ι → A →+ S := fun i =>
    AddMonoidHom.mk' (fun x => coef x i) fun x y => congrFun (huniq (hcoef (x + y)) ((hcoef x).add (hcoef y))) i
  refine ⟨⟨b, c, ?_, ?_, ?_, ?_, ?_, hA, i₀, hb0⟩, rfl⟩
  · intro i a x
    change coef (s a * x) i = a * coef x i
    rw [huniq (hcoef (s a * x)) ((hcoef x).mul a)]
  · intro i
    change coef (b i) i = 1
    rw [huniq (hcoef (b i)) (approx_single i)]
    simp
  · intro i j hij
    change coef (b j) i = 0
    rw [huniq (hcoef (b j)) (approx_single j)]
    exact Pi.single_eq_of_ne hij _
  · intro x n
    exact (hcoef x).finite n
  · intro x n F hF
    exact (hcoef x).approx n F hF
end
end

