module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory

theorem finrank_le_of_subset_closure_range {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (J : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hdense : (K : Set (PadicAlgCl l)) ⊆ closure (Set.range J)) :
    finrank ℚ_[l] ↥K ≤ finrank ℚ E := by
  classical
  let b := Module.finBasis ℚ E
  let S : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (Set.range fun k => J (b k))
  have hfd : FiniteDimensional ℚ_[l] S := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hcl : IsClosed (S : Set (PadicAlgCl l)) := Submodule.closed_of_finiteDimensional S
  have hsub : Set.range J ⊆ S := by
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine S.sum_mem fun k _ => ?_
    have e : J (b.repr x k • b k) = ((b.repr x k : ℚ) : ℚ_[l]) • J (b k) := by
      rw [Rat.smul_def, map_mul, map_ratCast, Algebra.smul_def, map_ratCast]
    rw [e]
    exact S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have hle : K.toSubalgebra.toSubmodule ≤ S := fun x hx => closure_minimal hsub hcl (hdense hx)
  have h1 : finrank ℚ_[l] ↥K.toSubalgebra.toSubmodule ≤ finrank ℚ_[l] S := Submodule.finrank_mono hle
  have h2 : finrank ℚ_[l] S ≤ finrank ℚ E := by
    have := finrank_range_le_card (R := ℚ_[l]) (fun k => J (b k))
    simpa [Set.finrank] using this
  exact le_trans h1 h2

theorem bridge_finrank_le (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≤ 4 * D.R.n := by
  have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h2 := finrank_le_of_subset_closure_range
    ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw.1 (D.nbr i w hw).j_dense
  have h3 : D.R.n = D.R.ord := rfl
  have h4 : finrank ℚ D.host.E = 4 * D.R.n := by rw [h1, h3]
  exact le_trans h2 h4.le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfFixedByDeltaGammaLifts
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.HerrClass

namespace GlobalTheory.RedDense

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_pred_sub_one_le {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l]) ^ (l - 1) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
  let u : ℤ_[l] := ⟨(χ g : ℚ_[l]), hχ.norm_le_one g⟩
  have hu : IsUnit u := PadicInt.isUnit_iff.2 (hχ.norm_eq_one g)
  have h3 : PadicInt.toZMod (u ^ (l - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one (hu.map _).ne_zero, sub_self]
  have h4 : u ^ (l - 1) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
    rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
    exact h3
  have h5 := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 h4
  rw [PadicInt.norm_def] at h5
  exact h5

theorem card_and_dense {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} {s : ℕ} (h2 : l ≠ 2)
    (hK : K.1 ≤ Ks K s)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    ¬ l ∣ W.DelF.card ∧ ∀ γ : W.Gam, (W.χΓ γ : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
      ∀ U : Subgroup ↥(GK K), IsClosed (U : Set ↥(GK K)) →
        (∀ g, (W.resΓ g ∈ W.DelF ∨ W.resΓ g = γ) → g ∈ U) → ∀ g, g ∈ U := by
  have hl : l.Prime := Fact.out
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨-, -, hG⟩ := cyc_basic l P.χQ hχ
  have hH0 : ∀ x ∈ Hinf K, x ∈ (K0 K).fixingSubgroup := fun x hx y =>
    hx ⟨y.1, (le_sup_left : K0 K ≤ Kinf K) y.2⟩
  have hH : Hinf K ≤ GK K := by
    intro x hx
    have h1 : x ∈ Gj K s := ((hG K x (hH0 x hx)).1 s).2 (by
      rw [(hG K x (hH0 x hx)).2.1 hx, Units.val_one, sub_self, norm_zero]
      positivity)
    exact fun y => h1 ⟨y.1, hK y.2⟩
  have hj : Lev l 1 := ⟨le_rfl, fun e => absurd e h2⟩
  have hN : ¬ l ∣ l - 1 := by
    have := hl.two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpow := norm_pow_pred_sub_one_le hχ
  have hN0 : l - 1 ≠ 0 := by have := hl.two_le; omega
  refine ⟨?_, fun γ hγ U hU hp g => ?_⟩
  · have htor : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := by
      intro δ hδ
      obtain ⟨g, rfl⟩ := W.resΓ_onto δ
      obtain ⟨k, hk, hk'⟩ := (W.DelF_def _).1 hδ
      rw [res_pow_eq_one_iff] at hk' ⊢
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      refine eq_one_of_pow hj (hpow g) hk.ne' ?_
      rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hk', Units.val_one, one_pow]
    have h1Δ : (1 : W.Gam) ∈ W.DelF := (mem_DelF_iff W _).2 (one_mem _)
    intro hdv
    haveI : Finite ↥(CommGroup.torsion W.Gam) := Nat.finite_of_card_ne_zero (by
      rw [card_torsion]; exact Finset.card_ne_zero.2 ⟨1, h1Δ⟩)
    rw [← card_torsion] at hdv
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hdv
    apply hN
    have h3 : orderOf x ∣ l - 1 :=
      orderOf_dvd_iff_pow_eq_one.2 (Subtype.ext (htor x ((mem_DelF_iff W _).2 x.2)))
    rwa [hx] at h3
  · have hmemΔ : ∀ g : ↥(GK K), P.χQ g ^ (l - 1) = 1 → W.resΓ g ∈ W.DelF := fun g hg =>
      (W.DelF_def _).2 ⟨l - 1, Nat.pos_of_ne_zero hN0, (res_pow_eq_one_iff W g _).2 hg⟩
    obtain ⟨γ', hγ'⟩ := W.resΓ_onto γ
    have hv : (P.χQ γ' : ℚ_[l]) = 1 + l := by
      apply (algebraMap ℚ_[l] ↥LL.1).injective
      rw [← chi_res W γ', hγ', hγ]
      simp
    have hn : ‖(P.χQ γ' : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [hv, add_sub_cancel_left, Padic.norm_p]
      simp
    refine mem_of_tors_gen ha hχ K hH hj hN hN (fun x _ => hpow x) (fun x _ hx => hx) U hU
      (fun x hx => hp x (Or.inl (hmemΔ x hx))) γ' (hp γ' (Or.inr hγ')) (fun x => ?_) g
    rw [norm_pow_sub_one hj hn.le hN, hn]
    exact hpow x

theorem exists_closed_stab {G Qp LL O k : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL] [Field k]
    [Algebra O k] (hO : IsOpen (Set.range (algebraMap O LL))) {c : O} (hc : algebraMap O LL c ≠ 0)
    (hk : algebraMap O k c = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (hq : Onto T A q) (t : Fin A.m → k) :
    ∃ U : Subgroup G, IsClosed (U : Set G) ∧ ∀ g, g ∈ U ↔ A.ρ g t = t := by
  obtain ⟨x, rfl⟩ := hq.1 t
  have hlc : IsLocallyConstant fun g => q (latRep T.L g x) :=
    GlobalTheory.FiniteAdm.isLocallyConstant_comp hO T.L.T T.L.fg T.L.span hc q
      (fun y => by rw [← algebraMap_smul k, hk, zero_smul]) _ (T.cont x)
  let U : Subgroup G :=
    { carrier := {g | A.ρ g (q x) = q x}
      mul_mem' := fun {a b} ha hb => by
        change A.ρ a (q x) = q x at ha
        change A.ρ b (q x) = q x at hb
        change A.ρ (a * b) (q x) = q x
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        change A.ρ a (q x) = q x at ha
        change A.ρ a⁻¹ (q x) = q x
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  refine ⟨U, ?_, fun g => Iff.rfl⟩
  have := hlc.isClosed_fiber (q x)
  simp only [hq.2] at this
  exact this

theorem fixed_of_fixed_lifts : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → (((S.W H).DelF.card : ℕ) : k) ≠ 0 ∧ ∀ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)), Onto T A q → ∀ t : Fin A.m → k, (∀ g, ((S.W H).resΓ g ∈ (S.W H).DelF ∨ (S.W H).resΓ g = γ) → A.ρ g t = t) → ∀ g, A.ρ g t = t := by
  intro l _ P AI H S k _ _ _ _
  have hl : l.Prime := Fact.out
  obtain ⟨h1, h2⟩ := card_and_dense AI S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1 (S.W H)
  refine ⟨fun h => h1 ((CharP.cast_eq_zero_iff k l _).1 h), fun γ hγ T A q hq t ht => ?_⟩
  haveI : IsTopologicalRing ↥S.LL.1 :=
    inferInstanceAs (IsTopologicalRing ↥S.LL.1.toSubalgebra.toSubring)
  obtain ⟨U, hU, hm⟩ := exists_closed_stab (c := (l : S.O)) (GlobalTheory.LocalIntegers.isOpen_integers l S.LL)
    (by rw [map_natCast]; exact Nat.cast_ne_zero.2 hl.ne_zero)
    (by rw [map_natCast, CharP.cast_eq_zero]) T A q hq t
  exact fun g => (hm g).1 (h2 γ hγ U hU (fun g hg => (hm g).2 (ht g hg)) g)

end GlobalTheory.RedDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplFrob

variable {l : ℕ} [Fact l.Prime]

theorem frobW_inclW (a : Ainf l) :
    frobW l (inclW l a) = inclW l (WittVector.map (frobenius (OCb l) l) a) := by
  ext n
  rw [coeff_frobW, coeff_inclW, coeff_inclW, WittVector.map_coeff, frobenius_def, map_pow]

theorem frob_inclR (LL : FinExt l) (a : RA LL) :
    ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a' := by
  refine ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]]
    WittVector.map (frobenius (OCb l) l) (crd (basisO LL) j a), ext_crd (basisO LL) fun i => ?_⟩
  rw [crd_φRW, crd_inclR, crd_inclR, crd_sum, frobW_inclW]

theorem nearPi_frob {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s m n : ℕ)
    (h : n ≤ m * l) (x : RW LL) (hx : NearPi AI LL s m x) : NearPi AI LL s n (φRW LL x) := by
  rw [nearPi_iff_crd] at hx ⊢
  intro i
  obtain ⟨c, hc⟩ := hx i
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  refine ⟨(AI.εroot s - 1) ^ k * c ^ l, ?_⟩
  rw [crd_φRW, coeff_frobW, hc, ← map_pow, mul_pow, ← pow_mul, hk, pow_add, mul_assoc]

theorem near_self {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (p : ℕ) (t : R) :
    Near ι p t 1 t := ⟨1, 0, by simp⟩

theorem not_isUnit_root_sub_one {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    ¬ IsUnit (AI.εroot s - 1) := fun h =>
  one_ne_zero ((GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 1
    fun m => (h.pow m).dvd)

theorem dvd_of_coeff {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) (z : ℤ_[l]) (c : OCb l)
    (h : (z • (1 : WCb l)).coeff 0 = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ 1 * c)) :
    (l : ℤ_[l]) ∣ z := by
  by_contra hz
  have hu : IsUnit z := by
    rw [PadicInt.isUnit_iff]
    rw [← PadicInt.norm_lt_one_iff_dvd] at hz
    exact le_antisymm z.2 (not_lt.1 hz)
  have h1 : z • (1 : WCb l) = inclW l (zlW l (OCb l) z) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (map_zlW l (algebraMap (OCb l) (Cb l)) z).symm
  rw [h1, coeff_inclW, pow_one] at h
  have h2 := IsFractionRing.injective (OCb l) (Cb l) h
  have h3 : IsUnit ((zlW l (OCb l) z).coeff 0) :=
    (hu.map (zlW l (OCb l))).map (WittVector.constantCoeff : Ainf l →+* OCb l)
  rw [h2] at h3
  exact not_isUnit_root_sub_one AI s (isUnit_of_mul_isUnit_left h3)

theorem const_dvd {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (o : ↥(OL LL))
    (h : NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o)) :
    ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  rw [nearPi_iff_crd] at h
  have h1 : ∀ i, (l : ℤ_[l]) ∣ (basisO LL).repr o i := fun i => by
    obtain ⟨c, hc⟩ := h i
    exact dvd_of_coeff AI s _ c hc
  choose d hd using h1
  refine ⟨∑ i, d i • basisO LL i, ?_⟩
  rw [Finset.mul_sum]
  refine ((basisO LL).sum_repr o).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hd, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem frobenius_and_constants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ),
    (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧
    NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧
    (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧
    ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) →
      ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  intro l hl P AI LL s
  refine ⟨frob_inclR LL, ?_, fun m x hx => ?_, const_dvd AI LL s⟩
  · exact nearPi_frob AI LL s 1 2 (by rw [one_mul]; exact hl.out.two_le) _ (near_self _ _ _)
  · exact nearPi_frob AI LL s m m (Nat.le_mul_of_pos_right m hl.out.pos) x hx

end GlobalTheory.DecomplFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusFixedTensorEqConstant
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedFixed

theorem exists_lift {Z O W k T : Type} [CommRing Z] [CommRing O] [CommRing W] [CommRing k] [CommRing T]
    [Algebra Z O] [Algebra Z W] [Algebra O k] (a : k →+* T) (b : W →+* T)
    (h : ∀ z : Z, a (algebraMap O k (algebraMap Z O z)) = b (algebraMap Z W z)) :
    ∃ F : k ⊗[O] (O ⊗[Z] W) →+* T, ∀ c o w, F (c ⊗ₜ (o ⊗ₜ w)) = a c * (a (algebraMap O k o) * b w) := by
  let _ : Algebra O T := (a.comp (algebraMap O k)).toAlgebra
  let _ : Algebra Z T := (b.comp (algebraMap Z W)).toAlgebra
  have : IsScalarTower Z O T := IsScalarTower.of_algebraMap_eq fun z => (h z).symm
  let b' : W →ₐ[Z] T := { b with commutes' := fun _ => rfl }
  let a' : k →ₐ[O] T := { a with commutes' := fun _ => rfl }
  let F₁ : O ⊗[Z] W →ₐ[O] T :=
    Algebra.TensorProduct.lift (Algebra.ofId O T) b' fun _ _ => Commute.all _ _
  exact ⟨(Algebra.TensorProduct.lift a' F₁ fun _ _ => Commute.all _ _).toRingHom, fun c o w => rfl⟩

variable {l : ℕ} [Fact l.Prime]

theorem map_padicInt {R : Type} [CommRing R] [CharP R l] [Algebra (ZMod l) R] (f : ℤ_[l] →+* R) (z : ℤ_[l]) :
    f z = algebraMap (ZMod l) R (PadicInt.toZMod z) := by
  have h := PadicInt.toZMod_spec z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  have h2 := congrArg f hy
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_sub, sub_eq_zero] at h2
  rw [h2]
  generalize PadicInt.toZMod z = n
  rw [ZMod.cast_eq_val, map_natCast, ← map_natCast (algebraMap (ZMod l) R), ZMod.natCast_zmod_val]

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem fixed_tensor {k C : Type} [Field k] [Field C] [CharP C l] [Algebra (ZMod l) k] [Algebra (ZMod l) C]
    (f : C →ₗ[ZMod l] C) (hf : ∀ x, f x = x ^ l) (y : k ⊗[ZMod l] C) (hy : f.lTensor k y = y) :
    ∃ c : k, y = c ⊗ₜ[ZMod l] (1 : C) := by
  have hex : Function.Exact (Algebra.linearMap (ZMod l) C) (f - LinearMap.id : C →ₗ[ZMod l] C) := by
    intro x
    rw [LinearMap.sub_apply, hf, sub_eq_zero, LinearMap.id_apply]
    constructor
    · intro h
      have h2 := (Subfield.mem_bot_iff_pow_eq_self C l).2 h
      have h3 : (⊥ : Subfield C) ≤ (algebraMap (ZMod l) C).fieldRange := bot_le
      exact h3 h2
    · rintro ⟨a, rfl⟩
      rw [Algebra.linearMap_apply, ← map_pow, ZMod.pow_card]
  obtain ⟨t, ht⟩ := (Module.Flat.lTensor_exact k hex y).1 (by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, hy, LinearMap.lTensor_id, LinearMap.id_apply, sub_self])
  refine ⟨TensorProduct.rid (ZMod l) k t, ?_⟩
  rw [← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add a b ha hb => simp [ha, hb, TensorProduct.add_tmul]

theorem fixed_witt {O k C : Type} [CommRing O] [Field k] [Field C] [CharP k l] [CharP C l] [PerfectRing C l]
    [Algebra ℤ_[l] O] [Algebra O k] [Algebra ℤ_[l] (WittVector l C)]
    (φ : WittVector l C →ₐ[ℤ_[l]] WittVector l C) (hφ0 : ∀ w, (φ w).coeff 0 = w.coeff 0 ^ l)
    (x : k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C))
    (hx : Algebra.TensorProduct.map (AlgHom.id k k) (Algebra.TensorProduct.map (AlgHom.id O O) φ) x = x) :
    ∃ c : k, x = algebraMap k (k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)) c := by
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  let _ : Algebra (ZMod l) C := ZMod.algebra C l
  obtain ⟨F, hF⟩ := exists_lift (Z := ℤ_[l]) (O := O) (W := WittVector l C) (k := k) (T := k ⊗[ZMod l] C)
    Algebra.TensorProduct.includeLeftRingHom
    ((Algebra.TensorProduct.includeRight : C →ₐ[ZMod l] k ⊗[ZMod l] C).toRingHom.comp
      WittVector.constantCoeff) (fun z => by
      have h1 := map_padicInt ((algebraMap O k).comp (algebraMap ℤ_[l] O)) z
      have h2 := map_padicInt ((WittVector.constantCoeff : WittVector l C →+* C).comp (algebraMap ℤ_[l] (WittVector l C))) z
      rw [RingHom.comp_apply] at h1 h2
      rw [RingHom.comp_apply, h1, h2]
      simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  have hF' : ∀ (c : k) (o : O) (w : WittVector l C),
      F (c ⊗ₜ (o ⊗ₜ w)) = (o • c) ⊗ₜ[ZMod l] w.coeff 0 := by
    intro c o w
    rw [hF]
    simp [Algebra.smul_def, mul_comm]
  let j : WittVector l C →+* k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) :=
    (Algebra.TensorProduct.includeRight : O ⊗[ℤ_[l]] WittVector l C →ₐ[O] k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : WittVector l C →ₐ[ℤ_[l]] (O ⊗[ℤ_[l]] WittVector l C)).toRingHom
  have hl : ((l : ℕ) : k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)) = 0 := by
    rw [← map_natCast (algebraMap k (k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C))), CharP.cast_eq_zero, map_zero]
  have hs : Function.Surjective (WittVector.constantCoeff : WittVector l C →+* C) := fun c =>
    ⟨WittVector.teichmuller l c, by simp⟩
  let g : C →+* k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) := RingHom.liftOfSurjective _ hs ⟨j, by
    rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff]
    change j _ = 0
    rw [map_natCast, hl]⟩
  have hg : ∀ w : WittVector l C, g (w.coeff 0) = (1 : k) ⊗ₜ ((1 : O) ⊗ₜ w) := fun w =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ w
  let G : k ⊗[ZMod l] C →+ k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) := TensorProduct.liftAddHom
    { toFun := fun c =>
        { toFun := fun t => c • g t
          map_zero' := by simp
          map_add' := fun _ _ => by simp }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_smul] }
    (fun n c t => by
      obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective n
      change ((m : ZMod l) • c) • g t = c • g ((m : ZMod l) • t)
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul, smul_assoc, smul_comm])
  have hG : ∀ c t, G (c ⊗ₜ t) = c • g t := fun _ _ => rfl
  have hGF : ∀ y, G (F y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | tmul c r =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), ha, hb]
      | tmul o w =>
        rw [hF', hG, hg, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let f : C →ₗ[ZMod l] C := (frobenius C l).toAddMonoidHom.toZModLinearMap l
  have hφ : ∀ y, F (Algebra.TensorProduct.map (AlgHom.id k k) (Algebra.TensorProduct.map (AlgHom.id O O) φ) y) = f.lTensor k (F y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    | tmul c r =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
      | tmul o w =>
        rw [hF']
        exact (hF' c o (φ w)).trans (by rw [hφ0]; rfl)
  obtain ⟨c, hc⟩ := fixed_tensor f (fun _ => rfl) (F x) (by rw [← hφ, hx])
  refine ⟨c, ?_⟩
  rw [← hGF x, hc, hG, map_one, Algebra.algebraMap_eq_smul_one]

theorem fixed_red : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] [CharP k l] (x : k ⊗[↥(OL LL)] RW LL), Algebra.TensorProduct.map (AlgHom.id k k) (φRW LL) x = x → ∃ c : k, x = algebraMap k (k ⊗[↥(OL LL)] RW LL) c := by
  intro l _ LL k _ _ _ x hx
  have := perfect_Cb (l := l)
  exact fixed_witt (frobW l) (fun _ => rfl) x hx

end GlobalTheory.RedFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableComm
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem phiV_crisIncl_comm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (w : V ⊗[ℚ_[l]] P.R.B), phiV P ℚ_[l] V (crisIncl P ℚ_[l] V w) = crisIncl P ℚ_[l] V (φVB (P.PD K) (LL := ℚ_[l]) (V := V) w) := by
  intro l _ P K V _ _ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [crisIncl_tmul, phiV_tmul, phiSt_C, φVB, AlgebraTensorModule.map_tmul,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, P.PD_φ K b]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisInvComplexPadicPeriodMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem GlobalTheory.PMon.galois_inv_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ g : ↥(GK K), ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) * (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) := by
  intro l _ n _ _ K ρ M h g
  set σ := Formalism.Per.σC (g : GQ l) with hσ
  have h1 : (M : Matrix n n ℂ_[l]).map σ * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h2 := h g
  set R := (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l])
  have h3 : R = (M : Matrix n n ℂ_[l]) * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ := by
    calc R = R * ((M : Matrix n n ℂ_[l]).map σ * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h2]
  rw [h3, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeComapOfExactFlatStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_comap_of_exact_flat : ∀ (A E : Type) [CommRing A] [CommRing E] [Algebra A E] [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂] [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂] (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂), Function.Injective j → Function.Exact j q → Function.Surjective q → IsBaseChange E N₁.subtype → IsBaseChange E N₂.subtype → (∀ x ∈ N₁, q x ∈ N₂) → IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  first | exact @GlobalTheory.isBaseChange_comap_of_exact | exact GlobalTheory.isBaseChange_comap_of_exact | (intros; apply GlobalTheory.isBaseChange_comap_of_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationFrobeniusMemUpToQPowerStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachSaturation_frobenius_mem_up_to_Q_power : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  first | exact @GlobalTheory.NL.PhiSat.φD_satM_Q | exact GlobalTheory.NL.PhiSat.φD_satM_Q | (intros; apply GlobalTheory.NL.PhiSat.φD_satM_Q <;> assumption)
end

