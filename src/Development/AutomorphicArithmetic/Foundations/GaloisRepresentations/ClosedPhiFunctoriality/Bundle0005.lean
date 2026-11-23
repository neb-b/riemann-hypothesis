module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FixOfHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem fix_aux {A S : Type} [CommSemiring A] [Semiring S] [Algebra A S] (φ : S →ₐ[A] S) (x y : ℕ) (c : S)
    (h : (φ ^ y) c = (φ ^ x) c) : (φ ^ ((x : ℤ) - y).natAbs) ((φ ^ y) c) = (φ ^ y) c := by
  rcases le_total x y with hxy | hxy
  · have e : ((x : ℤ) - y).natAbs = y - x := by omega
    rw [e, h, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hxy, h]
  · have e : ((x : ℤ) - y).natAbs = x - y := by omega
    rw [e, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hxy, h]

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixOf_holds :
    FixOf := by
  intro l _ E Ω _ _ _ _ _ w A h O _ _ _ Bw hj g c hc
  obtain ⟨a, b, hσ⟩ := g.2
  have hal : (alpha l g) = ((resDeg l w * a : ℕ) : ℤ) - ((resDeg l w * b : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨c', rfl⟩ := (Algebra.IsAlgebraic.algHom_bijective (frobUr l ^ (resDeg l w * b))).2 c
  have h1 := weilToGK_frobUr hj g hσ c'
  rw [mem_GK.mp (weilToGK Bw h g).2 _ hc] at h1
  rw [hal]
  exact fix_aux _ _ _ _ (Subtype.ext h1)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.LinkOp
section
noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem linkOp_holds : LinkOp2 := by
  intro R _ π s d d' W Z Zs W₁ Z₁ Zs₁ Pm R₀ h1 h2 hA hB i j
  have hl : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) R) (A : Matrix (Fin n) (Fin p) R),
      (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (X * A) i j := by
    intro m n p X A h i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (h k j).mul_left _
  have hr : ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R) (Y : Matrix (Fin n) (Fin p) R),
      (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (A * Y) i j := by
    intro m n p A Y h i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (h i k).mul_right _
  have e1 : W * Zs * Pm * Z₁ * Zs₁ = s • (W * Zs * Pm) := by
    rw [Matrix.mul_assoc (W * Zs * Pm), h2, Matrix.mul_smul, Matrix.mul_one]
  have e2 : W * Zs * Z * R₀ * Zs₁ = s • (W * R₀ * Zs₁) := by
    rw [Matrix.mul_assoc W Zs Z, h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.smul_mul]
  have key : s • (W * Zs) * Pm - Pm * s • (W₁ * Zs₁) =
      W * Zs * (Pm * Z₁ - Z * R₀) * Zs₁ - s • ((Pm * W₁ - W * R₀) * Zs₁) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, smul_sub, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [e1, e2]
    abel
  rw [key, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_sub (hr _ _ (hl _ _ hA) i j) ((hr _ _ hB i j).mul_left s)

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.LinkZHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkZ_holds :
    LinkA → LinkQ → LinkZ := by
  intro hA hQ l _ K bk τ hτ N M
  obtain ⟨n, hn⟩ := hQ l K bk N M
  refine ⟨max n M, ?_⟩
  intro k d d' ρ ρ' F F' Y Y₁ hY hY₁ Q Q' Q₁ Q₁' hS hS₁ Pi R hL
  obtain ⟨h1, h2⟩ := hA l K bk τ hτ N d d' (max n M) ρ ρ' F F' Y Y₁ hY hY₁ Pi R hL
  have hfz : ∀ z : ℤ_[l], fI l (Per.zA l z) = zC l z := fun z => by
    have h := (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z
    simp only [fI, zC, RingHom.comp_apply]
    rw [← GlobalTheory.RingBasics.φA_apply, h]
  have hfe : ∀ s : bk.S, fI l (bk.ev s) = fA bk s := fun s => by
    simp only [fI, fA, RingHom.comp_apply, bk.ev_frob]
  have hlM : ∀ i j, (l : Per.Acris l) ^ M ∣
      (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) i j := by
    intro i j
    have h := map_dvd (fI l) (h1 i j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, hfz, hfe,
      map_pow, map_natCast] at h ⊢
    exact (pow_dvd_pow _ (le_max_right _ _)).trans h
  have h3 := hn k d d' F.A F'.A F'.A' Q Q' Q₁ Q₁' R F'.A_mul hS hS₁
    (fun i j => (pow_dvd_pow _ (le_max_left _ _)).trans (h2 i j))
  intro i j
  have e : Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk) =
      (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) * Q₁ +
        Y.map (fI l) * (R.map (fA bk) * Q₁ - Q * R.map (f0 bk)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact dvd_add (Finset.dvd_sum fun x _ => (hlM i x).mul_right _)
    (Finset.dvd_sum fun x _ => (h3 x j).mul_left _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.OpExHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem phi_zC (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ) (z : ℤ_[l]) :
    (phiA l ^ n) (zC l z) = zC l z := by
  have h1 : phiA l (zC l z) = zC l z := by
    have h := (_root_.GlobalTheory.AcrisFrobE.main l K bk).2.2.2.1 (Per.zA l z)
    have h2 : WittVector.frobenius (Per.zA l z) = Per.zA l z := by
      rw [← GlobalTheory.RingBasics.φA_apply]; exact (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z
    rw [h2] at h
    exact h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    change (phiA l ^ n) (phiA l (zC l z)) = _
    rw [h1, ih]

private theorem map_link (hFix : FixW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (n : ℕ) (hn : FixUr K n) (d d' M : ℕ) (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (R : Matrix (Fin d) (Fin d') bk.S) (Z : Matrix (Fin d) (Fin d) (Per.Acris l)) (Z₁ : Matrix (Fin d') (Fin d') (Per.Acris l))
    (h : ∀ i j, (l : Per.Acris l) ^ M ∣ (Pi.map (zC l) * Z₁ - Z * R.map (f0 bk)) i j) :
    ∀ i j, (l : Per.Acris l) ^ M ∣
      (Pi.map (zC l) * Z₁.map ⇑(phiA l ^ n) - Z.map ⇑(phiA l ^ n) * R.map (f0 bk)) i j := by
  intro i j
  have hP : (Pi.map (zC l)).map ⇑(phiA l ^ n) = Pi.map (zC l) := by
    ext a b; simp only [Matrix.map_apply]; exact phi_zC l K bk n _
  have hR : (R.map (f0 bk)).map ⇑(phiA l ^ n) = R.map (f0 bk) := by
    ext a b; simp only [Matrix.map_apply]; exact hFix l K bk P AI T n hn _
  have h1 := map_dvd (phiA l ^ n) (h i j)
  rw [map_pow, map_natCast] at h1
  have h2 : (phiA l ^ n) ((Pi.map (zC l) * Z₁ - Z * R.map (f0 bk)) i j) =
      (Pi.map (zC l) * Z₁.map ⇑(phiA l ^ n) - Z.map ⇑(phiA l ^ n) * R.map (f0 bk)) i j := by
    have h3 : (Pi.map (zC l) * Z₁ - Z * R.map (f0 bk)).map ⇑(phiA l ^ n) =
        Pi.map (zC l) * Z₁.map ⇑(phiA l ^ n) - Z.map ⇑(phiA l ^ n) * R.map (f0 bk) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, hP, hR]
    rw [← h3, Matrix.map_apply]
  rwa [h2] at h1

private theorem one (hInvQ : InvQ) (hInvU : InvU) (hOp : OpOne2) (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l)
    (hτ : bk.IsPer τ) (N k n₁ n₂ : ℕ)
    (hk : ∀ (d : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S),
      A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → ∃ Q Q', IsSecQ bk N k A Q Q')
    (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (G : Frame bk N d fun g => (ρ g).val) (hG : G.IsCr) :
    ∃ (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)),
      Y.map (inclW l) = inclW l τ ^ N • G.T ∧ IsSecQ bk N k G.A Q Q' ∧
      (Y.map (fI l) * Q) * (Q' * Y'.map (fI l)) =
        (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
      (Q' * Y'.map (fI l)) * (Y.map (fI l) * Q) =
        (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
      IsUnit (iB l ((phiA l ^ n₂) (fI l τ) ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) (fI l τ) ^ N)) ∧
      IsOp2 ρ n₁ n₂ (iB l ((phiA l ^ n₂) (fI l τ) ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) (fI l τ) ^ N))
        (((phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
          ((Y.map (fI l) * Q).map ⇑(phiA l ^ n₁) * (Q' * Y'.map (fI l)).map ⇑(phiA l ^ n₂))).map (iB l)) := by
  obtain ⟨Y, Y', hY, hYY⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N d _ G.toPre
  obtain ⟨Q, Q', hQ⟩ := hk d G.A G.A' G.A_mul
  have hinv := hInvQ l K bk τ hτ N k d ρ G hG Q Q' hQ
  have hyy : Y.map (fI l) * Y'.map (fI l) = fI l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, hYY, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  obtain ⟨U, hU, hUe⟩ := (hInvU l K bk τ hτ).2 N k d ρ G Y Y' Q Q' hY hYY hQ.mul hinv
  exact ⟨Y, Y', Q, Q', hY, hQ,
    hOp l (fI l τ) (hInvU l K bk τ hτ).1 K N k n₁ n₂ d ρ (Y.map (fI l)) (Y'.map (fI l)) Q Q' U hyy hQ.mul hU hUe⟩

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.opEx_holds :
    SecU → InvQ → InvU → LinkZ → LinkOp2 → FixW → OpOne2 → OpEx2 := by
  intro hSec hInvQ hInvU hLinkZ hLinkOp hFix hOp l _ K bk τ hτ P AI T n₁ n₂ hn₁ hn₂ d N ρ tw F F₀ r hF hF₀ hlink
  obtain ⟨k, hk⟩ := hSec l K bk N
  obtain ⟨Y₀, Y₀', Q₀, Q₀', hY₀, hQ₀, a1, a2, a3, a4⟩ :=
    one hInvQ hInvU hOp l K bk τ hτ N k n₁ n₂ hk d ρ F₀ hF₀
  choose Y Y' Q Q' hY hQ b1 b2 b3 b4 using fun m =>
    one hInvQ hInvU hOp l K bk τ hτ N k n₁ n₂ hk (tw.d' m) (tw.ρ' m) (F m) (hF m)
  refine ⟨_, (phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
      ((Y₀.map (fI l) * Q₀).map ⇑(phiA l ^ n₁) * (Q₀' * Y₀'.map (fI l)).map ⇑(phiA l ^ n₂)),
    fun m => (phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
      (((Y m).map (fI l) * Q m).map ⇑(phiA l ^ n₁) * (Q' m * (Y' m).map (fI l)).map ⇑(phiA l ^ n₂)),
    a3, a4, b4, ?_⟩
  intro M
  obtain ⟨n, hn⟩ := hLinkZ l K bk τ hτ N M
  obtain ⟨m, hm, R, -, hdiv, -⟩ := hlink (max n M)
  refine ⟨m, le_trans (le_max_right _ _) hm, ?_⟩
  have hd : ∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - F₀.T * R.map bk.evW) i j :=
    fun i j => (pow_dvd_pow _ (le_max_left _ _)).trans (hdiv i j)
  have h0 := hn k d (tw.d' m) _ _ F₀ (F m) Y₀ (Y m) hY₀ (hY m) Q₀ Q₀' (Q m) (Q' m) hQ₀ (hQ m) (tw.Pi m) R hd
  have h1 := map_link hFix l K bk P AI T n₁ hn₁ d (tw.d' m) M (tw.Pi m) R _ _ h0
  have h2 := map_link hFix l K bk P AI T n₂ hn₂ d (tw.d' m) M (tw.Pi m) R _ _ h0
  have e1 : (Q₀' * Y₀'.map (fI l)).map ⇑(phiA l ^ n₂) * (Y₀.map (fI l) * Q₀).map ⇑(phiA l ^ n₂) =
      (phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, a2, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : ((Y m).map (fI l) * Q m).map ⇑(phiA l ^ n₂) * (Q' m * (Y' m).map (fI l)).map ⇑(phiA l ^ n₂) =
      (phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
        (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Per.Acris l)) := by
    rw [← Matrix.map_mul, b1 m, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
  exact hLinkOp (Per.Acris l) ((l : Per.Acris l) ^ M) _ d (tw.d' m) _ _ _ _ _ _ ((tw.Pi m).map (zC l)) (R.map (f0 bk))
    e1 e2 h2 h1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.OpOneHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem opOne_comm {A B : Type*} [CommRing A] [CommRing B] (i : A →+* B) (hi : Function.Injective i) {d : ℕ}
    (M M' : Matrix (Fin d) (Fin d) A) (c : A) (hc : IsUnit (i c))
    (h : M * M' = c • (1 : Matrix (Fin d) (Fin d) A)) : M' * M = c • (1 : Matrix (Fin d) (Fin d) A) := by
  obtain ⟨u, hu⟩ := hc
  have h1 : M.map i * M'.map i = i c • (1 : Matrix (Fin d) (Fin d) B) := by
    rw [← Matrix.map_mul, h]
    ext a b
    simp [Matrix.smul_apply, Matrix.one_apply, apply_ite i]
  have h2 : M.map i * (((u⁻¹ : Bˣ) : B) • M'.map i) = 1 := by
    rw [Matrix.mul_smul, h1, ← hu, smul_smul, Units.inv_mul, one_smul]
  have h3 := mul_eq_one_comm.mp h2
  have h4 : M'.map i * M.map i = i c • (1 : Matrix (Fin d) (Fin d) B) := by
    rw [Matrix.smul_mul] at h3
    have := congrArg (fun X => (u : B) • X) h3
    simp only [smul_smul, Units.mul_inv, one_smul] at this
    rw [this, hu]
  ext a b
  apply hi
  have := congrFun (congrFun h4 a) b
  rw [← Matrix.map_mul] at this
  simpa [Matrix.smul_apply, Matrix.one_apply, apply_ite i] using this

private theorem opOne_core {B : Type*} [CommRing B] {d : ℕ} (φ₁ φ₂ : B →+* B) (Z Zs U : Matrix (Fin d) (Fin d) B)
    (a L : B) (N : ℕ) (hL : φ₂ L = L) (ht : IsUnit (φ₂ a))
    (hU : a ^ N • U = Z) (hZ : Zs * Z = (a ^ (2 * N) * L) • (1 : Matrix (Fin d) (Fin d) B)) :
    (φ₂ (a ^ (2 * N) * L) • (Z.map φ₁ * Zs.map φ₂)) * U.map φ₂ =
      (φ₂ a ^ (3 * N) * L ^ 2 * φ₁ a ^ N) • U.map φ₁ := by
  have hm : ∀ (φ : B →+* B), Z.map φ = φ a ^ N • U.map φ := by
    intro φ
    subst hU
    ext i j
    simp [Matrix.smul_apply]
  have hZZ : Zs.map φ₂ * Z.map φ₂ = φ₂ (a ^ (2 * N) * L) • (1 : Matrix (Fin d) (Fin d) B) := by
    rw [← Matrix.map_mul, hZ]
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply, apply_ite φ₂]
  have hs : φ₂ (a ^ (2 * N) * L) = φ₂ a ^ (2 * N) * L := by rw [map_mul, map_pow, hL]
  apply (ht.pow N).smul_left_cancel.mp
  calc φ₂ a ^ N • ((φ₂ (a ^ (2 * N) * L) • (Z.map φ₁ * Zs.map φ₂)) * U.map φ₂)
      = φ₂ (a ^ (2 * N) * L) • (Z.map φ₁ * (Zs.map φ₂ * (φ₂ a ^ N • U.map φ₂))) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_smul, mul_comm]
    _ = (φ₂ (a ^ (2 * N) * L) * φ₂ (a ^ (2 * N) * L)) • Z.map φ₁ := by
        rw [← hm, hZZ, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    _ = φ₂ a ^ N • ((φ₂ a ^ (3 * N) * L ^ 2 * φ₁ a ^ N) • U.map φ₁) := by
        rw [hm φ₁, hs, smul_smul, smul_smul]
        congr 1
        ring

private theorem opOne_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (y : Per.Acris l) :
    (Per.φB l ^ n) (iB l y) = iB l ((phiA l ^ n) y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, RingHom.mul_def, RingHom.mul_def, RingHom.comp_apply, RingHom.comp_apply]
    rw [show Per.φB l (iB l y) = iB l (phiA l y) from GlobalTheory.MemLoc.PhiInj.φB_alg l y, ih]

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.opOne_holds :
    OpOne2 := by
  intro l _ τ₁ hτ K N k n₁ n₂ d ρ y y' Q Q' U hy hQ hU hZ
  have hinj : Function.Injective (iB l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
  have hlB : IsUnit (iB l (l : Per.Acris l)) := by
    rw [map_natCast]; exact isUnit_l_Bcris l
  have h1 : (y * Q) * (Q' * y') = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hy, smul_smul, mul_comm]
  have hc : IsUnit (iB l (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k))) := by
    rw [map_mul, map_pow, map_pow]
    exact (hτ.pow _).mul (hlB.pow _)
  have h2 := opOne_comm (iB l) hinj _ _ _ hc h1
  have hφ : ∀ n, (Per.φB l ^ n) (iB l (l : Per.Acris l)) = iB l (l : Per.Acris l) := by
    intro n; rw [opOne_pow, map_natCast]
  have ht : ∀ n, IsUnit (iB l ((phiA l ^ n) τ₁)) := by
    intro n; rw [← opOne_pow]; exact hτ.map (Per.φB l ^ n)
  refine ⟨h1, h2, ?_, U, hU, ?_⟩
  · rw [map_mul, map_mul, map_pow, map_pow, map_pow]
    exact (((ht n₂).pow _).mul (hlB.pow _)).mul ((ht n₁).pow _)
  · have key := opOne_core (Per.φB l ^ n₁) (Per.φB l ^ n₂) ((y * Q).map (iB l)) ((Q' * y').map (iB l)) U
      (iB l τ₁) (iB l (l : Per.Acris l) ^ (2 * k)) N (by rw [map_pow, hφ])
      (by rw [opOne_pow]; exact ht n₂) hZ
      (by
        rw [← Matrix.map_mul, h2]
        ext a b
        simp [Matrix.smul_apply, Matrix.one_apply, apply_ite (iB l)])
    have hmap : ∀ (n : ℕ) (M : Matrix (Fin d) (Fin d) (Per.Acris l)),
        (M.map ⇑(phiA l ^ n)).map (iB l) = (M.map (iB l)).map ⇑(Per.φB l ^ n) := by
      intro n M
      ext a b
      exact (opOne_pow l n (M a b)).symm
    have hsm : ∀ (c : Per.Acris l) (M : Matrix (Fin d) (Fin d) (Per.Acris l)),
        (c • M).map (iB l) = iB l c • M.map (iB l) := by
      intro c M
      ext a b
      simp [Matrix.smul_apply]
    have hsc : iB l ((phiA l ^ n₂) (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k))) =
        (Per.φB l ^ n₂) (iB l τ₁ ^ (2 * N) * iB l (l : Per.Acris l) ^ (2 * k)) := by
      rw [← opOne_pow, map_mul (iB l), map_pow (iB l), map_pow (iB l)]
    have hs : iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N) =
        (Per.φB l ^ n₂) (iB l τ₁) ^ (3 * N) * (iB l (l : Per.Acris l) ^ (2 * k)) ^ 2 *
          (Per.φB l ^ n₁) (iB l τ₁) ^ N := by
      rw [opOne_pow, opOne_pow, map_mul, map_mul, map_pow, map_pow, map_pow, ← pow_mul,
        show 2 * k * 2 = 4 * k by ring]
    rw [hsm, Matrix.map_mul, hmap, hmap, hsc, hs]
    exact key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TieRep
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

variable {l : ℕ} [Fact l.Prime]

private lemma exists_solve {B : Type} [CommRing B] {d : ℕ} (U : Matrix (Fin d) (Fin d) B) (hU : IsUnit U)
    (f₁ f₂ : B →+* B) (V : Matrix (Fin d) (Fin d) B) (s : B) (z : Fin d → B)
    (hV : V * U.map ⇑f₂ = s • U.map ⇑f₁) :
    ∃ w₀ : Fin d → B, U.map ⇑f₂ *ᵥ w₀ = z ∧ V *ᵥ z = s • (U.map ⇑f₁ *ᵥ w₀) := by
  obtain ⟨u, hu⟩ := hU.map (RingHom.mapMatrix f₂)
  have hu' : (u : Matrix (Fin d) (Fin d) B) = U.map ⇑f₂ := hu
  have hw : U.map ⇑f₂ *ᵥ ((↑u⁻¹ : Matrix (Fin d) (Fin d) B) *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← hu', Units.mul_inv, Matrix.one_mulVec]
  refine ⟨(↑u⁻¹ : Matrix (Fin d) (Fin d) B) *ᵥ z, hw, ?_⟩
  conv_lhs => rw [← hw]
  rw [Matrix.mulVec_mulVec, hV, Matrix.smul_mulVec]

private lemma key_sum {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {d : ℕ}
    (M : Matrix (Fin d) (Fin d) (Per.Bcris l)) (w₀ : Fin d → Per.Bcris l) (t : Fin d → Om l) :
    (∑ j, ((1 : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm (w₀ j)) : Bst P) : OB P) *
      ∑ i, (t i ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm (M i j)) : Bst P) : OB P)) =
    ∑ i, (t i ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm ((M *ᵥ w₀) i)) : Bst P) : OB P) := by
  simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← TensorProduct.tmul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma tmul_zB {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (L : FinExt l)
    (x : ↥L.1) (z : ℤ_[l]) :
    (((x : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm (Per.zB l z)) : Bst P) : OB P) =
      ((((z : ℚ_[l]) • x : ↥L.1)) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] (1 : Bst P) := by
  have h1 : T.eB.symm (Per.zB l z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
    rw [← T.zB z, RingEquiv.symm_apply_apply]
  have h2 : (Polynomial.C (algebraMap ℚ_[l] P.R.B (z : ℚ_[l])) : Bst P) =
      (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • (1 : Bst P) := by
    rw [algebraMap_smul, Algebra.smul_def, mul_one]
    rfl
  have h3 : ((((z : ℚ_[l]) • x : ↥L.1)) : Om l) =
      (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • ((x : ↥L.1) : Om l) := by
    rw [algebraMap_smul]
    rfl
  rw [h1, h2, h3, TensorProduct.smul_tmul]

private lemma coord_sum {P : LocPrime l} {L : FinExt l} {a d : ℕ}
    {ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)} (h : IsCoord P L ψ₀)
    (v : Fin d → Fin a → ↥L.1) (y : Fin d → Bst P) (i' : Fin a) :
    ψ₀ (∑ i, v i ⊗ₜ[ℚ_[l]] y i) i' = ∑ i, ((v i i' : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] y i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => h _ _ _

end UpperTheory.Gal.ClosedPhiFromClosedTrace

set_option maxHeartbeats 4000000 in
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.tieRep_holds :
    TrLin → CoordEx → CoordWD → ColInv → WeilPhi2 → TestTr → TieRep2 := by
  intro hTr hCE hCW hCI hWP hTT l _ ι P AI T E Ω _ _ _ _ _ w A h O _ _ _ Bw hj g n₁ n₂ hα L a d R _
    hdim ρ b e hb he s V hOp
  classical
  obtain ⟨U, hU, hV⟩ := hOp
  have hh := exists_solve U hU.unit (Per.φB l ^ n₁) (Per.φB l ^ n₂) V s (fun i => Per.zB l (e i)) hV
  obtain ⟨w₀, hw⟩ := hh
  obtain ⟨hw₀, hv₀⟩ := hw
  obtain ⟨ψ₀, hψ₀⟩ := hCE l P L a
  obtain ⟨ψ, hψs, hψm⟩ := hCW l P ι Bw.Kw L a R ψ₀ hψ₀
  have hcol := fun (j : Fin d) (k : Fin a) =>
    hCI l P AI T Bw.Kw L a d ρ R (fun i i' => b i i' k) (fun g j => hb g j k) U hU j
  choose x hx₂ hx₁ using fun (j : Fin d) (k : Fin a) =>
    hWP l P E Ω w A h O Bw g n₁ n₂ hα L a R _ (hcol j k).1
  have hψ₂ : ∀ j k i', ψ (wdMk P ι R (x j k)) i' =
      ∑ i, ((b i i' k : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)]
        (Polynomial.C (T.eB.symm ((U.map ⇑(Per.φB l ^ n₂)) i j)) : Bst P) := by
    intro j k i'
    rw [hψm, hx₂, (hcol j k).2 n₂]
    exact coord_sum hψ₀ _ _ i'
  have hψ₁ : ∀ j k i', ψ (wdRho P ι Bw h hj R g (wdMk P ι R (x j k))) i' =
      ∑ i, ((b i i' k : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)]
        (Polynomial.C (T.eB.symm ((U.map ⇑(Per.φB l ^ n₁)) i j)) : Bst P) := by
    intro j k i'
    rw [wdRho_mk, hψm, hx₁, (hcol j k).2 n₁]
    exact coord_sum hψ₀ _ _ i'
  let κ : ℂ →+* OB P := (Algebra.TensorProduct.includeLeftRingHom :
    Om l →+* Om l ⊗[↥(MaximalUnramifiedExtension l)] Bst P).comp ι.symm.toRingHom
  let β : Per.Bcris l → OB P := fun y => (1 : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm y) : Bst P)
  have hframe : ∀ i i', ∑ j, β (w₀ j) * ψ (wdMk P ι R (x j i')) i = if i = i' then 1 else 0 := by
    intro i i'
    have h1 : ∑ j, β (w₀ j) * ψ (wdMk P ι R (x j i')) i = ∑ j, β (w₀ j) *
        ∑ i₂, ((b i₂ i i' : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)]
          (Polynomial.C (T.eB.symm ((U.map ⇑(Per.φB l ^ n₂)) i₂ j)) : Bst P) :=
      Finset.sum_congr rfl fun j _ => by rw [hψ₂]
    rw [h1, key_sum T _ w₀ (fun i₂ => ((b i₂ i i' : ↥L.1) : Om l)), hw₀]
    simp only [tmul_zB T L]
    rw [← TensorProduct.sum_tmul]
    have hs : ∑ i₂, ((((e i₂ : ℚ_[l]) • b i₂ i i' : ↥L.1)) : Om l) = if i = i' then 1 else 0 := by
      have h2 := congrFun (congrFun he i) i'
      rw [Matrix.sum_apply] at h2
      simp only [Matrix.smul_apply] at h2
      rw [← AddSubmonoidClass.coe_finsetSum, h2, Matrix.one_apply]
      split_ifs <;> rfl
    rw [hs]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _
  have hmain := hTr ℂ (OB P) (WDSpace P ι R) (Fin d) a hdim κ ψ hψs (wdRho P ι Bw h hj R g)
    (fun j k => wdMk P ι R (x j k)) (fun j => β (w₀ j)) hframe
  refine hTT l P AI T d s _ ((U.map ⇑(Per.φB l ^ n₁)) *ᵥ w₀) _ _ hv₀ (Eq.trans ?_ hmain)
  have h3 : ∀ i, ∑ j, β (w₀ j) * ψ (wdRho P ι Bw h hj R g (wdMk P ι R (x j i))) i =
      ∑ i₂, ((b i₂ i i : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)]
        (Polynomial.C (T.eB.symm (((U.map ⇑(Per.φB l ^ n₁)) *ᵥ w₀) i₂)) : Bst P) := fun i => by
    rw [← key_sum T _ w₀ (fun i₂ => ((b i₂ i i : ↥L.1) : Om l))]
    exact Finset.sum_congr rfl fun j _ => by rw [hψ₁]
  simp only [h3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i₂ _ => ?_
  rw [← TensorProduct.sum_tmul]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply]
  exact AddSubmonoidClass.coe_finsetSum _ _

end
end

