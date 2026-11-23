module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JointApproxOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.InvQHolds
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix GlobalTheory.CrTop
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem invQ_holds : InvQ := by
  intro l _ K bk τ hτ N k d ρ F hcr Q Q' hsec g
  obtain ⟨hQQ, hQu₀, hQ'u₀, hQφ₀⟩ := hsec
  obtain ⟨Y, Y', hY, hYY⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨-, -, hE2⟩ := GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d (fun g => (ρ g).val) F Y Y' hY hYY
  obtain ⟨htf, -, ⟨v, hv⟩, hφι, hσι⟩ := _root_.GlobalTheory.AcrisFrobE.main l K bk
  set ι := algebraMap (Ainf l) (Per.Acris l) with hι
  have hQu : ∀ i j, ι (bk.ev X) ∣ (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := hQu₀
  have hQ'u : ∀ i j, ι (bk.ev X) ∣ (Q' - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := hQ'u₀
  change (F.ε g).map (fun a => ι (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q
  set σ := sigA (g : GQ l) with hσdef
  set fA : bk.S →+* Per.Acris l := (ι.comp bk.ev).comp (frobS l bk.a) with hfA
  set f0 : bk.S →+* Per.Acris l := fA.comp ((PowerSeries.C).comp PowerSeries.constantCoeff) with hf0
  have hQφ : fA bk.E ^ N • (Q * F.A.map f0) = f0 bk.E ^ N • (F.A.map fA * Q.map (phiA l)) := hQφ₀
  set ε' := (F.ε g).map (fun a => ι (WittVector.frobenius a)) with hε'
  have hfr : ∀ s : bk.S, fA s = ι (WittVector.frobenius (bk.ev s)) := fun s => by
    simp only [hfA, RingHom.comp_apply, bk.ev_frob]
  have hfix : ∀ c : Wq l bk.a, σ (fA (PowerSeries.C c)) = fA (PowerSeries.C c) := fun c => by
    rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g c]
  have hcomm : ∀ x, phiA l (σ x) = σ (phiA l x) := fun x => GlobalTheory.CrisMaps.phiA_sigA (g : GQ l) x
  have he₀ : ∃ w : (Per.Acris l)ˣ, f0 bk.E = (l : Per.Acris l) * w := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; simp
    refine ⟨((Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map fA.toMonoidHom), ?_⟩
    simp [hf0, hc]
  have hBB : F.A.map fA * F.A'.map fA = fA bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAA : F.A.map f0 * F.A'.map f0 = f0 bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have hσA₀ : (F.A.map f0).map σ = F.A.map f0 := by
    ext i j; simp only [Matrix.map_apply, hf0, RingHom.comp_apply]; exact hfix _
  have hσe₀ : σ (f0 bk.E) = f0 bk.E := by simp only [hf0, RingHom.comp_apply]; exact hfix _
  have hσf : ∀ s : bk.S, ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))) = σ (fA s) := fun s => by
    rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← GlobalTheory.RingBasics.φA_apply, ActLaws.φA_σA]
  have h2 : fA bk.E ^ N • (ε' * (F.A.map fA).map σ) = σ (fA bk.E) ^ N • (F.A.map fA * ε'.map (phiA l)) := by
    have e := congrArg (fun M => M.map (ι.comp WittVector.frobenius)) (hE2 g)
    simp only [map_smul_ring, Matrix.map_mul, Matrix.map_map, map_pow, RingHom.comp_apply] at e
    have hm1 : F.A.map (fun s => ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s)))) =
        (F.A.map fA).map σ := by
      ext i j
      exact hσf _
    have hm2 : F.A.map (fun s => ι (WittVector.frobenius (bk.ev s))) = F.A.map fA := by
      ext i j
      exact (hfr _).symm
    have hm3 : (F.ε g).map (fun a => ι (WittVector.frobenius (WittVector.frobenius a))) =
        ε'.map (phiA l) := by
      ext i j
      exact (hφι _).symm
    change ι (WittVector.frobenius (bk.ev bk.E)) ^ N •
      (ε' * F.A.map (fun s => ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))))) =
      ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev bk.E))) ^ N •
      (F.A.map (fun s => ι (WittVector.frobenius (bk.ev s))) *
        (F.ε g).map (fun a => ι (WittVector.frobenius (WittVector.frobenius a)))) at e
    rw [← hfr, hσf, hm1, hm2, hm3] at e
    exact e
  have hL1 := GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect (Per.Acris l) (phiA l) σ d N k (l : Per.Acris l) (fA bk.E) (f0 bk.E) Q Q' (F.A.map fA) (F.A'.map fA)
    (F.A.map f0) (F.A'.map f0) ε' htf ⟨v, hv⟩ he₀ hcomm (map_natCast _ _) (map_natCast _ _) hσe₀ hσA₀ hQQ hBB hAA hQφ h2
  obtain ⟨w₀, hw₀⟩ := he₀
  set D := Q' * ε' * Q.map σ - (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) with hD
  have hDeq : (l : Per.Acris l) ^ (2 * N) • D = F.A.map f0 * D.map (phiA l) * (((w₀⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) ^ (2 * N) • F.A'.map f0) := by
    rw [Matrix.mul_smul, ← hL1, smul_smul, hw₀]
    congr 1
    rw [mul_pow, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  set u := ι (bk.ev X) with hu
  set π := Ideal.Quotient.mk (Ideal.span {u}) with hπ
  have hz : ∀ M : Matrix (Fin d) (Fin d) (Per.Acris l), (∀ i j, u ∣ M i j) ↔ M.map π = 0 := fun M => by
    constructor
    · intro h; ext i j
      simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h i j
    · intro h i j
      have := congrFun (congrFun h i) j
      simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
  have hQ1 : Q.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQu
  have hQ'1 : Q'.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQ'u
  have hdvdφ : bk.ev X ∣ WittVector.frobenius (bk.ev X) := by
    rw [bk.ev_X, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
    exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero
  have hε1 : ε'.map π = 1 := by
    have : ∀ i j, u ∣ (ε' - 1) i j := fun i j => by
      obtain ⟨c, hc⟩ := hcr g i j
      have e1 : (ε' - 1) i j = ι (WittVector.frobenius ((F.ε g - 1) i j)) := by
        simp only [hε', Matrix.sub_apply, Matrix.map_apply, map_sub]
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      rw [e1, hc, map_mul, map_mul]
      exact dvd_mul_of_dvd_left (map_dvd ι hdvdφ) _
    rw [← sub_eq_zero, ← Matrix.map_one π (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub π)]
    exact (hz _).1 this
  have hQσ : (Q.map σ).map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    have hdσ : u ∣ σ u := by
      rw [hu, hσdef, hσι]; exact map_dvd ι ((galois_discMap l K bk).1 (g : GQ l))
    have : ∀ i j, u ∣ (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := fun i j => by
      have e1 : (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j =
          σ ((Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) := by
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      obtain ⟨c, hc⟩ := hQu i j
      rw [e1, hc, map_mul]
      exact dvd_mul_of_dvd_left hdσ _
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 this
  have hdiv : ∀ i j, ι (bk.ev X) ∣ D i j := by
    refine (hz D).2 ?_
    rw [hD, Matrix.map_sub _ (map_sub π), Matrix.map_mul, Matrix.map_mul, hQ'1, hε1, hQσ]
    simp only [map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), mul_one, smul_mul_smul_comm, map_pow]
    rw [← pow_add, ← two_mul, sub_self]
  have hD0 := _root_.GlobalTheory.BKLim.acris_frob_eq_zero l K bk d (2 * N) D (F.A.map f0) _ hdiv hDeq
  have hM : Q' * ε' * Q.map σ = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) :=
    sub_eq_zero.1 hD0
  refine smul_cancel (pow_cancel htf (2 * k)) ?_
  have := congrArg (fun M => Q * M) hM
  simp only [← Matrix.mul_assoc, hQQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at this
  exact this

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

def IsOp2 {l : ℕ} [Fact l.Prime] {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (n₁ n₂ : ℕ) (s : Per.Bcris l)
    (V : Matrix (Fin d) (Fin d) (Per.Bcris l)) : Prop :=
  ∃ U, IsPerU ρ U ∧ V * U.map ⇑(Per.φB l ^ n₂) = s • U.map ⇑(Per.φB l ^ n₁)

def LinkOp2 : Prop :=
  ∀ (R : Type) [CommRing R] (π s : R) (d d' : ℕ) (W Z Zs : Matrix (Fin d) (Fin d) R)
    (W₁ Z₁ Zs₁ : Matrix (Fin d') (Fin d') R) (Pm R₀ : Matrix (Fin d) (Fin d') R),
    Zs * Z = s • (1 : Matrix (Fin d) (Fin d) R) → Z₁ * Zs₁ = s • (1 : Matrix (Fin d') (Fin d') R) →
    (∀ i j, π ∣ (Pm * Z₁ - Z * R₀) i j) → (∀ i j, π ∣ (Pm * W₁ - W * R₀) i j) →
    ∀ i j, π ∣ ((s • (W * Zs)) * Pm - Pm * (s • (W₁ * Zs₁))) i j

def OpOne2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (τ₁ : Per.Acris l), IsUnit (iB l τ₁) → ∀ (K : FinExt l) (N k n₁ n₂ d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l])
    (y y' Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    y * y' = τ₁ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    IsPerU ρ U → iB l τ₁ ^ N • U = (y * Q).map (iB l) →
    (y * Q) * (Q' * y') = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    (Q' * y') * (y * Q) = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    IsUnit (iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N)) ∧
    IsOp2 ρ n₁ n₂ (iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N))
      (((phiA l ^ n₂) (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
        ((y * Q).map ⇑(phiA l ^ n₁) * (Q' * y').map ⇑(phiA l ^ n₂))).map (iB l))

def LinkZ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N M : ℕ), ∃ n : ℕ, ∀ (k d d' : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (F : Frame bk N d ρ) (F' : Frame bk N d' ρ')
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y₁ : Matrix (Fin d') (Fin d') (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T →
    Y₁.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (Q₁ Q₁' : Matrix (Fin d') (Fin d') (Per.Acris l)),
    IsSecQ bk N k F.A Q Q' → IsSecQ bk N k F'.A Q₁ Q₁' → ∀ (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (R : Matrix (Fin d) (Fin d') bk.S),
    (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) →
    ∀ i j, (l : Per.Acris l) ^ M ∣ (Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk)) i j

def OpEx2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n₁ n₂ : ℕ), FixUr K n₁ → FixUr K n₂ →
    ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ m, Frame bk N (tw.d' m) fun g => (tw.ρ' m g).val)
      (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ m, (F m).IsCr) → F₀.IsCr →
      (∀ n', ∃ m, n' ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n' r) →
    ∃ (s : Per.Acris l) (V : Matrix (Fin d) (Fin d) (Per.Acris l)) (V' : ∀ m, Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Per.Acris l)),
      IsUnit (iB l s) ∧ IsOp2 ρ n₁ n₂ (iB l s) (V.map (iB l)) ∧ (∀ m, IsOp2 (tw.ρ' m) n₁ n₂ (iB l s) ((V' m).map (iB l))) ∧
      ∀ M, ∃ m, M ≤ m ∧ ∀ i j, (l : Per.Acris l) ^ M ∣ (V * (tw.Pi m).map (zC l) - (tw.Pi m).map (zC l) * V' m) i j

def FixOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw → ∀ (g : ↥(Weil h)), FixUr Bw.Kw (alpha l g).natAbs

def WeilPhi2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (L : FinExt l) (a : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)]
      (m : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P), m ∈ Dst P R → ∃ x : ↥(Dpst P R),
      (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n₂) m ∧
      ((weilD Bw h P R g x : ↥(Dpst P R)) : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n₁) m

def TieRep2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (L : FinExt l) (a d : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)],
    Module.finrank ℂ (WDSpace P ι R) = a → ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) ↥L.1)
      (e : Fin d → ℤ_[l]), (∀ g j (k : Fin a), R g (fun i => b j i k) = ∑ i, ((ρ g).val i j : ℚ_[l]) • fun i' => b i i' k) →
      ∑ i, (e i : ℚ_[l]) • b i = 1 → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp2 ρ n₁ n₂ s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (((b i).trace : ↥L.1) : Om l))
        (ι.symm (LinearMap.trace ℂ (WDSpace P ι R) (wdRho P ι Bw h hj R g)))

def Tie2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (a d : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), IsCrysAt P Bw r →
    ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]),
      Reads ρ (r.comp Bw.e.symm.toMonoidHom) b e → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp2 ρ n₁ n₂ s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (b i).trace) (wdTr P ι Bw h hj r g)

def ClosedTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ)
    (a : ℕ), 1 ≤ a → ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw)
      (J : (E →+* Om l) → Multiset ℤ) (r : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l)), Continuous r → IsSSRep r →
    ∀ (C : Set (Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l))) (g : ↥(Weil h)) (θ : Om l),
      JointApprox r C (fun ρ => wdTr P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype) g) θ →
      (∀ ρ ∈ C, Continuous ρ ∧ GlobalTheory.GalOfCusp.IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Om l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
      wdTr P ι Bw h hj (r.comp (Dec (F := E) A).subtype) g = θ

def PowTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x : WD h) (σ : ↥(Weil h)) (n : ℕ),
    GlobalTheory.CongPhi.phiSum x σ n = -(x.charPol (σ ^ n)).nextCoeff

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.LinkRec
section
namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem linkRec_holds : LinkRec := by
  intro R _ φ lr π v w N d d' α β Q α₁ β₁ β₁' Q₁ R₁ R₀ h1 h2 h3 h4 h5
  obtain ⟨u, hu_def⟩ : ∃ u : R, u = ((v ^ N * w ^ (2 * N))⁻¹ : Rˣ) := ⟨_, rfl⟩
  set s := (lr * (v : R)) ^ N with hs
  set t := (lr * (w : R)) ^ N with ht
  have hvw : u * ((v : R) ^ N * (w : R) ^ (2 * N)) = 1 := by
    rw [hu_def, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, Units.inv_mul]
  have hu : u * (s * (lr * (w : R)) ^ (2 * N)) = lr ^ (3 * N) := by
    calc u * (s * (lr * (w : R)) ^ (2 * N))
        = (u * ((v : R) ^ N * (w : R) ^ (2 * N))) * lr ^ (3 * N) := by
          rw [hs]
          ring
      _ = lr ^ (3 * N) := by rw [hvw, one_mul]
  refine ⟨(u * t) • α, β₁', ?_⟩
  set D4 := R₁ * α₁ - α * R₁.map φ with hD4def
  set D5 := R₀ * β₁ - β * R₀.map φ with hD5def
  have hD4 : α * R₁.map φ = R₁ * α₁ - D4 := by rw [hD4def, sub_sub_cancel]
  have hD5 : β * R₀.map φ = R₀ * β₁ - D5 := by rw [hD5def, sub_sub_cancel]
  have e1 : t • (α * R₁.map φ * Q₁.map φ) = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by
    calc t • (α * R₁.map φ * Q₁.map φ) = t • ((R₁ * α₁ - D4) * Q₁.map φ) := by rw [hD4]
      _ = R₁ * (t • (α₁ * Q₁.map φ)) - t • (D4 * Q₁.map φ) := by
        simp only [Matrix.sub_mul, smul_sub, Matrix.mul_smul, Matrix.mul_assoc]
      _ = R₁ * (s • (Q₁ * β₁)) - t • (D4 * Q₁.map φ) := by rw [h3]
      _ = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by
        simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have e2 : t • (α * Q.map φ * R₀.map φ) = s • (Q * R₀ * β₁) - s • (Q * D5) := by
    calc t • (α * Q.map φ * R₀.map φ) = (t • (α * Q.map φ)) * R₀.map φ := by rw [Matrix.smul_mul]
      _ = (s • (Q * β)) * R₀.map φ := by rw [h2]
      _ = s • (Q * (β * R₀.map φ)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = s • (Q * (R₀ * β₁ - D5)) := by rw [hD5]
      _ = s • (Q * R₀ * β₁) - s • (Q * D5) := by
        simp only [Matrix.mul_sub, smul_sub, Matrix.mul_assoc]
  have hmap : (R₁ * Q₁ - Q * R₀).map φ = R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ := by
    rw [Matrix.map_sub _ (map_sub φ), Matrix.map_mul, Matrix.map_mul]
  have e3 : (u * t) • α * (R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ)
      = u • (t • (α * R₁.map φ * Q₁.map φ) - t • (α * Q.map φ * R₀.map φ)) := by
    simp only [Matrix.smul_mul, Matrix.mul_sub, smul_sub, smul_smul, Matrix.mul_assoc]
  have key : lr ^ (3 * N) • (R₁ * Q₁ - Q * R₀) - (u * t) • α * (R₁ * Q₁ - Q * R₀).map φ * β₁'
      = (u * t) • (D4 * (Q₁.map φ * β₁')) - (u * s) • (Q * (D5 * β₁')) := by
    rw [hmap, e3, e1, e2, ← hu]
    simp only [Matrix.sub_mul, Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc, h1,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_sub]
    module
  intro i j
  rw [key, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    Matrix.mul_apply, Matrix.mul_apply]
  refine dvd_sub (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (h4 i k) _) _)
    (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right ?_ _) _)
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k' _ => dvd_mul_of_dvd_left (h5 k k') _

end UpperTheory.Gal.ClosedPhiFromClosedTrace
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.PowDvdOfEv
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem link_core {W : Type} [CommRing W] (fr : W →+* W) (c e : W) (hc : fr c = c) {d d' : ℕ}
    (Z Rv : Matrix (Fin d) (Fin d') W) (T A : Matrix (Fin d) (Fin d) W) (T' A' : Matrix (Fin d') (Fin d') W)
    (hZ : Z.map fr = Z) (hT : IsUnit T) (hφ : e • T.map fr = T * A) (hφ' : e • T'.map fr = T' * A')
    (hD : ∀ i j, c ∣ (Z * T' - T * Rv) i j) :
    ∀ i j, c ∣ (Rv * A' - A * Rv.map fr) i j := by
  choose G hG using hD
  have hD' : Z * T' - T * Rv = c • Matrix.of G := by
    ext i j
    simp [hG i j]
  have h1 : Z * T'.map fr - T.map fr * Rv.map fr = c • (Matrix.of G).map fr := by
    have h := congrArg (fun M => M.map fr) hD'
    have e1 : (Z * T' - T * Rv).map fr = Z * T'.map fr - T.map fr * Rv.map fr := by
      rw [Matrix.map_sub _ (map_sub fr), Matrix.map_mul, Matrix.map_mul, hZ]
    have e2 : (c • Matrix.of G).map fr = c • (Matrix.of G).map fr := by
      ext i j
      simp [hc]
    simpa only [e1, e2] using h
  have h2 : T * (Rv * A' - A * Rv.map fr) = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by
    have e3 : T * Rv = Z * T' - c • Matrix.of G := by rw [← hD']; abel
    calc T * (Rv * A' - A * Rv.map fr)
        = (T * Rv) * A' - (T * A) * Rv.map fr := by
          rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Z * (T' * A') - c • (Matrix.of G * A') - (T * A) * Rv.map fr := by
          rw [e3, Matrix.sub_mul, Matrix.mul_assoc, Matrix.smul_mul]
      _ = e • (Z * T'.map fr - T.map fr * Rv.map fr) - c • (Matrix.of G * A') := by
          rw [← hφ, ← hφ', Matrix.mul_smul, Matrix.smul_mul, smul_sub]
          abel
      _ = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by
          rw [h1, smul_sub, smul_comm]
  obtain ⟨u, rfl⟩ := hT
  have h3 : Rv * A' - A * Rv.map fr =
      c • ((↑u⁻¹ : Matrix (Fin d) (Fin d) W) * (e • (Matrix.of G).map fr - Matrix.of G * A')) := by
    rw [← Matrix.mul_smul, ← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  intro i j
  rw [h3, Matrix.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

private theorem pow_dvd_of_ev {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (n : ℕ) (x : bk.S)
    (h : (l : Ainf l) ^ n ∣ bk.ev x) : (l : bk.S) ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨x', rfl⟩ := bk.dvd_of_dvd_ev x ⟨(l : Ainf l) ^ n * c, by rw [hc, pow_succ', mul_assoc]⟩
    have h0 : bk.ev x' - (l : Ainf l) ^ n * c = 0 := by
      apply ainf_torsionFree
      rw [map_mul, map_natCast, pow_succ', mul_assoc] at hc
      rw [mul_sub, hc, sub_self]
    have h1 : (l : Ainf l) ^ n ∣ bk.ev x' := ⟨c, sub_eq_zero.1 h0⟩
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih x' h1)

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkA_holds :
    LinkA := by
  intro l _ K bk τ hτ N d d' n ρ ρ' F F' Y Y' hY hY' Pi R hlink
  have hev : ∀ s, inclW l (bk.ev s) = bk.evW s := fun s => rfl
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.HTBound.pow_dvd_of_inclW
    have e1 : (Pi.map (Per.zA l)).map (inclW l) = zW Pi := by
      refine Matrix.ext fun a b => ?_
      exact (inclWA l).commutes _
    have e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW := by
      rw [Matrix.map_map]; rfl
    have e : (Pi.map (Per.zA l) * Y' - Y * R.map bk.ev).map (inclW l) =
        inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW) := by
      rw [Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left (hlink i j) _
  · have key := link_core (frobW l).toRingHom ((l : WCb l) ^ n) (bk.evW bk.E ^ N) (by simp)
      (zW Pi) (R.map bk.evW) F.T (F.A.map bk.evW) F'.T (F'.A.map bk.evW)
      (by ext i j; simp [zW]) F.unit F.φ F'.φ hlink
    have hfr : (R.map bk.evW).map (frobW l).toRingHom = (R.map (frobS l bk.a)).map bk.evW := by
      refine Matrix.ext fun a b => ?_
      simp only [Matrix.map_apply]
      show frobW l (inclW l (bk.ev (R a b))) = inclW l (bk.ev (frobS l bk.a (R a b)))
      rw [frobW_inclW, bk.ev_frob]
    rw [hfr] at key
    have hmap : R.map bk.evW * F'.A.map bk.evW - F.A.map bk.evW * (R.map (frobS l bk.a)).map bk.evW =
        (R * F'.A - F.A * R.map (frobS l bk.a)).map bk.evW := by
      rw [Matrix.map_sub _ (map_sub bk.evW), Matrix.map_mul, Matrix.map_mul]
    rw [hmap] at key
    intro i j
    apply pow_dvd_of_ev
    apply GlobalTheory.HTBound.pow_dvd_of_inclW
    simpa only [Matrix.map_apply, hev] using key i j
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TestTr
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.testTr_holds :
    TestTr := by
  intro l _ P AI T d s v v₀ t p hv h lam
  subst hv
  let Λ : OB P →ₗ[↥(MaximalUnramifiedExtension l)] Bst P :=
    (TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P)).toLinearMap ∘ₗ lam.rTensor (Bst P)
  have hΛ : ∀ (x : Om l) (b : Bst P), Λ (x ⊗ₜ b) = lam x • b := by
    intro x b
    change TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P) (lam.rTensor (Bst P) (x ⊗ₜ b)) = lam x • b
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  have h1 := congrArg Λ h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hΛ] at h1
  simp only [hΛ] at h1
  have hc : lam p • (1 : Bst P) = Polynomial.C (lam p • (1 : P.R.B)) := by
    rw [← Polynomial.smul_C, map_one]
  have h2 : (∑ i, lam (t i) • T.eB.symm (v₀ i)) = lam p • (1 : P.R.B) := by
    apply Polynomial.C_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hc, ← h1]
    simp only [Polynomial.smul_C]
  simp only [Algebra.smul_def] at h2
  have h3 := congrArg T.eB h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_one, mul_one, RingEquiv.apply_symm_apply] at h3
  have h4 : ∑ i, uB T (lam (t i)) * v₀ i = uB T (lam p) := h3
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h4, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
end

