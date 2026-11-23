module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem crd_cmb (d : SD σ) (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  have e : d.cmb c i j = ∑ k, c (i, j, k) • (Algebra.TensorProduct.basis (AF F) d.bs) k := by
    simp only [SD.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  show (Algebra.TensorProduct.basis (AF F) d.bs).repr (d.cmb c i j) l = c (i, j, l)
  rw [e, Module.Basis.repr_sum_self]

theorem real_indep {u v : ℂ} (hD : u.im * v.re - u.re * v.im ≠ 0) {x y : ℝ} (h : (x : ℂ) * u + (y : ℂ) * v = 0) :
    x = 0 ∧ y = 0 := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.zero_re, Complex.add_im, Complex.mul_im, add_zero, Complex.zero_im] at hr hi
  constructor
  · have e : x * (u.im * v.re - u.re * v.im) = 0 := by linear_combination v.re * hi - v.im * hr
    exact (mul_eq_zero.mp e).resolve_right hD
  · have e : y * (u.im * v.re - u.re * v.im) = 0 := by linear_combination u.im * hr - u.re * hi
    exact (mul_eq_zero.mp e).resolve_right hD

theorem detIm_ne (d : SD σ) (w : InfinitePlace F) :
    ((d.B.emb w).1 (d.bs 0)).im * ((d.B.emb w).1 (d.bs 1)).re -
      ((d.B.emb w).1 (d.bs 0)).re * ((d.B.emb w).1 (d.bs 1)).im ≠ 0 := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  haveI : IsTotallyReal F := hcm.1
  haveI : IsTotallyComplex E := hcm.2.1
  set τ : E →+* ℂ := (d.B.emb w).1 with hτ
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hreal : ∀ f : F, (τ (algebraMap F E f)).im = 0 := by
    intro f
    have e1 : τ (algebraMap F E f) = w.embedding f := RingHom.congr_fun (d.B.emb w).2 f
    have e3 : ComplexEmbedding.conjugate w.embedding = w.embedding :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    have e4 := RingHom.congr_fun e3 f
    rw [ComplexEmbedding.conjugate_coe_eq] at e4
    rw [e1]
    exact Complex.conj_eq_iff_im.mp e4
  have hexp : ∀ e : E, τ e = τ (algebraMap F E (d.bs.repr e 0)) * τ (d.bs 0) +
      τ (algebraMap F E (d.bs.repr e 1)) * τ (d.bs 1) := by
    intro e
    conv_lhs => rw [← d.bs.sum_repr e]
    simp [Fin.sum_univ_two, Algebra.smul_def, map_add (f := _), map_mul]
  obtain ⟨e, he⟩ : ∃ e : E, (τ e).im ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    rw [InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x => ?_
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr (hne x)
  intro hD
  apply he
  have h1 := hexp 1
  have h2 := hexp e
  set p := τ (algebraMap F E (d.bs.repr 1 0)) with hp
  set q := τ (algebraMap F E (d.bs.repr 1 1)) with hq
  set p' := τ (algebraMap F E (d.bs.repr e 0)) with hp'
  set q' := τ (algebraMap F E (d.bs.repr e 1)) with hq'
  have ip : p.im = 0 := hreal _
  have iq : q.im = 0 := hreal _
  have ip' : p'.im = 0 := hreal _
  have iq' : q'.im = 0 := hreal _
  rw [map_one] at h1
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  have h2im := congrArg Complex.im h2
  simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, ip, iq,
    ip', iq', zero_mul, sub_zero, add_zero] at h1re h1im h2im
  linear_combination -(p'.re * (τ (d.bs 0)).re + q'.re * (τ (d.bs 1)).re) * h1im - (p.re * q'.re - q.re * p'.re) * hD +
    (p'.re * (τ (d.bs 0)).im + q'.re * (τ (d.bs 1)).im) * h1re + h2im

def lam0 (d : SD σ) (R : RD d) (hr : ∀ w : InfinitePlace F, w.IsReal) :
    (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun r w a j := star (∑ i, ((R.fr w)⁻¹).1 a i *
    ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))
  map_add' r s := by
    funext w a j
    simp only [Pi.add_apply, Prod.fst_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add, star_add]
  map_smul' c r := by
    funext w a j
    simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul, Prod.smul_fst, smul_eq_mul, Complex.ofReal_mul]
    conv_rhs => rw [show (c : ℂ) = star (c : ℂ) from (Complex.conj_ofReal c).symm, ← star_mul']
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

theorem fock_lattice_injective (d : SD σ) (R : RD d) (hr : ∀ w : InfinitePlace F, w.IsReal) : Function.Injective (lam0 d R hr) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro r hr0
  have hz : ∀ w i j, ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l) = 0 := by
    intro w
    let Z : Matrix (Fin d.m) (Fin d.n) ℂ := fun i j => ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l)
    have h1 : ((R.fr w)⁻¹).1 * Z = 0 := by
      ext a j
      have h := congrFun (congrFun (congrFun hr0 w) a) j
      have h' : star (∑ i, ((R.fr w)⁻¹).1 a i * Z i j) = 0 := h
      rw [star_eq_zero] at h'
      rw [Matrix.mul_apply]
      exact h'
    have h2 : Z = 0 := by
      have e : Z = (R.fr w).1 * (((R.fr w)⁻¹).1 * Z) := by
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rw [e, h1, Matrix.mul_zero]
    intro i j
    exact congrFun (congrFun h2 i) j
  funext k
  obtain ⟨i, j, l⟩ := k
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · have h := hz v.1 i j
    rw [Fin.sum_univ_two] at h
    have hi := real_indep (detIm_ne d v.1) h
    have ev : (⟨v.1, hr v.1⟩ : {w : InfinitePlace F // w.IsReal}) = v := Subtype.ext rfl
    rw [ev] at hi
    fin_cases l
    · exact hi.1
    · exact hi.2
  · exact absurd v.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (hr v.1))

theorem archEquiv (d : SD σ) (R : RD d) :
    ∃ L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ),
      ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
        L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c) := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  haveI : IsTotallyReal F := hcm.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  have hdim : Module.finrank ℝ (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) =
      Module.finrank ℝ (InfinitePlace F → Fin d.m → Fin d.n → ℂ) := by
    simp only [Module.finrank_pi_fintype, mixedEmbedding.finrank, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]
    ring
  have hinj := fock_lattice_injective d R hr
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨(LinearEquiv.ofBijective (lam0 d R hr) ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun c w => ?_⟩
  funext a j
  show star (∑ i, ((R.fr w)⁻¹).1 a i * ∑ l : Fin 2,
      ((((InfiniteAdeleRing.ringEquiv_mixedSpace F (c (i, j, l)).1).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))) =
    star ((((R.fr w)⁻¹).1 * d.cw w (d.cmb c)) a j)
  rw [Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  show _ = piInf (d.B.emb w) (∑ l, c (i, j, l) ⊗ₜ[F] d.bs l)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  rfl

end PositivityTheory.SiegelWeilFormula.KFock

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LocAddOf
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (R : RD d)

theorem tens_add (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ Ψ' : Mx F E d.m d.n → ℂ) :
    R.tens w f (Ψ + Ψ') = R.tens w f Ψ + R.tens w f Ψ' := by
  funext X
  simp only [RD.tens, Pi.add_apply, mul_add]

theorem tens_smul (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx F E d.m d.n → ℂ) :
    R.tens w f (a • Ψ) = a • R.tens w f Ψ := by
  funext X
  simp only [RD.tens, Pi.smul_apply, smul_eq_mul]
  ring

def tensL (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := R.tens w f
  map_add' := tens_add R w f
  map_smul' a Ψ := tens_smul R w f a Ψ

omit R in
theorem cw_add (d : SD σ) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z :=
  Matrix.map_add _ (map_add _) X Z

theorem loc_add_of (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (h : d.cw w Z = 0) : R.loc w (X + Z) = R.loc w X := by
  unfold RD.loc
  rw [cw_add, h, add_zero]

omit R in
theorem crd_add (d : SD σ) (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) :
    d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  unfold SD.crd
  rw [Matrix.add_apply, map_add (f := _), Finsupp.add_apply]

omit R in
theorem crd_fin (d : SD σ) (Z : Mx F E d.m d.n) (h : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have e1 : d.crd (finOne F • Z) k = finOne F * d.crd Z k := by
    unfold SD.crd
    rw [Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e2 : d.crd (finOne F • Z) k = 0 := by
    rw [h]
    unfold SD.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
  have e3 : (finOne F * d.crd Z k).2 = (d.crd Z k).2 := by
    show (finOne F).2 * (d.crd Z k).2 = _
    rw [show (finOne F).2 = 1 from rfl, one_mul]
  rw [← e3, ← e1, e2]
  rfl

theorem away_inv (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X := by
  intro X Z hZ hf
  induction hΨ using Submodule.span_induction generalizing X with
  | mem x hx =>
    obtain ⟨P, g, -, rfl⟩ := hx
    have e1 : ∀ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z)) = fP (P w') (R.loc w' X) := fun w' hw' => by
      rw [loc_add_of R w' X Z (hZ w' (Finset.ne_of_mem_erase hw'))]
    have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
      funext k
      rw [crd_add]
      show (d.crd X k).2 + (d.crd Z k).2 = _
      rw [crd_fin d Z hf k, add_zero]
    show (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z))) * g (fun k => (d.crd (X + Z) k).2) =
      (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g (fun k => (d.crd X k).2)
    rw [Finset.prod_congr rfl e1, e2]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [Pi.smul_apply, hx]

theorem away_tens (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) (P : PX d.m d.n) :
    R.tens w (fP P) Ψ ∈ R.fock := by
  have h : R.away w ≤ R.fock.comap (tensL R w (fP P)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P', g, hg, rfl⟩
    refine Submodule.subset_span ⟨Function.update P' w P, g, hg, ?_⟩
    funext X
    show fP P (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P' w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', fP (Function.update P' w P w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  exact h hΨ

theorem fock_dec (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.fock) :
    ∃ (k : ℕ) (P : Fin k → PX d.m d.n) (Ψ : Fin k → Mx F E d.m d.n → ℂ),
      (∀ i, Ψ i ∈ R.away w) ∧ f = ∑ i, R.tens w (fP (P i)) (Ψ i) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, g, hg, rfl⟩ := hx
    refine ⟨1, fun _ => P w, fun _ X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2,
      fun _ => Submodule.subset_span ⟨P, g, hg, rfl⟩, ?_⟩
    rw [Fin.sum_univ_one]
    funext X
    show (∏ w', fP (P w') (R.loc w' X)) * g (fun k => (d.crd X k).2) =
      fP (P w) (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2)
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), mul_assoc]
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k1, P1, Ψ1, h1, e1⟩ := hx
    obtain ⟨k2, P2, Ψ2, h2, e2⟩ := hy
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append Ψ1 Ψ2, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact h1 j
      · rw [Fin.append_right]; exact h2 j
    · rw [Fin.sum_univ_add, e1, e2]
      simp only [Fin.append_left, Fin.append_right]
  | smul a x _ hx =>
    obtain ⟨k, P, Ψ, h, e⟩ := hx
    refine ⟨k, P, fun i => a • Ψ i, fun i => (R.away w).smul_mem a (h i), ?_⟩
    rw [e, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (tens_smul R w _ a (Ψ i)).symm

omit R in
theorem T_add (d : SD σ) (Φ Φ' : d.Fn) : d.T (Φ + Φ') = d.T Φ + d.T Φ' := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (Φ + Φ')) = d.l (d.dd.rho d.B.ψ _ Φ) + d.l (d.dd.rho d.B.ψ _ Φ')
  rw [← map_add (f := _)]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_add]

omit R in
theorem T_smul (d : SD σ) (a : ℂ) (Φ : d.Fn) : d.T (a • Φ) = a • d.T Φ := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (a • Φ)) = a • d.l (d.dd.rho d.B.ψ _ Φ)
  rw [← map_smul]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_left_comm]

end PositivityTheory.SiegelWeilFormula.KFock

end
end

